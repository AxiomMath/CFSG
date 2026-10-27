module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCentCore
public import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace KS11LieProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

section Diag

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem diagE_mem_statedScalars_iff (e : Kˣ) :
    diagE e ∈ StatedScalars (Fin 3) K ↔ e = 1 := by
  constructor
  · rintro ⟨z, hz⟩
    have h := eq_of_scalar_eq_diagE_mul_blockHom (B := 1) (map_one _)
      (by rw [hz, map_one, mul_one])
    have h1 : (z : K) = 1 := by
      have := congrFun (congrFun h.2 0) 0
      simpa using this.symm
    exact Units.ext (by rw [h.1, h1, Units.val_one])
  · rintro rfl
    refine ⟨1, ?_⟩
    rw [map_one]
    apply Units.ext
    rw [coe_diagE, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem diagTwo_pow (μ : Kˣ) (n : ℕ) : diagTwo μ ^ n = diagTwo (μ ^ n) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_diagTwo, coe_diagTwo, Matrix.diagonal_pow]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diagTwo_eq_one_iff (μ : Kˣ) : diagTwo μ = 1 ↔ μ = 1 := by
  constructor
  · intro h
    have := congrFun (congrFun (congrArg (fun A : GL (Fin 2) K =>
      (A : Matrix (Fin 2) (Fin 2) K)) h) 0) 0
    simp only [coe_diagTwo, Units.val_one, diagonal_apply_eq, Matrix.one_apply_eq] at this
    exact Units.ext (by simpa using this)
  · rintro rfl
    apply Units.ext
    rw [coe_diagTwo, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem orderOf_blockProj_diagTwo (hK : PiField π p f K) {h₀ : GL (Fin 3) K}
    (hh₀ : h₀ ∈ glPi π 3 (p ^ f) K) {μ : Kˣ} (hμ : diagTwo μ ∈ slPi π 2 (p ^ f) K) :
    orderOf (blockProj hK hh₀ ⟨diagTwo μ, hμ⟩) = orderOf μ := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow, (map_eq_one_iff _ (blockProj_injective hK hh₀)), ← diagTwo_eq_one_iff,
    ← diagTwo_pow]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext (by simpa using h)

end Diag

theorem isLThreePi_of_commutator {Z X : Type} [Group Z] [Group X] (hX : Sec13.IsLThreePi X)
    (ψ : Z ≃* _root_.commutator X) (hZ : ¬ Group.IsSolvable Z) : Sec13.IsLThreePi Z := by
  obtain ⟨p, e, hp, he, hiso⟩ := hX
  have hperf : ∀ (W : Type) [Group W], Group.IsPerfect W → (X ≃* W) → Nonempty (Z ≃* W) := by
    intro W _ hW χ
    have hXp : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (f := χ.symm.toMonoidHom) χ.symm.surjective
    exact ⟨ψ.trans ((MulEquiv.subgroupCongr (Group.isPerfect_def.mp hXp)).trans
      (Subgroup.topEquiv.trans χ))⟩
  rcases hiso with ⟨hpe, ⟨χ⟩⟩ | ⟨hpe, ⟨χ⟩⟩
  · obtain ⟨φ⟩ := hperf _ (Sec13.isPerfect_center_projSL p e he hpe).1 χ
    exact ⟨p, e, hp, he, Or.inl ⟨hpe, ⟨φ⟩⟩⟩
  · by_cases hq2 : 2 < p ^ e
    · obtain ⟨φ⟩ := hperf _ (Sec13.isPerfect_center_projSU p e he hpe hq2).1 χ
      exact ⟨p, e, hp, he, Or.inr ⟨hpe, ⟨φ⟩⟩⟩
    · exfalso
      have h2 : p ^ e = 2 := by
        have : 2 ≤ p ^ e := hp.out.two_le.trans (Nat.le_self_pow (by omega) p)
        omega
      obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp.out h2
      apply hZ
      have := Sec13.isSolvable_projSU_two
      have hXs : Group.IsSolvable X :=
        Group.isSolvable_of_isSolvable_injective (f := χ.toMonoidHom) χ.injective
      exact Group.isSolvable_of_isSolvable_injective
        (f := (_root_.commutator X).subtype.comp ψ.toMonoidHom)
        ((_root_.commutator X).subtype_injective.comp ψ.injective)

variable {G : Type} [Group G] [Finite G]

theorem pow_eq_one_iff_of_conj {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf]
    (hKf : PiField π p f Kf) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {β : MulAut (projImage (slPi π 3 (p ^ f) Kf))} {h₀ : GL (Fin 3) Kf} {l : Kfˣ}
    (hβ : ∀ m : projImage (slPi π 3 (p ^ f) Kf), (β m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE l * h₀⁻¹))⁻¹) (n : ℕ) :
    β ^ n = 1 ↔ l ^ n = 1 := by
  have hβn : ∀ m : projImage (slPi π 3 (p ^ f) Kf), ((β ^ n) m : ProjGenLinGroup (Fin 3) Kf) =
      ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹) * m *
        (ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹))⁻¹ := by
    intro m
    rw [mulAut_pow_coe hβ n m, ← map_pow, conj_pow_gl, diagE_pow]
  constructor
  · intro h1
    have hs : h₀ * diagE (l ^ n) * h₀⁻¹ ∈ StatedScalars (Fin 3) Kf := by
      refine Sec13.mem_statedScalars_of_commute_mk hKf hq hq2 fun s hs => ?_
      have h2 := hβn (projOf _ ⟨s, hs⟩)
      rw [h1, MulAut.one_apply] at h2
      have h3 : ((projOf _ ⟨s, hs⟩ : projImage (slPi π 3 (p ^ f) Kf)) :
          ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk s := rfl
      rw [h3] at h2
      calc ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹) * ProjGenLinGroup.mk s =
          (ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹) * ProjGenLinGroup.mk s *
            (ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹))⁻¹) *
              ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹) := by group
        _ = ProjGenLinGroup.mk s * ProjGenLinGroup.mk (h₀ * diagE (l ^ n) * h₀⁻¹) := by
            rw [← h2]
    exact (diagE_mem_statedScalars_iff _).mp (conj_mem_statedScalars_iff.mp hs)
  · intro h1
    have hd : diagE (1 : Kfˣ) = 1 := by
      apply Units.ext
      rw [coe_diagE, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    ext m
    rw [hβn m, h1, hd, mul_one, mul_inv_cancel, map_one, inv_one, one_mul, mul_one]
    rfl

omit [Finite G] in
theorem orderOf_dvd_card_of_image {Y K : Subgroup G} {X : Type} [Group X]
    (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* X) {x : X}
    (hx : ∃ y : Y, (y : G) ∈ K ∧ φ (y : Y ⧸ aschbacherSolvableCore 3 Y) = x) :
    orderOf x ∣ Nat.card K := by
  obtain ⟨y, hyK, rfl⟩ := hx
  have h1 := orderOf_map_dvd (φ.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) y
  have h2 : orderOf (y : G) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hyK
  rw [Subgroup.orderOf_coe] at h2
  exact h1.trans h2

theorem orderOf_dvd_of_cent {Y K : Subgroup G} {π : Bool} {p f : ℕ} {Kf : Type} [Field Kf]
    (hKf : PiField π p f Kf) (φ : Y ⧸ aschbacherSolvableCore 3 Y ≃* projImage (slPi π 3 (p ^ f) Kf))
    {h₀ : GL (Fin 3) Kf} (hh₀ : h₀ ∈ glPi π 3 (p ^ f) Kf) {l : Kfˣ}
    (hl : π = false → (l : Kf) ^ (p ^ f + 1) = 1)
    (hblk : ∀ B : slPi π 2 (p ^ f) Kf, ∃ y : Y, (y : G) ∈ K ∧
      φ (y : Y ⧸ aschbacherSolvableCore 3 Y) = blockProj hKf hh₀ B) {k : ℕ} (hlk : l ^ 3 ^ k = 1) :
    ∃ j ≤ (Nat.card K).factorization 3, orderOf l = 3 ^ j := by
  have hμ := diagTwo_mem_slPi hKf hl
  have h1 := orderOf_dvd_card_of_image φ (hblk ⟨diagTwo l, hμ⟩)
  rw [orderOf_blockProj_diagTwo hKf hh₀ hμ] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hlk)
  refine ⟨j, ?_, hj⟩
  rw [hj] at h1
  exact (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1

theorem centBound119L3 : CentBound119L3 := by
  intro G _ _ Y K c t hY hcN hc3 hK hT htN ht3 _ htK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨X, _, hX, ⟨ψ⟩⟩ := hY
  have hYL := isLThreePi_of_commutator hX ψ (not_isSolvable_thetaQuot hcN hc3 hK)
  obtain ⟨π, p, f, Kf, _, hKf, hq, hq2, ⟨φ⟩⟩ := exists_model hYL hcN hc3 hK
  obtain ⟨k, hk⟩ := ht3
  obtain ⟨h₀, hh₀, l, hl, hβl, hblk⟩ := cent_core hcN hc3 hK hT hKf hq hq2 φ htN hk htK
  set β := MulAut.congr φ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩)) with hβ
  have hβk : β ^ 3 ^ k = 1 := by
    have h1 : (⟨t, htN⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [hβ, ← map_pow, ← map_pow, ← map_pow, h1, map_one, map_one, map_one]
  have hlk := (pow_eq_one_iff_of_conj hKf hq hq2 hβl _).mp hβk
  obtain ⟨j, hj, hlj⟩ := orderOf_dvd_of_cent hKf φ hh₀ hl hblk hlk
  set N := 3 ^ (Nat.card K).factorization 3 with hN
  have hlN : l ^ N = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hlj]
    exact Nat.pow_dvd_pow 3 hj
  have hβN : β ^ N = 1 := (pow_eq_one_iff_of_conj hKf hq hq2 hβl _).mpr hlN
  have hτN : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨t, htN⟩) ^ N = 1 := by
    apply (MulAut.congr φ).injective
    rw [map_pow, map_one]
    exact hβN
  refine ⟨⟨t, htN⟩ ^ N, MonoidHom.mem_ker.mpr ?_, by simp⟩
  rw [map_pow, MonoidHom.comp_apply]
  exact hτN

section Transport

variable {K : Type} [Field K] {p f : ℕ}

section Unitary

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem congr_eq_psuConj (hK : PiField false p f K)
    {β : MulAut (projImage (slPi false 3 (p ^ f) K))} {A : GL (Fin 3) K}
    (hA : A ∈ glPi false 3 (p ^ f) K)
    (hβ : ∀ m : projImage (slPi false 3 (p ^ f) K), (β m : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk A * m * (ProjGenLinGroup.mk A)⁻¹) :
    MulAut.congr (psuEquivUnitary hK.unitary) β =
      psuConj hK.unitary ⟨A, mem_unitaryIsom3.mpr ((mem_glPi_false hK.unitary).mp hA)⟩ := by
  set h := hK.unitary with hh
  set ψ := psuEquivUnitary h with hψ
  have hproj : ∀ t : unitarySU p f K 3, ψ.symm (unitaryProj h 3 t) = suToPsu p f K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  ext x
  induction x using QuotientGroup.induction_on with
  | H s =>
    have h1 : β (suToPsu p f K s) = suToPsu p f K
        (suConj h ⟨A, mem_unitaryIsom3.mpr ((mem_glPi_false h).mp hA)⟩ s) := by
      apply Subtype.ext
      rw [hβ, coe_suToPsu, coe_suToPsu, coe_suConj, map_mul, map_mul, Subgroup.coe_inv,
        map_inv]
    change (MulAut.congr ψ β) (unitaryProj h 3 s) = psuConj h _ (unitaryProj h 3 s)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hproj, h1,
      psuEquivUnitary_suToPsu, psuConj_unitaryProj]

end Unitary

theorem diagE_mem_glPi {π : Bool} (hK : PiField π p f K) {l : Kˣ}
    (hl : π = false → (l : K) ^ (p ^ f + 1) = 1) : diagE l ∈ glPi π 3 (p ^ f) K := by
  cases π
  · have h := hK.unitary
    rw [mem_glPi_false h, coe_diagE, diagonal_map (map_zero _), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, cons_val_zero, h.bar_apply]
      rw [← pow_succ, hl rfl]
    · simp
    · simp
  · exact mem_glPi_true _ _

theorem det_conj_gl (h M : GL (Fin 3) K) :
    ((h * M * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (M : Matrix (Fin 3) (Fin 3) K).det := by
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm (det (h : Matrix (Fin 3) (Fin 3) K)),
    mul_assoc, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, mul_one]

end Transport

end KS11LieProof

end CFSG.RankThree.PartTwo.Sec11
