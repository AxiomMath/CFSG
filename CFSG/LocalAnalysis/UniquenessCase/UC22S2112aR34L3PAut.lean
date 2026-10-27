module

public import CFSG.Blueprint.Catalog
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix
open CFSG.Open CFSG.Open.StatedAPI CFSG.RankThree.SubgroupLists
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

section Matrices

variable (K : Type) [Field K]

private def rotGL : GL (Fin 3) K :=
  SpecialLinearGroup.toGL ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], by simp [det_fin_three]⟩

private def flipGL : GL (Fin 3) K :=
  SpecialLinearGroup.toGL ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], by simp [det_fin_three]⟩

private theorem coe_rotGL :
    ((rotGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; -1, 0, 0; 0, 0, 1] :=
  rfl

private theorem coe_flipGL :
    ((flipGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, -1, 0; 0, 0, -1] :=
  rfl

private theorem rotGL_flipGL_rels : rotGL K ^ 4 = 1 ∧ flipGL K ^ 2 = 1 ∧
    flipGL K * rotGL K * flipGL K * rotGL K = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Units.ext <;>
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, coe_rotGL, coe_flipGL, Units.val_one] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

private theorem rotGL_flipGL_mem_statedSU {q : ℕ} (hq : Odd q) :
    rotGL K ∈ StatedSU 3 q K ∧ flipGL K ∈ StatedSU 3 q K := by
  refine ⟨Subgroup.subset_closure ⟨by simp [coe_rotGL, det_fin_three], ?_⟩,
    Subgroup.subset_closure ⟨by simp [coe_flipGL, det_fin_three], ?_⟩⟩ <;>
    simp only [coe_rotGL, coe_flipGL] <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hq.neg_one_pow, hq.pos.ne']

variable {K}

private theorem eq_diagonal_of_commute (h2 : (2 : K) ≠ 0) {Y : Matrix (Fin 3) (Fin 3) K}
    (hR : (rotGL K : Matrix (Fin 3) (Fin 3) K) * Y = Y * (rotGL K : Matrix (Fin 3) (Fin 3) K))
    (hF : (flipGL K : Matrix (Fin 3) (Fin 3) K) * Y = Y * (flipGL K : Matrix (Fin 3) (Fin 3) K)) :
    Y = diagonal ![Y 0 0, Y 0 0, Y 2 2] := by
  simp only [coe_rotGL, coe_flipGL] at hR hF
  have z : ∀ t : K, t = -t → t = 0 := fun t ht =>
    (mul_eq_zero.1 (show (2 : K) * t = 0 by linear_combination ht)).resolve_left h2
  obtain ⟨r01, r02, r21⟩ := And.intro (congrFun (congrFun hR 0) 1)
    (And.intro (congrFun (congrFun hR 0) 2) (congrFun (congrFun hR 2) 1))
  obtain ⟨f01, f02, f10, f20⟩ := And.intro (congrFun (congrFun hF 0) 1)
    (And.intro (congrFun (congrFun hF 0) 2)
      (And.intro (congrFun (congrFun hF 1) 0) (congrFun (congrFun hF 2) 0)))
  simp [Matrix.mul_apply, Fin.sum_univ_three] at r01 r02 r21 f01 f02 f10 f20
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal] <;> grind

end Matrices

private theorem mul_comm_of_mk {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {y r : H}
    (hr : ((r : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace ≠ 0)
    (h : Commute (y : StatedProj H) (r : StatedProj H)) :
    ((r : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (y : GL (Fin 3) K) =
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (r : GL (Fin 3) K) := by
  obtain ⟨c, hc⟩ := (statedProj_mk_eq_iff H (y * r) (r * y)).1
    (by rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact h)
  simp only [Subgroup.coe_mul, Units.val_mul] at hc
  set R := ((r : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have e : (((y : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (R * (y : GL (Fin 3) K)) = (c : K) • R := by
    rw [hc, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, Matrix.mul_smul, mul_one]
  have hc1 : ((c : K) - 1) * R.trace = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero, ← smul_eq_mul, ← trace_smul, ← e, trace_mul_comm,
      mul_assoc, Units.mul_inv, mul_one]
  rw [hc, sub_eq_zero.1 ((mul_eq_zero.1 hc1).resolve_right hr), one_smul, mul_one]

private theorem exists_conj_commute {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) (S : Sylow 2 X) {x : X} (hx : x ∈ centralizer (S : Set X)) :
    ∃ g : X, ∀ z ∈ P, Commute (g * x * g⁻¹) z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X S Q
  refine ⟨g, fun z hz => ?_⟩
  have hz' : g⁻¹ * z * g ∈ (S : Subgroup X) := by
    simpa [mul_assoc] using (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).1 (hQ hz)
  calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by rw [mem_centralizer_iff.1 hx _ hz']
    _ = z * (g * x * g⁻¹) := by group

private theorem isPGroup_zpowers {X : Type} [Group X] {u : X} {k : ℕ} (hu : u ^ 2 ^ k = 1) :
    IsPGroup 2 (zpowers u) :=
  IsPGroup.of_card_dvd_pow (n := k) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hu)

private theorem exists_diag {X : Type} [Group X] [Finite X] {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) {H : Subgroup (GL (Fin 3) K)} (hR : rotGL K ∈ H) (hF : flipGL K ∈ H)
    (e : X ≃* StatedProj H) (S : Sylow 2 X) {x : X} (hx : x ∈ centralizer (S : Set X)) :
    ∃ g : X, ∃ y : H, ∃ a b : K, e (g * x * g⁻¹) = (y : StatedProj H) ∧
      ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![a, a, b] := by
  let π : H →* X := e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  let r : H := ⟨rotGL K, hR⟩
  let f : H := ⟨flipGL K, hF⟩
  obtain ⟨h4, h2', h3⟩ := rotGL_flipGL_rels K
  have hu : π r ^ 2 ^ 2 = 1 := by rw [← map_pow, show r ^ 2 ^ 2 = 1 from Subtype.ext h4, map_one]
  have hv : π f ^ 2 ^ 1 = 1 := by rw [← map_pow, show f ^ 2 ^ 1 = 1 from Subtype.ext h2', map_one]
  have hvu : π f * π r * π f * π r = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, show f * r * f * r = 1 from Subtype.ext h3, map_one]
  have hvinv : (π f)⁻¹ = π f := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; simpa using hv)
  have hN : zpowers (π f) ≤ normalizer (zpowers (π r) : Set X) := by
    rw [zpowers_le, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    rw [show (MulAut.conj (π f) : X →* X) (π r) = (π r)⁻¹ by
      rw [MonoidHom.coe_coe, MulAut.conj_apply, hvinv]
      exact eq_inv_of_mul_eq_one_left hvu, zpowers_inv]
  obtain ⟨g, hg⟩ := exists_conj_commute
    (IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers hv) (isPGroup_zpowers hu) hN) S hx
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (e (g * x * g⁻¹))
  have hcomm : ∀ w : H, π w ∈ zpowers (π f) ⊔ zpowers (π r) →
      Commute (y : StatedProj H) (w : StatedProj H) := fun w hw => by
    have := (hg _ hw).map e
    rwa [← hy, show e (π w) = (w : StatedProj H) from e.apply_symm_apply _] at this
  have hyr := mul_comm_of_mk (by simp [r, coe_rotGL, trace_fin_three])
    (hcomm r (mem_sup_right (mem_zpowers _)))
  have hyf := mul_comm_of_mk (by simp [f, coe_flipGL, trace_fin_three])
    (hcomm f (mem_sup_left (mem_zpowers _)))
  exact ⟨g, y, _, _, hy.symm, eq_diagonal_of_commute h2 hyr hyf⟩

private theorem sl2_map_injective {R S : Type} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) : Function.Injective (SpecialLinearGroup.map (n := Fin 2) φ) := by
  intro A B h
  ext i j
  exact hφ (by simpa using congrArg (fun C : SL(2, S) => (C : Matrix (Fin 2) (Fin 2) S) i j) h)

private theorem model_data {X : Type} [Group X] {p : ℕ} (hp2 : p ≠ 2)
    (hX : LieModel X .PSL 3 p 1 ∨ LieModel X .PSU 3 p 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (H : Subgroup (GL (Fin 3) K)),
      (2 : K) ≠ 0 ∧ rotGL K ∈ H ∧ flipGL K ∈ H ∧
      (∀ A ∈ H, (A : Matrix (Fin 3) (Fin 3) K).det = 1) ∧ Nat.card K - 1 ∣ p ^ 2 - 1 ∧
      (∃ φ : SL(2, ZMod p) →* GL (Fin 2) K, Function.Injective φ ∧ ∀ γ, blockGL3 (φ γ) ∈ H) ∧
      Nonempty (X ≃* StatedProj H) := by
  have hp : p.Prime := by rcases hX with h | h <;> exact h.admissible.1
  have : Fact p.Prime := ⟨hp⟩
  rcases hX with h | h
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
    have : Fintype K := Fintype.ofFinite K
    have : CharP K p :=
      charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK])
    refine ⟨K, inferInstance, inferInstance, StatedSL 3 K,
      Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2),
      mem_statedSL_of_det (by simp [coe_rotGL, det_fin_three]),
      mem_statedSL_of_det (by simp [coe_flipGL, det_fin_three]), fun A hA => det_of_mem_statedSL hA,
      by rw [hK, pow_one]; simpa using Nat.sub_dvd_pow_sub_pow p 1 2,
      ⟨SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (ZMod.castHom (dvd_refl p) K)),
        SpecialLinearGroup.toGL_injective.comp (sl2_map_injective (ZMod.castHom _ K).injective),
        fun γ => mem_statedSL_of_det (by
          rw [coe_blockGL3, det_leviMat]; exact (SpecialLinearGroup.map _ γ).prop)⟩, ⟨e⟩⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
    have : Fintype K := Fintype.ofFinite K
    have : CharP K p :=
      charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK, pow_one])
    obtain ⟨E⟩ := nonempty_sl2_mulEquiv_statedSU_two (K := K) (r := p) (f := 1) hK
    have : Fintype (CFSG.LieType.Steinberg.fixedSubfield K p 1) := Fintype.ofFinite _
    let ε : ZMod p ≃+* CFSG.LieType.Steinberg.fixedSubfield K p 1 :=
      FiniteField.ringEquivOfCardEq (by
        rw [ZMod.card, ← Nat.card_eq_fintype_card,
          CFSG.LieType.Steinberg.card_fixedSubfield hK, pow_one])
    obtain ⟨hR, hF⟩ := rotGL_flipGL_mem_statedSU K (hp.odd_of_ne_two hp2).pow
    refine ⟨K, inferInstance, inferInstance, StatedSU 3 (p ^ 1) K,
      Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2), hR, hF,
      fun A hA => det_of_mem_statedSU hA, by rw [hK, pow_one],
      ⟨(StatedSU 2 (p ^ 1) K).subtype.comp
          (E.toMonoidHom.comp (SpecialLinearGroup.map ε.toRingHom)),
        Subtype.val_injective.comp (E.injective.comp (sl2_map_injective ε.injective)),
        fun γ => map_blockGL3_statedSU_le (Nat.one_le_pow _ _ hp.pos)
          (mem_map_of_mem _ (E (SpecialLinearGroup.map ε.toRingHom γ)).2)⟩, ⟨e⟩⟩

theorem uc22s2112l3p_dvd_sq_sub_one {X : Type} [Group X] [Finite X] {p : ℕ} (hp2 : p ≠ 2)
    (hX : LieModel X .PSL 3 p 1 ∨ LieModel X .PSU 3 p 1) (S : Sylow 2 X) {x : X}
    (hx : x ∈ centralizer (S : Set X)) (hxp : (orderOf x).Prime) : orderOf x ∣ p ^ 2 - 1 := by
  obtain ⟨K, _, _, H, h2, hR, hF, hdet, hcard, -, ⟨e⟩⟩ := model_data hp2 hX
  obtain ⟨g, y, a, b, hxy, hy⟩ := exists_diag h2 hR hF e S hx
  have hos : orderOf (y : StatedProj H) = orderOf x := by
    rw [← hxy, MulEquiv.orderOf_eq, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have hab : a * a * b = 1 := by
    simpa [hy, det_diagonal, Fin.prod_univ_three] using hdet _ y.2
  obtain ⟨c, hc⟩ := (statedProj_mk_eq_iff H 1 (y ^ orderOf x)).1 (by
    rw [QuotientGroup.mk_pow, QuotientGroup.mk_one, ← hos, pow_orderOf_eq_one])
  simp only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val, Units.val_one,
    one_mul, hy, diagonal_pow] at hc
  have h0 := congrFun (congrFun hc 0) 0
  have h2' := congrFun (congrFun hc 2) 2
  simp at h0 h2'
  have ha0 : a ≠ 0 := fun h => by simp [h] at hab
  have hne : a ≠ b := by
    rintro rfl
    have h1 : (y : StatedProj H) = 1 := by
      rw [← QuotientGroup.mk_one, eq_comm, statedProj_mk_eq_iff]
      exact ⟨Units.mk0 a ha0, by rw [hy]; ext i j; fin_cases i <;> fin_cases j <;> simp [diagonal]⟩
    exact hxp.one_lt.ne' (hos ▸ orderOf_eq_one_iff.2 h1)
  have ha3 : a ^ 3 ≠ 1 := fun h3 => hne (by
    calc a = a * (a * a * b) := by rw [hab, mul_one]
      _ = a ^ 3 * b := by ring
      _ = b := by rw [h3, one_mul])
  have ha3s : a ^ (3 * orderOf x) = 1 := by
    calc a ^ (3 * orderOf x) = (a ^ orderOf x) ^ 2 * a ^ orderOf x := by ring
      _ = (a ^ orderOf x) ^ 2 * b ^ orderOf x := by rw [h0, h2']
      _ = (a * a * b) ^ orderOf x := by ring
      _ = 1 := by rw [hab, one_pow]
  have hsd : orderOf x ∣ orderOf a := by
    by_contra hns
    exact ha3 (orderOf_dvd_iff_pow_eq_one.1 ((((hxp.coprime_iff_not_dvd).2 hns).symm
      ).dvd_of_dvd_mul_right (orderOf_dvd_of_pow_eq_one ha3s)))
  have hak : orderOf a ∣ Nat.card K - 1 := by
    have := orderOf_dvd_natCard (Units.mk0 a ha0)
    rwa [← orderOf_units, Units.val_mk0, Nat.card_units] at this
  exact (hsd.trans hak).trans hcard

theorem uc22s2112l3p_exists_sl2_le_centralizer {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp2 : p ≠ 2) (hX : LieModel X .PSL 3 p 1 ∨ LieModel X .PSU 3 p 1) (S : Sylow 2 X) {x : X}
    (hx : x ∈ centralizer (S : Set X)) :
    ∃ Y : Subgroup X, Y ≤ centralizer ({x} : Set X) ∧ Nonempty (↥Y ≃* SL(2, ZMod p)) := by
  obtain ⟨K, _, _, H, h2, hR, hF, -, -, ⟨φ, hφ, hφH⟩, ⟨e⟩⟩ := model_data hp2 hX
  obtain ⟨g, y, a, b, hxy, hy⟩ := exists_diag h2 hR hF e S hx
  let ρ : X ≃* StatedProj H := (MulAut.conj g).trans e
  let β : SL(2, ZMod p) →* H := (blockGL3.comp φ).codRestrict H hφH
  have hβ : Function.Injective
      ((QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf H)).comp β) := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hγ
    exact hφ ((blockGL3_eq_one_of_scalar hγ).trans φ.map_one.symm)
  let ψ : SL(2, ZMod p) →* X := ρ.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp β)
  have hψ : Function.Injective ψ := ρ.symm.injective.comp hβ
  refine ⟨ψ.range, ?_, ⟨(MonoidHom.ofInjective hψ).symm⟩⟩
  rintro _ ⟨γ, rfl⟩
  rw [mem_centralizer_singleton_iff]
  apply ρ.injective
  rw [map_mul, map_mul, show ρ x = (y : StatedProj H) from hxy,
    show ρ (ψ γ) = (β γ : StatedProj H) from ρ.apply_symm_apply _, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  change leviMat _ * _ = _ * leviMat _
  rw [hy]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, Matrix.mul_apply, diagonal, mul_comm]

end CFSG.LocalAnalysis.UniquenessCase.UC22
