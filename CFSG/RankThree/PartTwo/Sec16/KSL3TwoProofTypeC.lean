module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofE
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTools
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofCUL
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC
public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofCore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup conjAut fieldAut
  dualAut mem_linearAutGroup_iff conjAut_mem_linearAutGroup automorphism_generation proj
  conjAut_proj)
open CFSG.LocalAnalysis.ComponentInitial (card_ringAut_and_isCyclic)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitarySU unitaryProj)
open Matrix

namespace ProofKSL3Two

open ProofHess

theorem not_eighty_one_dvd_sl3 {q : ℕ} (hq : q % 3 = 1) (h9 : q % 9 ≠ 1) :
    ¬ 81 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 1 := ⟨q / 3, by omega⟩
  have hb : ¬ 3 ∣ b := by omega
  have h2 : (3 * b + 1) ^ 2 - 1 = 3 * b * (3 * b + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h3 : (3 * b + 1) ^ 3 - 1 = 9 * b * (3 * b ^ 2 + 3 * b + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e : (3 * b + 1) ^ 3 * (3 * b * (3 * b + 2)) * (9 * b * (3 * b ^ 2 + 3 * b + 1)) =
      27 * (b ^ 2 * ((3 * b + 1) ^ 3 * (3 * b + 2) * (3 * b ^ 2 + 3 * b + 1))) := by ring
  rw [h2, h3, e, show (81 : ℕ) = 27 * 3 by norm_num, Nat.mul_dvd_mul_iff_left (by norm_num)]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · exact hb (Nat.prime_three.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · have := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · omega
    · omega

theorem not_eighty_one_dvd_su3 {q : ℕ} (hq : q % 3 = 2) (h9 : q % 9 ≠ 8) :
    ¬ 81 ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 2 := ⟨q / 3, by omega⟩
  have hb : ¬ 3 ∣ b + 1 := by omega
  have h2 : (3 * b + 2) ^ 2 - 1 = 3 * (3 * b + 1) * (b + 1) := Nat.sub_eq_of_eq_add (by ring)
  have e : (3 * b + 2) ^ 3 * (3 * (3 * b + 1) * (b + 1)) * ((3 * b + 2) ^ 3 + 1) =
      27 * ((b + 1) ^ 2 * ((3 * b + 2) ^ 3 * (3 * b + 1) * (3 * b ^ 2 + 3 * b + 1))) := by ring
  rw [h2, e, show (81 : ℕ) = 27 * 3 by norm_num, Nat.mul_dvd_mul_iff_left (by norm_num)]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
  · exact hb (Nat.prime_three.dvd_of_dvd_pow h)
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · have := Nat.prime_three.dvd_of_dvd_pow h
        omega
      · omega
    · omega

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem not_eighty_one_dvd_card_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : ¬ ModNine π (p ^ f)) : ¬ 81 ∣ Nat.card (slPi π 3 (p ^ f) K) := by
  rw [card_slPi_three hK]
  cases π
  · exact not_eighty_one_dvd_su3 hq h9
  · exact not_eighty_one_dvd_sl3 hq h9

theorem card_projImage_glPi (hK : PiField π p f K) :
    Nat.card (projImage (glPi π 3 (p ^ f) K)) = Nat.card (slPi π 3 (p ^ f) K) := by
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set G' := glPi π 3 (p ^ f) K with hG'
  set μ := rootsOfUnity (qSubPi π (p ^ f)) K with hμ
  set δ : ↥G' →* Kˣ := GeneralLinearGroup.det.comp G'.subtype with hδ
  have hδrange : δ.range = μ := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      cases π
      · have h := hK.unitary
        have hx := (mem_glPi_false h).mp x.2
        have h1 := Sec4.det_pow_succ_eq_one (h := h) (A := (x : GL (Fin 3) K)) hx
        rw [mem_rootsOfUnity]
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact h1
      · exact mem_rootsOfUnity_of_card hK.card _
    · intro hu
      refine ⟨⟨diagUnits u 1 1, diagUnits_mem_glPi hK hu (one_mem _) (one_mem _)⟩, ?_⟩
      apply Units.ext
      simp only [hδ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        GeneralLinearGroup.val_det_apply, coe_diagUnits, det_diagonal, Fin.prod_univ_three]
      simp
  have hδker : Nat.card δ.ker = Nat.card (slPi π 3 (p ^ f) K) := by
    have : δ.ker = (slPi π 3 (p ^ f) K).subgroupOf G' := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_slPi_iff hπ]
      simp only [hδ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype]
      constructor
      · intro h1
        refine ⟨x.2, ?_⟩
        rw [← GeneralLinearGroup.val_det_apply, h1, Units.val_one]
      · rintro ⟨-, h1⟩
        exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, h1, Units.val_one])
    rw [this, Proof1617.card_subgroupOf_of_le (slPi_le_glPi hπ)]
  set ν : ↥G' →* ProjGenLinGroup (Fin 3) K := ProjGenLinGroup.mk.comp G'.subtype with hν
  have hνrange : ν.range = projImage G' := by
    rw [hν, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  set sc : ↥μ →* ↥ν.ker :=
    { toFun := fun u => ⟨⟨GeneralLinearGroup.scalar (Fin 3) (u : Kˣ),
        (scalar_mem_glPi_iff hK _).mpr u.2⟩, by
          rw [MonoidHom.mem_ker, hν, MonoidHom.comp_apply, Subgroup.coe_subtype,
            KFacts.mk_eq_one_iff_mem_statedScalars']
          exact ⟨_, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun u v => by
        apply Subtype.ext
        apply Subtype.ext
        simp } with hsc
  have hscbij : Function.Bijective sc := by
    constructor
    · intro u v huv
      have h1 := congrArg (fun x : ↥ν.ker => ((x : ↥G') : GL (Fin 3) K)) huv
      simp only [hsc, MonoidHom.coe_mk, OneHom.coe_mk] at h1
      have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagonal_apply_eq] at h2
      exact Subtype.ext (Units.ext h2)
    · rintro ⟨x, hx⟩
      rw [MonoidHom.mem_ker, hν, MonoidHom.comp_apply, Subgroup.coe_subtype,
        KFacts.mk_eq_one_iff_mem_statedScalars'] at hx
      obtain ⟨c, hc⟩ := hx
      have hcμ : c ∈ μ := (scalar_mem_glPi_iff hK c).mp (hc ▸ x.2)
      refine ⟨⟨c, hcμ⟩, Subtype.ext (Subtype.ext ?_)⟩
      simp only [hsc, MonoidHom.coe_mk, OneHom.coe_mk]
      exact hc
  have hνker : Nat.card ν.ker = Nat.card μ :=
    (Nat.card_congr (MulEquiv.ofBijective sc hscbij).toEquiv).symm
  have h1 := Proof1617.card_eq_card_range_mul_card_ker δ
  have h2 := Proof1617.card_eq_card_range_mul_card_ker ν
  rw [hδrange, hδker] at h1
  rw [hνrange, hνker] at h2
  have hμpos : 0 < Nat.card μ := Nat.card_pos
  have h3 : Nat.card (projImage G') * Nat.card μ = Nat.card (slPi π 3 (p ^ f) K) * Nat.card μ := by
    rw [← h2, h1, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hμpos h3

theorem isTypeC_map_conj {A : Subgroup (GL (Fin 3) K)} (hA : IsTypeC π (p ^ f) K A)
    {h : GL (Fin 3) K} (hh : h ∈ glPi π 3 (p ^ f) K) :
    IsTypeC π (p ^ f) K (A.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨hAH, hA3, hAcard, b, hb, hAb⟩ := hA
  refine ⟨?_, ?_, ?_, fun i => (h : Matrix (Fin 3) (Fin 3) K) *ᵥ b i, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem hh (hAH ha)) (inv_mem hh)
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [_root_.conj_pow]
    obtain ⟨c, hc⟩ := hA3 a ha
    rw [← hc]
    refine ⟨c, ?_⟩
    rw [commute_of_mem_statedScalars ⟨c, rfl⟩ h, mul_inv_cancel_right]
  · have hmap : (A.map (MulAut.conj h).toMonoidHom).map
        (QuotientGroup.mk' (StatedScalars (Fin 3) K)) =
        (A.map (QuotientGroup.mk' (StatedScalars (Fin 3) K))).map
          (MulAut.conj (QuotientGroup.mk' (StatedScalars (Fin 3) K) h)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj _).injective, hAcard]
  · have hinj : Function.Injective (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) K)) := by
      intro v w hvw
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hvw
      have h1 : ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
          ((h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by rw [hvw]
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec] at h1
    show LinearIndependent K ((Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) K)) ∘ b)
    exact hb.map' _ (LinearMap.ker_eq_bot.mpr hinj)
  · rintro _ ⟨a, ha, rfl⟩ i
    obtain ⟨c, hc⟩ := hAb a ha i
    refine ⟨c, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : ((h * a * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (h : Matrix (Fin 3) (Fin 3) K) =
        (h : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_mul, inv_mul_cancel_right]
      rfl
    calc ((h * a * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) =
        (((h * a * h⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (h : Matrix (Fin 3) (Fin 3) K)) *ᵥ b i := Matrix.mulVec_mulVec _ _ _
      _ = ((h : Matrix (Fin 3) (Fin 3) K) * (a : Matrix (Fin 3) (Fin 3) K)) *ᵥ b i := by rw [e]
      _ = (h : Matrix (Fin 3) (Fin 3) K) *ᵥ ((a : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) :=
          (Matrix.mulVec_mulVec _ _ _).symm
      _ = c • ((h : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) := by rw [hc, Matrix.mulVec_smul]

theorem projImage_glPi_le_normalizer (hK : PiField π p f K) :
    projImage (glPi π 3 (p ^ f) K) ≤
      Subgroup.normalizer (projImage (slPi π 3 (p ^ f) K) : Set (ProjGenLinGroup (Fin 3) K)) := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective ProjGenLinGroup.mk (QuotientGroup.mk'_surjective _)
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  rintro _ ⟨g, hg, rfl⟩
  refine Subgroup.mem_normalizer_fintype fun m hm => ?_
  obtain ⟨s, hs, rfl⟩ := hm
  exact ⟨g * s * g⁻¹, conj_mem_slPi hπ hg hs, by simp only [map_mul, map_inv]⟩

theorem conjHom_injective (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) :
    Function.Injective ((projImage (slPi π 3 (p ^ f) K)).normalizerMonoidHom.comp
      (Subgroup.inclusion (projImage_glPi_le_normalizer hK))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨_, ⟨g, hg, rfl⟩⟩ hx
  rw [MonoidHom.mem_ker] at hx
  have hc : ∀ s ∈ slPi π 3 (p ^ f) K,
      ProjGenLinGroup.mk g * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk s * ProjGenLinGroup.mk g := by
    intro s hs
    have h1 := congrArg (fun σ : MulAut (projImage (slPi π 3 (p ^ f) K)) =>
      ((σ ⟨ProjGenLinGroup.mk s, s, hs, rfl⟩ : projImage (slPi π 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K)) hx
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulAut.one_apply] at h1
    have h2 : ProjGenLinGroup.mk g * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk g)⁻¹ =
        ProjGenLinGroup.mk s := h1
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk s =
        ProjGenLinGroup.mk g * ProjGenLinGroup.mk s * (ProjGenLinGroup.mk g)⁻¹ *
          ProjGenLinGroup.mk g := by group
      _ = _ := by rw [h2]
  have hgs := mem_statedScalars_of_commute_mk hK hq hq2 hc
  apply Subtype.ext
  exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr hgs

theorem exists_typeC_of_inndiag (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (h81 : ¬ 81 ∣ Nat.card (slPi π 3 (p ^ f) K))
    {X : Type} [Group X] [Finite X] (φ : X ≃* projImage (slPi π 3 (p ^ f) K))
    (hA : ∀ σ : MulAut (projImage (slPi π 3 (p ^ f) K)), (∃ k : ℕ, σ ^ 3 ^ k = 1) →
      ∃ y ∈ glPi π 3 (p ^ f) K, ∀ m : projImage (slPi π 3 (p ^ f) K),
        ((σ m : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹)
    (P : Subgroup (MulAut X)) (hP3 : IsPGroup 3 P) (hP27 : Nat.card P = 27) :
    ∃ P₀ : Subgroup (MulAut X), P₀ ≤ P ∧ Nat.card P₀ = 9 ∧
      ∃ D : Subgroup (GL (Fin 3) K), IsTypeC π (p ^ f) K D ∧
        (∀ τ ∈ P₀, ∃ y ∈ D, ∀ z : X,
          ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
            ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) *
              (ProjGenLinGroup.mk y)⁻¹) ∧
        ∀ y ∈ D, ∃ τ ∈ P₀, ∀ z : X,
          ((φ (τ z) : ProjGenLinGroup (Fin 3) K)) =
            ProjGenLinGroup.mk y * (φ z : ProjGenLinGroup (Fin 3) K) *
              (ProjGenLinGroup.mk y)⁻¹ := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective ProjGenLinGroup.mk (QuotientGroup.mk'_surjective _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := projImage (glPi π 3 (p ^ f) K) with hH
  set Γ : ↥H →* MulAut ↥(projImage (slPi π 3 (p ^ f) K)) :=
    (projImage (slPi π 3 (p ^ f) K)).normalizerMonoidHom.comp
      (Subgroup.inclusion (projImage_glPi_le_normalizer hK)) with hΓ
  have hΓapp : ∀ (h : ↥H) (m : ↥(projImage (slPi π 3 (p ^ f) K))),
      ((Γ h m : ↥(projImage (slPi π 3 (p ^ f) K))) : ProjGenLinGroup (Fin 3) K) =
        (h : ProjGenLinGroup (Fin 3) K) * m * (h : ProjGenLinGroup (Fin 3) K)⁻¹ := fun h m => rfl
  have hΓinj : Function.Injective Γ := conjHom_injective hK hq hq2
  set c : MulAut X ≃* MulAut ↥(projImage (slPi π 3 (p ^ f) K)) := MulAut.congr φ with hc
  have hcapp : ∀ (τ : MulAut X) (z : X), c τ (φ z) = φ (τ z) := fun τ z => by
    simp [hc, MulAut.congr_apply]
  set P' := P.map c.toMonoidHom with hP'
  have hP'3 : IsPGroup 3 P' := hP3.map _
  have hP'27 : Nat.card P' = 27 := by rw [hP', Subgroup.card_map_of_injective c.injective, hP27]
  have hP'Γ : P' ≤ Γ.range := by
    intro σ hσ
    obtain ⟨k, hk⟩ := hP'3 ⟨σ, hσ⟩
    have hk' : σ ^ 3 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    obtain ⟨y, hy, hσy⟩ := hA σ ⟨k, hk'⟩
    refine ⟨⟨ProjGenLinGroup.mk y, y, hy, rfl⟩, ?_⟩
    ext m
    rw [hΓapp, hσy]
  set Pt := P'.comap Γ with hPt
  have hPtmap : Pt.map Γ = P' := Subgroup.map_comap_eq_self hP'Γ
  have hPt27 : Nat.card Pt = 27 := by
    rw [← hP'27, ← hPtmap, Subgroup.card_map_of_injective hΓinj]
  have hPt3 : IsPGroup 3 Pt := IsPGroup.of_card (n := 3) (by rw [hPt27]; norm_num)
  have hH81 : ¬ 81 ∣ Nat.card ↥H := by rw [hH, card_projImage_glPi hK]; exact h81
  obtain ⟨S, hS⟩ := hPt3.exists_le_sylow
  have hSeq : (S : Subgroup ↥H) = Pt := by
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
    have hdvd : Nat.card (S : Subgroup ↥H) ∣ Nat.card ↥H := Subgroup.card_subgroup_dvd_card _
    have hge : 27 ≤ Nat.card (S : Subgroup ↥H) := by
      rw [← hPt27]
      exact Subgroup.card_le_of_le hS
    have hk3 : k = 3 := by
      rw [hk] at hdvd hge
      have hk4 : k < 4 := by
        by_contra h4
        push Not at h4
        exact hH81 (dvd_trans (pow_dvd_pow 3 h4) hdvd)
      have hk3 : 3 ≤ k := by
        by_contra h3
        push Not at h3
        have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      omega
    rw [hk3] at hk
    exact (Subgroup.eq_of_le_of_card_ge hS (by rw [hk, hPt27]; norm_num)).symm
  have hstd := isTypeC_stdTypeC hK hq
  set C₀ : Subgroup ↥H := ((stdTypeC K).map ProjGenLinGroup.mk).subgroupOf H with hC₀
  have hC₀3 : IsPGroup 3 C₀ := by
    rintro ⟨x, hx⟩
    refine ⟨1, ?_⟩
    obtain ⟨d, hd, hdx⟩ := Subgroup.mem_subgroupOf.mp hx
    have h3 : d ^ 3 ∈ StatedScalars (Fin 3) K := hstd.2.1 d hd
    apply Subtype.ext
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hdx, ← map_pow]
    exact KFacts.mk_eq_one_iff_mem_statedScalars'.mpr h3
  obtain ⟨x, hx⟩ := KFacts.exists_conj_mem_sylow S hC₀3
  obtain ⟨h, hh, hhx⟩ := x.2
  set D := (stdTypeC K).map (MulAut.conj h).toMonoidHom with hD
  have hDC : IsTypeC π (p ^ f) K D := isTypeC_map_conj hstd hh
  have hDH : ∀ y ∈ D, ProjGenLinGroup.mk y ∈ H := fun y hy => ⟨y, hDC.1 hy, rfl⟩
  have hDPt : ∀ y (hy : y ∈ D), (⟨ProjGenLinGroup.mk y, hDH y hy⟩ : ↥H) ∈ Pt := by
    rintro _ ⟨d, hd, rfl⟩
    have h1 := hx ⟨ProjGenLinGroup.mk d, ⟨d, hstd.1 hd, rfl⟩⟩
      (Subgroup.mem_subgroupOf.mpr ⟨d, hd, rfl⟩)
    rw [hSeq] at h1
    convert h1 using 1
    apply Subtype.ext
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      map_mul, map_inv, ← hhx]
  set Dt : Subgroup ↥H := (D.map ProjGenLinGroup.mk).subgroupOf H with hDt
  set P₀ : Subgroup (MulAut X) := (Dt.map Γ).map c.symm.toMonoidHom with hP₀
  have hDtPt : Dt ≤ Pt := by
    rintro ⟨_, hz⟩ hzD
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_subgroupOf.mp hzD
    have := hDPt y hy
    convert this using 1
    exact Subtype.ext hyz.symm
  have hDt9 : Nat.card Dt = 9 := by
    rw [hDt, Proof1617.card_subgroupOf_of_le (fun z hz => by
      obtain ⟨y, hy, rfl⟩ := hz
      exact hDH y hy)]
    rw [← hDC.2.2.1]
    have hker : (ProjGenLinGroup.mk.comp D.subtype).ker =
        ((QuotientGroup.mk' (StatedScalars (Fin 3) K)).comp D.subtype).ker := by
      ext y
      simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        Subgroup.coe_subtype, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        KFacts.mk_eq_one_iff_mem_statedScalars']
    have h1 := card_range_eq_of_ker_eq _ _ hker
    rwa [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype] at h1
  refine ⟨P₀, ?_, ?_, D, hDC, ?_, ?_⟩
  ·
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    have h1 : Γ z ∈ P' := hDtPt hz
    obtain ⟨τ, hτ, hτz⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom] at hτz ⊢
    rw [← hτz, MulEquiv.symm_apply_apply]
    exact hτ
  ·
    rw [hP₀, Subgroup.card_map_of_injective c.symm.injective,
      Subgroup.card_map_of_injective hΓinj, hDt9]
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_subgroupOf.mp hz
    refine ⟨y, hy, fun w => ?_⟩
    have h1 := hcapp (c.symm (Γ z)) w
    rw [MulEquiv.apply_symm_apply] at h1
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← h1, hΓapp, ← hyz]
  · intro y hy
    set z : ↥H := ⟨ProjGenLinGroup.mk y, hDH y hy⟩ with hz
    refine ⟨c.symm (Γ z), ⟨Γ z, ⟨z, Subgroup.mem_subgroupOf.mpr ⟨y, hy, rfl⟩, rfl⟩, rfl⟩,
      fun w => ?_⟩
    have h1 := hcapp (c.symm (Γ z)) w
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← h1, hΓapp]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (standard_automorphism_transport)

theorem inndiag_of_three_pow_linear {n : ℕ} (hn : 2 ≤ n) (hn3 : ¬ 3 ∣ n)
    (σ : MulAut (projImage (slPi true 3 (2 ^ n) (GaloisField 2 n))))
    (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) :
    ∃ y ∈ glPi true 3 (2 ^ n) (GaloisField 2 n),
      ∀ m : projImage (slPi true 3 (2 ^ n) (GaloisField 2 n)),
        ((σ m : projImage (slPi true 3 (2 ^ n) (GaloisField 2 n))) :
          ProjGenLinGroup (Fin 3) (GaloisField 2 n)) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
  set K := GaloisField 2 n with hKdef
  have hKc : Nat.card K = 2 ^ n := GaloisField.card 2 n (by omega)
  set ψ := pslEquivProjective (2 ^ n) K with hψ
  set α := MulAut.congr ψ σ with hα
  obtain ⟨k, hk⟩ := hσ
  have hαk : α ^ 3 ^ k = 1 := by rw [hα, ← map_pow, hk, map_one]
  have : (linearAutGroup 3 K).Normal := (KFacts.stdPinnedPSL_stable (by norm_num)).normal
  have hcop : Nat.Coprime (3 ^ k) (2 * n) := Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (fun h => by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · omega
      · exact hn3 h))
  have hαI : α ∈ linearAutGroup 3 K := by
    refine mem_of_pow_mem_of_coprime _ hcop (by rw [hαk]; exact one_mem _) ?_
    obtain ⟨-, hform⟩ := automorphism_generation (K := K) (n := 3) (by norm_num)
    obtain ⟨A, τ, ε, -, hαA⟩ := hform α
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hαA, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup A),
      one_mul, (show Commute _ _ from quotient_linearAutGroup_comm _ _).mul_pow]
    have hτn : τ ^ n = 1 := by
      have h := pow_card_eq_one' (G := RingAut K) (x := τ)
      rwa [(card_ringAut_and_isCyclic Nat.prime_two K hKc).1] at h
    have hδ2 : dualAut 3 K ^ 2 = 1 := by
      rw [sq]
      exact (standard_automorphism_transport (n := 3) (K := K)).2.2.2.1
    have hτ2n : fieldAut 3 K τ ^ (2 * n) = 1 := by
      rw [← map_pow, mul_comm, pow_mul, hτn, one_pow, map_one]
    have hδ2n : (dualAut 3 K ^ ε) ^ (2 * n) = 1 := by
      rw [← pow_mul, mul_comm ε, pow_mul, pow_mul, hδ2, one_pow, one_pow]
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, hτ2n, hδ2n, QuotientGroup.mk_one, mul_one]
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hαI
  refine ⟨A, mem_glPi_true _ _, fun m => ?_⟩
  obtain ⟨s, rfl⟩ := slToPsl_surjective (K := K) (2 ^ n) m
  have hproj : ∀ t : SpecialLinearGroup (Fin 3) K, ψ.symm (proj 3 K t) = slToPsl (2 ^ n) K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  have hσs : σ (slToPsl (2 ^ n) K s) = ψ.symm (α (proj 3 K s)) := by
    have h1 : α (proj 3 K s) = ψ (σ (ψ.symm (proj 3 K s))) := rfl
    rw [h1, MulEquiv.symm_apply_apply, hproj]
  rw [hσs, ← hA, conjAut_proj, hproj, coe_slToPsl, coe_slToPsl,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul,
    map_inv]

theorem inndiag_of_three_pow_unitary {n : ℕ} (hn : 2 ≤ n) (hn3 : ¬ 3 ∣ n)
    (σ : MulAut (projImage (slPi false 3 (2 ^ n) (GaloisField 2 (2 * n)))))
    (hσ : ∃ k : ℕ, σ ^ 3 ^ k = 1) :
    ∃ y ∈ glPi false 3 (2 ^ n) (GaloisField 2 (2 * n)),
      ∀ m : projImage (slPi false 3 (2 ^ n) (GaloisField 2 (2 * n))),
        ((σ m : projImage (slPi false 3 (2 ^ n) (GaloisField 2 (2 * n)))) :
          ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) =
          ProjGenLinGroup.mk y * m * (ProjGenLinGroup.mk y)⁻¹ := by
  set K := GaloisField 2 (2 * n) with hKdef
  have hKc : Nat.card K = 2 ^ (2 * n) := GaloisField.card 2 _ (by omega)
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, by omega, hKc⟩
  have := h.finite
  have hq2 : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  set ψ := psuEquivUnitary h with hψ
  set α := MulAut.congr ψ σ with hα
  obtain ⟨k, hk⟩ := hσ
  have hαk : α ^ 3 ^ k = 1 := by rw [hα, ← map_pow, hk, map_one]
  have : ((KFacts.psuConj h).range).Normal := (KFacts.stdPinnedPSU3_stable hq2).normal
  have hcop : Nat.Coprime (3 ^ k) (2 * n) := Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (fun h => by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · omega
      · exact hn3 h))
  have hαI : α ∈ (KFacts.psuConj h).range := by
    refine mem_of_pow_mem_of_coprime _ hcop (by rw [hαk]; exact one_mem _) ?_
    obtain ⟨A, τ, hαA⟩ := KFacts.exists_psuConj_mul_psuField hq2 α
    have hτ : τ ^ (2 * n) = 1 := by
      have h1 := pow_card_eq_one' (G := RingAut K) (x := τ)
      rwa [(card_ringAut_and_isCyclic Nat.prime_two K hKc).1] at h1
    have hA1 : KFacts.psuConj h A ∈ (KFacts.psuConj h).range := ⟨A, rfl⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hαA, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr hA1, one_mul, ← QuotientGroup.mk_pow, ← map_pow, hτ,
      map_one]
    rfl
  obtain ⟨A, hA⟩ := hαI
  refine ⟨A, (mem_glPi_false h).mpr A.2, fun m => ?_⟩
  obtain ⟨s, rfl⟩ := suToPsu_surjective (p := 2) (f := n) (K := K) m
  have hproj : ∀ t : unitarySU 2 n K 3, ψ.symm (unitaryProj h 3 t) = suToPsu 2 n K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  have hσs : σ (suToPsu 2 n K s) = ψ.symm (α (unitaryProj h 3 s)) := by
    have h1 : α (unitaryProj h 3 s) = ψ (σ (ψ.symm (unitaryProj h 3 s))) := rfl
    rw [h1, MulEquiv.symm_apply_apply, hproj]
  rw [hσs, ← hA, psuConj_unitaryProj, hproj, coe_suToPsu, coe_suToPsu, KFacts.coe_suConj,
    map_mul, map_mul, Subgroup.coe_inv, map_inv]

end ProofKSL3Two

open ProofKSL3Two in
theorem kS1617TypeC_two :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → ¬ 3 ∣ n → Sec4.IsoLThreePi X 2 n →
      ∀ P : Subgroup (MulAut X), IsPGroup 3 P → Nat.card P = 27 →
        ∃ P₀ : Subgroup (MulAut X), P₀ ≤ P ∧ Nat.card P₀ = 9 ∧
          ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : Sec4.PiField π p f K)
            (_ : Sec4.ModThree π (p ^ f)) (e : X ≃* projImage (Sec4.slPi π 3 (p ^ f) K))
            (D : Subgroup (GL (Fin 3) K)), Sec4.IsTypeC π (p ^ f) K D ∧
            (∀ τ ∈ P₀, ∃ y ∈ D, ∀ z : X,
              ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
                ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) *
                  (ProjGenLinGroup.mk y)⁻¹) ∧
            ∀ y ∈ D, ∃ τ ∈ P₀, ∀ z : X,
              ((e (τ z) : ProjGenLinGroup (Fin 3) K)) =
                ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) *
                  (ProjGenLinGroup.mk y)⁻¹ := by
  intro X _ _ n hn2 hn3 hX P hP3 hP27
  have hn : 1 ≤ n := by omega
  have hq2 : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn2)
  have h9 := not_two_pow_mod_nine hn3
  rcases hX with ⟨h3, ⟨e⟩⟩ | ⟨h3, ⟨e⟩⟩
  · have hK : PiField true 2 n (GaloisField 2 n) :=
      ⟨Nat.prime_two, hn, by rw [GaloisField.card 2 n (by omega)]; rfl⟩
    have hq : ModThree true (2 ^ n) := h3
    have h81 := not_eighty_one_dvd_card_slPi hK hq (fun h => h9 (Or.inl h))
    set φ := e.trans (MulEquiv.subgroupCongr (projSL_eq_projImage (2 ^ n) (GaloisField 2 n)))
      with hφ
    obtain ⟨P₀, hP₀P, hP₀9, D, hD, hτD, hDτ⟩ := exists_typeC_of_inndiag hK hq hq2 h81 φ
      (inndiag_of_three_pow_linear hn2 hn3) P hP3 hP27
    exact ⟨P₀, hP₀P, hP₀9, true, 2, n, GaloisField 2 n, inferInstance, hK, hq, φ, D, hD, hτD,
      hDτ⟩
  · have hK : PiField false 2 n (GaloisField 2 (2 * n)) :=
      ⟨Nat.prime_two, hn, by
        rw [GaloisField.card 2 _ (by omega)]
        change 2 ^ (2 * n) = (2 ^ n) ^ 2
        rw [← pow_mul, mul_comm]⟩
    have hq : ModThree false (2 ^ n) := h3
    have h81 := not_eighty_one_dvd_card_slPi hK hq (fun h => h9 (Or.inr h))
    set φ := e.trans (MulEquiv.subgroupCongr (projSU_eq_projImage 2 n)) with hφ
    obtain ⟨P₀, hP₀P, hP₀9, D, hD, hτD, hDτ⟩ := exists_typeC_of_inndiag hK hq hq2 h81 φ
      (inndiag_of_three_pow_unitary hn2 hn3) P hP3 hP27
    exact ⟨P₀, hP₀P, hP₀9, false, 2, n, GaloisField 2 (2 * n), inferInstance, hK, hq, φ, D, hD,
      hτD, hDτ⟩

end CFSG.RankThree.PartTwo.Sec16
