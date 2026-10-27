module

public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
open scoped Pointwise commutatorElement

section RankOne

variable {τ : Tag} {L : Type} [Field L]

theorem exists_twistedEntrywise_rootSL2 {z : ModGL τ L} (hz : z ∈ monomialSubgroup τ L)
    (hw : ∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨z, hz⟩ • v = -v) (σ : L ≃+* L)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ a b : Lˣ,
      (∀ c, twistedEntrywise z (σ : L →+* L) (rootSL2 τ L α (uSL c)) =
        rootSL2 τ L α (vSL (a * σ c))) ∧
      ∀ c, twistedEntrywise z (σ : L →+* L) (rootSL2 τ L α (vSL c)) =
        rootSL2 τ L α (uSL (b * σ c)) := by
  obtain ⟨s, hs, hsz⟩ := exists_unit_zsmul_eq_mul (K := L) (pinnedSign_eq τ α)
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := L) hα
  obtain ⟨μ, hμ⟩ := conj_pinnedX_of_smul_eq_neg hz hw hα
  obtain ⟨μ', hμ'⟩ := conj_pinnedX_of_smul_eq_neg hz hw (IsRoot.neg hα)
  have hmapu : ∀ c, Matrix.SpecialLinearGroup.map (σ : L →+* L) (uSL c) = uSL (σ c) :=
    fun c => map_sl2Upper σ c
  have hmapv : ∀ c, Matrix.SpecialLinearGroup.map (σ : L →+* L) (vSL c) = vSL (σ c) :=
    fun c => map_sl2Lower σ c
  have hss : (s : L) * s = 1 := by rw [← Units.val_mul, hs, Units.val_one]
  refine ⟨Units.mkOfMulEqOne ε ε hε * μ * s, s * μ' * Units.mkOfMulEqOne ε ε hε,
    fun c => ?_, fun c => ?_⟩
  · rw [twistedEntrywise_apply, entrywise_rootSL2_of_field, hmapu, rootSL2_uSL_eq, hsz, hμ, hv]
    congr 1
    simp only [Units.val_mul, Units.val_mkOfMulEqOne]
    linear_combination (-(μ * s * σ c : L)) * hε
  · rw [twistedEntrywise_apply, entrywise_rootSL2_of_field, hmapv, hv, hμ', neg_neg,
      rootSL2_uSL_eq, hsz]
    congr 1
    simp only [Units.val_mul, Units.val_mkOfMulEqOne]
    linear_combination (-(μ' * ε * σ c : L)) * hss

theorem exists_semilinearConj_rootSL2 {z : ModGL τ L} (hz : z ∈ monomialSubgroup τ L)
    (hw : ∀ v : Fin τ.rank → ℤ, weylQuotientHom τ L ⟨z, hz⟩ • v = -v) (σ : L ≃+* L)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    ∃ M : GL (Fin 2) L, ∀ A, rootSL2 τ L α (semilinearConj M σ A) =
      twistedEntrywise z (σ : L →+* L) (rootSL2 τ L α A) := by
  obtain ⟨a, b, hu, hl⟩ := exists_twistedEntrywise_rootSL2 hz hw σ hα
  have hinj : Function.Injective (rootSL2 τ L α) := rootSL2_injective_of_field α
  have hmem : ∀ A, twistedEntrywise z (σ : L →+* L) (rootSL2 τ L α A) ∈
      (rootSL2 τ L α).range := by
    have hle : (⊤ : Subgroup (SL2 L)) ≤ (rootSL2 τ L α).range.comap
        ((twistedEntrywise z (σ : L →+* L)).comp (rootSL2 τ L α)) := by
      rw [← sl2_closure_upper_lower, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨vSL (a * σ c), (hu c).symm⟩
      · exact ⟨uSL (b * σ c), (hl c).symm⟩
    exact fun A => hle (Subgroup.mem_top A)
  let T : SL2 L →* SL2 L := (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
    (((twistedEntrywise z (σ : L →+* L)).comp (rootSL2 τ L α)).codRestrict _ hmem)
  have hT : ∀ A, rootSL2 τ L α (T A) = twistedEntrywise z (σ : L →+* L) (rootSL2 τ L α A) :=
    fun A => by
      rw [← MonoidHom.ofInjective_apply hinj]
      change ((MonoidHom.ofInjective hinj ((MonoidHom.ofInjective hinj).symm _)) :
        ModGL τ L) = _
      rw [MulEquiv.apply_symm_apply]
      rfl
  have hTu : ∀ c, T (sl2Upper L c) = sl2Lower L (a * σ c) := fun c => hinj (by
    rw [hT]
    exact hu c)
  have hTl : ∀ c, T (sl2Lower L c) = sl2Upper L (b * σ c) := fun c => hinj (by
    rw [hT]
    exact hl c)
  obtain ⟨-, M, -, hM⟩ := sl2_semilinear_exchanged_root_compatibility σ a b T hTu hTl
  refine ⟨M, fun A => ?_⟩
  have hTA : T A = semilinearConj M σ A := Subtype.ext (by rw [hM A]; rfl)
  rw [← hTA, hT]

theorem conjSL_toGL (B A : SL2 L) :
    conjSL (Matrix.SpecialLinearGroup.toGL B) A = B * A * B⁻¹ := by
  apply Subtype.ext
  rw [coe_conjSL, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]

theorem exists_conj_rootSL2_eq_conjSL {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {y : ModGL τ L}
    (hy : y ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootRankOneGroup τ L α : Set (ModGL τ L))) :
    ∃ X : GL (Fin 2) L, ∀ A, y * rootSL2 τ L α A * y⁻¹ = rootSL2 τ L α (conjSL X A) := by
  obtain ⟨h, hh, u, hu, rfl⟩ := hy
  obtain ⟨B, rfl⟩ := MonoidHom.mem_range.1 hu
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  refine ⟨diagUnitOne (rootChar c α) * Matrix.SpecialLinearGroup.toGL B, fun A => ?_⟩
  rw [conjSL_mul, conjSL_toGL, ← rootDiagUnit_conj_rootSL2 c hα, map_mul, map_mul, map_inv]
  group

theorem commute_rootSL2_of_commute_fixed {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    {S : Subgroup (SL2 L)}
    (hS : Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) L)) :
      Set (GL (Fin 2) L)) = (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    {y : ModGL τ L}
    (hy : y ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootRankOneGroup τ L α : Set (ModGL τ L)))
    (hc : ∀ A ∈ S, y * rootSL2 τ L α A = rootSL2 τ L α A * y) (A : SL2 L) :
    y * rootSL2 τ L α A = rootSL2 τ L α A * y := by
  obtain ⟨X, hX⟩ := exists_conj_rootSL2_eq_conjSL hα hy
  have hinj : Function.Injective (rootSL2 τ L α) := rootSL2_injective_of_field α
  have hXS : X ∈ Subgroup.centralizer ((S.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B, hB, rfl⟩
    have h1 : conjSL X B = B := hinj (by rw [← hX, hc B hB, mul_inv_cancel_right])
    have h2 := commute_of_conjSL_eq X h1
    ext1
    rw [Units.val_mul, Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact h2.symm
  rw [hS] at hXS
  obtain ⟨u, rfl⟩ := hXS
  have h := hX A
  rw [conjSL_scalar] at h
  exact mul_inv_eq_iff_eq_mul.1 h

end RankOne

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂]

theorem rootSL2_comap_fixed_eq (hK : Odd (Nat.card K)) (hdeg : Module.finrank K K₂ = 2)
    (σ : K₂ ≃+* K₂) (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂}
    (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v)
    {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) :
    ∃ P : GL (Fin 2) K₂,
      (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .G2 K₂ α) =
        (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P) ∧
      Subgroup.centralizer ((((rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap
          (rootSL2 .G2 K₂ α)).map Matrix.SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) K₂)) :
            Set (GL (Fin 2) K₂)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  obtain ⟨M, hM⟩ := exists_semilinearConj_rootSL2 hz hw σ hα
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hinv : ∀ c, σ (σ c) = c := (exists_frobenius_eq_neg hdeg σ hσ).1
  have hinj : Function.Injective (rootSL2 .G2 K₂ α) := rootSL2_injective_of_field α
  have hinvol : ∀ A, semilinearConj M σ (semilinearConj M σ A) = A := fun A => hinj (by
    rw [hM, hM, twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv hzdef])
  have hfix : (semilinearConj M σ).eqLocus (MonoidHom.id _) =
      (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .G2 K₂ α) := by
    ext A
    change semilinearConj M σ A = A ↔
      rootSL2 .G2 K₂ α A ∈ rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g
    rw [hΓ]
    constructor
    · intro h
      refine ⟨⟨A, rfl⟩, (exceptional_Lang_root_rank_one_data .G2 K₂ α).2.2.2.2.1 A, ?_⟩
      change twistedEntrywise z (σ : K₂ →+* K₂) (rootSL2 .G2 K₂ α A) = rootSL2 .G2 K₂ α A
      rw [← hM, h]
    · rintro ⟨-, -, h⟩
      exact hinj (by rw [hM]; exact h)
  obtain ⟨P, -, hP, -, hcent⟩ :=
    even_quadratic_semilinear_SL2_fixed_matrix_group K K₂ hdeg σ hσ M hinvol
  refine ⟨P, ?_, ?_⟩
  · rw [← hfix]
    exact hP
  · rw [← hfix]
    exact hcent

theorem isQuasisimple_of_rootSL2_comap_eq (hK4 : 4 ≤ Nat.card K) {α : Fin Tag.G2.rank → ℤ}
    {R : Subgroup (ModGL .G2 K₂)} (hR : R ≤ rootRankOneGroup .G2 K₂ α) {P : GL (Fin 2) K₂}
    (hRP : R.comap (rootSL2 .G2 K₂ α) =
      (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P)) :
    CFSG.IsQuasisimple R := by
  have hSLinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2)
      (algebraMap K K₂)) := by
    intro A B h
    ext i j
    have h1 := congrArg (fun X : SL2 K₂ => (X : Matrix (Fin 2) (Fin 2) K₂) i j) h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at h1
    exact (algebraMap K K₂).injective h1
  have hPinj : Function.Injective (conjSL P) := fun A B h => by
    have h1 := congrArg (conjSL P⁻¹) h
    rwa [← conjSL_mul, ← conjSL_mul, inv_mul_cancel, conjSL_one, conjSL_one] at h1
  have hinj : Function.Injective (rootSL2 .G2 K₂ α) := rootSL2_injective_of_field α
  have hmap : (R.comap (rootSL2 .G2 K₂ α)).map (rootSL2 .G2 K₂ α) = R := by
    rw [Subgroup.map_comap_eq]
    exact inf_of_le_right hR
  let e : SL2 K ≃* R :=
    ((((MonoidHom.ofInjective hSLinj).trans (Subgroup.equivMapOfInjective _ _ hPinj)).trans
      (MulEquiv.subgroupCongr hRP.symm)).trans
        (Subgroup.equivMapOfInjective _ _ hinj)).trans (MulEquiv.subgroupCongr hmap)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (isQuasisimple_SL2 (exists_finset_card_four hK4))

theorem comm_and_two_generated_of_injective_torusGroup {L : Type} [Field L] [Finite L]
    {G : Type*} [Group G] (f : G →* ModGL .G2 L) (hf : Function.Injective f)
    (hT : ∀ x, f x ∈ torusGroup .G2 L) (S : Subgroup G) :
    (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤ := by
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) L
  have hcod : Function.Injective (f.codRestrict _ hT) := fun a b h => hf (congrArg Subtype.val h)
  exact comm_and_two_generated_of_injective
    (e.symm.toMonoidHom.comp ((f.codRestrict _ hT).comp S.subtype))
    (e.symm.injective.comp (hcod.comp S.subtype_injective))

theorem commutator_self_le {G : Type*} [Group G] (D : Subgroup G) : ⁅D, D⁆ ≤ D :=
  Subgroup.commutator_le.2 fun x hx y hy => by
    rw [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hx hy) (D.inv_mem hx)) (D.inv_mem hy)

theorem qplus_prime_element_centralizer (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1) (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {g z : ModGL .G2 K₂} (hg : g ∈ adjointGroup .G2 K₂)
    (hzdef : z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹)
    (hz : z ∈ monomialSubgroup .G2 K₂)
    (hw : ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v)
    (a : Fin Tag.G2.rank → K₂ˣ) (ha : orderOf (rootDiagUnit .G2 a) = p) :
    (rootCharKernel a = ∅ →
      conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} =
        torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g ∧
      (∀ x ∈ conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
        ∀ y ∈ conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
          x * y = y * x) ∧
      ∀ S : Sylow 2 (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} :
          Subgroup (ModGL .G2 K₂)),
        (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) ∧
    (rootCharKernel a ≠ ∅ → ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧
      rootCharKernel a = {α, -α} ∧
      ⁅conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
          conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}⁆ =
        rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g ∧
      (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}) ⊓
          Subgroup.centralizer ((rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g :
            Subgroup (ModGL .G2 K₂)) : Set (ModGL .G2 K₂)) =
        (Subgroup.center (conjEntrywiseImage K g ⊓
          Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))).map
          (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}).subtype ∧
      (Subgroup.center (conjEntrywiseImage K g ⊓
          Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))).map
          (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}).subtype ≤
        torusGroup .G2 K₂ ∧
      ∀ S : Sylow 2 (Subgroup.center (conjEntrywiseImage K g ⊓
          Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))),
        (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hodd₂ : Odd (Nat.card K₂) := by
    rw [hq2]
    exact hK.pow
  have hpq₂ : p ∣ Nat.card K₂ - 1 := by
    refine hpq.trans ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hq4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have := five_le_of_prime_of_three_lt hp hp3
    omega
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hΓC : conjEntrywiseImage K g ≤ adjointGroup .G2 K₂ := by
    rw [hΓ]
    exact inf_le_left
  have hHcomm := (triangular_borel_structure.{0, 0} .G2 K₂).1
  have hDM : conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} =
      conjEntrywiseImage K g ⊓ toralCentralizer .G2 K₂ a := by
    rw [toralCentralizer, ← inf_assoc, inf_of_le_left hΓC]
  have hcases := toral_centralizer_cases_G2 K₂ hodd₂ hp hp3 hpq₂ a ha
  set D := conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} with hDdef
  constructor
  · intro hker
    rcases hcases with ⟨⟨-, hMH, -⟩, -⟩ | ⟨⟨α, -, hα, -⟩, -⟩
    · have hD : D = torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g := by
        rw [hDM, hMH, inf_comm]
      have hDH : ∀ x ∈ D, x ∈ torusGroup .G2 K₂ := fun x hx => by
        rw [hD] at hx
        exact hx.1
      refine ⟨hD, fun x hx y hy => hHcomm x (hDH x hx) y (hDH y hy), fun S => ?_⟩
      exact comm_and_two_generated_of_injective_torusGroup D.subtype D.subtype_injective
        (fun x => hDH x x.2) (S : Subgroup D)
    · exact absurd (hα.symm.trans hker) (Set.insert_nonempty _ _).ne_empty
  · intro hker
    rcases hcases with ⟨⟨hker', -, -⟩, -⟩ |
      ⟨⟨α, hαr, hkerα, hMQ, hMset, -, -, hMcomm, hMZ, hMZH, -⟩, -⟩
    · exact absurd hker' hker
    set M := toralCentralizer .G2 K₂ a with hMdef
    have hL : rootRankOneGroup .G2 K₂ α = rootSubgroup .G2 K₂ α ⊔ rootSubgroup .G2 K₂ (-α) :=
      (exceptional_Lang_root_rank_one_torus_transport .G2 K₂ hαr).1
    rw [← hL] at hMQ hMset hMcomm hMZ
    obtain ⟨P, hPfix, hPcent⟩ := rootSL2_comap_fixed_eq hK hdeg σ hσ hg hzdef hz hw hαr
    set R := rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g with hRdef
    have hRq : CFSG.IsQuasisimple R := isQuasisimple_of_rootSL2_comap_eq hq4 inf_le_left hPfix
    have hRperf : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.1 hRq.1
    have hQM : rootRankOneGroup .G2 K₂ α ≤ M := by
      rw [hMQ]
      exact le_sup_right
    have hDle : D ≤ M := by
      rw [hDM]
      exact inf_le_right
    have hRD : R ≤ D := by
      intro r hr
      rw [hDM]
      exact ⟨hr.2, hQM hr.1⟩
    have hcentM : ∀ y ∈ D, (∀ r ∈ R, r * y = y * r) → y ∈ (Subgroup.center M).map M.subtype := by
      intro y hyD hyR
      have hyM := hDle hyD
      have hyset : y ∈ (torusGroup .G2 K₂ : Set (ModGL .G2 K₂)) *
          (rootRankOneGroup .G2 K₂ α : Set (ModGL .G2 K₂)) := by
        rw [← hMset]
        exact hyM
      have hyQ := commute_rootSL2_of_commute_fixed hαr hPcent hyset
        (fun A hA => (hyR _ hA).symm)
      rw [← hMZ]
      refine ⟨hyM, Subgroup.mem_centralizer_iff.2 fun q hq => ?_⟩
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hq
      exact (hyQ A).symm
    have hcentD : D ⊓ Subgroup.centralizer (R : Set (ModGL .G2 K₂)) =
        (Subgroup.center D).map D.subtype := by
      refine le_antisymm (fun y hy => ?_) ?_
      · obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
        obtain ⟨m, hm, rfl⟩ := hcentM y hyD fun r hr => Subgroup.mem_centralizer_iff.1 hyC r hr
        refine ⟨⟨m, hyD⟩, Subgroup.mem_center_iff.2 fun d => Subtype.ext ?_, rfl⟩
        have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hm ⟨d, hDle d.2⟩)
        exact h1
      · rintro _ ⟨d, hd, rfl⟩
        refine ⟨d.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hd ⟨r, hRD hr⟩)
    have hZH : (Subgroup.center D).map D.subtype ≤ torusGroup .G2 K₂ := by
      rw [← hcentD]
      intro y hy
      obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
      exact hMZH (hcentM y hyD fun r hr => Subgroup.mem_centralizer_iff.1 hyC r hr)
    refine ⟨α, hαr, hkerα, le_antisymm (le_inf ?_ ?_)
      (hRperf.symm.le.trans (Subgroup.commutator_mono hRD hRD)), hcentD, hZH, fun S => ?_⟩
    · rw [← hMcomm]
      exact Subgroup.commutator_mono hDle hDle
    · exact (commutator_self_le D).trans inf_le_left
    · exact comm_and_two_generated_of_injective_torusGroup
        (D.subtype.comp (Subgroup.center D).subtype)
        (D.subtype_injective.comp (Subgroup.center D).subtype_injective)
        (fun x => hZH ⟨x, x.2, rfl⟩) (S : Subgroup (Subgroup.center D))


theorem odd_G2_qplus_toral_Sylow_and_fixed_root_centralizers (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K + 1)
    (K₂ : Type) [Field K₂] [Algebra K K₂] (hdeg : Module.finrank K K₂ = 2) (σ : K₂ ≃+* K₂)
    (hσ : ∀ c, σ c = c ^ Nat.card K) :
    ∃ g z : ModGL .G2 K₂, g ∈ adjointGroup .G2 K₂ ∧ z ∈ adjointGroup .G2 K₂ ∧
      z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ ∧
      (∃ hz : z ∈ monomialSubgroup .G2 K₂,
        ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v) ∧
      conjEntrywiseImage K g =
        adjointGroup .G2 K₂ ⊓ (twistedEntrywise z (σ : K₂ →+* K₂)).eqLocus (MonoidHom.id _) ∧
      (∀ y, twistedEntrywise z (σ : K₂ →+* K₂) (twistedEntrywise z (σ : K₂ →+* K₂) y) = y) ∧
      Nonempty ((torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) ≃*
        Multiplicative (ZMod (Nat.card K + 1)) × Multiplicative (ZMod (Nat.card K + 1))) ∧
      (∃ S : Sylow p (conjEntrywiseImage K g), (S : Subgroup (conjEntrywiseImage K g)) ≤
        (torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g).subgroupOf (conjEntrywiseImage K g)) ∧
      (∃ E : Subgroup (ModGL .G2 K₂), (∀ h, h ∈ E ↔ h ∈ torusGroup .G2 K₂ ∧ h ^ p = 1) ∧
        E ≤ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g ∧ Nat.card E = p ^ 2 ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x ^ p = 1) ∧
      (∀ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α → ∃ P : GL (Fin 2) K₂,
        (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g).comap (rootSL2 .G2 K₂ α) =
          (Matrix.SpecialLinearGroup.map (algebraMap K K₂)).range.map (conjSL P) ∧
        CFSG.IsQuasisimple
          (rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂))) ∧
      (∀ x ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g,
        ∃! a : Fin Tag.G2.rank → K₂ˣ, rootDiagUnit .G2 a = x) ∧
      ∀ a : Fin Tag.G2.rank → K₂ˣ,
        rootDiagUnit .G2 a ∈ torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g →
        orderOf (rootDiagUnit .G2 a) = p →
        (rootCharKernel a = ∅ →
          conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} =
            torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g ∧
          (∀ x ∈ conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
            ∀ y ∈ conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
              x * y = y * x) ∧
          ∀ S : Sylow 2 (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a} :
              Subgroup (ModGL .G2 K₂)),
            (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) ∧
        (rootCharKernel a ≠ ∅ → ∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧
          rootCharKernel a = {α, -α} ∧
          ⁅conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a},
              conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}⁆ =
            rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g ∧
          (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}) ⊓
              Subgroup.centralizer ((rootRankOneGroup .G2 K₂ α ⊓ conjEntrywiseImage K g :
                Subgroup (ModGL .G2 K₂)) : Set (ModGL .G2 K₂)) =
            (Subgroup.center (conjEntrywiseImage K g ⊓
              Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))).map
              (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}).subtype ∧
          (Subgroup.center (conjEntrywiseImage K g ⊓
              Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))).map
              (conjEntrywiseImage K g ⊓ Subgroup.centralizer {rootDiagUnit .G2 a}).subtype ≤
            torusGroup .G2 K₂ ∧
          ∀ S : Sylow 2 (Subgroup.center (conjEntrywiseImage K g ⊓
              Subgroup.centralizer {rootDiagUnit .G2 a} : Subgroup (ModGL .G2 K₂))),
            (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) := by
  classical
  obtain ⟨hfin, -, -⟩ := quadratic_frobenius hdeg σ hσ
  have : Finite K₂ := hfin
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  have hq2 := natCard_eq_sq_of_finrank_eq_two hdeg
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvd₂ : Nat.card K + 1 ∣ Nat.card K₂ - 1 := by
    refine ⟨Nat.card K - 1, ?_⟩
    rw [hq2]
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  have hq4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    have := five_le_of_prime_of_three_lt hp hp3
    omega
  have hodd₂ : Odd (Nat.card K₂) := by
    rw [hq2]
    exact hK.pow
  have h2 : (2 : K₂) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_odd_natCard hodd₂)
  obtain ⟨hinv, ω, hω, hσω⟩ := exists_frobenius_eq_neg hdeg σ hσ
  have hPn := quadraticTorusP_mul_nSL σ hω h2 hσω
  have hρC : ∀ (β : Fin Tag.G2.rank → ℤ) (A : SL2 K₂),
      rootSL2 .G2 K₂ β A ∈ adjointGroup .G2 K₂ :=
    fun β A => (exceptional_Lang_root_rank_one_data .G2 K₂ β).2.2.2.2.1 A
  obtain ⟨g, hgdef⟩ : ∃ g : ModGL .G2 K₂, g = rootSL2 .G2 K₂ g2a (quadraticTorusP ω hω h2)⁻¹ *
      rootSL2 .G2 K₂ g2v (quadraticTorusP ω hω h2)⁻¹ := ⟨_, rfl⟩
  have hg : g ∈ adjointGroup .G2 K₂ := by
    rw [hgdef]
    exact mul_mem (hρC _ _) (hρC _ _)
  obtain ⟨z, hzdef⟩ : ∃ z, z = g * (Units.map (entrywiseHom (σ : K₂ →+* K₂)) g)⁻¹ := ⟨_, rfl⟩
  have hzeq : z = rootWeylSL2 .G2 K₂ g2a (twoMulUnit ω hω h2) *
      rootWeylSL2 .G2 K₂ g2v (twoMulUnit ω hω h2) := by
    rw [hzdef, hgdef]
    exact rootSL2_pair_mul_entrywise_inv_eq (σ : K₂ →+* K₂) hPn
  obtain ⟨hzN, hw⟩ : ∃ hz : z ∈ monomialSubgroup .G2 K₂,
      ∀ v : Fin Tag.G2.rank → ℤ, weylQuotientHom .G2 K₂ ⟨z, hz⟩ • v = -v := by
    rw [hzeq]
    exact rootWeylSL2_pair_mem_monomial _
  have hzC : z ∈ adjointGroup .G2 K₂ := by
    rw [hzeq]
    exact mul_mem (hρC _ _) (hρC _ _)
  have hΓ := conjEntrywiseImage_eq_fixed σ hσ hg hzdef
  have hT := torusGroup_inf_eq_torusTorsion hzN hw (σ : K₂ →+* K₂) hσ hΓ
  have hHcomm := (triangular_borel_structure.{0, 0} .G2 K₂).1
  have hTΓ : torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g ≤ conjEntrywiseImage K g := inf_le_right
  have hcardΓ : Nat.card (conjEntrywiseImage K g) = CFSG.Open.ordG2 (Nat.card K) := by
    rw [natCard_conjEntrywiseImage, card_adjointGroup_G2]
  have hcardT : Nat.card (torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g : Subgroup (ModGL .G2 K₂)) =
      (Nat.card K + 1) ^ 2 := by
    rw [hT]
    exact natCard_torusTorsion hdvd₂
  have hidx : ¬ p ∣ ((torusGroup .G2 K₂ ⊓ conjEntrywiseImage K g).subgroupOf
      (conjEntrywiseImage K g)).index := by
    refine not_dvd_of_sq_mul_eq_ordG2 hq1 hp hp3 hpq ?_
    rw [← hcardΓ, ← hcardT, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTΓ).toEquiv]
    exact Subgroup.card_mul_index _
  refine ⟨g, z, hg, hzC, hzdef, ⟨hzN, hw⟩, hΓ,
    twistedEntrywise_twistedEntrywise (σ := (σ : K₂ →+* K₂)) hinv hzdef, ?_,
    exists_sylow_le_of_not_dvd_index hidx, ?_, fun α hα => ?_, fun x hx => ?_,
    fun a _ ha => qplus_prime_element_centralizer hK hp hp3 hpq hdeg σ hσ hg hzdef hzN hw a ha⟩
  · rw [hT]
    exact nonempty_torusTorsion_mulEquiv hdvd₂
  · have : NeZero p := ⟨hp.ne_zero⟩
    refine ⟨torusTorsion K₂ p, fun h => mem_torusTorsion_iff, ?_, natCard_torusTorsion
      (hpq.trans hdvd₂), fun x hx y hy => hHcomm x (torusTorsion_le_torusGroup p hx) y
        (torusTorsion_le_torusGroup p hy), fun x hx => (mem_torusTorsion_iff.1 hx).2⟩
    rw [hT]
    exact torusTorsion_mono hpq
  · obtain ⟨P, hP, -⟩ := rootSL2_comap_fixed_eq hK hdeg σ hσ hg hzdef hzN hw hα
    exact ⟨P, hP, isQuasisimple_of_rootSL2_comap_eq hq4 inf_le_left hP⟩
  · obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx.1
    exact ⟨a, rfl, fun b hb => rootDiagUnit_injective hb⟩

end CFSG.RankThree.Chevalley
