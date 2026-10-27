module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpTwo
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpInner
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueBasic
import CFSG.Quasithin.H13.A5M22HatRow
import CFSG.GroupTheory.E3Params
import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
private theorem w135c2_spField_conj_mul_apply {F : Type} [Field F] {n : ℕ} (σ : F ≃+* F)
    (h y : StatedSp n F) :
    (MulAut.conj h * fieldSp n F σ * (MulAut.conj h)⁻¹) (MulAut.conj h y) =
      MulAut.conj h (fieldSp n F σ y) := by
  have hinner : (MulAut.conj h)⁻¹ (MulAut.conj h y) = y := by
    rw [MulAut.conj_inv_apply, MulAut.conj_apply]
    group
  rw [MulAut.mul_apply, MulAut.mul_apply, hinner]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
private theorem w135c2_spField_apply {F : Type} [Field F] {n : ℕ} {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {t : MulAut W}
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (e₀ : StatedSp n F ≃* ↥L)
    {σ : F ≃+* F} {h : StatedSp n F}
    (hαeq : CFSG.SeitzReduction.F4Pilot.normalizerMulAut e₀.symm ⟨t, htN⟩ =
      MulAut.conj h * fieldSp n F σ * (MulAut.conj h)⁻¹) :
    ∀ y, t * ((((MulAut.conj h).trans e₀) y : ↥L) : MulAut W) * t⁻¹ =
      ((((MulAut.conj h).trans e₀) (fieldSp n F σ y) : ↥L) : MulAut W) := by
  intro y
  have hx : CFSG.SeitzReduction.F4Pilot.normalizerMulAut e₀.symm ⟨t, htN⟩
      (MulAut.conj h y) = MulAut.conj h (fieldSp n F σ y) := by
    rw [hαeq]
    exact w135c2_spField_conj_mul_apply σ h y
  have h := CFSG.SeitzReduction.F4Pilot.coe_symm_normalizerMulAut_apply e₀.symm ⟨t, htN⟩
    (MulAut.conj h y)
  rw [MulEquiv.symm_symm, hx] at h
  exact h.symm

private theorem w135c2_spField_not_inner {F : Type} [Field F] {n : ℕ} {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (htL : t ∉ L) (hZ : Subgroup.center ↥L = ⊥)
    (htN : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (e₀ : StatedSp n F ≃* ↥L) :
    CFSG.SeitzReduction.F4Pilot.normalizerMulAut e₀.symm ⟨t, htN⟩ ∉
      (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range := by
  rintro ⟨s, hs⟩
  have hconj : ∀ l ∈ L, t * l * t⁻¹ =
      ((e₀ s : ↥L) : MulAut W) * l * ((e₀ s : ↥L) : MulAut W)⁻¹ := by
    intro l hl
    have h := CFSG.SeitzReduction.F4Pilot.coe_symm_normalizerMulAut_apply e₀.symm ⟨t, htN⟩
      (e₀.symm (⟨l, hl⟩ : ↥L))
    rw [MulEquiv.symm_symm] at h
    rw [show CFSG.SeitzReduction.F4Pilot.normalizerMulAut e₀.symm ⟨t, htN⟩ =
      MulAut.conj s from hs.symm, MulAut.conj_apply] at h
    rw [map_mul, map_mul, map_inv] at h
    simp only [MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h.symm
  exact htL (w135c2_mem_of_conj_eq_conj hctx htY (e₀ s).2 hconj hZ)

open CFSG.LieType.Universal.Symplectic.SpExtras in
private theorem w135c2_spField_orderOf_elt {F : Type} [Field F] [CharP F 2] {n : ℕ}
    (r : TauCeti.GLSymplecticFin.RootSubgroupIndex n) {d : F} (hd : d ≠ 0) :
    orderOf (elt r d) = 2 := by
  let hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : elt r d ^ 2 = 1 := by
    rw [pow_two, ← elt_add, CharTwo.add_self_eq_zero, elt_zero]
  refine orderOf_eq_prime h2 ?_
  intro h1
  exact hd (elt_injective r (by rw [h1, elt_zero]))

open CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher in
private theorem w135c2_spField_mul_conj {F : Type} [Field F] {n : ℕ} {W : Type} [CommGroup W]
    {L : Subgroup (MulAut W)} {t : MulAut W} (htt : t * t = 1) (e : StatedSp n F ≃* ↥L)
    {σ : F ≃+* F} (r : TauCeti.GLSymplecticFin.RootSubgroupIndex n) {c : F}
    (he : ∀ y, t * ((e y : ↥L) : MulAut W) * t⁻¹ =
      ((e (fieldSp n F σ y) : ↥L) : MulAut W)) :
    t * ((((e (elt r c) : ↥L) : MulAut W))⁻¹ * t * ((e (elt r c) : ↥L) : MulAut W)) =
      ((e (elt r (-(σ c) + c)) : ↥L) : MulAut W) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hfield : fieldSp n F σ (elt r (-c)) = elt r (-(σ c)) := by
    rw [elt_neg, map_inv, CFSG.SeitzReduction.F4Pilot.fieldSp_elt, elt_neg]
  have hec : ((e (elt r (-c)) : ↥L) : MulAut W) = (((e (elt r c) : ↥L) : MulAut W))⁻¹ := by
    rw [elt_neg, map_inv, Subgroup.coe_inv]
  have h1 : t * (((e (elt r c) : ↥L) : MulAut W))⁻¹ * t =
      ((e (elt r (-(σ c))) : ↥L) : MulAut W) := by
    have h := he (elt r (-c))
    rw [hfield, hec, hti] at h
    exact h
  calc t * ((((e (elt r c) : ↥L) : MulAut W))⁻¹ * t * ((e (elt r c) : ↥L) : MulAut W))
      = (t * (((e (elt r c) : ↥L) : MulAut W))⁻¹ * t) *
          ((e (elt r c) : ↥L) : MulAut W) := by group
    _ = ((e (elt r (-(σ c))) : ↥L) : MulAut W) *
          ((e (elt r c) : ↥L) : MulAut W) := by rw [h1]
    _ = ((e (elt r (-(σ c)) * elt r c) : ↥L) : MulAut W) := by
        rw [map_mul, Subgroup.coe_mul]
    _ = ((e (elt r (-(σ c) + c)) : ↥L) : MulAut W) := by rw [← elt_add]

private theorem w135c2_spField_rank_le {W : Type} [CommGroup W] [Finite W] {t x : MulAut W}
    (hW : ∀ w : W, w ^ 2 = 1) :
    E3.mQuot ⊤ (fixV (Subgroup.zpowers (t * (x⁻¹ * t * x)))) ≤
      2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have hconj : CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers (x⁻¹ * t * x))) =
      CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) := by
    rw [← CFSG.GroupTheory.mQuot_top_eq_rkIdx,
      show x⁻¹ * t * x = x⁻¹ * t * (x⁻¹)⁻¹ by rw [inv_inv],
      w135c2_mQuot_conj, CFSG.GroupTheory.mQuot_top_eq_rkIdx]
  calc E3.mQuot ⊤ (fixV (Subgroup.zpowers (t * (x⁻¹ * t * x))))
      = CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers (t * (x⁻¹ * t * x)))) := by
        rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx]
    _ ≤ CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) +
        CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers (x⁻¹ * t * x))) :=
        CFSG.Quasithin.H13.A5.M22Hat.rkIdx_fixV_mul_le hW t (x⁻¹ * t * x)
    _ = CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) +
        CFSG.Quasithin.rkIdx (fixV (Subgroup.zpowers t)) := by rw [hconj]
    _ = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
        rw [two_mul, CFSG.GroupTheory.mQuot_top_eq_rkIdx]

private theorem w135c2_spField_mul_self {G : Type} [Group G] {t : G} (h : orderOf t = 2) :
    t * t = 1 := by
  have h1 := pow_orderOf_eq_one t
  rwa [h, pow_two] at h1

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
theorem w135c2_sp_exists_fieldSp_of_not_mem
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L)
    (htY : t ∈ Y) (htL : t ∉ L) (ht2 : orderOf t = 2) {n f : ℕ} (hn : 3 ≤ n)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ (e : StatedSp n F ≃* ↥L) (σ : F ≃+* F), orderOf σ = 2 ∧
        ∀ y, t * ((e y : ↥L) : MulAut W) * t⁻¹ = ((e (fieldSp n F σ y) : ↥L) : MulAut W) := by
  classical
  have hZ : Subgroup.center ↥L = ⊥ := w135c2_center_eq_bot_of_lieModel_psp hctx hlie
  have hL' : LieModel ↥L .PSp n 2 f := LieModel.of_quotient_center hZ hlie
  obtain ⟨F, instF, instFin, hF, ⟨e₀⟩⟩ := w135c2_nonempty_equiv_statedSp_of_lieModel_psp hL'
  let hField : Field F := instF
  let hFinite : Finite F := instFin
  let hFintype : Fintype F := Fintype.ofFinite F
  let hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hCharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have hLY : L ≤ Y := hctx.2.2.1
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp (w135_normal_of_ctx hctx) htY
  have htt : t * t = 1 := w135c2_spField_mul_self ht2
  let α : MulAut (StatedSp n F) :=
    CFSG.SeitzReduction.F4Pilot.normalizerMulAut e₀.symm ⟨t, htN⟩
  have hα2 : α * α = 1 := by
    change CFSG.SeitzReduction.F4Pilot.normalizerMulAut e₀.symm ⟨t, htN⟩ *
      CFSG.SeitzReduction.F4Pilot.normalizerMulAut e₀.symm ⟨t, htN⟩ = 1
    rw [← map_mul]
    have h1 : (⟨t, htN⟩ : Subgroup.normalizer (L : Set (MulAut W))) * ⟨t, htN⟩ = 1 := by
      apply Subtype.ext
      simpa using htt
    rw [h1, map_one]
  have hαi : α ∉ (MulAut.conj : StatedSp n F →* MulAut (StatedSp n F)).range :=
    w135c2_spField_not_inner hctx htY htL hZ htN e₀
  obtain ⟨σ, hσ, h, hαeq⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_eq_conj_fieldSp_of_not_inner hn hα2 hαi
  exact ⟨F, instF, instFin, hF, (MulAut.conj h).trans e₀, σ, hσ,
    w135c2_spField_apply htN e₀ hαeq⟩

private theorem w135c2_spField_exists_apply_ne {F : Type} [Field F] {σ : F ≃+* F}
    (hσ : orderOf σ = 2) : ∃ c : F, σ c ≠ c := by
  have hσne : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    omega
  by_contra h
  exact hσne (RingEquiv.ext fun x => by_contra fun hx => h ⟨x, hx⟩)

open CFSG.LieType.Universal.Symplectic.SpExtras in
theorem w135c2_sp_outer_le_two_mul
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (htL : t ∉ L) (ht2 : orderOf t = 2) {n f : ℕ} (hn : 3 ≤ n)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) :
    f ≤ 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  classical
  obtain ⟨F, instF, instFin, hF, e, σ, hσ, he⟩ :=
    w135c2_sp_exists_fieldSp_of_not_mem hctx htY htL ht2 hn hlie
  let hField : Field F := instF
  let hFinite : Finite F := instFin
  let hFintype : Fintype F := Fintype.ofFinite F
  let hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hCharP : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have htt : t * t = 1 := w135c2_spField_mul_self ht2
  obtain ⟨c, hc⟩ := w135c2_spField_exists_apply_ne hσ
  have hd : (-(σ c) + c : F) ≠ 0 := by
    have hd' : (-(σ c) + c : F) = c - σ c := by rw [sub_eq_add_neg, add_comm]
    rw [hd']
    exact sub_ne_zero.mpr (Ne.symm hc)
  have hn0 : 0 < n := by omega
  let r : TauCeti.GLSymplecticFin.RootSubgroupIndex n := .positiveLong ⟨0, hn0⟩
  let u : StatedSp n F := CFSG.LieType.Universal.Symplectic.SpExtras.elt r c
  let x : MulAut W := ((e u : ↥L) : MulAut W)
  let d : F := -(σ c) + c
  let s : MulAut W := ((e (CFSG.LieType.Universal.Symplectic.SpExtras.elt r d) : ↥L) : MulAut W)
  have hmul : t * (x⁻¹ * t * x) = s := by
    show t * ((((e (CFSG.LieType.Universal.Symplectic.SpExtras.elt r c) : ↥L) : MulAut W))⁻¹ *
        t * ((e (CFSG.LieType.Universal.Symplectic.SpExtras.elt r c) : ↥L) : MulAut W)) =
      ((e (CFSG.LieType.Universal.Symplectic.SpExtras.elt r (-(σ c) + c)) : ↥L) : MulAut W)
    exact w135c2_spField_mul_conj htt e r he
  have hs2 : orderOf s = 2 := by
    change orderOf ((e (CFSG.LieType.Universal.Symplectic.SpExtras.elt r d) : ↥L) : MulAut W) = 2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact w135c2_spField_orderOf_elt r hd
  have hinner : f ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers s)) :=
    w135c2_sp_inner_le_mQuot hW hctx (e (CFSG.LieType.Universal.Symplectic.SpExtras.elt r d)).2
      hs2 hlie
  have hmain : E3.mQuot ⊤ (fixV (Subgroup.zpowers (t * (x⁻¹ * t * x)))) ≤
      2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := w135c2_spField_rank_le hW
  rw [← hmul] at hinner
  exact hinner.trans hmain

end CFSG.LocalAnalysis.WeakClosure81
