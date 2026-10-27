module

public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeA
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.Quasithin.H13.GoldschmidtG52Sec
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShape
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open scoped MatrixGroups IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private noncomputable def kyRep {r : ℕ} [Fact r.Prime] {U W : Subgroup G}
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W)
    [(W.subgroupOf U).Normal] [IsElementaryAbelian r (↥U ⧸ W.subgroupOf U)] :
    Representation (ZMod r) ↥t.Ky (Additive (↥U ⧸ W.subgroupOf U)) :=
  (Units.coeHom _).comp (CFSG.ABGLocalTools.chiefRep (p := r) hUW.2.1 hUW.2.2.1)

private theorem kyRep_apply_mk {r : ℕ} [Fact r.Prime] {U W : Subgroup G}
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W)
    [(W.subgroupOf U).Normal] [IsElementaryAbelian r (↥U ⧸ W.subgroupOf U)]
    (k : ↥t.Ky) (u : ↥U) :
    kyRep t hUW k (Additive.ofMul ((u : ↥U) : ↥U ⧸ W.subgroupOf U)) =
      Additive.ofMul (((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) :
        ↥U ⧸ W.subgroupOf U)) :=
  CFSG.ABGLocalTools.chiefRep_apply_mk (p := r) hUW.2.1 hUW.2.2.1 k u

private theorem mul_conj_mul_inv_mem {X : Type*} [Group X] {U W : Subgroup X}
    (hW : ∀ x ∈ U, ∀ y ∈ W, x * y * x⁻¹ ∈ W) {k u : X} (hu : u ∈ U)
    (h : (k * u * k⁻¹)⁻¹ * u ∈ W) : k * u * k⁻¹ * u⁻¹ ∈ W := by
  have h1 : u⁻¹ * (k * u * k⁻¹) ∈ W := by
    simpa [mul_assoc] using inv_mem h
  have h2 := hW u hu _ h1
  simpa [mul_assoc] using h2

private theorem kyRep_injective {r : ℕ} [Fact r.Prime] {U W : Subgroup G}
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W)
    [(W.subgroupOf U).Normal] [IsElementaryAbelian r (↥U ⧸ W.subgroupOf U)]
    (hfaith : ∀ k ∈ t.Ky, (∀ u ∈ U, k * u * k⁻¹ * u⁻¹ ∈ W) → k = 1) :
    Function.Injective (kyRep t hUW) := by
  have hker : ∀ k : ↥t.Ky, kyRep t hUW k = 1 → k = 1 := by
    intro k hk
    apply Subtype.ext
    apply hfaith (k : G) k.2
    intro u hu
    let u₀ : ↥U := ⟨u, hu⟩
    have hfixed : kyRep t hUW k (Additive.ofMul ((u₀ : ↥U) : ↥U ⧸ W.subgroupOf U)) =
        Additive.ofMul ((u₀ : ↥U) : ↥U ⧸ W.subgroupOf U) := by
      have h := congrArg (fun f : Module.End (ZMod r)
        (Additive (↥U ⧸ W.subgroupOf U)) =>
          f (Additive.ofMul ((u₀ : ↥U) : ↥U ⧸ W.subgroupOf U))) hk
      simpa using h
    rw [kyRep_apply_mk t hUW] at hfixed
    have hclass : (((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u₀ : ↥U) :
        ↥U ⧸ W.subgroupOf U)) = ((u₀ : ↥U) : ↥U ⧸ W.subgroupOf U) :=
      Additive.ofMul.injective hfixed
    have hmem : (((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u₀ : ↥U) : G))⁻¹ * u ∈ W := by
      have := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hclass)
      simpa using this
    have hcoe : ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u₀ : ↥U) : G) =
        k * u * k⁻¹ := CFSG.ABGLocalTools.chiefConj_apply_coe hUW.2.1 k u₀
    rw [hcoe] at hmem
    exact mul_conj_mul_inv_mem hUW.2.2.2.1 hu hmem
  intro a b hab
  have h1 : kyRep t hUW (a * b⁻¹) = 1 := by
    rw [map_mul, hab, ← map_mul, mul_inv_cancel, map_one]
  exact mul_inv_eq_one.mp (hker _ h1)

private theorem nontrivial_kyRep {r : ℕ} {U W : Subgroup G}
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W) :
    Nontrivial (Additive (↥U ⧸ W.subgroupOf U)) := by
  haveI : Nontrivial (↥U ⧸ W.subgroupOf U) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hUW.1.ne ((Subgroup.subgroupOf_eq_top.mp htop).antisymm hUW.1.le).symm
  infer_instance

private theorem kyRep_irreducible {r : ℕ} [Fact r.Prime] {U W : Subgroup G}
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W)
    [(W.subgroupOf U).Normal] [IsElementaryAbelian r (↥U ⧸ W.subgroupOf U)] :
    Representation.IsIrreducible (kyRep t hUW) := by
  haveI := nontrivial_kyRep t hUW
  refine CFSG.Quasithin.H13.A6.G52.isIrreducible_of_forall_submodule _ ?_
  intro V₀ hV₀
  exact CFSG.ABGLocalTools.chiefRep_irreducible hUW V₀ (fun k v hv => hV₀ k v hv)

private theorem fixV_kyRep_eq_bot {r : ℕ} [Fact r.Prime] {U W : Subgroup G}
    (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W)
    [(W.subgroupOf U).Normal] [IsElementaryAbelian r (↥U ⧸ W.subgroupOf U)]
    (hfix : ∀ u ∈ U, (∀ x ∈ t.Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W) :
    CFSG.LocalAnalysis.UniquenessCase.UCK.fixV (kyRep t hUW) (t.Z.subgroupOf t.Ky) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨u, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk v
  have hZKy : t.Z ≤ t.Ky := t.Z_le_Dz.trans t.Dz_le_Ky
  have huW : (u : G) ∈ W := by
    apply hfix (u : G) u.2
    intro x hx
    let k : ↥t.Ky := ⟨x, hZKy hx⟩
    have hkD : k ∈ t.Z.subgroupOf t.Ky := Subgroup.mem_subgroupOf.mpr hx
    have hfixed := hv k hkD
    have hclass : (((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) :
        ↥U ⧸ W.subgroupOf U)) = ((u : ↥U) : ↥U ⧸ W.subgroupOf U) := by
      rw [kyRep_apply_mk t hUW] at hfixed
      exact Additive.ofMul.injective hfixed
    have hmem : (((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : G))⁻¹ * u ∈ W := by
      have := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hclass)
      simpa using this
    have hcoe : ((CFSG.ABGLocalTools.chiefConj hUW.2.1 k u : ↥U) : G) = x * u * x⁻¹ := by
      rw [CFSG.ABGLocalTools.chiefConj_apply_coe]
    rw [hcoe] at hmem
    exact mul_conj_mul_inv_mem hUW.2.2.2.1 u.2 hmem
  have hq : ((u : ↥U) : ↥U ⧸ W.subgroupOf U) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr huW)
  rw [Submodule.mem_bot, hq]
  rfl

private theorem Ky_ne_top : t.Ky ≠ ⊤ := by
  haveI : IsSimpleGroup G := c.standing.simple
  intro htop
  have hcent : Subgroup.centralizer ({t.y} : Set G) = ⊤ :=
    eq_top_iff.mpr fun x _ => (t.Ky_le (by rw [htop]; trivial)).2
  have hy : t.y ∈ Subgroup.center G :=
    Subgroup.centralizer_eq_top_iff_subset.mp hcent (Set.mem_singleton t.y)
  rw [CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot c.standing.nonab,
    Subgroup.mem_bot] at hy
  simpa [hy] using t.orderOf_y

private theorem isKGroup_Ky : CFSG.Open.IsKGroup ↥t.Ky :=
  c.standing.kProper.isKGroup t.Ky (Ky_ne_top t)

private theorem commutator_Ky_top : commutator ↥t.Ky = ⊤ := by
  haveI : Group.IsPerfect ↥t.Ky := Subgroup.isPerfect_iff.mpr t.commutator_Ky
  exact Group.IsPerfect.commutator_eq_top

private theorem card_subgroupOf_Z : Nat.card (t.Z.subgroupOf t.Ky) = 3 := by
  rw [show Nat.card (t.Z.subgroupOf t.Ky) = Nat.card t.Z from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (t.Z_le_Dz.trans t.Dz_le_Ky)).toEquiv]
  exact t.card_Z

private theorem normalClosure_subgroupOf_Z_eq_top
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    Subgroup.normalClosure ((t.Z.subgroupOf t.Ky : Subgroup ↥t.Ky) : Set ↥t.Ky) = ⊤ := by
  classical
  have hZKy : t.Z ≤ t.Ky := t.Z_le_Dz.trans t.Dz_le_Ky
  set D : Subgroup ↥t.Ky := t.Z.subgroupOf t.Ky with hD
  set Nc : Subgroup ↥t.Ky := Subgroup.normalClosure (D : Set ↥t.Ky) with hNc
  have hDNc : D ≤ Nc := Subgroup.subset_normalClosure
  haveI : Nc.Normal := Subgroup.normalClosure_normal
  set M₀ : Subgroup G := Nc.map t.Ky.subtype with hM
  have hMle : M₀ ≤ t.Ky := Subgroup.map_subtype_le _
  have hZM : t.Z ≤ M₀ := by
    intro z hz
    exact ⟨⟨z, hZKy hz⟩, hDNc (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hNc_eq : M₀.subgroupOf t.Ky = Nc := by
    ext k
    constructor
    · intro hk
      obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hk)
      have : y = k := Subtype.ext hyk
      rwa [this] at hy
    · intro hk
      exact Subgroup.mem_subgroupOf.mpr ⟨k, hk, rfl⟩
  have hnormal : (M₀.subgroupOf t.Ky).Normal := hNc_eq.symm ▸ (inferInstance : Nc.Normal)
  have hMnorm : t.Ky ≤ Subgroup.normalizer (M₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMle).mp hnormal
  rcases t.le_N_or_eq_Ky hK32 hGA hSp hMle hMnorm with hN | hEq
  · exfalso
    have hN2 : IsPGroup 2 t.d.N := by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.S.M
    have h3N : ¬ 3 ∣ Nat.card t.d.N :=
      CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num)
    have hdiv : 3 ∣ Nat.card t.d.N := by
      simpa [t.card_Z] using Subgroup.card_dvd_of_le (hZM.trans hN)
    exact h3N hdiv
  · have hmap : Nc.map t.Ky.subtype = (⊤ : Subgroup ↥t.Ky).map t.Ky.subtype := by
      rw [hM] at hEq
      rw [hEq, Subgroup.map_top, Subgroup.range_subtype]
    exact Subgroup.map_injective t.Ky.subtype_injective hmap

private theorem pRank_top_Ky_eq_one
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥t.Ky) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) t.Ky]
    exact (CFSG.SectionRank.pRank_mono (by norm_num) (t.Ky_le_Xz hK32 hGA hSp)).trans
      (le_of_eq (t.pRank_Xz hK332 hOut hp hN hZ))
  · have hD_elab : CFSG.Open.IsElemAbelian 3 (t.Z.subgroupOf t.Ky) :=
      CFSG.GroupTheory.isElemAbelian_of_card_prime (card_subgroupOf_Z t)
    exact CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := t.Z.subgroupOf t.Ky)
      (by norm_num) le_top hD_elab (k := 1) (by rw [card_subgroupOf_Z t]; norm_num)

theorem Ky_cases (hK461 : CFSG.LocalAnalysis.UniquenessCase.UCK.K461)
    (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462)
    (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) {r : ℕ} (hr : r.Prime)
    {U W : Subgroup G} (hUW : CFSG.ABGLocalTools.IsChiefFactorUnder r t.Ky U W)
    (hfix : ∀ u ∈ U, (∀ x ∈ t.Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    (hfaith : ∀ k ∈ t.Ky, (∀ u ∈ U, k * u * k⁻¹ * u⁻¹ ∈ W) → k = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nonempty (↥t.Ky ≃* SL(2, F))) ∨
      (∃ n : ℕ, CFSG.Blueprint.LieModel ↥t.Ky .PSL 2 2 n) ∨
      CFSG.Quasithin.IsExt ↥t.Ky
        (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
        (fun Y _ => CFSG.Quasithin.IsAlt 5 Y) := by
  classical
  rcases eq_or_ne r 2 with rfl | hr2
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hWn : (W.subgroupOf U).Normal := hUW.normal
    haveI hEl : IsElementaryAbelian 2 (↥U ⧸ W.subgroupOf U) := hUW.isElementaryAbelian
    have hinj : Function.Injective (kyRep t hUW) := kyRep_injective t hUW hfaith
    have hirr : Representation.IsIrreducible (kyRep t hUW) := kyRep_irreducible t hUW
    have hfixV := fixV_kyRep_eq_bot t hUW hfix
    have hfixSub : CFSG.RankThree.FFModules.fixSub (kyRep t hUW)
        (t.Z.subgroupOf t.Ky) = ⊥ := by
      rw [show CFSG.RankThree.FFModules.fixSub (kyRep t hUW) (t.Z.subgroupOf t.Ky) =
        CFSG.LocalAnalysis.UniquenessCase.UCK.fixV (kyRep t hUW)
          (t.Z.subgroupOf t.Ky) from rfl]
      exact hfixV
    obtain ⟨n, hn⟩ := hK461 ↥t.Ky (isKGroup_Ky t)
      (Additive (↥U ⧸ W.subgroupOf U)) (kyRep t hUW) hinj hirr
      (t.Z.subgroupOf t.Ky) (card_subgroupOf_Z t)
      (normalClosure_subgroupOf_Z_eq_top t hK32 hGA hSp) hfixSub
      (pRank_top_Ky_eq_one t hK32 hGA hSp hK332 hOut hp hN hZ) (commutator_Ky_top t)
    rcases hn with ⟨F, hF, hFin, φ, ψ, hcard, hact⟩
    exact Or.inl ⟨F, hF, hFin, ⟨φ⟩⟩
  · haveI : Fact r.Prime := ⟨hr⟩
    have h2r : 2 < r := by
      have := hr.two_le
      omega
    haveI hWn : (W.subgroupOf U).Normal := hUW.normal
    haveI hEl : IsElementaryAbelian r (↥U ⧸ W.subgroupOf U) := hUW.isElementaryAbelian
    have hinj : Function.Injective (kyRep t hUW) := kyRep_injective t hUW hfaith
    have hirr : Representation.IsIrreducible (kyRep t hUW) := kyRep_irreducible t hUW
    have hfixV := fixV_kyRep_eq_bot t hUW hfix
    obtain hSL | hL2 | hExt := hK462 r h2r ↥t.Ky (isKGroup_Ky t)
      (Additive (↥U ⧸ W.subgroupOf U)) (kyRep t hUW) hinj hirr
      (t.Z.subgroupOf t.Ky) (card_subgroupOf_Z t)
      (normalClosure_subgroupOf_Z_eq_top t hK32 hGA hSp) hfixV
      (pRank_top_Ky_eq_one t hK32 hGA hSp hK332 hOut hp hN hZ) (commutator_Ky_top t)
    · rcases hSL with ⟨F, hF, hFin, hodd, φ⟩
      exact Or.inl ⟨F, hF, hFin, φ⟩
    · rcases hL2 with ⟨n, hodd, hmodel⟩
      exact Or.inr (Or.inl ⟨n, hmodel⟩)
    · exact Or.inr (Or.inr hExt)

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
