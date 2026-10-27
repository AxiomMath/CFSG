module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derStepTwo
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l48uB_hOut {G : Type} [Group G] [Finite G] {B L : Subgroup G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)}
    (hM : GGB2derModelProp B L hBL ψ β) :
    ∀ φ : MulAut ↥L, ∃ l : ↥L, ∀ a : ↥L,
      φ a * (l * a * l⁻¹)⁻¹ ∈ Subgroup.center ↥L := by
  intro φ
  let θ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r) := ψ.comp φ.toMonoidHom
  have hθsurj : Function.Surjective θ := hM.surj.comp φ.surjective
  have hcomapc : Subgroup.comap φ.toMonoidHom (Subgroup.center ↥L) = Subgroup.center ↥L :=
    le_antisymm (Subgroup.comap_center_le_center (f := φ.toMonoidHom) φ.injective)
      (Subgroup.map_le_iff_le_comap.mp
        (Subgroup.map_center_le_center (f := φ.toMonoidHom) φ.surjective))
  have hθker : θ.ker = Subgroup.center ↥L := by
    show (ψ.comp φ.toMonoidHom).ker = Subgroup.center ↥L
    rw [← MonoidHom.comap_ker ψ φ.toMonoidHom, hM.ker_eq, hcomapc]
  let e : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSpGroup K r) :=
    (QuotientGroup.quotientMulEquivOfEq hM.ker_eq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hM.surj)
  let f : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (LargeEvenSpGroup K r) :=
    (QuotientGroup.quotientMulEquivOfEq hθker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)
  let α : MulAut (LargeEvenProj (LargeEvenSpGroup K r)) := e.symm.trans f
  obtain ⟨l₀, hl₀⟩ := TwoThree.mem_range_conj_sp hK hr α
  obtain ⟨l, hl⟩ := hM.surj l₀
  refine ⟨l, fun a => ?_⟩
  have he_mk : ∀ a : ↥L, e (QuotientGroup.mk a) = ψ a := by
    intro a
    show (QuotientGroup.quotientKerEquivOfSurjective ψ hM.surj)
        (QuotientGroup.quotientMulEquivOfEq hM.ker_eq.symm (QuotientGroup.mk a)) = ψ a
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    show (QuotientGroup.kerLift ψ) (QuotientGroup.mk a) = ψ a
    rw [QuotientGroup.kerLift_mk]
  have hf_mk : ∀ a : ↥L, f (QuotientGroup.mk a) = ψ (φ a) := by
    intro a
    show (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)
        (QuotientGroup.quotientMulEquivOfEq hθker.symm (QuotientGroup.mk a)) = ψ (φ a)
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    show (QuotientGroup.kerLift θ) (QuotientGroup.mk a) = ψ (φ a)
    rw [QuotientGroup.kerLift_mk]
    rfl
  have hα : α (ψ a) = ψ (φ a) := by
    calc α (ψ a) = f (e.symm (ψ a)) := rfl
      _ = f (e.symm (e (QuotientGroup.mk a))) := by rw [← he_mk a]
      _ = f (QuotientGroup.mk a) := by rw [MulEquiv.symm_apply_apply]
      _ = ψ (φ a) := hf_mk a
  have hψeq : ψ (φ a) = ψ (l * a * l⁻¹) := by
    rw [← hα, ← hl₀, ← hl]
    simp only [MulAut.conj_apply, map_mul, map_inv]
  rw [← hM.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hψeq, mul_inv_cancel]

theorem ggB2der_U_bar {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)} (hM : GGB2derModelProp B L hBL ψ β)
    (hZ2 : IsPGroup 2 (Subgroup.center ↥L))
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) :
    ∃ U : Subgroup (LargeEvenProj (LargeEvenSpGroup K r)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ a ∈ β.range, ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have hperf : commutator ↥L = ⊤ := (GGConfig.data_L hcfg).2.2.2
  have hOut := l48uB_hOut hK hr hM
  have hN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun g hg => mem_normalizer_of_sstar hS hnc hg
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) →
      IsPGroup 3 S → IsCyclic S := hS.2.2.2.2
  obtain ⟨T, hTx, hT2, hBT, hTB⟩ := hst.2.1
  obtain ⟨U, hUL, hU2, hBU, hUne⟩ :=
    ggB2der_exists_two_subgroup Nat.prime_three (by decide) hS.1.1 hS.2.1 hS.2.2.1
      hS.2.2.2.1.1 hperf hZ2 hOut hN hBL hcyc hTx hT2 hBT hTB
  refine ⟨(U.subgroupOf L).map ψ, ?_, ?_, ?_⟩
  · intro hbot
    apply hUne
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hx : (⟨u, hUL hu⟩ : ↥L) ∈ U.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact hu
    have hmem : (⟨u, hUL hu⟩ : ↥L) ∈ ψ.ker :=
      (Subgroup.map_eq_bot_iff (U.subgroupOf L)).mp hbot hx
    rw [hM.ker_eq] at hmem
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨l, hl⟩)
  · exact (hU2.comap_of_injective L.subtype L.subtype_injective).map ψ
  · intro a ha u hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨v, hvU, rfl⟩ := hu
    rw [MonoidHom.mem_range] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [← hM.conj b v]
    refine Subgroup.mem_map.mpr
      ⟨(L.normalizerMonoidHom (Subgroup.inclusion hBL b)) v, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hvU' : (v : G) ∈ U := Subgroup.mem_subgroupOf.mp hvU
    convert (Subgroup.mem_normalizer_iff.mp (hBU b.2) (v : G)).mp hvU' using 1
    rfl

end CFSG.StandardType
