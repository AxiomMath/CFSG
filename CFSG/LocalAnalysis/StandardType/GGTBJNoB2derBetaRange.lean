module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derPerfAut
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derCardB
import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derCentB
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48bR_ker_iff {G : Type} [Group G] {B L : Subgroup G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r]
    {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)}
    (hM : GGB2derModelProp B L hBL ψ β) (hperf : commutator ↥L = ⊤) (b : ↥B) :
    β b = 1 ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro hb
    have hcenter : ∀ a : ↥L,
        (L.normalizerMonoidHom (Subgroup.inclusion hBL b)) a * a⁻¹ ∈ Subgroup.center ↥L := by
      intro a
      rw [← hM.ker_eq, MonoidHom.mem_ker]
      rw [map_mul, map_inv, hM.conj b a, hb, one_mul, inv_one, mul_one, mul_inv_cancel]
    have hpoint : ∀ a : ↥L, (L.normalizerMonoidHom (Subgroup.inclusion hBL b)) a = a :=
      fun a => ggB2der_eq_of_perfect hperf
        (L.normalizerMonoidHom (Subgroup.inclusion hBL b)) hcenter a
    have hphi : L.normalizerMonoidHom (Subgroup.inclusion hBL b) = 1 :=
      MulEquiv.ext (fun a => by rw [hpoint a, MulAut.one_apply])
    simpa using (normalizerMonoidHom_eq_one_iff (Subgroup.inclusion hBL b).2).mp hphi
  · intro hb
    have harg : Subgroup.inclusion hBL b = ⟨(b : G), hBL b.2⟩ := Subtype.ext rfl
    have hphi : L.normalizerMonoidHom (Subgroup.inclusion hBL b) = 1 := by
      rw [harg]
      exact (normalizerMonoidHom_eq_one_iff (hBL b.2)).mpr hb
    have hcenter : β b ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K r)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := hM.surj y
      have hconj := hM.conj b l
      have hfix : L.normalizerMonoidHom (Subgroup.inclusion hBL b) l = l := by
        rw [hphi]; rfl
      rw [hfix] at hconj
      calc ψ l * β b = (β b * ψ l * (β b)⁻¹) * β b := congrArg (fun z => z * β b) hconj
        _ = β b * ψ l := by group
    have hbot : β b ∈ (⊥ : Subgroup (LargeEvenProj (LargeEvenSpGroup K r))) := by
      rwa [TableBSymp.center_spProj_eq_bot] at hcenter
    exact Subgroup.mem_bot.mp hbot

theorem ggB2der_beta_range {G : Type} [Group G] [Finite G] {B L : Subgroup G} {x : G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r)} (hM : GGB2derModelProp B L hBL ψ β)
    (hperf : commutator ↥L = ⊤) (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S)
    (hcard : Nat.card B = 81) :
    β.ker.map B.subtype = Subgroup.zpowers x ∧ IsElemAbelian 3 β.range ∧
      Nat.card β.range = 27 := by
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hker : β.ker.map B.subtype = Subgroup.zpowers x := by
    have hS := ggB2der_centralizer_B_eq (B := B) (L := L) (x := x) hB hxB hx1 hxL hcyc
    rw [← hS]
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, (l48bR_ker_iff hM hperf b).mp (MonoidHom.mem_ker.mp hb)⟩
    · rintro ⟨hgB, hgC⟩
      exact ⟨⟨g, hgB⟩,
        MonoidHom.mem_ker.mpr ((l48bR_ker_iff hM hperf ⟨g, hgB⟩).mpr hgC), rfl⟩
  have hker3 : Nat.card (β.ker.map B.subtype) = 3 := by rw [hker, hxcard]
  have hkercard : Nat.card β.ker = 3 := by
    have hmap : Nat.card (β.ker.map B.subtype) = Nat.card β.ker :=
      Subgroup.card_map_of_injective (f := B.subtype) (Subgroup.subtype_injective B)
    rw [← hmap, hker3]
  have hq : Nat.card (↥B ⧸ β.ker) = Nat.card β.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange β)
  have hrangecard : Nat.card β.range = 27 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    rw [hcard, hkercard, hq] at h
    omega
  exact ⟨hker, isElemAbelian_range_of_isElemAbelian hB β, hrangecard⟩

end CFSG.StandardType
