module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Open.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6N588A2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

@[expose] def PL332 : ∀ (L : Type) [Group L] [Finite L], Prop := fun L _ _ =>
  CFSG.Open.IsKGroup L ∧ CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3 ∧ IsPGroup 3 (Subgroup.center L)

theorem descend332 {G : Type} [Group G] [Finite G] (hK : CFSG.Open.IsKGroup G)
    {S Z : Subgroup G} (hS : IsSylowOf 3 S ⊤) (hrk : CFSG.Open.pRank 3 S ≤ 3) (hZS : Z ≤ S)
    (hZ3 : Nat.card Z = 3) (hwc : IsWeaklyClosedIn Z S)
    (hd : Disjoint (Z.subgroupOf S) (commutator ↥S)) :
    let N := CFSG.pPrimeCore 3 G
    CFSG.Open.IsKGroup (G ⧸ N) ∧
      IsSylowOf 3 (S.map (QuotientGroup.mk' N)) ⊤ ∧
      CFSG.Open.pRank 3 (S.map (QuotientGroup.mk' N)) ≤ 3 ∧
      Z.map (QuotientGroup.mk' N) ≤ S.map (QuotientGroup.mk' N) ∧
      Nat.card (Z.map (QuotientGroup.mk' N)) = 3 ∧
      IsWeaklyClosedIn (Z.map (QuotientGroup.mk' N)) (S.map (QuotientGroup.mk' N)) ∧
      Disjoint ((Z.map (QuotientGroup.mk' N)).subgroupOf (S.map (QuotientGroup.mk' N)))
        (commutator ↥(S.map (QuotientGroup.mk' N))) := by
  intro N
  have hN : Nat.Coprime 3 (Nat.card N) := CFSG.pPrimeCore_coprime_card
  obtain ⟨P, hPS⟩ := N588A.exists_sylow_of_isSylowOf_top hS
  have hSp : IsPGroup 3 S := hPS ▸ P.isPGroup'
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hZ3)
  have hSN : S ⊓ N = ⊥ := N588A.inf_eq_bot_of_coprime hSp hN
  have hker : ∀ x ∈ S, QuotientGroup.mk' N x = 1 → x = 1 := fun x hx h1 => by
    have hx' : x ∈ S ⊓ N := ⟨hx, (QuotientGroup.eq_one_iff x).mp h1⟩
    rwa [hSN, Subgroup.mem_bot] at hx'
  have hinj : ∀ a ∈ S, ∀ b ∈ S, QuotientGroup.mk' N a = QuotientGroup.mk' N b → a = b :=
    fun a ha b hb hab => inv_mul_eq_one.mp (hker _ (S.mul_mem (S.inv_mem ha) hb)
      (by rw [map_mul, map_inv, hab, inv_mul_cancel]))
  have hconj : ∀ {s : G}, s ∈ S → CFSG.conjugate Z s = Z := fun {s} hs => by
    apply hwc s
    intro x hx
    rw [N588A.mem_conjugate_iff] at hx
    have e : x = s⁻¹ * (s * x * s⁻¹) * s := by group
    rw [e]
    exact S.mul_mem (S.mul_mem (S.inv_mem hs) (hZS hx)) hs
  refine ⟨hK.quotient N, ?_, ?_, Subgroup.map_mono hZS, ?_, ?_, ?_⟩
  · have hs := N588A.isSylowOf_top_of_sylow (P.mapSurjective (QuotientGroup.mk'_surjective N))
    rwa [Sylow.coe_mapSurjective, hPS] at hs
  · calc CFSG.Open.pRank 3 (S.map (QuotientGroup.mk' N))
          ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (G ⧸ N)) :=
          CFSG.SectionRank.pRank_mono (by norm_num) le_top
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
          CFSG.SectionRank.pRank_quotient_eq N
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN)
      _ ≤ 3 := (N588A.pRank_le_of_isSylowOf Nat.prime_three hS ⊤).trans hrk
  · rw [N588A.card_map_of_injOn _ (fun x hx => hker x (hZS hx)), hZ3]
  · intro gbar hgbar
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gbar
    have hle : CFSG.conjugate Z g ≤ S ⊔ N := by
      intro x hx
      have hfx : QuotientGroup.mk' N x ∈ S.map (QuotientGroup.mk' N) := by
        apply hgbar
        rw [N588A.mem_conjugate_iff, ← map_inv, ← map_mul, ← map_mul]
        exact Subgroup.mem_map_of_mem _ (N588A.mem_conjugate_iff.mp hx)
      have hx' : x ∈ (S.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := hfx
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hx'
    have hSSN : IsSylowOf 3 S (S ⊔ N) := hS.of_le le_sup_left le_top
    obtain ⟨Q, hQ, hZgQ⟩ := N588A.exists_isSylowOf_ge_of_le hle (hZp.map _)
    obtain ⟨k, hk, hkQ⟩ := hSSN.exists_mem_conj hQ
    have h1 : CFSG.conjugate Z (g * k) = Z := by
      apply hwc
      intro x hx
      rw [N588A.mem_conjugate_iff] at hx
      have hx' : k * x * k⁻¹ ∈ CFSG.conjugate Z g := by
        rw [N588A.mem_conjugate_iff]
        simpa [mul_assoc] using hx
      have hxS := (hkQ _).mp (hZgQ hx')
      simpa [mul_assoc] using hxS
    have h2 : CFSG.conjugate Z g = CFSG.conjugate Z k⁻¹ := by
      have e := congrArg (fun H => CFSG.conjugate H k⁻¹) h1
      simpa only [N588A.conjugate_conjugate, mul_inv_cancel_right] using e
    have hk' : k ∈ ((S ⊔ N : Subgroup G) : Set G) := hk
    rw [Subgroup.mul_normal] at hk'
    obtain ⟨s, hs, n, hn, rfl⟩ := hk'
    have hfn : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [← N588A.map_conjugate, h2, N588A.map_conjugate, map_inv, map_mul, hfn, mul_one,
      ← map_inv, ← N588A.map_conjugate, hconj (S.inv_mem hs)]
  · rw [Subgroup.disjoint_def]
    intro x hxZ hxC
    have hcomm : commutator ↥(S.map (QuotientGroup.mk' N)) =
        (commutator ↥S).map ((QuotientGroup.mk' N).subgroupMap S) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (MonoidHom.subgroupMap_surjective _ _),
        commutator_def]
    rw [hcomm] at hxC
    obtain ⟨c, hc, rfl⟩ := hxC
    obtain ⟨z, hz, hzc⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hxZ)
    have hcz : (c : G) = z := hinj c c.2 z (hZS hz) hzc.symm
    have hcZ : c ∈ Z.subgroupOf S := Subgroup.mem_subgroupOf.mpr (by rw [hcz]; exact hz)
    rw [Subgroup.disjoint_def.mp hd hcZ hc, map_one]

theorem pullback332 {G : Type} [Group G] [Finite G] {Z : Subgroup G} (hZ3 : Nat.card Z = 3)
    (hq : CFSG.Open.pRank 3 (Subgroup.normalClosure
      ((Z.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 G)) :
        Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) : Set (G ⧸ CFSG.pPrimeCore 3 G))) = 1) :
    CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set G)) = 1 := by
  have hNc : Nat.Coprime 3 (Nat.card (CFSG.pPrimeCore 3 G)) := CFSG.pPrimeCore_coprime_card
  rw [Subgroup.coe_map,
    ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 G))] at hq
  refine le_antisymm ?_ (N588A.one_le_pRank Nat.prime_three Subgroup.le_normalClosure hZ3)
  rw [← hq]
  apply N588A.pRank_le_pRank_map (by norm_num)
  intro E _ hE x hx h1
  have hEN := N588A.inf_eq_bot_of_coprime (N588A.isPGroup_of_isElemAbelian hE) hNc
  have hx' : x ∈ E ⊓ CFSG.pPrimeCore 3 G := ⟨hx, (QuotientGroup.eq_one_iff x).mp h1⟩
  rwa [hEN, Subgroup.mem_bot] at hx'

theorem components_PL332 {H : Type} [Group H] [Finite H] (hK : CFSG.Open.IsKGroup H)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3)
    (hc : ∀ K : Subgroup H, CFSG.IsComponent K → IsPGroup 3 (Subgroup.center K)) :
    ∀ K : Subgroup H, CFSG.IsComponent K → PL332 K := fun K hKc =>
  ⟨hK.subgroup K, (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) K.subtype
    K.subtype_injective).trans hr, hc K hKc⟩

theorem wc_normalizer {H : Type} [Group H] [Finite H] {S Z : Subgroup H} (hS : IsSylowOf 3 S ⊤)
    (hZS : Z ≤ S) (hwc : IsWeaklyClosedIn Z S) :
    ∀ g : H, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set H) →
      Z.map (MulAut.conj g).toMonoidHom = Z := by
  intro g hg
  obtain ⟨P, hPS⟩ := N588A.exists_sylow_of_isSylowOf_top hS
  have hSp : IsPGroup 3 S := hPS ▸ P.isPGroup'
  have e : CFSG.conjugate Z g⁻¹ = Z.map (MulAut.conj g).toMonoidHom := by
    unfold CFSG.conjugate
    rw [inv_inv]
  rw [← e] at hg ⊢
  exact N588A.conjugate_eq_of_le_normalizer hS hwc (hSp.to_le hZS) hg

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
