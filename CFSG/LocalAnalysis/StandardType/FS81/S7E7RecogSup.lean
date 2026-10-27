module

public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogDefs
public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7E7RecogSurj

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.QuasithinUnique

theorem le_sup_of_e7RootRecog
    (hRec : E7RootRecog) {G : Type} [Group G] [Finite G] (H N : Subgroup G)
    [(N.subgroupOf H).Normal] (hNH : N ≤ H)
    (φ : ↥(adjointGroup .E7 (ZMod 2)) →* G) (hφH : ∀ x, φ x ∈ H)
    (hφN : ∀ x, φ x ∈ N → x = 1) (r : ↥(adjointGroup .E7 (ZMod 2)))
    (hr : (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2))
    (hr3 : orderOf r = 3)
    (hmem : ∀ g ∈ H, g * φ r * g⁻¹ ∈ φ.range ⊔ N → g ∈ φ.range ⊔ N)
    (hchar : ∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) →
      orderOf s = 2 → CharTwoMod H N ⟨φ s, hφH s⟩) :
    H ≤ φ.range ⊔ N := by
  let φ' : ↥(adjointGroup .E7 (ZMod 2)) →* ↥H := φ.codRestrict H hφH
  let ψ : ↥(adjointGroup .E7 (ZMod 2)) →* (↥H ⧸ N.subgroupOf H) :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp φ'
  have hφ'coe : ∀ x, (φ' x : G) = φ x := fun x => rfl
  have hφ'val : ∀ x, φ' x = (⟨φ x, hφH x⟩ : ↥H) := fun x => rfl
  have hψapply : ∀ x, ψ x = (QuotientGroup.mk (φ' x) : ↥H ⧸ N.subgroupOf H) := fun x => rfl
  have hHnorm : H ≤ Subgroup.normalizer N :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp inferInstance
  have hrangeH : φ.range ≤ H := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    exact hφH y
  have hrangeNorm : φ.range ≤ Subgroup.normalizer N := hrangeH.trans hHnorm
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (QuotientGroup.mk (φ' x) : ↥H ⧸ N.subgroupOf H) = 1 := hx
    have hmem : φ' x ∈ N.subgroupOf H := (QuotientGroup.eq_one_iff (φ' x)).mp hx'
    have hmemG : (φ' x : G) ∈ N := (Subgroup.mem_subgroupOf).mp hmem
    exact hφN x (by simpa [hφ'coe x] using hmemG)
  have hmem' : ∀ g : ↥H ⧸ N.subgroupOf H,
      g * ψ r * g⁻¹ ∈ ψ.range → g ∈ ψ.range := by
    intro g hg
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
    rw [MonoidHom.mem_range] at hg
    obtain ⟨x, hx⟩ := hg
    have heq : (QuotientGroup.mk (φ' x) : ↥H ⧸ N.subgroupOf H) =
        QuotientGroup.mk (g₀ * φ' r * g₀⁻¹) := by
      rw [← hψapply x, hx, hψapply r]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hqmem : (φ' x)⁻¹ * (g₀ * φ' r * g₀⁻¹) ∈ N.subgroupOf H :=
      (QuotientGroup.eq).mp heq
    have hmemG : ((φ' x : G)⁻¹ * ((g₀ : G) * φ r * (g₀ : G)⁻¹)) ∈ N :=
      (Subgroup.mem_subgroupOf).mp hqmem
    have hmem_sup : (g₀ : G) * φ r * (g₀ : G)⁻¹ ∈ φ.range ⊔ N := by
      have hxrange : φ x ∈ φ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
      have hthis := Subgroup.mul_mem_sup hxrange hmemG
      rw [hφ'coe x, mul_inv_cancel_left] at hthis
      exact hthis
    have hg₀sup : (g₀ : G) ∈ φ.range ⊔ N := hmem (g₀ : G) g₀.2 hmem_sup
    change (g₀ : G) ∈ ((φ.range ⊔ N : Subgroup G) : Set G) at hg₀sup
    rw [Subgroup.coe_mul_of_left_le_normalizer_right φ.range N hrangeNorm, Set.mem_mul]
      at hg₀sup
    obtain ⟨a, ha, b, hb, hab⟩ := hg₀sup
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp ha
    refine MonoidHom.mem_range.mpr ⟨y, ?_⟩
    have hb_mem : (⟨b, hNH hb⟩ : ↥H) ∈ N.subgroupOf H := (Subgroup.mem_subgroupOf).mpr hb
    have hmul : φ' y * (⟨b, hNH hb⟩ : ↥H) = g₀ := by
      apply Subtype.ext
      simpa [hφ'coe y] using hab
    show QuotientGroup.mk' (N.subgroupOf H) (φ' y) = QuotientGroup.mk' (N.subgroupOf H) g₀
    exact (QuotientGroup.mk'_eq_mk' (N.subgroupOf H)).mpr ⟨⟨b, hNH hb⟩, hb_mem, hmul⟩
  have hchar' : ∀ s : ↥(adjointGroup .E7 (ZMod 2)),
      (s : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) →
      orderOf s = 2 →
      CharTwo (Subgroup.centralizer ({ψ s} : Set (↥H ⧸ N.subgroupOf H))) := by
    intro s hs hs2
    have hs' := hchar s hs hs2
    have hthis : ψ s = (QuotientGroup.mk (⟨φ s, hφH s⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) := by
      rw [hψapply s, hφ'val s]
    rw [hthis]
    exact hs'
  have hsurj : Function.Surjective ψ :=
    e7RootRecog_surjective hRec ψ hψinj r hr hr3 hmem' hchar'
  intro h hh
  obtain ⟨x, hx⟩ := hsurj (QuotientGroup.mk (⟨h, hh⟩ : ↥H))
  have hx' : (QuotientGroup.mk (φ' x) : ↥H ⧸ N.subgroupOf H) =
      QuotientGroup.mk (⟨h, hh⟩ : ↥H) := hx
  have hmem : (φ' x)⁻¹ * (⟨h, hh⟩ : ↥H) ∈ N.subgroupOf H := (QuotientGroup.eq).mp hx'
  have hmemG : ((φ' x : G)⁻¹ * h) ∈ N := (Subgroup.mem_subgroupOf).mp hmem
  have hxrange : φ x ∈ φ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hthis := Subgroup.mul_mem_sup hxrange hmemG
  rwa [hφ'coe x, mul_inv_cancel_left] at hthis

end CFSG.StandardType.FrameRoute.FS81

end
