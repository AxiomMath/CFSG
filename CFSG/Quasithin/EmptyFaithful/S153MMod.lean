module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F918P3
public import CFSG.Quasithin.Background.F9Eighteen
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique

namespace S153M

section Mod

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G]

theorem modMk_eq_one_iff {W U : Subgroup G} (hUW : U ≤ Subgroup.normalizer (W : Set G)) {a : G}
    (ha : a ∈ U) : modMk hUW a ha = 1 ↔ a ∈ W := by
  constructor
  · intro h
    have h1 : secMk (Subgroup.normalizer (W : Set G)) W ⟨a, hUW ha⟩ = 1 :=
      congrArg Subtype.val h
    exact secMk_eq_one_iff.mp h1
  · intro h
    exact Subtype.ext (secMk_eq_one_iff.mpr h)

theorem modMk_eq_modMk_iff {W U : Subgroup G} (hUW : U ≤ Subgroup.normalizer (W : Set G)) {a b : G}
    (ha : a ∈ U) (hb : b ∈ U) : modMk hUW a ha = modMk hUW b hb ↔ a⁻¹ * b ∈ W := by
  constructor
  · intro h
    have h1 : secMk (Subgroup.normalizer (W : Set G)) W ⟨a, hUW ha⟩ =
        secMk (Subgroup.normalizer (W : Set G)) W ⟨b, hUW hb⟩ := congrArg Subtype.val h
    exact secMk_eq_secMk_iff.mp h1
  · intro h
    exact Subtype.ext (secMk_eq_secMk_iff.mpr h)

theorem modMk_conj_eq_iff {W U : Subgroup G} (hUW : U ≤ Subgroup.normalizer (W : Set G)) {x u : G}
    (hu : u ∈ U) (hxu : x * u * x⁻¹ ∈ U) :
    modMk hUW (x * u * x⁻¹) hxu = modMk hUW u hu ↔ x * u * x⁻¹ * u⁻¹ ∈ W := by
  rw [modMk_eq_modMk_iff hUW hxu hu]
  constructor
  · intro h1
    have h2 : u⁻¹ * (x * u * x⁻¹) ∈ W := by
      have := W.inv_mem h1
      simpa [mul_assoc] using this
    have h3 : u * (u⁻¹ * (x * u * x⁻¹)) * u⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hUW hu) _).mp h2
    have e : u * (u⁻¹ * (x * u * x⁻¹)) * u⁻¹ = x * u * x⁻¹ * u⁻¹ := by group
    rwa [e] at h3
  · intro hc
    have h3 : u⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * u⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hUW (Subgroup.inv_mem _ hu)) _).mp (W.inv_mem hc)
    have e : (x * u * x⁻¹)⁻¹ * u = u⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * u⁻¹⁻¹ := by group
    rw [e]
    exact h3

variable {H W U : Subgroup G}

theorem actE_eq_one_iff [Fact (IsElemAbelian 2 (tildeOf W U))]
    (hWN : H ≤ Subgroup.normalizer (W : Set G)) (hUN : H ≤ Subgroup.normalizer (U : Set G))
    (hUW : U ≤ Subgroup.normalizer (W : Set G)) (x : ↥H) :
    actH hWN hUN x = 1 ↔ ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ W := by
  have hxu : ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ ∈ U := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hUN x.2) u).mp hu
  constructor
  · intro h u hu
    have h1 := congrArg (fun φ : MulAut ↥(tildeOf W U) => φ (modMk hUW u hu)) h
    simp only [MulAut.one_apply] at h1
    rw [actH_modMk hWN hUW hUN x hu, modMk_eq_modMk_iff hUW (hxu u hu) hu] at h1
    have h2 : u⁻¹ * ((x : G) * u * (x : G)⁻¹) ∈ W := by
      have := W.inv_mem h1
      simpa [mul_assoc] using this
    have h3 : u * (u⁻¹ * ((x : G) * u * (x : G)⁻¹)) * u⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hUW hu) _).mp h2
    have e : u * (u⁻¹ * ((x : G) * u * (x : G)⁻¹)) * u⁻¹ = (x : G) * u * (x : G)⁻¹ * u⁻¹ := by
      group
    rwa [e] at h3
  · intro h
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply]
    obtain ⟨a, haU, haw⟩ := exists_mk_of_mem_tilde w
    have hw : w = modMk hUW (a : G) haU := Subtype.ext haw.symm
    rw [hw, actH_modMk hWN hUW hUN x haU, modMk_eq_modMk_iff hUW (hxu _ haU) haU]
    have hc := h (a : G) haU
    have h3 : (a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹)⁻¹ * (a : G)⁻¹⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hUW (Subgroup.inv_mem _ haU)) _).mp (W.inv_mem hc)
    have e : ((x : G) * (a : G) * (x : G)⁻¹)⁻¹ * (a : G) =
        (a : G)⁻¹ * ((x : G) * (a : G) * (x : G)⁻¹ * (a : G)⁻¹)⁻¹ * (a : G)⁻¹⁻¹ := by
      group
    rw [e]
    exact h3

end Mod

section Hyp

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

omit [Finite G] in
theorem isQuasisimple_subgroupOf {H K : Subgroup G} (hKH : K ≤ H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K)) :
    CFSG.IsQuasisimple (↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H)) := by
  let e : ↥(K.subgroupOf H) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKH
  have h1 : (CFSG.pCore 2 ↥(K.subgroupOf H)).map e.toMonoidHom = (pCoreOf 2 K).subgroupOf K := by
    rw [CFSG.LieType.BorelTits.map_pCore_mulEquiv (r := 2) e]
    exact (map_subtype_subgroupOf' (CFSG.Open.pCore 2 K)).symm
  have hn : ((pCoreOf 2 K).subgroupOf K).Normal := inferInstance
  let f := QuotientGroup.congr (CFSG.pCore 2 ↥(K.subgroupOf H)) ((pCoreOf 2 K).subgroupOf K) e h1
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv f.symm hq

theorem actE_eq_one_of_mem_pCoreOf (hF : HypF918 T V L V₁ Vp H K) {W : Subgroup G} (hV₁W : V₁ ≤ W)
    [Fact (IsElemAbelian 2 (tildeOf W (conjClosure Vp H)))]
    (hWN : H ≤ Subgroup.normalizer (W : Set G))
    (hUW : conjClosure Vp H ≤ Subgroup.normalizer (W : Set G)) {x : ↥H}
    (hx : (x : G) ∈ pCoreOf 2 H) :
    actH hWN (le_normalizer_conjClosure Vp H) x = 1 := by
  rw [actE_eq_one_iff hWN (le_normalizer_conjClosure Vp H) hUW]
  intro u hu
  have h1 := V₁.inv_mem (hF.toHypF98.toHypF91.commutator_conjClosure_le u hu x hx)
  have e : (u * (x : G) * u⁻¹ * (x : G)⁻¹)⁻¹ = (x : G) * u * (x : G)⁻¹ * u⁻¹ := by group
  rw [e] at h1
  exact hV₁W h1

omit [Finite G] in
theorem exists_two_pow_mem {H K T : Subgroup G} (hH : H = K ⊔ T) (hT : IsPGroup 2 ↥T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    ∀ y : ↥H, ∃ e : ℕ, y ^ 2 ^ e ∈ K.subgroupOf H := by
  intro y
  obtain ⟨e, he⟩ := InternalSec.two_of_sup hT hTK (y : G) (hH ▸ y.2)
  exact ⟨e, Subgroup.mem_subgroupOf.mpr (by simpa using he)⟩

omit [Finite G] in
theorem normal_subgroupOf_of_le {H K : Subgroup G} (hKH : K ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) : (K.subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHK

omit [Finite G] in
theorem not_forall_comm_of_ne {W : Subgroup G}
    (hWU : W ≤ conjClosure Vp H)
    (hWK : tildeOf V₁ ⁅W, conjClosure K T⁆ = tildeOf V₁ W)
    (ha : ¬ tildeOf V₁ W = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆) :
    ¬ ∀ k ∈ conjClosure K T, ∀ u ∈ conjClosure Vp H, k * u * k⁻¹ * u⁻¹ ∈ W := by
  intro hall
  have hle : ⁅conjClosure Vp H, conjClosure K T⁆ ≤ W := by
    refine Subgroup.commutator_le.mpr fun u hu k hk => ?_
    have := W.inv_mem (hall k hk u hu)
    have e : (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ := by group
    rwa [e] at this
  apply ha
  refine le_antisymm ?_ (secImg_mono hle)
  rw [← hWK]
  exact secImg_mono (Subgroup.commutator_mono hWU le_rfl)

end Hyp

end S153M

end CFSG.Quasithin
