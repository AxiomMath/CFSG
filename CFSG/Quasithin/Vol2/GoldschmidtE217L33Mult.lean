module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Defs
public import CFSG.GH74.KGroups.L33
public import CFSG.GH74.E2.Shapes
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M E217R3 CFSG.LieType.BorelTits B2F
open scoped MatrixGroups commutatorElement

namespace E217R4

theorem nonempty_mulEquiv_sl33 {X : Type} [Group X] (h : IsPSL 3 3 1 X) :
    Nonempty (X ≃* SL(3, ZMod 3)) := by
  have hL : CFSG.GH74.E2.ShapeL33 X := by
    unfold CFSG.GH74.E2.ShapeL33 CFSG.Blueprint.LieModel
    exact Or.inl ⟨by decide, h⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_lieModel (F := ZMod 3) 3 3 1 (by norm_num)
    CFSG.GH74.KGroups.L33.card_F hL
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq CFSG.GH74.KGroups.L33.center_bot).trans
    QuotientGroup.quotientBot)⟩

theorem commutator_mul_central {X : Type*} [Group X] {s t y z : X} (hy : ∀ g : X, g * y = y * g)
    (hz : ∀ g : X, g * z = z * g) : ⁅s * y, t * z⁆ = ⁅s, t⁆ := by
  simp only [commutatorElement_def]
  have e1 : y * (t * z) * y⁻¹ = t * z := by
    rw [← hy (t * z)]
    group
  calc s * y * (t * z) * (s * y)⁻¹ * (t * z)⁻¹ = s * (y * (t * z) * y⁻¹) * s⁻¹ * (t * z)⁻¹ := by
        group
    _ = s * (t * z) * s⁻¹ * (t * z)⁻¹ := by rw [e1]
    _ = s * t * (z * s⁻¹) * (z⁻¹ * t⁻¹) := by group
    _ = s * t * (s⁻¹ * z) * (z⁻¹ * t⁻¹) := by rw [← hz s⁻¹]
    _ = s * t * s⁻¹ * t⁻¹ := by group

variable {G : Type} [Group G] [Finite G]

theorem kerIn_eq_pCoreOf_of_L33 {H T M V K : Subgroup G} (hS : Setting2 H T M V K)
    (hC2 : Case2 H T M K) (hL : IsPSL 3 3 1 ↥(E2.star M H K)) : kerIn M H = pCoreOf 2 H := by
  have hmp := hS.toHyp2.hyp.minParabolic
  have hKc := hS.mem_cComp
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hOJ : pCoreOf 2 H ≤ kerIn M H := hmp.pCoreOf_le_kerIn
  have hKN : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hKH.trans (le_normalizer_pCoreOf 2 H)
  have hOh : ((pCoreOf 2 H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).2 (le_normalizer_pCoreOf 2 H)
  set Oh : Subgroup ↥H := (pCoreOf 2 H).subgroupOf H with hOhdef
  set π₁ : ↥H →* ↥H ⧸ Oh := QuotientGroup.mk' Oh with hπ₁
  have hker : Oh ≤ (E2P.starMap M H).ker := by
    rw [E2P.ker_starMap]
    exact Subgroup.subgroupOf_mono H hOJ
  set ρ : (↥H ⧸ Oh) →* E2.StarQuot M H := QuotientGroup.lift Oh (E2P.starMap M H) hker with hρ
  have hρπ : ∀ x : ↥H, ρ (π₁ x) = E2P.starMap M H x := fun x => rfl
  set K' : Subgroup ↥H := K.subgroupOf H with hK'
  set Kb : Subgroup (↥H ⧸ Oh) := K'.map π₁ with hKb
  have hmem : ∀ x : ↥Kb, ρ (x : ↥H ⧸ Oh) ∈ E2.star M H K := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    exact ⟨k, hk, rfl⟩
  obtain ⟨θ⟩ := nonempty_mulEquiv_sl33 hL
  let φ : ↥Kb →* ↥(E2.star M H K) := (ρ.comp Kb.subtype).codRestrict (E2.star M H K) hmem
  let π : ↥Kb →* SL(3, ZMod 3) := θ.toMonoidHom.comp φ
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨k, hk, hky⟩ := (θ.symm y).2
    refine ⟨⟨π₁ k, k, hk, rfl⟩, ?_⟩
    show θ (φ ⟨π₁ k, k, hk, rfl⟩) = y
    have : φ ⟨π₁ k, k, hk, rfl⟩ = θ.symm y := Subtype.ext hky
    rw [this, MulEquiv.apply_symm_apply]
  have hcomm : ∀ k ∈ K', ∀ k' ∈ K', E2P.starMap M H k = 1 → π₁ k' * π₁ k = π₁ k * π₁ k' := by
    intro k hk k' hk' h1
    have hkJ : (k : G) ∈ kerIn M H := by
      have : k ∈ (E2P.starMap M H).ker := h1
      rw [E2P.ker_starMap] at this
      exact Subgroup.mem_subgroupOf.1 this
    have hk'K : (k' : G) ∈ K ⊔ pCoreOf 2 H := Subgroup.mem_sup_left hk'
    have h2 := ((hC2.2 (k : G)).1 hkJ).2 (k' : G) hk'K
    have h3 : π₁ ⁅k, k'⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (by
      rw [hOhdef, Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using h2)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h3
    exact h3.symm.eq
  have hcen : π.ker ≤ Subgroup.center ↥Kb := by
    rintro ⟨_, k, hk, rfl⟩ hx
    have hx1 : E2P.starMap M H k = 1 := by
      have h1 : π ⟨π₁ k, k, hk, rfl⟩ = 1 := hx
      have h2 : φ ⟨π₁ k, k, hk, rfl⟩ = 1 := θ.injective (by rw [map_one]; exact h1)
      exact congrArg Subtype.val h2
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, k', hk', rfl⟩
    exact Subtype.ext (hcomm k hk k' hk' hx1)
  have hsep : CFSG.LieType.Steinberg.CentralExt.SLClosed.Separating 2 (ZMod 3) :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (by norm_num)
      (by rw [Nat.card_zmod]; norm_num) (by rw [Nat.card_zmod]; norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating
    (m := 2) (F := ZMod 3) le_rfl hsep hπsurj hcen
  have hperfK' : ⁅K', K'⁆ = K' := perfect_of_mem_cComp (subgroupOf_mem_cComp hKc)
  have hperfKb : ⁅Kb, Kb⁆ = Kb := by
    rw [hKb, ← Subgroup.map_commutator, hperfK']
  have hR : Kb ≤ σ.range.map Kb.subtype := by
    refine le_of_eq_of_le hperfKb.symm (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    set a' : ↥Kb := ⟨a, ha⟩ with ha'
    set b' : ↥Kb := ⟨b, hb⟩ with hb'
    have hcz : ∀ c : ↥Kb, ∀ g : ↥Kb, g * ((σ (π c))⁻¹ * c) = ((σ (π c))⁻¹ * c) * g := fun c g =>
      Subgroup.mem_center_iff.1 (hcen (by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel])) g
    have hab : ⁅a', b'⁆ = ⁅σ (π a'), σ (π b')⁆ := by
      have := commutator_mul_central (s := σ (π a')) (t := σ (π b')) (hcz a') (hcz b')
      rwa [mul_inv_cancel_left, mul_inv_cancel_left] at this
    refine ⟨⁅a', b'⁆, ⟨⁅π a', π b'⁆, ?_⟩, rfl⟩
    rw [map_commutatorElement, hab]
  have hKbT : ∀ x : ↥Kb, ρ (x : ↥H ⧸ Oh) = 1 → x = 1 := by
    intro x hx
    obtain ⟨y, ⟨g, rfl⟩, hyx⟩ := hR x.2
    have hy : σ g = x := Subtype.ext hyx
    have hπx : π x = 1 := by
      show θ (φ x) = 1
      have : φ x = 1 := Subtype.ext hx
      rw [this, map_one]
    have hg : g = 1 := by
      rw [← hy, hσ] at hπx
      exact hπx
    rw [← hy, hg, map_one]
  refine le_antisymm (fun x hx => ?_) hOJ
  have hxK := ((hC2.2 x).1 hx).1
  have hxKO : x ∈ ((pCoreOf 2 H ⊔ K : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hxK
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 H) K hKN] at hxKO
  obtain ⟨o, ho, k, hk, rfl⟩ := hxKO
  have hkJ : k ∈ kerIn M H :=
    by simpa using (kerIn M H).mul_mem ((kerIn M H).inv_mem (hOJ ho)) hx
  have hkH : k ∈ H := hKH hk
  have hk' : (⟨k, hkH⟩ : ↥H) ∈ K' := hk
  have hk1 : E2P.starMap M H ⟨k, hkH⟩ = 1 := by
    have : (⟨k, hkH⟩ : ↥H) ∈ (E2P.starMap M H).ker := by
      rw [E2P.ker_starMap]
      exact Subgroup.mem_subgroupOf.2 hkJ
    exact this
  have hk2 := hKbT ⟨π₁ ⟨k, hkH⟩, ⟨k, hkH⟩, hk', rfl⟩ hk1
  have hk3 : π₁ ⟨k, hkH⟩ = 1 := congrArg Subtype.val hk2
  have hkO : k ∈ pCoreOf 2 H :=
    Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hk3)
  exact (pCoreOf 2 H).mul_mem ho hkO

end E217R4

end CFSG.Quasithin
