module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma7Act

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

namespace L1297

section Action

variable {G : Type} [Group G] {Z U X : Subgroup G}

@[expose] noncomputable def tRho (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) : ↥X →* MulAut ↥(tildeOf Z U) :=
  (conjAct (tildeOf Z U)).comp
    (((secMk (Subgroup.normalizer (Z : Set G)) Z).comp (Subgroup.inclusion hXZ)).codRestrict
      (Subgroup.normalizer (tildeOf Z U : Set (SecQuot (Subgroup.normalizer (Z : Set G)) Z)))
      (fun k => secMk_mem_normalizer_secImg (a := Subgroup.inclusion hXZ k) (hXU k.2)))

theorem tRho_coe (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (k : ↥X) (w : ↥(tildeOf Z U)) :
    ((tRho hXZ hXU k w : ↥(tildeOf Z U)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ k) * w *
        (secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ k))⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ (Subgroup.inclusion le_rfl _) w

@[expose] def tElt (hU : U ≤ Subgroup.normalizer (Z : Set G)) (u : G) (hu : u ∈ U) :
    ↥(tildeOf Z U) :=
  ⟨secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hU hu⟩, secMk_mem_secImg hu⟩

theorem tElt_coe (hU : U ≤ Subgroup.normalizer (Z : Set G)) (u : G) (hu : u ∈ U) :
    ((tElt hU u hu : ↥(tildeOf Z U)) : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨u, hU hu⟩ := rfl

theorem tElt_mul (hU : U ≤ Subgroup.normalizer (Z : Set G)) {u u' : G} (hu : u ∈ U)
    (hu' : u' ∈ U) : tElt hU u hu * tElt hU u' hu' = tElt hU (u * u') (U.mul_mem hu hu') :=
  Subtype.ext (map_mul (secMk (Subgroup.normalizer (Z : Set G)) Z) ⟨u, hU hu⟩ ⟨u', hU hu'⟩).symm

theorem tElt_inv (hU : U ≤ Subgroup.normalizer (Z : Set G)) {u : G} (hu : u ∈ U) :
    (tElt hU u hu)⁻¹ = tElt hU u⁻¹ (U.inv_mem hu) :=
  Subtype.ext (map_inv (secMk (Subgroup.normalizer (Z : Set G)) Z) ⟨u, hU hu⟩).symm

theorem tElt_eq_one_iff (hU : U ≤ Subgroup.normalizer (Z : Set G)) {u : G} (hu : u ∈ U) :
    tElt hU u hu = 1 ↔ u ∈ Z := by
  have e := secMk_eq_one_iff (A := Subgroup.normalizer (Z : Set G)) (B := Z)
    (x := (⟨u, hU hu⟩ : ↥(Subgroup.normalizer (Z : Set G))))
  constructor
  · intro h
    exact e.1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (e.2 h)

theorem tElt_eq_iff (hU : U ≤ Subgroup.normalizer (Z : Set G)) {u u' : G} (hu : u ∈ U)
    (hu' : u' ∈ U) : tElt hU u hu = tElt hU u' hu' ↔ u⁻¹ * u' ∈ Z := by
  have e := secMk_eq_secMk_iff (A := Subgroup.normalizer (Z : Set G)) (B := Z)
    (x := (⟨u, hU hu⟩ : ↥(Subgroup.normalizer (Z : Set G)))) (y := ⟨u', hU hu'⟩)
  constructor
  · intro h
    exact e.1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (e.2 h)

theorem exists_tElt (hU : U ≤ Subgroup.normalizer (Z : Set G)) (w : ↥(tildeOf Z U)) :
    ∃ u, ∃ hu : u ∈ U, tElt hU u hu = w := by
  obtain ⟨x, hx, hxw⟩ := mem_secImg.1 w.2
  exact ⟨x, hx, Subtype.ext (by rw [tElt_coe]; exact hxw)⟩

theorem tRho_tElt (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    (x : ↥X) {u : G} (hu : u ∈ U) :
    tRho hXZ hXU x (tElt hU u hu) =
      tElt hU ((x : G) * u * (x : G)⁻¹) ((Subgroup.mem_normalizer_iff.1 (hXU x.2) u).1 hu) := by
  apply Subtype.ext
  rw [tRho_coe, tElt_coe, tElt_coe, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem tRho_tElt_eq_iff (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    (x : ↥X) {u : G} (hu : u ∈ U) :
    tRho hXZ hXU x (tElt hU u hu) = tElt hU u hu ↔ (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ Z := by
  rw [tRho_tElt, tElt_eq_iff]
  have hg : (x : G) * u * (x : G)⁻¹ ∈ Subgroup.normalizer (Z : Set G) :=
    hU ((Subgroup.mem_normalizer_iff.1 (hXU x.2) u).1 hu)
  constructor
  · intro h
    have h2 := Z.inv_mem ((Subgroup.mem_normalizer_iff.1 hg _).1 h)
    rwa [show ((x : G) * u * (x : G)⁻¹ * (((x : G) * u * (x : G)⁻¹)⁻¹ * u) *
      ((x : G) * u * (x : G)⁻¹)⁻¹)⁻¹ = (x : G) * u * (x : G)⁻¹ * u⁻¹ by group] at h2
  · intro h
    have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) _).1 (Z.inv_mem h)
    rwa [show ((x : G) * u * (x : G)⁻¹)⁻¹ * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ *
      ((x : G) * u * (x : G)⁻¹)⁻¹⁻¹ = ((x : G) * u * (x : G)⁻¹)⁻¹ * u by group] at h2

theorem tRho_eq_one_iff (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    (x : ↥X) : tRho hXZ hXU x = 1 ↔ ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ Z := by
  constructor
  · intro h u hu
    exact (tRho_tElt_eq_iff hXZ hXU hU x hu).1 (by rw [h, MulAut.one_apply])
  · intro h
    refine MulEquiv.ext fun w => ?_
    obtain ⟨u, hu, rfl⟩ := exists_tElt hU w
    rw [(tRho_tElt_eq_iff hXZ hXU hU x hu).2 (h u hu), MulAut.one_apply]

theorem card_tildeOf_mul (hZU : Z ≤ U) (hUN : U ≤ Subgroup.normalizer (Z : Set G)) :
    Nat.card ↥(tildeOf Z U) * Nat.card ↥Z = Nat.card ↥U := by
  have h2 := relIndex_secImg (A := Subgroup.normalizer (Z : Set G)) (B := Z) (T := Z) (H := U)
    le_rfl hZU hUN
  have h3 : secImg (Subgroup.normalizer (Z : Set G)) Z Z = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
    rw [Subgroup.mem_bot]
    exact secMk_eq_one_iff.2 hx
  rw [h3, Subgroup.relIndex_bot_left] at h2
  have h4 := Subgroup.relIndex_mul_card Z U
  rw [inf_eq_left.2 hZU] at h4
  have h5 : Nat.card ↥(tildeOf Z U) = Z.relIndex U := h2
  rw [h5]
  exact h4

end Action

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_of_commutator_mem {V₁ V₂ : Subgroup G} (hidx : (V₁.subgroupOf V₂).index = 2)
    (hV₁₂ : V₁ ≤ V₂) {v₂ : G} (hv₂ : v₂ ∈ V₂) (hv₂V₁ : v₂ ∉ V₁) {g : G}
    (hg : g ∈ Subgroup.normalizer (V₁ : Set G)) (hc : g * v₂ * g⁻¹ * v₂⁻¹ ∈ V₁) {w : G}
    (hw : w ∈ V₂) : g * w * g⁻¹ ∈ V₂ := by
  by_cases hwV₁ : w ∈ V₁
  · exact hV₁₂ ((Subgroup.mem_normalizer_iff.1 hg w).1 hwV₁)
  have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨w, hw⟩) (b := ⟨v₂, hv₂⟩⁻¹)).2
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
  have hwv : w * v₂⁻¹ ∈ V₁ := key (by rw [V₁.inv_mem_iff]; exact iff_of_false hwV₁ hv₂V₁)
  have h1 : g * (w * v₂⁻¹) * g⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 hg _).1 hwv
  have h2 : g * w * g⁻¹ = (g * (w * v₂⁻¹) * g⁻¹) * (g * v₂ * g⁻¹ * v₂⁻¹) * v₂ := by group
  rw [h2]
  exact V₂.mul_mem (V₂.mul_mem (hV₁₂ h1) (hV₁₂ hc)) hv₂

omit [Finite G] in
theorem mem_normalizer_iff_commutator_mem {V₁ V₂ : Subgroup G}
    (hidx : (V₁.subgroupOf V₂).index = 2) (hV₁₂ : V₁ ≤ V₂) {v₂ : G} (hv₂ : v₂ ∈ V₂)
    (hv₂V₁ : v₂ ∉ V₁) {g : G} (hg : g ∈ Subgroup.normalizer (V₁ : Set G)) :
    g ∈ Subgroup.normalizer (V₂ : Set G) ↔ g * v₂ * g⁻¹ * v₂⁻¹ ∈ V₁ := by
  constructor
  · intro hg₂
    have h1 : g * v₂ * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 hg₂ v₂).1 hv₂
    have h2 : g * v₂ * g⁻¹ ∉ V₁ := fun h3 => hv₂V₁ (by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) _).1 h3
      simpa [mul_assoc] using this)
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨g * v₂ * g⁻¹, h1⟩)
      (b := ⟨v₂, hv₂⟩⁻¹)).2
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
    exact key (by rw [V₁.inv_mem_iff]; exact iff_of_false h2 hv₂V₁)
  · intro hc
    have hc' : g⁻¹ * v₂ * g⁻¹⁻¹ * v₂⁻¹ ∈ V₁ := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) _).1 (V₁.inv_mem hc)
      rwa [show g⁻¹ * (g * v₂ * g⁻¹ * v₂⁻¹)⁻¹ * g⁻¹⁻¹ = g⁻¹ * v₂ * g⁻¹⁻¹ * v₂⁻¹ by group] at h1
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact conj_mem_of_commutator_mem hidx hV₁₂ hv₂ hv₂V₁ hg hc
    · intro hw
      have := conj_mem_of_commutator_mem hidx hV₁₂ hv₂ hv₂V₁ (Subgroup.inv_mem _ hg) hc' hw
      simpa [mul_assoc] using this

theorem relIndex_lOne_inf_normalizer {T L V : Subgroup G} {n : ℕ} (h : Hyp1281One G T L V n)
    {V₁ V₂ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hV₂ : IsTSub T V V₂ 2) (hV₁₂ : V₁ ≤ V₂) :
    (lOne L V₁ ⊓ Subgroup.normalizer (V₂ : Set G)).relIndex (lOne L V₁) = 2 ^ (n - 1) - 1 := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hV₂.2.1
  have hidx : (V₁.subgroupOf V₂).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card V₁ V₂
    rw [inf_eq_left.2 hV₁₂, hV₁2, hV₂4] at h1
    have h2 : V₁.relIndex V₂ = 2 := by omega
    exact h2
  obtain ⟨v₂, hv₂, hv₂V₁⟩ : ∃ v₂ ∈ V₂, v₂ ∉ V₁ := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from fun x hx => hall x hx)
    rw [hV₁2, hV₂4] at h1
    norm_num at h1
  have hv₂V := hV₂.1 hv₂
  set L₁ := lOne L V₁ with hL₁
  have hL₁L : L₁ ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hL₁V₁ : L₁ ≤ Subgroup.normalizer (V₁ : Set G) := (oTwoUpper_le _).trans inf_le_right
  have hL₁V : L₁ ≤ Subgroup.normalizer (V : Set G) := hL₁L.trans h.hyp.irrPlus.2.2.1
  have hVN : V ≤ Subgroup.normalizer (V₁ : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx =>
      hab x (hV₁.1 hx) v hv)
  let _ : MulAction ↥L₁ ↥(tildeOf V₁ V) := MulAction.compHom _ (tRho hL₁V₁ hL₁V)
  set vt := tElt hVN v₂ hv₂V with hvt
  have hsmul : ∀ (l : ↥L₁) (w : ↥(tildeOf V₁ V)), l • w = tRho hL₁V₁ hL₁V l w := fun _ _ => rfl
  have hstab : MulAction.stabilizer ↥L₁ vt =
      (L₁ ⊓ Subgroup.normalizer (V₂ : Set G)).subgroupOf L₁ := by
    ext l
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hvt,
      tRho_tElt_eq_iff hL₁V₁ hL₁V hVN l hv₂V,
      mem_normalizer_iff_commutator_mem hidx hV₁₂ hv₂ hv₂V₁ (hL₁V₁ l.2)]
    exact ⟨fun h1 => ⟨l.2, h1⟩, fun h1 => h1.2⟩
  have horbit : MulAction.orbit ↥L₁ vt = {w | w ≠ 1} := by
    ext w
    simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨l, rfl⟩ h1
      rw [hsmul] at h1
      exact hv₂V₁ ((tElt_eq_one_iff hVN hv₂V).1 ((MulEquiv.map_eq_one_iff _).1 h1))
    · intro hw
      obtain ⟨u, hu, rfl⟩ := exists_tElt hVN w
      have huV₁ : u ∉ V₁ := fun h1 => hw ((tElt_eq_one_iff hVN hu).2 h1)
      obtain ⟨σ, hσ, hσu⟩ := exists_mem_lOne_conj h hV₁ hv₂V hu hv₂V₁ huV₁
      refine ⟨⟨σ, hσ⟩, ?_⟩
      rw [hsmul, hvt, tRho_tElt, tElt_eq_iff]
      have hσv : σ * v₂ * σ⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hL₁V hσ) v₂).1 hv₂V
      have h1 : (σ * v₂ * σ⁻¹)⁻¹ * u = u * (σ * v₂ * σ⁻¹)⁻¹ :=
        (hab u hu _ (V.inv_mem hσv)).symm
      change (σ * v₂ * σ⁻¹)⁻¹ * u ∈ V₁
      rw [h1]
      have := V₁.inv_mem hσu
      rwa [show (σ * v₂ * σ⁻¹ * u⁻¹)⁻¹ = u * (σ * v₂ * σ⁻¹)⁻¹ by group] at this
  have hcardV : Nat.card ↥(tildeOf V₁ V) = 2 ^ (n - 1) := by
    have h1 := card_tildeOf_mul hV₁.1 hVN
    rw [hV₁2, hcard] at h1
    have hn : 1 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> norm_num
    have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hn]
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hidx' := MulAction.index_stabilizer ↥L₁ vt
  rw [hstab, horbit] at hidx'
  change ((L₁ ⊓ Subgroup.normalizer (V₂ : Set G)).subgroupOf L₁).index = _
  rw [hidx']
  have hcompl : {w : ↥(tildeOf V₁ V) | w ≠ 1} = Set.univ \ {1} := by
    ext w
    simp
  rw [hcompl, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcardV]

end L1297

end CFSG.Quasithin.H13
