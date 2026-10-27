module

public import CFSG.Quasithin.EmptyFaithful.T1531In46
public import CFSG.Quasithin.EmptyFaithful.Der6BMod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement

namespace Der6B

variable {G : Type} [Group G]

section Transfer

variable {V M : Subgroup G} {hV : IsElemAbelian 2 V} {L₁ L₂ : Subgroup (MulAut (IntMod V hV))}
  {tb : MulAut (IntMod V hV)}

theorem totSing_card_le [Finite G] (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hS : OfourStruct (autI hV M) L₁ L₂ tb) {Y : Subgroup G} (hYM : Y ≤ M)
    (h₁ : ⁅V, Y⁆ ⊓ (commV L₁).map (inclMod hV) = ⊥)
    (h₂ : ⁅V, Y⁆ ⊓ (commV L₂).map (inclMod hV) = ⊥) :
    Nat.card ↥(autI hV Y) ≤ 2 ∧
      (¬ Y ≤ Subgroup.centralizer (V : Set G) → Nat.card ↥(V ⊓ Subgroup.centralizer (Y : Set G)) ≤ 4) := by
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := hYM.trans hMV
  have hYX : autI hV Y ≤ autI hV M := autI_mono hV hYM
  have hcomm := commutator_eq_map_commV hV hYN
  have hi := inclMod_injective hV
  have e₁ : commV (autI hV Y) ⊓ commV L₁ = ⊥ := by
    have := h₁
    rw [hcomm, ← Subgroup.map_inf _ _ _ hi] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ hi).1 this
  have e₂ : commV (autI hV Y) ⊓ commV L₂ = ⊥ := by
    have := h₂
    rw [hcomm, ← Subgroup.map_inf _ _ _ hi] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ hi).1 this
  refine ⟨card_le_two_of_inf_sup hS hYX (inf_sup_eq_bot_of_totSing hS e₁ e₂), fun hnc => ?_⟩
  have hne : autI hV Y ≠ ⊥ := fun hbot => hnc ((autI_eq_bot_iff hV hYN).1 hbot)
  have := card_fixV_le_four_of_totSing hS hYX hne e₁ e₂
  rwa [card_fixV_autI hV hYN] at this

theorem fixLine_card_le_two [Finite G]
    (hS : OfourStruct (autI hV M) L₁ L₂ tb) {Y B : Subgroup G} (hYM : Y ≤ M) (hBV : B ≤ V)
    (hB4 : Nat.card B = 4) (h₁ : B ⊓ (commV L₁).map (inclMod hV) = ⊥)
    (h₂ : B ⊓ (commV L₂).map (inclMod hV) = ⊥) (hYB : Y ≤ Subgroup.centralizer (B : Set G)) :
    Nat.card ↥(autI hV Y) ≤ 2 := by
  have hi := inclMod_injective hV
  set E : Subgroup (IntMod V hV) := B.comap (inclMod hV) with hE
  have hEmap : E.map (inclMod hV) = B := by
    rw [hE, Subgroup.map_comap_eq, MonoidHom.range_eq_map, map_inclMod_top]
    exact inf_of_le_right hBV
  have hLine : T1531O4.IsLine (commV L₁) (commV L₂) E := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← Subgroup.card_map_of_injective hi, hEmap, hB4]
    · refine (Subgroup.map_eq_bot_iff_of_injective _ hi).1 ?_
      rw [Subgroup.map_inf _ _ _ hi, hEmap]
      exact h₁
    · refine (Subgroup.map_eq_bot_iff_of_injective _ hi).1 ?_
      rw [Subgroup.map_inf _ _ _ hi, hEmap]
      exact h₂
  refine card_le_two_of_fix_line hS hLine (autI_mono hV hYM) fun y hy w hw => ?_
  obtain ⟨g, hgY, rfl⟩ := (mem_autI hV).1 hy
  refine IntMod.val_injective ?_
  rw [convI_apply_val]
  have hwB : w.val ∈ B := by
    have : inclMod hV w ∈ B := hw
    rwa [inclMod_apply] at this
  have hc := Subgroup.mem_centralizer_iff.mp (hYB hgY) w.val hwB
  calc (g : G) * w.val * (g : G)⁻¹ = (w.val * g) * (g : G)⁻¹ := by rw [hc]
    _ = w.val := by group

end Transfer

section KeyP

variable [Finite G]

theorem mem_normalizer_of_commute {V : Subgroup G} (hV2 : IsPGroup 2 V) (hV16 : Nat.card V = 16)
    (hr : (2 : ℕ∞) ≤ E3.rParam V) {g : G} (hAN : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G))
    (hC4 : 4 ≤ Nat.card ↥(conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G)))
    {x v : G} (hxA : x ∈ conjSubgroup V g) (hxC : x ∉ Subgroup.centralizer (V : Set G)) (hvV : v ∈ V)
    (hxv : x * v = v * x) : v ∈ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  by_contra hvN
  set A := conjSubgroup V g with hA
  set B : Subgroup G := A ⊓ Subgroup.centralizer ({v} : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hB1 : B ≤ A ⊓ Subgroup.normalizer (V : Set G) := le_inf hBA (hBA.trans hAN)
  have hC : ¬ V ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (A : Set G) := by
    intro hle
    apply hvN
    refine hle ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hb.2 v (Set.mem_singleton v)).symm
  have h2 := E3.e3_4_one hB1 hC
  have h2' : 2 ≤ E3.mQuot A B := by
    have := hr.trans h2
    exact_mod_cast this
  have hA2 : IsPGroup 2 A := E3.isPGroup_conjSubgroup hV2 g
  have hAcard : Nat.card A = 16 := by rw [hA, E3.card_conjSubgroup, hV16]
  have hpow := E3.card_eq_two_pow_mul hA2 hBA
  have hB4 : Nat.card B ≤ 4 := by
    have h4 : 2 ^ 2 ≤ 2 ^ E3.mQuot A B := Nat.pow_le_pow_right (by norm_num) h2'
    rw [hAcard] at hpow
    have hpos : 0 < Nat.card B := Nat.card_pos
    nlinarith
  set C : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hCdef
  have hCB : C ≤ B := fun c hc => ⟨hc.1, Subgroup.mem_centralizer_iff.mpr fun w hw => by
    rw [Set.mem_singleton_iff.mp hw]
    exact Subgroup.mem_centralizer_iff.mp hc.2 v hvV⟩
  have hxB : x ∈ B := ⟨hxA, Subgroup.mem_centralizer_iff.mpr fun w hw => by
    rw [Set.mem_singleton_iff.mp hw]
    exact hxv.symm⟩
  have hxnC : x ∉ C := fun hc => hxC hc.2
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hCB
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hlt' : k < 2 := not_le.mp hlt
    interval_cases k
    · have : Nat.card B = 0 := by rw [hk]; ring
      exact absurd this Nat.card_pos.ne'
    · have heq : C = B := Subgroup.eq_of_le_of_card_ge hCB (le_of_eq (by rw [hk, mul_one]))
      exact hxnC (heq ▸ hxB)
  have : 8 ≤ Nat.card B := by
    rw [hk]
    nlinarith
  omega

end KeyP

section Case2

variable [Finite G] {V M T : Subgroup G} {hV : IsElemAbelian 2 V}
  {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}

theorem case2_false (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hHv : Subgroup.normalizer (V : Set G) ≤ M) (hS : OfourStruct (autI hV M) L₁ L₂ tb)
    (hT' : IsSylowTwoOf (autI hV T) (autI hV M)) (hTM : T ≤ M) (hV16 : Nat.card V = 16)
    (hV2 : IsPGroup 2 V) (hr : (2 : ℕ∞) ≤ E3.rParam V)
    (htot : ∀ B : Subgroup G, B ≤ V → ⊥ < B → B < V →
      ¬ Subgroup.normalizer (B : Set G) ≤ M →
      B ⊓ (commV L₁).map (inclMod hV) = ⊥ ∧ B ⊓ (commV L₂).map (inclMod hV) = ⊥)
    {g : G} (hgT : conjSubgroup V g ≤ T)
    (hVA : ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)) : False := by
  classical
  set A := conjSubgroup V g with hA
  have hAM : A ≤ M := hgT.trans hTM
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hAe : IsElemAbelian 2 A := E3.isElemAbelian_conjSubgroup hV g
  have hAcard : Nat.card A = 16 := by rw [hA, E3.card_conjSubgroup, hV16]
  have hA2 : IsPGroup 2 A := E3.isPGroup_conjSubgroup hV2 g
  set C := A ⊓ Subgroup.centralizer (V : Set G) with hCdef
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hCle4 : Nat.card C ≤ 4 := by
    have h2 := E3.e3_4_two (V := V) (g := g) hVA
    have h2' : 2 ≤ E3.mQuot A C := by
      have := hr.trans h2
      exact_mod_cast this
    have hpow := E3.card_eq_two_pow_mul hA2 (inf_le_left : C ≤ A)
    rw [hAcard] at hpow
    have h4 : 2 ^ 2 ≤ 2 ^ E3.mQuot A C := Nat.pow_le_pow_right (by norm_num) h2'
    nlinarith
  have hAbe : IsElemAbelian2 (autI hV A) := isElemAbelian2_autI hV hAe hAN
  have hAbT : autI hV A ≤ autI hV T := autI_mono hV hgT
  have hprod : Nat.card ↥(autI hV A) * Nat.card C = Nat.card A := card_autI_mul_card_inf hV hAN
  rw [hAcard] at hprod
  have hAb4 : 4 ≤ Nat.card ↥(autI hV A) := by
    have : 16 ≤ 4 * Nat.card ↥(autI hV A) := by nlinarith
    omega
  have hAb4' : Nat.card ↥(autI hV A) ≤ 4 := card_le_four_of_elemAbelian hS hT' hAbT hAbe
  have hC4 : Nat.card C = 4 := by
    have : Nat.card ↥(autI hV A) = 4 := le_antisymm hAb4' hAb4
    rw [this] at hprod
    omega
  set Nb : Subgroup (IntMod V hV) :=
    (V ⊓ Subgroup.normalizer (A : Set G)).comap (inclMod hV) with hNb
  have hmemNb : ∀ w : IntMod V hV, w ∈ Nb ↔ w.val ∈ Subgroup.normalizer (A : Set G) := fun w => by
    rw [hNb, Subgroup.mem_comap, inclMod_apply, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨w.val_mem, h⟩⟩
  have hNbtop : Nb ≠ ⊤ := by
    intro htop
    apply hVA
    intro v hv
    have : IntMod.mk hV ⟨v, hv⟩ ∈ Nb := by rw [htop]; exact Subgroup.mem_top _
    exact (hmemNb _).1 this
  have hP : ∀ y ∈ autI hV A, y ≠ 1 → ∀ w, y w = w → w ∈ Nb := by
    intro y hy hy1 w hw
    obtain ⟨x, hxA, rfl⟩ := (mem_autI hV).1 hy
    have hxC : (x : G) ∉ Subgroup.centralizer (V : Set G) := fun hc =>
      hy1 ((convI_eq_one_iff hV x).2 hc)
    have hxw : (x : G) * w.val = w.val * (x : G) := by
      have := congrArg IntMod.val hw
      rw [convI_apply_val] at this
      calc (x : G) * w.val = ((x : G) * w.val * (x : G)⁻¹) * x := by group
        _ = w.val * x := by rw [this]
    exact (hmemNb w).2 (mem_normalizer_of_commute hV2 hV16 hr hAN (hC4 ▸ le_rfl) hxA hxC
      w.val_mem hxw)
  obtain ⟨U, hUN, hU4⟩ := exists_fix_sup hS hT' hAbT hAbe hAb4 hNbtop hP
  set UG : Subgroup G := U.map (inclMod hV) with hUG
  have hUGV : UG ≤ V := map_inclMod_le hV U
  have hUGN : UG ≤ Subgroup.normalizer (A : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hmemNb u).1 (hUN hu)
  have hUGcard : Nat.card UG = Nat.card U := Subgroup.card_map_of_injective (inclMod_injective hV)
  have hUGfix : Nat.card ↥(UG ⊓ Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(U ⊓ fixV (autI hV A)) := by
    have : UG ⊓ Subgroup.centralizer (A : Set G) = (U ⊓ fixV (autI hV A)).map (inclMod hV) := by
      ext v
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, hvC⟩
        refine ⟨u, ⟨hu, (mem_fixV_autI hV hAN u).2 ?_⟩, rfl⟩
        rwa [← inclMod_apply hV u]
      · rintro ⟨u, ⟨hu, hfix⟩, rfl⟩
        refine ⟨⟨u, hu, rfl⟩, ?_⟩
        rw [inclMod_apply]
        exact (mem_fixV_autI hV hAN u).1 hfix
    rw [this, Subgroup.card_map_of_injective (inclMod_injective hV)]
  have hUG4 : 4 * Nat.card ↥(UG ⊓ Subgroup.centralizer (A : Set G)) ≤ Nat.card UG := by
    rw [hUGfix, hUGcard]
    exact hU4
  have hAinv : conjSubgroup A g⁻¹ = V := E3.conjSubgroup_conj_inv V g
  set U'' := conjSubgroup UG g⁻¹ with hU''
  have hU''N : U'' ≤ Subgroup.normalizer (V : Set G) := by
    have := E3.conjSubgroup_mono_left g⁻¹ hUGN
    rwa [E3.conjSubgroup_normalizer, hAinv] at this
  have hU''M : U'' ≤ M := hU''N.trans hHv
  have hU''card : Nat.card U'' = Nat.card UG := E3.card_conjSubgroup _ _
  have hU''fix : Nat.card ↥(U'' ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(UG ⊓ Subgroup.centralizer (A : Set G)) := by
    have : U'' ⊓ Subgroup.centralizer (V : Set G) =
        conjSubgroup (UG ⊓ Subgroup.centralizer (A : Set G)) g⁻¹ := by
      rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, hAinv]
    rw [this, E3.card_conjSubgroup]
  have hU''4 : 4 ≤ Nat.card ↥(autI hV U'') := by
    have h1 := card_autI_mul_card_inf hV hU''N
    have hpos : 0 < Nat.card ↥(U'' ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
    rw [← hU''card, ← hU''fix] at hUG4
    nlinarith
  set B' := conjSubgroup C g⁻¹ with hB'
  have hB'V : B' ≤ V := by
    have := E3.conjSubgroup_mono_left g⁻¹ (inf_le_left : C ≤ A)
    rwa [hAinv] at this
  have hB'card : Nat.card B' = 4 := by rw [hB', E3.card_conjSubgroup, hC4]
  have hU''B' : U'' ≤ Subgroup.centralizer (B' : Set G) := by
    have h1 : UG ≤ Subgroup.centralizer (C : Set G) := fun u hu =>
      Subgroup.mem_centralizer_iff.mpr fun c hc =>
        (Subgroup.mem_centralizer_iff.mp hc.2 u (hUGV hu)).symm
    have := E3.conjSubgroup_mono_left g⁻¹ h1
    rwa [E3.conjSubgroup_centralizer] at this
  have hB'N : ¬ Subgroup.normalizer (B' : Set G) ≤ M := by
    intro hle
    obtain ⟨v, hvV, hvN⟩ := Set.not_subset.mp hVA
    have hv'C : g * v * g⁻¹ ∈ Subgroup.centralizer (B' : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun b' hb' => ?_
      have hb : g⁻¹ * b' * g ∈ C := E3.mem_conjSubgroup_inv_iff.mp hb'
      have hc := Subgroup.mem_centralizer_iff.mp hb.2 v hvV
      calc b' * (g * v * g⁻¹) = g * ((g⁻¹ * b' * g) * v) * g⁻¹ := by group
        _ = g * (v * (g⁻¹ * b' * g)) * g⁻¹ := by rw [hc]
        _ = g * v * g⁻¹ * b' := by group
    have hv'M : g * v * g⁻¹ ∈ M := hle (Subgroup.centralizer_le_normalizer _ hv'C)
    apply hvN
    have : v ∈ conjSubgroup (Subgroup.normalizer (V : Set G)) g := by
      rw [mem_conjSubgroup_iff]
      exact hMV hv'M
    rwa [E3.conjSubgroup_normalizer] at this
  have hB'pos : ⊥ < B' := by
    refine bot_lt_iff_ne_bot.mpr fun hbot => ?_
    rw [hbot, Subgroup.card_bot] at hB'card
    omega
  have hB'lt : B' < V := by
    refine lt_of_le_of_ne hB'V fun heq => ?_
    rw [heq, hV16] at hB'card
    omega
  obtain ⟨h₁, h₂⟩ := htot B' hB'V hB'pos hB'lt hB'N
  have := fixLine_card_le_two hS hU''M hB'V hB'card h₁ h₂ hU''B'
  omega

end Case2

section Case1

variable [Finite G] {V M : Subgroup G} {hV : IsElemAbelian 2 V}
  {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}

theorem case1_false (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hHv : Subgroup.normalizer (V : Set G) ≤ M) (hS : OfourStruct (autI hV M) L₁ L₂ tb)
    (hV16 : Nat.card V = 16)
    (htot : ∀ x : G, x ∉ M →
      (V ⊓ conjSubgroup V x) ⊓ (commV L₁).map (inclMod hV) = ⊥ ∧
        (V ⊓ conjSubgroup V x) ⊓ (commV L₂).map (inclMod hV) = ⊥)
    {g : G} (hgM : g ∉ M) (hAM : conjSubgroup V g ≤ M)
    (hVA : V ≤ Subgroup.normalizer (conjSubgroup V g : Set G))
    (hnle : ¬ conjSubgroup V g ≤ Subgroup.centralizer (V : Set G)) : False := by
  classical
  set A := conjSubgroup V g with hA
  set A' := conjSubgroup V g⁻¹ with hA'
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := hAM.trans hMV
  have hA'N : A' ≤ Subgroup.normalizer (V : Set G) := by
    intro x hx
    have h1 : V ≤ conjSubgroup (Subgroup.normalizer (V : Set G)) g := by
      rw [E3.conjSubgroup_normalizer]
      exact hVA
    have hv : g⁻¹ * x * g ∈ V := E3.mem_conjSubgroup_inv_iff.mp hx
    have := h1 hv
    rw [mem_conjSubgroup_iff] at this
    simpa [mul_assoc] using this
  have hVA' : V ≤ Subgroup.normalizer (A' : Set G) := by
    intro v hv
    have h1 : g⁻¹ * v * g ∈ A := by
      rw [hA, mem_conjSubgroup_iff]
      simpa [mul_assoc] using hv
    have h2 : v ∈ conjSubgroup (Subgroup.normalizer (V : Set G)) g⁻¹ :=
      E3.mem_conjSubgroup_inv_iff.mpr (hAN h1)
    rwa [E3.conjSubgroup_normalizer] at h2
  have hcomm : ∀ (B : Subgroup G), B ≤ Subgroup.normalizer (V : Set G) →
      V ≤ Subgroup.normalizer (B : Set G) → ⁅V, B⁆ ≤ V ⊓ B := by
    intro B hBN hVB
    rw [Subgroup.commutator_le]
    intro v hv a ha
    refine ⟨?_, ?_⟩
    · have h1 : a * v⁻¹ * a⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hBN ha) v⁻¹).mp (V.inv_mem hv)
      have : ⁅v, a⁆ = v * (a * v⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact V.mul_mem hv h1
    · have h1 : v * a * v⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hVB hv) a).mp ha
      have : ⁅v, a⁆ = (v * a * v⁻¹) * a⁻¹ := by simp [commutatorElement_def]
      rw [this]
      exact B.mul_mem h1 (B.inv_mem ha)
  have hg'M : g⁻¹ ∉ M := fun h => hgM (by simpa using M.inv_mem h)
  obtain ⟨t₁, t₂⟩ := htot g hgM
  obtain ⟨t₁', t₂'⟩ := htot g⁻¹ hg'M
  have hcommA := hcomm A hAN hVA
  have hcommA' := hcomm A' hA'N hVA'
  have hA1 : ⁅V, A⁆ ⊓ (commV L₁).map (inclMod hV) = ⊥ :=
    eq_bot_iff.mpr (t₁ ▸ inf_le_inf_right _ hcommA)
  have hA2 : ⁅V, A⁆ ⊓ (commV L₂).map (inclMod hV) = ⊥ :=
    eq_bot_iff.mpr (t₂ ▸ inf_le_inf_right _ hcommA)
  have hA'1 : ⁅V, A'⁆ ⊓ (commV L₁).map (inclMod hV) = ⊥ :=
    eq_bot_iff.mpr (t₁' ▸ inf_le_inf_right _ hcommA')
  have hA'2 : ⁅V, A'⁆ ⊓ (commV L₂).map (inclMod hV) = ⊥ :=
    eq_bot_iff.mpr (t₂' ▸ inf_le_inf_right _ hcommA')
  have hAbound := (totSing_card_le hMV hS hAM hA1 hA2).1
  have hA'M : A' ≤ M := hA'N.trans hHv
  have hnc' : ¬ A' ≤ Subgroup.centralizer (V : Set G) := by
    intro hc
    apply hnle
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have hy : g * v * g⁻¹ ∈ A' := E3.mem_conjSubgroup_inv_iff.mpr (by simpa [mul_assoc] using hv)
    have hz : g * x * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
    have h1 := Subgroup.mem_centralizer_iff.mp (hc hy) _ hz
    have h2 : g * (x * v) * g⁻¹ = g * (v * x) * g⁻¹ := by
      calc g * (x * v) * g⁻¹ = (g * x * g⁻¹) * (g * v * g⁻¹) := by group
        _ = (g * v * g⁻¹) * (g * x * g⁻¹) := h1
        _ = g * (v * x) * g⁻¹ := by group
    exact (mul_left_cancel (mul_right_cancel h2)).symm
  have hA'bound := (totSing_card_le hMV hS hA'M hA'1 hA'2).2 hnc'
  have hconj : Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) =
      Nat.card ↥(V ⊓ Subgroup.centralizer (A' : Set G)) := by
    have : conjSubgroup (V ⊓ Subgroup.centralizer (A' : Set G)) g =
        A ⊓ Subgroup.centralizer (V : Set G) := by
      rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer, hA', E3.conjSubgroup_inv_conj]
    rw [← this, E3.card_conjSubgroup]
  have h1 := card_autI_mul_card_inf hV hAN
  have hAcard : Nat.card A = 16 := by rw [hA, E3.card_conjSubgroup, hV16]
  rw [hAcard] at h1
  have hpos := Nat.card_pos (α := ↥(A ⊓ Subgroup.centralizer (V : Set G)))
  have h8 : 8 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := by
    nlinarith [Nat.mul_le_mul_right (Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G))) hAbound]
  omega

end Case1

section Main

variable [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem centralizes_of_conj_le (c : Ctx153 G T Mc M V₁ V₂ t) (e : Res15346Easy T M V₁ V₂) {g : G}
    (hgT : conjSubgroup (VZ T M) g ≤ T) :
    conjSubgroup (VZ T M) g ≤ Subgroup.centralizer (VZ T M : Set G) := by
  classical
  have h := c.hyp
  have hr : (2 : ℕ∞) ≤ E3.rParam (VZ T M) := by
    have h1 := e.one_lt_r
    have h2 : (1 : ℕ∞) + 1 ≤ E3.rParam (VZ T M) :=
      (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr h1
    rwa [one_add_one_eq_two] at h2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer
  have hHv : M = Subgroup.normalizer (VZ T M : Set G) := h.isHv_of_inM' h.inM
  have hV2 : IsPGroup 2 (VZ T M) := B2F.isPGroup_of_isElemAbelian h.elemAbelian
  by_cases hgM : g ∈ M
  · have hAV : conjSubgroup (VZ T M) g = VZ T M :=
      conjSubgroup_eq_iff_mem_normalizer.2 (hMV hgM)
    rw [hAV]
    intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => B2F.isElemAbelian_comm h.elemAbelian hv hx
  by_contra hnle
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -⟩ := c.decomp.model
  have htot₁ : ∀ x : G, x ∉ M →
      (VZ T M ⊓ conjSubgroup (VZ T M) x) ⊓ (commV L₁).map (inclMod hV) = ⊥ ∧
        (VZ T M ⊓ conjSubgroup (VZ T M) x) ⊓ (commV L₂).map (inclMod hV) = ⊥ := fun x hx =>
    ⟨(e.totSingular_inter x hx).2.1, (e.totSingular_inter x hx).2.2⟩
  have htot₂ : ∀ B : Subgroup G, B ≤ VZ T M → ⊥ < B → B < VZ T M →
      ¬ Subgroup.normalizer (B : Set G) ≤ M →
      B ⊓ (commV L₁).map (inclMod hV) = ⊥ ∧ B ⊓ (commV L₂).map (inclMod hV) = ⊥ :=
    fun B hB h1 h2 hN =>
      ⟨(e.totSingular_of_normalizer B hB h1 h2 hN).2.1,
        (e.totSingular_of_normalizer B hB h1 h2 hN).2.2⟩
  by_cases hVA : VZ T M ≤ Subgroup.normalizer (conjSubgroup (VZ T M) g : Set G)
  · exact case1_false hMV hHv.ge hS h.card_VZ htot₁ hgM (hgT.trans h.T_le) hVA hnle
  · exact case2_false hMV hHv.ge hS h.isSylowTwoOf_autI h.T_le h.card_VZ hV2 hr htot₂ hgT hVA

theorem res15346W0_of (c : Ctx153 G T Mc M V₁ V₂ t) (e : Res15346Easy T M V₁ V₂) :
    Res15346W0 T M := by
  have hV2 : IsPGroup 2 (VZ T M) := B2F.isPGroup_of_isElemAbelian c.hyp.elemAbelian
  unfold Res15346W0 E3.wClos
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  have hAeq : A = conjSubgroup (VZ T M) g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) hAg).1 hm
  rw [hAeq]
  exact centralizes_of_conj_le c e (hAeq ▸ hAT)

end Main

end Der6B

theorem stage15346Four_of : Stage15346Four :=
  fun _ _ _ _ _ _ _ _ _ c _ e => Der6B.res15346W0_of c e

end CFSG.Quasithin
