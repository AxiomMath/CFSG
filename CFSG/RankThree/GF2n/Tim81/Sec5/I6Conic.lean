module

import CFSG.RankThree.GF2n.Tim81.Sec5.S53S55
public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec45Shape

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Timmesfeld.Bridge
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V H : Subgroup G} {h₀ : G}

namespace Sec45Shape

private theorem commute_of_mem_xOf (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {x y : G} (hx : x ∈ Tim79a.xOf V H) (hy : y ∈ Tim79a.xOf V H) : x * y = y * x :=
  congrArg Subtype.val ((hS.isElemAbelian h).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem card_eq_of_mem_pts {C : Subgroup G}
    (hC : C ∈ Tim79a.omegaOf V H) : Nat.card C = Nat.card V := by
  obtain ⟨y, _, rfl⟩ := hC
  exact card_conjSubgroup y V

private theorem inf_eq_bot_of_mem_pts (h : RootHyp M V) {C C' : Subgroup G}
    (hC : C ∈ Tim79a.omegaOf V H) (hC' : C' ∈ Tim79a.omegaOf V H) (hne : C ≠ C') :
    C ⊓ C' = ⊥ := by
  obtain ⟨y, _, rfl⟩ := hC
  obtain ⟨y', _, rfl⟩ := hC'
  by_contra hbot
  have hne' : conjSubgroup (y⁻¹ * y') V ≠ V := by
    intro hEq
    apply hne
    calc conjSubgroup y V = conjSubgroup y (conjSubgroup (y⁻¹ * y') V) := by rw [hEq]
      _ = conjSubgroup (y * (y⁻¹ * y')) V :=
          conjSubgroup_conjSubgroup y (y⁻¹ * y') V
      _ = conjSubgroup y' V := by rw [show y * (y⁻¹ * y') = y' by group]
  have hinf : V ⊓ conjSubgroup (y⁻¹ * y') V = ⊥ :=
    inf_conjSubgroup_eq_bot_of_isTI h.toHyp.ti hne'
  have hconj : conjSubgroup y⁻¹ (conjSubgroup y V ⊓ conjSubgroup y' V) =
      V ⊓ conjSubgroup (y⁻¹ * y') V := by
    rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
      show y⁻¹ * y = 1 by group, conjSubgroup_one]
  have hbot' : conjSubgroup y⁻¹ (conjSubgroup y V ⊓ conjSubgroup y' V) ≠ ⊥ := by
    intro hEq
    apply hbot
    calc conjSubgroup y V ⊓ conjSubgroup y' V
        = conjSubgroup y (conjSubgroup y⁻¹ (conjSubgroup y V ⊓ conjSubgroup y' V)) := by
            rw [conjSubgroup_conjSubgroup, show y * y⁻¹ = 1 by group, conjSubgroup_one]
      _ = conjSubgroup y ⊥ := by rw [hEq]
      _ = ⊥ := Subgroup.map_bot _
  rw [hconj] at hbot'
  exact hbot' hinf

private theorem inf_V_eq_bot_of_mem_pts (h : RootHyp M V) {C : Subgroup G}
    (hC : C ∈ Tim79a.omegaOf V H) (hCV : C ≠ V) : V ⊓ C = ⊥ := by
  obtain ⟨y, _, rfl⟩ := hC
  exact inf_conjSubgroup_eq_bot_of_isTI h.toHyp.ti hCV

private theorem exists_mul_of_mem_sup (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {C : Subgroup G} (hC : C ∈ Tim79a.omegaOf V H) {x : G}
    (hx : x ∈ V ⊔ C) : ∃ v ∈ V, ∃ c ∈ C, v * c = x := by
  have hcomm : ∀ v ∈ V, ∀ c ∈ C, v * c = c * v := fun v hv c hc =>
    commute_of_mem_xOf h hS (le_xOf_self V H hv) (Tim79a.le_xOf hC hc)
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V C hcomm).2
  change x ∈ ((V ⊔ C : Subgroup G) : Set G) at hx
  rw [hset, Set.mem_mul] at hx
  exact hx

private theorem card_sup_eq_sq (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {C : Subgroup G} (hC : C ∈ Tim79a.omegaOf V H) (hCV : C ≠ V) :
    Nat.card ↥(V ⊔ C) = Nat.card V ^ 2 := by
  have hcomm : ∀ v ∈ V, ∀ c ∈ C, v * c = c * v := fun v hv c hc =>
    commute_of_mem_xOf h hS (le_xOf_self V H hv) (Tim79a.le_xOf hC hc)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute V C hcomm).1
  rw [inf_V_eq_bot_of_mem_pts h hC hCV, card_eq_of_mem_pts hC, Subgroup.card_bot,
    mul_one] at hprod
  simpa [pow_two] using hprod

theorem mem_or_mem_of_points (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {C₁ C₂ : Subgroup G} (h₁ : C₁ ∈ Tim79a.omegaOf V H)
    (h₂ : C₂ ∈ Tim79a.omegaOf V H) (hne : C₁ ≠ C₂) {d : G}
    (hd : d ∈ C₁ ⊔ C₂) (hdD : d ∈ Tim78.classD V) : d ∈ C₁ ∨ d ∈ C₂ := by
  classical
  obtain ⟨y₁, hy₁, rfl⟩ := h₁
  obtain ⟨y₂, hy₂, rfl⟩ := h₂
  set e := y₁⁻¹ * y₂ with he
  have heH : e ∈ H := H.mul_mem (H.inv_mem hy₁) hy₂
  have heV : conjSubgroup e V ≠ V := by
    intro hEq
    apply hne
    calc conjSubgroup y₁ V = conjSubgroup y₁ (conjSubgroup e V) := by rw [hEq]
      _ = conjSubgroup (y₁ * e) V := conjSubgroup_conjSubgroup y₁ e V
      _ = conjSubgroup y₂ V := by rw [he]; group
  have hd' : y₁⁻¹ * d * y₁ ∈ V ⊔ conjSubgroup e V := by
    have h1 : conjSubgroup y₁⁻¹ (conjSubgroup y₁ V ⊔ conjSubgroup y₂ V) =
        V ⊔ conjSubgroup e V := by
      change (conjSubgroup y₁ V ⊔ conjSubgroup y₂ V).map
        (MulAut.conj y₁⁻¹).toMonoidHom = V ⊔ conjSubgroup e V
      rw [Subgroup.map_sup]
      change conjSubgroup y₁⁻¹ (conjSubgroup y₁ V) ⊔
        conjSubgroup y₁⁻¹ (conjSubgroup y₂ V) = V ⊔ conjSubgroup e V
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup,
        show y₁⁻¹ * y₁ = 1 by group, conjSubgroup_one]
    rw [← h1]
    exact mem_conjSubgroup.mpr (by
      have h0 : (y₁⁻¹)⁻¹ * (y₁⁻¹ * d * y₁) * y₁⁻¹ = d := by group
      rw [h0]
      exact hd)
  have hdD' : y₁⁻¹ * d * y₁ ∈ Tim78.classD V := by
    simpa using Tim78.mem_classD_conj (B := V) hdD y₁⁻¹
  have hmain := mem_or_mem_of_mem_sup h hS heH heV hd' hdD'
  rcases hmain with hV | hU
  · left
    exact mem_conjSubgroup.mpr hV
  · right
    have h2 : conjSubgroup y₁⁻¹ (conjSubgroup y₂ V) = conjSubgroup e V := by
      rw [conjSubgroup_conjSubgroup]
    have hmem : y₁⁻¹ * d * y₁ ∈ conjSubgroup y₁⁻¹ (conjSubgroup y₂ V) := by
      rw [h2]
      exact hU
    have hmem' : d ∈ conjSubgroup y₁ (conjSubgroup y₁⁻¹ (conjSubgroup y₂ V)) := by
      refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
      show y₁ * (y₁⁻¹ * d * y₁) * y₁⁻¹ = d
      group
    rwa [conjSubgroup_conjSubgroup, show y₁ * y₁⁻¹ = 1 by group,
      conjSubgroup_one] at hmem'

private theorem inf_sup_sup_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {C C' : Subgroup G} (hC : C ∈ Tim79a.omegaOf V H)
    (hC' : C' ∈ Tim79a.omegaOf V H) (hne : C ≠ C') :
    (V ⊔ C) ⊓ (V ⊔ C') = V := by
  by_cases hCV : C = V
  · subst hCV
    rw [sup_idem]
    exact inf_eq_left.mpr le_sup_left
  by_cases hC'V : C' = V
  · subst hC'V
    rw [sup_idem]
    exact inf_eq_right.mpr le_sup_left
  refine le_antisymm ?_ (le_inf le_sup_left le_sup_left)
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨v, hv, c, hc, rfl⟩ := exists_mul_of_mem_sup h hS hC hx1
  obtain ⟨v', hv', c', hc', h_eq⟩ := exists_mul_of_mem_sup h hS hC' hx2
  by_cases hz1 : v'⁻¹ * v = 1
  · have hvv : v = v' := by
      calc v = v' * (v'⁻¹ * v) := by group
        _ = v' * 1 := by rw [hz1]
        _ = v' := mul_one v'
    have hcc : c = c' := by
      have h1 : v * c' = v * c := by simpa [hvv] using h_eq
      exact (mul_left_cancel h1).symm
    have hcbot : c ∈ C ⊓ C' := Subgroup.mem_inf.mpr ⟨hc, hcc ▸ hc'⟩
    rw [inf_eq_bot_of_mem_pts h hC hC' hne] at hcbot
    have hc1 : c = 1 := Subgroup.mem_bot.mp hcbot
    simpa [hc1] using hv
  · have hzV : v'⁻¹ * v ∈ V := V.mul_mem (V.inv_mem hv') hv
    have hz_eq : v'⁻¹ * v = c' * c⁻¹ := by
      calc v'⁻¹ * v = v'⁻¹ * (v' * c') * c⁻¹ := by rw [h_eq]; group
        _ = c' * c⁻¹ := by group
    have hz_sup : v'⁻¹ * v ∈ C ⊔ C' := by
      rw [hz_eq]
      exact (C ⊔ C').mul_mem (Subgroup.mem_sup_right hc')
        (Subgroup.mem_sup_left (C.inv_mem hc))
    have hzV' : v'⁻¹ * v ∈ conjSubgroup (1 : G) V := by
      simpa [conjSubgroup_one] using hzV
    have hzD : v'⁻¹ * v ∈ Tim78.classD V :=
      Tim78.mem_classD_of_mem_conjSubgroup (B := V) (g := 1) hzV' hz1
    rcases mem_or_mem_of_points h hS hC hC' hne hz_sup hzD with hzC | hzC'
    · have hmem : v'⁻¹ * v ∈ V ⊓ C := Subgroup.mem_inf.mpr ⟨hzV, hzC⟩
      rw [inf_V_eq_bot_of_mem_pts h hC hCV] at hmem
      exact absurd (Subgroup.mem_bot.mp hmem) hz1
    · have hmem : v'⁻¹ * v ∈ V ⊓ C' := Subgroup.mem_inf.mpr ⟨hzV, hzC'⟩
      rw [inf_V_eq_bot_of_mem_pts h hC' hC'V] at hmem
      exact absurd (Subgroup.mem_bot.mp hmem) hz1

theorem card_add_le (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    (𝒞 : Finset (Subgroup G)) (hpts : ∀ C ∈ 𝒞, C ∈ Tim79a.omegaOf V H)
    (hV : V ∈ 𝒞) {X : Subgroup G} (hX : ∀ C ∈ 𝒞, C ≤ X) :
    Nat.card V + (𝒞.card - 1) * (Nat.card V ^ 2 - Nat.card V) ≤ Nat.card X := by
  classical
  let q := Nat.card V
  let d := q ^ 2 - q
  let L := 𝒞.erase V
  let D : Subgroup G → Set G := fun C => ((V ⊔ C : Subgroup G) : Set G) \ (V : Set G)
  let U : Finset (Subgroup G) → Set G :=
    fun T => (V : Set G) ∪ ⋃ C ∈ (T : Set (Subgroup G)), D C
  change Nat.card V + (𝒞.card - 1) * d ≤ Nat.card X
  have hLmem : ∀ C ∈ L, C ∈ 𝒞 := fun C hC => Finset.mem_of_mem_erase hC
  have hLne : ∀ C ∈ L, C ≠ V := fun C hC => Finset.ne_of_mem_erase hC
  have hDcard : ∀ C ∈ L, (D C).ncard = d := by
    intro C hC
    have hCV : C ≠ V := hLne C hC
    have hCpts : C ∈ Tim79a.omegaOf V H := hpts C (hLmem C hC)
    have hsub : (V : Set G) ⊆ ((V ⊔ C : Subgroup G) : Set G) :=
      fun x hx => Subgroup.mem_sup_left hx
    have hcard : Nat.card ↥(V ⊔ C) = q ^ 2 := by
      simpa [q] using card_sup_eq_sq h hS hCpts hCV
    calc (D C).ncard
        = ((V ⊔ C : Subgroup G) : Set G).ncard - (V : Set G).ncard := Set.ncard_sdiff hsub
      _ = Nat.card ↥(V ⊔ C) - Nat.card ↥V := rfl
      _ = d := by rw [hcard]
  have hdisjV : ∀ C ∈ L, Disjoint (D C) (V : Set G) := fun C _ => Set.disjoint_sdiff_left
  have hdisj : ∀ C ∈ L, ∀ C' ∈ L, C ≠ C' → Disjoint (D C) (D C') := by
    intro C hC C' hC' hne
    have hCpts : C ∈ Tim79a.omegaOf V H := hpts C (hLmem C hC)
    have hC'pts : C' ∈ Tim79a.omegaOf V H := hpts C' (hLmem C' hC')
    have hinf := inf_sup_sup_eq h hS hCpts hC'pts hne
    refine Set.disjoint_left.mpr ?_
    rintro x ⟨hxA, hxV⟩ ⟨hx'A, _⟩
    exact hxV (hinf ▸ Subgroup.mem_inf.mpr ⟨hxA, hx'A⟩)
  have hUcard : ∀ T : Finset (Subgroup G), (∀ C ∈ T, C ∈ L) →
      (U T).ncard = q + T.card * d := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _
        simp only [U, q, Finset.coe_empty, Set.biUnion_empty, Set.union_empty,
          Finset.card_empty, Nat.zero_mul, add_zero]
        exact (Nat.card_coe_set_eq (V : Set G)).symm
    | insert C T' hCT' ih =>
        intro hT
        have hC : C ∈ L := hT C (Finset.mem_insert_self C T')
        have hT' : ∀ C' ∈ T', C' ∈ L := fun C' hC' =>
          hT C' (Finset.mem_insert_of_mem hC')
        have hUeq : U (insert C T') = U T' ∪ D C := by
          simp [U, Finset.coe_insert, Finset.set_biUnion_insert, Set.union_assoc,
            Set.union_comm, Set.union_left_comm]
        have hdisj' : Disjoint (U T') (D C) := by
          change Disjoint ((V : Set G) ∪ ⋃ C' ∈ (T' : Set (Subgroup G)), D C') (D C)
          rw [Set.disjoint_union_left, Set.disjoint_iUnion₂_left]
          exact ⟨(hdisjV C hC).symm, fun C' hC' =>
            hdisj C' (hT' C' hC') C hC (by
              intro h; exact hCT' (h ▸ hC'))⟩
        rw [hUeq, Set.ncard_union_eq hdisj', ih hT', hDcard C hC,
          Finset.card_insert_of_notMem hCT']
        ring
  have hUL : U L ⊆ (X : Set G) := by
    refine Set.union_subset (hX V hV) ?_
    refine Set.iUnion_subset fun C => Set.iUnion_subset fun hC => ?_
    exact Set.sdiff_subset.trans (sup_le (hX V hV) (hX C (hLmem C hC)))
  have hle : (U L).ncard ≤ (X : Set G).ncard := Set.ncard_le_ncard hUL
  rw [hUcard L (fun C hC => hC), Finset.card_erase_of_mem hV] at hle
  rw [← Nat.card_coe_set_eq] at hle
  simpa [q, d] using hle

theorem card_sup_three (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {C₂ C₃ : Subgroup G} (h₂ : C₂ ∈ Tim79a.omegaOf V H)
    (h₃ : C₃ ∈ Tim79a.omegaOf V H) (hV₂ : C₂ ≠ V) (hV₃ : C₃ ≠ V)
    (h₂₃ : C₂ ≠ C₃) : Nat.card ↥(V ⊔ C₂ ⊔ C₃) = Nat.card V ^ 3 := by
  have hcard₂ : Nat.card ↥(V ⊔ C₂) = Nat.card V ^ 2 := card_sup_eq_sq h hS h₂ hV₂
  have hinf : (V ⊔ C₂) ⊓ C₃ = ⊥ := by
    have hleV : (V ⊔ C₂) ⊓ C₃ ≤ V := by
      calc (V ⊔ C₂) ⊓ C₃ ≤ (V ⊔ C₂) ⊓ (V ⊔ C₃) := inf_le_inf_left _ le_sup_right
        _ = V := inf_sup_sup_eq h hS h₂ h₃ h₂₃
    have hle : (V ⊔ C₂) ⊓ C₃ ≤ V ⊓ C₃ := le_inf hleV inf_le_right
    rw [inf_V_eq_bot_of_mem_pts h h₃ hV₃] at hle
    exact le_bot_iff.mp hle
  have hcomm : ∀ x ∈ (V ⊔ C₂ : Subgroup G), ∀ y ∈ C₃, x * y = y * x := by
    intro x hx y hy
    exact commute_of_mem_xOf h hS
      (sup_le (le_xOf_self V H) (Tim79a.le_xOf h₂) hx) (Tim79a.le_xOf h₃ hy)
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (V ⊔ C₂) C₃ hcomm).1
  rw [hinf, Subgroup.card_bot, mul_one, hcard₂, card_eq_of_mem_pts h₃] at hprod
  simpa [pow_succ] using hprod

theorem exists_swap (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {C₂ C₃ : Subgroup G} (h₂ : C₂ ∈ Tim79a.omegaOf V H)
    (h₃ : C₃ ∈ Tim79a.omegaOf V H) (hV₂ : C₂ ≠ V) (hV₃ : C₃ ≠ V) :
    ∃ p ∈ Pc M V, conjSubgroup p C₂ = C₃ ∧ conjSubgroup p C₃ = C₂ := by
  obtain ⟨y₂, hy₂, rfl⟩ := h₂
  obtain ⟨y₃, hy₃, rfl⟩ := h₃
  obtain ⟨y₀, hy₀, -, hVy₀, -⟩ := h.exists_mem_conj_eq_of_eq_sup hS.Pc_le hS.hH
  have hVhW : conjSubgroup h₀ V ≤ Tim79a.xOf V H := hVy₀ ▸ conjSubgroup_le_xOf_of_mem hy₀
  obtain ⟨p₂, hp₂, hC₂⟩ := exists_Pc_conj_eq h hS hy₂ hV₂
  obtain ⟨p₃, hp₃, hC₃⟩ := exists_Pc_conj_eq h hS hy₃ hV₃
  have huP : p₂⁻¹ * p₃ ∈ Pc M V :=
    (Pc M V).mul_mem ((Pc M V).inv_mem hp₂) hp₃
  have hu2V : (p₂⁻¹ * p₃) * (p₂⁻¹ * p₃) ∈ V :=
    h.toHyp.mul_self_mem_of_mem_Pc huP
  have hcomm : ∀ v ∈ V, ∀ w ∈ conjSubgroup h₀ V, v * w = w * v := fun v hv w hw =>
    commute_of_mem_xOf h hS (le_xOf_self V H hv) (hVhW hw)
  have hfix : conjSubgroup ((p₂⁻¹ * p₃) * (p₂⁻¹ * p₃)) (conjSubgroup h₀ V) =
      conjSubgroup h₀ V := by
    have hcent : (p₂⁻¹ * p₃) * (p₂⁻¹ * p₃) ∈
        Subgroup.centralizer (conjSubgroup h₀ V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (hcomm _ hu2V x hx).symm
    exact conjSubgroup_eq_self_iff.mpr (Subgroup.centralizer_le_normalizer _ hcent)
  have hmul : (p₃ * p₂⁻¹) * p₃ = p₂ * ((p₂⁻¹ * p₃) * (p₂⁻¹ * p₃)) := by group
  have hcalc : conjSubgroup ((p₃ * p₂⁻¹) * p₃) (conjSubgroup h₀ V) =
      conjSubgroup p₂ (conjSubgroup h₀ V) := by
    calc conjSubgroup ((p₃ * p₂⁻¹) * p₃) (conjSubgroup h₀ V)
        = conjSubgroup (p₂ * ((p₂⁻¹ * p₃) * (p₂⁻¹ * p₃))) (conjSubgroup h₀ V) := by
          rw [hmul]
      _ = conjSubgroup p₂ (conjSubgroup ((p₂⁻¹ * p₃) * (p₂⁻¹ * p₃))
            (conjSubgroup h₀ V)) :=
          (conjSubgroup_conjSubgroup p₂ _ _).symm
      _ = conjSubgroup p₂ (conjSubgroup h₀ V) := by rw [hfix]
  refine ⟨p₃ * p₂⁻¹, (Pc M V).mul_mem hp₃ ((Pc M V).inv_mem hp₂), ?_, ?_⟩
  · rw [hC₂, hC₃, conjSubgroup_conjSubgroup]
    congr 1
    group
  · rw [hC₃, hC₂, conjSubgroup_conjSubgroup]
    exact hcalc

theorem eq_V_of_conj_eq (h : RootHyp M V) (hS : Sec45Shape M V H h₀)
    {p : G} (hp : p ∈ Pc M V) {C₂ : Subgroup G} (h₂ : C₂ ∈ Tim79a.omegaOf V H)
    (hp₂ : conjSubgroup p C₂ ≠ C₂) {C : Subgroup G} (hC : C ∈ Tim79a.omegaOf V H)
    (hpC : conjSubgroup p C = C) : C = V := by
  obtain ⟨y₂, hy₂, rfl⟩ := h₂
  obtain ⟨y, hy, rfl⟩ := hC
  by_contra hCV
  obtain ⟨p_C, hp_C, hCeq⟩ := exists_Pc_conj_eq h hS hy hCV
  set hV := conjSubgroup h₀ V with hVdef
  have hfix : conjSubgroup (p_C⁻¹ * p * p_C) hV = hV := by
    have h1 : conjSubgroup (p * p_C) hV = conjSubgroup p_C hV := by
      calc conjSubgroup (p * p_C) hV = conjSubgroup p (conjSubgroup p_C hV) :=
            (conjSubgroup_conjSubgroup p p_C hV).symm
        _ = conjSubgroup p (conjSubgroup y V) := by rw [hCeq]
        _ = conjSubgroup y V := hpC
        _ = conjSubgroup p_C hV := hCeq
    have := congrArg (conjSubgroup p_C⁻¹) h1
    simpa [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, conjSubgroup_one,
      mul_assoc] using this
  have hqP : p_C⁻¹ * p * p_C ∈ Pc M V := by
    have hpCN : p_C ∈ Subgroup.normalizer (Pc M V : Set G) :=
      h.toHyp.le_normalizer_Pc (h.toHyp.Pc_le_M hp_C)
    have hconjP : conjSubgroup p_C (Pc M V) = Pc M V := conjSubgroup_eq_self_iff.mpr hpCN
    have hpconj : p ∈ conjSubgroup p_C (Pc M V) := by
      rw [hconjP]
      exact hp
    exact mem_conjSubgroup.mp hpconj
  have hqK : p_C⁻¹ * p * p_C ∈ kOf V H := (conj_Pc_conj_eq_iff h hS hqP).mp hfix
  have hpK : p ∈ kOf V H := by
    have hpCN : p_C ∈ Subgroup.normalizer (kOf V H : Set G) :=
      le_normalizer_kOf V H (hS.Pc_le hp_C)
    have hconjK : conjSubgroup p_C (kOf V H) = kOf V H := conjSubgroup_eq_self_iff.mpr hpCN
    have hmem : p ∈ conjSubgroup p_C (kOf V H) := by
      rw [mem_conjSubgroup]
      exact hqK
    rwa [hconjK] at hmem
  have hcent : p ∈ Subgroup.centralizer (conjSubgroup y₂ V : Set G) :=
    RootHyp.kOf_le_centralizer_conjSubgroup_of_mem (V := V) (H := H) hy₂ hpK
  have hpN : p ∈ Subgroup.normalizer (conjSubgroup y₂ V : Set G) :=
    Subgroup.centralizer_le_normalizer _ hcent
  exact hp₂ (conjSubgroup_eq_self_iff.mpr hpN)

end Sec45Shape

end CFSG.RankThree.GF2n.Tim81
