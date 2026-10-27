module

public import CFSG.Quasithin.Background.C2Blocks

public section

set_option maxRecDepth 100000

namespace CFSG.Quasithin.SmithC27

open Equiv Equiv.Perm
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

theorem eq_top_of_not_dvd_factorial_index [Finite G] [IsSimpleGroup G] (H : Subgroup G)
    (h : ¬ Nat.card G ∣ H.index.factorial) : H = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h0 | h0
  · exfalso
    apply h
    have := H.index_normalCore_dvd_factorial_index
    rwa [h0, Subgroup.index_bot] at this
  · exact top_le_iff.mp (h0 ▸ H.normalCore_le)

theorem mem_normalizer_closure_of {S : Set G} {g : G} (h₁ : ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (h₂ : ∀ s ∈ S, g⁻¹ * s * g ∈ S) :
    g ∈ Subgroup.normalizer ((Subgroup.closure S : Subgroup G) : Set G) := by
  have key : ∀ x : G, (∀ s ∈ S, x * s * x⁻¹ ∈ S) →
      ∀ y ∈ Subgroup.closure S, x * y * x⁻¹ ∈ Subgroup.closure S := by
    intro x hx y hy
    have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro s hs
      exact Subgroup.subset_closure (hx s hs)
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g h₁ y, fun hy => ?_⟩
  have := key g⁻¹ (by simpa using h₂) _ hy
  simpa [mul_assoc] using this

theorem eq_or_eq_of_isCoatom {A B H : Subgroup G} (hB : IsCoatom (B.subgroupOf A))
    (hBH : B ≤ H) (hHA : H ≤ A) : H = B ∨ H = A := by
  have hle : B.subgroupOf A ≤ H.subgroupOf A := Subgroup.subgroupOf_mono A hBH
  rcases hle.lt_or_eq with hlt | heq
  · right
    have htop := hB.2 _ hlt
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact le_antisymm hHA htop
  · left
    have hBA : B ≤ A := hBH.trans hHA
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hBA, inf_of_le_left hHA] at heq
    exact heq.symm

end Generic

section Perm

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] [Fintype α] in
private theorem inv_app (f : Perm α) (x : α) : f⁻¹ (f x) = x := f.symm_apply_apply x

omit [DecidableEq α] [Fintype α] in
private theorem app_inv (f : Perm α) (x : α) : f (f⁻¹ x) = x := f.apply_symm_apply x

theorem two_mul_card_inf_alternatingGroup {H : Subgroup (Perm α)} {g : Perm α} (hg : g ∈ H)
    (hs : sign g = -1) : 2 * Nat.card ↥(alternatingGroup α ⊓ H) = Nat.card H := by
  have h1 := Subgroup.relIndex_mul_card (alternatingGroup α) H
  have h2 : (alternatingGroup α).relIndex H = 2 := by
    rw [alternatingGroup_eq_sign_ker, Subgroup.relIndex_ker]
    have htop : H.map sign = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact Subgroup.one_mem _
      · exact ⟨g, hg, hs⟩
    rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  rw [h2] at h1
  exact h1

omit [DecidableEq α] [Fintype α] in
theorem eq_of_inf_stabilizer_eq {A B : Subgroup (Perm α)} {x : α}
    (hstab : A ⊓ MulAction.stabilizer (Perm α) x = B ⊓ MulAction.stabilizer (Perm α) x)
    (htr : ∀ y, ∃ g ∈ A ⊓ B, g x = y) : A = B := by
  have key : ∀ {A B : Subgroup (Perm α)},
      A ⊓ MulAction.stabilizer (Perm α) x = B ⊓ MulAction.stabilizer (Perm α) x →
      (∀ y, ∃ g ∈ A ⊓ B, g x = y) → A ≤ B := by
    intro A B hs ht a ha
    obtain ⟨g, hg, hgx⟩ := ht (a x)
    have hmem : g⁻¹ * a ∈ A ⊓ MulAction.stabilizer (Perm α) x := by
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem (Subgroup.mem_inf.mp hg).1) ha, ?_⟩
      rw [MulAction.mem_stabilizer_iff, Perm.smul_def, Perm.mul_apply, ← hgx, inv_app]
    rw [hs] at hmem
    have := B.mul_mem (Subgroup.mem_inf.mp hg).2 (Subgroup.mem_inf.mp hmem).1
    simpa using this
  refine le_antisymm (key hstab htr) (key hstab.symm fun y => ?_)
  obtain ⟨g, hg, h⟩ := htr y
  exact ⟨g, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).2, (Subgroup.mem_inf.mp hg).1⟩, h⟩

omit [DecidableEq α] [Fintype α] in
theorem isPretransitive_of_forall {H : Subgroup (Perm α)} {x : α}
    (h : ∀ y, ∃ g ∈ H, g x = y) : MulAction.IsPretransitive H α := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨g₁, hg₁, rfl⟩ := h a
  obtain ⟨g₂, hg₂, rfl⟩ := h b
  refine ⟨⟨g₂ * g₁⁻¹, H.mul_mem hg₂ (H.inv_mem hg₁)⟩, ?_⟩
  rw [Subgroup.mk_smul, Perm.smul_def, Perm.mul_apply, inv_app]

theorem alternatingGroup_le_of_prime {H : Subgroup (Perm α)} {x : α}
    (hp : (Fintype.card α).Prime) (htr : ∀ y, ∃ g ∈ H, g x = y) {c : Perm α}
    (hc : c.IsThreeCycle) (hcH : c ∈ H) : alternatingGroup α ≤ H := by
  have := isPretransitive_of_forall htr
  have hprim : MulAction.IsPreprimitive H α :=
    MulAction.IsPreprimitive.of_prime_card (by rwa [Nat.card_eq_fintype_card])
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim hc hcH

theorem stabilizer_alternatingGroup_eq {β : Type*} [MulAction (Perm α) β] (s : β) :
    MulAction.stabilizer (alternatingGroup α) s =
      (MulAction.stabilizer (Perm α) s).subgroupOf (alternatingGroup α) := by
  ext g
  rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rfl

end Perm

section Involution

variable {α : Type*} [DecidableEq α] [Fintype α]

@[expose] def swapsOf (z : Perm α) : Set (Perm α) := {s | ∃ x, z x ≠ x ∧ s = swap x (z x)}

@[expose] def pairsOf (z : Perm α) : Finset (Finset α) := Finset.univ.image fun x => {x, z x}

private def pairFix (z : Perm α) (hz : ∀ x, z (z x) = x) : Subgroup (Perm α) where
  carrier := {g | ∀ x, g x = x ∨ g x = z x}
  one_mem' := fun _ => Or.inl rfl
  mul_mem' := by
    intro a b ha hb x
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Perm.mul_apply]
    rcases hb x with h | h <;> rw [h]
    · exact ha x
    · rcases ha (z x) with h' | h'
      · exact Or.inr h'
      · exact Or.inl (h'.trans (hz x))
  inv_mem' := by
    intro a ha x
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hy : a (a⁻¹ x) = x := a.apply_symm_apply x
    rcases ha (a⁻¹ x) with h | h <;> rw [hy] at h
    · exact Or.inl h.symm
    · right
      conv_rhs => rw [h, hz]

omit [Fintype α] in
private theorem swapsOf_subset_pairFix {z : Perm α} (hz : ∀ x, z (z x) = x) :
    swapsOf z ⊆ (pairFix z hz : Set (Perm α)) := by
  rintro s ⟨x, -, rfl⟩ y
  by_cases hy : y = x
  · subst hy
    right
    rw [swap_apply_left]
  · by_cases hy' : y = z x
    · subst hy'
      right
      rw [swap_apply_right, hz]
    · left
      exact swap_apply_of_ne_of_ne hy hy'

omit [Fintype α] in
theorem normalizer_closure_swapsOf {z : Perm α} (hz : ∀ x, z (z x) = x) :
    Subgroup.normalizer ((Subgroup.closure (swapsOf z) : Subgroup (Perm α)) : Set (Perm α)) =
      Subgroup.centralizer {z} := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have key : ∀ h ∈ Subgroup.normalizer
        ((Subgroup.closure (swapsOf z) : Subgroup (Perm α)) : Set (Perm α)),
        ∀ x, z x ≠ x → h (z x) = z (h x) := by
      intro h hh x hx
      have hs : swap x (z x) ∈ Subgroup.closure (swapsOf z) :=
        Subgroup.subset_closure ⟨x, hx, rfl⟩
      have hc := (Subgroup.mem_normalizer_iff.mp hh _).mp hs
      rw [← swap_apply_apply] at hc
      have hP := (Subgroup.closure_le (pairFix z hz)).mpr (swapsOf_subset_pairFix hz) hc
      have hne : h x ≠ h (z x) := fun e => hx (h.injective e).symm
      rcases hP (h x) with e | e <;> rw [swap_apply_left] at e
      · exact absurd e.symm hne
      · exact e
    have hall : ∀ y, g (z y) = z (g y) := by
      intro y
      by_cases hy : z y = y
      · rw [hy]
        by_contra hne
        have := key g⁻¹ (Subgroup.inv_mem _ hg) (g y) (Ne.symm hne)
        rw [inv_app, hy] at this
        apply hne
        have h2 := congrArg g this
        rw [app_inv] at h2
        exact h2.symm
      · exact key g hg y hy
    ext y
    simp only [Perm.mul_apply]
    exact hall y
  · intro hg
    have hc : ∀ h : Perm α, h * z = z * h → ∀ s ∈ swapsOf z, h * s * h⁻¹ ∈ swapsOf z := by
      rintro h hh s ⟨x, hx, rfl⟩
      have hzx : h (z x) = z (h x) := by
        have := congrArg (· x) hh
        simpa only [Perm.mul_apply] using this
      refine ⟨h x, ?_, ?_⟩
      · rw [← hzx]
        exact fun e => hx (h.injective e)
      · rw [← swap_apply_apply, hzx]
    apply mem_normalizer_closure_of (hc g hg)
    have hg' : g⁻¹ * z = z * g⁻¹ := by
      have := (Commute.inv_left (show Commute g z from hg))
      exact this.eq
    intro s hs
    simpa using hc g⁻¹ hg' s hs

theorem stabilizer_pairsOf {z : Perm α} (hz : ∀ x, z (z x) = x) :
    MulAction.stabilizer (Perm α) (pairsOf z) = Subgroup.centralizer {z} := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have key : ∀ x, g (z x) = z (g x) := by
      intro x
      have hmem : g • ({x, z x} : Finset α) ∈ pairsOf z := by
        rw [← hg]
        exact Finset.smul_mem_smul_finset (Finset.mem_image_of_mem _ (Finset.mem_univ x))
      rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, Perm.smul_def,
        Perm.smul_def] at hmem
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp hmem
      have h1 : g x ∈ ({y, z y} : Finset α) := by rw [hy]; simp
      have h2 : g (z x) ∈ ({y, z y} : Finset α) := by rw [hy]; simp
      have h3 : y ∈ ({g x, g (z x)} : Finset α) := by rw [← hy]; simp
      have h4 : z y ∈ ({g x, g (z x)} : Finset α) := by rw [← hy]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3 h4
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · have hx : z x = x := g.injective (h2.trans h1.symm)
        rw [hx, h1]
        rcases h4 with h4 | h4
        · rw [h4, h1]
        · rw [h4, h2]
      · rw [h1, h2]
      · rw [h1, h2, hz]
      · have hx : z x = x := g.injective (h2.trans h1.symm)
        have hyy : y = z y := by
          rcases h3 with h3 | h3
          · exact h3.trans h1
          · exact h3.trans h2
        rw [h2, h1, hz]
        exact hyy.symm
    ext y
    simp only [Perm.mul_apply]
    exact key y
  · intro hg
    have key : ∀ x, g (z x) = z (g x) := by
      intro x
      have := congrArg (· x) hg
      simpa only [Perm.mul_apply] using this
    have hsub : g • pairsOf z ⊆ pairsOf z := by
      intro B hB
      obtain ⟨B', hB', rfl⟩ := Finset.mem_smul_finset.mp hB
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hB'
      rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, Perm.smul_def,
        Perm.smul_def, key]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

end Involution

section KOne

variable {α : Type*} [DecidableEq α] [Fintype α]

@[expose] def kJ (T : Set (Perm α)) : Subgroup (Perm α) :=
  alternatingGroup α ⊓
    Subgroup.normalizer ((Subgroup.closure T : Subgroup (Perm α)) : Set (Perm α))

omit [Fintype α] in
theorem swapsOf_swap {a b : α} (hab : a ≠ b) : swapsOf (swap a b) = {swap a b} := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    by_cases hxa : x = a
    · subst hxa
      rw [swap_apply_left]
      rfl
    · by_cases hxb : x = b
      · subst hxb
        rw [swap_apply_right, swap_comm]
        rfl
      · exact absurd (swap_apply_of_ne_of_ne hxa hxb) hx
  · rintro rfl
    exact ⟨a, by rw [swap_apply_left]; exact hab.symm, by rw [swap_apply_left]⟩

theorem swap_eq_swap_iff_pair {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b = swap c d ↔ ({a, b} : Set α) = {c, d} := by
  constructor
  · intro h
    have h' := congrArg Perm.support h
    rw [support_swap hab, support_swap hcd] at h'
    rw [← Finset.coe_pair, ← Finset.coe_pair, h']
  · intro h
    have ha : a ∈ ({c, d} : Set α) := h ▸ Set.mem_insert a {b}
    have hb : b ∈ ({c, d} : Set α) := h ▸ Set.mem_insert_of_mem a (Set.mem_singleton b)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact swap_comm _ _
    · exact absurd rfl hab

theorem centralizer_swap {a b : α} (hab : a ≠ b) :
    Subgroup.centralizer {swap a b} = MulAction.stabilizer (Perm α) ({a, b} : Set α) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, MulAction.mem_stabilizer_iff, Set.smul_set_insert,
    Set.smul_set_singleton, Perm.smul_def, Perm.smul_def]
  have hconj : g * swap a b = swap a b * g ↔ swap (g a) (g b) = swap a b := by
    rw [swap_apply_apply]
    constructor
    · intro h
      rw [h, mul_inv_cancel_right]
    · intro h
      calc g * swap a b = g * swap a b * g⁻¹ * g := by rw [inv_mul_cancel_right]
        _ = swap a b * g := by rw [h]
  rw [hconj, swap_eq_swap_iff_pair (g.injective.ne hab) hab]

theorem kJ_swap {a b : α} (hab : a ≠ b) :
    kJ {swap a b} = alternatingGroup α ⊓ MulAction.stabilizer (Perm α) ({a, b} : Set α) := by
  rw [kJ, ← swapsOf_swap hab, normalizer_closure_swapsOf (swap_apply_self a b),
    centralizer_swap hab]

theorem kJ_swap_eq_centralizer {a b : α} (hab : a ≠ b) :
    kJ {swap a b} = alternatingGroup α ⊓ Subgroup.centralizer {swap a b} := by
  rw [kJ_swap hab, centralizer_swap hab]

theorem isCoatom_kJ_swap (hα : 5 ≤ Fintype.card α) {a b : α} (hab : a ≠ b) :
    IsCoatom ((kJ {swap a b}).subgroupOf (alternatingGroup α)) := by
  rw [kJ_swap hab, Subgroup.inf_subgroupOf_left, ← stabilizer_alternatingGroup_eq]
  have hcard : ({a, b} : Set α).ncard = 2 := Set.ncard_pair hab
  refine alternatingGroup.isCoatom_stabilizer (Set.insert_nonempty a {b}) ?_ ?_
  · rw [Set.nonempty_compl]
    intro h
    have h' := congrArg Set.ncard h
    rw [hcard, Set.ncard_univ, Nat.card_eq_fintype_card] at h'
    omega
  · rw [hcard, Nat.card_eq_fintype_card]
    omega

theorem kJ_swap_overgroups (hα : 5 ≤ Fintype.card α) {t : Perm α} (ht : t.IsSwap)
    {H : Subgroup (Perm α)} (h1 : kJ {t} ≤ H) (h2 : H ≤ alternatingGroup α) :
    H = kJ {t} ∨ H = alternatingGroup α := by
  obtain ⟨a, b, hab, rfl⟩ := ht
  exact eq_or_eq_of_isCoatom (isCoatom_kJ_swap hα hab) h1 h2

end KOne

section Counting

variable {G : Type*} [Group G]

theorem eq_or_eq_of_card_eq_prime_mul [Finite G] {A B H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card B = p * Nat.card A) (hAH : A ≤ H) (hHB : H ≤ B) : H = A ∨ H = B := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hAH
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le hHB
  have hA : 0 < Nat.card A := Nat.card_pos
  have hcd : c * d = p := by
    have h : Nat.card A * (c * d) = Nat.card A * p := by
      rw [← mul_assoc, ← hc, ← hd, hcard, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hA h
  rcases hp.eq_one_or_self_of_dvd c ⟨d, hcd.symm⟩ with h | h
  · left
    exact (Subgroup.eq_of_le_of_card_ge hAH (by rw [hc, h, mul_one])).symm
  · right
    have hd1 : d = 1 := by
      rw [h] at hcd
      have hp0 : 0 < p := hp.pos
      exact (Nat.mul_eq_left hp0.ne').mp hcd
    exact Subgroup.eq_of_le_of_card_ge hHB (by rw [hd, hd1, mul_one])

theorem relIndex_mul_card_of_le {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card H = Nat.card K := by
  have := Subgroup.relIndex_mul_card H K
  rwa [inf_of_le_left h] at this

end Counting

section PermCount

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
theorem card_dvd_of_forall {H : Subgroup (Perm α)} {x : α} (htr : ∀ y, ∃ g ∈ H, g x = y) :
    Fintype.card α ∣ Nat.card H := by
  have h := MulAction.index_stabilizer H x
  have horb : MulAction.orbit H x = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    obtain ⟨g, hg, rfl⟩ := htr y
    exact ⟨⟨g, hg⟩, rfl⟩
  rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card] at h
  rw [← h]
  exact Subgroup.index_dvd_card _

omit [Fintype α] in
theorem mem_stabilizer_coe_finset_iff {s : Finset α} {g : Perm α} :
    g ∈ MulAction.stabilizer (Perm α) (s : Set α) ↔ ∀ x, g x ∈ s ↔ x ∈ s := by
  rw [MulAction.mem_stabilizer_iff, ← Finset.coe_smul_finset, Finset.coe_inj]
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_smul_finset.mp hx
      rw [Perm.smul_def] at hyx
      rwa [g.injective hyx] at hy
    · intro hx
      rw [← h]
      exact Finset.smul_mem_smul_finset hx
  · intro h
    ext y
    rw [Finset.mem_smul_finset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h x).mpr hx
    · intro hy
      exact ⟨g⁻¹ y, (h _).mp (by rw [app_inv]; exact hy), by rw [Perm.smul_def, app_inv]⟩

omit [Fintype α] in
theorem exists_mem_apply_not_mem {s : Finset α} {g : Perm α}
    (h : g ∉ MulAction.stabilizer (Perm α) (s : Set α)) : ∃ x ∈ s, g x ∉ s := by
  rw [mem_stabilizer_coe_finset_iff] at h
  by_contra hcon
  push Not at hcon
  apply h
  have himg : s.image g = s :=
    Finset.eq_of_subset_of_card_le
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact hcon x hx)
      (by rw [Finset.card_image_of_injective _ g.injective])
  intro x
  constructor
  · intro hgx
    rw [← himg] at hgx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hgx
    rwa [← g.injective hyx]
  · exact hcon x

theorem card_stabilizer_coe_finset (s : Finset α) :
    Nat.card (MulAction.stabilizer (Perm α) (s : Set α)) =
      ∏ i : Bool, (Fintype.card {a // decide (a ∈ s) = i}).factorial := by
  have e : MulAction.stabilizer (Perm α) (s : Set α) ≃
      {g : Perm α // (fun a => decide (a ∈ s)) ∘ g = fun a => decide (a ∈ s)} :=
    Equiv.subtypeEquivRight fun g => by
      rw [mem_stabilizer_coe_finset_iff, funext_iff]
      simp only [Function.comp_apply, decide_eq_decide]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]

theorem mem_alt_inf_centralizer_iff {z g : Perm α} :
    g ∈ alternatingGroup α ⊓ Subgroup.centralizer {z} ↔ sign g = 1 ∧ g * z = z * g := by
  rw [Subgroup.mem_inf, Perm.mem_alternatingGroup, Subgroup.mem_centralizer_singleton_iff]

theorem mem_alt_inf_stabilizer_iff {s : Finset α} {g : Perm α} :
    g ∈ alternatingGroup α ⊓ MulAction.stabilizer (Perm α) (s : Set α) ↔
      sign g = 1 ∧ ∀ x, g x ∈ s ↔ x ∈ s := by
  rw [Subgroup.mem_inf, Perm.mem_alternatingGroup, mem_stabilizer_coe_finset_iff]

end PermCount

section Std

variable (n : ℕ) [NeZero n]

@[expose] def stdT2 : Set (Perm (Fin n)) := {swap 0 1, swap 2 3}

@[expose] def stdT3 : Set (Perm (Fin n)) := {swap 0 1, swap 2 3, swap 4 5}

@[expose] def z2 : Perm (Fin n) := swap 0 1 * swap 2 3

@[expose] def z3 : Perm (Fin n) := swap 0 1 * swap 2 3 * swap 4 5

@[expose] def quad : Finset (Fin n) := {0, 1, 2, 3}

@[expose] def quadStab : Subgroup (Perm (Fin n)) :=
  alternatingGroup (Fin n) ⊓
    MulAction.stabilizer (Perm (Fin n)) ((quad n : Finset (Fin n)) : Set (Fin n))

end Std

section SmallAlt

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem eq_alternatingGroup_five_of_dvd {H : Subgroup (Perm (Fin 5))}
    (h2 : H ≤ alternatingGroup (Fin 5)) (h20 : 20 ∣ Nat.card H) :
    H = alternatingGroup (Fin 5) := by
  have hr := relIndex_mul_card_of_le h2
  rw [card_alt_five] at hr
  obtain ⟨c, hc⟩ := h20
  rw [hc] at hr
  have hrc : H.relIndex (alternatingGroup (Fin 5)) * c = 3 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 20 by norm_num)
    rw [show 20 * 3 = 60 by norm_num, ← hr]
    ring
  have h3 : H.relIndex (alternatingGroup (Fin 5)) ∣ 3 := ⟨c, hrc.symm⟩
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have htop := eq_top_of_not_dvd_factorial_index (H.subgroupOf (alternatingGroup (Fin 5))) (by
    rw [card_alt_five]
    change ¬ 60 ∣ (H.relIndex (alternatingGroup (Fin 5))).factorial
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ h3 with h | h
    · rw [h]
      decide
    · rw [h]
      decide)
  rw [Subgroup.subgroupOf_eq_top] at htop
  exact le_antisymm h2 htop

end SmallAlt

section KTwo

theorem z2_invol_five : ∀ x : Fin 5, z2 5 (z2 5 x) = x := by decide

theorem z2_invol_seven : ∀ x : Fin 7, z2 7 (z2 7 x) = x := by decide

theorem stdT2_eq_swapsOf_five : stdT2 5 = swapsOf (z2 5) := by
  ext s
  simp only [stdT2, swapsOf, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
  · rintro ⟨x, hx, rfl⟩
    revert x
    decide

theorem stdT2_eq_swapsOf_seven : stdT2 7 = swapsOf (z2 7) := by
  ext s
  simp only [stdT2, swapsOf, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
  · rintro ⟨x, hx, rfl⟩
    revert x
    decide

theorem kJ_stdT2_five : kJ (stdT2 5) = alternatingGroup (Fin 5) ⊓ Subgroup.centralizer {z2 5} := by
  rw [kJ, stdT2_eq_swapsOf_five, normalizer_closure_swapsOf z2_invol_five]

theorem kJ_stdT2_seven : kJ (stdT2 7) = alternatingGroup (Fin 7) ⊓ Subgroup.centralizer {z2 7} := by
  rw [kJ, stdT2_eq_swapsOf_seven, normalizer_closure_swapsOf z2_invol_seven]

theorem cycleType_z2_five : (z2 5).cycleType = {2, 2} :=
  cycleType_swap_mul_swap_of_nodup (by decide)

theorem cycleType_z2_seven : (z2 7).cycleType = {2, 2} :=
  cycleType_swap_mul_swap_of_nodup (by decide)

theorem card_centralizer_z2_five : Nat.card (Subgroup.centralizer {z2 5}) = 8 := by
  rw [Perm.nat_card_centralizer, cycleType_z2_five]
  decide +kernel

theorem card_centralizer_z2_seven : Nat.card (Subgroup.centralizer {z2 7}) = 48 := by
  rw [Perm.nat_card_centralizer, cycleType_z2_seven]
  decide +kernel

theorem card_kJ_stdT2_five : Nat.card (kJ (stdT2 5)) = 4 := by
  have h := two_mul_card_inf_alternatingGroup (H := Subgroup.centralizer {z2 5})
    (g := swap 0 1) (Subgroup.mem_centralizer_singleton_iff.mpr (by decide))
    (Perm.sign_swap (by decide))
  rw [card_centralizer_z2_five] at h
  rw [kJ_stdT2_five]
  omega

theorem card_kJ_stdT2_seven : Nat.card (kJ (stdT2 7)) = 24 := by
  have h := two_mul_card_inf_alternatingGroup (H := Subgroup.centralizer {z2 7})
    (g := swap 0 1) (Subgroup.mem_centralizer_singleton_iff.mpr (by decide))
    (Perm.sign_swap (by decide))
  rw [card_centralizer_z2_seven] at h
  rw [kJ_stdT2_seven]
  omega

theorem kJ_stdT2_le_quadStab_five : kJ (stdT2 5) ≤ quadStab 5 := by
  rw [kJ_stdT2_five]
  intro g hg
  rw [mem_alt_inf_centralizer_iff] at hg
  rw [quadStab, mem_alt_inf_stabilizer_iff]
  refine ⟨hg.1, fun x => ?_⟩
  have key : g (z2 5 x) = z2 5 (g x) := by
    have := congrArg (· x) hg.2
    simpa only [Perm.mul_apply] using this
  have hq : ∀ y : Fin 5, y ∈ quad 5 ↔ z2 5 y ≠ y := by decide
  rw [hq, hq, ← key, g.injective.ne_iff]

theorem kJ_stdT2_le_quadStab_seven : kJ (stdT2 7) ≤ quadStab 7 := by
  rw [kJ_stdT2_seven]
  intro g hg
  rw [mem_alt_inf_centralizer_iff] at hg
  rw [quadStab, mem_alt_inf_stabilizer_iff]
  refine ⟨hg.1, fun x => ?_⟩
  have key : g (z2 7 x) = z2 7 (g x) := by
    have := congrArg (· x) hg.2
    simpa only [Perm.mul_apply] using this
  have hq : ∀ y : Fin 7, y ∈ quad 7 ↔ z2 7 y ≠ y := by decide
  rw [hq, hq, ← key, g.injective.ne_iff]

theorem card_quadStab_five : Nat.card (quadStab 5) = 12 := by
  have hs : Nat.card (MulAction.stabilizer (Perm (Fin 5))
      ((quad 5 : Finset (Fin 5)) : Set (Fin 5))) = 24 := by
    rw [card_stabilizer_coe_finset]
    decide
  have h := two_mul_card_inf_alternatingGroup (g := swap 0 1)
    ((mem_stabilizer_coe_finset_iff (s := quad 5) (g := swap 0 1)).mpr (by decide))
    (Perm.sign_swap (by decide))
  rw [hs] at h
  rw [quadStab]
  omega

theorem card_quadStab_seven : Nat.card (quadStab 7) = 72 := by
  have hs : Nat.card (MulAction.stabilizer (Perm (Fin 7))
      ((quad 7 : Finset (Fin 7)) : Set (Fin 7))) = 144 := by
    rw [card_stabilizer_coe_finset]
    decide
  have h := two_mul_card_inf_alternatingGroup (g := swap 0 1)
    ((mem_stabilizer_coe_finset_iff (s := quad 7) (g := swap 0 1)).mpr (by decide))
    (Perm.sign_swap (by decide))
  rw [hs] at h
  rw [quadStab]
  omega

theorem isCoatom_quadStab_five :
    IsCoatom ((quadStab 5).subgroupOf (alternatingGroup (Fin 5))) := by
  rw [quadStab, Subgroup.inf_subgroupOf_left, ← stabilizer_alternatingGroup_eq]
  refine alternatingGroup.isCoatom_stabilizer ⟨0, by decide⟩ ⟨4, by decide⟩ ?_
  rw [Set.ncard_coe_finset, Nat.card_fin]
  decide

theorem isCoatom_quadStab_seven :
    IsCoatom ((quadStab 7).subgroupOf (alternatingGroup (Fin 7))) := by
  rw [quadStab, Subgroup.inf_subgroupOf_left, ← stabilizer_alternatingGroup_eq]
  refine alternatingGroup.isCoatom_stabilizer ⟨0, by decide⟩ ⟨4, by decide⟩ ?_
  rw [Set.ncard_coe_finset, Nat.card_fin]
  decide

theorem isCoatom_quadStab {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) :
    IsCoatom ((quadStab n).subgroupOf (alternatingGroup (Fin n))) := by
  rcases hn with rfl | rfl
  · exact isCoatom_quadStab_five
  · exact isCoatom_quadStab_seven

theorem quadStab_overgroups {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) {H : Subgroup (Perm (Fin n))}
    (h1 : quadStab n ≤ H) (h2 : H ≤ alternatingGroup (Fin n)) :
    H = quadStab n ∨ H = alternatingGroup (Fin n) :=
  eq_or_eq_of_isCoatom (isCoatom_quadStab hn) h1 h2

theorem mem_kJ_stdT2_five {g : Perm (Fin 5)} (h : sign g = 1 ∧ g * z2 5 = z2 5 * g) :
    g ∈ kJ (stdT2 5) := by
  rw [kJ_stdT2_five, mem_alt_inf_centralizer_iff]
  exact h

theorem mem_kJ_stdT2_seven {g : Perm (Fin 7)} (h : sign g = 1 ∧ g * z2 7 = z2 7 * g) :
    g ∈ kJ (stdT2 7) := by
  rw [kJ_stdT2_seven, mem_alt_inf_centralizer_iff]
  exact h

private theorem quad_reach_five {H : Subgroup (Perm (Fin 5))} (h1 : kJ (stdT2 5) ≤ H) :
    ∀ x ∈ quad 5, ∃ e ∈ H, e 0 = x := by
  have he1 : swap 0 1 * swap 2 3 ∈ H := h1 (mem_kJ_stdT2_five (by decide +kernel))
  have he2 : swap 0 2 * swap 1 3 ∈ H := h1 (mem_kJ_stdT2_five (by decide +kernel))
  have he3 : swap 0 3 * swap 1 2 ∈ H := h1 (mem_kJ_stdT2_five (by decide +kernel))
  have hq : ∀ y : Fin 5, y ∈ quad 5 → y = 0 ∨ y = (swap 0 1 * swap 2 3 : Perm (Fin 5)) 0 ∨
      y = (swap 0 2 * swap 1 3 : Perm (Fin 5)) 0 ∨ y = (swap 0 3 * swap 1 2 : Perm (Fin 5)) 0 := by
    decide +kernel
  intro x hx
  rcases hq x hx with rfl | rfl | rfl | rfl
  · exact ⟨1, H.one_mem, rfl⟩
  · exact ⟨_, he1, rfl⟩
  · exact ⟨_, he2, rfl⟩
  · exact ⟨_, he3, rfl⟩

private theorem quad_reach_seven {H : Subgroup (Perm (Fin 7))} (h1 : kJ (stdT2 7) ≤ H) :
    ∀ x ∈ quad 7, ∃ e ∈ H, e 0 = x := by
  have he1 : swap 0 1 * swap 2 3 ∈ H := h1 (mem_kJ_stdT2_seven (by decide +kernel))
  have he2 : swap 0 2 * swap 1 3 ∈ H := h1 (mem_kJ_stdT2_seven (by decide +kernel))
  have he3 : swap 0 3 * swap 1 2 ∈ H := h1 (mem_kJ_stdT2_seven (by decide +kernel))
  have hq : ∀ y : Fin 7, y ∈ quad 7 → y = 0 ∨ y = (swap 0 1 * swap 2 3 : Perm (Fin 7)) 0 ∨
      y = (swap 0 2 * swap 1 3 : Perm (Fin 7)) 0 ∨ y = (swap 0 3 * swap 1 2 : Perm (Fin 7)) 0 := by
    decide +kernel
  intro x hx
  rcases hq x hx with rfl | rfl | rfl | rfl
  · exact ⟨1, H.one_mem, rfl⟩
  · exact ⟨_, he1, rfl⟩
  · exact ⟨_, he2, rfl⟩
  · exact ⟨_, he3, rfl⟩

private theorem rest_reach_seven {H : Subgroup (Perm (Fin 7))} (h1 : kJ (stdT2 7) ≤ H) :
    ∀ w y : Fin 7, w ∉ quad 7 → y ∉ quad 7 → ∃ c ∈ H, c w = y := by
  have hc : swap 4 5 * swap 4 6 ∈ H := h1 (mem_kJ_stdT2_seven (by decide +kernel))
  have hr : ∀ w y : Fin 7, w ∉ quad 7 → y ∉ quad 7 → y = w ∨
      y = (swap 4 5 * swap 4 6 : Perm (Fin 7)) w ∨
      y = (swap 4 5 * swap 4 6 * (swap 4 5 * swap 4 6) : Perm (Fin 7)) w := by
    decide +kernel
  intro w y hw hy
  rcases hr w y hw hy with rfl | rfl | rfl
  · exact ⟨1, H.one_mem, rfl⟩
  · exact ⟨_, hc, rfl⟩
  · exact ⟨_, H.mul_mem hc hc, rfl⟩

theorem kJ_stdT2_overgroups_five {H : Subgroup (Perm (Fin 5))} (h1 : kJ (stdT2 5) ≤ H)
    (h2 : H ≤ alternatingGroup (Fin 5)) :
    H = kJ (stdT2 5) ∨ H = quadStab 5 ∨ H = alternatingGroup (Fin 5) := by
  by_cases hq : H ≤ MulAction.stabilizer (Perm (Fin 5)) ((quad 5 : Finset (Fin 5)) : Set (Fin 5))
  · rcases eq_or_eq_of_card_eq_prime_mul Nat.prime_three
        (by rw [card_quadStab_five, card_kJ_stdT2_five]) h1
        (show H ≤ quadStab 5 from le_inf h2 hq) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · right
    right
    obtain ⟨h, hH, hns⟩ := IsConcreteLE.not_le_iff_exists.mp hq
    obtain ⟨x, hx, hhx⟩ := exists_mem_apply_not_mem hns
    have hrest : ∀ a b : Fin 5, a ∉ quad 5 → b ∉ quad 5 → a = b := by decide
    have htr : ∀ y, ∃ g ∈ H, g 0 = y := by
      intro y
      by_cases hy : y ∈ quad 5
      · exact quad_reach_five h1 y hy
      · obtain ⟨e, he, hex⟩ := quad_reach_five h1 x hx
        refine ⟨h * e, H.mul_mem hH he, ?_⟩
        rw [Perm.mul_apply, hex]
        exact hrest _ _ hhx hy
    have h5 := card_dvd_of_forall htr
    rw [Fintype.card_fin] at h5
    have h4 : 4 ∣ Nat.card H := card_kJ_stdT2_five ▸ Subgroup.card_dvd_of_le h1
    exact eq_alternatingGroup_five_of_dvd h2 (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h4 h5)

theorem kJ_stdT2_overgroups_seven {H : Subgroup (Perm (Fin 7))} (h1 : kJ (stdT2 7) ≤ H)
    (h2 : H ≤ alternatingGroup (Fin 7)) :
    H = kJ (stdT2 7) ∨ H = quadStab 7 ∨ H = alternatingGroup (Fin 7) := by
  by_cases hq : H ≤ MulAction.stabilizer (Perm (Fin 7)) ((quad 7 : Finset (Fin 7)) : Set (Fin 7))
  · rcases eq_or_eq_of_card_eq_prime_mul Nat.prime_three
        (by rw [card_quadStab_seven, card_kJ_stdT2_seven]) h1
        (show H ≤ quadStab 7 from le_inf h2 hq) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · right
    right
    obtain ⟨h, hH, hns⟩ := IsConcreteLE.not_le_iff_exists.mp hq
    obtain ⟨x, hx, hhx⟩ := exists_mem_apply_not_mem hns
    have htr : ∀ y, ∃ g ∈ H, g 0 = y := by
      intro y
      by_cases hy : y ∈ quad 7
      · exact quad_reach_seven h1 y hy
      · obtain ⟨e, he, hex⟩ := quad_reach_seven h1 x hx
        obtain ⟨c, hc, hcy⟩ := rest_reach_seven h1 _ _ hhx hy
        refine ⟨c * (h * e), H.mul_mem hc (H.mul_mem hH he), ?_⟩
        rw [Perm.mul_apply, Perm.mul_apply, hex, hcy]
    have hc : swap (4 : Fin 7) 5 * swap 4 6 ∈ H := h1 (mem_kJ_stdT2_seven (by decide +kernel))
    exact le_antisymm h2 (alternatingGroup_le_of_prime (by rw [Fintype.card_fin]; norm_num) htr
      (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)) hc)

theorem kJ_stdT2_overgroups {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) {H : Subgroup (Perm (Fin n))}
    (h1 : kJ (stdT2 n) ≤ H) (h2 : H ≤ alternatingGroup (Fin n)) :
    H = kJ (stdT2 n) ∨ H = quadStab n ∨ H = alternatingGroup (Fin n) := by
  rcases hn with rfl | rfl
  · exact kJ_stdT2_overgroups_five h1 h2
  · exact kJ_stdT2_overgroups_seven h1 h2

@[expose] def part43 : Finset (Finset (Fin 7)) := {{0, 1, 2, 3}, {4, 5, 6}}

theorem isPartitionOfType_part43 : IsPartitionOfType part43 {4, 3} := by
  unfold IsPartitionOfType
  decide +kernel

theorem quadStab_seven_eq :
    quadStab 7 = MulAction.stabilizer (Perm (Fin 7)) part43 ⊓ alternatingGroup (Fin 7) := by
  rw [quadStab, inf_comm]
  congr 1
  ext g
  rw [mem_stabilizer_coe_finset_iff, MulAction.mem_stabilizer_iff]
  have hc : ∀ y : Fin 7, y ∉ quad 7 ↔ y ∈ ({4, 5, 6} : Finset (Fin 7)) := by decide
  constructor
  · intro h
    have h4 : g • quad 7 = quad 7 := by
      ext y
      rw [Finset.mem_smul_finset]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (h x).mpr hx
      · intro hy
        exact ⟨g⁻¹ y, (h _).mp (by rw [app_inv]; exact hy), by rw [Perm.smul_def, app_inv]⟩
    have h3 : g • ({4, 5, 6} : Finset (Fin 7)) = {4, 5, 6} := by
      ext y
      rw [Finset.mem_smul_finset, ← hc]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [← hc] at hx
        exact fun hy => hx ((h x).mp hy)
      · intro hy
        refine ⟨g⁻¹ y, ?_, by rw [Perm.smul_def, app_inv]⟩
        rw [← hc]
        exact fun hy' => hy (by rw [← app_inv g y]; exact (h _).mpr hy')
    rw [part43, Finset.smul_finset_insert, Finset.smul_finset_singleton]
    rw [show ({0, 1, 2, 3} : Finset (Fin 7)) = quad 7 from rfl, h4, h3]
  · intro h
    have hmem : g • quad 7 ∈ part43 := by
      rw [← h]
      exact Finset.smul_mem_smul_finset (by decide)
    have hq : g • quad 7 = quad 7 := by
      rw [part43, Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hm | hm
      · exact hm
      · exfalso
        have := congrArg Finset.card hm
        rw [Finset.card_smul_finset] at this
        exact absurd this (by decide)
    intro x
    constructor
    · intro hx
      rw [← hq] at hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_smul_finset.mp hx
      rw [Perm.smul_def] at hyx
      rwa [g.injective hyx] at hy
    · intro hx
      rw [← hq]
      exact Finset.smul_mem_smul_finset hx

end KTwo

section KThree

theorem z3_invol : ∀ x : Fin 7, z3 7 (z3 7 x) = x := by decide

theorem stdT3_eq_swapsOf : stdT3 7 = swapsOf (z3 7) := by
  ext s
  simp only [stdT3, swapsOf, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨4, by decide, by decide⟩
  · rintro ⟨x, hx, rfl⟩
    revert x
    decide

theorem kJ_stdT3 : kJ (stdT3 7) = alternatingGroup (Fin 7) ⊓ Subgroup.centralizer {z3 7} := by
  rw [kJ, stdT3_eq_swapsOf, normalizer_closure_swapsOf z3_invol]

theorem cycleType_z3 : (z3 7).cycleType = {2, 2, 2} := by
  rw [z3, ((disjoint_swap_swap (by decide : [(0 : Fin 7), 1, 4, 5].Nodup)).mul_left
    (disjoint_swap_swap (by decide : [(2 : Fin 7), 3, 4, 5].Nodup))).cycleType_mul,
    cycleType_swap_mul_swap_of_nodup (by decide), isSwap_iff_cycleType.mp ⟨4, 5, by decide, rfl⟩]
  rfl

theorem card_centralizer_z3 : Nat.card (Subgroup.centralizer {z3 7}) = 48 := by
  rw [Perm.nat_card_centralizer, cycleType_z3]
  decide +kernel

theorem card_kJ_stdT3 : Nat.card (kJ (stdT3 7)) = 24 := by
  have h := two_mul_card_inf_alternatingGroup (H := Subgroup.centralizer {z3 7})
    (g := swap 0 1) (Subgroup.mem_centralizer_singleton_iff.mpr (by decide))
    (Perm.sign_swap (by decide))
  rw [card_centralizer_z3] at h
  rw [kJ_stdT3]
  omega

theorem mem_kJ_stdT3 {g : Perm (Fin 7)} (h : sign g = 1 ∧ g * z3 7 = z3 7 * g) :
    g ∈ kJ (stdT3 7) := by
  rw [kJ_stdT3, mem_alt_inf_centralizer_iff]
  exact h

@[expose] def part2221 : Finset (Finset (Fin 7)) := {{0, 1}, {2, 3}, {4, 5}, {6}}

theorem isPartitionOfType_part2221 : IsPartitionOfType part2221 {2, 2, 2, 1} := by
  unfold IsPartitionOfType
  decide +kernel

theorem pairsOf_z3 : pairsOf (z3 7) = part2221 := by decide +kernel

theorem kJ_stdT3_eq_stabilizer :
    kJ (stdT3 7) = MulAction.stabilizer (Perm (Fin 7)) part2221 ⊓ alternatingGroup (Fin 7) := by
  rw [kJ_stdT3, ← pairsOf_z3, stabilizer_pairsOf z3_invol, inf_comm]

theorem kJ_stdT3_fix {g : Perm (Fin 7)} (hg : g ∈ kJ (stdT3 7)) : g 6 = 6 := by
  rw [kJ_stdT3, mem_alt_inf_centralizer_iff] at hg
  have key : g (z3 7 6) = z3 7 (g 6) := by
    have := congrArg (· 6) hg.2
    simpa only [Perm.mul_apply] using this
  rw [show z3 7 6 = 6 by decide] at key
  have hfix : ∀ y : Fin 7, z3 7 y = y → y = 6 := by decide
  exact hfix _ key.symm

@[expose] def pointStab : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7)

theorem mem_pointStab_iff {g : Perm (Fin 7)} : g ∈ pointStab ↔ sign g = 1 ∧ g 6 = 6 := by
  rw [pointStab, Subgroup.mem_inf, Perm.mem_alternatingGroup, MulAction.mem_stabilizer_iff,
    Perm.smul_def]

private def jA6 : alternatingGroup ↥(Finset.univ.erase (6 : Fin 7)) →* Perm (Fin 7) :=
  (alternatingGroup (Fin 7)).subtype.comp (alternatingGroup.ofSubtype (Finset.univ.erase 6))

private theorem jA6_injective : Function.Injective jA6 :=
  (alternatingGroup (Fin 7)).subtype_injective.comp alternatingGroup.ofSubtype_injective

private theorem range_jA6 : jA6.range = pointStab := by
  ext g
  rw [mem_pointStab_iff]
  constructor
  · rintro ⟨k, rfl⟩
    have hk := (alternatingGroup.mem_range_ofSubtype_iff _ (alternatingGroup.ofSubtype _ k)).mp
      ⟨k, rfl⟩
    refine ⟨Perm.mem_alternatingGroup.mp (alternatingGroup.ofSubtype _ k).2, ?_⟩
    by_contra hne
    have := hk (Perm.mem_support.mpr hne)
    simp at this
  · rintro ⟨hs, h6⟩
    have hmem : (⟨g, Perm.mem_alternatingGroup.mpr hs⟩ : alternatingGroup (Fin 7)) ∈
        (alternatingGroup.ofSubtype (Finset.univ.erase (6 : Fin 7))).range := by
      rw [alternatingGroup.mem_range_ofSubtype_iff]
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact (Perm.mem_support.mp hx) h6
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k, ?_⟩
    simp only [jA6, MonoidHom.coe_comp, Function.comp_apply, hk]
    rfl

private noncomputable def pointStabEquiv :
    alternatingGroup ↥(Finset.univ.erase (6 : Fin 7)) ≃* pointStab :=
  (MonoidHom.ofInjective jA6_injective).trans (MulEquiv.subgroupCongr range_jA6)

theorem isSimpleGroup_pointStab : IsSimpleGroup pointStab := by
  have : IsSimpleGroup (alternatingGroup ↥(Finset.univ.erase (6 : Fin 7))) :=
    alternatingGroup.isSimpleGroup (by simp)
  exact pointStabEquiv.symm.isSimpleGroup

theorem card_pointStab : Nat.card pointStab = 360 := by
  have : Nontrivial ↥(Finset.univ.erase (6 : Fin 7)) :=
    ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩⟩
  rw [← Nat.card_congr pointStabEquiv.toEquiv, nat_card_alternatingGroup]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

theorem isCoatom_pointStab : IsCoatom (pointStab.subgroupOf (alternatingGroup (Fin 7))) := by
  have h := alternatingGroup.isCoatom_stabilizer_singleton (α := Fin 7) (by simp)
    (Set.singleton_nonempty (6 : Fin 7)) Set.subsingleton_singleton
  rw [MulAction.stabilizer_singleton, stabilizer_alternatingGroup_eq] at h
  rwa [pointStab, Subgroup.inf_subgroupOf_left]

theorem kJ_stdT3_le_pointStab : kJ (stdT3 7) ≤ pointStab := fun _ hg =>
  mem_pointStab_iff.mpr ⟨Perm.mem_alternatingGroup.mp (Subgroup.mem_inf.mp hg).1, kJ_stdT3_fix hg⟩

theorem kJ_stdT3_maximal {H : Subgroup (Perm (Fin 7))} (h1 : kJ (stdT3 7) ≤ H)
    (h2 : H ≤ pointStab) : H = kJ (stdT3 7) ∨ H = pointStab := by
  have hr := relIndex_mul_card_of_le h2
  rw [card_pointStab] at hr
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le h1
  rw [card_kJ_stdT3] at hc
  rw [hc] at hr
  have hrc : H.relIndex pointStab * c = 15 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 24 by norm_num)
    rw [show 24 * 15 = 360 by norm_num, ← hr]
    ring
  by_cases hc1 : c = 1
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hc, hc1, card_kJ_stdT3])).symm
  · right
    have : IsSimpleGroup pointStab := isSimpleGroup_pointStab
    have key : ∀ r, r < 16 → r ∣ 15 → r ≠ 15 → ¬ 360 ∣ r.factorial := by decide
    have hr15 : H.relIndex pointStab ∣ 15 := ⟨c, hrc.symm⟩
    have hne : H.relIndex pointStab ≠ 15 := by
      intro h
      rw [h] at hrc
      omega
    have htop := eq_top_of_not_dvd_factorial_index (H.subgroupOf pointStab) (by
      rw [card_pointStab]
      exact key _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hr15)) hr15 hne)
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact le_antisymm h2 htop

@[expose] def fanoEven : Finset (Finset (Fin 7)) :=
  {{0, 1, 6}, {2, 3, 6}, {4, 5, 6}, {0, 2, 4}, {0, 3, 5}, {1, 2, 5}, {1, 3, 4}}

@[expose] def fanoOdd : Finset (Finset (Fin 7)) :=
  {{0, 1, 6}, {2, 3, 6}, {4, 5, 6}, {0, 2, 5}, {0, 3, 4}, {1, 2, 4}, {1, 3, 5}}

@[expose] def fanoStabEven : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) fanoEven

@[expose] def fanoStabOdd : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) fanoOdd

private def chkA (g : Perm (Fin 7)) : Prop :=
  g * z3 7 = z3 7 * g → sign g = 1 → (g • fanoEven = fanoEven ∧ g • fanoOdd = fanoOdd) ∧
    (g 0 = 0 → (g 2 = 2 ∨ g 3 = 3 ∨ g 4 = 4 ∨ g 5 = 5) → ∀ y, g y = y)

private instance (g : Perm (Fin 7)) : Decidable (chkA g) :=
  inferInstanceAs (Decidable (g * z3 7 = z3 7 * g → sign g = 1 →
    (g • fanoEven = fanoEven ∧ g • fanoOdd = fanoOdd) ∧
    (g 0 = 0 → (g 2 = 2 ∨ g 3 = 3 ∨ g 4 = 4 ∨ g 5 = 5) → ∀ y, g y = y)))

private def chkB (g : Perm (Fin 7)) : Prop :=
  g 0 = 6 → g 1 = 1 → g 2 = 2 → g 6 = 0 → sign g = 1 →
    g = swap 0 6 * swap 3 4 ∨ g = swap 0 6 * swap 3 5 ∨ g = swap 0 6 * swap 4 5

private instance (g : Perm (Fin 7)) : Decidable (chkB g) :=
  inferInstanceAs (Decidable (g 0 = 6 → g 1 = 1 → g 2 = 2 → g 6 = 0 → sign g = 1 →
    g = swap 0 6 * swap 3 4 ∨ g = swap 0 6 * swap 3 5 ∨ g = swap 0 6 * swap 4 5))

private theorem s7_checks : ∀ g : Perm (Fin 7), chkA g ∧ chkB g := by
  decide +kernel

theorem kJ_stdT3_le_fanoStabEven : kJ (stdT3 7) ≤ fanoStabEven := by
  intro g hg
  have hg' := hg
  rw [kJ_stdT3, mem_alt_inf_centralizer_iff] at hg'
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1,
    ((s7_checks g).1 hg'.2 hg'.1).1.1⟩

theorem kJ_stdT3_le_fanoStabOdd : kJ (stdT3 7) ≤ fanoStabOdd := by
  intro g hg
  have hg' := hg
  rw [kJ_stdT3, mem_alt_inf_centralizer_iff] at hg'
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hg).1,
    ((s7_checks g).1 hg'.2 hg'.1).1.2⟩

private theorem six_reach : ∀ y : Fin 7, y ≠ 6 → ∃ e ∈ kJ (stdT3 7), e 0 = y ∧ e y = 0 := by
  have hq : ∀ y : Fin 7, y ≠ 6 → y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 := by decide
  intro y hy
  rcases hq y hy with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, Subgroup.one_mem _, rfl, rfl⟩
  · exact ⟨swap 0 1 * swap 2 3, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩
  · exact ⟨swap 0 2 * swap 1 3, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩
  · exact ⟨swap 0 3 * swap 1 2, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩
  · exact ⟨swap 0 4 * swap 1 5, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩
  · exact ⟨swap 0 5 * swap 1 4, mem_kJ_stdT3 (by decide +kernel), by decide, by decide⟩

private theorem isThreeCycle_016 : (swap (0 : Fin 7) 6 * swap 0 1).IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private theorem fanoStabEven_ne_pointStab : ¬ pointStab ≤ fanoStabEven := by
  intro h
  have hm : swap (0 : Fin 7) 1 * swap 0 2 ∈ pointStab := mem_pointStab_iff.mpr (by decide +kernel)
  have := (Subgroup.mem_inf.mp (h hm)).2
  rw [MulAction.mem_stabilizer_iff] at this
  exact absurd this (by decide +kernel)

private theorem fanoStabOdd_ne_pointStab : ¬ pointStab ≤ fanoStabOdd := by
  intro h
  have hm : swap (0 : Fin 7) 1 * swap 0 2 ∈ pointStab := mem_pointStab_iff.mpr (by decide +kernel)
  have := (Subgroup.mem_inf.mp (h hm)).2
  rw [MulAction.mem_stabilizer_iff] at this
  exact absurd this (by decide +kernel)

theorem fanoStabEven_inf_pointStab : fanoStabEven ⊓ pointStab = kJ (stdT3 7) := by
  rcases kJ_stdT3_maximal (le_inf kJ_stdT3_le_fanoStabEven kJ_stdT3_le_pointStab)
      (inf_le_right : fanoStabEven ⊓ pointStab ≤ pointStab) with h | h
  · exact h
  · exact absurd (h ▸ inf_le_left) fanoStabEven_ne_pointStab

theorem fanoStabOdd_inf_pointStab : fanoStabOdd ⊓ pointStab = kJ (stdT3 7) := by
  rcases kJ_stdT3_maximal (le_inf kJ_stdT3_le_fanoStabOdd kJ_stdT3_le_pointStab)
      (inf_le_right : fanoStabOdd ⊓ pointStab ≤ pointStab) with h | h
  · exact h
  · exact absurd (h ▸ inf_le_left) fanoStabOdd_ne_pointStab

private theorem inf_stab6 {H : Subgroup (Perm (Fin 7))} (h : H ≤ alternatingGroup (Fin 7)) :
    H ⊓ MulAction.stabilizer (Perm (Fin 7)) (6 : Fin 7) = H ⊓ pointStab := by
  rw [pointStab, ← inf_assoc, inf_of_le_left h]

private theorem eq_of_six_zero {H L : Subgroup (Perm (Fin 7))} (h1 : kJ (stdT3 7) ≤ H)
    (h2 : H ≤ alternatingGroup (Fin 7)) (hL1 : kJ (stdT3 7) ≤ L)
    (hL2 : L ≤ alternatingGroup (Fin 7)) (hH6 : H ⊓ pointStab = kJ (stdT3 7))
    (hL6 : L ⊓ pointStab = kJ (stdT3 7)) {σ : Perm (Fin 7)} (hσH : σ ∈ H) (hσL : σ ∈ L)
    (hσ : σ 6 = 0) : H = L := by
  apply eq_of_inf_stabilizer_eq (x := (6 : Fin 7))
  · rw [inf_stab6 h2, inf_stab6 hL2, hH6, hL6]
  · intro y
    by_cases hy : y = 6
    · exact ⟨1, Subgroup.one_mem _, by rw [hy]; rfl⟩
    · obtain ⟨e, he, he0, -⟩ := six_reach y hy
      exact ⟨e * σ, Subgroup.mem_inf.mpr ⟨H.mul_mem (h1 he) hσH, L.mul_mem (hL1 he) hσL⟩,
        by rw [Perm.mul_apply, hσ, he0]⟩

theorem kJ_stdT3_overgroups {H : Subgroup (Perm (Fin 7))} (h1 : kJ (stdT3 7) ≤ H)
    (h2 : H ≤ alternatingGroup (Fin 7)) :
    H = kJ (stdT3 7) ∨ H = pointStab ∨ H = fanoStabEven ∨ H = fanoStabOdd ∨
      H = alternatingGroup (Fin 7) := by
  by_cases hfix : ∀ g ∈ H, g 6 = 6
  · have h2' : H ≤ pointStab := fun g hg =>
      mem_pointStab_iff.mpr ⟨Perm.mem_alternatingGroup.mp (h2 hg), hfix g hg⟩
    rcases kJ_stdT3_maximal h1 h2' with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  push Not at hfix
  obtain ⟨h, hH, h6⟩ := hfix
  right
  right
  have htr : ∀ y, ∃ g ∈ H, g 6 = y := by
    intro y
    by_cases hy : y = 6
    · exact ⟨1, H.one_mem, by rw [hy]; rfl⟩
    · obtain ⟨e, he, he0, -⟩ := six_reach y hy
      obtain ⟨f, hf, -, hf0⟩ := six_reach (h 6) h6
      exact ⟨e * f * h, H.mul_mem (H.mul_mem (h1 he) (h1 hf)) hH, by
        simp only [Perm.mul_apply, hf0, he0]⟩
  rcases kJ_stdT3_maximal (le_inf h1 kJ_stdT3_le_pointStab)
      (inf_le_right : H ⊓ pointStab ≤ pointStab) with hH6 | hH6
  swap
  · right
    right
    have hle : pointStab ≤ H := hH6 ▸ inf_le_left
    rcases eq_or_eq_of_isCoatom isCoatom_pointStab hle h2 with h' | h'
    · exact absurd (mem_pointStab_iff.mp (h' ▸ hH)).2 h6
    · exact h'
  obtain ⟨g₁, hg₁, hg₁6⟩ := htr 0
  have hr : g₁⁻¹ 6 ≠ 6 := by
    intro e
    have := congrArg g₁ e
    rw [app_inv, hg₁6] at this
    exact absurd this (by decide)
  obtain ⟨f, hf, -, hf0⟩ := six_reach (g₁⁻¹ 6) hr
  have hg₁0 : g₁⁻¹ 0 = 6 := by rw [← hg₁6, inv_app]
  set σ := f * g₁⁻¹ with hσdef
  have hσH : σ ∈ H := H.mul_mem (h1 hf) (H.inv_mem hg₁)
  have hσ0 : σ 0 = 6 := by rw [hσdef, Perm.mul_apply, hg₁0, kJ_stdT3_fix hf]
  have hσ6 : σ 6 = 0 := by rw [hσdef, Perm.mul_apply, hf0]
  have hσi6 : σ⁻¹ 6 = 0 := by rw [← hσ0, inv_app]
  have hσi0 : σ⁻¹ 0 = 6 := by rw [← hσ6, inv_app]
  have ha : swap (2 : Fin 7) 3 * swap 4 5 ∈ kJ (stdT3 7) := mem_kJ_stdT3 (by decide +kernel)
  set x := σ * (swap 2 3 * swap 4 5) * σ⁻¹ with hxdef
  have hxH : x ∈ H := H.mul_mem (H.mul_mem hσH (h1 ha)) (H.inv_mem hσH)
  have hx6 : x 6 = 6 := by
    rw [hxdef, Perm.mul_apply, Perm.mul_apply, hσi6, show (swap 2 3 * swap 4 5 : Perm (Fin 7)) 0 = 0
      by decide, hσ0]
  have hx0 : x 0 = 0 := by
    rw [hxdef, Perm.mul_apply, Perm.mul_apply, hσi0, show (swap 2 3 * swap 4 5 : Perm (Fin 7)) 6 = 6
      by decide, hσ6]
  have hxN : x ∈ kJ (stdT3 7) := by
    rw [← hH6]
    exact Subgroup.mem_inf.mpr ⟨hxH, mem_pointStab_iff.mpr
      ⟨Perm.mem_alternatingGroup.mp (h2 hxH), hx6⟩⟩
  have hxN' := hxN
  rw [kJ_stdT3, mem_alt_inf_centralizer_iff] at hxN'
  have hxconj : ∀ y, x (σ y) = σ ((swap 2 3 * swap 4 5 : Perm (Fin 7)) y) := by
    intro y
    rw [hxdef, Perm.mul_apply, Perm.mul_apply, inv_app]
  have hxmov : ∀ y : Fin 7, x y = y → y = 0 ∨ y = 1 ∨ y = 6 := by
    have hnot : ¬ (x 2 = 2 ∨ x 3 = 3 ∨ x 4 = 4 ∨ x 5 = 5) := by
      intro hfx
      have hid := ((s7_checks x).1 hxN'.2 hxN'.1).2 hx0 hfx
      have h2' := hid (σ 2)
      rw [hxconj] at h2'
      have := σ.injective h2'
      exact absurd this (by decide)
    have hcases : ∀ y : Fin 7, y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 6 := by
      decide
    intro y hy
    rcases hcases y with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd (Or.inl hy) hnot
    · exact absurd (Or.inr (Or.inl hy)) hnot
    · exact absurd (Or.inr (Or.inr (Or.inl hy))) hnot
    · exact absurd (Or.inr (Or.inr (Or.inr hy))) hnot
    · exact Or.inr (Or.inr rfl)
  have hσ1 : σ 1 = 1 := by
    have hfix1 : x (σ 1) = σ 1 := by
      rw [hxconj, show (swap 2 3 * swap 4 5 : Perm (Fin 7)) 1 = 1 by decide]
    rcases hxmov _ hfix1 with e | e | e
    · exact absurd (σ.injective (e.trans hσ6.symm)) (by decide)
    · exact e
    · exact absurd (σ.injective (e.trans hσ0.symm)) (by decide)
  have hσ2 : σ 2 = 2 ∨ σ 2 = 3 ∨ σ 2 = 4 ∨ σ 2 = 5 := by
    have h20 : σ 2 ≠ 6 := fun e => absurd (σ.injective (e.trans hσ0.symm)) (by decide)
    have h21 : σ 2 ≠ 1 := fun e => absurd (σ.injective (e.trans hσ1.symm)) (by decide)
    have h26 : σ 2 ≠ 0 := fun e => absurd (σ.injective (e.trans hσ6.symm)) (by decide)
    revert h20 h21 h26
    generalize σ 2 = w
    revert w
    decide
  obtain ⟨m, hm, hm2, hm6, hm0, hm1⟩ : ∃ m ∈ kJ (stdT3 7), m (σ 2) = 2 ∧ m 6 = 6 ∧ m 0 = 0 ∧
      m 1 = 1 := by
    rcases hσ2 with e | e | e | e <;> rw [e]
    · exact ⟨1, Subgroup.one_mem _, rfl, rfl, rfl, rfl⟩
    · exact ⟨swap 2 3 * swap 4 5, ha, by decide, by decide, by decide, by decide⟩
    · exact ⟨swap 2 4 * swap 3 5, mem_kJ_stdT3 (by decide +kernel), by decide, by decide,
        by decide, by decide⟩
    · exact ⟨swap 2 5 * swap 3 4, mem_kJ_stdT3 (by decide +kernel), by decide, by decide,
        by decide, by decide⟩
  set τ := m * σ with hτdef
  have hτH : τ ∈ H := H.mul_mem (h1 hm) hσH
  have hτ0 : τ 0 = 6 := by rw [hτdef, Perm.mul_apply, hσ0, hm6]
  have hτ1 : τ 1 = 1 := by rw [hτdef, Perm.mul_apply, hσ1, hm1]
  have hτ2 : τ 2 = 2 := by rw [hτdef, Perm.mul_apply, hm2]
  have hτ6 : τ 6 = 0 := by rw [hτdef, Perm.mul_apply, hσ6, hm0]
  have hτs : sign τ = 1 := Perm.mem_alternatingGroup.mp (h2 hτH)
  rcases (s7_checks τ).2 hτ0 hτ1 hτ2 hτ6 hτs with e | e | e
  ·
    left
    have hτL : τ ∈ fanoStabEven := by
      rw [e]
      exact Subgroup.mem_inf.mpr ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel),
        MulAction.mem_stabilizer_iff.mpr (by decide +kernel)⟩
    exact eq_of_six_zero h1 h2 kJ_stdT3_le_fanoStabEven inf_le_left hH6
      fanoStabEven_inf_pointStab hτH hτL hτ6
  ·
    right
    left
    have hτL : τ ∈ fanoStabOdd := by
      rw [e]
      exact Subgroup.mem_inf.mpr ⟨Perm.mem_alternatingGroup.mpr (by decide +kernel),
        MulAction.mem_stabilizer_iff.mpr (by decide +kernel)⟩
    exact eq_of_six_zero h1 h2 kJ_stdT3_le_fanoStabOdd inf_le_left hH6
      fanoStabOdd_inf_pointStab hτH hτL hτ6
  ·
    right
    right
    have hb : swap (0 : Fin 7) 1 * swap 4 5 ∈ kJ (stdT3 7) := mem_kJ_stdT3 (by decide +kernel)
    have hc : swap (0 : Fin 7) 6 * swap 0 1 ∈ H := by
      have : τ * (swap 0 1 * swap 4 5) = swap 0 6 * swap 0 1 := by
        rw [e]
        decide +kernel
      rw [← this]
      exact H.mul_mem hτH (h1 hb)
    exact le_antisymm h2 (alternatingGroup_le_of_prime (by rw [Fintype.card_fin]; norm_num) htr
      isThreeCycle_016 hc)

end KThree

end CFSG.Quasithin.SmithC27
