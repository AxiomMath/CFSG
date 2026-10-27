module

public import CFSG.Quasithin.EmptyFaithful.F112SInputs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Quasithin.F112S

open CFSG.Open

section Adjoin

variable {G : Type*} [Group G]

@[expose] def adjoin (A : Subgroup G) (y : G) (hy : y * y = 1) (hc : ∀ a ∈ A, a * y = y * a) :
    Subgroup G where
  carrier := {x | x ∈ A ∨ ∃ a ∈ A, x = y * a}
  one_mem' := Or.inl A.one_mem
  mul_mem' := by
    intro x z hx hz
    rcases hx with hx | ⟨a, ha, rfl⟩ <;> rcases hz with hz | ⟨b, hb, rfl⟩
    · exact Or.inl (A.mul_mem hx hz)
    · refine Or.inr ⟨x * b, A.mul_mem hx hb, ?_⟩
      rw [← mul_assoc, hc x hx, mul_assoc]
    · exact Or.inr ⟨a * z, A.mul_mem ha hz, by rw [mul_assoc]⟩
    · refine Or.inl ?_
      have : y * a * (y * b) = a * b := by
        calc y * a * (y * b) = y * (a * y) * b := by group
          _ = y * (y * a) * b := by rw [hc a ha]
          _ = (y * y) * a * b := by group
          _ = a * b := by rw [hy, one_mul]
      rw [this]
      exact A.mul_mem ha hb
  inv_mem' := by
    rintro _ (ha | ⟨a, ha, rfl⟩)
    · exact Or.inl (A.inv_mem ha)
    · refine Or.inr ⟨a⁻¹, A.inv_mem ha, ?_⟩
      have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
      rw [mul_inv_rev, hy', hc a⁻¹ (A.inv_mem ha)]

theorem mem_adjoin {A : Subgroup G} {y : G} {hy : y * y = 1} {hc : ∀ a ∈ A, a * y = y * a}
    {x : G} : x ∈ adjoin A y hy hc ↔ x ∈ A ∨ ∃ a ∈ A, x = y * a := Iff.rfl

theorem le_adjoin {A : Subgroup G} {y : G} {hy : y * y = 1} {hc : ∀ a ∈ A, a * y = y * a} :
    A ≤ adjoin A y hy hc := fun _ hx => Or.inl hx

theorem mem_adjoin_self {A : Subgroup G} {y : G} {hy : y * y = 1}
    {hc : ∀ a ∈ A, a * y = y * a} : y ∈ adjoin A y hy hc :=
  Or.inr ⟨1, A.one_mem, (mul_one y).symm⟩

theorem adjoin_le {A B : Subgroup G} {y : G} {hy : y * y = 1} {hc : ∀ a ∈ A, a * y = y * a}
    (hAB : A ≤ B) (hyB : y ∈ B) : adjoin A y hy hc ≤ B := by
  rintro _ (hx | ⟨a, ha, rfl⟩)
  · exact hAB hx
  · exact B.mul_mem hyB (hAB ha)

theorem card_adjoin_le [Finite G] {A : Subgroup G} {y : G} {hy : y * y = 1}
    {hc : ∀ a ∈ A, a * y = y * a} : Nat.card (adjoin A y hy hc) ≤ 2 * Nat.card A := by
  let f : A × Bool → adjoin A y hy hc := fun p =>
    if p.2 then ⟨y * p.1, Or.inr ⟨p.1, p.1.2, rfl⟩⟩ else ⟨p.1, Or.inl p.1.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx | ⟨a, ha, rfl⟩⟩
    · exact ⟨(⟨x, hx⟩, false), rfl⟩
    · exact ⟨(⟨a, ha⟩, true), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

end Adjoin

theorem search_zero (N : ℕ) (mulT : ℕ → ℕ → ℕ) (sp : List ℕ) (lo : ℕ) :
    search N mulT 0 sp lo = false := rfl

theorem search_child {N : ℕ} {mulT : ℕ → ℕ → ℕ} {f : ℕ} {sp : List ℕ} {lo : ℕ}
    (h : search N mulT (f + 1) sp lo = true) {y : ℕ} (hy : y < N) (hlo : lo ≤ y)
    (hsp : y ∉ sp) (hc : ∀ s ∈ sp, mulT y s < N) (hm : ∀ s ∈ sp, y ≤ mulT y s) :
    search N mulT f (y :: (sp ++ sp.map (mulT y))) (y + 1) = true := by
  simp only [search, List.all_eq_true, List.mem_range] at h
  have h1 := h y hy
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem,
    Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_false] at h1
  rcases h1 with (((h | h) | ⟨x, hx, h⟩) | ⟨x, hx, h⟩) | h
  · omega
  · exact absurd h hsp
  · exact absurd (hc x hx) h
  · exact absurd (hm x hx) h
  · exact h

section Main

variable {G : Type*} [Group G] [Finite G]

structure InvList (S : Subgroup G) (N : ℕ) (φ : ℕ → G) (mulT : ℕ → ℕ → ℕ) : Prop where
  ne_one : ∀ i < N, φ i ≠ 1
  inj : ∀ i < N, ∀ j < N, φ i = φ j → i = j
  complete : ∀ x ∈ S, x * x = 1 → x ≠ 1 → ∃ i < N, φ i = x
  mul : ∀ i < N, ∀ j < N, (∃ k < N, φ k = φ i * φ j) → mulT i j < N ∧ φ (mulT i j) = φ i * φ j

theorem card_le_of_search {S : Subgroup G} {N : ℕ} {φ : ℕ → G} {mulT : ℕ → ℕ → ℕ}
    (hI : InvList S N φ mulT) (hs : search N mulT 6 [] 0 = true)
    {E : Subgroup G} (hES : E ≤ S) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 32 := by
  by_contra hlt
  have hlt : 32 < Nat.card E := not_le.mp hlt
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ E, a * a = 1 := fun a ha => by simpa [sq] using hE.2 a ha
  let Inv : ℕ → List ℕ → ℕ → Subgroup G → Prop := fun j sp lo A =>
    A ≤ E ∧ Nat.card A ≤ 2 ^ j ∧ (∀ i < N, (i ∈ sp ↔ φ i ∈ A)) ∧ (∀ i ∈ sp, i < N) ∧
      (∀ i < N, φ i ∈ E → φ i ∉ A → lo ≤ i)
  have key : ∀ j ≤ 6, ∃ sp lo A, Inv j sp lo A ∧ search N mulT (6 - j) sp lo = true := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨[], 0, ⊥, ⟨bot_le, by simp, fun i hi => ?_, by simp, fun i _ _ _ => Nat.zero_le _⟩,
        hs⟩
      simp only [List.not_mem_nil, false_iff, Subgroup.mem_bot]
      exact hI.ne_one i hi
    | succ j ih =>
      intro hj
      obtain ⟨sp, lo, A, ⟨hAE, hAc, hmem, hlt', hlo⟩, hsr⟩ := ih (by omega)
      obtain ⟨f, hf⟩ : ∃ f, 6 - j = f + 1 := ⟨5 - j, by omega⟩
      rw [hf] at hsr
      have hne : A ≠ E := by
        rintro rfl
        have : 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      obtain ⟨x, hxE, hxA⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hAE hne)
      have hx1 : x ≠ 1 := fun h => hxA (h ▸ A.one_mem)
      obtain ⟨i0, hi0N, hi0⟩ := hI.complete x (hES hxE) (hsq x hxE) hx1
      have hex : ∃ i, i < N ∧ φ i ∈ E ∧ φ i ∉ A := ⟨i0, hi0N, hi0 ▸ hxE, hi0 ▸ hxA⟩
      classical
      let y := Nat.find hex
      obtain ⟨hyN, hyE, hyA⟩ : y < N ∧ φ y ∈ E ∧ φ y ∉ A := Nat.find_spec hex
      have hmin : ∀ i, i < N → φ i ∈ E → φ i ∉ A → y ≤ i := fun i hi hiE hiA =>
        Nat.find_min' hex ⟨hi, hiE, hiA⟩
      have hysp : y ∉ sp := fun h => hyA ((hmem y hyN).1 h)
      have hprod : ∀ s ∈ sp, mulT y s < N ∧ φ (mulT y s) = φ y * φ s ∧ y ≤ mulT y s := by
        intro s hs'
        have hsN := hlt' s hs'
        have hsA : φ s ∈ A := (hmem s hsN).1 hs'
        have hsE : φ s ∈ E := hAE hsA
        have hpE : φ y * φ s ∈ E := E.mul_mem hyE hsE
        have hp2 : (φ y * φ s) * (φ y * φ s) = 1 := by
          calc (φ y * φ s) * (φ y * φ s) = φ y * (φ s * φ y) * φ s := by group
            _ = φ y * (φ y * φ s) * φ s := by rw [hcomm _ hsE _ hyE]
            _ = (φ y * φ y) * (φ s * φ s) := by group
            _ = 1 := by rw [hsq _ hyE, hsq _ hsE, one_mul]
        have hp1 : φ y * φ s ≠ 1 := by
          intro h
          apply hyA
          have : φ y = (φ s)⁻¹ := eq_inv_of_mul_eq_one_left h
          rw [this]
          exact A.inv_mem hsA
        obtain ⟨k, hkN, hk⟩ := hI.complete _ (hES hpE) hp2 hp1
        obtain ⟨hm1, hm2⟩ := hI.mul y hyN s hsN ⟨k, hkN, hk⟩
        refine ⟨hm1, hm2, hmin _ hm1 (hm2 ▸ hpE) ?_⟩
        rw [hm2]
        intro h
        apply hyA
        have : φ y = (φ y * φ s) * (φ s)⁻¹ := by group
        rw [this]
        exact A.mul_mem h (A.inv_mem hsA)
      have hchild := search_child hsr hyN (hlo y hyN hyE hyA) hysp
        (fun s hs' => (hprod s hs').1) (fun s hs' => (hprod s hs').2.2)
      have hcy : ∀ a ∈ A, a * φ y = φ y * a := fun a ha => hcomm a (hAE ha) _ hyE
      refine ⟨y :: (sp ++ sp.map (mulT y)), y + 1, adjoin A (φ y) (hsq _ hyE) hcy,
        ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · exact adjoin_le hAE hyE
      · have := card_adjoin_le (A := A) (y := φ y) (hy := hsq _ hyE) (hc := hcy)
        calc Nat.card (adjoin A (φ y) (hsq _ hyE) hcy) ≤ 2 * Nat.card A := this
          _ ≤ 2 * 2 ^ j := Nat.mul_le_mul_left 2 hAc
          _ = 2 ^ (j + 1) := by ring
      · intro i hi
        simp only [List.mem_cons, List.mem_append, List.mem_map, mem_adjoin]
        constructor
        · rintro (rfl | h | ⟨s, hs', rfl⟩)
          · exact Or.inr ⟨1, A.one_mem, (mul_one _).symm⟩
          · exact Or.inl ((hmem i hi).1 h)
          · exact Or.inr ⟨φ s, (hmem s (hlt' s hs')).1 hs', (hprod s hs').2.1⟩
        · rintro (h | ⟨a, ha, hia⟩)
          · exact Or.inr (Or.inl ((hmem i hi).2 h))
          · by_cases ha1 : a = 1
            · subst ha1
              rw [mul_one] at hia
              exact Or.inl (hI.inj i hi y hyN hia)
            · obtain ⟨s, hsN, hsa⟩ := hI.complete a (hES (hAE ha)) (hsq a (hAE ha)) ha1
              have hs' : s ∈ sp := (hmem s hsN).2 (hsa ▸ ha)
              have h2 := (hprod s hs').2.1
              have : i = mulT y s := hI.inj i hi _ (hprod s hs').1 (by rw [h2, hsa, hia])
              exact Or.inr (Or.inr ⟨s, hs', this.symm⟩)
      · intro i hi
        simp only [List.mem_cons, List.mem_append, List.mem_map] at hi
        rcases hi with rfl | h | ⟨s, hs', rfl⟩
        · exact hyN
        · exact hlt' i h
        · exact (hprod s hs').1
      · intro i hi hiE hiA
        have hiA' : φ i ∉ A := fun h => hiA (le_adjoin h)
        have hne' : i ≠ y := fun h => hiA (h ▸ mem_adjoin_self)
        have := hmin i hi hiE hiA'
        omega
      · have : 6 - (j + 1) = f := by omega
        rw [this]
        exact hchild
  obtain ⟨sp, lo, A, -, hsr⟩ := key 6 le_rfl
  rw [Nat.sub_self, search_zero] at hsr
  exact Bool.false_ne_true hsr

end Main

end CFSG.Quasithin.F112S
