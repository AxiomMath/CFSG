module

public import CFSG.GroupTheory.ThompsonIndexTwo
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

public section

namespace CFSG.Quasithin.SBd16

section Thompson

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem no_index_two_of_simple (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hidx
  have : N.Normal := hN
  rcases hs.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.index_bot] at hidx
    have : Fact (Nat.Prime (Nat.card G)) := ⟨by rw [hidx]; exact Nat.prime_two⟩
    have hcyc : IsCyclic G := isCyclic_of_prime_card rfl
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (mul_comm a b)
  · rw [h, Subgroup.index_top] at hidx
    omega

theorem exists_conj_mem_of_index_two (hG : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) {T W : Subgroup G}
    (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) (hWT : W ≤ T) (hW : W.relIndex T = 2) {x : G}
    (hxT : x ∈ T) (hxW : x ∉ W) (hx2 : x * x = 1) : ∃ g : G, g⁻¹ * x * g ∈ W := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := fun h => hxW (h ▸ W.one_mem)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hmin : ∀ y ∈ T, y ∉ W → orderOf x ≤ orderOf y := by
    intro y _ hyW
    have hy1 : y ≠ 1 := fun h => hyW (h ▸ W.one_mem)
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    have h2 := orderOf_pos y
    rw [hxo]
    omega
  obtain ⟨N, hN, hNidx⟩ :=
    CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hT hTidx hWT hW hxT hxW hmin hcon
  exact hG N hN hNidx

end Thompson

section TI

variable {G : Type*} [Group G]

theorem mem_of_conj_mem {X M : Subgroup G}
    (hM : ∀ x ∈ X, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ M)
    (hfus : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ X, y ≠ 1 → (∃ g : G, g⁻¹ * x * g = y) →
      ∃ m ∈ M, m⁻¹ * x * m = y)
    {g x : G} (hxX : x ∈ X) (hx1 : x ≠ 1) (hgx : g⁻¹ * x * g ∈ X) : g ∈ M := by
  have hy1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨m, hmM, hm⟩ := hfus x hxX hx1 _ hgx hy1 ⟨g, rfl⟩
  have h1 : (g * m⁻¹) * x * (g * m⁻¹)⁻¹ = x := by
    calc (g * m⁻¹) * x * (g * m⁻¹)⁻¹ = g * (m⁻¹ * x * m) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hm]
      _ = x := by group
  have hc : g * m⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1)
  have : g = (g * m⁻¹) * m := by group
  rw [this]
  exact M.mul_mem (hM x hxX hx1 hc) hmM

theorem normalizes_of_conj_mem {X : Subgroup G}
    (hM : ∀ x ∈ X, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hfus : ∀ x ∈ X, x ≠ 1 → ∀ y ∈ X, y ≠ 1 → (∃ g : G, g⁻¹ * x * g = y) →
      ∃ m ∈ Subgroup.normalizer (X : Set G), m⁻¹ * x * m = y)
    {g x : G} (hxX : x ∈ X) (hx1 : x ≠ 1) (hgx : g⁻¹ * x * g ∈ X) :
    g ∈ Subgroup.normalizer (X : Set G) :=
  mem_of_conj_mem hM hfus hxX hx1 hgx

end TI

section Faithful

variable {G : Type*} [Group G]

theorem isKleinFour_of_card_four {V : Subgroup G} (hV : Nat.card V = 4)
    (hsq : ∀ v ∈ V, v * v = 1) : IsKleinFour ↥V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥V := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial ↥V := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    omega
  refine ⟨hV, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
  refine orderOf_eq_prime ?_ hg
  apply Subtype.ext
  have := hsq g g.2
  simpa [pow_two] using this

theorem mem_klein_four {V : Subgroup G} (hV : Nat.card V = 4) (hsq : ∀ v ∈ V, v * v = 1)
    {a b : G} (haV : a ∈ V) (hbV : b ∈ V) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ∀ c ∈ V, c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  intro c hc
  have : IsKleinFour ↥V := isKleinFour_of_card_four hV hsq
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  by_cases hca : c = a
  · exact Or.inr (Or.inl hca)
  by_cases hcb : c = b
  · exact Or.inr (Or.inr (Or.inl hcb))
  right; right; right
  have := IsKleinFour.eq_mul_of_ne_all (x := (⟨a, haV⟩ : ↥V)) (y := ⟨b, hbV⟩) (z := ⟨c, hc⟩)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
    (fun h => hab (congrArg Subtype.val h)) (fun h => hc1 (congrArg Subtype.val h))
    (fun h => hca (congrArg Subtype.val h)) (fun h => hcb (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem centralizes_of_centralizes_nonidentity {V F : Subgroup G} (hV : Nat.card V = 4)
    (hsq : ∀ v ∈ V, v * v = 1)
    (hTI : ∀ (g x : G), x ∈ V → x ≠ 1 → g⁻¹ * x * g ∈ V → g ∈ Subgroup.normalizer (V : Set G))
    (hFgen : ∀ K : Subgroup G, (∀ x ∈ F, Odd (orderOf x) → x ∈ K) → F ≤ K) {a : G} (haV : a ∈ V)
    (ha1 : a ≠ 1) (haF : ∀ f ∈ F, a * f = f * a) : ∀ b ∈ V, ∀ f ∈ F, b * f = f * b := by
  intro b hbV
  have hFK : F ≤ Subgroup.centralizer ({b} : Set G) := by
    refine hFgen _ fun x hxF hxodd => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxa : x⁻¹ * a * x = a := by
      have := haF x hxF
      calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
        _ = x⁻¹ * (x * a) := by rw [this]
        _ = a := by group
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hTI x a haV ha1 (by rw [hxa]; exact haV)
    have hconjV : ∀ c ∈ V, x⁻¹ * c * x ∈ V := fun c hc => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) c).mp hc
      simpa using this
    by_cases hb1 : b = 1
    · rw [hb1]; simp
    by_cases hba : b = a
    · rw [hba]; exact (haF x hxF).symm
    have hVeq := mem_klein_four hV hsq haV hbV ha1 hb1 (fun h => hba h.symm)
    have hxbV : x⁻¹ * b * x ∈ V := hconjV b hbV
    have hne1 : x⁻¹ * b * x ≠ 1 := by
      intro h
      apply hb1
      calc b = x * (x⁻¹ * b * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hnea : x⁻¹ * b * x ≠ a := by
      intro h
      apply hba
      calc b = x * (x⁻¹ * b * x) * x⁻¹ := by group
        _ = x * a * x⁻¹ := by rw [h]
        _ = a := by
          have : x * a = a * x := (haF x hxF).symm
          rw [this]; group
    have hcases : x⁻¹ * b * x = b ∨ x⁻¹ * b * x = a * b := by
      rcases hVeq _ hxbV with h | h | h | h
      · exact absurd h hne1
      · exact absurd h hnea
      · exact Or.inl h
      · exact Or.inr h
    have hx2 : x⁻¹ * (x⁻¹ * b * x) * x = b := by
      rcases hcases with h | h
      · rw [h]; exact h
      · rw [h]
        calc x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group
          _ = a * (a * b) := by rw [hxa, h]
          _ = (a * a) * b := by group
          _ = b := by rw [hsq a haV]; group
    have hcomm2 : Commute (x * x) b := by
      have h : (x * x)⁻¹ * b * (x * x) = b := by
        calc (x * x)⁻¹ * b * (x * x) = x⁻¹ * (x⁻¹ * b * x) * x := by group
          _ = b := hx2
      show x * x * b = b * (x * x)
      calc x * x * b = (x * x) * ((x * x)⁻¹ * b * (x * x)) := by rw [h]
        _ = b * (x * x) := by group
    obtain ⟨k, hk⟩ := hxodd
    have hxk : x = (x * x) ^ (k + 1) := by
      have h4 : (x * x) ^ (k + 1) = x ^ (orderOf x) * x := by
        rw [← pow_two, ← pow_mul, hk, ← pow_succ]
        congr 1
      rw [h4, pow_orderOf_eq_one, one_mul]
    have : Commute x b := by
      rw [hxk]
      exact hcomm2.pow_left _
    exact this.eq
  exact fun f hf => (Subgroup.mem_centralizer_singleton_iff.mp (hFK hf)).symm

end Faithful

section Commute

variable {G : Type*} [Group G]

theorem commute_of_normalizes {V A : Subgroup G} (hV : Nat.card V = 4) (hA : Nat.card A = 4)
    (hTI : ∀ (g x : G), x ∈ V → x ≠ 1 → g⁻¹ * x * g ∈ V → g ∈ Subgroup.normalizer (V : Set G))
    (hVA : V ⊓ A = ⊥) (hN : ∀ v ∈ V, ∀ a ∈ A, v * a * v⁻¹ ∈ A) :
    ∀ v ∈ V, ∀ a ∈ A, v * a = a * v := by
  have claim1 : ∀ a ∈ A, (∃ x ∈ V, x ≠ 1 ∧ x * a = a * x) → ∀ v ∈ V, v * a = a * v := by
    intro a haA ⟨x, hxV, hx1, hxa⟩ v hvV
    have hax : a⁻¹ * x * a = x := by
      calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
        _ = a⁻¹ * (a * x) := by rw [hxa]
        _ = x := by group
    have haN : a ∈ Subgroup.normalizer (V : Set G) := hTI a x hxV hx1 (by rw [hax]; exact hxV)
    have hav : a⁻¹ * v * a ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) v).mp hvV
      simpa using this
    have hcA : v⁻¹ * (a⁻¹ * v * a) ∈ A := by
      have h1 : v⁻¹ * a⁻¹ * v ∈ A := by
        have := hN v⁻¹ (V.inv_mem hvV) a⁻¹ (A.inv_mem haA)
        simpa using this
      have : v⁻¹ * (a⁻¹ * v * a) = (v⁻¹ * a⁻¹ * v) * a := by group
      rw [this]
      exact A.mul_mem h1 haA
    have hcV : v⁻¹ * (a⁻¹ * v * a) ∈ V := V.mul_mem (V.inv_mem hvV) hav
    have h1 : v⁻¹ * (a⁻¹ * v * a) ∈ V ⊓ A := ⟨hcV, hcA⟩
    rw [hVA, Subgroup.mem_bot] at h1
    have h2 : a⁻¹ * v * a = v := by
      calc a⁻¹ * v * a = v * (v⁻¹ * (a⁻¹ * v * a)) := by group
        _ = v := by rw [h1]; group
    calc v * a = a * (a⁻¹ * v * a) := by group
      _ = a * v := by rw [h2]
  have claim2 : ∀ a ∈ A, a ≠ 1 → ∃ x ∈ V, x ≠ 1 ∧ x * a = a * x := by
    intro a haA ha1
    by_contra hcon
    push Not at hcon
    have : Finite ↥V := Nat.finite_of_card_ne_zero (by omega)
    have : Finite ↥A := Nat.finite_of_card_ne_zero (by omega)
    let g : ↥V ⊕ Unit → ↥A := fun s =>
      Sum.elim (fun x : ↥V => (⟨x * a * x⁻¹, hN x x.2 a haA⟩ : ↥A)) (fun _ => (1 : ↥A)) s
    have hg : Function.Injective g := by
      intro o₁ o₂ h
      rcases o₁ with x | u₁ <;> rcases o₂ with y | u₂
      · simp only [g, Sum.elim_inl] at h
        have h1 : (x : G) * a * (x : G)⁻¹ = (y : G) * a * (y : G)⁻¹ := congrArg Subtype.val h
        have h2 : ((y : G)⁻¹ * x) * a = a * ((y : G)⁻¹ * x) := by
          calc ((y : G)⁻¹ * x) * a = (y : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) * x := by group
            _ = (y : G)⁻¹ * ((y : G) * a * (y : G)⁻¹) * x := by rw [h1]
            _ = a * ((y : G)⁻¹ * x) := by group
        have hz : (y : G)⁻¹ * x ∈ V := V.mul_mem (V.inv_mem y.2) x.2
        have hz1 : (y : G)⁻¹ * x = 1 := by
          by_contra hne
          exact hcon _ hz hne h2
        exact congrArg Sum.inl (Subtype.ext (inv_mul_eq_one.mp hz1).symm)
      · simp only [g, Sum.elim_inl, Sum.elim_inr] at h
        have h1 : (x : G) * a * (x : G)⁻¹ = 1 := congrArg Subtype.val h
        exact absurd (by
          calc a = (x : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) * x := by group
            _ = 1 := by rw [h1]; group) ha1
      · simp only [g, Sum.elim_inl, Sum.elim_inr] at h
        have h1 : (y : G) * a * (y : G)⁻¹ = 1 := (congrArg Subtype.val h).symm
        exact absurd (by
          calc a = (y : G)⁻¹ * ((y : G) * a * (y : G)⁻¹) * y := by group
            _ = 1 := by rw [h1]; group) ha1
      · rfl
    have := Nat.card_le_card_of_injective g hg
    rw [Nat.card_sum, hV, hA, Nat.card_unique] at this
    omega
  intro v hvV a haA
  by_cases ha1 : a = 1
  · rw [ha1]; simp
  exact claim1 a haA (claim2 a haA ha1) v hvV

end Commute

end CFSG.Quasithin.SBd16
