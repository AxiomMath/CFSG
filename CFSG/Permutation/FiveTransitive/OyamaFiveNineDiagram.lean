module

public import CFSG.Permutation.FiveTransitive.CommutingFourSeed
public import CFSG.Permutation.FiveTransitive.OyamaFiveFirstPair
public import CFSG.Permutation.FiveTransitive.OyamaFiveSecondPair

public section

namespace CFSG

namespace FiveTransitive.OyamaFiveNineDiagram

open MulAction FixedFiveInvolutionGeometry CommutingFourSeed

theorem exists_diagram
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (hseed : Seed G X)
    (hmax : ∀ g : G, g * g = 1 → g ≠ 1 → (fixedBy X g).ncard ≤ 5)
    (a : G) (ha : a * a = 1) (hfixa : (fixedBy X a).ncard = 5)
    (t : Fin 4 ↪ X)
    (ha01 : a • t 0 = t 1) (ha10 : a • t 1 = t 0)
    (ha23 : a • t 2 = t 3) (ha32 : a • t 3 = t 2) :
    ∃ (e : Fin 9 ↪ X) (c : G),
      (∀ i : Fin 4, e (Fin.natAdd 5 i) = t i) ∧
      c * c = 1 ∧ c ≠ 1 ∧ a * c = c * a ∧
      fixedBy X a = {e 0, e 1, e 2, e 3, e 4} ∧
      fixedBy X c = {e 0, e 1, e 2, e 5, e 6} ∧
      fixedBy X (a * c) = {e 0, e 1, e 2, e 7, e 8} ∧
      a • e 5 = e 6 ∧ a • e 6 = e 5 ∧ a • e 7 = e 8 ∧ a • e 8 = e 7 ∧
      c • e 3 = e 4 ∧ c • e 4 = e 3 ∧ c • e 7 = e 8 ∧ c • e 8 = e 7 := by
  have htcard : (Set.range t).ncard = 4 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective t.injective
  have htnofix (i : Fin 4) : t i ∉ fixedBy X a := by
    change a • t i ≠ t i
    fin_cases i
    · change a • t 0 ≠ t 0
      rw [ha01]; intro h; have := t.injective h; omega
    · change a • t 1 ≠ t 1
      rw [ha10]; intro h; have := t.injective h; omega
    · change a • t 2 ≠ t 2
      rw [ha23]; intro h; have := t.injective h; omega
    · change a • t 3 ≠ t 3
      rw [ha32]; intro h; have := t.injective h; omega
  have htstable : ∀ x ∈ Set.range t, a • x ∈ Set.range t := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨1, ha01.symm⟩
    · exact ⟨0, ha10.symm⟩
    · exact ⟨3, ha23.symm⟩
    · exact ⟨2, ha32.symm⟩
  obtain ⟨b, hb, hb1, hbfix, hab⟩ := for_one hseed (Set.range t) htcard a ha htstable
  have hdisj : Disjoint (Set.range t) (fixedBy X a) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i, rfl⟩ h
    exact htnofix i h
  obtain ⟨u, hurange, hfixb, hb0, hb12, hb21, hb34, hb43⟩ :=
    OyamaFiveFirstPair.enumerate_fixed_five a b hb hab hfixa (hmax b hb hb1)
      (Set.range t) htcard hdisj hbfix
  let e : Fin 9 ↪ X := ⟨Fin.append u t, Fin.append_injective_iff.mpr
    ⟨u.injective, t.injective, by
      intro i j he
      have hu : u i ∈ fixedBy X a := hurange ▸ Set.mem_range_self i
      exact htnofix j (he ▸ hu)⟩⟩
  have heL (i : Fin 5) : e (Fin.castAdd 4 i) = u i := Fin.append_left u t i
  have heR (i : Fin 4) : e (Fin.natAdd 5 i) = t i := Fin.append_right u t i
  have huall : Set.range u = {e 0, e 1, e 2, e 3, e 4} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
  have htall : Set.range t = {e 5, e 6, e 7, e 8} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
  have hfixae : fixedBy X a = {e 0, e 1, e 2, e 3, e 4} := hurange.symm.trans huall
  have hfixbe : fixedBy X b = {e 0, e 5, e 6, e 7, e 8} := by
    rw [hfixb, htall]
    rfl
  have haE5 : a • e 5 = e 6 := ha01
  have haE6 : a • e 6 = e 5 := ha10
  have haE7 : a • e 7 = e 8 := ha23
  have haE8 : a • e 8 = e 7 := ha32
  have haE (i : Fin 9) (hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) : a • e i = e i := by
    change e i ∈ fixedBy X a
    rw [hfixae]
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
  have hbE1 : b • e 1 = e 2 := hb12
  have hbE2 : b • e 2 = e 1 := hb21
  have hbE5 : b • e 5 = e 5 := hbfix _ ⟨0, rfl⟩
  have hbE6 : b • e 6 = e 6 := hbfix _ ⟨1, rfl⟩
  let s : Set X := {e 1, e 2, e 5, e 6}
  have hs : s.ncard = 4 := by simp [s, e.injective.eq_iff]
  have haS : ∀ x ∈ s, a • x ∈ s := by
    intro x hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [haE 1 (by simp)]; simp [s]
    · rw [haE 2 (by simp)]; simp [s]
    · rw [haE5]; simp [s]
    · rw [haE6]; simp [s]
  have hbS : ∀ x ∈ s, b • x ∈ s := by
    intro x hx
    simp only [s, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp only [hbE1, hbE2, hbE5, hbE6] <;> simp [s]
  obtain ⟨c, hc, hc1, hcfix, hac, hbc⟩ := for_pair hseed s hs a b ha hb hab haS hbS
  obtain ⟨hfixc, hc0, hc34, hc43, hc78, hc87⟩ := OyamaFiveSecondPair.coordinates
    hmax e a b c hc hc1 hac hbc hfixae hfixbe
    (hcfix _ (by simp [s])) (hcfix _ (by simp [s]))
    (hcfix _ (by simp [s])) (hcfix _ (by simp [s]))
  have hcE1 : c • e 1 = e 1 := hcfix _ (by simp [s])
  have hcE2 : c • e 2 = e 2 := hcfix _ (by simp [s])
  have hac1 : a * c ≠ 1 := by
    intro he
    have hh : (a * c) • e 3 = e 3 := by rw [he, one_smul]
    rw [mul_smul, hc34, haE 4 (by simp)] at hh
    have := e.injective hh
    omega
  have hfixac : fixedBy X (a * c) = {e 0, e 1, e 2, e 7, e 8} := by
    apply fixedBy_eq_of_five (a * c) (hmax _ (mul_square_one a c ha hc hac) hac1)
    · simp [e.injective.eq_iff]
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> change (a * c) • _ = _
      · rw [mul_smul, hc0, haE 0 (by simp)]
      · rw [mul_smul, hcE1, haE 1 (by simp)]
      · rw [mul_smul, hcE2, haE 2 (by simp)]
      · rw [mul_smul, hc78, haE8]
      · rw [mul_smul, hc87, haE7]
  exact ⟨e, c, heR, hc, hc1, hac, hfixae, hfixc, hfixac,
    haE5, haE6, haE7, haE8, hc34, hc43, hc78, hc87⟩

end FiveTransitive.OyamaFiveNineDiagram

end CFSG
