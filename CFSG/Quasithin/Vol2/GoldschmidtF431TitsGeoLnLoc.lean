module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoBase

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}

structure LnLoc (X : Type u) [Group X] {V : Type v} [MulAction X V] (Γ : SimpleGraph V)
    (a b₇ b₁ b₂ : V) : Prop where
  card : (Γ.neighborSet a).ncard = 3
  orb7 : ∀ b, Γ.dist a b = 7 → ∃ g : X, g • a = a ∧ g • b₇ = b
  orb8 : ∀ b, Γ.dist a b = 8 → (∃ g : X, g • a = a ∧ g • b₁ = b) ∨
    ∃ g : X, g • a = a ∧ g • b₂ = b
  moves1 : ∀ u, Γ.Adj a u → ∃ k : X, k • a = a ∧ k • b₁ = b₁ ∧ k • u = u ∧
    ∃ w, Γ.Adj a w ∧ k • w ≠ w
  moves2 : ∀ u, Γ.Adj a u → ∃ k : X, k • a = a ∧ k • b₂ = b₂ ∧ k • u = u ∧
    ∃ w, Γ.Adj a w ∧ k • w ≠ w

variable [GraphAction X Γ]

theorem nontriv_of_moves (hP : IsGenPolygon Γ 8) {a b : V} {r : GPath Γ 8}
    (hr : r ∈ GPath.nbPaths Γ a 8) (hb : ∃ h : X, h • a = a ∧ h • b = r 8)
    (hmv : ∀ u, Γ.Adj a u → ∃ k : X, k • a = a ∧ k • b = b ∧ k • u = u ∧
      ∃ w, Γ.Adj a w ∧ k • w ≠ w) :
    ∃ g ∈ (r.stabPath : Subgroup X), ∃ w, Γ.Adj a w ∧ g • w ≠ w := by
  obtain ⟨h, hha, hhb⟩ := hb
  have hh1 : h⁻¹ • a = a := by rw [inv_smul_eq_iff, hha]
  have hs : h⁻¹ • r ∈ GPath.nbPaths Γ a 8 := smul_mem_nbPaths hr hh1
  have hs8 : (h⁻¹ • r) 8 = b := by
    rw [GPath.smul_apply, inv_smul_eq_iff, hhb]
  have a1 : Γ.Adj a ((h⁻¹ • r) 1) := by
    have := (h⁻¹ • r).adj 0 (by norm_num)
    rwa [hs.1] at this
  obtain ⟨k, hka, hkb, hku, w, hw, hkw⟩ := hmv _ a1
  have hk : k ∈ ((h⁻¹ • r).stabPath : Subgroup X) :=
    mem_stabPath_of_fix hP hs hka hku (by rw [hs8]; exact hkb)
  refine ⟨h * k * h⁻¹, ?_, h • w, ?_, ?_⟩
  · have e : h • (h⁻¹ • r) = r := by
      rw [← GPath.mul_smul', mul_inv_cancel, GPath.one_smul']
    rw [← e, GPath.stabPath_smul]
    exact mul_mem_conjSub hk
  · have := (GraphAction.adj_smul h a w).mpr hw
    rwa [hha] at this
  · rw [mul_smul, mul_smul, inv_smul_smul]
    intro hcon
    exact hkw (smul_left_cancel h hcon)

theorem swap_of_moves {a P Q R : V} (hPQ : P ≠ Q) (hPR : P ≠ R) (hQR : Q ≠ R)
    (hT : ∀ t, Γ.Adj a t → t = P ∨ t = Q ∨ t = R) (hP : Γ.Adj a P) (hQ : Γ.Adj a Q)
    (hR : Γ.Adj a R) {g : X} (hga : g • a = a) (hgP : g • P = P)
    (hm : ∃ w, Γ.Adj a w ∧ g • w ≠ w) : g • Q = R ∧ g • R = Q := by
  have hmap : ∀ t, Γ.Adj a t → Γ.Adj a (g • t) := fun t ht => by
    have := (GraphAction.adj_smul g a t).mpr ht
    rwa [hga] at this
  have hinj : ∀ s t : V, g • s = g • t → s = t := fun s t h => smul_left_cancel g h
  obtain ⟨w, hw, hgw⟩ := hm
  have key : g • Q = R ∨ g • R = Q := by
    rcases hT w hw with rfl | rfl | rfl
    · exact absurd hgP hgw
    · left
      rcases hT _ (hmap _ hQ) with h | h | h
      · exact absurd (hinj _ _ (h.trans hgP.symm)) (Ne.symm hPQ)
      · exact absurd h hgw
      · exact h
    · right
      rcases hT _ (hmap _ hR) with h | h | h
      · exact absurd (hinj _ _ (h.trans hgP.symm)) (Ne.symm hPR)
      · exact h
      · exact absurd h hgw
  rcases key with h | h
  · refine ⟨h, ?_⟩
    rcases hT _ (hmap _ hR) with h' | h' | h'
    · exact absurd (hinj _ _ (h'.trans hgP.symm)) (Ne.symm hPR)
    · exact h'
    · exact absurd (hinj _ _ (h'.trans h.symm)) (Ne.symm hQR)
  · refine ⟨?_, h⟩
    rcases hT _ (hmap _ hQ) with h' | h' | h'
    · exact absurd (hinj _ _ (h'.trans hgP.symm)) (Ne.symm hPQ)
    · exact absurd (hinj _ _ (h'.trans h.symm)) hQR
    · exact h'

namespace LnLoc

variable {a b₇ b₁ b₂ : V} (L : LnLoc X Γ a b₇ b₁ b₂) (hP : IsGenPolygon Γ 8)

include L hP

theorem pathTrans7 {q q' : GPath Γ 7} (hq : q ∈ GPath.nbPaths Γ a 7)
    (hq' : q' ∈ GPath.nbPaths Γ a 7) : ∃ g : X, g • a = a ∧ g • q = q' := by
  have d := end_dist hP (by norm_num) hq
  have d' := end_dist hP (by norm_num) hq'
  obtain ⟨h, hha, hhq⟩ := L.orb7 _ d
  obtain ⟨h', hha', hhq'⟩ := L.orb7 _ d'
  have hh1 : h⁻¹ • a = a := by rw [inv_smul_eq_iff, hha]
  have hga : (h' * h⁻¹) • a = a := by rw [mul_smul, hh1, hha']
  refine ⟨h' * h⁻¹, hga, ?_⟩
  have g1 : q.IsGeodesic := by
    show Γ.dist (q 0) (q 7) = 7
    rw [hq.1]
    exact d
  have g2 : q'.IsGeodesic := by
    show Γ.dist (q' 0) (q' 7) = 7
    rw [hq'.1]
    exact d'
  refine hP.uniqueGeod 7 _ _ (GPath.IsGeodesic.smul hP.connected g1 _) g2 ?_ ?_ (by norm_num)
  · rw [GPath.smul_apply, hq.1, hq'.1, hga]
  · rw [GPath.smul_apply, ← hhq, ← hhq', mul_smul, inv_smul_smul]

theorem nontriv {r : GPath Γ 8} (hr : r ∈ GPath.nbPaths Γ a 8) :
    ∃ g ∈ (r.stabPath : Subgroup X), ∃ w, Γ.Adj a w ∧ g • w ≠ w := by
  rcases L.orb8 _ (end_dist hP le_rfl hr) with hb | hb
  · exact nontriv_of_moves hP hr hb L.moves1
  · exact nontriv_of_moves hP hr hb L.moves2

theorem transPair {p q : GPath Γ 8} (hp : p ∈ GPath.nbPaths Γ a 8)
    (hq : q ∈ GPath.nbPaths Γ a 8) (hpq : p 1 ≠ q 1) {y y' : V} (hy : Γ.Adj a y)
    (hy' : Γ.Adj a y') : ∃ g ∈ ((p.stabPath : Subgroup X) ⊔ q.stabPath), g • y = y' := by
  obtain ⟨g₁, hg₁, w₁, hw₁, hw₁m⟩ := L.nontriv hP hp
  obtain ⟨g₂, hg₂, w₂, hw₂, hw₂m⟩ := L.nontriv hP hq
  have ha1 : g₁ • a = a := by simpa [hp.1] using hg₁ 0 (Nat.zero_le _)
  have ha2 : g₂ • a = a := by simpa [hq.1] using hg₂ 0 (Nat.zero_le _)
  have hp1 : Γ.Adj a (p 1) := by
    have := p.adj 0 (by norm_num)
    rwa [hp.1] at this
  have hq1 : Γ.Adj a (q 1) := by
    have := q.adj 0 (by norm_num)
    rwa [hq.1] at this
  have hsub : ({p 1, q 1} : Set V) ⊆ Γ.neighborSet a := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hp1
    · exact hq1
  have hc : (Γ.neighborSet a \ {p 1, q 1}).ncard = 1 := by
    rw [Set.ncard_sdiff hsub, L.card, Set.ncard_pair hpq]
  obtain ⟨R, hR⟩ := Set.ncard_eq_one.mp hc
  have hRm : R ∈ Γ.neighborSet a \ {p 1, q 1} := by rw [hR]; rfl
  have hRadj : Γ.Adj a R := hRm.1
  have hRP : R ≠ p 1 := fun h => hRm.2 (Or.inl h)
  have hRQ : R ≠ q 1 := fun h => hRm.2 (Or.inr h)
  have hT : ∀ t, Γ.Adj a t → t = p 1 ∨ t = q 1 ∨ t = R := by
    intro t ht
    by_cases h1 : t = p 1
    · exact Or.inl h1
    by_cases h2 : t = q 1
    · exact Or.inr (Or.inl h2)
    have : t ∈ Γ.neighborSet a \ {p 1, q 1} := ⟨ht, by simp [h1, h2]⟩
    rw [hR] at this
    exact Or.inr (Or.inr this)
  have e1P : g₁ • p 1 = p 1 := hg₁ 1 (by norm_num)
  obtain ⟨e1Q, e1R⟩ := swap_of_moves hpq (Ne.symm hRP) (Ne.symm hRQ) hT hp1 hq1 hRadj ha1 e1P
    ⟨w₁, hw₁, hw₁m⟩
  have e2Q : g₂ • q 1 = q 1 := hg₂ 1 (by norm_num)
  have hT' : ∀ t, Γ.Adj a t → t = q 1 ∨ t = p 1 ∨ t = R := fun t ht => by
    rcases hT t ht with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  obtain ⟨e2P, e2R⟩ := swap_of_moves hpq.symm (Ne.symm hRQ) (Ne.symm hRP) hT' hq1 hp1 hRadj ha2
    e2Q ⟨w₂, hw₂, hw₂m⟩
  have m1 : g₁ ∈ (p.stabPath : Subgroup X) ⊔ q.stabPath := Subgroup.mem_sup_left hg₁
  have m2 : g₂ ∈ (p.stabPath : Subgroup X) ⊔ q.stabPath := Subgroup.mem_sup_right hg₂
  have o1 : (1 : X) ∈ (p.stabPath : Subgroup X) ⊔ q.stabPath := Subgroup.one_mem _
  rcases hT y hy with h | h | h <;> rcases hT y' hy' with h' | h' | h' <;> rw [h, h']
  · exact ⟨1, o1, one_smul _ _⟩
  · exact ⟨g₁ * g₂, Subgroup.mul_mem _ m1 m2, by rw [mul_smul, e2P, e1R]⟩
  · exact ⟨g₂, m2, e2P⟩
  · exact ⟨g₂ * g₁, Subgroup.mul_mem _ m2 m1, by rw [mul_smul, e1Q, e2R]⟩
  · exact ⟨1, o1, one_smul _ _⟩
  · exact ⟨g₁, m1, e1Q⟩
  · exact ⟨g₂, m2, e2R⟩
  · exact ⟨g₁, m1, e1R⟩
  · exact ⟨1, o1, one_smul _ _⟩

omit [GraphAction X Γ] hP in
theorem exists_third {p q : V} (hp : Γ.Adj a p) (hq : Γ.Adj a q)
    (hpq : p ≠ q) : ∃ R, Γ.Adj a R ∧ R ≠ p ∧ R ≠ q ∧
      ∀ t, Γ.Adj a t → t = p ∨ t = q ∨ t = R := by
  have hsub : ({p, q} : Set V) ⊆ Γ.neighborSet a := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hq
  have hc : (Γ.neighborSet a \ {p, q}).ncard = 1 := by
    rw [Set.ncard_sdiff hsub, L.card, Set.ncard_pair hpq]
  obtain ⟨R, hR⟩ := Set.ncard_eq_one.mp hc
  have hRm : R ∈ Γ.neighborSet a \ {p, q} := by rw [hR]; rfl
  refine ⟨R, hRm.1, fun h => hRm.2 (Or.inl h), fun h => hRm.2 (Or.inr h), fun t ht => ?_⟩
  by_cases h1 : t = p
  · exact Or.inl h1
  by_cases h2 : t = q
  · exact Or.inr (Or.inl h2)
  have : t ∈ Γ.neighborSet a \ {p, q} := ⟨ht, by simp [h1, h2]⟩
  rw [hR] at this
  exact Or.inr (Or.inr this)

omit hP in
theorem flag {u u' : V} (hu : Γ.Adj a u) (hu' : Γ.Adj a u') :
    ∃ k : X, k • a = a ∧ k • u = u' := by
  by_cases huu : u = u'
  · exact ⟨1, one_smul _ _, by rw [one_smul, huu]⟩
  obtain ⟨R, hR, hRu, hRu', hT⟩ := L.exists_third hu hu' huu
  obtain ⟨k, hka, -, hkR, w, hw, hkw⟩ := L.moves1 R hR
  have hT' : ∀ t, Γ.Adj a t → t = R ∨ t = u ∨ t = u' := fun t ht => by
    rcases hT t ht with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  obtain ⟨hku, -⟩ := swap_of_moves hRu hRu' huu hT' hR hu hu' hka hkR
    ⟨w, hw, hkw⟩
  exact ⟨k, hka, hku⟩

end LnLoc

end CFSG.Quasithin.TitsGeo
