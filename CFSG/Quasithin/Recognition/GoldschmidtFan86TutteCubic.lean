module


import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteFinal
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide

public section

namespace CFSG.Quasithin.Fan86.Tutte

open CFSG.Quasithin.F6.GoldAmL3T Red

theorem le_five_of_regular_of_connected {W : Type} {Γ : SimpleGraph W} (hconn : Γ.Connected)
    (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) {H : Type} [Group H] [MulAction H W]
    (hadj : ∀ (h : H) (u v : W), Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v) {s : ℕ} (hs : 1 ≤ s)
    (htrans : ∀ P Q : Arc Γ s, ∃ h : H, ∀ i, i ≤ s → h • P.vert i = Q.vert i)
    (hfaith : ∀ (P : Arc Γ s) (h : H), (∀ i, i ≤ s → h • P.vert i = P.vert i) →
      ∀ w : W, h • w = w) :
    s ≤ 5 := by
  by_contra h5
  have : Nonempty W := hconn.nonempty
  obtain ⟨r, l, ξ, Hs, hsys⟩ := Geo.isTutteSys_of_regData
    (Geo.regData_of_regular hcard H hadj s hs htrans hfaith) (by omega)
  exact h5 (tutteCalculus _ s r l ξ Hs hsys)

theorem exists_singular_of_connected {W : Type} {Γ : SimpleGraph W} (hconn : Γ.Connected)
    (hcard : ∀ w, Nat.card (Γ.neighborSet w) = 3) {H : Type} [Group H] [MulAction H W]
    (hadj : ∀ (h : H) (u v : W), Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (hvt : ∀ u v : W, ∃ h : H, h • u = v) (hfin : ∀ w : W, Finite (MulAction.stabilizer H w))
    (hloc : ∀ w u v : W, Γ.Adj w u → Γ.Adj w v → ∃ h ∈ MulAction.stabilizer H w, h • u = v) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 5 ∧ ∀ (P : Arc Γ k) (h : H), (∀ i, i ≤ k → h • P.vert i = P.vert i) →
      ∀ w : W, h • w = w := by
  have hdeg : ∀ a b, Γ.Adj a b → ∃ w, Γ.Adj a w ∧ w ≠ b := fun a b hab =>
    exists_other (hcard a) hab
  obtain ⟨w₀⟩ := hconn.nonempty
  obtain ⟨u, hu⟩ : (Γ.neighborSet w₀).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [← Nat.card_coe_set_eq, hcard w₀]
    omega
  have hex : ∃ a b, Γ.Adj a b := ⟨w₀, u, hu⟩
  have h1 : ArcTrans H Γ 1 := by
    intro P Q
    obtain ⟨h₁, hh₁⟩ := hvt (P.vert 0) (Q.vert 0)
    have ha : Γ.Adj (Q.vert 0) (h₁ • P.vert 1) := by
      have := (hadj h₁ _ _).2 (P.adj 0 (by omega))
      rwa [hh₁] at this
    obtain ⟨h₂, hh₂, hh₂'⟩ := hloc (Q.vert 0) _ _ ha (Q.adj 0 (by omega))
    refine ⟨h₂ * h₁, fun i hi => ?_⟩
    have hh₂0 : h₂ • Q.vert 0 = Q.vert 0 := MulAction.mem_stabilizer_iff.1 hh₂
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [mul_smul, hh₁, hh₂0]
    · rw [mul_smul]
      exact hh₂'
  obtain ⟨K, hK⟩ : ∃ K, 1 ≤ K ∧ ¬ ArcTrans H Γ K := by
    by_contra hcon
    exact not_arcTrans_all hcard hfin hex fun k hk => by
      by_contra hk'
      exact hcon ⟨k, hk, hk'⟩
  classical
  let K₀ := Nat.find (⟨K, hK⟩ : ∃ K, 1 ≤ K ∧ ¬ ArcTrans H Γ K)
  have hK₀ : 1 ≤ K₀ ∧ ¬ ArcTrans H Γ K₀ := Nat.find_spec (⟨K, hK⟩ : ∃ K, 1 ≤ K ∧ ¬ ArcTrans H Γ K)
  have hmin : ∀ j, j < K₀ → ¬ (1 ≤ j ∧ ¬ ArcTrans H Γ j) := fun j hj =>
    Nat.find_min (⟨K, hK⟩ : ∃ K, 1 ≤ K ∧ ¬ ArcTrans H Γ K) hj
  have hK₀ne : K₀ ≠ 1 := fun e => hK₀.2 (e ▸ h1)
  obtain ⟨s, hs⟩ : ∃ s, K₀ = s + 1 := ⟨K₀ - 1, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hts : ArcTrans H Γ s := by
    by_contra hn
    exact hmin s (by omega) ⟨hs1, hn⟩
  have htn : ¬ ArcTrans H Γ (s + 1) := hs ▸ hK₀.2
  have hext := fixesExtensions_of_arcTrans hcard hadj hs1 hts htn
  have htriv : ∀ (P : Arc Γ s) (h : H), (∀ i, i ≤ s → h • P.vert i = P.vert i) →
      ∀ w : W, h • w = w := fun P h hfix w =>
    fixes_all_of_fixesExtensions hconn hdeg hs1 hext P ((Arc.mem_stab H).2 hfix) w
  exact ⟨s, hs1, le_five_of_regular_of_connected hconn hcard hadj hs1 hts htriv, htriv⟩

theorem fixes_of_fixes_fiveArc {W : Type} {Γ : SimpleGraph W} (hconn : Γ.Connected)
    (hdeg : ∀ w, Nat.card (Γ.neighborSet w) = 3)
    {A : Type} [Group A] [MulAction A W]
    (hadj : ∀ (a : A) (u v : W), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v)
    (htrans : ∀ u v : W, ∃ a : A, a • u = v)
    (hfin : ∀ w : W, Finite (MulAction.stabilizer A w))
    (hloc : ∀ w u v : W, Γ.Adj w u → Γ.Adj w v → ∃ a ∈ MulAction.stabilizer A w, a • u = v)
    (P : Arc Γ 5) (a : A) (hP : ∀ i, i ≤ 5 → a • P.vert i = P.vert i) : ∀ w : W, a • w = w := by
  obtain ⟨k, -, hk5, htriv⟩ :=
    exists_singular_of_connected hconn hdeg hadj htrans hfin hloc
  exact htriv ⟨P.vert, fun i hi => P.adj i (by omega), fun i hi => P.nb i (by omega)⟩ a
    fun i hi => hP i (by omega)

end CFSG.Quasithin.Fan86.Tutte
