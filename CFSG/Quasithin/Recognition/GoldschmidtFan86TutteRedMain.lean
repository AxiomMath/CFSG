module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteRedKey
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteDefs

public section

namespace CFSG.Quasithin.Fan86.Tutte

open CFSG.Quasithin.F6.GoldAmL3T Red

theorem tutteTree_of_regular (hR : TutteRegular) : TutteTree := by
  intro W Γ hΓ hcard H _ _ hadj hvt hfin hloc
  have hconn : Γ.Connected := hΓ.connected
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
  exact ⟨s, hs1, hR W Γ hΓ hcard H hadj s hs1 hts htriv, htriv⟩

end CFSG.Quasithin.Fan86.Tutte
