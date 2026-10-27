module

public import CFSG.Quasithin.H13.L32NLem14324b
public import CFSG.Quasithin.H13.L32NLem14324c
public import CFSG.Quasithin.H13.L32NLem14324d
public import CFSG.Quasithin.H13.L32NLem14324e
public import CFSG.Quasithin.Background.G10Three

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14324

theorem cases_of_inputs
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12813 : Lemma12_8_13)
    (h14312 : Lemma14312One) (hFixS : G11.SzG11S.TheoremG112FixS)
    (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (h : Hyp14310One G T L V)
    (hlt : fsuV1 T V < centerOf (fsuU T V)) (V₂ : Subgroup G) (g : G)
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V)
    (D : HatModelU (fsuU T V)) (hd : 6 ≤ Module.finrank (ZMod 2) D.V) :
    G112Concl6 (D.img (l32nH T V)) ∨ G112Concl5 D.B (D.img (l32nH T V)) ∨
      G11.SzG11S.G112Concl7S (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g)) ∨
      G11.G112Concl8S8 D.B (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g)) ∨
      G11.SzG11S.G112Concl13S (D.img (l32nH T V)) := by
  obtain ⟨a, H, hconc, hX, -⟩ :=
    data_of h1332 h1334 h1222 h12213 h12813 h14312 hFixS h hlt hV₂ hgP hgN D
  set X := D.img (CFSG.conjugate (l32nW T V V₂) g) with hXdef
  set Γ := D.img (l32nH T V) with hΓdef
  obtain ⟨k, hk₀⟩ := H.toG101Hyp.exists_card_X
  have hk : Nat.card X = 2 ^ k := hk₀
  have hXΓ : X ≤ Γ := H.X_le
  have hsq : ∀ x ∈ X, x * x = 1 := H.X_sq
  have hXel : IsElemAbelian 2 X := H.toG101Hyp.X_isElemAbelian
  have hO2 : pCoreOf 2 Γ = ⊥ := H.toG101Hyp.g10_3_pCoreOf_eq_bot
  have h8 : 8 ≤ Nat.card X := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 3 ≤ Module.finrank (ZMod 2) D.V / 2
      by omega)
    omega
  rcases hconc with ((h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8' | h9 | h10 | h11 | h12 | h13) |
    h8S | h6U)
  · exact absurd h1.1 (by omega)
  · exact absurd h2.1 (by omega)
  · have := card_le_four_of_concl3 hXΓ hXel hk hO2 h3
    omega
  · have := card_le_four_of_concl4 H h4
    omega
  · exact Or.inr (Or.inl h5)
  · exact Or.inl h6
  · exact Or.inr (Or.inr (Or.inl h7))
  · have hd8 := h8'.1
    have h16 : 16 ≤ Nat.card X := by
      rw [hd8] at hX
      simpa using hX
    exact (false_of_concl8 hXΓ hsq hk h16 h8').elim
  · have h16 : 16 ≤ Nat.card X := by
      rw [h9.1] at hX
      simpa using hX
    exact (false_of_concl9 hXΓ hsq hk h16 h9).elim
  · have h16 : 16 ≤ Nat.card X := by
      rw [h10.1] at hX
      simpa using hX
    exact (false_of_concl10 hXΓ hsq hk h16 h10).elim
  · have h16 : 16 ≤ Nat.card X := by
      rw [h11.1] at hX
      simpa using hX
    have := lt_of_concl11 hXΓ hk h11
    omega
  · have h16 : 16 ≤ Nat.card X := by
      rw [h12.1] at hX
      simpa using hX
    have := card_X_of_concl12 h12
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr h13)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h8S)))
  · have := lt_of_concl6U33 hXΓ hXel hk h6U.2
    omega

end L14324

end CFSG.Quasithin.H13
