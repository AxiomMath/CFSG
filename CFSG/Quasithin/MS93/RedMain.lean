module

public import CFSG.Quasithin.MS93.SkItems
public import CFSG.Quasithin.MS93.RedCrit
public import CFSG.Quasithin.MS93.RedIrr

public section

namespace CFSG.Quasithin.MS93

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem puReduce_holds : PUReduce := by
  intro G _ _ M T L T₁ h hT₁ hc hO hne
  exact ⟨h.reduce hT₁ hc hO hne, h.vq_reduce hT₁ hc hO hne⟩

theorem s7two_of (h32 : S32) (h36 : S36) (h18 : S18) : S7Two := by
  intro G _ _ M T L M₁ T₁ h h₁ _ _ hV hb hb₁
  rw [← hV]
  obtain ⟨h36a, -⟩ := h36 G M₁ T₁ L h₁ hb₁
  by_cases hVU : Vq M₁ L = Uq M₁ T₁ L
  swap
  · exact h18 G M₁ T₁ L h₁ hb₁ hVU (h36a.resolve_left hVU)
  have key : ∀ C : Subgroup G, C ≤ Uq M₁ T₁ L → C ≤ Subgroup.centralizer (L : Set G) →
      (∀ W : Subgroup G, C ≤ W → W ≤ Uq M₁ T₁ L → L ≤ Subgroup.normalizer (W : Set G) →
        ⁅W, L⁆ ⊔ C = W → W = C ∨ W = Uq M₁ T₁ L) → False := by
    intro C hCU hCL hirr
    refine h.false_of_two_lt_critDist hb (C := C) ?_ hCL fun W hCW hWV hLW hW => ?_
    · rw [← hV, hVU]
      exact hCU
    · rw [← hV, hVU] at hWV ⊢
      exact hirr W hCW hWV hLW hW
  have hLU : L ≤ Subgroup.normalizer (Uq M₁ T₁ L : Set G) :=
    h₁.L_le.trans (le_normalizer_Uq h₁.le_normalizer)
  have hCL : Uq M₁ T₁ L ⊓ Zq M₁ L ≤ Subgroup.centralizer (L : Set G) :=
    inf_le_right.trans inf_le_right
  obtain ⟨-, -, h32c⟩ := h32 G M₁ T₁ L h₁
  rcases h32c with ⟨-, -, n, F, _, _, α, -, hα, hn⟩ | ⟨-, -, hU, h6⟩ |
      ⟨-, -, n, F, _, _, α, hF, hα, hn⟩ | ⟨-, -, ⟨α, -, hn⟩, -⟩ | ⟨-, -, -, α, hα, hn⟩ |
      ⟨k, ⟨-, N, hN⟩ | ⟨-, F, _, _, α, -, hα, hn⟩⟩ | ⟨-, -, ⟨hU, hG2⟩, -⟩
  ·
    exact (key ⊥ bot_le bot_le fun W hCW hWU hLW _ =>
      eq_or_eq_of_natural hα statedSL3_transitive hn hCW hWU hLW).elim
  ·
    exact (key ⊥ bot_le bot_le fun W _ hWU hLW _ =>
      eq_bot_or_eq_of_tripleA6Six hU hLU h₁.perfect h6 hWU hLW).elim
  ·
    rw [hVU]
    exact ⟨n, F, inferInstance, inferInstance, α, hF, hα, hn⟩
  ·
    exact (key _ inf_le_left hCL fun W hCW hWU hLW hW =>
      eq_or_eq_of_relIndex_eight hCW hWU hLU hLW
        ((Subgroup.le_centralizer_iff.mp hCL).trans (Subgroup.centralizer_le_normalizer _))
        h₁.commutator_uq hW (relIndex_eq_eight_of_natural_sl3_two hn)).elim
  ·
    exact (key ⊥ bot_le bot_le fun W hCW hWU hLW _ =>
      eq_or_eq_of_natural hα statedSL3_transitive hn hCW hWU hLW).elim
  ·
    exact (key _ inf_le_left hCL fun W hCW hWU hLW _ =>
      eq_or_eq_of_altNaturalSection_six hN hCW hWU hLW).elim
  ·
    exact (key _ inf_le_left hCL fun W hCW hWU hLW _ =>
      eq_or_eq_of_natural hα statedSp2_transitive hn hCW hWU hLW).elim
  ·
    exact (key _ inf_le_left hCL fun W hCW hWU hLW _ =>
      eq_or_eq_of_g2NaturalDerived hU (fun _ => Iff.rfl) hG2 hCW hWU hLW).elim

end CFSG.Quasithin.MS93
