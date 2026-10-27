module

public import CFSG.Quasithin.Background.FFC5Idx

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace B59

section Generic

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commV_eq_commSub_of_sup {L A : Subgroup (MulAut V)} {W₀ : Subgroup V} (hLW : L ≤ stabSub W₀)
    (hAW : A ≤ stabSub W₀) (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (hLA : ⁅L, A⁆ = L)
    (hsup : commSub W₀ L ⊔ fixV A = ⊤) : commV L = commSub W₀ L := by
  set U := commSub W₀ L with hU
  have hLinv : ∀ l ∈ L, ∀ w ∈ W₀, l w ∈ W₀ := fun l hl w hw => (hLW hl w).2 hw
  have hAinv : ∀ a ∈ A, ∀ w ∈ W₀, a w ∈ W₀ := fun a ha w hw => (hAW ha w).2 hw
  have hUL : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U := commSub_inv_H L W₀
  have hUA : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := by
    exact B1.commSub_invariant_of_normalizes (Y := L) (Bg := A) hAn hAinv
  have hAle : A ≤ B19.commLeSub U := by
    intro a ha v
    obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 (hsup ▸ (Subgroup.mem_top v))
    have : a (u * c) * (u * c)⁻¹ = a u * u⁻¹ := by
      rw [map_mul, hc a ha]; simp [mul_comm]
    rw [this]
    exact U.mul_mem (hUA a ha u hu) (U.inv_mem hu)
  have hLle : L ≤ B19.commLeSub U := by
    rw [← hLA, Subgroup.commutator_le]
    intro l hl a ha
    show ⁅l, a⁆ ∈ B19.commLeSub U
    have h1 : l * a * l⁻¹ ∈ B19.commLeSub U := by
      intro v
      have e : (l * a * l⁻¹) v * v⁻¹ = l (a (l⁻¹ v) * (l⁻¹ v)⁻¹) := by
        simp [MulAut.mul_apply, map_mul, map_inv]
      rw [e]
      exact hUL l hl _ (hAle ha (l⁻¹ v))
    have h2 : a⁻¹ ∈ B19.commLeSub U := (B19.commLeSub U).inv_mem (hAle ha)
    have := (B19.commLeSub U).mul_mem h1 h2
    simpa [commutatorElement_def, mul_assoc] using this
  apply le_antisymm
  · exact B19.commV_le_iff.2 hLle
  · rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl


theorem eq_one_of_sec (hV : ∀ v : V, v ^ 2 = 1) {G : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥)
    {W : Subgroup V} (hWG : ∀ g ∈ G, ∀ w ∈ W, g w ∈ W) {g : MulAut V} (hg : g ∈ G)
    (hgW : ∀ w ∈ W, g w = w) (hgq : ∀ v : V, g v * v⁻¹ ∈ W) : g = 1 := by
  set N : Subgroup (MulAut V) := G ⊓ centSub W ⊓ B19.commLeSub W with hN
  have hNG : N ≤ G := fun x hx => hx.1.1
  have hGN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn'
    refine ⟨⟨G.mul_mem (G.mul_mem hg hn'.1.1) (G.inv_mem hg), fun w hw => ?_⟩, fun v => ?_⟩
    · have hw' : (g⁻¹ : MulAut V) w ∈ W := hWG g⁻¹ (G.inv_mem hg) w hw
      show g (n (g⁻¹ w)) = w
      rw [hn'.1.2 _ hw']
      simp
    · have h1 : (g * n * g⁻¹ : MulAut V) v * v⁻¹ = g (n (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
        simp [MulAut.mul_apply]
      rw [h1]
      exact hWG g hg _ (hn'.2 (g⁻¹ v))
  have hle : N ≤ pCoreOf 2 G :=
    le_pCoreOf_of_trivial_sec hV hNG hGN (fun n hn' x hx => hn'.1.2 x hx) (fun n hn' v => hn'.2 v)
  rw [hO2, le_bot_iff] at hle
  have hmem : g ∈ N := ⟨⟨hg, hgW⟩, hgq⟩
  rw [hle] at hmem
  exact Subgroup.mem_bot.1 hmem

theorem mem_of_eq_on (hV : ∀ v : V, v ^ 2 = 1) {G A L : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥)
    (hLG : L ≤ G) (hAG : A ≤ G) (hn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) {W₀ : Subgroup V}
    (hcomm : commV L ≤ W₀) (hAq : ∀ a ∈ A, ∀ v : V, a v * v⁻¹ ∈ commV L) {a : MulAut V} (ha : a ∈ A)
    {l : MulAut V} (hl : l ∈ L) (heq : ∀ w ∈ W₀, a w = l w) : a ∈ L := by
  have hWG : ∀ g ∈ G, ∀ w ∈ commV L, g w ∈ commV L := fun g hg w hw => commV_invariant (hn g hg) hw
  have hc : l⁻¹ * a = 1 := by
    refine eq_one_of_sec hV hO2 hWG (G.mul_mem (G.inv_mem (hLG hl)) (hAG ha)) ?_ ?_
    · intro w hw
      have : (l⁻¹ * a : MulAut V) w = l⁻¹ (a w) := rfl
      rw [this, heq w (hcomm hw)]
      simp
    · intro v
      have h1 : (l⁻¹ * a : MulAut V) v * v⁻¹ = (l⁻¹ (a v) * (a v)⁻¹) * (a v * v⁻¹) := by
        simp [MulAut.mul_apply]
      rw [h1]
      exact (commV L).mul_mem (Subgroup.subset_closure ⟨l⁻¹, L.inv_mem hl, a v, rfl⟩) (hAq a ha v)
  have : a = l := by
    have h2 := congrArg (fun x => l * x) hc
    simpa using h2
  rw [this]
  exact hl

end Generic

end B59

end FFC

end CFSG.Quasithin
