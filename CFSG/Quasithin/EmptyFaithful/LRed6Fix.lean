module

public import CFSG.Quasithin.EmptyFaithful.LRed6Real
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin

namespace LRed6

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Explicit

variable {V : Type*} [CommGroup V]

theorem dim4_fix {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) {W : Subgroup V} (hWU : W ≤ U) (hWZ : W ⊓ Z = ⊥)
    [Finite ↥W] [Finite ↥D.sec] (hcard : Nat.card ↥W * Nat.card ↥D.ker = Nat.card ↥D.sec)
    {γ : D.Gam} (hγ : ∀ w ∈ W, ((π γ : ↥H) : MulAut V) w = w) : γ = 1 := by
  obtain ⟨Wm, hWm, -, hcardWm, hfix, -, -⟩ := exists_preimage h hWU hWZ
  have hEq : Wm = D.sec :=
    Subgroup.eq_of_le_of_card_ge hWm (by rw [hcardWm, hcard])
  apply hD
  intro m hm
  exact hfix γ hγ m (hEq ▸ hm)

theorem alt6_fix {L : Subgroup (MulAut V)} {U Z : Subgroup V} (h : AlternatingNatural L U Z 6)
    {W : Subgroup V} [Finite ↥W] (hWU : W ≤ U) (hWZ : W ⊓ Z = ⊥) (hW : Nat.card ↥W = 16)
    {x : MulAut V} (hx : x ∈ L) (hxW : ∀ w ∈ W, x w = w) : x = 1 := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨γ, hγ⟩ := hπ.1 ⟨x, hx⟩
  have hγW : ∀ w ∈ W, ((π γ : ↥L) : MulAut V) w = w := by
    intro w hw
    rw [hγ]
    exact hxW w hw
  have hcard : Nat.card ↥W * Nat.card ↥(FFModel.altDn 6).ker = Nat.card ↥(FFModel.altDn 6).sec := by
    show Nat.card ↥W * Nat.card ↥(Subgroup.zpowers (G6.allOnes 6) ⊓ G6.coreMod 6) =
      Nat.card ↥(G6.coreMod 6)
    rw [card_dnZ (by norm_num), card_coreMod (by norm_num), hW]
    norm_num
  have : Finite ↥(FFModel.altDn 6).sec := inferInstanceAs (Finite ↥(G6.coreMod 6))
  have h1 := dim4_fix (FFC.altDn_faithful (by norm_num)) hπ hWU hWZ hcard hγW
  have h2 : (π γ : ↥L) = 1 := by rw [h1, map_one]
  have h3 : (⟨x, hx⟩ : ↥L) = 1 := by rw [← hγ, h2]
  exact congrArg Subtype.val h3

theorem a7Four_fix {L : Subgroup (MulAut V)} {U Z : Subgroup V} (h : A7Four L U Z)
    {W : Subgroup V} [Finite ↥W] (hWU : W ≤ U) (hWZ : W ⊓ Z = ⊥) (hW : Nat.card ↥W = 16)
    {x : MulAut V} (hx : x ∈ L) (hxW : ∀ w ∈ W, x w = w) : x = 1 := by
  obtain ⟨α, π, hπ⟩ := h
  obtain ⟨γ, hγ⟩ := hπ.1 ⟨x, hx⟩
  have hγW : ∀ w ∈ W, ((π γ : ↥L) : MulAut V) w = w := by
    intro w hw
    rw [hγ]
    exact hxW w hw
  have hcard : Nat.card ↥W * Nat.card ↥(FFModel.a7Four α).ker = Nat.card ↥(FFModel.a7Four α).sec := by
    show Nat.card ↥W * Nat.card ↥(⊥ : Subgroup (Multiplicative (Fin 4 → ZMod 2))) =
      Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2)))
    rw [Subgroup.card_bot, Subgroup.card_top, hW]
    change 16 * 1 = Nat.card (Fin 4 → ZMod 2)
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have : Finite ↥(FFModel.a7Four α).sec :=
    inferInstanceAs (Finite ↥(⊤ : Subgroup (Multiplicative (Fin 4 → ZMod 2))))
  have h1 := dim4_fix (FFC.a7Four_faithful α) hπ hWU hWZ hcard hγW
  have h2 : (π γ : ↥L) = 1 := by rw [h1, map_one]
  have h3 : (⟨x, hx⟩ : ↥L) = 1 := by rw [← hγ, h2]
  exact congrArg Subtype.val h3

end LRed6

end CFSG.Quasithin
