module

public import CFSG.LocalAnalysis.StandardType.GGQ2SubStab
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBigHeart
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBigIrr
import CFSG.LocalAnalysis.StandardType.GGQ2TwoNodeBigRed
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggQ2TN_big_false (hK : GGReflClassOmegaLarge) [Module.Finite (ZMod 3) V]
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hTF : TransvectionFree A) {m : ℕ} (hm : 11 ≤ m)
    (h3 : 3 ∣ m + 1) (hdim : Module.finrank (ZMod 3) V = m)
    (c : Fin m → V) (α : Fin m → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A m i j : ZMod 3))
    (s : Fin m → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i) (hsA : ∀ i, s i ∈ A)
    (x : V) (hxH : x ∉ Submodule.span (ZMod 3) (Set.range c)) (hxfix : ∀ i, α i x = 0)
    (hRx : ¬ ∀ r ∈ reflGp A, r x ∈ Submodule.span (ZMod 3) {x})
    (hStab : ∀ g ∈ A, g x = x → ∃ w ∈ Subgroup.closure (Set.range s), ∃ ε : ZMod 3,
      ∀ h ∈ Submodule.span (ZMod 3) (Set.range c), g h = ε • w h) :
    False := by
  obtain ⟨hH, hsup, hker, hfix⟩ := ggQ2TN_heart hdim c α hpair x hxH hxfix
  have hconn := ggQ2TN_conn c α hpair
  have hcardW : Nat.card (Subgroup.closure (Set.range s)) = (m + 1).factorial :=
    l04fD5_P_card (p := 3) (by decide) (by omega) hpair s hs
  have hcard := ggQ2TN_card_le hdim A c s x hsup hcardW hStab
  by_cases hHR : ∀ r ∈ reflGp A, ∀ h ∈ Submodule.span (ZMod 3) (Set.range c),
      r h ∈ Submodule.span (ZMod 3) (Set.range c)
  · exact ggQ2TN_caseII hK A hTF hm h3 c α hpair s hs hsA x hxfix hfix hker hconn hH hRx hcard
      hHR
  · exact ggQ2TN_caseI hK A hm h3 hdim c α hpair s hs hsA x hfix hconn hH hRx hcard hHR

end CFSG.StandardType

end
