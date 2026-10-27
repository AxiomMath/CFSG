module

public import CFSG.Monster.B.Final.PairNodes
public import CFSG.Monster.B.CTIB.Defs
public import CFSG.Monster.Existence.BabyOrder
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import Certificates.Certificate3027

public section

namespace CFSG.Monster.B

open Matrix MulOpposite CFSG.Blueprint CFSG.Monster

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem pinned_B_explicit_embedding_perfectness_and_order_divisor :
    ∃ ι : NativeSporadic.B →* Sbp, Function.Injective ι ∧
      (∀ X, ((betaRow Dyadic.betaS (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
      ι.range = HB ∧ ι bA₁ = aB ∧ ι bA₂ = bB ∧
      Nontrivial NativeSporadic.B ∧ commutator NativeSporadic.B = ⊤ ∧
      Nat.card NativeSporadic.B ∣ 4154781481226426191177580544000000 ∧
      2 * 3 * 5 * 11 * 23 ∣ Nat.card NativeSporadic.B := by
  obtain ⟨ι, hι, hιβ, hr, h1, h2, hn, hc, hd⟩ := pinned_B_explicit_embedding CTIB.betaS_explicit
  refine ⟨ι, hι, hιβ, hr, h1, h2, hn, hc, ?_, hd⟩
  rw [CFSG.Monster.Existence.card_nativeB]
  exact dvd_refl _

theorem pinned_B_explicit_native_isomorphism_simplicity_and_order :
    HB = ⊤ ∧
      (∃ e : NativeSporadic.B ≃* Sbp,
        (∀ X, ((betaRow Dyadic.betaS (e X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) ∧
        e bA₁ = aB ∧ e bA₂ = bB) ∧
      Nontrivial NativeSporadic.B ∧ IsSimpleGroup NativeSporadic.B ∧
      Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
  obtain ⟨hH, e, he, h1, h2, hs⟩ := pinned_B_explicit_native_isomorphism CTIB.betaS_explicit
  refine ⟨hH, ⟨e, he, h1, h2⟩, hs.toNontrivial, hs, ?_⟩
  rw [CFSG.Monster.Existence.card_nativeB]
  rfl

end CFSG.Monster.B
