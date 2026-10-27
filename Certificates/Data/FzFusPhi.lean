module

public import Certificates.Data.FzJ36

public section

namespace Certificates.FzFus

open Certificates.FzJ36

abbrev Z2 : Type := Multiplicative (ZMod 2)

@[expose] def chiVal (n : Fin 4) (q : Q8) : ZMod 2 :=
  match n.val, q with
  | 1, QuaternionGroup.a _ => 0
  | 1, QuaternionGroup.xa _ => 1
  | 2, QuaternionGroup.a i => ((i.val % 2 : Nat) : ZMod 2)
  | 2, QuaternionGroup.xa i => ((i.val % 2 : Nat) : ZMod 2)
  | 3, QuaternionGroup.a i => ((i.val % 2 : Nat) : ZMod 2)
  | 3, QuaternionGroup.xa i => (((i.val + 1) % 2 : Nat) : ZMod 2)
  | _, _ => 0

@[expose] def chi (n : Fin 4) : Q8 →* Z2 :=
  MonoidHom.mk' (fun q => Multiplicative.ofAdd (chiVal n q)) (by revert n; decide)

@[expose] def phiN (u v : Fin 4) : N3 →* Z2 :=
  MonoidHom.mk' (fun n => chi u n.1 * chi u n.2.1 * chi v n.2.2) (by
    intro a b
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    ac_rfl)

@[expose] def phi (u v : Fin 4) : Model →* Z2 :=
  SemidirectProduct.lift (phiN u v) 1 (by
    intro g
    ext n
    have hg : ∀ g : Multiplicative (ZMod 2), g = 1 ∨ g = Multiplicative.ofAdd 1 := by decide
    rcases hg g with rfl | rfl
    · simp [act]
    · have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
      simp [act, hne, swapAut, phiN, mul_comm])

theorem phi_mk (u v : Fin 4) (a b c : Q8) (e : Multiplicative (ZMod 2)) :
    phi u v ⟨(a, b, c), e⟩ = chi u a * chi u b * chi v c := by
  simp [phi, phiN]

end Certificates.FzFus
