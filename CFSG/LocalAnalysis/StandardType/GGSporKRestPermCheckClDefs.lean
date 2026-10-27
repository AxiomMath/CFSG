module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestPermCheckKey

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv

@[expose] def specCl {n : ℕ} (a b : Perm (Fin n)) (pOrder : ℕ) (d : Data) : Prop :=
  (tab a b d).length = pOrder ∧ (tab a b d).Nodup ∧ (1 : Perm (Fin n)) ∈ tab a b d ∧
  (∀ t ∈ tab a b d, ∀ g ∈ sg a b d, t * g ∈ tab a b d ∧ t * g⁻¹ ∈ tab a b d) ∧
  (∀ c ∈ d.classes,
    (∀ e ∈ c.ent, e.idx < (tab a b d).length ∧
      (sporKRestEval [a, b] (sporKRestParse e.h))⁻¹ * rep a b c * sporKRestEval [a, b] (sporKRestParse e.h) =
        (tab a b d).getD e.idx 1 ∧
      ∀ zw ∈ e.zs, sporKRestEval [a, b] (sporKRestParse zw) * (tab a b d).getD e.idx 1 =
        (tab a b d).getD e.idx 1 * sporKRestEval [a, b] (sporKRestParse zw)) ∧
    sporKRestEval (letters a b d c) (sporKRestParse c.wa) = a ∧
      sporKRestEval (letters a b d c) (sporKRestParse c.wb) = b)

theorem specCl_of_spec {n : ℕ} {a b : Perm (Fin n)} {pOrder : ℕ} {d : Data}
    (h : spec a b pOrder d) : specCl a b pOrder d :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

@[expose] def checkClMatK {n : ℕ} (B : List ℕ) (a b : Perm (Fin n)) (pOrder : ℕ) (d : Data) : Bool :=
  let a := mat a
  let b := mat b
  let sg := sgMat a b d
  let tab := tabK sg d
  tableOkK B pOrder sg tab && classesOkK B a b d sg tab

end CFSG.StandardType.SporadicShape.PermCover
