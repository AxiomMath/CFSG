module

public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveMats

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

theorem e8F5_transport_6 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 6 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 6 [])
    (Equiv.ofBijective (fun k => (![1, 3, 0, 4, 2] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_7 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 7 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 7 [])
    (Equiv.ofBijective (fun k => (![3, 0, 1, 4, 2] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_8 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 8 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 8 [])
    (Equiv.ofBijective (fun k => (![2, 0, 3, 4, 1] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_9 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 9 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 9 [])
    (Equiv.ofBijective (fun k => (![3, 0, 1, 4, 2] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_10 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 10 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 10 [])
    (Equiv.ofBijective (fun k => (![2, 0, 3, 4, 1] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_11 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 11 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 11 [])
    (Equiv.ofBijective (fun k => (![3, 0, 1, 4, 2] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

end CFSG.RankThree.Lattice
