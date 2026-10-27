module

public import CFSG.RankThree.Lattice.SteinbergBIE8OrderFiveMats

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

theorem e8F5_transport_0 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 0 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 0 [])
    (Equiv.ofBijective (fun k => (![2, 0, 3, 4, 1] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_1 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 1 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 1 [])
    (Equiv.ofBijective (fun k => (![1, 3, 0, 4, 2] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_2 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 2 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 2 [])
    (Equiv.ofBijective (fun k => (![2, 0, 4, 1, 3] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_3 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 3 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 3 [])
    (Equiv.ofBijective (fun k => (![1, 4, 0, 2, 3] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_4 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 4 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 4 [])
    (Equiv.ofBijective (fun k => (![1, 3, 0, 4, 2] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

theorem e8F5_transport_5 :
    ∃ a : WeylGroup Tag.E8, (a • ·) '' e8F5ClassSet 5 = parabolicRoots Tag.E8 e8F5J ∧
      (∃ π : Equiv.Perm (Fin 5), orderOf π = 5 ∧ ∀ k l,
        (a * e8F5U * a⁻¹) • chainRoot e8F5Chain k l = chainRoot e8F5Chain (π k) (π l)) ∧
      IsNegativeTransition (fun x => (a * e8F5C ^ 21 * a⁻¹) • x) e8F5Chain e8F5Chain :=
  e8F5_transport_of_checks (by norm_num) (e8F5Words.getD 5 [])
    (Equiv.ofBijective (fun k => (![1, 3, 0, 4, 2] : Fin 5 → Fin 5) k) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide)

end CFSG.RankThree.Lattice
