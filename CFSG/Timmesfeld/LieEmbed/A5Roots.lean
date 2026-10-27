module

public import CFSG.LieType.Universal.Unitary.Roots
public import CFSG.Timmesfeld.LieEmbed.C3Roots
public import CFSG.LieType.Steinberg.TwistedE6.Roots

public section

namespace CFSG.Timmesfeld.LieEmbed

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg.TwistedE6

@[expose] def a5Pos (m : Fin (Tag.rank .E6)) : ℕ := (![0, 0, 1, 2, 3, 4] : Fin 6 → ℕ) m

@[expose] def a5Root (i j : Fin 6) : Fin (Tag.rank .E6) → ℤ := fun m =>
  if m.val = 1 then 0 else
    (if i.val ≤ a5Pos m ∧ a5Pos m < j.val then 1 else 0) -
      (if j.val ≤ a5Pos m ∧ a5Pos m < i.val then 1 else 0)

set_option maxRecDepth 100000 in
theorem a5Root_check : ∀ i j : Fin 6, i ≠ j → a5Root i j ∈ rootFinset .E6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a5Root_add_check : ∀ i j l : Fin 6, a5Root i j + a5Root j l = a5Root i l := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a5Root_add_ne_zero_check : ∀ i j k l : Fin 6,
    (i ≠ j ∧ k ≠ l ∧ ¬ (k = j ∧ l = i)) → a5Root i j + a5Root k l ≠ 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem not_isRoot_a5Root_add_check : ∀ i j k l : Fin 6,
    (i ≠ j ∧ k ≠ l ∧ ¬ (k = j ∧ l = i) ∧ j ≠ k ∧ i ≠ l) →
      ¬ (a5Root i j + a5Root k l ∈ rootFinset .E6) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rho_a5Root_check : ∀ i j : Fin 6, rho (a5Root i j) = a5Root (Fin.rev j) (Fin.rev i) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem a5Root_ne_check : ∀ i j : Fin 6, i ≠ j → j ≠ Fin.rev i →
    a5Root (Fin.rev j) (Fin.rev i) ≠ a5Root i j := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem proj_a5Root_check : ∀ i j : Fin 6, i ≠ j → j ≠ Fin.rev i → ∃ γ ∈ c3Roots,
    Universal.Unitary.toStd 6 γ = Universal.Unitary.weight 6 i - Universal.Unitary.weight 6 j ∧
      proj (a5Root i j) = c3ToF4 γ := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem proj_a5Root_rev_check : ∀ i : Fin 6, ∃ γ ∈ c3Roots,
    Universal.Unitary.toStd 6 γ = 2 • Universal.Unitary.weight 6 i ∧
      proj (a5Root i (Fin.rev i)) = c3ToF4 γ := by
  decide +kernel

theorem isRoot_a5Root {i j : Fin 6} (h : i ≠ j) : IsRoot .E6 (a5Root i j) :=
  mem_rootFinset.1 (a5Root_check i j h)

theorem a5Root_add (i j l : Fin 6) : a5Root i j + a5Root j l = a5Root i l :=
  a5Root_add_check i j l

theorem a5Root_add_ne_zero {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) : a5Root i j + a5Root k l ≠ 0 :=
  a5Root_add_ne_zero_check i j k l ⟨hij, hkl, hex⟩

theorem not_isRoot_a5Root_add {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l)
    (hex : ¬ (k = j ∧ l = i)) (hjk : j ≠ k) (hil : i ≠ l) :
    ¬ IsRoot .E6 (a5Root i j + a5Root k l) := fun h =>
  not_isRoot_a5Root_add_check i j k l ⟨hij, hkl, hex, hjk, hil⟩ (mem_rootFinset.2 h)

theorem rho_a5Root (i j : Fin 6) : rho (a5Root i j) = a5Root (Fin.rev j) (Fin.rev i) :=
  rho_a5Root_check i j

theorem rho_a5Root_ne {i j : Fin 6} (hij : i ≠ j) (hji : j ≠ Fin.rev i) :
    rho (a5Root i j) ≠ a5Root i j := by
  rw [rho_a5Root]
  exact a5Root_ne_check i j hij hji

theorem rho_a5Root_rev (i : Fin 6) : rho (a5Root i (Fin.rev i)) = a5Root i (Fin.rev i) := by
  rw [rho_a5Root, Fin.rev_rev]

theorem toStd_six_inj : Function.Injective (Universal.Unitary.toStd 6) := by
  intro v w h
  have e : ∀ u, Universal.Unitary.toStd 6 u = Universal.Symplectic.toStd 3 u := fun u => by
    rw [Universal.Unitary.toStd, ite_eq_left (by decide)]
  rw [e, e] at h
  exact Universal.Symplectic.SpExtras.toStd_inj h

theorem proj_a5Root {i j : Fin 6} (hij : i ≠ j) (hji : j ≠ Fin.rev i) {γ : Fin 3 → ℤ}
    (hγ : Universal.Unitary.toStd 6 γ =
      Universal.Unitary.weight 6 i - Universal.Unitary.weight 6 j) :
    proj (a5Root i j) = c3ToF4 γ := by
  obtain ⟨γ', -, h1, h2⟩ := proj_a5Root_check i j hij hji
  rw [h2, toStd_six_inj (h1.trans hγ.symm)]

theorem proj_a5Root_rev (i : Fin 6) {γ : Fin 3 → ℤ}
    (hγ : Universal.Unitary.toStd 6 γ = 2 • Universal.Unitary.weight 6 i) :
    proj (a5Root i (Fin.rev i)) = c3ToF4 γ := by
  obtain ⟨γ', -, h1, h2⟩ := proj_a5Root_rev_check i
  rw [h2, toStd_six_inj (h1.trans hγ.symm)]

end CFSG.Timmesfeld.LieEmbed
