module

public import CFSG.Permutation.FiveTransitive.Degree20SylowFiveMax
public import CFSG.Permutation.FiveTransitive.Degree24SmallSupport

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_maximal_sylow_and_small_prime_element
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    {p : ℕ} (hp : p.Prime)
    (S : Sylow p P)
    (hScard :
      Nat.card S =
        p ^ (Nat.card (Equiv.Perm X)).factorization p)
    (w₀ : Equiv.Perm X) (hw₀order : orderOf w₀ = p)
    (hw₀support : w₀.support.card ≤ 7) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let inclusion : S →* Equiv.Perm X :=
    P.subtype.comp (S : Subgroup P).subtype
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let R : Subgroup (Equiv.Perm X) := inclusion.range
  have hRcard :
      Nat.card R =
        p ^ (Nat.card (Equiv.Perm X)).factorization p := by
    calc
      Nat.card R = Nat.card S :=
        Nat.card_congr
          (MonoidHom.ofInjective hinclusion).toEquiv.symm
      _ = p ^ (Nat.card (Equiv.Perm X)).factorization p :=
        hScard
  let Q : Sylow p (Equiv.Perm X) :=
    Sylow.ofCard R hRcard
  let A : Subgroup (Equiv.Perm X) :=
    Subgroup.zpowers w₀
  have hAcard : Nat.card A = p := by
    rw [Nat.card_zpowers, hw₀order]
  have hAisP : IsPGroup p A := by
    apply IsPGroup.of_card
    rw [hAcard, pow_one]
  obtain ⟨Q₀, hAQ₀⟩ :=
    hAisP.exists_le_sylow
  have hw₀Q₀ :
      w₀ ∈ (Q₀ : Subgroup (Equiv.Perm X)) :=
    hAQ₀ (Subgroup.mem_zpowers w₀)
  obtain ⟨q, hq⟩ :=
    exists_smul_eq (Equiv.Perm X) Q Q₀
  have hqInv : q⁻¹ • Q₀ = Q :=
    inv_smul_eq_iff.mpr hq.symm
  let w : Equiv.Perm X :=
    MulAut.conj q⁻¹ w₀
  have hwConjugate :
      w ∈ (q⁻¹ • Q₀ :
        Sylow p (Equiv.Perm X)) := by
    change ∃ x ∈
      (Q₀ : Subgroup (Equiv.Perm X)),
        MulAut.conj q⁻¹ x = w
    exact ⟨w₀, hw₀Q₀, rfl⟩
  have hwQ :
      w ∈ (Q : Subgroup (Equiv.Perm X)) := by
    rwa [hqInv] at hwConjugate
  have hwRange : w ∈ R := by
    exact hwQ
  obtain ⟨v, hv⟩ := hwRange
  have hwMem : w ∈ P := by
    rw [← hv]
    exact ((S : Subgroup P).subtype v).prop
  have hwSupport :
      w.support.card = w₀.support.card := by
    change
      (q⁻¹ * w₀ * (q⁻¹)⁻¹).support.card =
        w₀.support.card
    rw [Equiv.Perm.card_support_conj]
  have hwSupportLe : w.support.card ≤ 7 := by
    rwa [hwSupport]
  have hwNe : w ≠ 1 := by
    intro hw
    have hw₀ne : w₀ ≠ 1 := by
      intro hw₀
      rw [hw₀, orderOf_one] at hw₀order
      exact hp.ne_one hw₀order.symm
    apply hw₀ne
    change q⁻¹ * w₀ * q = 1 at hw
    have h :=
      congrArg (fun z : Equiv.Perm X => q * z * q⁻¹) hw
    simpa [mul_assoc] using h
  exact alternatingGroup_le_of_nontrivial_support_le_seven
    X P hcard h5 hwMem hwNe hwSupportLe

theorem alternatingGroup_le_of_maximal_sylow_three
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 3 P)
    (hScard :
      Nat.card S =
        3 ^ (Nat.card (Equiv.Perm X)).factorization 3) :
    alternatingGroup X ≤ P := by
  classical
  let e : X ≃ Fin 24 :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin]
      exact hcard)
  let w₀ : Equiv.Perm X :=
    e.symm.permCongr
      (Fin.cycleRange 2 : Equiv.Perm (Fin 24))
  have hw₀support : w₀.support.card = 3 := by
    change
      (e.symm.permCongr
        (Fin.cycleRange 2 :
          Equiv.Perm (Fin 24))).support.card = 3
    rw [Degree20.card_support_permCongr,
      Fin.isThreeCycle_cycleRange_two.card_support]
  have hw₀three : w₀.IsThreeCycle :=
    card_support_eq_three_iff.mp hw₀support
  exact
    alternatingGroup_le_of_maximal_sylow_and_small_prime_element
      X P hcard h5 (p := 3) (by norm_num) S hScard
        w₀ hw₀three.orderOf (by omega)

theorem alternatingGroup_le_of_maximal_sylow_two
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 2 P)
    (hScard :
      Nat.card S =
        2 ^ (Nat.card (Equiv.Perm X)).factorization 2) :
    alternatingGroup X ≤ P := by
  classical
  let e : X ≃ Fin 24 :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin]
      exact hcard)
  let w₀ : Equiv.Perm X :=
    e.symm.permCongr
      (Equiv.swap (0 : Fin 24) 1)
  have hw₀support : w₀.support.card = 2 := by
    change
      (e.symm.permCongr
        (Equiv.swap (0 : Fin 24) 1)).support.card = 2
    rw [Degree20.card_support_permCongr,
      Equiv.Perm.card_support_swap (by decide)]
  have hw₀swap : w₀.IsSwap :=
    Equiv.Perm.card_support_eq_two.mp hw₀support
  exact
    alternatingGroup_le_of_maximal_sylow_and_small_prime_element
      X P hcard h5 (p := 2) (by norm_num) S hScard
        w₀ hw₀swap.orderOf (by omega)

end FiveTransitive.Degree24

end CFSG
