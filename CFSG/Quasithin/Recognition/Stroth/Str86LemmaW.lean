module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbBase
public import CFSG.Quasithin.Recognition.Stroth.Str86AbOdd

import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWElts
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWChief
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWNat
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWPrime
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWL2
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWCent
import CFSG.Quasithin.Recognition.Stroth.Str86LemmaWFix

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commute_z2_of_fixedPointFree
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {L N : Subgroup G}
    (hstep : IsChiefStep (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1) L N)
    (hL : ⁅L, oTwoUpper (L1 ⊔ S)⁆ = ⊥)
    (hN : ⁅conjClosure (Z2 L1 L2 S) L1, oTwoUpper (L1 ⊔ S)⁆ ≤ N)
    {w h : G} (hfpf : ∀ x ∈ N, w * x * w⁻¹ * x⁻¹ ∈ L → x ∈ L)
    (hhH : h ∈ L1 ⊔ S) (hhodd : Odd (orderOf h)) (hhw : Commute h w)
    (hwC : w ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G)) :
    ∀ v ∈ Z2 L1 L2 S, Commute h v := by
  intro v hv
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hI.hF.toW)
  obtain ⟨hVQ1, -, hP1NZ⟩ := str86_conjClosure_frame hI hZQ
  have hV : IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1) :=
    hI.hF.1.h1.pgroup.to_le (hVQ1.trans hQ1S)
  have hZV : Z2 L1 L2 S ≤ conjClosure (Z2 L1 L2 S) L1 := by
    have h := hP1NZ 1 ((P1 L1 L2 S).one_mem)
    exact fun z hz => h (by simpa using hz)
  have hvw : Commute v w := (Subgroup.mem_centralizer_iff.mp hwC v hv)
  exact commute_of_commute_of_fixedPointFree hV hstep.2.2.1.le hstep.1.1 hL hN
    hfpf hhH hhodd hhw (hZV hv) hvw

private theorem conj_smul_eq_of_commute {Z : Subgroup G} {h : G}
    (hcomm : ∀ v ∈ Z, Commute h v) : MulAut.conj h • Z = Z := by
  ext v
  rw [mem_conj_smul_iff']
  constructor
  · intro hv
    have hc := hcomm (h⁻¹ * v * h) hv
    have h1 : h * (h⁻¹ * v * h) = (h⁻¹ * v * h) * h := hc.eq
    have h2 : v = h⁻¹ * v * h := by
      calc v = h * (h⁻¹ * v * h) * h⁻¹ := by group
        _ = ((h⁻¹ * v * h) * h) * h⁻¹ := by rw [h1]
        _ = h⁻¹ * v * h := by group
    rwa [h2]
  · intro hv
    have hc := hcomm v hv
    have h1 : v * h = h * v := hc.eq.symm
    have h2 : h⁻¹ * v * h = v := by
      calc h⁻¹ * v * h = h⁻¹ * (v * h) := by group
        _ = h⁻¹ * (h * v) := by rw [h1]
        _ = v := by group
    rwa [h2]

private theorem exists_primePow_and_d {k m : ℕ} (hk : 2 ≤ k) (hm : 0 < m) (hmk : m < 2 * k) :
    ∃ p a d : ℕ, p.Prime ∧ p ≠ 2 ∧ p ^ a ∣ 2 ^ k + 1 ∧ d < p ^ a ∧
      d = Nat.gcd (p ^ a) m * Nat.gcd (p ^ a) (2 ^ m - 1) ∧ ¬ p ^ a ∣ d := by
  obtain ⟨p, a, hp, hp2, hpa, hlt⟩ := exists_lemmaW_primePow hk hm hmk
  let d : ℕ := Nat.gcd (p ^ a) m * Nat.gcd (p ^ a) (2 ^ m - 1)
  have hlt' : d < p ^ a := hlt
  have hdpos : 0 < d := by
    show 0 < Nat.gcd (p ^ a) m * Nat.gcd (p ^ a) (2 ^ m - 1)
    exact Nat.mul_pos (Nat.gcd_pos_of_pos_right (p ^ a) hm)
      (Nat.gcd_pos_of_pos_left (2 ^ m - 1) (pow_pos hp.pos a))
  refine ⟨p, a, d, hp, hp2, hpa, hlt', rfl, ?_⟩
  intro h
  have := Nat.le_of_dvd hdpos h
  omega

theorem str86_two_mul_le_of_involution
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {t : G}
    (htP : t ∈ P1 L1 L2 S) (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (conjClosure (Z2 L1 L2 S) L1) ≤ (2 ^ k) ^ 3) :
    2 * k ≤ m := by
  classical
  by_contra hle
  have hm : 0 < m := by have := hI.hm; omega
  have hmk : m < 2 * k := by omega
  obtain ⟨p, a, d, hp, hp2, hpa, hlt, hddef, hd⟩ := exists_primePow_and_d hI.hk hm hmk
  obtain ⟨L, N, hstep, hnc, hL, hN⟩ :=
    hI.exists_unique_noncentral_chiefStep hZQ htP htQ ht2 hdisp
  obtain ⟨hE, hnat⟩ := hI.chiefFactor_natural hZQ hstep hnc htP htQ ht2 hdisp
  have hUH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S := by
    obtain ⟨hVQ1, -, -⟩ := str86_conjClosure_frame hI hZQ
    have hQ1S : Q1 L1 L2 S ≤ S :=
      CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hI.hF.toW)
    exact hVQ1.trans (hQ1S.trans le_sup_right)
  obtain ⟨ω, h, hωL, hωB, hωp, hfpf, hhH, hhodd, hhcomm, hhB⟩ :=
    hI.exists_lemmaW_elements hUH hstep hE hnat hp hp2 hpa hd
  have hoddpa : Odd (p ^ a) := (hp.odd_of_ne_two hp2).pow
  have htriv : ∀ x ∈ u3H L1 L2 S,
      ω ^ d * x * (ω ^ d)⁻¹ * x⁻¹ ∈ Q2 L1 L2 S := by
    intro x hx
    have h := hI.commutator_mem_q2_of_pow_eq_one hωB hoddpa hωp x hx
    simpa [hddef] using h
  have hωdodd : Odd (orderOf (ω ^ d)) := by
    have hord : orderOf ω ∣ p ^ a := orderOf_dvd_of_pow_eq_one hωp
    exact Odd.of_dvd_nat (Odd.of_dvd_nat hoddpa hord) (orderOf_pow_dvd d)
  have hωdL : ω ^ d ∈ L1 ⊔ S := (L1 ⊔ S).pow_mem hωL d
  have hωdB : ω ^ d ∈ bigB L1 L2 S := (bigB L1 L2 S).pow_mem hωB d
  have hC : ω ^ d ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    hI.mem_centralizer_z2_of_odd hωdL hωdB hωdodd htriv
  have hcommZ : ∀ v ∈ Z2 L1 L2 S, Commute h v :=
    commute_z2_of_fixedPointFree hI hZQ hstep hL hN hfpf hhH hhodd hhcomm hC
  have hconj : MulAut.conj h • Z2 L1 L2 S = Z2 L1 L2 S :=
    conj_smul_eq_of_commute hcommZ
  have hHP1 : L1 ⊔ S ≤ P1 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hhP1 : h ∈ P1 L1 L2 S := hHP1 hhH
  exact (str86_conj_z2_ne hI hhP1 hhB) hconj

theorem str86LemmaW_holds :
    Str86LemmaW :=
  fun _ _ _ _ _ _ _ _ _ _ _ hI hZQ _ htP htQ ht2 hdisp =>
    str86_two_mul_le_of_involution hI hZQ htP htQ ht2 hdisp

end CFSG.Quasithin.Stroth

end
