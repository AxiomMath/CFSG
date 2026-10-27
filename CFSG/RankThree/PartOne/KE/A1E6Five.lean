module

public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.PartOne.KE.NativeSolvCyclicE
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFive
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1Untwisted

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)
open scoped Matrix Polynomial

namespace CTE6

theorem e6Five_data {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 4 + (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + (q : ℤ) + 1) :
    7 < p ∧ ¬ p ∣ q ∧ orderOf (q : ZMod p) = 5 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 + (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 4 + (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + (q : ℤ)
      + 1) p).2 h
    simpa using this
  have hq0 : ¬ p ∣ q := by
    intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    simp at hx
  have hq1 : (q : ZMod p) ≠ 1 := by
    intro h1
    rw [h1] at hx
    have h5 : ((5 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hx
    exact natCast_ne_zero_of_lt (by norm_num) hp5 h5
  obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
  rw [← hxdef] at hx hq1
  have h5 : x ^ 5 = 1 := by linear_combination (x - 1) * hx
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf x = 5 := orderOf_eq_prime h5 hq1
  rw [← hxdef]
  refine ⟨?_, hq0, hord⟩
  have hx0 : x ≠ 0 := fun h0 => by rw [h0] at h5; simp at h5
  have hdvd := ZMod.orderOf_dvd_card_sub_one hx0
  rw [hord] at hdvd
  by_contra hle
  have hp7 : p ≤ 7 := not_lt.1 hle
  interval_cases p <;> first | omega | (exfalso; revert hp; decide)

end CTE6

open Polynomial in
@[expose] def e6FiveBlock : A1BlockData .E6 e6O5W e6O5Theta where
  c := e6O5Cols
  β := e6O5Beta
  P := X ^ 5 - C 1
  hk := by decide
  hlin := E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.1.1
  hspan := E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.1.2
  hc0 := by simp [e6O5Cols]
  hβ := fun j hj => by
    have h : (j : ℕ) ≠ 0 := by omega
    simp [e6O5Cols, h]
  hθM := ⟨1, by rw [E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.1, one_smul]⟩
  hP := Polynomial.monic_X_pow_sub_C 1 (by norm_num)
  hPdeg := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    rfl
  hrel := by
    have h5 : e6O5W ^ 5 = 1 := by
      rw [← E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.1]
      exact pow_orderOf_eq_one _
    simp [h5]
  hdet := Or.inr (by simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow])

theorem E6_five_data (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 5).eval (Nat.card K : ℤ)) :
    (∀ Q : Subgroup (adjointGroup .E6 K), IsPGroup p Q → IsCyclic Q) ∧
      (4 ≤ Nat.card K → ∀ x : adjointGroup .E6 K, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))), V.Normal →
          Group.IsSolvable V → IsCyclic V) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpf' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 +
      (Nat.card K : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord5⟩ := CTE6.e6Five_data hp hp5 hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E6) := not_dvd_card_weylGroup_E hp hp7 (Or.inl rfl)
  have hΦ5 : ((Nat.card K : ℕ) : ZMod p) ^ 4 + ((Nat.card K : ℕ) : ZMod p) ^ 3 +
      ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 +
      (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1) p).2 hpf'
    simpa using this
  set w : WeylGroup .E6 := (coxeterSystem .E6).wordProd [0, 2, 3, 4] with hwdef
  have hw : ∀ u, w • u = e6O5W *ᵥ u := wordProd_smul_eq_wordMat_mulVec .E6 [0, 2, 3, 4]
  set n : ModGL .E6 L := canonicalRep (coxeterSystem .E6) L w with hndef
  have hnC : n ∈ adjointGroup .E6 L := canonicalRep_mem_adjointGroup (coxeterSystem .E6) L w
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hθroot : IsRoot .E6 e6O5Theta := E6_order_five_lattice_and_exact_A1_prime_root_kernel.1
  set J : Set (Fin Tag.E6.rank) := {i | i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4} with hJ
  have hJorth : ∀ i ∈ J, CFSG.LieType.Steinberg.Adjoint.iform
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ) e6O5Theta = 0 := by
    intro i hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide +kernel
  have hwJ : w ∈ parabolicWeylGroup .E6 J := by
    refine wordProd_mem_parabolicWeylGroup (fun i hi => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hi
  have hsl : ∀ j : Fin Tag.E6.rank, Tag.E6.symmetrizer j j = 1 := by decide
  have hn : n ∈ Subgroup.centralizer (rootRankOneGroup .E6 L e6O5Theta : Set (ModGL .E6 L)) :=
    canonicalRep_mem_centralizer_rootRankOneGroup hsl hθroot hJorth hwJ
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e6O5W Fr).map (rootDiagUnitHom .E6 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
    exact twistedTorus_eq_map_twistedFixedTuples w Fr
  have hZeq := subtorusA1_eq_map_fixedBlockTuples hT hθroot
  have hinj0 : Function.Injective (rootDiagUnitHom .E6 L) := rootDiagUnit_injective
  have hne : e6FiveBlock.P.eval (Nat.card K : ℤ) ≠ 0 := by
    have h1 : (1 : ℤ) < (Nat.card K : ℤ) ^ 5 := by
      have : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq2
      calc (1 : ℤ) < 2 := by norm_num
        _ ≤ 2 ^ 5 := by norm_num
        _ ≤ (Nat.card K : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
    show (Polynomial.X ^ 5 - Polynomial.C 1 : ℤ[X]).eval (Nat.card K : ℤ) ≠ 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain ⟨hcycB, hcardB⟩ := e6FiveBlock.isCyclic_and_card Fr hFr hℓ hℓq hne
  have hZcyc : IsCyclic (subtorusA1 n (Units.map (entrywiseHom Fr)) e6O5Theta) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom .E6 L) hinj0).isCyclic.1 hcycB
  have hZcard : Nat.card (subtorusA1 n (Units.map (entrywiseHom Fr)) e6O5Theta) =
      Nat.card K ^ 5 - 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
    show ((Polynomial.X ^ 5 - Polynomial.C 1 : ℤ[X]).eval (Nat.card K : ℤ)).natAbs = _
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have h1 : 1 ≤ Nat.card K ^ 5 := Nat.one_le_pow _ _ (by omega)
    have e : ((Nat.card K : ℤ) ^ 5 - 1) = ((Nat.card K ^ 5 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [e, Int.natAbs_natCast]
  have hN : Nat.card K ^ 5 - 1 ≠ 0 := by
    have : 1 < Nat.card K ^ 5 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hord : p ^ (Nat.card (adjointGroup .E6 K)).factorization p =
      p ^ (Nat.card K ^ 5 - 1).factorization p := by
    have h1 : 1 ≤ Nat.card K ^ 5 := Nat.one_le_pow _ _ (by omega)
    exact ordProj_card_adjointGroup_E6 hp (by omega) hpq hord5 (d₀ := 5) (by decide) (by decide)
      hN (R := 1) (by push_cast [Nat.cast_sub h1]; ring) (by
        intro h
        exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h))
  have hz : ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
      (e6O5W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((Nat.card K : ℕ) : ZMod p) • z →
        {α | IsRoot .E6 α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} := fun z hz0 hzM =>
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.2.2.2.2 p hp hp5
      ((Nat.card K : ℕ) : ZMod p) hΦ5 z hz0 hzM
  have hkerZ : ∀ a : Fin Tag.E6.rank → Lˣ,
      rootDiagUnit .E6 a ∈ subtorusA1 n (Units.map (entrywiseHom Fr)) e6O5Theta →
      orderOf (rootDiagUnit .E6 a) = p → rootCharKernel a ⊆ {e6O5Theta, -e6O5Theta} := by
    intro a ha hap
    rw [hZeq] at ha
    obtain ⟨a', ha', haa'⟩ := ha
    have : a' = a := hinj0 haa'
    subst this
    exact (A1BlockData.rootCharKernel_eq Fr hFr hp hz ha'.1
      (pow_eq_one_of_orderOf_rootDiagUnit hap) (ne_one_of_orderOf_rootDiagUnit hp hap)).le
  obtain ⟨hcyc, hsolv⟩ := a1_untwisted_data .E6 3 (Or.inl ⟨rfl, rfl⟩) K hf hK L hp (by omega)
    hordW n hnC hθroot hZcyc hN hZcard hord hkerZ
  refine ⟨hcyc, fun hK4 => ?_⟩
  obtain ⟨hSfin, hSqs⟩ := sl2_conj_range_quasisimple (L := L) hK4 (1 : GL (Fin 2) L)
  exact hsolv _ (a1_typeI_action Fr hFr hn) hSqs (sl2_conj_range_centralizer (K := K) 1)

theorem oddEndpoint_E6_phi5 :
    OddEndpoint .E6 fun p ℓ f => 5 < p ∧ (p : ℤ) ∣ cycloVal 5 ℓ f := by
  refine oddEndpoint_E6_of_solvable_cyclic ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact E6_five_data K hℓ hf hK hp hc.1 (by simpa [cycloVal, hK] using hc.2)

end CFSG.RankThree.PartOne.KE
