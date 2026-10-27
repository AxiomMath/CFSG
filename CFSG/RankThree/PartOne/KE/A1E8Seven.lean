module

public import CFSG.RankThree.PartOne.KE.A1E8Frame
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE.NativeSolvCyclicE
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1Untwisted
public import CFSG.RankThree.PartOne.KE.A1Weyl

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.Classical (conjSL)
open scoped Matrix Polynomial

namespace CTE8

theorem phi7_of_phi14 {R : Type*} [CommRing R] (x a : R)
    (hx : x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1 = 0) (hax : a + x = 0) :
    a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0 := by
  linear_combination hx + ((a ^ 5 - a ^ 4 * x + a ^ 3 * x ^ 2 - a ^ 2 * x ^ 3 + a * x ^ 4 - x ^ 5) +
    (a ^ 4 - a ^ 3 * x + a ^ 2 * x ^ 2 - a * x ^ 3 + x ^ 4) +
    (a ^ 3 - a ^ 2 * x + a * x ^ 2 - x ^ 3) + (a ^ 2 - a * x + x ^ 2) + (a - x) + 1) * hax

theorem seven_eq_zero_of_phi14 {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 6 - x ^ 5 + x ^ 4 - x ^ 3 + x ^ 2 - x + 1 = 0) (hx1 : x + 1 = 0) :
    (7 : R) = 0 := by
  linear_combination hx - (x ^ 5 - 2 * x ^ 4 + 3 * x ^ 3 - 4 * x ^ 2 + 5 * x - 6) * hx1

theorem e8SevenPlus_data {p q : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 6 + (q : ℤ) ^ 5 + (q : ℤ) ^ 4 + (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + (q : ℤ)
      + 1) :
    ¬ p ∣ q ∧ orderOf (q : ZMod p) = 7 ∧ (p : ℤ) ∣ (q : ℤ) ^ 7 - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 6 + (q : ZMod p) ^ 5 + (q : ZMod p) ^ 4 + (q : ZMod p) ^ 3 +
      (q : ZMod p) ^ 2 + (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 6 + (q : ℤ) ^ 5 + (q : ℤ) ^ 4 +
      (q : ℤ) ^ 3 + (q : ℤ) ^ 2 + (q : ℤ) + 1) p).2 h
    simpa using this
  have hq0 : ¬ p ∣ q := by
    intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    simp at hx
  have hq1 : (q : ZMod p) ≠ 1 := by
    intro h1
    rw [h1] at hx
    have h7 : ((7 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hx
    exact CTE6.natCast_ne_zero_of_lt (by norm_num) hp7 h7
  obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
  rw [← hxdef] at hx hq1 ⊢
  have h7 : x ^ 7 = 1 := by linear_combination (x - 1) * hx
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨hq0, orderOf_eq_prime h7 hq1, ?_⟩
  have h71 : ((q : ℤ) ^ 7 - 1 : ℤ) = ((q : ℤ) ^ 7 - 1) := rfl
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 7 - 1) p).1 ?_
  push_cast
  rw [← hxdef, h7]
  ring

theorem e8SevenMinus_data {p q : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 6 - (q : ℤ) ^ 5 + (q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2 - (q : ℤ)
      + 1) :
    ¬ p ∣ q ∧ orderOf (q : ZMod p) = 14 ∧ (p : ℤ) ∣ (q : ℤ) ^ 7 + 1 ∧
      (-(q : ZMod p)) ^ 6 + (-(q : ZMod p)) ^ 5 + (-(q : ZMod p)) ^ 4 + (-(q : ZMod p)) ^ 3 +
        (-(q : ZMod p)) ^ 2 + (-(q : ZMod p)) + 1 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 6 - (q : ZMod p) ^ 5 + (q : ZMod p) ^ 4 - (q : ZMod p) ^ 3 +
      (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 6 - (q : ℤ) ^ 5 + (q : ℤ) ^ 4 -
      (q : ℤ) ^ 3 + (q : ℤ) ^ 2 - (q : ℤ) + 1) p).2 h
    simpa using this
  have hq0 : ¬ p ∣ q := by
    intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    simp at hx
  refine ⟨hq0, ?_, ?_, phi7_of_phi14 _ _ hx (neg_add_cancel _)⟩
  · obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
    rw [← hxdef] at hx ⊢
    have h7 : x ^ 7 + 1 = 0 := by linear_combination (x + 1) * hx
    have h14 : x ^ 14 = 1 := by linear_combination (x ^ 7 - 1) * h7
    have hnm1 : x + 1 ≠ 0 := fun h1 =>
      CTE6.natCast_ne_zero_of_lt (by norm_num) hp7 (by
        have := seven_eq_zero_of_phi14 x hx h1
        exact_mod_cast this)
    have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h14 fun ℓ hℓ hdvd => ?_
    have h14' : ℓ ∣ 2 * 7 := hdvd
    rcases (Nat.Prime.dvd_mul hℓ).1 h14' with h2 | h7d
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2
      intro h1
      have h1' : x ^ 7 = 1 := by simpa using h1
      apply h2ne
      push_cast
      linear_combination h7 - h1'
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 h7d
      intro h1
      have h1' : x ^ 2 = 1 := by simpa using h1
      apply hnm1
      have h7x : x ^ 7 = x := by
        calc x ^ 7 = (x ^ 2) ^ 3 * x := by ring
          _ = x := by rw [h1']; ring
      rw [h7x] at h7
      exact h7
  · refine (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 7 + 1) p).1 ?_
    push_cast
    linear_combination ((q : ZMod p) + 1) * hx

theorem not_dvd_add_of_dvd_sub {p : ℕ} (hp7 : 7 < p) {m : ℤ}
    (h1 : (p : ℤ) ∣ m - 1) (h2 : (p : ℤ) ∣ m + 1) : False := by
  have h3 : (p : ℤ) ∣ (m + 1) - (m - 1) := dvd_sub h2 h1
  have h4 : (p : ℤ) ∣ 2 := by simpa using h3
  have h5 : p ∣ 2 := by exact_mod_cast h4
  have := Nat.le_of_dvd (by norm_num) h5
  omega

end CTE8

theorem e8SevenBlock_basis (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    LinearIndependent ℤ (fun j : Fin Tag.E8.rank =>
      if (j : ℕ) = 0 then e8O7Theta else ((δ • e8O7W) ^ ((j : ℕ) - 1)) *ᵥ e8O7Beta) ∧
    Submodule.span ℤ (Set.range fun j : Fin Tag.E8.rank =>
      if (j : ℕ) = 0 then e8O7Theta else ((δ • e8O7W) ^ ((j : ℕ) - 1)) *ᵥ e8O7Beta) = ⊤ := by
  obtain ⟨hlin0, hspan0⟩ :=
    E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.2.2.2.2.2.1
  let b : Module.Basis (Fin Tag.E8.rank) ℤ (Fin Tag.E8.rank → ℤ) :=
    Module.Basis.mk hlin0 hspan0.ge
  have hε : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  let ε : ℤˣ := ⟨δ, δ, hε, hε⟩
  let u : Fin Tag.E8.rank → ℤˣ := fun j => if (j : ℕ) = 0 then 1 else ε ^ ((j : ℕ) - 1)
  have hc : ∀ j, (b.unitsSMul u) j =
      if (j : ℕ) = 0 then e8O7Theta else ((δ • e8O7W) ^ ((j : ℕ) - 1)) *ᵥ e8O7Beta := by
    intro j
    rw [Module.Basis.unitsSMul_apply]
    have hbj : b j = e8O7Cols j := Module.Basis.mk_apply hlin0 _ j
    rw [hbj]
    by_cases hj : (j : ℕ) = 0
    · simp [u, hj, e8O7Cols]
    · simp only [u, hj, e8O7Cols, ite_false, Units.smul_def, smul_pow, Matrix.smul_mulVec]
      rw [Units.val_pow_eq_pow_val]
  have hfun : ⇑(b.unitsSMul u) = fun j : Fin Tag.E8.rank =>
      if (j : ℕ) = 0 then e8O7Theta else ((δ • e8O7W) ^ ((j : ℕ) - 1)) *ᵥ e8O7Beta :=
    funext hc
  rw [← hfun]
  exact ⟨(b.unitsSMul u).linearIndependent, (b.unitsSMul u).span_eq⟩

open Polynomial in
@[expose] def e8SevenBlock (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    A1BlockData .E8 (δ • e8O7W) e8O7Theta where
  c := fun j => if (j : ℕ) = 0 then e8O7Theta else ((δ • e8O7W) ^ ((j : ℕ) - 1)) *ᵥ e8O7Beta
  β := e8O7Beta
  P := X ^ 7 - C δ
  hk := by decide
  hlin := (e8SevenBlock_basis δ hδ).1
  hspan := (e8SevenBlock_basis δ hδ).2
  hc0 := by simp
  hβ := fun j hj => by
    have h : (j : ℕ) ≠ 0 := by omega
    simp [h]
  hθM := ⟨δ, by
    rw [Matrix.smul_mulVec, E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.2.2.2.1]⟩
  hP := Polynomial.monic_X_pow_sub_C δ (by norm_num)
  hPdeg := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    rfl
  hrel := by
    have h7 : e8O7W ^ 7 = 1 := by
      rw [← E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.2.2.1]
      exact pow_orderOf_eq_one _
    have hδ7 : δ ^ 7 = δ := by rcases hδ with rfl | rfl <;> norm_num
    have h0 : Polynomial.aeval (δ • e8O7W) (X ^ 7 - C δ : ℤ[X]) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, _root_.smul_pow, h7, hδ7,
        Algebra.algebraMap_eq_smul_one, sub_self]
    rw [h0, Matrix.zero_mulVec]
  hdet := by
    rcases hδ with rfl | rfl <;> simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow]

theorem E8_seven_aux (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {p : ℕ}
    (hp : p.Prime) (hp7 : 7 < p) {m : ℕ} (hm : m = 7 ∨ m = 14)
    (hordq : orderOf ((Nat.card K : ℕ) : ZMod p) = m) (hpq : ¬ p ∣ Nat.card K)
    (hR : ¬ (p : ℤ) ∣ (Nat.card K : ℤ) ^ 7 + δ) (a : ZMod p)
    (ha : a ^ 6 + a ^ 5 + a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0)
    (hcol : ∀ z : Fin Tag.E8.rank → ZMod p,
      ((δ • e8O7W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((Nat.card K : ℕ) : ZMod p) • z →
        (e8O7W.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = a • z)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E8 L) (hnm : n ∈ monomialSubgroup .E8 L)
    (hnW : ∀ u, weylQuotientHom .E8 L ⟨n, hnm⟩ • u = (δ • e8O7W) *ᵥ u) (P : GL (Fin 2) L)
    (hX : ∀ B : SL2 L, n * Units.map (entrywiseHom (iterateFrobenius L ℓ f))
        (rootSL2 .E8 L e8O7Theta B) * n⁻¹ = rootSL2 .E8 L e8O7Theta
          (conjSL (P * GeneralLinearGroup.map (iterateFrobenius L ℓ f) P⁻¹)
            (SpecialLinearGroup.map (iterateFrobenius L ℓ f) B))) :
    (∀ Q : Subgroup (adjointGroup .E8 K), IsPGroup p Q → IsCyclic Q) ∧
      (4 ≤ Nat.card K → ∀ x : adjointGroup .E8 K, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
          Group.IsSolvable V → IsCyclic V) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hℓ : ℓ.Prime := Fact.out
  have hordW : ¬ p ∣ Nat.card (WeylGroup .E8) :=
    not_dvd_card_weylGroup_E hp hp7 (Or.inr (Or.inr rfl))
  have hθroot : IsRoot .E8 e8O7Theta :=
    E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.1
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  have hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (δ • e8O7W) Fr).map (rootDiagUnitHom .E8 L) := by
    rw [← twistedFixedTuples_eq_fixedCharTuples hnW Fr]
    exact twistedTorus_eq_map_twistedFixedTuples_of_weylImage hnm _ rfl Fr
  have hZeq := subtorusA1_eq_map_fixedBlockTuples hT hθroot
  have hinj0 : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  set D := e8SevenBlock δ hδ with hD
  have hq7 : (1 : ℤ) < (Nat.card K : ℤ) ^ 7 := by
    have : (2 : ℤ) ≤ Nat.card K := by exact_mod_cast hq2
    calc (1 : ℤ) < 2 := by norm_num
      _ ≤ 2 ^ 7 := by norm_num
      _ ≤ (Nat.card K : ℤ) ^ 7 := pow_le_pow_left₀ (by norm_num) this 7
  have hδle : δ ≤ 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hδge : -1 ≤ δ := by rcases hδ with rfl | rfl <;> norm_num
  have hne : D.P.eval (Nat.card K : ℤ) ≠ 0 := by
    show (Polynomial.X ^ 7 - Polynomial.C δ : ℤ[X]).eval (Nat.card K : ℤ) ≠ 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain ⟨hcycB, hcardB⟩ := D.isCyclic_and_card Fr hFr hℓ hℓq hne
  set N : ℕ := ((Nat.card K : ℤ) ^ 7 - δ).natAbs with hNdef
  have hNint : (N : ℤ) = (Nat.card K : ℤ) ^ 7 - δ := by
    rw [hNdef]
    exact Int.natAbs_of_nonneg (by omega)
  have hZcyc : IsCyclic (subtorusA1 n (Units.map (entrywiseHom Fr)) e8O7Theta) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom .E8 L) hinj0).isCyclic.1 hcycB
  have hZcard : Nat.card (subtorusA1 n (Units.map (entrywiseHom Fr)) e8O7Theta) = N := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0, hcardB]
    show ((Polynomial.X ^ 7 - Polynomial.C δ : ℤ[X]).eval (Nat.card K : ℤ)).natAbs = N
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    exact hNdef.symm
  have hN : N ≠ 0 := by
    intro h0
    rw [h0] at hNint
    push_cast at hNint
    omega
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p =
      p ^ N.factorization p := by
    have h1 : 1 ≤ Nat.card K ^ 14 := Nat.one_le_pow _ _ (by omega)
    have hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ 14 → ¬ m ∣ d := by
      intro d hd hd14
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hm with rfl | rfl <;>
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    refine ordProj_card_adjointGroup_E8 hp (by omega) hpq hordq (d₀ := 14) (by decide) hrest hN
      (R := (Nat.card K : ℤ) ^ 7 + δ) ?_ hR
    push_cast [Nat.cast_sub h1]
    rw [hNint]
    rcases hδ with rfl | rfl <;> ring
  have hz : ∀ z : Fin Tag.E8.rank → ZMod p, z ≠ 0 →
      ((δ • e8O7W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = ((Nat.card K : ℕ) : ZMod p) • z →
        {α | IsRoot .E8 α ∧ pair α z = 0} = {e8O7Theta, -e8O7Theta} := fun z hz0 hzM =>
    E8_order_seven_lattice_exact_A1_root_kernel_and_negative_frame.2.2.2.2.2.2.2.2.2.1 p hp hp7 a
      ha z hz0 (hcol z hzM)
  have hkerZ : ∀ b : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit .E8 b ∈ subtorusA1 n (Units.map (entrywiseHom Fr)) e8O7Theta →
      orderOf (rootDiagUnit .E8 b) = p → rootCharKernel b ⊆ {e8O7Theta, -e8O7Theta} := by
    intro b hb hbp
    rw [hZeq] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := hinj0 hbb'
    subst this
    exact (A1BlockData.rootCharKernel_eq Fr hFr hp hz hb'.1
      (pow_eq_one_of_orderOf_rootDiagUnit hbp) (ne_one_of_orderOf_rootDiagUnit hp hbp)).le
  obtain ⟨hcyc, hsolv⟩ := a1_untwisted_data .E8 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hf hK L hp
    (by omega) hordW n hnC hθroot hZcyc hN hZcard hord hkerZ
  refine ⟨hcyc, fun hK4 => ?_⟩
  obtain ⟨hSfin, hSqs⟩ := sl2_conj_range_quasisimple (L := L) hK4 P
  exact hsolv _ (fun B => a1_hS1_of_action Fr hFr P hX B) hSqs
    (sl2_conj_range_centralizer (K := K) P)

theorem E8_seven_data (K : Type) [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (hpf : (p : ℤ) ∣ (exhaustionPhi 7).eval (Nat.card K : ℤ) ∨
      (p : ℤ) ∣ (exhaustionPhi 14).eval (Nat.card K : ℤ)) :
    (∀ Q : Subgroup (adjointGroup .E8 K), IsPGroup p Q → IsCyclic Q) ∧
      (4 ≤ Nat.card K → ∀ x : adjointGroup .E8 K, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
          Group.IsSolvable V → IsCyclic V) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ hf hK
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  rcases hpf with h7 | h14
  ·
    have h7' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 6 + (Nat.card K : ℤ) ^ 5 + (Nat.card K : ℤ) ^ 4 +
        (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1 := by
      simpa [exhaustionPhi] using h7
    obtain ⟨hpq, hord, hdvd⟩ := CTE8.e8SevenPlus_data hp hp7 h7'
    have hΦ : ((Nat.card K : ℕ) : ZMod p) ^ 6 + ((Nat.card K : ℕ) : ZMod p) ^ 5 +
        ((Nat.card K : ℕ) : ZMod p) ^ 4 + ((Nat.card K : ℕ) : ZMod p) ^ 3 +
        ((Nat.card K : ℕ) : ZMod p) ^ 2 + ((Nat.card K : ℕ) : ZMod p) + 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((Nat.card K : ℤ) ^ 6 + (Nat.card K : ℤ) ^ 5 +
        (Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 + (Nat.card K : ℤ) + 1)
        p).2 h7'
      simpa using this
    have hcm := canonicalRep_mem_monomialSubgroup L e8W
    have hπ : weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L e8W, hcm⟩ = e8W :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep e8W)
    have hnW : ∀ u, weylQuotientHom .E8 L ⟨canonicalRep (coxeterSystem .E8) L e8W, hcm⟩ • u =
        ((1 : ℤ) • e8O7W) *ᵥ u := fun u => by
      rw [hπ, one_smul]
      exact wordProd_smul_eq_wordMat_mulVec .E8 [0, 2, 3, 4, 5, 6] u
    exact E8_seven_aux K hf hK 1 (Or.inl rfl) hp hp7 (m := 7) (Or.inl rfl) hord hpq
      (fun h => CTE8.not_dvd_add_of_dvd_sub hp7 hdvd h) _ hΦ
      (fun z hz => by simpa only [one_smul] using hz) L _ hcm hnW 1
      (fun B => a1_typeI_hX Fr (e8W_centralizes L) B)
  ·
    have h14' : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 6 - (Nat.card K : ℤ) ^ 5 + (Nat.card K : ℤ) ^ 4 -
        (Nat.card K : ℤ) ^ 3 + (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1 := by
      simpa [exhaustionPhi] using h14
    obtain ⟨hpq, hord, hdvd, ha⟩ := CTE8.e8SevenMinus_data hp hp7 h14'
    obtain ⟨hnm, hW, hQ⟩ := e8_negative_data (L := L)
    have hnW : ∀ u, weylQuotientHom .E8 L ⟨_, hnm⟩ • u = ((-1 : ℤ) • e8O7W) *ᵥ u := fun u => by
      rw [hW u, neg_one_smul, Matrix.neg_mulVec]
    obtain ⟨P, hP⟩ := exists_WSL_twist (K := K) (L := L) Fr hFr
    exact E8_seven_aux K hf hK (-1) (Or.inr rfl) hp hp7 (m := 14) (Or.inr rfl) hord hpq
      (fun h => CTE8.not_dvd_add_of_dvd_sub hp7 (by simpa [sub_eq_add_neg] using h) hdvd)
      (-((Nat.card K : ℕ) : ZMod p)) ha
      (fun z hz => by
        rw [neg_one_smul, Matrix.map_neg (Int.cast : ℤ → ZMod p) (fun a => Int.cast_neg a) e8O7W,
          Matrix.transpose_neg, Matrix.neg_mulVec] at hz
        rw [neg_smul, ← hz, neg_neg]) L _ hnm hnW P
      (fun B => a1_typeII_hX Fr hQ P hP B)

theorem oddEndpoint_E8_phi7Phi14 :
    OddEndpoint .E8 fun p ℓ f =>
      7 < p ∧ ((p : ℤ) ∣ cycloVal 7 ℓ f ∨ (p : ℤ) ∣ cycloVal 14 ℓ f) := by
  refine oddEndpoint_E8_of_solvable_cyclic ?_
  intro K _ _ p ℓ f hp hp3 hℓ hℓp hf hK hc
  exact E8_seven_data K hℓ hf hK hp hc.1 (by simpa [cycloVal, hK] using hc.2)

end CFSG.RankThree.PartOne.KE
