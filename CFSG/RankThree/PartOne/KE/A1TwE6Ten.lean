module

public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.NativeSolvCyclicTw
public import CFSG.RankThree.PartOne.KE.CTTwistedArith
public import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFive
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open CFSG.RankThree.Chevalley (exhaustionPhi)
open CFSG.RankThree.Classical (conjSL)
open scoped Matrix Polynomial

namespace CTE6

theorem phi5_of_phi10 {R : Type*} [CommRing R] (x a : R)
    (hx : x ^ 4 - x ^ 3 + x ^ 2 - x + 1 = 0) (hax : a + x = 0) :
    a ^ 4 + a ^ 3 + a ^ 2 + a + 1 = 0 := by
  linear_combination hx + ((a ^ 3 - a ^ 2 * x + a * x ^ 2 - x ^ 3) + (a ^ 2 - a * x + x ^ 2) +
    (a - x) + 1) * hax

theorem five_eq_zero_of_phi10 {R : Type*} [CommRing R] (x : R)
    (hx : x ^ 4 - x ^ 3 + x ^ 2 - x + 1 = 0) (hx1 : x + 1 = 0) : (5 : R) = 0 := by
  linear_combination hx - (x ^ 3 - 2 * x ^ 2 + 3 * x - 4) * hx1

theorem twE6Ten_data {p q : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (h : (p : ℤ) ∣ (q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2 - (q : ℤ) + 1) :
    7 < p ∧ ¬ p ∣ q ∧ orderOf (q : ZMod p) = 10 ∧
      (-(q : ZMod p)) ^ 4 + (-(q : ZMod p)) ^ 3 + (-(q : ZMod p)) ^ 2 + (-(q : ZMod p)) + 1 =
        0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx : (q : ZMod p) ^ 4 - (q : ZMod p) ^ 3 + (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) ^ 4 - (q : ℤ) ^ 3 + (q : ℤ) ^ 2 -
      (q : ℤ) + 1) p).2 h
    simpa using this
  have hq0 : ¬ p ∣ q := by
    intro hdvd
    have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hdvd
    rw [hq0] at hx
    simp at hx
  have hΦ5 := phi5_of_phi10 _ _ hx (neg_add_cancel (q : ZMod p))
  obtain ⟨x, hxdef⟩ : ∃ x : ZMod p, x = (q : ZMod p) := ⟨_, rfl⟩
  rw [← hxdef] at hx hΦ5 ⊢
  have h5 : x ^ 5 + 1 = 0 := by linear_combination (x + 1) * hx
  have h10 : x ^ 10 = 1 := by linear_combination (x ^ 5 - 1) * h5
  have hnm1 : x + 1 ≠ 0 := fun h1 =>
    CTE6.natCast_ne_zero_of_lt (by norm_num) hp5 (by
      have := five_eq_zero_of_phi10 x hx h1
      exact_mod_cast this)
  have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := CTE6.natCast_ne_zero_of_lt (by norm_num) (by omega)
  have hord : orderOf x = 10 := by
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h10 fun ℓ hℓ hdvd => ?_
    have h10' : ℓ ∣ 2 * 5 := hdvd
    rcases (Nat.Prime.dvd_mul hℓ).1 h10' with h2 | h5d
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2
      intro h1
      have h1' : x ^ 5 = 1 := by simpa using h1
      apply h2ne
      push_cast
      linear_combination h5 - h1'
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 h5d
      intro h1
      have h1' : x ^ 2 = 1 := by simpa using h1
      apply hnm1
      have h5x : x ^ 5 = x := by
        calc x ^ 5 = (x ^ 2) ^ 2 * x := by ring
          _ = x := by rw [h1']; ring
      rw [h5x] at h5
      exact h5
  refine ⟨?_, hq0, hord, hΦ5⟩
  have hx0 : x ≠ 0 := fun h0 => by rw [h0] at h10; simp at h10
  have hdvd := ZMod.orderOf_dvd_card_sub_one hx0
  rw [hord] at hdvd
  by_contra hle
  have hp7 : p ≤ 7 := not_lt.1 hle
  interval_cases p <;> omega

end CTE6

namespace CTTw

theorem ordProj_twisted_ten {p q : ℕ} (hp : p.Prime) (hq : 2 ≤ q) (hpq : ¬ p ∣ q)
    (hord : orderOf (q : ZMod p) = 10) :
    p ^ (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
        (q ^ 2 - 1)).factorization p = p ^ (q ^ 5 + 1).factorization p := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hn₀ : q ^ 5 + 1 ≠ 0 := by omega
  have h36 := not_dvd_pow hp hpq 36
  have h12 := not_dvd_pow_sub_one hord (show ¬ 10 ∣ 12 by norm_num)
  have h9 := not_dvd_pow_add_one hord (show ¬ 10 ∣ 2 * 9 by norm_num)
  have h8 := not_dvd_pow_sub_one hord (show ¬ 10 ∣ 8 by norm_num)
  have h6 := not_dvd_pow_sub_one hord (show ¬ 10 ∣ 6 by norm_num)
  have h2 := not_dvd_pow_sub_one hord (show ¬ 10 ∣ 2 by norm_num)
  refine ordProj_eq_of_int_cofactor hn₀ (R := (q : ℤ) ^ 36 * ((q : ℤ) ^ 12 - 1) *
    ((q : ℤ) ^ 9 + 1) * ((q : ℤ) ^ 8 - 1) * ((q : ℤ) ^ 6 - 1) * ((q : ℤ) ^ 2 - 1)) ?_
    (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul (hpz.not_dvd_mul
      (hpz.not_dvd_mul h36 h12) h9) h8) h6) h2)
  simp only [Nat.cast_mul, cast_pow_sub_one (by omega : 1 ≤ q), Nat.cast_add, Nat.cast_pow,
    Nat.cast_one]
  ring

end CTTw

theorem e6FiveSignedBlock_basis (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    LinearIndependent ℤ (fun j : Fin Tag.E6.rank =>
      if (j : ℕ) = 0 then e6O5Theta else ((δ • e6O5W) ^ ((j : ℕ) - 1)) *ᵥ e6O5Beta) ∧
    Submodule.span ℤ (Set.range fun j : Fin Tag.E6.rank =>
      if (j : ℕ) = 0 then e6O5Theta else ((δ • e6O5W) ^ ((j : ℕ) - 1)) *ᵥ e6O5Beta) = ⊤ := by
  obtain ⟨hlin0, hspan0⟩ :=
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.1
  let b : Module.Basis (Fin Tag.E6.rank) ℤ (Fin Tag.E6.rank → ℤ) :=
    Module.Basis.mk hlin0 hspan0.ge
  have hε : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  let ε : ℤˣ := ⟨δ, δ, hε, hε⟩
  let u : Fin Tag.E6.rank → ℤˣ := fun j => if (j : ℕ) = 0 then 1 else ε ^ ((j : ℕ) - 1)
  have hc : ∀ j, (b.unitsSMul u) j =
      if (j : ℕ) = 0 then e6O5Theta else ((δ • e6O5W) ^ ((j : ℕ) - 1)) *ᵥ e6O5Beta := by
    intro j
    rw [Module.Basis.unitsSMul_apply]
    have hbj : b j = e6O5Cols j := Module.Basis.mk_apply hlin0 _ j
    rw [hbj]
    by_cases hj : (j : ℕ) = 0
    · simp [u, hj, e6O5Cols]
    · simp only [u, hj, e6O5Cols, ite_false, Units.smul_def, smul_pow, Matrix.smul_mulVec]
      rw [Units.val_pow_eq_pow_val]
  have hfun : ⇑(b.unitsSMul u) = fun j : Fin Tag.E6.rank =>
      if (j : ℕ) = 0 then e6O5Theta else ((δ • e6O5W) ^ ((j : ℕ) - 1)) *ᵥ e6O5Beta :=
    funext hc
  rw [← hfun]
  exact ⟨(b.unitsSMul u).linearIndependent, (b.unitsSMul u).span_eq⟩

open Polynomial in
def e6FiveSignedBlock (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    A1BlockData .E6 (δ • e6O5W) e6O5Theta where
  c := fun j => if (j : ℕ) = 0 then e6O5Theta else ((δ • e6O5W) ^ ((j : ℕ) - 1)) *ᵥ e6O5Beta
  β := e6O5Beta
  P := X ^ 5 - C δ
  hk := by decide
  hlin := (e6FiveSignedBlock_basis δ hδ).1
  hspan := (e6FiveSignedBlock_basis δ hδ).2
  hc0 := by simp
  hβ := fun j hj => by
    have h : (j : ℕ) ≠ 0 := by omega
    simp [h]
  hθM := ⟨δ, by
    rw [Matrix.smul_mulVec, E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.1]⟩
  hP := Polynomial.monic_X_pow_sub_C δ (by norm_num)
  hPdeg := by
    rw [Polynomial.natDegree_X_pow_sub_C]
    rfl
  hrel := by
    have h5 : e6O5W ^ 5 = 1 := by
      rw [← E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.1]
      exact pow_orderOf_eq_one _
    have hδ5 : δ ^ 5 = δ := by rcases hδ with rfl | rfl <;> norm_num
    have h0 : Polynomial.aeval (δ • e6O5W) (X ^ 5 - C δ : ℤ[X]) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, _root_.smul_pow, h5, hδ5,
        Algebra.algebraMap_eq_smul_one, sub_self]
    rw [h0, Matrix.zero_mulVec]
  hdet := by
    rcases hδ with rfl | rfl <;> simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow]

theorem e6HRw_smul (y : Fin TwistTag.E6.tag.rank → ℤ) :
    e6HRw • y = e6O5W *ᵥ y := by
  have h : e6HRw = (coxeterSystem TwistTag.E6.tag).wordProd [0, 2, 3, 4] := by
    simp [e6HRw, CoxeterSystem.wordProd, mul_assoc]
    rfl
  rw [h]
  exact wordProd_smul_eq_wordMat_mulVec .E6 [0, 2, 3, 4] y

theorem twE6_ten_data {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) (hpf : (p : ℤ) ∣ (exhaustionPhi 10).eval ((ℓ ^ f : ℕ) : ℤ)) :
    (∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q → IsCyclic Q) ∧
      (4 ≤ ℓ ^ f → ∀ x : twistedE6RootGroup K σ, orderOf x = p →
        ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (twistedE6RootGroup K σ))), V.Normal →
          Group.IsSolvable V → IsCyclic V) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  have hpf' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 4 - ((ℓ ^ f : ℕ) : ℤ) ^ 3 + ((ℓ ^ f : ℕ) : ℤ) ^ 2 -
      ((ℓ ^ f : ℕ) : ℤ) + 1 := by simpa [exhaustionPhi] using hpf
  obtain ⟨hp7, hpq, hord10, hΦ5⟩ := CTE6.twE6Ten_data hp hp5 hpf'
  have hordW : ¬ p ∣ Nat.card (WeylGroup TwistTag.E6.tag) :=
    not_dvd_card_weylGroup_E (τ := .E6) hp hp7 (Or.inl rfl)
  obtain ⟨-, -, -, -, hrange, hPfix, ⟨hn, hπ, hv1, hv2⟩, htw, -⟩ :=
    E6_highest_root_graph_fixed_and_signed_order_five_descent L
  set n : ModGL TwistTag.E6.tag L := e6HRn L with hndef
  have hnC : n ∈ adjointGroup TwistTag.E6.tag L := monomialSubgroup_le_adjointGroup' hn
  set v := weylQuotientHom TwistTag.E6.tag L ⟨n, hn⟩ with hvdef
  have hv : ∀ x : Fin TwistTag.E6.tag.rank → ℤ,
      v • x = (((-1 : ℤ)) • e6O5W) *ᵥ permLattice TwistTag.E6.perm x := fun x => by
    rw [hv1 x, smul_neg, e6HRw_smul, neg_one_smul, Matrix.neg_mulVec]
    rfl
  have hθroot : IsRoot TwistTag.E6.tag e6O5Theta :=
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.1
  have hθ : e6HighestRoot = e6O5Theta := rfl
  have hT := twistedTorus_E6_eq_map_of_weylImage Fr hn v rfl ((-1 : ℤ) • e6O5W) hv
  have hZeq := subtorusA1_eq_map_fixedBlockTuples hT hθroot
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.E6.tag L) := rootDiagUnit_injective
  set D := e6FiveSignedBlock (-1) (Or.inr rfl) with hD
  have hq5 : (1 : ℤ) < ((ℓ ^ f : ℕ) : ℤ) ^ 5 := by
    have : (2 : ℤ) ≤ ((ℓ ^ f : ℕ) : ℤ) := by exact_mod_cast hq2
    calc (1 : ℤ) < 2 := by norm_num
      _ ≤ 2 ^ 5 := by norm_num
      _ ≤ ((ℓ ^ f : ℕ) : ℤ) ^ 5 := pow_le_pow_left₀ (by norm_num) this 5
  have hne : D.P.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0 := by
    show (Polynomial.X ^ 5 - Polynomial.C (-1) : ℤ[X]).eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    omega
  obtain ⟨hcycB, hcardB⟩ := D.isCyclic_and_card Fr hFr hℓ hℓq hne
  have hZcyc : IsCyclic (subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta) := by
    rw [hZeq]
    exact (Subgroup.equivMapOfInjective _ (rootDiagUnitHom TwistTag.E6.tag L) hinj0).isCyclic.1
      hcycB
  have hZcard : Nat.card (subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta) =
      (ℓ ^ f) ^ 5 + 1 := by
    rw [hZeq, Subgroup.card_map_of_injective hinj0]
    refine hcardB.trans ?_
    show ((Polynomial.X ^ 5 - Polynomial.C (-1) : ℤ[X]).eval ((ℓ ^ f : ℕ) : ℤ)).natAbs = _
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    have e : ((ℓ ^ f : ℕ) : ℤ) ^ 5 - -1 = (((ℓ ^ f) ^ 5 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [e, Int.natAbs_natCast]
  have hN : (ℓ ^ f) ^ 5 + 1 ≠ 0 := by omega
  have hord := CTTw.ordProj_twisted_ten hp hq2 hpq hord10
  have hz' : ∀ z : Fin Tag.E6.rank → ZMod p, z ≠ 0 →
      (((-1 : ℤ) • e6O5W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
        {α | IsRoot Tag.E6 α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} := fun z hz0 hzM =>
    E6_order_five_lattice_and_exact_A1_prime_root_kernel.2.2.2.2.2.2.2.2 p hp hp5
      (-((ℓ ^ f : ℕ) : ZMod p)) hΦ5 z hz0 (transpose_eigen_neg e6O5W _ z hzM)
  have hz : ∀ z : Fin TwistTag.E6.tag.rank → ZMod p, z ≠ 0 →
      (((-1 : ℤ) • e6O5W).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z =
        ((ℓ ^ f : ℕ) : ZMod p) • z →
        {α | IsRoot TwistTag.E6.tag α ∧ pair α z = 0} = {e6O5Theta, -e6O5Theta} :=
    fun z hz0 hzM => hz' z hz0 hzM
  have hkerZ : ∀ b : Fin TwistTag.E6.tag.rank → Lˣ,
      rootDiagUnit TwistTag.E6.tag b ∈ subtorusA1 n (twistHom TwistTag.E6 L Fr) e6O5Theta →
      orderOf (rootDiagUnit TwistTag.E6.tag b) = p →
      rootCharKernel b ⊆ {e6O5Theta, -e6O5Theta} := by
    intro b hb hbp
    rw [hZeq] at hb
    obtain ⟨b', hb', hbb'⟩ := hb
    have : b' = b := hinj0 hbb'
    subst this
    exact (A1BlockData.rootCharKernel_eq Fr hFr hp hz hb'.1
      (pow_eq_one_of_orderOf_rootDiagUnit hbp) (ne_one_of_orderOf_rootDiagUnit hp hbp)).le
  obtain ⟨hcyc, hsolv⟩ := a1_twisted_data (ℓ := ℓ) hf K hK σ hσ L hp hp7 hordW n hnC hθroot hZcyc
    hN hZcard hord hkerZ
  refine ⟨hcyc, fun hK4 => ?_⟩
  have hρmem : ∀ B : SL2 L, rootSL2 TwistTag.E6.tag L e6HighestRoot B ∈
      rootSubgroup TwistTag.E6.tag L e6HighestRoot ⊔
        rootSubgroup TwistTag.E6.tag L (-e6HighestRoot) := fun B => by
    rw [← hrange]
    exact ⟨B, rfl⟩
  have hΦ : ∀ B : SL2 L, twistHom TwistTag.E6 L Fr (rootSL2 TwistTag.E6.tag L e6HighestRoot B) =
      rootSL2 TwistTag.E6.tag L e6HighestRoot (SpecialLinearGroup.map Fr B) := fun B => by
    rw [twistHom_apply, entrywise_rootSL2_of_field Fr e6HighestRoot B]
    exact hPfix _ (hρmem _)
  have hnQ : ∀ B : SL2 L, n * rootSL2 TwistTag.E6.tag L e6HighestRoot B * n⁻¹ =
      rootSL2 TwistTag.E6.tag L e6HighestRoot (WSL * B * WSL⁻¹) := fun B => by
    have h := htw (RingEquiv.refl L) B
    have hP := hPfix _ (hρmem B)
    have hmapid : SpecialLinearGroup.map (RingEquiv.refl L).toRingHom B = B := by
      ext i j
      simp [SpecialLinearGroup.map_apply_coe]
    have e : Units.map (entrywiseHom (RingEquiv.refl L).toRingHom)
        (rootSL2 TwistTag.E6.tag L e6HighestRoot B) = rootSL2 TwistTag.E6.tag L e6HighestRoot B :=
      Units.ext (entrywise_id _)
    rw [e6HRTwist, e, hmapid] at h
    calc n * rootSL2 TwistTag.E6.tag L e6HighestRoot B * n⁻¹
        = n * (diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
          (diagramMap TwistTag.E6 L)⁻¹) * n⁻¹ := by rw [hP]
      _ = n * diagramMap TwistTag.E6 L * rootSL2 TwistTag.E6.tag L e6HighestRoot B *
          (diagramMap TwistTag.E6 L)⁻¹ * n⁻¹ := by group
      _ = rootSL2 TwistTag.E6.tag L e6HighestRoot (WSL * B * WSL⁻¹) := h
  obtain ⟨k, _, _, _, hkcard⟩ := exists_finite_field_into ℓ f hf L
  have hFrk : ∀ c, Fr c = c ^ Nat.card k := fun c => by rw [hkcard]; exact hFr c
  obtain ⟨P, hP⟩ := exists_WSL_twist (K := k) (L := L) Fr hFrk
  have hX : ∀ B : SL2 L, n * twistHom TwistTag.E6 L Fr (rootSL2 TwistTag.E6.tag L e6HighestRoot B) *
      n⁻¹ = rootSL2 TwistTag.E6.tag L e6HighestRoot
        (conjSL (P * GeneralLinearGroup.map Fr P⁻¹) (SpecialLinearGroup.map Fr B)) := fun B => by
    rw [hΦ B, hnQ, hP, conjSL_toGL]
  have hk4 : 4 ≤ Nat.card k := by rw [hkcard]; exact hK4
  obtain ⟨hSfin, hSqs⟩ := sl2_conj_range_quasisimple (L := L) hk4 P
  exact hsolv _ (fun B => a1_hS1_of_action Fr hFrk P hX B) hSqs
    (sl2_conj_range_centralizer (K := k) P)

theorem oddEndpoint_twE6_phi10 :
    OddEndpoint .twistedE6 fun p ℓ f => 5 < p ∧ (p : ℤ) ∣ cycloVal 10 ℓ f := by
  refine oddEndpoint_twistedE6_of_solvable_cyclic ?_
  intro K _ _ σ p ℓ f hp hp3 hℓ hℓp hf hK hσ hc
  exact twE6_ten_data hℓ hf K hK σ hσ hp hc.1 (by simpa [cycloVal] using hc.2)

end CFSG.RankThree.PartOne.KE
