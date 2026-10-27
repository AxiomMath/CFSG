module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.MatrixBlocks
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.HomocyclicFrattini
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.FixedPointProduct
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.MatrixTrace
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.StandardCover
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.SubgroupRectangular

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# Wielandt fixed point theorem

This file records the fixed-point endpoint from Wielandt's theorem used in
Peterfalvi `(9.1)`.
-/

noncomputable section

open scoped IsMulCommutative

namespace CFSG.Wielandt

universe u

/-- A nontrivial elementary abelian `p`-group has order divisible by `p`, so a
group whose order is coprime to it has order coprime to `p`. -/
private theorem coprime_prime_card_of_coprime_elementaryAbelian_card
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G)) :
    Nat.Coprime p (Nat.card G) := by
  classical
  have hVp : IsPGroup p V := IsElementaryAbelian.isPGroup p V
  rcases (IsPGroup.iff_card (p := p) (G := V)).1 hVp with ⟨n, hcard⟩
  have hVgt : 1 < Nat.card V := Finite.one_lt_card
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hcard1 : Nat.card V = 1 := by
      simp [hcard, hn0]
    exact (Nat.ne_of_gt hVgt) hcard1
  have hpdvd : p ∣ Nat.card V := by
    rw [hcard]
    exact dvd_pow_self p (Nat.ne_of_gt hnpos)
  exact Nat.Coprime.of_dvd_left hpdvd hcop

/-- Schur-Zassenhaus gives a group-theoretic section of a surjective map whose
kernel has order a power of `p` and whose quotient has order coprime to `p`. -/
public theorem exists_monoidHom_rightInverse_of_surjective_isPGroup_ker
    {E Q : Type u} [Group E] [Group Q] [Finite E] [Finite Q]
    {p : ℕ} [Fact p.Prime]
    (φ : E →* Q) (hφ : Function.Surjective φ)
    (hker : IsPGroup p φ.ker) (hcop : Nat.Coprime p (Nat.card Q)) :
    ∃ σ : Q →* E, Function.RightInverse σ φ := by
  classical
  haveI : φ.ker.Normal := inferInstance
  have hkerCard : Nat.Coprime (Nat.card φ.ker) φ.ker.index := by
    rcases (IsPGroup.iff_card (p := p) (G := φ.ker)).1 hker with ⟨n, hcard⟩
    have hindex : φ.ker.index = Nat.card Q := by
      rw [Subgroup.index_ker]
      calc
        Nat.card φ.range = Nat.card (⊤ : Subgroup Q) := by
          rw [φ.range_eq_top_of_surjective hφ]
        _ = Nat.card Q := Subgroup.card_top
    rw [hcard, hindex]
    exact hcop.pow_left n
  rcases Subgroup.exists_right_complement'_of_coprime
      (N := φ.ker) hkerCard with
    ⟨K, hcomp⟩
  have hcomp' : K.IsComplement' φ.ker := hcomp.symm
  let e : E ⧸ φ.ker ≃* K := hcomp'.QuotientMulEquiv
  let qIso : E ⧸ φ.ker ≃* Q :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφ
  let σ : Q →* E := K.subtype.comp (e.toMonoidHom.comp qIso.symm.toMonoidHom)
  refine ⟨σ, ?_⟩
  intro q
  rcases hφ q with ⟨x, rfl⟩
  dsimp [σ, qIso, e]
  have hq :
      (QuotientGroup.mk' φ.ker
          (hcomp'.QuotientMulEquiv
            ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x)) : E)) =
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x) := by
    exact Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hcomp' _
  have hq' :
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
        (QuotientGroup.mk' φ.ker
          (hcomp'.QuotientMulEquiv
            ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ x)) : E)) =
        φ x := by
    rw [hq, MulEquiv.apply_symm_apply]
  simpa [QuotientGroup.quotientKerEquivOfSurjective] using hq'

/-- A representation into the target of a surjective map with `p`-group kernel
lifts whenever the representing group has order coprime to `p`. -/
public theorem exists_lift_of_surjective_isPGroup_ker_of_coprime
    {E Q G : Type u} [Group E] [Group Q] [Group G]
    [Finite E] [Finite Q] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (φ : E →* Q) (hφ : Function.Surjective φ)
    (hker : IsPGroup p φ.ker) (hcop : Nat.Coprime p (Nat.card G))
    (ρ : G →* Q) :
    ∃ lift : G →* E, φ.comp lift = ρ := by
  classical
  let P : Subgroup E := ρ.range.comap φ
  let φP : P →* ρ.range := {
    toFun x := ⟨φ x, x.2⟩
    map_one' := by
      ext
      exact map_one φ
    map_mul' x y := by
      ext
      exact map_mul φ (x : E) (y : E)
  }
  have hφP : Function.Surjective φP := by
    rintro ⟨q, hq⟩
    rcases hφ q with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change φ x ∈ ρ.range
      simpa [hx] using hq
    · ext
      exact hx
  have hkerP : IsPGroup p φP.ker := by
    intro x
    have hxker : (x : P) ∈ φP.ker := x.2
    have hxφ : (x : E) ∈ φ.ker := by
      change φ ((x : P) : E) = 1
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hxker)
    rcases hker ⟨(x : E), hxφ⟩ with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hn
  have hcopRange : Nat.Coprime p (Nat.card ρ.range) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_range_dvd ρ) hcop
  rcases exists_monoidHom_rightInverse_of_surjective_isPGroup_ker
      (p := p) φP hφP hkerP hcopRange with
    ⟨σ, hσ⟩
  let lift : G →* E := P.subtype.comp (σ.comp ρ.rangeRestrict)
  refine ⟨lift, ?_⟩
  ext g
  change φ (lift g) = ρ g
  exact congrArg Subtype.val (hσ (ρ.rangeRestrict g))

/-- A unit after reduction from `ZMod (p ^ e)` to `ZMod p` was already a
unit before reduction. -/
private theorem zmod_prime_pow_isUnit_of_castHom_isUnit
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    {x : ZMod (p ^ e)}
    (hx : IsUnit (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt he)) (ZMod p) x)) :
    IsUnit x := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hpe0 : p ^ e ≠ 0 := pow_ne_zero e hp0
  haveI : NeZero (p ^ e) := ⟨hpe0⟩
  have hxval : IsUnit ((x.val : ℕ) : ZMod (p ^ e)) := by
    refine (ZMod.isUnit_iff_coprime x.val (p ^ e)).2 ?_
    apply (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd
    intro hpx
    have hxred0 :
        ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt he)) (ZMod p) x = 0 := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val]
      exact (ZMod.natCast_eq_zero_iff x.val p).2 hpx
    rw [hxred0] at hx
    exact not_isUnit_zero hx
  simpa [ZMod.natCast_zmod_val x] using hxval

/-- Entrywise reduction from `GL_κ (ZMod (p ^ e))` to `GL_κ (ZMod p)` is
surjective. -/
private theorem generalLinearGroup_map_zmod_castHom_surjective
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) :
    Function.Surjective
      (Matrix.GeneralLinearGroup.map (n := κ)
        (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt he)) (ZMod p))) := by
  classical
  let hpdiv : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
  let red : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpdiv (ZMod p)
  intro A
  choose B hB using fun i j => ZMod.castHom_surjective hpdiv (A i j)
  let Bmat : Matrix κ κ (ZMod (p ^ e)) := fun i j => B i j
  have hmapB : red.mapMatrix Bmat = (A : Matrix κ κ (ZMod p)) := by
    ext i j
    exact hB i j
  have hdetRed : red Bmat.det = (A : Matrix κ κ (ZMod p)).det := by
    rw [RingHom.map_det red Bmat, hmapB]
  have hdetUnitRed : IsUnit (red Bmat.det) := by
    rw [hdetRed]
    exact Matrix.isUnits_det_units A
  have hdetUnit : IsUnit Bmat.det :=
    zmod_prime_pow_isUnit_of_castHom_isUnit (p := p) (e := e) he hdetUnitRed
  refine ⟨Matrix.GeneralLinearGroup.mk'' Bmat hdetUnit, ?_⟩
  ext i j
  change red (Bmat i j) = A i j
  exact hB i j

/-- The additive group of matrices over `ZMod (p ^ e)` is a `p`-group. -/
private theorem matrix_additive_multiplicative_isPGroup
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    {p e : ℕ} [Fact p.Prime] :
    IsPGroup p (Multiplicative (Matrix κ κ (ZMod (p ^ e)))) := by
  intro x
  refine ⟨e, ?_⟩
  apply Multiplicative.toAdd.injective
  ext i j
  change (p ^ e) • Multiplicative.toAdd x i j = 0
  simp

/-- The kernel of entrywise reduction from `GL_κ (ZMod (p ^ e))` to
`GL_κ (ZMod p)` is a `p`-group. -/
private theorem generalLinearGroup_map_zmod_castHom_ker_isPGroup
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) :
    IsPGroup p
      (Matrix.GeneralLinearGroup.map (n := κ)
        (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt he)) (ZMod p))).ker := by
  classical
  let hpdiv : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
  let red : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpdiv (ZMod p)
  let φ : GL κ (ZMod (p ^ e)) →* GL κ (ZMod p) :=
    Matrix.GeneralLinearGroup.map (n := κ) red
  let redM : Matrix κ κ (ZMod (p ^ e)) →+ Matrix κ κ (ZMod p) := {
    toFun := fun M => red.mapMatrix M
    map_zero' := by
      ext i j
      simp [red]
    map_add' := by
      intro A B
      ext i j
      exact map_add red (A i j) (B i j)
  }
  let K : Subgroup (Multiplicative (Matrix κ κ (ZMod (p ^ e)))) :=
    AddSubgroup.toSubgroup redM.ker
  have hK : IsPGroup p K :=
    (matrix_additive_multiplicative_isPGroup (κ := κ) (p := p) (e := e)).to_subgroup K
  have : Finite K := inferInstance
  rcases (IsPGroup.iff_card (p := p) (G := K)).1 hK with ⟨n, hn⟩
  refine (IsPGroup.iff_card (p := p) (G := φ.ker)).2 ⟨n, ?_⟩
  let kerEquiv : φ.ker ≃ K := by
    refine {
      toFun := fun g =>
        ⟨Multiplicative.ofAdd
          (((g : GL κ (ZMod (p ^ e))) : Matrix κ κ (ZMod (p ^ e))) - 1), ?_⟩
      invFun := fun N => ?_
      left_inv := ?_
      right_inv := ?_ }
    · change (((g : GL κ (ZMod (p ^ e))) : Matrix κ κ (ZMod (p ^ e))) - 1) ∈
        redM.ker
      rw [AddMonoidHom.mem_ker]
      ext i j
      have hred_one : red ((1 : Matrix κ κ (ZMod (p ^ e))) i j) =
          (1 : Matrix κ κ (ZMod p)) i j := by
        by_cases hij : i = j
        · subst j
          simp [map_one red]
        · simp [hij, red]
      have hgmat :
          ((φ (g : GL κ (ZMod (p ^ e))) : GL κ (ZMod p)) :
              Matrix κ κ (ZMod p)) = 1 := by
        exact congrArg (fun A : GL κ (ZMod p) => (A : Matrix κ κ (ZMod p)))
          (MonoidHom.mem_ker.mp g.2)
      have hgij :
          red (((g : GL κ (ZMod (p ^ e))) : Matrix κ κ (ZMod (p ^ e))) i j) =
            (1 : Matrix κ κ (ZMod p)) i j := by
        simpa [φ, Matrix.GeneralLinearGroup.map_apply] using congrFun (congrFun hgmat i) j
      change red
          ((((g : GL κ (ZMod (p ^ e))) : Matrix κ κ (ZMod (p ^ e))) - 1) i j) =
        0
      rw [Matrix.sub_apply, map_sub, hgij, hred_one]
      simp
    · let Nmat : Matrix κ κ (ZMod (p ^ e)) :=
        Multiplicative.toAdd (N : Multiplicative (Matrix κ κ (ZMod (p ^ e))))
      let A : Matrix κ κ (ZMod (p ^ e)) := 1 + Nmat
      have hNker : Nmat ∈ redM.ker := by
        exact N.2
      have hNzero : redM Nmat = 0 := AddMonoidHom.mem_ker.mp hNker
      have hmapA : red.mapMatrix A = (1 : Matrix κ κ (ZMod p)) := by
        ext i j
        have hred_one : red ((1 : Matrix κ κ (ZMod (p ^ e))) i j) =
            (1 : Matrix κ κ (ZMod p)) i j := by
          by_cases hij : i = j
          · subst j
            simp [map_one red]
          · simp [hij, red]
        have hNij : red (Nmat i j) = 0 := by
          simpa [redM, Nmat] using congrFun (congrFun hNzero i) j
        change red ((1 : Matrix κ κ (ZMod (p ^ e))) i j + Nmat i j) =
          (1 : Matrix κ κ (ZMod p)) i j
        rw [map_add, hNij, hred_one]
        simp
      have hdetRed : red A.det = (1 : Matrix κ κ (ZMod p)).det := by
        rw [RingHom.map_det red A, hmapA]
      have hdetUnitRed : IsUnit (red A.det) := by
        rw [hdetRed]
        simp
      have hdetUnit : IsUnit A.det :=
        zmod_prime_pow_isUnit_of_castHom_isUnit (p := p) (e := e) he hdetUnitRed
      refine ⟨Matrix.GeneralLinearGroup.mk'' A hdetUnit, ?_⟩
      change φ (Matrix.GeneralLinearGroup.mk'' A hdetUnit) = 1
      ext i j
      simpa [φ, Matrix.GeneralLinearGroup.map_apply] using congrFun (congrFun hmapA i) j
    · intro g
      ext i j
      simp
    · intro N
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      ext i j
      simp
  calc
    Nat.card φ.ker = Nat.card K := Nat.card_congr kerEquiv
    _ = p ^ n := hn

/-- Compatibility of `Matrix.GeneralLinearGroup.toLin` with coordinatewise
reduction. -/
private theorem generalLinearGroup_toLin_zmod_castHom_apply
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (A : GL κ (ZMod (p ^ e))) (x : κ → ZMod (p ^ e)) :
    standardHomocyclicCoverAddReduction κ p e he
        (((Matrix.GeneralLinearGroup.toLin A :
            (Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e)))ˣ) :
          Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e))) x) =
      (((Matrix.GeneralLinearGroup.toLin
          (Matrix.GeneralLinearGroup.map (n := κ)
            (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt he)) (ZMod p)) A) :
          (Module.End (ZMod p) (κ → ZMod p))ˣ) :
        Module.End (ZMod p) (κ → ZMod p))
        (standardHomocyclicCoverAddReduction κ p e he x)) := by
  classical
  let hpdiv : p ∣ p ^ e := dvd_pow_self p (Nat.ne_of_gt he)
  let red : ZMod (p ^ e) →+* ZMod p := ZMod.castHom hpdiv (ZMod p)
  ext i
  change red (((fun j => (A : Matrix κ κ (ZMod (p ^ e))) i j) ⬝ᵥ x)) =
    ((fun j => red ((A : Matrix κ κ (ZMod (p ^ e))) i j)) ⬝ᵥ
      fun j => red (x j))
  simp only [dotProduct]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact map_mul red ((A : Matrix κ κ (ZMod (p ^ e))) i j) (x j)

/-- Matrix/linear-map source core for lifting a coprime mod-`p` representation.

The proof instantiates the group-theoretic coprime lift for the reduction map
`GL_κ (ZMod (p ^ e)) → GL_κ (ZMod p)`, using the checked surjectivity and
`p`-group kernel facts for this map. -/
private theorem exists_zmod_prime_power_linear_lift_of_coprime_core
    {G κ : Type u} [Group G] [Finite G] [Fintype G] [Fintype κ]
    {p e : ℕ} [Fact p.Prime]
    (hcop : Nat.Coprime p (Nat.card G)) (he : 1 < e)
    (ρ : G →* (Module.End (ZMod p) (κ → ZMod p))ˣ) :
    Nonempty
      {linearLift :
        G →* (Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e)))ˣ //
        ∀ (g : G) (x : κ → ZMod (p ^ e)),
          standardHomocyclicCoverAddReduction κ p e (le_of_lt he)
              (((linearLift g :
                  (Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e)))ˣ) :
                Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e))) x) =
            (((ρ g :
                (Module.End (ZMod p) (κ → ZMod p))ˣ) :
              Module.End (ZMod p) (κ → ZMod p))
              (standardHomocyclicCoverAddReduction κ p e (le_of_lt he) x))} := by
  classical
  let red : ZMod (p ^ e) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt (le_of_lt he))) (ZMod p)
  let φ : GL κ (ZMod (p ^ e)) →* GL κ (ZMod p) :=
    Matrix.GeneralLinearGroup.map (n := κ) red
  let ρM : G →* GL κ (ZMod p) :=
    Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp ρ
  have hφ : Function.Surjective φ := by
    simpa [φ, red] using
      generalLinearGroup_map_zmod_castHom_surjective
        (κ := κ) (p := p) (e := e) (le_of_lt he)
  have hker : IsPGroup p φ.ker := by
    simpa [φ, red] using
      generalLinearGroup_map_zmod_castHom_ker_isPGroup
        (κ := κ) (p := p) (e := e) (le_of_lt he)
  rcases exists_lift_of_surjective_isPGroup_ker_of_coprime
      (p := p) φ hφ hker hcop ρM with
    ⟨liftM, hliftM⟩
  let linearLift : G →* (Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e)))ˣ :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp liftM
  refine ⟨⟨linearLift, ?_⟩⟩
  intro g x
  have hcompat := generalLinearGroup_toLin_zmod_castHom_apply
    (κ := κ) (p := p) (e := e) (le_of_lt he) (liftM g) x
  have hρM : φ (liftM g) = ρM g := by
    exact congrFun (congrArg DFunLike.coe hliftM) g
  have htoLin :
      Matrix.GeneralLinearGroup.toLin (φ (liftM g)) = ρ g := by
    calc
      Matrix.GeneralLinearGroup.toLin (φ (liftM g)) =
          Matrix.GeneralLinearGroup.toLin (ρM g) := by rw [hρM]
      _ = ρ g := by
        simp [ρM]
  simpa [linearLift, φ, red, htoLin] using hcompat


public theorem exists_zmod_prime_power_linear_lift_of_coprime
    {G κ : Type u} [Group G] [Finite G] [Fintype G] [Fintype κ]
    {p e : ℕ} [Fact p.Prime]
    (hcop : Nat.Coprime p (Nat.card G)) (he : 1 < e)
    (ρ : G →* (Module.End (ZMod p) (κ → ZMod p))ˣ) :
    Nonempty
      {linearLift :
        G →* (Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e)))ˣ //
        ∀ (g : G) (x : κ → ZMod (p ^ e)),
          standardHomocyclicCoverAddReduction κ p e (le_of_lt he)
              (((linearLift g :
                  (Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e)))ˣ) :
                Module.End (ZMod (p ^ e)) (κ → ZMod (p ^ e))) x) =
            (((ρ g :
                (Module.End (ZMod p) (κ → ZMod p))ˣ) :
              Module.End (ZMod p) (κ → ZMod p))
              (standardHomocyclicCoverAddReduction κ p e (le_of_lt he) x))} := by
  classical
  exact exists_zmod_prime_power_linear_lift_of_coprime_core
    (G := G) (κ := κ) (p := p) (e := e) hcop he ρ


public theorem
    exists_standard_homocyclic_frattini_quotient_cover_canonical_additive_linear_reduction_gt_one
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (_hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 1 < e) :
    Nonempty
      (StandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData
        (G := G) (V := V) (p := p) e (le_of_lt he)) := by
  classical
  have hpG : Nat.Coprime p (Nat.card G) :=
    coprime_prime_card_of_coprime_elementaryAbelian_card
      (G := G) (V := V) (p := p) hcop
  rcases exists_zmod_prime_power_linear_lift_of_coprime
      (G := G) (κ := StandardHomocyclicCanonicalIndex (p := p) V)
      (p := p) (e := e) hpG he
      (standardHomocyclicCoverModPLinearAction G V (p := p)) with
    ⟨⟨linearLift, hred⟩⟩
  exact ⟨{
    linearLift := linearLift
    reduction_linear := hred }⟩


/-- Higher-exponent canonical-index source core for the lifted standard-cover
action at the reduction-compatible canonical linear interface.

This is now a checked wrapper around additive coordinate reduction data: the
compatibility with the multiplicative standard cover follows from the checked
coordinate adapter. -/
public theorem
    exists_standard_homocyclic_frattini_quotient_cover_canonical_linear_reduction_gt_one
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 1 < e) :
    Nonempty
      (StandardHomocyclicFrattiniQuotientCoverCanonicalLinearReductionData
        (G := G) (V := V) (p := p) e (le_of_lt he)) := by
  classical
  rcases
    exists_standard_homocyclic_frattini_quotient_cover_canonical_additive_linear_reduction_gt_one
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨L⟩
  exact
    ⟨L.toStandardHomocyclicFrattiniQuotientCoverCanonicalLinearReductionData⟩

/-- Higher-exponent canonical-index source core for the lifted standard-cover
action at the canonical quotient-linear interface.

This is now a checked wrapper around reduction-compatible canonical linear data:
the compatibility with the original `V` action follows from the checked
transport lemma `standardHomocyclicCoverModPAction_quotientToV`. -/
public theorem
    exists_standard_homocyclic_frattini_quotient_cover_canonical_linear_gt_one
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 1 < e) :
    Nonempty
      (StandardHomocyclicFrattiniQuotientCoverCanonicalLinearData
        (G := G) (V := V) (p := p) e (le_of_lt he)) := by
  classical
  rcases
    exists_standard_homocyclic_frattini_quotient_cover_canonical_linear_reduction_gt_one
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨L⟩
  exact ⟨L.toStandardHomocyclicFrattiniQuotientCoverCanonicalLinearData⟩


/-- Higher-exponent source core for the lifted linear action on the standard
homocyclic cover coordinates.

This is now a checked wrapper around the canonical-index quotient-linear source
core. -/
public theorem exists_standard_homocyclic_frattini_quotient_cover_linear_gt_one
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 1 < e) :
    Nonempty
      (StandardHomocyclicFrattiniQuotientCoverLinearData
        (G := G) (V := V) (p := p) e) := by
  classical
  rcases exists_standard_homocyclic_frattini_quotient_cover_canonical_linear_gt_one
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨L⟩
  exact ⟨L.toStandardHomocyclicFrattiniQuotientCoverLinearData⟩

/-- Higher-exponent source core for the lifted action on the standard
homocyclic cover.

This is now a checked wrapper around the coordinate-linear source core: linear
automorphisms of the standard coordinates act on
`StandardHomocyclicCover κ (p ^ e)` by type-tag transport. -/
public theorem exists_standard_homocyclic_frattini_quotient_cover_action_gt_one
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 1 < e) :
    Nonempty
      (StandardHomocyclicFrattiniQuotientCoverActionData
        (G := G) (V := V) (p := p) e) := by
  classical
  rcases exists_standard_homocyclic_frattini_quotient_cover_linear_gt_one
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨L⟩
  exact ⟨L.toStandardHomocyclicFrattiniQuotientCoverActionData⟩

/-- Higher-exponent source core of the homocyclic semidirect-product
construction.

This is now a checked wrapper around the action-only source core and the
standard Frattini quotient identification by coordinatewise mod-`p` reduction. -/
public theorem exists_standard_homocyclic_frattini_quotient_cover_gt_one
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 1 < e) :
    Nonempty
      (StandardHomocyclicFrattiniQuotientCoverData
        (G := G) (V := V) (p := p) e) := by
  classical
  rcases exists_standard_homocyclic_frattini_quotient_cover_action_gt_one
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨D⟩
  exact ⟨D.toStandardHomocyclicFrattiniQuotientCoverData⟩

/-- Higher-exponent source core of the homocyclic semidirect-product
construction.

This is now a checked wrapper around the standard-cover source core and the
generic standard homocyclic cover infrastructure. -/
public theorem exists_homocyclic_frattini_quotient_cover_gt_one
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 1 < e) :
    Nonempty (HomocyclicFrattiniQuotientCover (G := G) (V := V) (p := p) e) := by
  classical
  rcases exists_standard_homocyclic_frattini_quotient_cover_gt_one
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨D⟩
  exact ⟨D.toHomocyclicFrattiniQuotientCover⟩


public theorem exists_homocyclic_frattini_quotient_cover_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 0 < e) :
    Nonempty (HomocyclicFrattiniQuotientCover (G := G) (V := V) (p := p) e) := by
  classical
  rcases Nat.eq_or_lt_of_le he with rfl | he_gt
  · exact exists_homocyclic_frattini_quotient_cover_e_one (G := G) (V := V) (p := p)
  · exact exists_homocyclic_frattini_quotient_cover_gt_one
      (G := G) (V := V) (p := p) hcop hminv he_gt

public theorem exists_homocyclic_frattini_cover_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 0 < e) :
    Nonempty (HomocyclicFrattiniCover (G := G) (V := V) (p := p) e) := by
  classical
  rcases exists_homocyclic_frattini_quotient_cover_prime_power
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨C⟩
  rcases exists_homocyclic_frattini_cover_coordinate_data_prime_power
      (G := G) (V := V) (p := p) C with
    ⟨D⟩
  exact ⟨D.toHomocyclicFrattiniCover⟩

public theorem exists_homocyclic_frattini_cover_linear_lift_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 0 < e) :
    Nonempty (HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) := by
  classical
  rcases exists_homocyclic_frattini_cover_prime_power
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨C⟩
  rcases exists_homocyclic_frattini_cover_action_lift_prime_power
      (G := G) (V := V) (p := p) C with
    ⟨L⟩
  exact ⟨L.toHomocyclicFrattiniCoverLinearLift⟩


/-- Fixed-Frattini cardinality comparison in height one.

When the homocyclic cover has exponent `p`, it is elementary abelian, so its
Frattini subgroup is trivial and the fixed-Frattini count is `1`. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_fixed_frattini_card_data_eq_one
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) 1)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) →
    Nonempty
      (HomocyclicFrattiniCoverSubgroupFixedFrattiniCardData
        (G := G) (V := V) (p := p) A L D C) := by
  classical
  intro C
  letI : Group L.cover := L.instGroupCover
  letI : Finite L.cover := L.instFiniteCover
  letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
  let hΦinv : IsInvariant A L.cover (frattini L.cover) :=
    isInvariant_of_characteristic (frattini L.cover)
  letI : IsInvariant A L.cover (frattini L.cover) := hΦinv
  letI : MulDistribMulAction A (frattini L.cover) :=
    instMulDistribMulAction_subtype (A := A) (G := L.cover) (H := frattini L.cover)
  haveI : Fact (IsPGroup p L.cover) := ⟨L.cover_isPGroup⟩
  haveI : IsMulCommutative L.cover := L.cover_commutative
  haveI : IsElementaryAbelian p L.cover :=
    { toIsMulCommutative := L.cover_commutative
      exponent_dvd_p := by
        rw [L.cover_exponent]
        simp }
  have hΦbot : frattini L.cover = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (R := L.cover) (p := p)
  refine ⟨{ fixed_frattini_card := ?_ }⟩
  have hfixbot : fixedPointSubgroup A (frattini L.cover) = ⊥ := by
    ext x
    have hx1 : x = 1 := by
      apply Subtype.ext
      have hxbot : (x : L.cover) ∈ (⊥ : Subgroup L.cover) := by
        simpa [hΦbot] using x.property
      simpa using hxbot
    constructor
    · intro _hx
      simpa using hx1
    · intro _hx
      rw [hx1]
      intro a
      simp
  calc
    Nat.card (fixedPointSubgroup A (frattini L.cover)) = 1 := by
      simp [hfixbot]
    _ = p ^ ((1 - 1) * fixedSubspaceFinrank (G := G) (V := V) (p := p) A) := by
      simp

/-- Fixed points inside the kernel of the `p`-power map are the same as the
kernel of scalar multiplication by `p` on the additive fixed subgroup. -/
private noncomputable def
    fixedPointSubgroupPowKerFixedSubgroupEquiv
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Group L.cover := L.instGroupCover
    letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
    letI : IsMulCommutative L.cover := L.cover_commutative
    letI : CommGroup L.cover := IsMulCommutative.instCommGroup
    letI : Module (ZMod (p ^ e)) (Additive L.cover) := L.additiveCoverZModModule
    letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      AddSubgroupClass.instZModModule
        (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
    let φ : L.cover →* L.cover := powMonoidHom p
    let hkerInv : IsInvariant A L.cover φ.ker := by
      haveI : φ.ker.Characteristic := by
        simpa [φ] using powMonoidHom_ker_characteristic (H := L.cover) p
      exact isInvariant_of_characteristic φ.ker
    letI : IsInvariant A L.cover φ.ker := hkerInv
    letI : MulDistribMulAction A φ.ker :=
      instMulDistribMulAction_subtype (A := A) (G := L.cover) (H := φ.ker)
    fixedPointSubgroup A φ.ker ≃
      {x : Additive D.fixedSubgroup // (p : ZMod (p ^ e)) • x = 0} := by
  classical
  letI : Group L.cover := L.instGroupCover
  letI : Finite L.cover := L.instFiniteCover
  letI : Fintype L.cover := L.instFintypeCover
  letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
  haveI : Fact (IsPGroup p L.cover) := ⟨L.cover_isPGroup⟩
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  letI : Module (ZMod (p ^ e)) (Additive L.cover) := L.additiveCoverZModModule
  letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  let φ : L.cover →* L.cover := powMonoidHom p
  haveI : φ.ker.Characteristic := by
    simpa [φ] using powMonoidHom_ker_characteristic (H := L.cover) p
  let hkerInv : IsInvariant A L.cover φ.ker := isInvariant_of_characteristic φ.ker
  letI : IsInvariant A L.cover φ.ker := hkerInv
  letI : MulDistribMulAction A φ.ker :=
    instMulDistribMulAction_subtype (A := A) (G := L.cover) (H := φ.ker)
  refine {
    toFun := fun y => ?_
    invFun := fun x => ?_
    left_inv := ?_
    right_inv := ?_ }
  · have hyfixW : ((y.1 : φ.ker) : L.cover) ∈ fixedPointSubgroup A L.cover := by
      change ∀ a : A, a • (((y.1 : φ.ker) : L.cover)) =
        (((y.1 : φ.ker) : L.cover))
      intro a
      exact congrArg Subtype.val (y.2 a)
    have hyD : ((y.1 : φ.ker) : L.cover) ∈ D.fixedSubgroup := by
      simpa [D.fixedSubgroup_eq] using hyfixW
    refine
      ⟨Additive.ofMul (⟨((y.1 : φ.ker) : L.cover), hyD⟩ : D.fixedSubgroup), ?_⟩
    apply Additive.toMul.injective
    change Additive.toMul
        ((p : ZMod (p ^ e)) • Additive.ofMul (⟨((y.1 : φ.ker) : L.cover), hyD⟩ :
          D.fixedSubgroup)) = 1
    have hyker : ((y.1 : φ.ker) : L.cover) ^ p = 1 := by
      change (powMonoidHom p : L.cover →* L.cover) (((y.1 : φ.ker) : L.cover)) = 1
      exact (y.1 : φ.ker).property
    simpa [Nat.cast_smul_eq_nsmul, toMul_nsmul] using hyker
  · let w : L.cover := ((Additive.toMul x.1 : D.fixedSubgroup) : L.cover)
    have hwker : w ∈ φ.ker := by
      have hx0 := x.2
      rw [Nat.cast_smul_eq_nsmul] at hx0
      have hxD :=
        congrArg (fun z : Additive D.fixedSubgroup => Additive.toMul z) hx0
      change (Additive.toMul x.1 : D.fixedSubgroup) ^ p = 1 at hxD
      have hxL := congrArg (fun z : D.fixedSubgroup => (z : L.cover)) hxD
      change ((Additive.toMul x.1 : D.fixedSubgroup) : L.cover) ^ p = 1
      exact hxL
    have hwfix : (⟨w, hwker⟩ : φ.ker) ∈ fixedPointSubgroup A φ.ker := by
      change ∀ a : A, a • (⟨w, hwker⟩ : φ.ker) = (⟨w, hwker⟩ : φ.ker)
      intro a
      apply Subtype.ext
      have hDfix : w ∈ fixedPointSubgroup A L.cover := by
        simpa [D.fixedSubgroup_eq, w] using
          (Additive.toMul x.1 : D.fixedSubgroup).property
      exact hDfix a
    exact ⟨⟨w, hwker⟩, hwfix⟩
  · intro y
    ext
    rfl
  · intro x
    ext
    rfl


public theorem
    exists_homocyclic_frattini_cover_subgroup_fixed_frattini_card_data_gt_one
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ} (he : 1 < e)
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) →
    Nonempty
      (HomocyclicFrattiniCoverSubgroupFixedFrattiniCardData
        (G := G) (V := V) (p := p) A L D C) := by
  classical
  intro C
  letI : Group L.cover := L.instGroupCover
  letI : Finite L.cover := L.instFiniteCover
  letI : Fintype L.cover := L.instFintypeCover
  letI : MulDistribMulAction A L.cover := homocyclicFrattiniCoverSubgroupAction A L
  haveI : Fact (IsPGroup p L.cover) := ⟨L.cover_isPGroup⟩
  letI : IsMulCommutative L.cover := L.cover_commutative
  letI : CommGroup L.cover := IsMulCommutative.instCommGroup
  have he0 : 0 < e := lt_trans Nat.zero_lt_one he
  haveI : Nontrivial (ZMod (p ^ e)) := by
    rw [ZMod.nontrivial_iff]
    exact ne_of_gt
      (Nat.one_lt_pow (Nat.ne_of_gt he0) (Fact.out : p.Prime).one_lt)
  haveI : IsLocalRing (ZMod (p ^ e)) :=
    zmod_prime_pow_isLocalRing (Fact.out : p.Prime) he0
  letI : Module (ZMod (p ^ e)) (Additive L.cover) :=
    L.additiveCoverZModModule
  letI : Module (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    AddSubgroupClass.instZModModule
      (K := (D.fixedSubgroup.toAddSubgroup : AddSubgroup (Additive L.cover)))
  haveI : Module.Finite (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    Module.Finite.of_finite
  haveI : Module.Projective (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    D.projective_fixedSubgroup
  haveI : Module.Flat (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    Module.Flat.of_projective
  haveI : Module.Free (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
    Module.free_of_flat_of_isLocalRing
  let φ : L.cover →* L.cover := powMonoidHom p
  haveI : φ.ker.Characteristic := by
    simpa [φ] using powMonoidHom_ker_characteristic (H := L.cover) p
  haveI : φ.range.Characteristic := by
    simpa [φ] using powMonoidHom_range_characteristic (H := L.cover) p
  let hkerInv : IsInvariant A L.cover φ.ker := isInvariant_of_characteristic φ.ker
  let hrangeInv : IsInvariant A L.cover φ.range := isInvariant_of_characteristic φ.range
  let hΦinv : IsInvariant A L.cover (frattini L.cover) :=
    isInvariant_of_characteristic (frattini L.cover)
  letI : IsInvariant A L.cover φ.ker := hkerInv
  letI : IsInvariant A L.cover φ.range := hrangeInv
  letI : IsInvariant A L.cover (frattini L.cover) := hΦinv
  letI : MulDistribMulAction A φ.ker :=
    instMulDistribMulAction_subtype (A := A) (G := L.cover) (H := φ.ker)
  letI : MulDistribMulAction A φ.range :=
    instMulDistribMulAction_subtype (A := A) (G := L.cover) (H := φ.range)
  letI : MulDistribMulAction A (frattini L.cover) :=
    instMulDistribMulAction_subtype (A := A) (G := L.cover) (H := frattini L.cover)
  letI : MulDistribMulAction A (L.cover ⧸ φ.ker) :=
    quotientMulDistribMulAction (A := A) (G := L.cover) φ.ker hkerInv
  letI : MulDistribMulAction A (L.cover ⧸ frattini L.cover) :=
    quotientMulDistribMulAction (A := A) (G := L.cover) (frattini L.cover) hΦinv
  let r := fixedSubspaceFinrank (G := G) (V := V) (p := p) A
  have hΦ : frattini L.cover = φ.range := by
    simpa [φ] using
      (frattini_eq_powMonoidHom_range_of_isPGroup_commutative
        (R := L.cover) (p := p))
  have hsolv : IsSolvable L.cover := by
    exact isSolvable_of_comm fun x y =>
      (IsMulCommutative.is_comm (M := L.cover)).comm x y
  have hfactorKer :
      Nat.card (fixedPointSubgroup A L.cover) =
        Nat.card (fixedPointSubgroup A φ.ker) *
          Nat.card (fixedPointSubgroup A (L.cover ⧸ φ.ker)) := by
    simpa using
      (fixedPointSubgroup_card_eq_mul_quotient_action
        (A := A) (M := L.cover) (N := φ.ker)
        hkerInv hsolv D.coprime_card)
  have hquotRange :
      Nat.card (fixedPointSubgroup A (L.cover ⧸ φ.ker)) =
        Nat.card (fixedPointSubgroup A φ.range) := by
    exact Nat.card_congr
      (fixedPointSubgroupPowQuotientKerEquivRange
        (A := A) (M := L.cover) p).toEquiv
  have hfactorKerRange :
      Nat.card (fixedPointSubgroup A L.cover) =
        Nat.card (fixedPointSubgroup A φ.ker) *
          Nat.card (fixedPointSubgroup A φ.range) := by
    calc
      Nat.card (fixedPointSubgroup A L.cover) =
          Nat.card (fixedPointSubgroup A φ.ker) *
            Nat.card (fixedPointSubgroup A (L.cover ⧸ φ.ker)) := hfactorKer
      _ = Nat.card (fixedPointSubgroup A φ.ker) *
            Nat.card (fixedPointSubgroup A φ.range) := by
          rw [hquotRange]
  have hfrRange :
      Nat.card (fixedPointSubgroup A (frattini L.cover)) =
        Nat.card (fixedPointSubgroup A φ.range) := by
    exact Nat.card_congr
      (fixedPointSubgroupMulEquiv (A := A)
        (M := frattini L.cover) (N := φ.range)
        (MulEquiv.subgroupCongr hΦ) (by
          intro a x
          ext
          rfl)).toEquiv
  have hfactorFrattini :
      Nat.card (fixedPointSubgroup A L.cover) =
        Nat.card (fixedPointSubgroup A (frattini L.cover)) *
          Nat.card (fixedPointSubgroup A (L.cover ⧸ frattini L.cover)) := by
    simpa using
      (fixedPointSubgroup_card_eq_mul_quotient_action
        (A := A) (M := L.cover) (N := frattini L.cover)
        hΦinv hsolv D.coprime_card)
  have hfactorRange :
      Nat.card (fixedPointSubgroup A L.cover) =
        Nat.card (fixedPointSubgroup A φ.range) * p ^ r := by
    calc
      Nat.card (fixedPointSubgroup A L.cover) =
          Nat.card (fixedPointSubgroup A (frattini L.cover)) *
            Nat.card (fixedPointSubgroup A (L.cover ⧸ frattini L.cover)) :=
        hfactorFrattini
      _ = Nat.card (fixedPointSubgroup A φ.range) *
            Nat.card (fixedPointSubgroup A (L.cover ⧸ frattini L.cover)) := by
          rw [hfrRange]
      _ = Nat.card (fixedPointSubgroup A φ.range) * p ^ r := by
          rw [L.fixedPointSubgroup_frattiniQuotient_card
            (G := G) (V := V) (p := p) (A := A)]
  have hfixedKer_card_r :
      Nat.card (fixedPointSubgroup A φ.ker) = p ^ r := by
    have hprod :
        Nat.card (fixedPointSubgroup A φ.ker) *
            Nat.card (fixedPointSubgroup A φ.range) =
          Nat.card (fixedPointSubgroup A φ.range) * p ^ r :=
      hfactorKerRange.symm.trans hfactorRange
    have hrange_pos : 0 < Nat.card (fixedPointSubgroup A φ.range) := by
      haveI : Finite φ.range := inferInstance
      haveI : Finite (fixedPointSubgroup A φ.range) := inferInstance
      exact Nat.card_pos
    apply Nat.mul_right_cancel hrange_pos
    exact hprod.trans (Nat.mul_comm (Nat.card (fixedPointSubgroup A φ.range)) (p ^ r))
  have hfixedKer_card_finrank :
      Nat.card (fixedPointSubgroup A φ.ker) =
        p ^ Module.finrank (ZMod (p ^ e)) (Additive D.fixedSubgroup) := by
    calc
      Nat.card (fixedPointSubgroup A φ.ker) =
          Nat.card {x : Additive D.fixedSubgroup //
            (p : ZMod (p ^ e)) • x = 0} :=
        Nat.card_congr
          (fixedPointSubgroupPowKerFixedSubgroupEquiv
            (G := G) (V := V) (p := p) A L D)
      _ = p ^ Module.finrank (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
        finite_free_zmod_prime_pow_mul_p_ker_natCard
          (p := p) (e := e) he0 (M := Additive D.fixedSubgroup)
  have hfixed_finrank :
      Module.finrank (ZMod (p ^ e)) (Additive D.fixedSubgroup) = r := by
    apply Nat.pow_right_injective (Fact.out : Nat.Prime p).one_lt
    exact hfixedKer_card_finrank.symm.trans hfixedKer_card_r
  have hRcard : Nat.card (ZMod (p ^ e)) = p ^ e := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hfixed_cover_card :
      Nat.card (fixedPointSubgroup A L.cover) = (p ^ e) ^ r := by
    have hfree :
        Nat.card (Additive D.fixedSubgroup) =
          Nat.card (ZMod (p ^ e)) ^
            Module.finrank (ZMod (p ^ e)) (Additive D.fixedSubgroup) :=
      finite_free_natCard_eq_pow_finrank
        (R := ZMod (p ^ e)) (M := Additive D.fixedSubgroup)
    calc
      Nat.card (fixedPointSubgroup A L.cover) = Nat.card D.fixedSubgroup := by
        rw [D.fixedSubgroup_eq]
      _ = Nat.card (Additive D.fixedSubgroup) := rfl
      _ = Nat.card (ZMod (p ^ e)) ^
            Module.finrank (ZMod (p ^ e)) (Additive D.fixedSubgroup) := hfree
      _ = (p ^ e) ^ r := by
        rw [hRcard, hfixed_finrank]
  have hfixed_frattini_mul :
      Nat.card (fixedPointSubgroup A (frattini L.cover)) * p ^ r = (p ^ e) ^ r := by
    calc
      Nat.card (fixedPointSubgroup A (frattini L.cover)) * p ^ r =
          Nat.card (fixedPointSubgroup A (frattini L.cover)) *
            Nat.card (fixedPointSubgroup A (L.cover ⧸ frattini L.cover)) := by
            rw [L.fixedPointSubgroup_frattiniQuotient_card
              (G := G) (V := V) (p := p) (A := A)]
      _ = Nat.card (fixedPointSubgroup A L.cover) := hfactorFrattini.symm
      _ = (p ^ e) ^ r := hfixed_cover_card
  have harith :
      p ^ ((e - 1) * r) * p ^ r = (p ^ e) ^ r := by
    have hpred : e - 1 + 1 = e := Nat.sub_add_cancel (Nat.succ_le_of_lt he0)
    calc
      p ^ ((e - 1) * r) * p ^ r = p ^ ((e - 1) * r + r) := by
        rw [← pow_add]
      _ = p ^ (e * r) := by
        congr 1
        have hmul : (e - 1 + 1) * r = e * r := by
          rw [hpred]
        simpa [Nat.add_mul] using hmul
      _ = (p ^ e) ^ r := by
        rw [pow_mul]
  refine ⟨{ fixed_frattini_card := ?_ }⟩
  apply Nat.mul_right_cancel (pow_pos (Fact.out : Nat.Prime p).pos r)
  exact hfixed_frattini_mul.trans harith.symm

/-- Source-core fixed-Frattini cardinality comparison for a fixed
positive-height split.

The height-one case is checked directly; strict higher exponents use the
checked Mho/Frattini fixed-point count. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_fixed_frattini_card_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ} (he : 0 < e)
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) →
    Nonempty
      (HomocyclicFrattiniCoverSubgroupFixedFrattiniCardData
        (G := G) (V := V) (p := p) A L D C) := by
  classical
  intro C
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt he) with heq | hgt
  · cases heq
    exact
      exists_homocyclic_frattini_cover_subgroup_fixed_frattini_card_data_eq_one
        (G := G) (V := V) (p := p) A L D C
  · exact
      exists_homocyclic_frattini_cover_subgroup_fixed_frattini_card_data_gt_one
        (G := G) (V := V) (p := p) A hgt L D C

/-- Checked fixed-factor cardinality comparison for a fixed positive-height
split.

The full fixed-factor count follows from the checked fixed-Frattini count by
coprime fixed-point quotienting and the stored Frattini quotient equivalence. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_fixed_factor_card_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ} (he : 0 < e)
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) →
    Nonempty
      (HomocyclicFrattiniCoverSubgroupFixedFactorCardData
        (G := G) (V := V) (p := p) A L D C) := by
  classical
  intro C
  rcases exists_homocyclic_frattini_cover_subgroup_fixed_frattini_card_data
      (G := G) (V := V) (p := p) A he L D C with
    ⟨H⟩
  exact ⟨H.toFixedFactorCardData he⟩

/-- Checked fixed-factor finite-rank comparison for a fixed positive-height
split.

The rank statement follows from the fixed-factor cardinality comparison because
the fixed factor is a finite free module over the local ring `ZMod (p ^ e)`. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_fixed_factor_finrank_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ} (he : 0 < e)
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) →
    Nonempty
      (HomocyclicFrattiniCoverSubgroupFixedFactorFinrankData
        (G := G) (V := V) (p := p) A L D C) := by
  classical
  intro C
  haveI : Nontrivial (ZMod (p ^ e)) := by
    rw [ZMod.nontrivial_iff]
    exact ne_of_gt
      (Nat.one_lt_pow (Nat.ne_of_gt he) (Fact.out : p.Prime).one_lt)
  haveI : IsLocalRing (ZMod (p ^ e)) :=
    zmod_prime_pow_isLocalRing (Fact.out : p.Prime) he
  rcases exists_homocyclic_frattini_cover_subgroup_fixed_factor_card_data
      (G := G) (V := V) (p := p) A he L D C with
    ⟨H⟩
  exact ⟨H.toFixedFactorFinrankData he⟩

/-- Checked finite-rank comparison on the two action factors for a fixed
positive-height split.

The commutator-factor rank follows from the ambient free coordinates and the
checked product equivalence `[W,A] × C_W(A) ≃ W`; the fixed-factor rank is
supplied by the checked fixed-factor comparison. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_factor_finrank_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ} (he : 0 < e)
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) →
    Nonempty
      (HomocyclicFrattiniCoverSubgroupFactorFinrankData
        (G := G) (V := V) (p := p) A L D C) := by
  classical
  intro C
  haveI : Nontrivial (ZMod (p ^ e)) := by
    rw [ZMod.nontrivial_iff]
    exact ne_of_gt
      (Nat.one_lt_pow (Nat.ne_of_gt he) (Fact.out : p.Prime).one_lt)
  haveI : IsLocalRing (ZMod (p ^ e)) :=
    zmod_prime_pow_isLocalRing (Fact.out : p.Prime) he
  rcases exists_homocyclic_frattini_cover_subgroup_fixed_factor_finrank_data
      (G := G) (V := V) (p := p) A he L D C with
    ⟨H⟩
  exact ⟨H.toFactorFinrankData⟩

/-- Checked free coordinates on the two action factors for a fixed split.

For positive height this is a wrapper around the source finite-rank comparison:
the two factors are projective direct summands of the homocyclic cover, hence
free over the local ring `ZMod (p ^ e)`. At height zero the cover has exponent
one, so the two factor groups and the coordinate domains are all
subsingletons. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_factor_coordinate_equivs
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    (C : HomocyclicFrattiniCoverSubgroupCoordinateSplit
      (G := G) (V := V) (p := p) A L D) →
    Nonempty
      (HomocyclicFrattiniCoverSubgroupFactorCoordinateEquivs
        (G := G) (V := V) (p := p) A L D C) := by
  classical
  intro C
  by_cases he : 0 < e
  · haveI : Nontrivial (ZMod (p ^ e)) := by
      rw [ZMod.nontrivial_iff]
      exact ne_of_gt
        (Nat.one_lt_pow (Nat.ne_of_gt he) (Fact.out : p.Prime).one_lt)
    haveI : IsLocalRing (ZMod (p ^ e)) :=
      zmod_prime_pow_isLocalRing (Fact.out : p.Prime) he
    rcases exists_homocyclic_frattini_cover_subgroup_factor_finrank_data
        (G := G) (V := V) (p := p) A he L D C with
      ⟨H⟩
    exact ⟨H.toFactorCoordinateEquivs⟩
  · have he0 : e = 0 := Nat.eq_zero_of_not_pos he
    subst e
    letI : Group L.cover := L.instGroupCover
    haveI : Subsingleton L.cover := by
      refine ⟨fun x y => ?_⟩
      have hpow : ∀ z : L.cover, z ^ (p ^ 0) = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [L.cover_exponent])
      have hxy : x * y⁻¹ = 1 := by simpa using (hpow (x * y⁻¹))
      simpa using congr_arg (fun z => z * y) hxy
    haveI : Subsingleton (Additive D.commutatorSubgroup) := inferInstance
    haveI : Subsingleton (Additive D.fixedSubgroup) := inferInstance
    haveI : Subsingleton (ZMod (p ^ 0)) := by
      exact ZMod.subsingleton_iff.2 (by simp)
    haveI : Subsingleton (C.leftIndex → ZMod (p ^ 0)) := inferInstance
    haveI : Subsingleton (C.rightIndex → ZMod (p ^ 0)) := inferInstance
    exact ⟨{
      leftCoordinateEquiv :=
        AddEquiv.ofBijective
          (0 : (C.leftIndex → ZMod (p ^ 0)) →+ Additive D.commutatorSubgroup)
          ⟨fun x y _ => Subsingleton.elim x y,
            fun y => ⟨0, Subsingleton.elim _ _⟩⟩
      rightCoordinateEquiv :=
        AddEquiv.ofBijective
          (0 : (C.rightIndex → ZMod (p ^ 0)) →+ Additive D.fixedSubgroup)
          ⟨fun x y _ => Subsingleton.elim x y,
            fun y => ⟨0, Subsingleton.elim _ _⟩⟩ }⟩

/-- Source-core separate coordinates on the two action factors.

This is now a checked wrapper around the fixed-split `hR`/`hC` source core.
The ambient split is chosen by the existing coordinate-split construction, and
the two factor coordinate equivalences are supplied by the checked factor
coordinate theorem. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_factor_coordinate_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupFactorCoordinateData
        (G := G) (V := V) (p := p) A L D) := by
  classical
  rcases exists_homocyclic_frattini_cover_subgroup_coordinate_split_of_fixed_decomposition
      (G := G) (V := V) (p := p) A L D with
    ⟨C⟩
  rcases exists_homocyclic_frattini_cover_subgroup_factor_coordinate_equivs
      (G := G) (V := V) (p := p) A L D C with
    ⟨H⟩
  exact ⟨H.toFactorCoordinateData⟩

/-- Arbitrary product coordinates whose two coordinate axes land in the action
subgroups.

This is now a checked wrapper around separate factor coordinates: the
complement product equivalence builds the product-coordinate equivalence, and
the axis membership follows from the resulting product decomposition. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_product_coordinate_subgroup_membership_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupMembershipData
        (G := G) (V := V) (p := p) A L D) := by
  classical
  rcases exists_homocyclic_frattini_cover_subgroup_factor_coordinate_data
      (G := G) (V := V) (p := p) A L D with
    ⟨H⟩
  exact ⟨H.toProductCoordinateDecompositionData.toSubgroupMembershipData⟩


/-- A named adapted product-coordinate package used by the checked rectangular
wrappers below. -/
public noncomputable def homocyclicFrattiniCoverSubgroupProductCoordinateSubgroupMembershipDataChoice
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateSubgroupMembershipData
      (G := G) (V := V) (p := p) A L D :=
  Classical.choice
    (exists_homocyclic_frattini_cover_subgroup_product_coordinate_subgroup_membership_data
      (G := G) (V := V) (p := p) A L D)


public noncomputable def homocyclicFrattiniCoverSubgroupProductCoordinateBottomRightDataChoice
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightData
      (G := G) (V := V) (p := p) A L D :=
  let H :=
    homocyclicFrattiniCoverSubgroupProductCoordinateSubgroupMembershipDataChoice
      (G := G) (V := V) (p := p) A L D
  {
    productCoordinates := H.productCoordinates
    bottomRightIdentity := H.rightInFixedSubgroup.toRightFixed.toBottomRightIdentity }


public theorem
    exists_homocyclic_frattini_cover_subgroup_product_coordinate_choice_left_in_commutator_subgroup
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupProductCoordinateLeftInCommutatorSubgroup
        (G := G) (V := V) (p := p) A L D
        (homocyclicFrattiniCoverSubgroupProductCoordinateBottomRightDataChoice
          (G := G) (V := V) (p := p) A L D).productCoordinates) := by
  classical
  let H :=
    homocyclicFrattiniCoverSubgroupProductCoordinateSubgroupMembershipDataChoice
      (G := G) (V := V) (p := p) A L D
  exact ⟨H.leftInCommutatorSubgroup⟩

/-- Orbit-sum cancellation for elements of the action commutator subgroup.

This is a checked wrapper around the generic commutator orbit-sum theorem for
commutative groups, transported through the chosen product coordinates. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_product_coordinate_commutator_orbit_sum_zero
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L)
    (B : HomocyclicFrattiniCoverSubgroupProductCoordinateBottomRightData
      (G := G) (V := V) (p := p) A L D) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupProductCoordinateCommutatorOrbitSumZero
        (G := G) (V := V) (p := p) A L D B.productCoordinates) := by
  classical
  exact
    ⟨homocyclicFrattiniCoverSubgroupProductCoordinateCommutatorOrbitSumZero
      (G := G) (V := V) (p := p) (A := A) (L := L) (D := D)
      (P := B.productCoordinates)⟩

/-- Lower ambient left-factor cancellation for the named product coordinates.

This is now a checked assembly from the left-factor commutator membership and
the generic commutator orbit-sum cancellation. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_product_coordinate_choice_left_sum_zero_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupProductCoordinateLeftSumZeroData
        (G := G) (V := V) (p := p) A L D
        (homocyclicFrattiniCoverSubgroupProductCoordinateBottomRightDataChoice
          (G := G) (V := V) (p := p) A L D)) := by
  classical
  let B :=
    homocyclicFrattiniCoverSubgroupProductCoordinateBottomRightDataChoice
      (G := G) (V := V) (p := p) A L D
  rcases exists_homocyclic_frattini_cover_subgroup_product_coordinate_choice_left_in_commutator_subgroup
      (G := G) (V := V) (p := p) A L D with
    ⟨Hleft⟩
  rcases exists_homocyclic_frattini_cover_subgroup_product_coordinate_commutator_orbit_sum_zero
      (G := G) (V := V) (p := p) A L D B with
    ⟨Hcomm⟩
  exact ⟨{
    leftSumZero := Hleft.toLeftSumZero Hcomm }⟩

/-- Lower product-coordinate upper-left zero-sum package for the named
bottom-right coordinate package.

This is now a checked wrapper around the ambient left-factor cancellation
source statement. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_product_coordinate_choice_top_left_sum_zero_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupProductCoordinateTopLeftSumZeroData
        (G := G) (V := V) (p := p) A L D
        (homocyclicFrattiniCoverSubgroupProductCoordinateBottomRightDataChoice
          (G := G) (V := V) (p := p) A L D)) := by
  classical
  rcases exists_homocyclic_frattini_cover_subgroup_product_coordinate_choice_left_sum_zero_data
      (G := G) (V := V) (p := p) A L D with
    ⟨H⟩
  exact ⟨H.toTopLeftSumZeroData⟩

/-- Lower product-coordinate package for one subgroup after the action-side
decomposition has been chosen.

This is now a checked wrapper around the product-coordinate equivalence and the
two source action identities needed to recover `Pl`, `Pr`, `Pu`, and `Pd`. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_product_coordinate_data
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupProductCoordinateData
        (G := G) (V := V) (p := p) A L D) := by
  classical
  let B :=
    homocyclicFrattiniCoverSubgroupProductCoordinateBottomRightDataChoice
      (G := G) (V := V) (p := p) A L D
  rcases exists_homocyclic_frattini_cover_subgroup_product_coordinate_choice_top_left_sum_zero_data
      (G := G) (V := V) (p := p) A L D with
    ⟨H11⟩
  exact ⟨B.toProductCoordinateData H11⟩

/-- Lower rectangular linear maps for one subgroup after the action-side
decomposition has been chosen.

This is now a checked wrapper around the source-side product-coordinate data:
the four maps corresponding to `Pl`, `Pr`, `Pu`, and `Pd` are transported
product inclusions and projections. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_chosen_split_rectangular_linear_maps
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupChosenSplitRectangularLinearMaps
        (G := G) (V := V) (p := p) A L D) := by
  classical
  rcases exists_homocyclic_frattini_cover_subgroup_product_coordinate_data
      (G := G) (V := V) (p := p) A L D with
    ⟨P⟩
  exact ⟨P.toChosenSplitRectangularLinearMaps⟩


/-- Lower source-core rectangular block matrices for one subgroup after the
action-side decomposition has been chosen.

This is now a checked wrapper around the source-side linear maps: the inverse
block equation, lower-right identity, and upper-left zero-sum are converted to
matrix statements by `LinearMap.toMatrix'`. -/
public theorem
    exists_homocyclic_frattini_cover_subgroup_chosen_split_rectangular_block_matrices
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V] [Fintype G]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    Nonempty
      (HomocyclicFrattiniCoverSubgroupChosenSplitRectangularBlockMatrices
        (G := G) (V := V) (p := p) A L D) := by
  classical
  rcases exists_homocyclic_frattini_cover_subgroup_chosen_split_rectangular_linear_maps
      (G := G) (V := V) (p := p) A L D with
    ⟨M⟩
  exact ⟨{
    coordinateSplit := M.coordinateSplit
    rectangularMatrices := M.linearMaps.toRectangularBlockMatrices }⟩


public theorem
    exists_rectangular_reindexed_block_trace_data_of_homocyclic_frattini_cover_with_fixed_decomposition
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    Nonempty
      (RectangularReindexedBlockTraceData
        (G := G) (κ := L.toCommonMatrixLift.matrixIndex)
        A (p ^ e) L.toCommonMatrixLift.matrixLift
        (fixedSubspaceFinrank (G := G) (V := V) (p := p) A)) := by
  classical
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  rcases exists_homocyclic_frattini_cover_subgroup_chosen_split_rectangular_block_matrices
      (G := G) (V := V) (p := p) A L D with
    ⟨M⟩
  exact ⟨M.rectangularMatrices.toRectangularReindexedBlockTraceData⟩

/-- Source-core rectangular block data for one subgroup after the action-side
decomposition has been chosen.

This is now a checked wrapper around the fixed-decomposition source core:
the coprime/minimality hypotheses and positive height are used upstream to
construct `L` and `D`, not in the raw rectangular block package itself. -/
public theorem
    exists_rectangular_reindexed_block_trace_data_of_homocyclic_frattini_cover_with_decomposition_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e)
    (D : HomocyclicFrattiniCoverSubgroupActionDecomposition
      (G := G) (V := V) (p := p) A L) :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    Nonempty
      (RectangularReindexedBlockTraceData
        (G := G) (κ := L.toCommonMatrixLift.matrixIndex)
        A (p ^ e) L.toCommonMatrixLift.matrixLift
        (fixedSubspaceFinrank (G := G) (V := V) (p := p) A)) := by
  classical
  exact
    exists_rectangular_reindexed_block_trace_data_of_homocyclic_frattini_cover_with_fixed_decomposition
      (G := G) (V := V) (p := p) A L D


public theorem
    exists_rectangular_reindexed_block_trace_data_of_homocyclic_frattini_cover_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    letI : Fintype L.toCommonMatrixLift.matrixIndex :=
      L.toCommonMatrixLift.instFintypeMatrixIndex
    Nonempty
      (RectangularReindexedBlockTraceData
        (G := G) (κ := L.toCommonMatrixLift.matrixIndex)
        A (p ^ e) L.toCommonMatrixLift.matrixLift
        (fixedSubspaceFinrank (G := G) (V := V) (p := p) A)) := by
  classical
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  rcases exists_homocyclic_frattini_cover_subgroup_action_decomposition_prime_power
      (G := G) (V := V) (p := p) hcop A L with
    ⟨D⟩
  rcases
      exists_rectangular_reindexed_block_trace_data_of_homocyclic_frattini_cover_with_decomposition_prime_power
      (G := G) (V := V) (p := p) A L D with
    ⟨B⟩
  exact ⟨B⟩


public theorem
    exists_homocyclic_frattini_cover_rectangular_common_lift_block_data_of_cover_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (A : Subgroup G)
    [DecidablePred (fun g : G => g ∈ A)]
    {e : ℕ}
    (L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e) :
    Nonempty
      (HomocyclicFrattiniCoverRectangularCommonLiftBlockData
        (G := G) (V := V) (p := p) A L) := by
  classical
  letI : Fintype L.toCommonMatrixLift.matrixIndex := L.toCommonMatrixLift.instFintypeMatrixIndex
  rcases exists_rectangular_reindexed_block_trace_data_of_homocyclic_frattini_cover_prime_power
      (G := G) (V := V) (p := p) hcop A L with
    ⟨D⟩
  exact ⟨{ blockData := D }⟩

/-- Homocyclic Frattini cover together with a provider for all rectangular
block-family data.

This assembles the two source phases: first construct the Frattini-stated cover,
then provide the one-subgroup `Pl Pr Pu Pd` block data for each subgroup. -/
public theorem
    exists_homocyclic_frattini_cover_linear_lift_with_block_family_provider_prime_power
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    {e : ℕ} (he : 0 < e) :
    Nonempty
      (Σ L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e,
        HomocyclicFrattiniCoverRectangularCommonLiftBlockFamilyProvider
          (G := G) (V := V) (p := p) L) := by
  classical
  rcases exists_homocyclic_frattini_cover_linear_lift_prime_power
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨L⟩
  refine ⟨⟨L, ?_⟩⟩
  refine { blockData := ?_ }
  intro A
  exact Classical.choice
    (exists_homocyclic_frattini_cover_rectangular_common_lift_block_data_of_cover_prime_power
      (G := G) (V := V) (p := p) hcop A L)

/-- Homocyclic Frattini cover and rectangular block-family data produced by
the semidirect-product cover, specialized to one finite subgroup family. -/
public theorem
    exists_homocyclic_frattini_cover_rectangular_common_lift_and_block_family_prime_power
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    Nonempty
      (Σ L : HomocyclicFrattiniCoverLinearLift (G := G) (V := V) (p := p) e,
        HomocyclicFrattiniCoverRectangularCommonLiftBlockFamily
          (G := G) (V := V) (ι := ι) (p := p) A L) := by
  classical
  rcases exists_homocyclic_frattini_cover_linear_lift_with_block_family_provider_prime_power
      (G := G) (V := V) (p := p) hcop hminv he with
    ⟨⟨L, provider⟩⟩
  exact ⟨⟨L, provider.blockFamily (A := A)⟩⟩


public theorem exists_homocyclic_cover_rectangular_common_lift_and_block_family_prime_power
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    Nonempty
      (Σ L : HomocyclicCoverLinearLift (G := G) (V := V) (p := p) e,
        HomocyclicCoverRectangularCommonLiftBlockFamily
          (G := G) (V := V) (ι := ι) (p := p) A L) := by
  classical
  rcases exists_homocyclic_frattini_cover_rectangular_common_lift_and_block_family_prime_power
      (G := G) (V := V) (ι := ι) (p := p) hcop hminv A he with
    ⟨⟨L, D⟩⟩
  exact ⟨⟨L.toHomocyclicCoverLinearLift,
    D.toHomocyclicCoverRectangularCommonLiftBlockFamily⟩⟩


public theorem
    exists_homocyclic_quotient_rectangular_common_lift_and_block_family_prime_power
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    Nonempty
      (Σ L : HomocyclicQuotientLinearLift (G := G) (V := V) (p := p) e,
        HomocyclicQuotientRectangularCommonLiftBlockFamily
          (G := G) (V := V) (ι := ι) (p := p) A L) := by
  classical
  rcases exists_homocyclic_cover_rectangular_common_lift_and_block_family_prime_power
      (G := G) (V := V) (ι := ι) (p := p) hcop hminv A he with
    ⟨⟨L, D⟩⟩
  exact ⟨⟨L.toHomocyclicQuotientLinearLift,
    D.toHomocyclicQuotientRectangularCommonLiftBlockFamily⟩⟩


public theorem exists_homocyclic_rectangular_common_lift_and_block_family_prime_power
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    Nonempty
      (Σ L : HomocyclicCommonLinearLift (G := G) (V := V) (p := p) e,
        HomocyclicRectangularCommonLiftBlockFamily
          (G := G) (V := V) (ι := ι) (p := p) A L) := by
  classical
  rcases
      exists_homocyclic_quotient_rectangular_common_lift_and_block_family_prime_power
        (G := G) (V := V) (ι := ι) (p := p) hcop hminv A he with
    ⟨⟨L, D⟩⟩
  exact ⟨⟨L.toHomocyclicCommonLinearLift,
    D.toHomocyclicRectangularCommonLiftBlockFamily⟩⟩


public theorem exists_homocyclic_rectangular_common_lift_block_data_prime_power
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    Nonempty
      (HomocyclicRectangularCommonLiftBlockData
        (G := G) (V := V) (ι := ι) (p := p) A e) := by
  classical
  rcases exists_homocyclic_rectangular_common_lift_and_block_family_prime_power
      (G := G) (V := V) (ι := ι) (p := p) hcop hminv A he with
    ⟨⟨L, D⟩⟩
  exact ⟨{
    homocyclicLift := L
    blockFamily := D.toRectangularCommonMatrixLiftBlockFamily }⟩


public theorem exists_rectangular_common_matrix_lift_block_data_prime_power
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    Nonempty
      (RectangularCommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e) := by
  classical
  rcases exists_homocyclic_rectangular_common_lift_block_data_prime_power
      (G := G) (V := V) (ι := ι) (p := p) hcop hminv A he with
    ⟨D⟩
  exact ⟨D.toRectangularCommonMatrixLiftBlockData A⟩


public theorem exists_common_matrix_lift_block_data_prime_power
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    Nonempty (CommonMatrixLiftBlockData (G := G) (V := V) (ι := ι) (p := p) A e) := by
  classical
  rcases exists_rectangular_common_matrix_lift_block_data_prime_power
      (G := G) (V := V) (ι := ι) (p := p) hcop hminv A he with
    ⟨D⟩
  exact ⟨D.toCommonMatrixLiftBlockData A⟩


public theorem exists_matrix_trace_model_prime_power_of_elementaryAbelian_minimal_pos
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    ∃ κ : Type u, ∃ hκ : Fintype κ,
      letI : Fintype κ := hκ
      ∃ M : G → Matrix κ κ (ZMod (p ^ e)),
        ∀ i : ι,
          Matrix.trace (∑ a : A i, M (a : G)) =
            (fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i) *
              Nat.card (A i) : ZMod (p ^ e)) := by
  classical
  rcases exists_common_matrix_lift_block_data_prime_power
      (G := G) (V := V) (ι := ι) (p := p) hcop hminv A he with
    ⟨D⟩
  exact CommonMatrixLiftBlockData.exists_matrix_trace_model (A := A) D


public theorem exists_trace_sum_function_prime_power_of_elementaryAbelian_minimal_pos
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    {e : ℕ} (he : 0 < e) :
    ∃ F : G → ZMod (p ^ e),
      ∀ i : ι,
        (∑ a : A i, F (a : G)) =
          (fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i) *
            Nat.card (A i) : ZMod (p ^ e)) := by
  classical
  rcases exists_matrix_trace_model_prime_power_of_elementaryAbelian_minimal_pos
      (G := G) (V := V) (ι := ι) (p := p) hcop hminv A he with
    ⟨κ, hκ, M, htrace⟩
  letI : Fintype κ := hκ
  exact exists_trace_sum_function_of_matrix_trace_model
    (A := A)
    (r := fun i => fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i))
    (q := p ^ e) M htrace

/-- Trace data needed for one prime-power congruence in the elementary-abelian
minimal branch, including the trivial modulus-one case. -/
public theorem exists_trace_sum_function_prime_power_of_elementaryAbelian_minimal
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (e : ℕ) :
    ∃ F : G → ZMod (p ^ e),
      ∀ i : ι,
        (∑ a : A i, F (a : G)) =
          (fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i) *
            Nat.card (A i) : ZMod (p ^ e)) := by
  classical
  rcases e with _ | e
  · refine ⟨fun _ => 0, ?_⟩
    intro i
    change (∑ a : A i, (0 : ZMod 1)) =
      (fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i) *
        Nat.card (A i) : ZMod 1)
    subsingleton
  · exact
      exists_trace_sum_function_prime_power_of_elementaryAbelian_minimal_pos
        (G := G) (V := V) (ι := ι) (p := p) hcop hminv A (e := e.succ) e.succ_pos


public theorem fixedSubspace_finrank_sum_modEq_prime_power_of_coeff_sum_eq_elementaryAbelian_minimal
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (m n : ι → ℕ)
    (hcoeff : ∀ g : G,
      (∑ i : ι, if g ∈ A i then m i else 0) =
        ∑ i : ι, if g ∈ A i then n i else 0)
    (e : ℕ) :
    letI : CommGroup V := IsMulCommutative.instCommGroup
    (∑ i : ι,
      letI : MulDistribMulAction (↥(A i)) V :=
        MulDistribMulAction.compHom V (A i).subtype
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
              (A := ↥(A i)) (G := V) (p := p) :
                Representation (ZMod p) (↥(A i)) (Additive V)).fixedSubspace
            (⊤ : Subgroup (↥(A i)))) *
        (m i * Nat.card (A i))) ≡
      (∑ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Module.finrank (ZMod p)
            ↥((Theory.Representation.ofElementaryAbelianAction
                (A := ↥(A i)) (G := V) (p := p) :
                  Representation (ZMod p) (↥(A i)) (Additive V)).fixedSubspace
              (⊤ : Subgroup (↥(A i)))) *
          (n i * Nat.card (A i))) [MOD p ^ e] := by
  classical
  letI : CommGroup V := IsMulCommutative.instCommGroup
  letI : Fintype G := Fintype.ofFinite G
  let r : ι → ℕ := fun i =>
    fixedSubspaceFinrank (G := G) (V := V) (p := p) (A i)
  obtain ⟨F, hF⟩ :=
    exists_trace_sum_function_prime_power_of_elementaryAbelian_minimal
      (G := G) (V := V) (ι := ι) (p := p) hcop hminv A e
  simpa [r, fixedSubspaceFinrank] using
    subgroup_weighted_sum_nat_modEq_of_coeff_sum_eq
      (A := A) (m := m) (n := n) (r := r) (q := p ^ e) (F := F) hcoeff hF


public theorem fixedSubspace_finrank_sum_eq_of_coeff_sum_eq_elementaryAbelian_minimal
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hminv : ∀ N : Subgroup V, N.Normal → IsInvariant G V N → N ≠ ⊥ → N = ⊤)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (m n : ι → ℕ)
    (hcoeff : ∀ g : G,
      (∑ i : ι, if g ∈ A i then m i else 0) =
        ∑ i : ι, if g ∈ A i then n i else 0) :
    letI : CommGroup V := IsMulCommutative.instCommGroup
    (∑ i : ι,
      letI : MulDistribMulAction (↥(A i)) V :=
        MulDistribMulAction.compHom V (A i).subtype
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
              (A := ↥(A i)) (G := V) (p := p) :
                Representation (ZMod p) (↥(A i)) (Additive V)).fixedSubspace
            (⊤ : Subgroup (↥(A i)))) *
        (m i * Nat.card (A i))) =
      ∑ i : ι,
        letI : MulDistribMulAction (↥(A i)) V :=
          MulDistribMulAction.compHom V (A i).subtype
        Module.finrank (ZMod p)
            ↥((Theory.Representation.ofElementaryAbelianAction
                (A := ↥(A i)) (G := V) (p := p) :
                  Representation (ZMod p) (↥(A i)) (Additive V)).fixedSubspace
              (⊤ : Subgroup (↥(A i)))) *
          (n i * Nat.card (A i)) := by
  classical
  letI : CommGroup V := IsMulCommutative.instCommGroup
  exact
    nat_eq_of_modEq_prime_power_all (Fact.out : Nat.Prime p).one_lt
      (fun e =>
        fixedSubspace_finrank_sum_modEq_prime_power_of_coeff_sum_eq_elementaryAbelian_minimal
          (G := G) (V := V) (ι := ι) (p := p) hcop hminv A m n hcoeff e)

/-- Wielandt's fixed point theorem in product form.

For a solvable finite group `V` acted on coprimely by `G`, any integral relation
between subgroup sums in `ℤ[G]` gives the corresponding product relation between
fixed-point subgroup cardinalities. This is HB XI, Theorem 12.4 in the form used
by Peterfalvi `(9.1)`.
-/
public theorem fixedPointSubgroup_product_card_eq_of_coeff_sum_eq
    {G V ι : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype ι]
    (hcop : Nat.Coprime (Nat.card V) (Nat.card G))
    (hsolv : IsSolvable V)
    (A : ι → Subgroup G)
    [∀ (g : G) (i : ι), Decidable (g ∈ A i)]
    (m n : ι → ℕ)
    (hcoeff : ∀ g : G,
      (∑ i : ι, if g ∈ A i then m i else 0) =
        ∑ i : ι, if g ∈ A i then n i else 0) :
    (∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (m i * Nat.card (A i))) =
      ∏ i : ι,
        letI : MulDistribMulAction (↥(A i)) V := MulDistribMulAction.compHom V (A i).subtype
        Nat.card (fixedPointSubgroup (↥(A i)) V) ^ (n i * Nat.card (A i)) := by
  classical
  exact
    fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_of_elementaryAbelian_minimal
      (G := G) (V := V) (ι := ι) hcop hsolv A m n hcoeff
      (by
        intro M _ _ _ hNontriv p _ _ hcopM hminvM hcoeffM
        exact
          fixedPointSubgroup_product_card_eq_of_coeff_sum_eq_elementaryAbelian_of_finrank_sum_eq
            (G := G) (V := M) (ι := ι) A m n
            (p := p)
            (fixedSubspace_finrank_sum_eq_of_coeff_sum_eq_elementaryAbelian_minimal
              (G := G) (V := M) (ι := ι) (p := p) hcopM hminvM A m n hcoeffM))

/-- Wielandt fixed-point theorem in actor-internal form.

This is the exact elementary-abelian chief-factor endpoint needed after the PF9
wrappers have reduced the source proof to the cited HB XI, Theorem 12.4. -/
public theorem fixedPointSubgroup_card_identity_kernel_fixed_bot_of_frobenius
    {A M : Type u} [Group A] [Finite A] [Group M] [Finite M] [Nontrivial M]
    (K R : Subgroup A)
    [MulDistribMulAction A M]
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card A))
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hKbot :
      letI : MulDistribMulAction (↥K) M := MulDistribMulAction.compHom M K.subtype
      fixedPointSubgroup (↥K) M = ⊥) :
    letI : MulDistribMulAction (↥R) M := MulDistribMulAction.compHom M R.subtype
    Nat.card M = Nat.card (fixedPointSubgroup (↥R) M) ^ Nat.card R := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : MulDistribMulAction (↥R) M := MulDistribMulAction.compHom M R.subtype
  have hsolvM : IsSolvable M :=
    isSolvable_of_comm fun x y => (IsMulCommutative.is_comm (M := M)).comm x y
  have hprod :=
    fixedPointSubgroup_product_card_eq_of_coeff_sum_eq
      (G := A) (V := M) (ι := FrobeniusProductIndex K) hcop hsolvM
      (frobeniusProductSubgroup K R)
      (frobeniusProductLeftCoeff K)
      (frobeniusProductRightCoeff K)
      (frobeniusProduct_coeff_sum_eq K R hfrob)
  exact
    fixedPointSubgroup_card_identity_kernel_fixed_bot_of_frobenius_of_product_card_eq
      (A := A) (M := M) K R hKbot hprod

/-- Wielandt fixed-point theorem in the elementary-abelian form used by
Peterfalvi `(9.1)`.

If `UE = U ⋊ E` is the Frobenius actor from the source, `M` is a nontrivial
elementary abelian group for the coprime `UE`-action, and `C_M(U) = 1`, then
`|M| = |C_M(E)| ^ |E|`.
-/
public theorem fixedPointSubgroup_complement_card_identity_kernel_fixed_bot
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
      MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
    Nat.card M = Nat.card (fixedPointSubgroup (↥(E.subgroupOf UE)) M) ^ Nat.card E := by
  classical
  let K : Subgroup UE := U.subgroupOf UE
  let R : Subgroup UE := E.subgroupOf UE
  have hfrobUE : IsFrobeniusGroupWithKernelComplement K R := by
    simpa [K, R] using
      section12FrobeniusJoinWithKernel_subgroupOf_complementIn UE U E hcomp hfrob
  have hKbot :
      letI : MulDistribMulAction (↥K) M := MulDistribMulAction.compHom M K.subtype
      fixedPointSubgroup (↥K) M = ⊥ := by
    have hUeq :
        fixedPointSubgroup (↥U) M =
          letI : MulDistribMulAction (↥(U.subgroupOf UE)) M :=
            MulDistribMulAction.compHom M (U.subgroupOf UE).subtype
          fixedPointSubgroup (↥(U.subgroupOf UE)) M :=
      fixedPointSubgroup_eq_subgroupOf_of_compatible UE U hcomp.1 hUcompat
    simpa [K, hUbot] using hUeq.symm
  have hRcard : Nat.card R = Nat.card E := by
    simpa [R] using natCard_subgroupOf_eq E UE hcomp.2.1
  have hcore :=
    fixedPointSubgroup_card_identity_kernel_fixed_bot_of_frobenius
      (A := UE) (M := M) K R hfrobUE hcop (p := p) hKbot
  simpa [R, hRcard] using hcore

/-- Fixed-subspace rank identity for the complement when the kernel has trivial
fixed points. -/
public theorem fixedSubspace_complement_finrank_identity_kernel_fixed_bot
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    letI : MulDistribMulAction (↥(E.subgroupOf UE)) M :=
      MulDistribMulAction.compHom M (E.subgroupOf UE).subtype
    Module.finrank (ZMod p) (Additive M) =
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
            (A := E.subgroupOf UE) (G := M) (p := p) :
              Representation (ZMod p) (E.subgroupOf UE) (Additive M)).fixedSubspace
          (⊤ : Subgroup (E.subgroupOf UE))) *
        Nat.card E := by
  classical
  letI : CommGroup M := IsMulCommutative.instCommGroup
  exact
    fixedSubspace_complement_finrank_identity_of_card_identity
      (UE := UE) (E := E) (M := M) (p := p)
      (fixedPointSubgroup_complement_card_identity_kernel_fixed_bot
        (p := p) UE U E hcomp hfrob hcop hUcompat hUbot)

/-- Reduced fixed-subspace rank identity in the branch where the kernel has
trivial fixed points. -/
public theorem fixedSubspace_finrank_identity_kernel_fixed_bot_reduced
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hUbot : fixedPointSubgroup (↥U) M = ⊥) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p) (Additive M) * Nat.card U =
    ∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p) :
                Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G)) := by
  classical
  letI : CommGroup M := IsMulCommutative.instCommGroup
  letI : Fintype U := Fintype.ofFinite U
  exact
    fixedSubspace_finrank_identity_kernel_fixed_bot_reduced_of_complement_finrank
      (p := p) UE U E hEact hcomp hEcompat
      (fixedSubspace_complement_finrank_identity_kernel_fixed_bot
        (p := p) UE U E hcomp hfrob hcop hUcompat hUbot)

/-- Fixed-subspace rank identity for a minimal nontrivial invariant
elementary-abelian actor factor. -/
public theorem fixedSubspace_finrank_identity_minimal_invariant
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant UE M N → N ≠ ⊥ → N = ⊤) :
    letI : CommGroup M := IsMulCommutative.instCommGroup
    letI : Fintype U := Fintype.ofFinite U
    Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := UE) (G := M) (p := p) :
          Representation (ZMod p) UE (Additive M)).fixedSubspace
          (⊤ : Subgroup UE)) * Nat.card UE +
      Module.finrank (ZMod p) (Additive M) * Nat.card U =
    (∑ u : U,
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      Module.finrank (ZMod p)
          ↥((Theory.Representation.ofElementaryAbelianAction
              (A := E.conjBy (u : G)) (G := M) (p := p) :
                Representation (ZMod p) (E.conjBy (u : G)) (Additive M)).fixedSubspace
            (⊤ : Subgroup (E.conjBy (u : G)))) *
        Nat.card (E.conjBy (u : G))) +
      Module.finrank (ZMod p)
        ↥((Theory.Representation.ofElementaryAbelianAction (A := U) (G := M) (p := p) :
          Representation (ZMod p) U (Additive M)).fixedSubspace
          (⊤ : Subgroup U)) * Nat.card U := by
  classical
  letI : CommGroup M := IsMulCommutative.instCommGroup
  exact
    fixedSubspace_finrank_identity_minimal_invariant_of_kernel_fixed_bot_case
      (p := p) UE U E hEact hcomp hfrob hUcompat hEcompat hminv
      (fixedSubspace_finrank_identity_kernel_fixed_bot_reduced
        (p := p) UE U E hEact hcomp hfrob hcop hUcompat hEcompat)

/-- Fixed-point product identity for a minimal invariant elementary-abelian
actor factor. -/
public theorem fixedPointSubgroup_product_identity_action_elementaryAbelian_minimal_invariant
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M] [Nontrivial M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p M]
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant UE M N → N ≠ ⊥ → N = ⊤) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      fixedPointSubgroup_conjBy_action_product U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  exact
    fixedPointSubgroup_product_identity_action_elementaryAbelian_of_finrank_identity
      (p := p) UE U E hEact
      (fixedSubspace_finrank_identity_minimal_invariant
        (p := p) UE U E hEact hcomp hfrob hcop hUcompat hEcompat hminv)

/-- Fixed-point product identity for a minimal invariant solvable actor factor. -/
public theorem fixedPointSubgroup_product_identity_action_chiefFactor
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hsolvM : IsSolvable M)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m)
    (hminv : ∀ N : Subgroup M, N.Normal → IsInvariant UE M N → N ≠ ⊥ → N = ⊤) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      fixedPointSubgroup_conjBy_action_product U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  exact
    fixedPointSubgroup_product_identity_action_chiefFactor_of_elementaryAbelian
      UE U E hEact hsolvM hminv
      (fun {p} _ _ _ =>
        fixedPointSubgroup_product_identity_action_elementaryAbelian_minimal_invariant
          (p := p) UE U E hEact hcomp hfrob hcop hUcompat hEcompat hminv)

/-- Fixed-point product identity for an explicit Frobenius actor action on a
finite solvable group. -/
public theorem fixedPointSubgroup_product_identity_action
    {G M : Type u} [Group G] [Finite G] [Group M] [Finite M]
    (UE U E : Subgroup G)
    [MulDistribMulAction UE M] [MulDistribMulAction U M]
    (hEact : ∀ u : U, MulDistribMulAction (↥(E.conjBy (u : G))) M)
    (hcomp : section12ComplementIn UE U E)
    (hfrob : section12FrobeniusJoinWithKernel U E)
    (hsolvM : IsSolvable M)
    (hcop : Nat.Coprime (Nat.card M) (Nat.card UE))
    (hUcompat : ∀ (u : U) (m : M),
      u • m = (⟨(u : G), hcomp.1 u.2⟩ : UE) • m)
    (hEcompat : ∀ (u : U) (e : E.conjBy (u : G)) (m : M),
      letI : MulDistribMulAction (↥(E.conjBy (u : G))) M := hEact u
      e • m =
        (⟨(e : G), section12ComplementIn_conj_complement_le UE U E hcomp u e.2⟩ :
          UE) • m) :
    letI : Fintype U := Fintype.ofFinite U
    Nat.card (fixedPointSubgroup (↥UE) M) ^ Nat.card UE *
        Nat.card M ^ Nat.card U =
      fixedPointSubgroup_conjBy_action_product U E hEact *
        Nat.card (fixedPointSubgroup (↥U) M) ^ Nat.card U := by
  classical
  exact
    fixedPointSubgroup_product_identity_action_of_chiefFactor
      UE U E hEact hcomp hsolvM hcop hUcompat hEcompat
      (fun M' _ _ _ _ hEact' hsolvM' hcop' hUcompat' hEcompat' hminv =>
        fixedPointSubgroup_product_identity_action_chiefFactor
          UE U E hEact' hcomp hfrob hsolvM' hcop' hUcompat' hEcompat' hminv)

end CFSG.Wielandt
