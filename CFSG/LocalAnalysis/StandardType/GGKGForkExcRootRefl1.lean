module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylReflectionOfFixedPoints
public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootSpace CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix Polynomial Module

theorem ggKGEr_zeta_zpow_eq {L : Type} [Field L] {p : ℕ} [NeZero p] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) (N : ℤ) (z : ZMod p) (h : (N : ZMod p) = z) :
    ζ ^ N = ζ ^ z.val := by
  have hmod : N ≡ (z.val : ℤ) [ZMOD p] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    rw [h]
    push_cast
    rw [ZMod.natCast_zmod_val]
  have h1 : ζ ^ N = ζ ^ (z.val : ℤ) :=
    CFSG.RankThree.PartOne.KLR.zpow_eq_zpow_of_modEq hζ.pow_eq_one hmod
  rwa [zpow_natCast] at h1

noncomputable def ggKGEr_tupleOf {τ : Tag} {K : Type} [Field K] {p : ℕ}
    (ζ : (AlgebraicClosure K)ˣ) (y : Fin τ.rank → ZMod p) :
    Fin τ.rank → (AlgebraicClosure K)ˣ :=
  fun i => ζ ^ (y i).val

theorem ggKGEr_tupleOf_pow {τ : Tag} {K : Type} [Field K] {p : ℕ}
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (y : Fin τ.rank → ZMod p) (i : Fin τ.rank) :
    ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y i ^ p = 1 := by
  rw [ggKGEr_tupleOf, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem ggKGEr_weylTuple_tupleOf {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) (w : WeylGroup τ)
    (y : Fin τ.rank → ZMod p) :
    weylTuple w (ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y) =
      ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ (Matrix.mulVec (Matrix.transpose
        ((weylLatticeMatrix τ w⁻¹).map (Int.castRingHom (ZMod p)))) y) := by
  funext i
  simp only [ggKGEr_tupleOf, weylTuple, rootChar]
  have h1 : ∀ j : Fin τ.rank,
      (ζ ^ (y j).val) ^ ((w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j) =
      ζ ^ (((y j).val : ℤ) * ((w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j)) := by
    intro j
    rw [show (ζ ^ (y j).val) = ζ ^ ((y j).val : ℤ) from (zpow_natCast _ _).symm, _root_.zpow_mul]
  rw [Finset.prod_congr rfl fun j _ => h1 j, Finset.prod_zpow_eq_zpow_sum]
  refine ggKGEr_zeta_zpow_eq hζ _ _ ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
    weylLatticeMatrix_apply]
  rw [Int.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [show (Int.castRingHom (ZMod p)) ((w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j) =
    ((w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) j : ZMod p) from rfl]
  exact mul_comm _ _

theorem ggKGEr_tupleOf_injective {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ) := by
  intro y y' h
  funext i
  have h2 : ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y i =
      ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y' i := congrFun h i
  simp only [ggKGEr_tupleOf] at h2
  have hlt : (y i).val < p := ZMod.val_lt _
  have hlt' : (y' i).val < p := ZMod.val_lt _
  exact ZMod.val_injective p (hζ.pow_inj hlt hlt' h2)

theorem ggKGEr_tupleOf_surjective {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    ∀ b : {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ i, b i ^ p = 1},
      ∃ y, ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y =
        (b : Fin τ.rank → (AlgebraicClosure K)ˣ) := by
  rintro ⟨b, hb⟩
  choose k hklt hk using fun i =>
    IsPrimitiveRoot.eq_pow_of_pow_eq_one (IsPrimitiveRoot.coe_units_iff.mpr hζ)
      (show (((b i : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ^ p = 1 by
        rw [← Units.val_pow_eq_pow_val, hb i, Units.val_one])
  refine ⟨fun i => (k i : ZMod p), ?_⟩
  funext i
  simp only [ggKGEr_tupleOf]
  rw [ZMod.val_natCast_of_lt (hklt i)]
  exact Units.ext (hk i)

noncomputable def ggKGEr_tupleFun {τ : Tag} {K : Type} [Field K] {p : ℕ}
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    (Fin τ.rank → ZMod p) → {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ i, b i ^ p = 1} :=
  fun y => ⟨ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y,
    ggKGEr_tupleOf_pow (τ := τ) (K := K) (p := p) ζ hζ y⟩

theorem ggKGEr_tupleFun_injective {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (ggKGEr_tupleFun (τ := τ) (K := K) (p := p) ζ hζ) :=
  fun y y' h => ggKGEr_tupleOf_injective ζ hζ (congrArg Subtype.val h)

theorem ggKGEr_tupleFun_surjective {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    Function.Surjective (ggKGEr_tupleFun (τ := τ) (K := K) (p := p) ζ hζ) := by
  rintro ⟨b, hb⟩
  obtain ⟨y, hy⟩ := ggKGEr_tupleOf_surjective ζ hζ ⟨b, hb⟩
  exact ⟨y, Subtype.ext hy⟩

noncomputable def ggKGEr_tupleEquiv {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) :
    (Fin τ.rank → ZMod p) ≃
      {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ i, b i ^ p = 1} :=
  Equiv.ofBijective (ggKGEr_tupleFun (τ := τ) (K := K) (p := p) ζ hζ) (by
    refine ⟨?_, ?_⟩
    · exact ggKGEr_tupleFun_injective ζ hζ
    · exact ggKGEr_tupleFun_surjective ζ hζ)

theorem ggKGEr_tupleEquiv_apply {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p) (y : Fin τ.rank → ZMod p) :
    ((ggKGEr_tupleEquiv (τ := τ) (K := K) (p := p) ζ hζ) y).val =
      ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y := by
  change (ggKGEr_tupleFun (τ := τ) (K := K) (p := p) ζ hζ y).val =
    ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y
  rfl

theorem ggKGEr_fix_iff {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p]
    (ζ : (AlgebraicClosure K)ˣ) (hζ : IsPrimitiveRoot ζ p)
    (w : WeylGroup τ) (y : Fin τ.rank → ZMod p) :
    (weylTuple w (ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y) =
        ggKGEr_tupleOf (τ := τ) (K := K) (p := p) ζ y) ↔
      Matrix.mulVec (Matrix.transpose
        ((weylLatticeMatrix τ w⁻¹).map (Int.castRingHom (ZMod p)))) y = y := by
  constructor
  · intro h
    rw [ggKGEr_weylTuple_tupleOf (τ := τ) (K := K) (p := p) ζ hζ w y] at h
    exact ggKGEr_tupleOf_injective ζ hζ h
  · intro h
    rw [ggKGEr_weylTuple_tupleOf (τ := τ) (K := K) (p := p) ζ hζ w y, h]

open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

noncomputable def ggKGEr_Y
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) (e : E) :
    {b : Fin τ.rank → (AlgebraicClosure K)ˣ // ∀ i, b i ^ p = 1} := by
  classical
  let hT : F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (e : ModGL τ K) * F.D.g0 ∈ torusGroup τ (AlgebraicClosure K) :=
    (mem_twistedTorusOf.1 ((F.mem_iff (e : adjointGroup τ K)).1 e.property).2).1
  let b := Classical.choose (exists_rootDiagUnit_eq_of_mem_torusGroup hT)
  refine ⟨b, ?_⟩
  have hb : rootDiagUnit τ b = F.D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0 :=
    (Classical.choose_spec (exists_rootDiagUnit_eq_of_mem_torusGroup hT)).symm
  have hbp : b ^ p = 1 := by
    apply rootDiagUnit_injective
    rw [← rootDiagUnit_pow, rootDiagUnit_one, hb]
    have hep : ((e : adjointGroup τ K) : ModGL τ K) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ((F.mem_iff (e : adjointGroup τ K)).1 e.property).1,
        Subgroup.coe_one]
    rw [show F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
        F.D.g0 = F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) *
        (F.D.g0⁻¹)⁻¹ from by group]
    rw [conj_pow, ← map_pow, hep, map_one, mul_one, mul_inv_cancel]
  intro i
  simpa using congrFun hbp i

theorem ggKGEr_Y_spec
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) (e : E) :
    rootDiagUnit τ (ggKGEr_Y F e).val =
      F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL τ K) * F.D.g0 := by
  classical
  dsimp only [ggKGEr_Y]
  exact (Classical.choose_spec (exists_rootDiagUnit_eq_of_mem_torusGroup
    ((mem_twistedTorusOf.1 ((F.mem_iff (e : adjointGroup τ K)).1 e.property).2).1))).symm

theorem exists_rootReflection_of_charpoly
    {τ : Tag} {w : WeylGroup τ} (hw : w * w = 1)
    (hch : (weylLatticeMatrix τ w).charpoly = (X - 1) ^ (τ.rank - 1) * (X + 1)) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ w = rootReflection β := by
  have hdim := finrank_ker_weylLinear_add_one hw hch
  obtain ⟨βs, hlen, hroots, hpair, hprod, hspan, -, -⟩ :=
    exceptional_Lang_Weyl_involution_orthogonal_reflections τ w (by rw [pow_two]; exact hw)
  have hdim' : finrank ℝ (minusSpace w) = 1 := by
    rw [minusSpace]
    exact hdim
  obtain ⟨c0, hc0, hinner⟩ := exists_inner_ofLattice_eq_iform τ
  have hli : LinearIndependent ℝ (fun j : Fin βs.length => ofLattice (βs.get j)) := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun j => ?_) fun i j hij => ?_
    · intro h0
      exact (hroots _ (List.get_mem _ _)).ne_zero (ofLattice_injective (h0.trans
        ofLattice_zero.symm))
    · simp only
      rw [hinner]
      have hp := List.pairwise_iff_get.1 hpair
      rcases lt_or_gt_of_ne hij with h | h
      · rw [hp i j h, Int.cast_zero, mul_zero]
      · rw [iform_comm, hp j i h, Int.cast_zero, mul_zero]
  have hspanv : Submodule.span ℝ
      (Set.range (fun j : Fin βs.length => ofLattice (βs.get j))) = minusSpace w := by
    have hrange : Set.range (fun j : Fin βs.length => ofLattice (βs.get j)) =
        ofLattice '' {β | β ∈ βs} := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨βs.get j, List.get_mem βs j, rfl⟩
      · rintro ⟨β, hβ, rfl⟩
        obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hβ
        exact ⟨j, rfl⟩
    rw [hrange]
    refine SetLike.ext fun x => ?_
    rw [mem_minusSpace]
    exact Set.ext_iff.mp hspan x
  have hcardv : βs.length = 1 := by
    have := finrank_span_eq_card hli
    rw [hspanv, hdim', Fintype.card_fin] at this
    omega
  rcases βs with _ | ⟨β, βs'⟩
  · simp at hcardv
  · rcases βs' with _ | ⟨γ, βs''⟩
    · exact ⟨β, hroots β (List.mem_cons_self ..), by simpa using hprod⟩
    · exfalso
      simp only [List.length_cons] at hcardv
      omega

theorem ggKGEr_involution_isRoot
    {τ : Tag} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hr : 0 < τ.rank)
    {w : WeylGroup τ} (hw : w * w = 1)
    (hfixT : Nat.card {y : Fin τ.rank → ZMod p // Matrix.mulVec
      (Matrix.transpose ((weylLatticeMatrix τ w).map (Int.castRingHom (ZMod p)))) y = y} =
      p ^ (τ.rank - 1)) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ w = rootReflection β := by
  have hMT2 : (Matrix.transpose (weylLatticeMatrix τ w)) *
      (Matrix.transpose (weylLatticeMatrix τ w)) = 1 := by
    rw [← Matrix.transpose_mul, weylLatticeMatrix_mul_self hw, Matrix.transpose_one]
  have hcard : Fintype.card (Fin τ.rank) = (τ.rank - 1) + 1 := by
    rw [Fintype.card_fin]; omega
  have hfixMT : Nat.card {f : Fin τ.rank → ZMod p //
      ((Matrix.transpose (weylLatticeMatrix τ w)).map (Int.castRingHom (ZMod p))) *ᵥ f = f} =
      p ^ (τ.rank - 1) := by
    convert hfixT using 2
    rw [Matrix.transpose_map]
  have hchMT := charpoly_eq_of_natCard_fixed_zmod hp2
    (Matrix.transpose (weylLatticeMatrix τ w)) hMT2 hcard hfixMT
  have hch : (weylLatticeMatrix τ w).charpoly = (X - 1) ^ (τ.rank - 1) * (X + 1) := by
    have h := Matrix.charpoly_transpose (weylLatticeMatrix τ w)
    rw [hchMT] at h
    exact h.symm
  exact exists_rootReflection_of_charpoly hw hch

theorem exists_rootReflection_of_natCard_fix_torusAct
    {τ : Tag} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hr : 0 < τ.rank) {w : WeylGroup τ} (hw : w * w = 1)
    (hfix : Nat.card {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p w x = x} =
      p ^ (τ.rank - 1)) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ w = rootReflection β := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hch := charpoly_eq_of_natCard_fixed_zmod (k := τ.rank - 1) hp2 (weylLatticeMatrix τ w)
    (weylLatticeMatrix_mul_self hw) (by rw [Fintype.card_fin]; omega)
    (by simpa only [torusAct_eq_weylMatrix_mulVec] using hfix)
  exact exists_rootReflection_of_charpoly hw hch

end CFSG.StandardType
