module

public import CFSG.LocalAnalysis.StandardType.GGIrred937F4Count
public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcLang
public import CFSG.LocalAnalysis.StandardType.GGIrred937Lattice
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
  CFSG.StandardType.ExcFrames CFSG.StandardType.ExcFramesHalf

open scoped Matrix

private lemma modMat_mul {τ : Tag} {p : ℕ} (A B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    modMat p (A * B) = modMat p A * modMat p B := by
  simp only [modMat, Matrix.map_mul]

private lemma modMat_one {τ : Tag} {p : ℕ} :
    modMat p (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) = 1 := by
  unfold modMat
  exact Matrix.map_one _ (Int.cast_zero) (Int.cast_one)

private lemma modMat_weylMatrix_eq_neg_one_F4
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian 3 E)
    (htor : ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g ∈ torusGroup Tag.F4 (AlgebraicClosure K))
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup Tag.F4 K)), x ^ 3 = 1 → x ∈ E)
    (w : WeylGroup Tag.F4) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL Tag.F4 (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ∈
      (twistedTorus (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) Fr).map
        (MulAut.conj g0).toMonoidHom) :
    modMat 3 (weylMatrix w) = -1 := by
  classical
  have hcount := f4_natCard_eq_torsion (L := AlgebraicClosure K) (p := 3) Nat.prime_three
    (by norm_num) E hE hSC w Fr hFr g0 hg0C hg0 hEin
  have hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hcard2 := ExcFramesHalf.natCard_twistedTorus_pTorsion (L := AlgebraicClosure K) (τ := Tag.F4)
    (ℓ := 2) Nat.prime_two Fr hFr (p := 3) Nat.prime_three (by norm_num) w
  have hq : ((Nat.card K : ℕ) : ZMod 3) = -1 := by
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  rw [hq] at hcard2
  have hcardE : Nat.card E = Nat.card {z : Fin Tag.F4.rank → ZMod 3 //
      (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod 3) • z} := hcount.trans hcard2
  have hcard4 : 3 ^ Tag.F4.rank ≤ Nat.card E := by
    rw [show Tag.F4.rank = 4 from rfl]
    exact card_ge_of_toral_F4_gen K hpq E hE htor hcard hSC
  have hcardpi : Nat.card (Fin Tag.F4.rank → ZMod 3) = 3 ^ Tag.F4.rank := by
    rw [Nat.card_pi]
    simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hKernel : Nat.card {z : Fin Tag.F4.rank → ZMod 3 //
      (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod 3) • z} ≤ 3 ^ Tag.F4.rank := by
    have hle := Finite.card_subtype_le (α := Fin Tag.F4.rank → ZMod 3)
      (p := fun z => (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod 3) • z)
    rw [hcardpi] at hle
    exact hle
  have htop : Nat.card {z : Fin Tag.F4.rank → ZMod 3 //
      (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod 3) • z} = 3 ^ Tag.F4.rank :=
    le_antisymm hKernel (hcardE ▸ hcard4)
  have hall : ∀ z : Fin Tag.F4.rank → ZMod 3,
      (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod 3) • z := by
    intro z
    by_contra hz
    have hlt := Finite.card_subtype_lt
      (p := fun z => (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod 3) • z) hz
    rw [htop, hcardpi] at hlt
    exact (lt_irrefl _) hlt
  ext i j
  have h := congrFun (hall (Pi.single i 1)) j
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply] at h
  rw [Pi.smul_apply, Pi.single_apply] at h
  rw [h, Matrix.neg_apply, Matrix.one_apply]
  by_cases hij : i = j
  · rw [if_pos hij.symm, if_pos hij]; ring
  · rw [if_neg (fun hji => hij hji.symm), if_neg hij]; ring

private lemma eq_one_of_modMat_weylMatrix_eq_one_F4
    {w : WeylGroup Tag.F4} (h : modMat 3 (weylMatrix w) = 1) : w = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine RankThree.Chevalley.F4_eq_one_of_smul_modEq (p := 3) (by norm_num) fun v i => ?_
  have hM : ∀ j, ((weylMatrix w i j : ℤ) : ZMod 3) = if i = j then 1 else 0 := by
    intro j
    have h1 := congrFun (congrFun h i) j
    rw [modMat, Matrix.map_apply, Matrix.one_apply] at h1
    exact h1
  calc ((w • v) i : ZMod 3)
      = (((weylMatrix w).mulVec v) i : ZMod 3) := by rw [← weylMatrix_mulVec w v]
    _ = ((∑ j, weylMatrix w i j * v j : ℤ) : ZMod 3) := by
        rw [Matrix.mulVec_apply_eq_sum]
    _ = ∑ j, ((weylMatrix w i j : ℤ) : ZMod 3) * (v j : ZMod 3) := by
        push_cast; rfl
    _ = ∑ j, (if i = j then (1 : ZMod 3) else 0) * (v j : ZMod 3) := by
        exact Finset.sum_congr rfl fun j _ => by rw [hM j]
    _ = v i := by simp

theorem exists_langFrame_F4
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian 3 E)
    (htor : ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g ∈ torusGroup Tag.F4 (AlgebraicClosure K))
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup Tag.F4 K)), x ^ 3 = 1 → x ∈ E) :
    LangFrameData .F4 3 K E:= by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpK : ¬ 3 ∣ Nat.card K := by
    intro h
    have h1 : 3 ∣ 1 := (Nat.dvd_add_right h).1 hpq
    exact Nat.prime_three.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hEin⟩ :=
    ExcFramesHalf.exists_langTorus_of_toral (p := 3) Nat.prime_three K hpK E hE htor
  have hmod : modMat 3 (weylMatrix w) = -1 :=
    modMat_weylMatrix_eq_neg_one_F4 K hpq E hE htor hcard hSC w Fr hFr g0 hg0C hg0 hEin
  have hcentral : ∀ v : WeylGroup Tag.F4, v * w = w * v := by
    intro v
    have hMinv : modMat 3 (weylMatrix w⁻¹) = -1 := by
      have h1 : modMat 3 (weylMatrix w) * modMat 3 (weylMatrix w⁻¹) = 1 := by
        rw [← modMat_mul, ← weylMatrix_mul, mul_inv_cancel, weylMatrix_one, modMat_one]
      rw [hmod] at h1
      have h2 : -modMat 3 (weylMatrix w⁻¹) = 1 := by simpa using h1
      calc modMat 3 (weylMatrix w⁻¹) = -(-modMat 3 (weylMatrix w⁻¹)) := by simp
        _ = -1 := by rw [h2]
    have hvv : modMat 3 (weylMatrix v) * modMat 3 (weylMatrix v⁻¹) = 1 := by
      rw [← modMat_mul, ← weylMatrix_mul, mul_inv_cancel, weylMatrix_one, modMat_one]
    have huv : modMat 3 (weylMatrix (v * w * v⁻¹ * w⁻¹)) = 1 := by
      have h1 : modMat 3 (weylMatrix (v * w * v⁻¹ * w⁻¹)) =
          ((modMat 3 (weylMatrix v) * (-1)) * modMat 3 (weylMatrix v⁻¹)) * (-1) := by
        simp only [weylMatrix_mul, modMat_mul, hmod, hMinv]
      rw [h1]
      calc ((modMat 3 (weylMatrix v) * (-1)) * modMat 3 (weylMatrix v⁻¹)) * (-1)
          = modMat 3 (weylMatrix v) * modMat 3 (weylMatrix v⁻¹) := by noncomm_ring
        _ = 1 := hvv
    have hu : v * w * v⁻¹ * w⁻¹ = 1 := eq_one_of_modMat_weylMatrix_eq_one_F4 huv
    have h2 : v * w * v⁻¹ = w := by
      have := congrArg (· * w) hu
      simpa [mul_assoc] using this
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ζ, hζprim⟩ := exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
    Nat.prime_two Nat.prime_three hp2
  have hζo : orderOf ζ = 3 := hζprim.eq_orderOf.symm
  have hζ : ζ ^ 3 = 1 := hζprim.pow_eq_one
  have hq : ((Nat.card K : ℕ) : ZMod 3) = -1 := by
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod 3) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) (p := 3) hp2
  have hframe_mem : ∀ s : Fin Tag.F4.rank → ZMod 3,
      frameDiag (τ := Tag.F4) ζ hζ s ∈
        twistedTorus (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) Fr := by
    intro s
    rw [twistedTorus_eq_map_fixedCharTuples]
    refine Subgroup.mem_map.2 ⟨TableBExc.E6Three.zetaVec ζ hζ (frameCoord Tag.F4 3 s), ?_, ?_⟩
    · have hzv : TableBExc.E6Three.zetaVec ζ hζ (frameCoord Tag.F4 3 s) = expTuple ζ (frameCoord Tag.F4 3 s) := by
        funext i
        rw [TableBExc.E6Three.zetaVec_apply]
        rfl
      rw [hzv]
      refine (expTuple_mem_fixedCharTuples_iff hζprim (weylMatrix w) Fr hFr
        (frameCoord Tag.F4 3 s)).2 ?_
      rw [hmod, hq, Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mulVec,
        Matrix.one_mulVec]
      simp
    · rfl
  let S := {x : ModGL Tag.F4 (AlgebraicClosure K) //
    x ∈ twistedTorus (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) Fr ∧ x ^ 3 = 1}
  have hT : ∀ x : E, ∃ t ∈ twistedTorus (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) Fr,
      g0 * t * g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) :=
    fun x => Subgroup.mem_map.1 (hEin x x.2)
  have hmem : ∀ x : E, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g0 ∈
      twistedTorus (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) Fr := by
    intro x
    obtain ⟨t, ht, htx⟩ := hT x
    rw [← htx]
    have : g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t := by group
    rw [this]
    exact ht
  have hpow : ∀ x : E, (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g0) ^ 3 = 1 := by
    intro x
    have h1 : ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ^ 3 = 1 :=
      congrArg Subtype.val (hE.2 x x.2)
    have := conj_pow (a := g0⁻¹) (b := baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)) (i := 3)
    rw [inv_inv] at this
    rw [this, ← map_pow, h1, map_one]
    group
  let f : E → S := fun x => ⟨_, hmem x, hpow x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g0 := congrArg Subtype.val hxy
    have h2 : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) :=
      mul_left_cancel (mul_right_cancel h1)
    exact Subtype.ext (Subtype.ext (baseChangeGL_injective _ h2))
  have hsurj : Function.Surjective f := by
    rintro ⟨t, ht, htp⟩
    have htC : t ∈ adjointGroup Tag.F4 (AlgebraicClosure K) :=
      twistedTorusOf_le_adjointGroup _ _ ht
    have hyC : g0 * t * g0⁻¹ ∈ adjointGroup Tag.F4 (AlgebraicClosure K) :=
      mul_mem (mul_mem hg0C htC) (inv_mem hg0C)
    have hyp : (g0 * t * g0⁻¹) ^ 3 = 1 := by
      rw [conj_pow, htp]
      group
    have hyΦ : Units.map (entrywiseHom Fr) (g0 * t * g0⁻¹) = g0 * t * g0⁻¹ := by
      have ht2 : canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w *
          Units.map (entrywiseHom Fr) t *
          (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹ = t :=
        (mem_twistedTorus.1 ht).2
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w *
            Units.map (entrywiseHom Fr) t *
            (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹
          = g0 * (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w *
              Units.map (entrywiseHom Fr) t *
              (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ := by group
        _ = g0 * t * g0⁻¹ := by rw [ht2]
    obtain ⟨c, hc⟩ := f4_exists_rational_of_fixed (K := K) (L := AlgebraicClosure K) Fr hFr hyC hyΦ
    have hcE : c ∈ Subgroup.centralizer (E : Set (adjointGroup Tag.F4 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨s, hs, hsx⟩ := hT ⟨x, hx⟩
      have hts : s * t = t * s := by
        have hcomm := (isMulCommutative_twistedTorus (L := AlgebraicClosure K) w Fr).is_comm.comm
          ⟨s, hs⟩ ⟨t, ht⟩
        exact congrArg Subtype.val hcomm
      have h3 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.F4 K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.F4 K) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) := by
        rw [hc, ← hsx]
        calc g0 * s * g0⁻¹ * (g0 * t * g0⁻¹) = g0 * (s * t) * g0⁻¹ := by group
          _ = g0 * (t * s) * g0⁻¹ := by rw [hts]
          _ = g0 * t * g0⁻¹ * (g0 * s * g0⁻¹) := by group
      have h4 : (x : ModGL Tag.F4 K) * (c : ModGL Tag.F4 K) =
          (c : ModGL Tag.F4 K) * (x : ModGL Tag.F4 K) :=
        baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) (by
          rw [map_mul, map_mul]
          exact h3)
      exact Subtype.ext h4
    have hcp : c ^ 3 = 1 := by
      apply Subtype.ext
      exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) (by
        rw [Subgroup.coe_pow, map_pow, hc, hyp, Subgroup.coe_one, map_one])
    have hcEmem : c ∈ E := hSC c hcE hcp
    refine ⟨⟨c, hcEmem⟩, ?_⟩
    apply Subtype.ext
    show g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.F4 K) * g0 = t
    rw [hc]
    group
  let eE : E ≃ S := Equiv.ofBijective f ⟨hinj, hsurj⟩
  let g : (Fin Tag.F4.rank → ZMod 3) → S :=
    fun s => ⟨frameDiag ζ hζ s, hframe_mem s, frameDiag_pow ζ hζ s⟩
  have ginj : Function.Injective g := by
    intro s t h
    exact frameDiag_injective hζo hζ hdet (congrArg Subtype.val h)
  have gsurj : Function.Surjective g := by
    rintro ⟨x, hx, hxp⟩
    obtain ⟨a, ha, hap, hxa⟩ := exists_tuple_of_mem_twistedTorus w Fr hx hxp
    obtain ⟨s, hs⟩ := exists_frameDiag_eq hζo hζ hdet (funext hap)
    exact ⟨s, Subtype.ext (hs.trans hxa)⟩
  let eT : (Fin Tag.F4.rank → ZMod 3) ≃ S := Equiv.ofBijective g ⟨ginj, gsurj⟩
  let e0 : Multiplicative (Fin Tag.F4.rank → ZMod 3) → E :=
    fun m => eE.symm (eT (Multiplicative.toAdd m))
  have e0_one : e0 1 = 1 := by
    show eE.symm (eT (Multiplicative.toAdd (1 : Multiplicative (Fin Tag.F4.rank → ZMod 3)))) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (Fin Tag.F4.rank → ZMod 3)) = 0 from rfl]
    rw [Equiv.symm_apply_eq]
    show eT 0 = f 1
    apply Subtype.ext
    show (frameDiag ζ hζ 0 : ModGL Tag.F4 (AlgebraicClosure K)) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((1 : E) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g0
    rw [frameDiag_zero]
    simp only [Subgroup.coe_one, map_one, inv_one, mul_one]
    group
  have e0_mul : ∀ a b : Multiplicative (Fin Tag.F4.rank → ZMod 3), e0 (a * b) = e0 a * e0 b := by
    intro a b
    show eE.symm (eT (Multiplicative.toAdd (a * b))) =
      eE.symm (eT (Multiplicative.toAdd a)) * eE.symm (eT (Multiplicative.toAdd b))
    rw [show Multiplicative.toAdd (a * b) =
      Multiplicative.toAdd a + Multiplicative.toAdd b from rfl]
    have hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((eE.symm (eT (Multiplicative.toAdd a)) : E) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g0 =
        frameDiag ζ hζ (Multiplicative.toAdd a) := by
      have h1 : f (eE.symm (eT (Multiplicative.toAdd a))) = g (Multiplicative.toAdd a) :=
        eE.apply_symm_apply (eT (Multiplicative.toAdd a))
      have := congrArg Subtype.val h1
      simpa only [f, g] using this
    have hy : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((eE.symm (eT (Multiplicative.toAdd b)) : E) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g0 =
        frameDiag ζ hζ (Multiplicative.toAdd b) := by
      have h1 : f (eE.symm (eT (Multiplicative.toAdd b))) = g (Multiplicative.toAdd b) :=
        eE.apply_symm_apply (eT (Multiplicative.toAdd b))
      have := congrArg Subtype.val h1
      simpa only [f, g] using this
    apply eE.injective
    rw [eE.apply_symm_apply]
    show eT (Multiplicative.toAdd a + Multiplicative.toAdd b) =
      f (eE.symm (eT (Multiplicative.toAdd a)) * eE.symm (eT (Multiplicative.toAdd b)))
    apply Subtype.ext
    show (frameDiag ζ hζ (Multiplicative.toAdd a + Multiplicative.toAdd b) :
        ModGL Tag.F4 (AlgebraicClosure K)) =
      (f (eE.symm (eT (Multiplicative.toAdd a)) *
        eE.symm (eT (Multiplicative.toAdd b)))).val
    simp only [f]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, frameDiag_add, ← hx, ← hy]
    group
  let e0Hom : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* E :=
    { toFun := e0, map_one' := e0_one, map_mul' := e0_mul }
  have e0Hom_bij : Function.Bijective e0Hom := by
    constructor
    · intro a b hab
      have h1 : eT (Multiplicative.toAdd a) = eT (Multiplicative.toAdd b) := by
        have h2 : eE (e0Hom a) = eE (e0Hom b) := congrArg eE hab
        have h3 : e0Hom a = e0 a := rfl
        have h4 : e0Hom b = e0 b := rfl
        rw [h3, h4] at h2
        have h5 : e0 a = eE.symm (eT (Multiplicative.toAdd a)) := rfl
        have h6 : e0 b = eE.symm (eT (Multiplicative.toAdd b)) := rfl
        rw [h5, h6, eE.apply_symm_apply, eE.apply_symm_apply] at h2
        exact h2
      exact Multiplicative.toAdd.injective (eT.injective h1)
    · intro y
      refine ⟨Multiplicative.ofAdd (eT.symm (eE y)), ?_⟩
      show eE.symm (eT (Multiplicative.toAdd
        (Multiplicative.ofAdd (eT.symm (eE y))))) = y
      rw [show Multiplicative.toAdd (Multiplicative.ofAdd (eT.symm (eE y))) =
        eT.symm (eE y) from rfl]
      rw [eT.apply_symm_apply, eE.symm_apply_apply]
  let e0Equiv : Multiplicative (Fin Tag.F4.rank → ZMod 3) ≃* E :=
    MulEquiv.ofBijective e0Hom e0Hom_bij
  let ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup Tag.F4 K :=
    E.subtype.comp e0Equiv.toMonoidHom
  have hιinj : Function.Injective ι₀ := by
    intro a b hab
    exact e0Equiv.injective ((Subgroup.subtype_injective E) hab)
  have hιrange : ι₀.range = E := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact (e0Equiv m).2
    · intro hx
      refine ⟨Multiplicative.ofAdd (eT.symm (eE ⟨x, hx⟩)), ?_⟩
      show E.subtype (e0Equiv (Multiplicative.ofAdd (eT.symm (eE ⟨x, hx⟩)))) = x
      have hz : e0Equiv (Multiplicative.ofAdd (eT.symm (eE ⟨x, hx⟩))) = ⟨x, hx⟩ := by
        show eE.symm (eT (Multiplicative.toAdd
          (Multiplicative.ofAdd (eT.symm (eE ⟨x, hx⟩))))) = ⟨x, hx⟩
        rw [show Multiplicative.toAdd (Multiplicative.ofAdd (eT.symm (eE ⟨x, hx⟩))) =
          eT.symm (eE ⟨x, hx⟩) from rfl]
        rw [eT.apply_symm_apply, eE.symm_apply_apply]
      rw [hz]
      rfl
  have hι0 : ∀ s : Fin Tag.F4.rank → ZMod 3,
      ((ι₀ (Multiplicative.ofAdd s) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
      (((eE.symm (eT s) : E) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) := fun _ => rfl
  have hιeq : ∀ s : Fin Tag.F4.rank → ZMod 3,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
        g0 * frameDiag ζ hζ s * g0⁻¹ := by
    intro s
    rw [hι0 s]
    have hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((eE.symm (eT s) : E) : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g0 =
        frameDiag ζ hζ s := by
      have h1 : f (eE.symm (eT s)) = g s := eE.apply_symm_apply (eT s)
      have := congrArg Subtype.val h1
      simpa only [f, g] using this
    rw [← hx]
    group
  exact ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcentral, hζo, hιinj, hιrange, hιeq⟩

theorem exists_realization_F4
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (E : Subgroup (adjointGroup .F4 K)) (hF : LangFrameData .F4 3 K E) :
    ∃ (ι₀ : Multiplicative (Fin Tag.F4.rank → ZMod 3) →* adjointGroup .F4 K)
      (m : Fin Tag.F4.rank → adjointGroup .F4 K), Function.Injective ι₀ ∧ ι₀.range = E ∧
      ∀ (i : Fin Tag.F4.rank) (s : Fin Tag.F4.rank → ZMod 3),
        m i * ι₀ (Multiplicative.ofAdd s) * (m i)⁻¹ =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct Tag.F4 3 (simple Tag.F4 i) s)) := by
  classical
  obtain ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcent, _hζo, hι₀, hrange, hbase⟩ := hF
  haveI hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr_bij : Function.Bijective Fr :=
    frobenius_bijective (k := K) (L := AlgebraicClosure K) Fr hFr
  set σ : AlgebraicClosure K ≃+* AlgebraicClosure K := RingEquiv.ofBijective Fr hFr_bij with hσdef
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hmul : ∀ a b : WeylGroup Tag.F4,
      canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) (a * b) =
        canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) a *
          canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) b :=
    fun a b => RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo (τ := Tag.F4)
      (R := AlgebraicClosure K) a b
  have hFr_canon : ∀ v : WeylGroup Tag.F4,
      Units.map (entrywiseHom Fr) (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v) =
        canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v :=
    fun v => by
      simpa only [hσ] using entrywise_canonicalRep (τ := Tag.F4) σ v
  have hinv : ∀ a : WeylGroup Tag.F4,
      canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) a⁻¹ =
        (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) a)⁻¹ := by
    intro a
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, inv_mul_cancel, canonicalRep_one]
  have hconj_fixed : ∀ v : WeylGroup Tag.F4,
      Units.map (entrywiseHom Fr)
          (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v * g0⁻¹) =
        g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v * g0⁻¹ := by
    intro v
    have hwv : (w * v) * w⁻¹ = v := by
      rw [← hcent v]; group
    have hkey : canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w *
        canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v *
        (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹ =
        canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v := by
      rw [← hinv, ← hmul, ← hmul, hwv]
    calc Units.map (entrywiseHom Fr)
          (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v * g0⁻¹)
        = (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) *
            canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v *
            (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg0, hFr_canon v]
      _ = g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v * g0⁻¹ := by
          rw [show (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w) *
                canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v *
                (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹ =
              g0 * (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w *
                canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v *
                (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ by group,
            hkey]
  have hex : ∀ i : Fin Tag.F4.rank,
      ∃ c : adjointGroup Tag.F4 K,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.F4 K) =
          g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) (simple Tag.F4 i) *
            g0⁻¹ := by
    intro i
    set v : WeylGroup Tag.F4 := simple Tag.F4 i with hv
    have hxC : g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v * g0⁻¹ ∈
        adjointGroup Tag.F4 (AlgebraicClosure K) :=
      mul_mem (mul_mem hg0C
        (canonicalRep_mem_adjointGroup (coxeterSystem Tag.F4) (AlgebraicClosure K) v)) (inv_mem hg0C)
    have hxF : Units.map (entrywiseHom Fr)
        (g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v * g0⁻¹) =
        g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) v * g0⁻¹ :=
      hconj_fixed v
    obtain ⟨c, hc⟩ := f4_exists_rational_of_fixed (K := K) (L := AlgebraicClosure K) Fr hFr hxC hxF
    exact ⟨c, by simpa [hv] using hc⟩
  choose m hm using hex
  refine ⟨ι₀, m, hι₀, hrange, ?_⟩
  intro i s
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  have hcomp : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((m i * ι₀ (Multiplicative.ofAdd s) * (m i)⁻¹ :
            adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
      g0 * (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) (simple Tag.F4 i) *
        ExcFrames.frameDiag (τ := Tag.F4) ζ hζ s *
        (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) (simple Tag.F4 i))⁻¹) * g0⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hm i, hbase s]
    group
  rw [hcomp, ExcFrames.canonicalRep_conj_frameDiag]
  exact (hbase (TableBExc.torusAct Tag.F4 3 (simple Tag.F4 i) s)).symm

theorem f4_weylIrred_of_toral
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup Tag.F4 K)) (hE : IsElemAbelian 3 E)
    (htor : ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K), ∀ x ∈ E,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g ∈ torusGroup Tag.F4 (AlgebraicClosure K))
    (hcard : 3 ^ 3 ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup Tag.F4 K)), x ^ 3 = 1 → x ∈ E) :
    GGWeylIrred E:= by
  have hF := exists_langFrame_F4 K hpq E hE htor hcard hSC
  obtain ⟨ι₀, m, hinj, hrange, hm⟩ := exists_realization_F4 K E hF
  have h : GGWeylIrred ι₀.range :=
    ggWeylIrred_range_of_torusAct ι₀ hinj m hm latticeIrred_F4
  rwa [hrange] at h

end Irred937

end CFSG.StandardType

end
