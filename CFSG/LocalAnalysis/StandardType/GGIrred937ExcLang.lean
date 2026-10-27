module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxCount
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE8Three
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7E8Five
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxFixedRoot
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTorus
public import CFSG.LocalAnalysis.StandardType.GGIrred937Lattice

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly
open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFrames CFSG.StandardType.ExcFramesHalf

open scoped Matrix

open TableBExc.E6Three (zetaVec zetaVec_apply)

@[expose] def LangFrameData
    (τ : Tag) (p : ℕ) [NeZero p] (K : Type) [Field K]
    (E : Subgroup (adjointGroup τ K)) : Prop :=
  ∃ (w : WeylGroup τ) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (g0 : ModGL τ (AlgebraicClosure K)) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
    (ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K),
    (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup τ (AlgebraicClosure K) ∧
    Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
    (∀ v : WeylGroup τ, v * w = w * v) ∧ orderOf ζ = p ∧
    Function.Injective ι₀ ∧ ι₀.range = E ∧
    ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * ExcFrames.frameDiag ζ hζ s * g0⁻¹

section Lang

private lemma modMat_mul {τ : Tag} {p : ℕ} (A B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    modMat p (A * B) = modMat p A * modMat p B := by
  simp only [modMat, Matrix.map_mul]

private lemma modMat_one {τ : Tag} {p : ℕ} :
    modMat p (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) = 1 := by
  unfold modMat
  exact Matrix.map_one _ (Int.cast_zero) (Int.cast_one)

private lemma modMat_weylMatrix_eq_neg_one
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hbar : BigElemAbelianToralBar τ p) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E)
    (hcard : p ^ (τ.rank - 1) ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E)
    (w : WeylGroup τ) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL τ (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) ∈
      (twistedTorus (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) Fr).map
        (MulAut.conj g0).toMonoidHom) :
    modMat p (weylMatrix w) = -1 := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcount := natCard_eq_torsion hτ hp hp2 E hE hSC w Fr hFr g0 hg0C hg0 hEin
  have hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hcard2 := natCard_twistedTorus_pTorsion (L := AlgebraicClosure K) (τ := τ) (ℓ := 2)
    Nat.prime_two Fr hFr hp hp2 w
  have hq : ((Nat.card K : ℕ) : ZMod p) = -1 := by
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  rw [hq] at hcard2
  have hcardE : Nat.card E = Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z} := hcount.trans hcard2
  have hcardpi : Nat.card (Fin τ.rank → ZMod p) = p ^ τ.rank := by
    rw [Nat.card_pi]
    simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hKernel : Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z} ≤ p ^ τ.rank := by
    have hle := Finite.card_subtype_le (α := Fin τ.rank → ZMod p)
      (p := fun z => (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z)
    rw [hcardpi] at hle
    exact hle
  have htop : Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z} = p ^ τ.rank := by
    by_contra hne
    have hlt : Nat.card {z : Fin τ.rank → ZMod p //
        (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z} < p ^ τ.rank :=
      lt_of_le_of_ne hKernel hne
    obtain ⟨β, hβ, hwβ⟩ := (halfMaxFixedRoot_E7_E8 hτ hp hp2) w (hcardE ▸ hcard) hlt
    exact false_of_fixed_root hτ hp hp2 hpq E hE hSC w Fr hFr g0 hg0C hg0 hEin hβ hwβ
  have hall : ∀ z : Fin τ.rank → ZMod p,
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z := by
    intro z
    by_contra hz
    have hlt := Finite.card_subtype_lt
      (p := fun z => (modMat p (weylMatrix w))ᵀ *ᵥ z = (-1 : ZMod p) • z) hz
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

theorem langFrameData_of_langTorus
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E)
    (w : WeylGroup τ) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL τ (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hEin : ∀ x ∈ E, baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
        (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom)
    (hmod : modMat p (weylMatrix w) = -1) :
    LangFrameData τ p K E := by
  classical
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hcentral : ∀ v : WeylGroup τ, v * w = w * v := by
    intro v
    have hMinv : modMat p (weylMatrix w⁻¹) = -1 := by
      have h1 : modMat p (weylMatrix w) * modMat p (weylMatrix w⁻¹) = 1 := by
        rw [← modMat_mul, ← weylMatrix_mul, mul_inv_cancel, weylMatrix_one, modMat_one]
      rw [hmod] at h1
      have h2 : -modMat p (weylMatrix w⁻¹) = 1 := by simpa using h1
      calc modMat p (weylMatrix w⁻¹) = -(-modMat p (weylMatrix w⁻¹)) := by simp
        _ = -1 := by rw [h2]
    have hvv : modMat p (weylMatrix v) * modMat p (weylMatrix v⁻¹) = 1 := by
      rw [← modMat_mul, ← weylMatrix_mul, mul_inv_cancel, weylMatrix_one, modMat_one]
    have huv : modMat p (weylMatrix (v * w * v⁻¹ * w⁻¹)) = 1 := by
      have h1 : modMat p (weylMatrix (v * w * v⁻¹ * w⁻¹)) =
          ((modMat p (weylMatrix v) * (-1)) * modMat p (weylMatrix v⁻¹)) * (-1) := by
        simp only [weylMatrix_mul, modMat_mul, hmod, hMinv]
      rw [h1]
      calc ((modMat p (weylMatrix v) * (-1)) * modMat p (weylMatrix v⁻¹)) * (-1)
          = modMat p (weylMatrix v) * modMat p (weylMatrix v⁻¹) := by noncomm_ring
        _ = 1 := hvv
    have hu : v * w * v⁻¹ * w⁻¹ = 1 := eq_one_of_modMat_weylMatrix_eq_one hτ hp3 huv
    have h2 : v * w * v⁻¹ = w := by
      have := congrArg (· * w) hu
      simpa [mul_assoc] using this
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hCharL : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨ζ, hζprim⟩ := exists_primitiveRoot_units (L := AlgebraicClosure K) (ℓ := 2)
    Nat.prime_two hp hp2
  have hζo : orderOf ζ = p := hζprim.eq_orderOf.symm
  have hζ : ζ ^ p = 1 := hζprim.pow_eq_one
  have hq : ((Nat.card K : ℕ) : ZMod p) = -1 := by
    have h0 : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p) := by
    rcases hτ with rfl | rfl
    · rw [det_symmetrizedCartan_E7]
      refine isUnit_iff_ne_zero.2 ?_
      intro h
      have h' : ((2 : ℕ) : ZMod p) = 0 := by simpa using h
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
    · rw [det_symmetrizedCartan_E8]
      norm_num
  have hframe_mem : ∀ s : Fin τ.rank → ZMod p,
      frameDiag (τ := τ) ζ hζ s ∈
        twistedTorus (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) Fr := by
    intro s
    rw [twistedTorus_eq_map_fixedCharTuples]
    refine Subgroup.mem_map.2 ⟨zetaVec ζ hζ (frameCoord τ p s), ?_, ?_⟩
    · have hzv : zetaVec ζ hζ (frameCoord τ p s) = expTuple ζ (frameCoord τ p s) := by
        funext i
        rw [zetaVec_apply]
        rfl
      rw [hzv]
      refine (expTuple_mem_fixedCharTuples_iff hζprim (weylMatrix w) Fr hFr
        (frameCoord τ p s)).2 ?_
      rw [hmod, hq, Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mulVec,
        Matrix.one_mulVec]
      simp
    · rfl
  let S := {x : ModGL τ (AlgebraicClosure K) //
    x ∈ twistedTorus (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) Fr ∧ x ^ p = 1}
  have hT : ∀ x : E, ∃ t ∈ twistedTorus (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) Fr,
      g0 * t * g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : adjointGroup τ K) : ModGL τ K) :=
    fun x => Subgroup.mem_map.1 (hEin x x.2)
  have hmem : ∀ x : E, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup τ K) : ModGL τ K) * g0 ∈
      twistedTorus (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) Fr := by
    intro x
    obtain ⟨t, ht, htx⟩ := hT x
    rw [← htx]
    have : g0⁻¹ * (g0 * t * g0⁻¹) * g0 = t := by group
    rw [this]
    exact ht
  have hpow : ∀ x : E, (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup τ K) : ModGL τ K) * g0) ^ p = 1 := by
    intro x
    have h1 : ((x : adjointGroup τ K) : ModGL τ K) ^ p = 1 :=
      congrArg Subtype.val (hE.2 x x.2)
    have := conj_pow (a := g0⁻¹) (b := baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((x : adjointGroup τ K) : ModGL τ K)) (i := p)
    rw [inv_inv] at this
    rw [this, ← map_pow, h1, map_one]
    group
  let f : E → S := fun x => ⟨_, hmem x, hpow x⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) * g0 =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y : adjointGroup τ K) : ModGL τ K) * g0 := congrArg Subtype.val hxy
    have h2 : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((x : adjointGroup τ K) : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y : adjointGroup τ K) : ModGL τ K) :=
      mul_left_cancel (mul_right_cancel h1)
    exact Subtype.ext (Subtype.ext (baseChangeGL_injective _ h2))
  have hsurj : Function.Surjective f := by
    rintro ⟨t, ht, htp⟩
    have htC : t ∈ adjointGroup τ (AlgebraicClosure K) :=
      twistedTorusOf_le_adjointGroup _ _ ht
    have hyC : g0 * t * g0⁻¹ ∈ adjointGroup τ (AlgebraicClosure K) :=
      mul_mem (mul_mem hg0C htC) (inv_mem hg0C)
    have hyp : (g0 * t * g0⁻¹) ^ p = 1 := by
      rw [conj_pow, htp]
      group
    have hyΦ : Units.map (entrywiseHom Fr) (g0 * t * g0⁻¹) = g0 * t * g0⁻¹ := by
      have ht2 : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
          Units.map (entrywiseHom Fr) t *
          (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹ = t :=
        (mem_twistedTorus.1 ht).2
      rw [map_mul, map_mul, map_inv, hg0]
      calc g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
            Units.map (entrywiseHom Fr) t *
            (g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹
          = g0 * (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w *
              Units.map (entrywiseHom Fr) t *
              (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)⁻¹) * g0⁻¹ := by group
        _ = g0 * t * g0⁻¹ := by rw [ht2]
    obtain ⟨c, hc⟩ := exists_rational_of_fixed_pTorsion hτ hp hp2 Fr hFr hyC hyΦ hyp
    have hcE : c ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨s, hs, hsx⟩ := hT ⟨x, hx⟩
      have hts : s * t = t * s := by
        have hcomm := (isMulCommutative_twistedTorus (L := AlgebraicClosure K) w Fr).is_comm.comm
          ⟨s, hs⟩ ⟨t, ht⟩
        exact congrArg Subtype.val hcomm
      have h3 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) := by
        rw [hc, ← hsx]
        calc g0 * s * g0⁻¹ * (g0 * t * g0⁻¹) = g0 * (s * t) * g0⁻¹ := by group
          _ = g0 * (t * s) * g0⁻¹ := by rw [hts]
          _ = g0 * t * g0⁻¹ * (g0 * s * g0⁻¹) := by group
      have h4 : (x : ModGL τ K) * (c : ModGL τ K) = (c : ModGL τ K) * (x : ModGL τ K) :=
        baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) (by
          rw [map_mul, map_mul]
          exact h3)
      exact Subtype.ext h4
    have hcp : c ^ p = 1 := by
      apply Subtype.ext
      exact baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) (by
        rw [Subgroup.coe_pow, map_pow, hc, hyp, Subgroup.coe_one, map_one])
    have hcEmem : c ∈ E := hSC c hcE hcp
    refine ⟨⟨c, hcEmem⟩, ?_⟩
    apply Subtype.ext
    show g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * g0 = t
    rw [hc]
    group
  let eE : E ≃ S := Equiv.ofBijective f ⟨hinj, hsurj⟩
  let g : (Fin τ.rank → ZMod p) → S :=
    fun s => ⟨frameDiag ζ hζ s, hframe_mem s, frameDiag_pow ζ hζ s⟩
  have ginj : Function.Injective g := by
    intro s t h
    exact frameDiag_injective hζo hζ hdet (congrArg Subtype.val h)
  have gsurj : Function.Surjective g := by
    rintro ⟨x, hx, hxp⟩
    obtain ⟨a, ha, hap, hxa⟩ := exists_tuple_of_mem_twistedTorus w Fr hx hxp
    obtain ⟨s, hs⟩ := exists_frameDiag_eq hζo hζ hdet (funext hap)
    exact ⟨s, Subtype.ext (hs.trans hxa)⟩
  let eT : (Fin τ.rank → ZMod p) ≃ S := Equiv.ofBijective g ⟨ginj, gsurj⟩
  let e0 : Multiplicative (Fin τ.rank → ZMod p) → E :=
    fun m => eE.symm (eT (Multiplicative.toAdd m))
  have e0_one : e0 1 = 1 := by
    show eE.symm (eT (Multiplicative.toAdd (1 : Multiplicative (Fin τ.rank → ZMod p)))) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (Fin τ.rank → ZMod p)) = 0 from rfl]
    rw [Equiv.symm_apply_eq]
    show eT 0 = f 1
    apply Subtype.ext
    show (frameDiag ζ hζ 0 : ModGL τ (AlgebraicClosure K)) =
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((1 : E) : adjointGroup τ K) : ModGL τ K) * g0
    rw [frameDiag_zero]
    simp only [Subgroup.coe_one, map_one, inv_one, mul_one]
    group
  have e0_mul : ∀ a b : Multiplicative (Fin τ.rank → ZMod p), e0 (a * b) = e0 a * e0 b := by
    intro a b
    show eE.symm (eT (Multiplicative.toAdd (a * b))) =
      eE.symm (eT (Multiplicative.toAdd a)) * eE.symm (eT (Multiplicative.toAdd b))
    rw [show Multiplicative.toAdd (a * b) =
      Multiplicative.toAdd a + Multiplicative.toAdd b from rfl]
    have hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((eE.symm (eT (Multiplicative.toAdd a)) : E) : adjointGroup τ K) : ModGL τ K) * g0 =
        frameDiag ζ hζ (Multiplicative.toAdd a) := by
      have h1 : f (eE.symm (eT (Multiplicative.toAdd a))) = g (Multiplicative.toAdd a) :=
        eE.apply_symm_apply (eT (Multiplicative.toAdd a))
      have := congrArg Subtype.val h1
      simpa only [f, g] using this
    have hy : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((eE.symm (eT (Multiplicative.toAdd b)) : E) : adjointGroup τ K) : ModGL τ K) * g0 =
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
        ModGL τ (AlgebraicClosure K)) =
      (f (eE.symm (eT (Multiplicative.toAdd a)) *
        eE.symm (eT (Multiplicative.toAdd b)))).val
    simp only [f]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, frameDiag_add, ← hx, ← hy]
    group
  let e0Hom : Multiplicative (Fin τ.rank → ZMod p) →* E :=
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
  let e0Equiv : Multiplicative (Fin τ.rank → ZMod p) ≃* E :=
    MulEquiv.ofBijective e0Hom e0Hom_bij
  let ι₀ : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K :=
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
  have hι0 : ∀ s : Fin τ.rank → ZMod p,
      ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
      (((eE.symm (eT s) : E) : adjointGroup τ K) : ModGL τ K) := fun _ => rfl
  have hιeq : ∀ s : Fin τ.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((ι₀ (Multiplicative.ofAdd s) : adjointGroup τ K) : ModGL τ K) =
        g0 * frameDiag ζ hζ s * g0⁻¹ := by
    intro s
    rw [hι0 s]
    have hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((eE.symm (eT s) : E) : adjointGroup τ K) : ModGL τ K) * g0 =
        frameDiag ζ hζ s := by
      have h1 : f (eE.symm (eT s)) = g s := eE.apply_symm_apply (eT s)
      have := congrArg Subtype.val h1
      simpa only [f, g] using this
    rw [← hx]
    group
  exact ⟨w, Fr, g0, ζ, hζ, ι₀, hFr, hg0C, hg0, hcentral, hζo, hιinj, hιrange, hιeq⟩

theorem exists_langFrame_of_sc_of_toral
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hbar : BigElemAbelianToralBar τ p) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E)
    (hcard : p ^ (τ.rank - 1) ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) :
    LangFrameData τ p K E := by
  classical
  have hp : p.Prime := Fact.out
  have hpK : ¬ p ∣ Nat.card K := by
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_right h).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, hEin⟩ :=
    exists_langTorus_of_toral_bar hp hbar K hpK E hE hcard
  exact langFrameData_of_langTorus hτ hp2 K hpq E hE hSC w Fr hFr g0 hg0C hg0 hEin
    (modMat_weylMatrix_eq_neg_one hτ hp hp2 hbar K hpq E hE hcard hSC w Fr hFr g0 hg0C hg0 hEin)

theorem exists_langFrame_of_sc
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime]
    (hp35 : p = 3 ∨ p = 5) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E)
    (hcard : p ^ (τ.rank - 1) ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) :
    LangFrameData τ p K E := by
  refine exists_langFrame_of_sc_of_toral hτ (by rcases hp35 with rfl | rfl <;> norm_num) ?_ K hpq
    E hE hcard hSC
  rcases hτ with rfl | rfl <;> rcases hp35 with rfl | rfl
  · exact bigElemAbelianToralBar_E7_three
  · exact bigElemAbelianToralBar_E7_five
  · exact bigElemAbelianToralBar_E8_three
  · exact bigElemAbelianToralBar_E8_five

end Lang

end Irred937

end CFSG.StandardType
