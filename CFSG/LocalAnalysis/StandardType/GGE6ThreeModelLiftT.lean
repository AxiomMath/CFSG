module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTSpec
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Core

public noncomputable section

namespace CFSG.StandardType.E6ThreeModel

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

include hn hK hσ hFr in
theorem exists_nb_lift (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) (i : Fin 6) :
    ∃ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom), c * c = 1 ∧
      baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) = g * weylElt Tag.E6 Ω i 1 * g⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  set m : ModGL Tag.E6 Ω := weylElt Tag.E6 Ω i 1 with hm
  have hmG : m ∈ adjointGroup Tag.E6 Ω := weylElt_mem_adjointGroup (τ := Tag.E6) i 1
  have hmθ : m ∈ TwistedDiag.thetaFixed Fr := by
    refine ⟨hmG, ?_⟩
    change TwistedDiag.theta Fr m = m
    rw [TwistedDiag.theta_apply]
    exact CFSG.HardMathSupport.Malle.E27Lie.ExcCross.weylElt_twistFixed6 (L := Ω) Fr
      (fun u => CFSG.HardMathSupport.Lang.E6Descent.twE6W0_smul u) i
  have hxR : g * m * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr :=
    (TwistedDiag.mem_thetaFixed_iff_conj Fr hL.1 hL.2 m).1 hmθ
  have hunit : (-1 : Ωˣ) = 1 := by
    refine Units.ext ?_
    have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
    have h1 : (1 : Ω) + 1 = 0 := by rw [← two_mul, h2, zero_mul]
    have hneg : (-1 : Ω) = 1 := (eq_neg_of_add_eq_zero_left h1).symm
    simpa using hneg
  have hm2 : m * m = 1 := by
    have h := weylElt_one_sq (τ := Tag.E6) (R := Ω) i
    have hT : torusElt Tag.E6 Ω i (-1) = 1 := by
      rw [hunit]
      exact torusElt_one (τ := Tag.E6) (R := Ω) i
    rw [hT] at h
    simpa [hm, pow_two] using h
  have hx2 : (g * m * g⁻¹) * (g * m * g⁻¹) = 1 := by
    rw [show (g * m * g⁻¹) * (g * m * g⁻¹) = g * (m * m) * g⁻¹ by group, hm2]
    group
  obtain ⟨-, -, hCn, hCi, -⟩ :=
    TwistedDiag.cgrp_facts (ℓ := 2) (f := n) hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  have hx3C : (g * m * g⁻¹) ^ 3 ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    haveI := hCn
    have h1 := Subgroup.pow_index_mem
      ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf (TwistedDiag.Rgrp Ω Fr))
      ⟨g * m * g⁻¹, hxR⟩
    have hidx : ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf
        (TwistedDiag.Rgrp Ω Fr)).index = 3 := hCi
    rw [hidx] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hxC : g * m * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    have h3eq : (g * m * g⁻¹) ^ 3 = g * m * g⁻¹ := by
      calc (g * m * g⁻¹) ^ 3 = (g * m * g⁻¹) ^ 2 * (g * m * g⁻¹) := by rw [pow_succ]
        _ = 1 * (g * m * g⁻¹) := by
            rw [show (g * m * g⁻¹) ^ 2 = 1 by rw [pow_two]; exact hx2]
        _ = g * m * g⁻¹ := one_mul _
    rwa [h3eq] at hx3C
  obtain ⟨c, hc, hceq⟩ := hxC
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · apply Subtype.ext
    change c * c = 1
    apply (baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω))
    change baseChangeGL (algebraMap K Ω) (c * c) = baseChangeGL (algebraMap K Ω) 1
    rw [map_mul, map_one, hceq]
    exact hx2
  · show baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c = g * m * g⁻¹
    exact hceq

theorem exists_tFrame (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ}
    (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) :
    ∃ D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom), TSpec hn hK σ hσ Fr hFr g hζ D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hb : ∀ x : Fin Tag.E6.rank → ZMod 3, ∀ i, zetaVec ζ hζ x i ^ 3 = 1 := fun x i => by
    rw [zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hdR : ∀ x : Fin Tag.E6.rank → ZMod 3,
      g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := fun x =>
    TwE6DD2.conj_cubeTorus_le_Rgrp Fr hFr h3 hL.1 hL.2
      ⟨_, TwE6DD2.rootDiagUnit_mem_cubeTorus (hb x), rfl⟩
  let θhom : Multiplicative (Fin Tag.E6.rank → ZMod 3) →* ↥(TwistedDiag.Rgrp Ω Fr) :=
    MonoidHom.mk' (fun x => ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹,
        hdR (Multiplicative.toAdd x)⟩) fun x y => Subtype.ext (by
      change g * rootDiagUnit Tag.E6 (zetaVec ζ hζ
          (Multiplicative.toAdd x + Multiplicative.toAdd y)) * g⁻¹ =
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd x)) * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (Multiplicative.toAdd y)) * g⁻¹)
      rw [ExcFrames.zetaVec_add, rootDiagUnit_mul]
      group)
  let ρTor : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →* ModGL Tag.E6 Ω :=
    (baseChangeGL (τ := Tag.E6) (algebraMap K Ω)).comp
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype
  let D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    { H := (RecipeExcLang.twConj K σ).range
      diag := (rgrpConjAut hn hK σ hσ Fr hFr).comp θhom
      Tor := ((torusGroup Tag.E6 Ω).map (MulAut.conj g).toMonoidHom).comap ρTor
      nb := fun i => Classical.choose (exists_nb_lift hn hK σ hσ Fr hFr h3 hL i) }
  refine ⟨D, ?_⟩
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x
    exact ⟨(θhom (Multiplicative.ofAdd x)).2, rfl⟩
  · intro c
    exact Subgroup.mem_comap
  · intro i
    exact (Classical.choose_spec (exists_nb_lift hn hK σ hσ Fr hFr h3 hL i)).2

private theorem mulAut_conj_apply' {R : Type} [Group R] (φ : MulAut R) (r : R) :
    φ * MulAut.conj r * φ⁻¹ = MulAut.conj (φ r) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

private theorem twE6_weylElt_conj_zetaVec {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (i : Fin 6) (x : Fin Tag.E6.rank → ZMod 3) :
    weylElt Tag.E6 Ω i 1 * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) *
        (weylElt Tag.E6 Ω i 1)⁻¹ =
      rootDiagUnit Tag.E6 (zetaVec ζ hζ (adRefl .E6 3 i x)) := by
  rw [monomial_conj_rootDiagUnit_weylTuple
      (weylElt_mem_monomialSubgroup (τ := Tag.E6) (R := Ω) i)
      (mapsRootLines_weylElt (τ := Tag.E6) (R := Ω) i),
    weylTuple_zetaVec]
  rw [show adAct Tag.E6 3 (simple Tag.E6 i) x = adRefl .E6 3 i x from adAct_simple (τ := Tag.E6) i x]

private theorem rgrpConjAut_baseChange (c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (h : baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) ∈ TwistedDiag.Rgrp Ω Fr) :
    rgrpConjAut hn hK σ hσ Fr hFr
        ⟨baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K), h⟩ = MulAut.conj c := by
  have hcΓ : (c : ModGL TwistTag.E6.tag K) ∈ RecipeExcLang.twInndiagGroup K σ :=
    RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2
  have h1 : twInndiagEquivRgrp hn hK σ hσ Fr hFr ⟨c, hcΓ⟩ =
      ⟨baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K), h⟩ := by
    refine Subtype.ext ?_
    rw [twInndiagEquivRgrp_apply]
    rfl
  rw [← h1, rgrpConjAut_apply_baseChange]
  exact RecipeExcLang.twConj_of_mem_C0 σ c

private theorem baseChange_rgrpConjAut (x : ↥(TwistedDiag.Rgrp Ω Fr))
    (c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        ((((rgrpConjAut hn hK σ hσ Fr hFr x c :
            ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K) :
          ModGL Tag.E6 K)) =
      (x : ModGL Tag.E6 Ω) *
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
          (((c : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 K)) *
        (x : ModGL Tag.E6 Ω)⁻¹ := by
  set w := (twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm x with hw
  have hxw : twInndiagEquivRgrp hn hK σ hσ Fr hFr w = x := MulEquiv.apply_symm_apply _ _
  let xT : ModGL TwistTag.E6.tag Ω := (x : ModGL Tag.E6 Ω)
  have hvalT : baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K) = xT := by
    change baseChangeGL (algebraMap K Ω) (w : ModGL TwistTag.E6.tag K) = (x : ModGL Tag.E6 Ω)
    rw [← hxw]
    exact (twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr w).symm
  show baseChangeGL (algebraMap K Ω)
      (((rgrpConjAut hn hK σ hσ Fr hFr x c :
          ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) : ModGL TwistTag.E6.tag K)) =
    xT * baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) * xT⁻¹
  rw [show rgrpConjAut hn hK σ hσ Fr hFr x = RecipeExcLang.twConj K σ w from rfl]
  rw [RecipeExcLang.coe_twConj]
  rw [map_mul, map_mul, map_inv]
  rw [hvalT]

theorem tFrame_weyl (h3 : 3 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω} (hL : IsLang Fr g) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (hζo : orderOf ζ = 3) {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) : D.WeylOK := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hunit : (-1 : Ωˣ) = 1 := by
    refine Units.ext ?_
    have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
    have h1 : (1 : Ω) + 1 = 0 := by rw [← two_mul, h2, zero_mul]
    have hneg : (-1 : Ω) = 1 := (eq_neg_of_add_eq_zero_left h1).symm
    simpa using hneg
  have hmθ : ∀ i : Fin 6, weylElt Tag.E6 Ω i 1 ∈ TwistedDiag.thetaFixed Fr := fun i => by
    refine ⟨weylElt_mem_adjointGroup (τ := Tag.E6) i 1, ?_⟩
    change TwistedDiag.theta Fr (weylElt Tag.E6 Ω i 1) = weylElt Tag.E6 Ω i 1
    rw [TwistedDiag.theta_apply]
    exact CFSG.HardMathSupport.Malle.E27Lie.ExcCross.weylElt_twistFixed6 (L := Ω) Fr
      (fun u => CFSG.HardMathSupport.Lang.E6Descent.twE6W0_smul u) i
  have hniR : ∀ i : Fin 6, g * weylElt Tag.E6 Ω i 1 * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := fun i =>
    (TwistedDiag.mem_thetaFixed_iff_conj Fr hL.1 hL.2 _).1 (hmθ i)
  have hweyl2 : ∀ i : Fin 6, weylElt Tag.E6 Ω i 1 * weylElt Tag.E6 Ω i 1 = 1 := fun i => by
    have h := weylElt_one_sq (τ := Tag.E6) (R := Ω) i
    have hT : torusElt Tag.E6 Ω i (-1) = 1 := by
      rw [hunit]
      exact torusElt_one (τ := Tag.E6) (R := Ω) i
    rw [hT] at h
    simpa [pow_two] using h
  let val : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) → ModGL Tag.E6 K :=
    fun c => (c : ModGL TwistTag.E6.tag K)
  have hnb : ∀ i : Fin 6, baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (val (D.nb i)) =
      g * weylElt Tag.E6 Ω i 1 * g⁻¹ := fun i => hD.nb_eq i
  have htor : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      c ∈ D.Tor ↔ baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (val c) ∈
        (torusGroup Tag.E6 Ω).map (MulAut.conj g).toMonoidHom := fun c => hD.tor_eq c
  obtain ⟨-, hCR, -, -, -⟩ :=
    TwistedDiag.cgrp_facts (ℓ := 2) (f := n) hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  have hnbR : ∀ i : Fin 6,
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (val (D.nb i)) ∈ TwistedDiag.Rgrp Ω Fr :=
    fun i => hCR (Subgroup.mem_map.2 ⟨val (D.nb i), (D.nb i).2, rfl⟩)
  have hconj : ∀ i : Fin 6, MulAut.conj (D.nb i) =
      rgrpConjAut hn hK σ hσ Fr hFr ⟨g * weylElt Tag.E6 Ω i 1 * g⁻¹, hniR i⟩ := by
    intro i
    have heq : (⟨g * weylElt Tag.E6 Ω i 1 * g⁻¹, hniR i⟩ : ↥(TwistedDiag.Rgrp Ω Fr)) =
        ⟨baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (val (D.nb i)), hnbR i⟩ :=
      Subtype.ext (hnb i).symm
    rw [heq]
    exact (rgrpConjAut_baseChange (hn := hn) (hK := hK) (σ := σ) (hσ := hσ) (Fr := Fr)
      (hFr := hFr) (c := D.nb i) (h := hnbR i)).symm
  have hcl1 : ∀ i : Fin 6, D.nb i * D.nb i = 1 := by
    intro i
    apply Subtype.ext
    change val (D.nb i) * val (D.nb i) = (1 : ModGL Tag.E6 K)
    apply (baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω))
    show baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (val (D.nb i) * val (D.nb i)) =
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) 1
    rw [map_mul, map_one, hnb i]
    rw [show (g * weylElt Tag.E6 Ω i 1 * g⁻¹) * (g * weylElt Tag.E6 Ω i 1 * g⁻¹) =
      g * (weylElt Tag.E6 Ω i 1 * weylElt Tag.E6 Ω i 1) * g⁻¹ by group, hweyl2 i]
    group
  have hcl2 : ∀ (i : Fin 6) (t : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)),
      t ∈ D.Tor → D.nb i * t * (D.nb i)⁻¹ ∈ D.Tor := by
    intro i t ht
    rw [htor]
    obtain ⟨k, hk, hk_eq⟩ := (htor t).1 ht
    refine ⟨weylElt Tag.E6 Ω i 1 * k * (weylElt Tag.E6 Ω i 1)⁻¹, ?_, ?_⟩
    · exact weylElt_mul_mul_inv_mem_torus Tag.E6 Ω i 1 hk
    · show (MulAut.conj g).toMonoidHom (weylElt Tag.E6 Ω i 1 * k * (weylElt Tag.E6 Ω i 1)⁻¹) =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (val (D.nb i) * val t * (val (D.nb i))⁻¹)
      conv_rhs => rw [map_mul, map_mul, map_inv]
      rw [hnb i]
      rw [show baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (val t) =
          (MulAut.conj g).toMonoidHom k from hk_eq.symm]
      show (MulAut.conj g).toMonoidHom (weylElt Tag.E6 Ω i 1 * k * (weylElt Tag.E6 Ω i 1)⁻¹) =
        (MulAut.conj g).toMonoidHom (weylElt Tag.E6 Ω i 1) *
          (MulAut.conj g).toMonoidHom k *
          ((MulAut.conj g).toMonoidHom (weylElt Tag.E6 Ω i 1))⁻¹
      rw [map_mul, map_mul, map_inv]
  have hcl3 : ∀ (i : Fin 6) (x : Fin Tag.E6.rank → ZMod 3),
      MulAut.conj (D.nb i) * D.ad x * (MulAut.conj (D.nb i))⁻¹ =
        D.ad (adRefl .E6 3 i x) := by
    intro i x
    obtain ⟨hx, hxad⟩ := hD.diag_eq x
    obtain ⟨hxi, hxiad⟩ := hD.diag_eq (adRefl .E6 3 i x)
    rw [hxad, hxiad, hconj i]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change g * weylElt Tag.E6 Ω i 1 * g⁻¹ *
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) *
        (g * weylElt Tag.E6 Ω i 1 * g⁻¹)⁻¹ =
      g * rootDiagUnit Tag.E6 (zetaVec ζ hζ (adRefl .E6 3 i x)) * g⁻¹
    rw [show g * weylElt Tag.E6 Ω i 1 * g⁻¹ *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) *
          (g * weylElt Tag.E6 Ω i 1 * g⁻¹)⁻¹ =
        g * (weylElt Tag.E6 Ω i 1 * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) *
          (weylElt Tag.E6 Ω i 1)⁻¹) * g⁻¹ by group,
      twE6_weylElt_conj_zetaVec hζ i x]
  have hcl4 : ∀ (i : Fin 6) (x : Fin Tag.E6.rank → ZMod 3),
      D.nb i * (D.ad x (D.nb i))⁻¹ ∈ D.V0 := by
    intro i x
    obtain ⟨hx, hxad⟩ := hD.diag_eq x
    set v : Fin Tag.E6.rank → ZMod 3 := adRefl .E6 3 i x - x with hv
    have hvhyp : v ∈ NoOffRest.hypE6 := by
      rw [NoOffRest.mem_hypE6, hv, NoOffRest.kDotP_sub,
        NoOffRest.kDotP_adRefl (NoOffRest.kDot_cartan i), sub_self]
    have hbd : baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (val (D.ad x (D.nb i))) =
        (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) *
          (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
          (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹)⁻¹ := by
      rw [hxad]
      rw [baseChange_rgrpConjAut (hn := hn) (hK := hK) (σ := σ) (hσ := hσ) (Fr := Fr)
        (hFr := hFr) (x := ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹, hx⟩)
        (c := D.nb i)]
      rw [hnb i]
    have hbase_r : baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
        (val (D.nb i * (D.ad x (D.nb i))⁻¹)) =
        g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ := by
      show baseChangeGL (τ := Tag.E6) (algebraMap K Ω)
          (val (D.nb i) * (val (D.ad x (D.nb i)))⁻¹) = _
      rw [map_mul, map_inv, hnb i, hbd]
      rw [show (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
            ((g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹) *
              (g * weylElt Tag.E6 Ω i 1 * g⁻¹) *
              (g * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) * g⁻¹)⁻¹)⁻¹ =
          g * (weylElt Tag.E6 Ω i 1 * rootDiagUnit Tag.E6 (zetaVec ζ hζ x) *
            (weylElt Tag.E6 Ω i 1)⁻¹ *
            (rootDiagUnit Tag.E6 (zetaVec ζ hζ x))⁻¹) * g⁻¹ by group,
        twE6_weylElt_conj_zetaVec hζ i x]
      have hsplit : zetaVec ζ hζ v * zetaVec ζ hζ x = zetaVec ζ hζ (adRefl .E6 3 i x) := by
        rw [hv, ← ExcFrames.zetaVec_add]
        congr 1
        abel
      rw [show rootDiagUnit Tag.E6 (zetaVec ζ hζ (adRefl .E6 3 i x)) *
              (rootDiagUnit Tag.E6 (zetaVec ζ hζ x))⁻¹ =
            rootDiagUnit Tag.E6 (zetaVec ζ hζ v) by
        rw [← hsplit, rootDiagUnit_mul]
        group]
    refine ⟨?_, ?_⟩
    · rw [htor]
      refine ⟨rootDiagUnit Tag.E6 (zetaVec ζ hζ v), rootDiagUnit_mem_torusGroup _, ?_⟩
      rw [hbase_r]
      rfl
    · refine ⟨v, hvhyp, ?_⟩
      change MulAut.conj (D.nb i * (D.ad x (D.nb i))⁻¹) = D.ad v
      rw [map_mul, map_inv]
      rw [show MulAut.conj (D.ad x (D.nb i)) =
          D.ad x * MulAut.conj (D.nb i) * (D.ad x)⁻¹ from
        (mulAut_conj_apply' (D.ad x) (D.nb i)).symm]
      rw [show MulAut.conj (D.nb i) *
            (D.ad x * MulAut.conj (D.nb i) * (D.ad x)⁻¹)⁻¹ =
          MulAut.conj (D.nb i) * D.ad x * (MulAut.conj (D.nb i))⁻¹ * (D.ad x)⁻¹ by group,
        hcl3 i x]
      rw [show D.ad (adRefl .E6 3 i x) * (D.ad x)⁻¹ = D.ad v by
        rw [hv, sub_eq_add_neg, D.ad_add]
        congr 1
        exact (D.ad_neg x).symm]
  exact ⟨hcl1, hcl2, hcl3, hcl4⟩

end CFSG.StandardType.E6ThreeModel
