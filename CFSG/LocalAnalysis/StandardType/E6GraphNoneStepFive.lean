module

public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFourField
public import CFSG.LocalAnalysis.StandardType.E6GraphNoneStepFiveWeights
public import CFSG.LocalAnalysis.StandardType.GGExcFiveFour
public import CFSG.LocalAnalysis.StandardType.GGExcPRankBound
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourFusion
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral

public section

namespace CFSG.StandardType.E6GraphNoneSteps

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close CFSG.StandardType.E6GraphNoneSteps

@[expose] def movedPosT : List V6 := CFSG.StandardType.E6GraphNoneSteps.movedPos

theorem killT : ∀ y : Fin Tag.F4.rank → ZMod 3, ∃ α ∈ movedPosT,
    ∑ i : Fin TwistTag.E6.tag.rank, ((α i : ℤ) : ZMod 3) * y (piF i) = 0 ∧
    ∑ i : Fin TwistTag.E6.tag.rank,
      ((permLattice TwistTag.E6.perm α i : ℤ) : ZMod 3) * y (piF i) = 0 := by
  decide +kernel

theorem exists_zmod_of_pow_three {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 3) {x : Lˣ}
    (hx : x ^ 3 = 1) : ∃ e : ZMod 3, x = ζ ^ e.val := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, he⟩ := CFSG.StandardType.NoOffUO.exists_pow_val_eq (p := 3) hζ hx
  exact ⟨e, he.symm⟩

theorem rootChar_cube {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 3)
    {c : Fin Tag.F4.rank → Lˣ} {y : Fin Tag.F4.rank → ZMod 3} (hy : ∀ k, c k = ζ ^ (y k).val)
    {v : V6} (hv : ∑ i : Fin TwistTag.E6.tag.rank, ((v i : ℤ) : ZMod 3) * y (piF i) = 0) :
    rootChar (fun i : Fin TwistTag.E6.tag.rank => c (e6IndexToF4 i)) v = 1 := by
  have h1 : rootChar (fun i : Fin TwistTag.E6.tag.rank => c (e6IndexToF4 i)) v =
      ζ ^ (∑ i : Fin TwistTag.E6.tag.rank, ((y (piF i)).val : ℤ) * v i) := by
    rw [rootChar, ← CFSG.RankThree.PartOne.KLR.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hy, zpow_mul, zpow_natCast]
    rfl
  rw [h1, ← orderOf_dvd_iff_zpow_eq_one, hζ]
  have : ((∑ i : Fin TwistTag.E6.tag.rank, ((y (piF i)).val : ℤ) * v i : ℤ) : ZMod 3) = 0 := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [← hv]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 this


private theorem exists_preimage_of_conj_frobenius_fixed
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {L : Type} [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr)
    {g z₀ : ModGL TwistTag.E6.tag L}
    (hzC : g * z₀ * g⁻¹ ∈ adjointGroup TwistTag.E6.tag L)
    (hzF : Units.map (entrywiseHom Fr) (g * z₀ * g⁻¹) = g * z₀ * g⁻¹) :
    ∃ j ∈ adjointGroup TwistTag.E6.tag K,
      g * z₀ * g⁻¹ = baseChangeGL (algebraMap K L) j := by
  obtain ⟨t, j, hj, hzj⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.exists_rootDiagUnit_mul_of_frobenius_fixed
      Fr hFr hbij hzC hzF
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
  have ht : t = 1 := Subsingleton.elim _ _
  rw [ht, rootDiagUnit_one, one_mul] at hzj
  exact ⟨j, hj, hzj⟩

private theorem e6_step5 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] [Algebra K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hbij : Function.Bijective Fr)
    {g : ModGL TwistTag.E6.tag L} (hg : g ∈ adjointGroup TwistTag.E6.tag L)
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hlang : Units.map (entrywiseHom Fr) g = g * weylWord (τ := TwistTag.E6.tag) L ω)
    (hw : ∀ b : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct (CFSG.StandardType.E6GraphNoneSteps.wt ω)
        (fun i => b (e6IndexToF4 i)) = (fun i => b (e6IndexToF4 i))⁻¹)
    {c : Fin Tag.F4.rank → Lˣ} (hc : ∀ k, c k ^ 3 = 1) :
    ∃ z ∈ (adjointGroup TwistTag.E6.tag K).map (baseChangeGL (algebraMap K L)),
      Commute z (g * rootDiagUnit TwistTag.E6.tag (fun i => c (e6IndexToF4 i)) * g⁻¹) ∧
      diagramMap TwistTag.E6 L * z * (diagramMap TwistTag.E6 L)⁻¹ ≠ z := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_orderOf_three L
  choose y hy using fun k => exists_zmod_of_pow_three hζ (hc k)
  obtain ⟨α, hα, hk1, hk2⟩ := killT y
  have hshape := wt_cases (CFSG.StandardType.E6GraphNoneSteps.wt ω) hw
  obtain ⟨z₀, hz₀C, hz₀d, hz₀F, hz₀P⟩ := CFSG.StandardType.E6GraphNoneSteps.exists_z0 Fr ω hshape hα
    (rootChar_cube hζ hy hk1) (rootChar_cube hζ hy hk2)
  have hzC : g * z₀ * g⁻¹ ∈ adjointGroup TwistTag.E6.tag L :=
    mul_mem (mul_mem hg hz₀C) (inv_mem hg)
  have hzF : Units.map (entrywiseHom Fr) (g * z₀ * g⁻¹) = g * z₀ * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hlang]
    conv_rhs => rw [← hz₀F]
    group
  obtain ⟨j, hj, hzj⟩ := exists_preimage_of_conj_frobenius_fixed hK Fr hFr hbij hzC hzF
  refine ⟨g * z₀ * g⁻¹, ⟨j, hj, hzj.symm⟩, hz₀d.conj g, ?_⟩
  intro h
  apply hz₀P
  have hP := diagramMap_mul_of_mem_twistedFixedGroup hgP
  have e : diagramMap TwistTag.E6 L * (g * z₀ * g⁻¹) * (diagramMap TwistTag.E6 L)⁻¹ =
      g * (diagramMap TwistTag.E6 L * z₀ * (diagramMap TwistTag.E6 L)⁻¹) * g⁻¹ := by
    calc diagramMap TwistTag.E6 L * (g * z₀ * g⁻¹) * (diagramMap TwistTag.E6 L)⁻¹ =
          (diagramMap TwistTag.E6 L * g) * z₀ * (diagramMap TwistTag.E6 L * g)⁻¹ := by group
      _ = (g * diagramMap TwistTag.E6 L) * z₀ * (g * diagramMap TwistTag.E6 L)⁻¹ := by rw [hP]
      _ = _ := by group
  rw [e] at h
  exact mul_left_cancel (mul_right_cancel h)

private theorem prime_eq_three_and_orderOf_eq_two_of_elemAbelian_card_ge_four
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (adjointGroup Tag.F4 K)}
    (hE : CFSG.Open.IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E) :
    p = 3 ∧ orderOf (Nat.card K : ZMod p) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hdeg : 4 ≤ CFSG.StandardType.ExcMaxToral.excDegCount Tag.F4
      (orderOf (Nat.card K : ZMod p)) := by
    by_contra h
    have hle := CFSG.StandardType.ExcMaxToral.excPRankBound (Or.inr (Or.inr rfl)) K hp hp2
      (by omega) E hE
    have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact (not_le.2 (lt_of_lt_of_le hlt h4)) hle
  have hd2 : orderOf (Nat.card K : ZMod p) = 2 := by
    rcases CFSG.StandardType.ExcMaxToral.excDegCount_ge_four hdeg with ⟨-, hd, -⟩ | ⟨hE8, -, -⟩
    · rcases hd with hd | hd
      · exfalso
        rw [orderOf_eq_one_iff, hK] at hd
        have h1 : ((2 : ℕ) : ZMod p) - 1 = 1 := by push_cast; ring
        rw [hd, sub_self] at h1
        exact zero_ne_one h1
      · exact hd
    · exact absurd hE8 (by decide)
  have hp3 : p = 3 := by
    have h := pow_orderOf_eq_one (Nat.card K : ZMod p)
    rw [hd2, hK] at h
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      have : ((3 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) ^ 2 - 1 := by push_cast; ring
      rw [this, h, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
  exact ⟨hp3, hd2⟩

private theorem exists_langTorus_with_neg_one_of_elemAbelian_card_ge_four
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd2 : orderOf (Nat.card K : ZMod p) = 2)
    {E : Subgroup (adjointGroup Tag.F4 K)}
    (hE : CFSG.Open.IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E) :
    ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
      (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ D : LangDatum Tag.F4 (AlgebraicClosure K),
        D.Φ = Units.map (entrywiseHom Fr) ∧
        (∃ w : WeylGroup Tag.F4,
          D.n = canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w ∧
          ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u) ∧
        (∀ x ∈ E,
          D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) *
            D.g0 ∈ D.torus) := by
  have hdeg : CFSG.StandardType.ExcMaxToral.excDegCount Tag.F4
      (orderOf (Nat.card K : ZMod p)) = 4 := by
    rw [hd2]; decide
  obtain ⟨Fr, hFr, D, hΦ, -, ⟨w, hDn, hshape⟩, hmemT, -⟩ :=
    CFSG.StandardType.ExcMaxToral.adjointMaxElemToral Tag.F4 K p inferInstance inferInstance hp
      hp2 (by rw [hdeg]) E hE (by rw [hdeg]; exact h4)
  refine ⟨Fr, hFr, D, hΦ, ⟨w, hDn, ?_⟩, hmemT⟩
  unfold CFSG.StandardType.ExcMaxToral.ExcLangShape at hshape
  exact hshape.2.1 hd2

private theorem exists_rootDiagUnit_cube_eq_one
    {K : Type} [Field K]
    {E : Subgroup (adjointGroup Tag.F4 K)} {D : LangDatum Tag.F4 (AlgebraicClosure K)}
    (hmemT : ∀ x ∈ E,
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.F4 K) *
        D.g0 ∈ D.torus)
    {b : adjointGroup Tag.F4 K} (hb : b ∈ E) (hb3 : (b : ModGL Tag.F4 K) ^ 3 = 1) :
    ∃ c : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.F4 c =
        D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL Tag.F4 K) * D.g0 ∧
      ∀ k, c k ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_of_mem_torusGroup
    ((mem_twistedTorusOf.1 (hmemT b hb)).1)
  refine ⟨c, hc, ?_⟩
  have h1 : rootDiagUnit Tag.F4 (c ^ 3) = rootDiagUnit Tag.F4 1 := by
    rw [rootDiagUnit_one]
    change rootDiagUnitHom Tag.F4 (AlgebraicClosure K) (c ^ 3) = 1
    rw [map_pow]
    change rootDiagUnit Tag.F4 c ^ 3 = 1
    rw [hc]
    have e : ∀ (g x : ModGL Tag.F4 (AlgebraicClosure K)), (g⁻¹ * x * g) ^ 3 = g⁻¹ * x ^ 3 * g :=
      fun g x => by simp only [pow_succ, pow_zero, one_mul]; group
    rw [e, ← map_pow, hb3, map_one, mul_one, inv_mul_cancel]
  intro k
  exact congrFun (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h1) k

private theorem baseChange_eq_conj_rootDiagUnit
    {K : Type} [Field K]
    {D : LangDatum Tag.F4 (AlgebraicClosure K)}
    (hconj : ∀ (b : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ)
      (hb : rootDiagUnit Tag.F4 b ∈ adjointGroup Tag.F4 (AlgebraicClosure K)),
      ((embE6F4 (AlgebraicClosure K) (⟨D.g0, D.g0_mem⟩ * ⟨_, hb⟩ * ⟨D.g0, D.g0_mem⟩⁻¹) :
        adjointGroup .E6 (AlgebraicClosure K)) : ModGL Tag.E6 (AlgebraicClosure K)) =
        ((embE6F4 (AlgebraicClosure K) ⟨D.g0, D.g0_mem⟩ : adjointGroup .E6
          (AlgebraicClosure K)) : ModGL Tag.E6 (AlgebraicClosure K)) *
          rootDiagUnit Tag.E6 (fun i => b (e6IndexToF4 i)) *
          ((embE6F4 (AlgebraicClosure K) ⟨D.g0, D.g0_mem⟩ : adjointGroup .E6
            (AlgebraicClosure K)) : ModGL Tag.E6 (AlgebraicClosure K))⁻¹)
    {c : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ}
    {b : twistedFixedGroup TwistTag.E6 K (RingHom.id K)}
    (hc : rootDiagUnit Tag.F4 c =
      D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((e6FixedF4EquivAll K b : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)) * D.g0) :
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL TwistTag.E6.tag K) =
      ((embE6F4 (AlgebraicClosure K) ⟨D.g0, D.g0_mem⟩ : adjointGroup .E6
        (AlgebraicClosure K)) : ModGL Tag.E6 (AlgebraicClosure K)) *
        rootDiagUnit Tag.E6 (fun i => c (e6IndexToF4 i)) *
        ((embE6F4 (AlgebraicClosure K) ⟨D.g0, D.g0_mem⟩ : adjointGroup .E6
          (AlgebraicClosure K)) : ModGL Tag.E6 (AlgebraicClosure K))⁻¹ := by
  have hcm := rootDiagUnit_mem_adjointGroup_of_isAlgClosed (τ := Tag.F4)
    (L := AlgebraicClosure K) c
  have hbg := hconj c hcm
  have hu : ((e6FixedF4EquivAll (AlgebraicClosure K)
      ⟨baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL TwistTag.E6.tag K),
        baseChangeGL_mem_twistedFixedGroup (algebraMap K (AlgebraicClosure K)) b.2⟩ :
          adjointGroup Tag.F4 (AlgebraicClosure K)) : ModGL Tag.F4 (AlgebraicClosure K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((e6FixedF4EquivAll K b : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) := by
    rw [coe_e6FixedF4EquivAll, e6FixedToF4_baseChangeGL]
    rfl
  have hy : (⟨D.g0, D.g0_mem⟩ * ⟨_, hcm⟩ * ⟨D.g0, D.g0_mem⟩⁻¹ :
      adjointGroup Tag.F4 (AlgebraicClosure K)) = e6FixedF4EquivAll (AlgebraicClosure K)
        ⟨baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL TwistTag.E6.tag K),
          baseChangeGL_mem_twistedFixedGroup (algebraMap K (AlgebraicClosure K)) b.2⟩ :=
    Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu]
      change D.g0 * rootDiagUnit Tag.F4 c * D.g0⁻¹ = _
      rw [hc]
      group)
  rw [hy, CFSG.StandardType.E6GraphNoneSteps.coe_embE6F4, MulEquiv.symm_apply_apply] at hbg
  exact hbg

private theorem weylWord_unfoldF4_inverts_torus
    {L : Type} [Field L] [IsAlgClosed L] {D : LangDatum Tag.F4 L} {w : WeylGroup Tag.F4}
    (hDn : D.n = canonicalRep (coxeterSystem Tag.F4) L w)
    (hw1 : ∀ u : Fin Tag.F4.rank → ℤ, w • u = -u)
    {ω : List (Fin Tag.F4.rank)} (hDnω : D.n = weylWord (τ := Tag.F4) L ω)
    (hconjW : ∀ b : Fin Tag.F4.rank → Lˣ,
      rootDiagUnit Tag.F4 b ∈ adjointGroup Tag.F4 L →
      weylWord (τ := Tag.E6) L (unfoldF4 ω) *
        rootDiagUnit Tag.E6 (fun i => b (e6IndexToF4 i)) *
        (weylWord (τ := Tag.E6) L (unfoldF4 ω))⁻¹ =
        rootDiagUnit Tag.E6
          (fun i => CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
            ((coxeterSystem Tag.F4).wordProd ω) b (e6IndexToF4 i))) :
    ∀ b' : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
        (CFSG.StandardType.E6GraphNoneSteps.wt (unfoldF4 ω))
        (fun i => b' (e6IndexToF4 i)) = (fun i => b' (e6IndexToF4 i))⁻¹ := by
  have hwF : ∀ b : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
        ((coxeterSystem Tag.F4).wordProd ω) b = b⁻¹ := by
    intro b
    have h1 := weylWord_conj_rootDiagUnit (τ := Tag.F4) (L := L) ω b
    have h2 := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.canonicalRep_conj_rootDiagUnit
      (K := L) w b
    rw [← hDn, hDnω] at h2
    rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective (h1.symm.trans h2)]
    funext i
    simp only [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct, Pi.inv_apply]
    have hi : w⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) = -Pi.single i 1 := by
      have := hw1 (-Pi.single i 1)
      rw [neg_neg] at this
      calc w⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) =
            w⁻¹ • (w • -(Pi.single i 1 : Fin Tag.F4.rank → ℤ)) := by rw [this]
        _ = _ := inv_smul_smul w _
    rw [hi, show rootChar b (-Pi.single i 1) = (rootChar b (Pi.single i 1))⁻¹ by
      simp only [rootChar, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib],
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_single]
  intro b'
  have hb' := rootDiagUnit_mem_adjointGroup_of_isAlgClosed (τ := Tag.F4) (L := L) b'
  have h1 := hconjW b' hb'
  have h2 := weylWord_conj_rootDiagUnit (τ := Tag.E6) (L := L) (unfoldF4 ω)
    (fun i => b' (e6IndexToF4 i))
  rw [h1, hwF] at h2
  exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h2).symm

private theorem exists_moved_involution_commuting
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr)
    {g : ModGL Tag.E6 L} (hg : g ∈ adjointGroup Tag.E6 L)
    (hgP : g ∈ twistedFixedGroup TwistTag.E6 L (RingHom.id L))
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hlang : Units.map (entrywiseHom Fr) g = g * weylWord (τ := Tag.E6) L ω)
    (hw : ∀ b' : Fin Tag.F4.rank → Lˣ,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct
        (CFSG.StandardType.E6GraphNoneSteps.wt ω) (fun i => b' (e6IndexToF4 i)) =
        (fun i => b' (e6IndexToF4 i))⁻¹)
    {c : Fin Tag.F4.rank → Lˣ} (hc3 : ∀ k, c k ^ 3 = 1)
    {b : twistedFixedGroup TwistTag.E6 K (RingHom.id K)}
    (hbg : baseChangeGL (algebraMap K L) (b : ModGL TwistTag.E6.tag K) =
      g * rootDiagUnit Tag.E6 (fun i => c (e6IndexToF4 i)) * g⁻¹) :
    ∃ z ∈ adjointGroup TwistTag.E6.tag K, Commute z (b : ModGL TwistTag.E6.tag K) ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  obtain ⟨z, hzC, hcomm, hne⟩ := e6_step5 hK Fr hFr hbij hg hgP ω hlang hw hc3
  obtain ⟨zK, hzK, rfl⟩ := hzC
  refine ⟨zK, hzK, ?_, fun heq => hne ?_⟩
  · have h2 := hcomm
    change Commute (baseChangeGL (algebraMap K L) zK)
      (g * rootDiagUnit Tag.E6 (fun i => c (e6IndexToF4 i)) * g⁻¹) at h2
    rw [← hbg] at h2
    apply baseChangeGL_injective (algebraMap K L)
    rw [map_mul, map_mul]
    exact h2.eq
  · rw [← baseChangeGL_diagramMap (algebraMap K L) TwistTag.E6, ← map_inv,
      ← map_mul, ← map_mul, heq]

theorem e6_step5_K {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (twistedFixedGroup TwistTag.E6 K (RingHom.id K)))
    (hE : CFSG.Open.IsElemAbelian p E) (h4 : p ^ 4 ≤ Nat.card E)
    {b : twistedFixedGroup TwistTag.E6 K (RingHom.id K)} (hb : b ∈ E) :
    ∃ z ∈ adjointGroup TwistTag.E6.tag K, Commute z (b : ModGL TwistTag.E6.tag K) ∧
      diagramMap TwistTag.E6 K * z * (diagramMap TwistTag.E6 K)⁻¹ ≠ z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hE' : CFSG.Open.IsElemAbelian p (E.map (e6FixedF4EquivAll K).toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hE _
  have hcard : Nat.card (E.map (e6FixedF4EquivAll K).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (e6FixedF4EquivAll K).injective
  have h4' : p ^ 4 ≤ Nat.card (E.map (e6FixedF4EquivAll K).toMonoidHom) := by
    rw [hcard]; exact h4
  obtain ⟨hp3, hd2⟩ :=
    prime_eq_three_and_orderOf_eq_two_of_elemAbelian_card_ge_four hK hp hp2 hE' h4'
  subst hp3
  obtain ⟨Fr, hFr, D, hΦ, ⟨w, hDn, hw1⟩, hmemT⟩ :=
    exists_langTorus_with_neg_one_of_elemAbelian_card_ge_four hp hp2 hd2 hE' h4'
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hbij : Function.Bijective Fr := ⟨Fr.injective, fun x => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x (n := 2) (by norm_num)
    exact ⟨z, by rw [hFr, hK]; exact hz⟩⟩
  have hbE' : e6FixedF4EquivAll K b ∈ E.map (e6FixedF4EquivAll K).toMonoidHom := ⟨b, hb, rfl⟩
  have hb3 : ((e6FixedF4EquivAll K b : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hE'.2 _ hbE', Subgroup.coe_one]
  obtain ⟨c, hc, hc3⟩ := exists_rootDiagUnit_cube_eq_one (D := D) hmemT hbE' hb3
  obtain ⟨ω, hDnω, hgP, hn, hlang, hconj, hconjW⟩ :=
    CFSG.StandardType.E6GraphNoneSteps.f4LangDatum_transport D Fr hΦ
  have hbg := baseChange_eq_conj_rootDiagUnit (D := D) hconj hc
  have hwE := weylWord_unfoldF4_inverts_torus (D := D) hDn hw1 hDnω hconjW
  exact exists_moved_involution_commuting hK Fr hFr hbij
    (embE6F4 (AlgebraicClosure K) ⟨D.g0, D.g0_mem⟩).2 hgP (unfoldF4 ω) hlang hwE hc3 hbg

end CFSG.StandardType.E6GraphNoneSteps
