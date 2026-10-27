module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofOuter

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

open Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
open scoped MatrixGroups

variable
  {L : Type} [Field L]

abbrev thetaVec : Fin TwistTag.D4.tag.rank → ℤ := d4Vec ![1, 1, 2, 1]

variable (L) in
noncomputable abbrev thetaPair : Subgroup (ModGL TwistTag.D4.tag L) :=
  rootSubgroup TwistTag.D4.tag L thetaVec ⊔ rootSubgroup TwistTag.D4.tag L (-thetaVec)

theorem range_rankOneHom_eq (i : Fin TwistTag.D4.tag.rank) :
    (rankOneHom TwistTag.D4 L i).range = rootSubgroup TwistTag.D4.tag L (Pi.single i 1) ⊔
      rootSubgroup TwistTag.D4.tag L (-Pi.single i 1) := by
  have h1 : pinnedX TwistTag.D4.tag L (Pi.single i 1) = xUnit TwistTag.D4.tag L i :=
    funext (pinnedX_single TwistTag.D4.tag L i)
  have h2 : pinnedX TwistTag.D4.tag L (-Pi.single i 1) = yUnit TwistTag.D4.tag L i :=
    funext (pinnedX_neg_single TwistTag.D4.tag L i)
  rw [rankOneHom_range, Subgroup.closure_union, rootSubgroup, rootSubgroup, h1, h2]

theorem commute_of_mem_rootPair_single {i : Fin TwistTag.D4.tag.rank} (hi : i ≠ n2)
    {x y : ModGL TwistTag.D4.tag L} (hx : x ∈ rootSubgroup TwistTag.D4.tag L (Pi.single i 1) ⊔
      rootSubgroup TwistTag.D4.tag L (-Pi.single i 1)) (hy : y ∈ thetaPair L) :
    x * y = y * x := by
  obtain ⟨hθ, hcheck⟩ := d4_outer_theta_check
  obtain ⟨hi1, h0, hp, hm⟩ := hcheck i hi
  exact commute_of_mem_rootPair_of_check hi1 hθ h0 hp hm hx hy

theorem rankOneHom_mul_comm_of_mem_thetaPair {i : Fin TwistTag.D4.tag.rank} (hi : i ≠ n2)
    (A : SL2 L) {y : ModGL TwistTag.D4.tag L} (hy : y ∈ thetaPair L) :
    rankOneHom TwistTag.D4 L i A * y = y * rankOneHom TwistTag.D4 L i A := by
  have hx : rankOneHom TwistTag.D4 L i A ∈ (rankOneHom TwistTag.D4 L i).range := ⟨A, rfl⟩
  rw [range_rankOneHom_eq] at hx
  exact commute_of_mem_rootPair_single hi hx hy

theorem commute_outerTriple_of_mem_thetaPair (A : SL2 L × SL2 L × SL2 L)
    {y : ModGL TwistTag.D4.tag L} (hy : y ∈ thetaPair L) :
    outerTriple L A * y = y * outerTriple L A := by
  have c0 := rankOneHom_mul_comm_of_mem_thetaPair (i := n0) (by decide) A.1 hy
  have c1 := rankOneHom_mul_comm_of_mem_thetaPair (i := n1) (by decide) A.2.1 hy
  have c3 := rankOneHom_mul_comm_of_mem_thetaPair (i := n3) (by decide) A.2.2 hy
  rw [outerTriple_apply]
  exact ((Commute.mul_left c0 c1).mul_left c3).eq

variable (L) in
@[expose] noncomputable def thetaConj : ModGL TwistTag.D4.tag L :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) L (TwistTag.D4.orbitReflection d4Middle) *
    canonicalRep (coxeterSystem TwistTag.D4.tag) L
      (TwistTag.D4.orbitReflection KS11Lie4Proof.d4Outer)

theorem d4HT_eq_thetaConj {K : Type} [Field K] (σ : K ≃+* K) : d4HT σ = thetaConj K := by
  obtain ⟨-, -, -, -, -, h1, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom d4Middle
  obtain ⟨-, -, -, -, -, h2, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer
  simp only [d4HT, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, List.prod_cons, List.prod_nil, mul_one]
  rw [h1, h2]
  rfl

theorem thetaConj_eq_triEmb {K : Type} [Field K] [Algebra K L] (σ : K ≃+* K) :
    thetaConj L = triEmb K σ L ⟨d4HT σ, d4HT_mem σ⟩ := by
  rw [triEmb_apply]
  change thetaConj L = baseChangeGL (algebraMap K L) (d4HT σ)
  rw [d4HT_eq_thetaConj, thetaConj, thetaConj, map_mul, baseChangeGL_canonicalRep,
    baseChangeGL_canonicalRep]

theorem thetaConj_mem_adjointGroup : thetaConj L ∈ adjointGroup TwistTag.D4.tag L :=
  mul_mem (canonicalRep_mem_adjointGroup _ L _) (canonicalRep_mem_adjointGroup _ L _)

theorem twistHom_thetaConj {K : Type} [Field K] [Algebra K L] (σ : K ≃+* K) (Fr : L →+* L)
    (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L)) :
    twistHom TwistTag.D4 L Fr (thetaConj L) = thetaConj L := by
  rw [thetaConj_eq_triEmb σ]
  exact triEmb_fixed Fr hcomm _

variable (L) in
@[expose] noncomputable def thetaHom : SL2 L →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (thetaConj L)).toMonoidHom.comp (rankOneHom TwistTag.D4 L n2)

theorem thetaHom_apply (A : SL2 L) :
    thetaHom L A = thetaConj L * rankOneHom TwistTag.D4 L n2 A * (thetaConj L)⁻¹ := rfl

theorem thetaHom_mem_adjointGroup (A : SL2 L) :
    thetaHom L A ∈ adjointGroup TwistTag.D4.tag L :=
  mul_mem (mul_mem thetaConj_mem_adjointGroup (rankOneHom_mem_adjointGroup_D4 _ _))
    (inv_mem thetaConj_mem_adjointGroup)

theorem range_thetaHom : (thetaHom L).range = thetaPair L := by
  have h := map_conj_orbitN_list_rootPair (K := L) TwistTag.D4 (RingEquiv.refl L).toRingHom
    [KS11Lie4Proof.d4Outer, d4Middle] (isRoot_single _ n2)
  have h' : ([KS11Lie4Proof.d4Outer, d4Middle].map fun a =>
      (orbitN TwistTag.D4 L (RingEquiv.refl L).toRingHom a 1 :
        ModGL TwistTag.D4.tag L)).reverse.prod = thetaConj L :=
    d4HT_eq_thetaConj (RingEquiv.refl L)
  rw [h', d4_fold_root] at h
  rw [thetaHom, MonoidHom.range_comp, range_rankOneHom_eq]
  exact h

theorem thetaHom_mem_thetaPair (A : SL2 L) : thetaHom L A ∈ thetaPair L := by
  rw [← range_thetaHom]
  exact ⟨A, rfl⟩

theorem commute_outerTriple_thetaHom (A : SL2 L × SL2 L × SL2 L) (B : SL2 L) :
    outerTriple L A * thetaHom L B = thetaHom L B * outerTriple L A :=
  commute_outerTriple_of_mem_thetaPair A (thetaHom_mem_thetaPair B)

theorem rootChar_zpow_tuple (t : Lˣ) (c v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (fun j => t ^ c j) v = t ^ (∑ j, c j * v j) := by
  rw [rootChar, ← prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun j _ => (zpow_mul t (c j) (v j)).symm

theorem thetaExp_check : ∀ i : Fin TwistTag.D4.tag.rank,
    ∑ j, TwistTag.D4.tag.cartan n2 j * wordVec [3, 1, 0, 2] (Pi.single i 1) j =
      if i = n2 then 1 else 0 := by
  decide

theorem thetaHom_HSL (t : Lˣ) :
    thetaHom L (HSL t) = rootDiagUnit TwistTag.D4.tag (Pi.mulSingle n2 t) := by
  have hm : TwistTag.D4.orbitReflection d4Middle = (coxeterSystem TwistTag.D4.tag).wordProd [2] :=
    by rw [TwistTag.orbitReflection, show TwistTag.D4.orbitWord d4Middle = [2] by decide]
  have ho : TwistTag.D4.orbitReflection KS11Lie4Proof.d4Outer =
      (coxeterSystem TwistTag.D4.tag).wordProd [0, 1, 3] := by
    rw [TwistTag.orbitReflection,
      show TwistTag.D4.orbitWord KS11Lie4Proof.d4Outer = [0, 1, 3] by decide]
  rw [thetaHom_apply, rankOneHom_HSL, LieType.Chevalley.torusElt_eq_rootDiagUnit, thetaConj,
    _root_.mul_inv_rev, show ∀ a b c d e : ModGL TwistTag.D4.tag L, a * b * c * (d * e) =
      a * (b * c * d) * e from fun a b c d e => by group, canonicalRep_conj_rootDiagUnit,
    canonicalRep_conj_rootDiagUnit, weylTuple_weylTuple, hm, ho,
    ← CoxeterSystem.wordProd_append]
  congr 1
  funext i
  rw [weylTuple, ← CoxeterSystem.wordProd_reverse, KS11Lie5Proof.wordProd_smul,
    rootChar_zpow_tuple]
  have h := thetaExp_check i
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h ⊢
  rw [h, Pi.mulSingle_apply]
  split_ifs <;> simp

theorem thetaHom_injective : Function.Injective (thetaHom L) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have hker := (exceptional_ordinary_rank_one_central_image (τ := TwistTag.D4.tag) (K := L)
    n2).choose_spec.2.2.2.2.2.1
  have h2 : rankOneHom TwistTag.D4 L n2 A = 1 := by
    rw [thetaHom_apply] at hA
    calc rankOneHom TwistTag.D4 L n2 A = (thetaConj L)⁻¹ * (thetaConj L *
          rankOneHom TwistTag.D4 L n2 A * (thetaConj L)⁻¹) * thetaConj L := by group
      _ = 1 := by rw [hA]; group
  obtain ⟨l, hl2, hl⟩ := hker A (MonoidHom.mem_ker.2 h2)
  have hl' : (l : L) = 1 ∨ (l : L) = -1 := by
    have : ((l : L) - 1) * ((l : L) + 1) = 0 := by linear_combination hl2
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hl' with h1 | h1
  · exact Subtype.ext (by rw [hl, h1, one_smul, Matrix.SpecialLinearGroup.coe_one])
  · have hA' : A = HSL (-1) := by
      rw [← neg_one_eq_HSL]
      exact Subtype.ext (by rw [hl, h1, neg_smul, one_smul, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one])
    have h3 : thetaHom L (HSL (-1)) = 1 := by rw [← hA']; exact hA
    rw [thetaHom_HSL, ← rootDiagUnit_one] at h3
    have h4 := congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h3) n2
    rw [Pi.mulSingle_eq_same, Pi.one_apply] at h4
    rw [hA', h4, HSL_units_one]

theorem twistHom_thetaHom (Fr : L →+* L)
    (hfix : twistHom TwistTag.D4 L Fr (thetaConj L) = thetaConj L) (A : SL2 L) :
    twistHom TwistTag.D4 L Fr (thetaHom L A) =
      thetaHom L (Matrix.SpecialLinearGroup.map Fr A) := by
  rw [thetaHom_apply, thetaHom_apply, map_mul, map_mul, map_inv, hfix, twistHom_rankOneHom_D4,
    show TwistTag.D4.perm n2 = n2 by decide]

end CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
