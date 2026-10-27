module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Permutation
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u v

private theorem eq_bot_of_isPGroup_two_of_odd_card
    {G : Type*} [Group G] [Finite G] (A : Subgroup G)
    (hA_two : IsPGroup 2 A) (hA_odd : Odd (Nat.card A)) :
    A = ⊥ := by
  obtain ⟨n, hn⟩ := hA_two.exists_card_eq
  have hn_zero : n = 0 := by
    by_contra hn_ne
    have hEven : Even (Nat.card A) := by
      rw [hn]
      exact even_two.pow_of_ne_zero hn_ne
    exact (Nat.not_even_iff_odd.mpr hA_odd) hEven
  apply Subgroup.card_eq_one.mp
  simpa [hn_zero] using hn

/-- The rank-one data supplied by Proposition 8.4 form Peterfalvi's local
Hypothesis (A1) inside `N_X(Y)`. -/
public theorem normalizer_fixedPoint_hypothesisA1
    {X : Type u} [Group X] [Finite X]
    (M Y F S : Subgroup X) (t : X)
    (htN : t ∈ Subgroup.normalizer (Y : Set X))
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hYDt : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({t} : Set X))
    (hFleN : F ≤ Subgroup.normalizer (Y : Set X))
    (htwo : IsTwoTransitiveOn F
      (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y))
    (hSle : S ≤ normalizerIn M Y)
    (hSnormal : (S.subgroupOf (normalizerIn M Y)).Normal)
    (hSp : IsPGroup 2 S)
    (hSeven : Even (Nat.card S))
    (hSfactor :
      (normalizerIn M Y : Set X) =
        (S : Set X) * (normalizerIn (M ⊓ rightConjugate M t) Y : Set X)) :
    let N : Subgroup X := Subgroup.normalizer (Y : Set X)
    let D0 : Subgroup X := M ⊓ rightConjugate M t
    let H0 : Subgroup X := normalizerIn M Y
    let D1 : Subgroup X := normalizerIn D0 Y
    let tn : N := ⟨t, htN⟩
    let H : Subgroup N := H0.subgroupOf N
    let D : Subgroup N := D1.subgroupOf N
    let Q : Subgroup N := S.subgroupOf N
    let A : Type u :=
      {omega : conjugateCosetSpace M //
        omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y}
    letI : MulAction N A :=
      normalizerFixedPointAction X (conjugateCosetSpace M) Y
    HypothesisA1 N A H D Q tn := by
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  let D0 : Subgroup X := M ⊓ rightConjugate M t
  let H0 : Subgroup X := normalizerIn M Y
  let D1 : Subgroup X := normalizerIn D0 Y
  let tn : N := ⟨t, htN⟩
  let H : Subgroup N := H0.subgroupOf N
  let D : Subgroup N := D1.subgroupOf N
  let Q : Subgroup N := S.subgroupOf N
  let A : Type u :=
    {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y}
  letI : MulAction N A :=
    normalizerFixedPointAction X (conjugateCosetSpace M) Y
  change HypothesisA1 N A H D Q tn
  have htwoN : MulAction.IsMultiplyPretransitive N A 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨f, hfac, hfbd⟩ :=
      htwo a.property b.property c.property d.property
        (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
    let n : N := ⟨(f : X), hFleN f.property⟩
    refine ⟨n, ?_, ?_⟩
    · apply Subtype.ext
      exact hfac
    · apply Subtype.ext
      exact hfbd
  have hpoint : ∃ point : A, H = MulAction.stabilizer N point := by
    have hYM : Y ≤ M := hYDt.trans (inf_le_left.trans inf_le_left)
    let alpha : A :=
      ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints hYM⟩
    refine ⟨alpha, ?_⟩
    ext n
    constructor
    · intro hn
      change (n : X) ∈ H0 at hn
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      have hnStab : (n : X) ∈ MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
        rw [baseCoset_stabilizer]
        exact hn.1
      exact MulAction.mem_stabilizer_iff.mp hnStab
    · intro hn
      have hn' := MulAction.mem_stabilizer_iff.mp hn
      have hnval := congrArg Subtype.val hn'
      change (n : X) • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
        QuotientGroup.mk 1 at hnval
      have hnM : (n : X) ∈ M :=
        (show (n : X) ∈ MulAction.stabilizer X
            (QuotientGroup.mk 1 : conjugateCosetSpace M) from
          MulAction.mem_stabilizer_iff.mpr hnval) |> fun h => by
            rwa [baseCoset_stabilizer] at h
      exact ⟨hnM, n.property⟩
  have hD_eq : D = H ⊓ rightConjugate H tn := by
    ext x
    constructor
    · intro hx
      change (x : X) ∈ D1 at hx
      refine ⟨?_, ?_⟩
      · exact ⟨hx.1.1, x.property⟩
      · change x ∈ H.map (MulAut.conj tn⁻¹).toMonoidHom
        rw [Subgroup.mem_map]
        let yX : X := rightConjugateElem (x : X) t⁻¹
        have hyM : yX ∈ M := by
          apply rightConjugateElem_mem_of_mem_rightConjugate (g := t⁻¹)
          simpa [ht.inv_eq_self] using hx.1.2
        have hyN : yX ∈ N := by
          dsimp [yX]
          simpa [rightConjugateElem, ht.inv_eq_self] using
            N.mul_mem (N.mul_mem htN x.property) (N.inv_mem htN)
        let y : N := ⟨yX, hyN⟩
        refine ⟨y, ⟨hyM, hyN⟩, ?_⟩
        change (MulAut.conj tn⁻¹) y = x
        apply Subtype.ext
        simp only [MulAut.conj_apply]
        dsimp [y, yX, tn, rightConjugateElem]
        group
    · rintro ⟨hxH, hxHt⟩
      change (x : X) ∈ D1
      refine ⟨⟨hxH.1, ?_⟩, x.property⟩
      change x ∈ H.map (MulAut.conj tn⁻¹).toMonoidHom at hxHt
      rw [Subgroup.mem_map] at hxHt
      rcases hxHt with ⟨y, hyH, hxy⟩
      change (x : X) ∈ rightConjugate M t
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨(y : X), hyH.1, ?_⟩
      exact congrArg Subtype.val hxy
  have hQ_le_H : Q ≤ H := by
    intro q hq
    exact hSle hq
  have hD_le_H : D ≤ H := by
    intro d hd
    exact ⟨hd.1.1, d.property⟩
  have hQ_normal : (Q.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ_le_H]
    intro q k hq hk
    change (k : X) * (q : X) * (k : X)⁻¹ ∈ S
    apply (Subgroup.normal_subgroupOf_iff hSle).mp hSnormal
      (q : X) (k : X) hq hk
  have hD0odd : Odd (Nat.card D0) := by
    simpa [D0] using hM.inf_rightConjugate_card_odd htM
  have hD1le : D1 ≤ D0 := inf_le_left
  have hD1dvd : Nat.card D1 ∣ Nat.card D0 := by
    rw [← natCard_subgroupOf_eq D1 D0 hD1le]
    exact Subgroup.card_subgroup_dvd_card (D1.subgroupOf D0)
  have hD1odd : Odd (Nat.card D1) := Odd.of_dvd_nat hD0odd hD1dvd
  have hDcard : Nat.card D = Nat.card D1 :=
    natCard_subgroupOf_eq D1 N inf_le_right
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    exact hD1odd
  have hQcard : Nat.card Q = Nat.card S :=
    natCard_subgroupOf_eq S N (hSle.trans inf_le_right)
  have hQp : IsPGroup 2 Q := by
    exact hSp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (hSle.trans inf_le_right)).symm
  have hQ_disjoint_D : Disjoint Q D := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    let I : Subgroup N := Q ⊓ D
    have hInfP : IsPGroup 2 I := by
      exact (hQp.to_subgroup (I.subgroupOf Q)).of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_left)
    have hInfOdd : Odd (Nat.card I) := by
      have hIdvd : Nat.card I ∣ Nat.card D := by
        rw [← natCard_subgroupOf_eq I D inf_le_right]
        exact Subgroup.card_subgroup_dvd_card (I.subgroupOf D)
      exact Odd.of_dvd_nat hDodd hIdvd
    have hbot := eq_bot_of_isPGroup_two_of_odd_card I hInfP hInfOdd
    have hxbot : x ∈ (⊥ : Subgroup N) := by
      rw [← hbot]
      exact ⟨hxQ, hxD⟩
    simpa using hxbot
  have hQ_sup_D : Q ⊔ D = H := by
    apply le_antisymm (sup_le hQ_le_H hD_le_H)
    intro x hxH
    have hxProduct : (x : X) ∈ (S : Set X) * (D1 : Set X) := by
      rw [← hSfactor]
      exact hxH
    rw [Set.mem_mul] at hxProduct
    rcases hxProduct with ⟨s, hs, d, hd, hsd⟩
    let sn : N := ⟨s, (hSle hs).2⟩
    let dn : N := ⟨d, hd.2⟩
    have hsnQ : sn ∈ Q := hs
    have hdnD : dn ∈ D := hd
    have hxeq : x = sn * dn := by
      apply Subtype.ext
      exact hsd.symm
    rw [hxeq]
    exact (Q ⊔ D).mul_mem
      ((le_sup_left : Q ≤ Q ⊔ D) hsnQ)
      ((le_sup_right : D ≤ Q ⊔ D) hdnD)
  have hQeven : Even (Nat.card Q) := by
    rw [hQcard]
    exact hSeven
  exact
    { two_transitive := htwoN
      point_stabilizer := hpoint
      involution_t := BenderSuzuki.IsInvolution.subtype ht htN
      t_not_mem_H := by
        intro htnH
        exact htM htnH.1
      D_eq := hD_eq
      Q_le_H := hQ_le_H
      D_le_H := hD_le_H
      Q_normal_in_H := hQ_normal
      Q_disjoint_D := hQ_disjoint_D
      Q_sup_D := hQ_sup_D
      Q_even := hQeven
      D_odd := hDodd }

private theorem normalizer_fixedPoint_rankOne_count
    {X : Type u} [Group X] [Finite X]
    (M Y F S : Subgroup X) (t : X)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hYDt : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({t} : Set X))
    (hFleN : F ≤ Subgroup.normalizer (Y : Set X))
    (htwo : IsTwoTransitiveOn F
      (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y))
    (hSle : S ≤ normalizerIn M Y)
    (hSnormal : (S.subgroupOf (normalizerIn M Y)).Normal)
    (hSp : IsPGroup 2 S)
    (hSeven : Even (Nat.card S))
    (hSfactor :
      (normalizerIn M Y : Set X) =
        (S : Set X) * (normalizerIn (M ⊓ rightConjugate M t) Y : Set X)) :
    Nat.card {x : X //
        x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
          x ∈ Subgroup.normalizer (Y : Set X)} =
      Nat.card {z : normalizerIn M Y | IsInvolution (z : X)} := by
  let N : Subgroup X := Subgroup.normalizer (Y : Set X)
  let D0 : Subgroup X := M ⊓ rightConjugate M t
  let H0 : Subgroup X := normalizerIn M Y
  let D1 : Subgroup X := normalizerIn D0 Y
  have htN : t ∈ N := by
    apply centralizer_le_normalizer Y
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYDt hy).2
  let tn : N := ⟨t, htN⟩
  let H : Subgroup N := H0.subgroupOf N
  let D : Subgroup N := D1.subgroupOf N
  let Q : Subgroup N := S.subgroupOf N
  let A : Type u :=
    {omega : conjugateCosetSpace M //
      omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y}
  letI : MulAction N A :=
    normalizerFixedPointAction X (conjugateCosetSpace M) Y
  have htwoN : MulAction.IsMultiplyPretransitive N A 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    obtain ⟨f, hfac, hfbd⟩ :=
      htwo a.property b.property c.property d.property
        (fun h => hab (Subtype.ext h)) (fun h => hcd (Subtype.ext h))
    let n : N := ⟨(f : X), hFleN f.property⟩
    refine ⟨n, ?_, ?_⟩
    · apply Subtype.ext
      exact hfac
    · apply Subtype.ext
      exact hfbd
  have hpoint : ∃ point : A, H = MulAction.stabilizer N point := by
    have hYM : Y ≤ M := hYDt.trans (inf_le_left.trans inf_le_left)
    let alpha : A :=
      ⟨QuotientGroup.mk 1, theorem4b_baseCoset_mem_fixedPoints hYM⟩
    refine ⟨alpha, ?_⟩
    ext n
    constructor
    · intro hn
      change (n : X) ∈ H0 at hn
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      have hnStab : (n : X) ∈ MulAction.stabilizer X
          (QuotientGroup.mk 1 : conjugateCosetSpace M) := by
        rw [baseCoset_stabilizer]
        exact hn.1
      exact MulAction.mem_stabilizer_iff.mp hnStab
    · intro hn
      have hn' := MulAction.mem_stabilizer_iff.mp hn
      have hnval := congrArg Subtype.val hn'
      change (n : X) • (QuotientGroup.mk 1 : conjugateCosetSpace M) =
        QuotientGroup.mk 1 at hnval
      have hnM : (n : X) ∈ M :=
        (show (n : X) ∈ MulAction.stabilizer X
            (QuotientGroup.mk 1 : conjugateCosetSpace M) from
          MulAction.mem_stabilizer_iff.mpr hnval) |> fun h => by
            rwa [baseCoset_stabilizer] at h
      exact ⟨hnM, n.property⟩
  have hD_eq : D = H ⊓ rightConjugate H tn := by
    ext x
    constructor
    · intro hx
      change (x : X) ∈ D1 at hx
      refine ⟨?_, ?_⟩
      · exact ⟨hx.1.1, x.property⟩
      · change x ∈ H.map (MulAut.conj tn⁻¹).toMonoidHom
        rw [Subgroup.mem_map]
        let yX : X := rightConjugateElem (x : X) t⁻¹
        have hyM : yX ∈ M := by
          apply rightConjugateElem_mem_of_mem_rightConjugate (g := t⁻¹)
          simpa [ht.inv_eq_self] using hx.1.2
        have hyN : yX ∈ N := by
          dsimp [yX]
          simpa [rightConjugateElem, ht.inv_eq_self] using
            N.mul_mem (N.mul_mem htN x.property) (N.inv_mem htN)
        let y : N := ⟨yX, hyN⟩
        refine ⟨y, ⟨hyM, hyN⟩, ?_⟩
        change (MulAut.conj tn⁻¹) y = x
        apply Subtype.ext
        simp only [MulAut.conj_apply]
        dsimp [y, yX, tn, rightConjugateElem]
        group
    · rintro ⟨hxH, hxHt⟩
      change (x : X) ∈ D1
      refine ⟨⟨hxH.1, ?_⟩, x.property⟩
      change x ∈ H.map (MulAut.conj tn⁻¹).toMonoidHom at hxHt
      rw [Subgroup.mem_map] at hxHt
      rcases hxHt with ⟨y, hyH, hxy⟩
      change (x : X) ∈ rightConjugate M t
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨(y : X), hyH.1, ?_⟩
      exact congrArg Subtype.val hxy
  have hQ_le_H : Q ≤ H := by
    intro q hq
    exact hSle hq
  have hD_le_H : D ≤ H := by
    intro d hd
    exact ⟨hd.1.1, d.property⟩
  have hQ_normal : (Q.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ_le_H]
    intro q k hq hk
    change (k : X) * (q : X) * (k : X)⁻¹ ∈ S
    apply (Subgroup.normal_subgroupOf_iff hSle).mp hSnormal
      (q : X) (k : X) hq hk
  have hD0odd : Odd (Nat.card D0) := by
    simpa [D0] using hM.inf_rightConjugate_card_odd htM
  have hD1le : D1 ≤ D0 := inf_le_left
  have hD1dvd : Nat.card D1 ∣ Nat.card D0 := by
    rw [← natCard_subgroupOf_eq D1 D0 hD1le]
    exact Subgroup.card_subgroup_dvd_card (D1.subgroupOf D0)
  have hD1odd : Odd (Nat.card D1) :=
    Odd.of_dvd_nat hD0odd hD1dvd
  have hDcard : Nat.card D = Nat.card D1 :=
    natCard_subgroupOf_eq D1 N inf_le_right
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    exact hD1odd
  have hQcard : Nat.card Q = Nat.card S :=
    natCard_subgroupOf_eq S N (hSle.trans inf_le_right)
  have hQp : IsPGroup 2 Q := by
    exact hSp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (hSle.trans inf_le_right)).symm
  have hQ_disjoint_D : Disjoint Q D := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    let I : Subgroup N := Q ⊓ D
    have hInfP : IsPGroup 2 I := by
      exact (hQp.to_subgroup (I.subgroupOf Q)).of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_left)
    have hInfOdd : Odd (Nat.card I) := by
      have hIdvd : Nat.card I ∣ Nat.card D := by
        rw [← natCard_subgroupOf_eq I D inf_le_right]
        exact Subgroup.card_subgroup_dvd_card (I.subgroupOf D)
      exact Odd.of_dvd_nat hDodd hIdvd
    have hbot := eq_bot_of_isPGroup_two_of_odd_card I hInfP hInfOdd
    have hxbot : x ∈ (⊥ : Subgroup N) := by
      rw [← hbot]
      exact ⟨hxQ, hxD⟩
    simpa using hxbot
  have hQ_sup_D : Q ⊔ D = H := by
    apply le_antisymm (sup_le hQ_le_H hD_le_H)
    intro x hxH
    have hxProduct : (x : X) ∈ (S : Set X) * (D1 : Set X) := by
      rw [← hSfactor]
      exact hxH
    rw [Set.mem_mul] at hxProduct
    rcases hxProduct with ⟨s, hs, d, hd, hsd⟩
    let sn : N := ⟨s, (hSle hs).2⟩
    let dn : N := ⟨d, hd.2⟩
    have hsnQ : sn ∈ Q := hs
    have hdnD : dn ∈ D := hd
    have hxeq : x = sn * dn := by
      apply Subtype.ext
      exact hsd.symm
    rw [hxeq]
    exact (Q ⊔ D).mul_mem
      ((le_sup_left : Q ≤ Q ⊔ D) hsnQ)
      ((le_sup_right : D ≤ Q ⊔ D) hdnD)
  have hQeven : Even (Nat.card Q) := by
    rw [hQcard]
    exact hSeven
  have hA1 : HypothesisA1 N A H D Q tn :=
    { two_transitive := htwoN
      point_stabilizer := hpoint
      involution_t := BenderSuzuki.IsInvolution.subtype ht htN
      t_not_mem_H := by
        intro htnH
        exact htM htnH.1
      D_eq := hD_eq
      Q_le_H := hQ_le_H
      D_le_H := hD_le_H
      Q_normal_in_H := hQ_normal
      Q_disjoint_D := hQ_disjoint_D
      Q_sup_D := hQ_sup_D
      Q_even := hQeven
      D_odd := hDodd }
  let LocalK : Type u := {x : N // x ∈ peterfalviKSet D tn}
  let AmbientK : Type u := {x : X //
    x ∈ peterfalviKSet D0 t ∧ x ∈ N}
  let eK : LocalK ≃ AmbientK :=
    { toFun := fun x =>
        ⟨((x : N) : X), by
          have hxD : ((x : N) : X) ∈ D1 := x.property.1
          refine ⟨⟨hxD.1, ?_⟩, (x : N).property⟩
          have hanti := congrArg Subtype.val x.property.2
          simpa [tn, rightConjugateElem] using hanti⟩
      invFun := fun x =>
        ⟨⟨(x : X), x.property.2⟩, by
          refine ⟨⟨x.property.1.1, x.property.2⟩, ?_⟩
          apply Subtype.ext
          simpa [tn, rightConjugateElem] using x.property.1.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }
  let LocalHInv : Type u :=
    {z : N // z ∈ H ∧ IsInvolution z}
  let AmbientHInv : Type u :=
    {z : H0 // IsInvolution (z : X)}
  let eH : LocalHInv ≃ AmbientHInv :=
    { toFun := fun z =>
        ⟨⟨((z : N) : X), (show ((z : N) : X) ∈ H0 from z.property.1)⟩,
          BenderSuzuki.IsInvolution.map_of_injective z.property.2
            N.subtype N.subtype_injective⟩
      invFun := fun z =>
        ⟨⟨((z : H0) : X), (z : H0).property.2⟩, by
          refine ⟨⟨(z : H0).property.1, (z : H0).property.2⟩, ?_⟩
          exact BenderSuzuki.IsInvolution.subtype
            z.property (z : H0).property.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        rfl
      right_inv := by
        intro z
        apply Subtype.ext
        rfl }
  have hlocal := (proposition_3 H D Q tn hA1).1
  calc
    Nat.card AmbientK = Nat.card LocalK :=
      (Nat.card_congr eK).symm
    _ = Nat.card LocalHInv := by simpa [LocalK, LocalHInv] using hlocal
    _ = Nat.card AmbientHInv := Nat.card_congr eH



/-- Proposition 8.4 and Peterfalvi's rank-one count identify the involutions
of the local normalizer with the selected Peterfalvi normalizer subgroup. -/
public theorem Proposition84Statement.normalizerIn_involutions_card_eq
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {t : X}
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    {Y : Subgroup X}
    (hYV : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({d83.u} : Set X))
    (hYne : Y ≠ ⊥)
    (hI : HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y)
    (J : Subgroup X)
    (hJ : (J : Set X) =
      {x : X | x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
        x ∈ Subgroup.normalizer (Y : Set X)}) :
    Nat.card {z : normalizerIn M Y | IsInvolution (z : X)} =
      Nat.card J := by
  have hsubnormal : (Y.subgroupOf Y).IsSubnormal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  obtain ⟨hAB, _hCD⟩ :=
    h84 Y Y hYV hYne le_rfl hsubnormal hI
  dsimp [Proposition84ABConclusion] at hAB
  rcases hAB with
    ⟨htwo, _hNormalizer, S, hSle, hSnormal, hSsylow,
      _hSregular, hSfactor⟩
  have hYDt : Y ≤ (M ⊓ rightConjugate M t) ⊓
      Subgroup.centralizer ({t} : Set X) := by
    rw [d83.centralizer_eq]
    exact hYV
  have hFleN : centralizerTwoPrimeResidual Y ≤
      Subgroup.normalizer (Y : Set X) :=
    (BenderSuzuki.centralizerTwoPrimeResidual_le_centralizer Y).trans
      (centralizer_le_normalizer Y)
  obtain ⟨P, hSdef⟩ := hSsylow
  have hSp : IsPGroup 2 S := by
    rw [hSdef]
    exact P.isPGroup'.map
      (centralizerTwoPrimeResidual Y ⊓ M).subtype
  have huC : d83.u ∈ Subgroup.centralizer (Y : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYV hy).2
  have huF : d83.u ∈ centralizerTwoPrimeResidual Y :=
    (zpowers_le_centralizerTwoPrimeResidual_of_isInvolution
      Y d83.u_involution huC) (Subgroup.mem_zpowers d83.u)
  have huFM : d83.u ∈ centralizerTwoPrimeResidual Y ⊓ M :=
    ⟨huF, d83.u_mem_M⟩
  have htwoAmbient : 2 ∣
      Nat.card ↥(centralizerTwoPrimeResidual Y ⊓ M) := by
    have hzle : Subgroup.zpowers
        (⟨d83.u, huFM⟩ : ↥(centralizerTwoPrimeResidual Y ⊓ M)) ≤ ⊤ :=
      le_top
    have hzcard : Nat.card (Subgroup.zpowers
        (⟨d83.u, huFM⟩ : ↥(centralizerTwoPrimeResidual Y ⊓ M))) = 2 := by
      rw [Nat.card_zpowers]
      exact (orderOf_eq_prime_iff).2
        ⟨(IsInvolution.subtype d83.u_involution huFM).sq_eq_one,
          (IsInvolution.subtype d83.u_involution huFM).ne_one⟩
    rw [← hzcard]
    simpa only [Subgroup.card_top] using Subgroup.card_dvd_of_le hzle
  have htwoP : 2 ∣ Nat.card
      (P : Subgroup ↥(centralizerTwoPrimeResidual Y ⊓ M)) :=
    Sylow.dvd_card_of_dvd_card P htwoAmbient
  have hmapCard :
      Nat.card ((P : Subgroup
          ↥(centralizerTwoPrimeResidual Y ⊓ M)).map
        (centralizerTwoPrimeResidual Y ⊓ M).subtype) =
        Nat.card (P : Subgroup
          ↥(centralizerTwoPrimeResidual Y ⊓ M)) :=
    Subgroup.card_map_of_injective
      (centralizerTwoPrimeResidual Y ⊓ M).subtype_injective
  have hSeven : Even (Nat.card S) := by
    rw [hSdef, hmapCard]
    exact even_iff_two_dvd.mpr htwoP
  have hcount := normalizer_fixedPoint_rankOne_count
    M Y (centralizerTwoPrimeResidual Y) S t hM ht htM hYDt
      hFleN htwo hSle hSnormal hSp hSeven hSfactor
  have hJcount :
      Nat.card J =
        Nat.card {x : X //
          x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧
            x ∈ Subgroup.normalizer (Y : Set X)} :=
    Nat.card_congr (Set.equivOfEq hJ)
  exact hcount.symm.trans hJcount.symm

end CFSG.BenderSuzuki
