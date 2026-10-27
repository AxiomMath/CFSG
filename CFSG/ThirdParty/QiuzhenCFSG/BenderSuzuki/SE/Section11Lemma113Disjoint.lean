module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113Callbacks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingCounting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Corollary713

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.3: the disjoint branch

These helpers formalize the group-theoretic part of the branch
`M° ∩ [E,E] = 1`.  An invariant Sylow `2`-subgroup contains a central
involution.  Peterfalvi transitivity then puts every involution of `M` in its
center, so the involution core is elementary abelian.  The resulting
cardinality identity is the exact input to the numerical `[II1; 4.7]`
callback.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The Peterfalvi anti-fixed set has the same cardinality as the set of
involutions in the strongly embedded subgroup. -/
public theorem lemma113_peterfalviKSet_card_eq_involutionsInSet
    {X : Type u} [Group X] [Finite X]
    {M : Subgroup X} {z t : X}
    (hM : IsStronglyEmbedded M)
    (hzM : z ∈ M) (hz : IsInvolution z)
    (ht : IsInvolution t) (htM : t ∉ M) :
    Nat.card {k : X //
      k ∈ peterfalviKSet (M ⊓ rightConjugate M t) t} =
      Nat.card {y : X // y ∈ involutionsInSet M} := by
  let I := {k : X //
    k ∈ peterfalviKSet (M ⊓ rightConjugate M t) t}
  let Z := {y : X // y ∈ involutionsInSet M}
  let F : I → Z := fun k =>
    ⟨rightConjugateElem z (k : X),
      ⟨by
        have hkM : (k : X) ∈ M := k.property.1.1
        dsimp [rightConjugateElem]
        exact M.mul_mem (M.mul_mem (M.inv_mem hkM) hzM) hkM,
       isInvolution_rightConjugateElem hz⟩⟩
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨k, hkI, hzy⟩ :=
      hM.exists_mem_peterfalviKSet_of_involution_mem
        hzM hz ht htM y.property.1 y.property.2
    refine ⟨⟨k, hkI⟩, ?_⟩
    exact Subtype.ext hzy
  have hFinj : Function.Injective F := by
    intro k1 k2 hk12
    have hconj :
        rightConjugateElem z (k1 : X) =
          rightConjugateElem z (k2 : X) :=
      congrArg Subtype.val hk12
    have hcentral : (k1 : X) * (k2 : X)⁻¹ ∈
        Subgroup.centralizer ({z} : Set X) :=
      mul_inv_mem_centralizer_singleton_iff_rightConjugateElem_eq.mpr hconj
    let s1 : X := (k1 : X) * t
    let s2 : X := (k2 : X) * t
    have hsInv (k : I) : IsInvolution ((k : X) * t) := by
      have htk : t * (k : X) * t = (k : X)⁻¹ := by
        simpa [rightConjugateElem, ht.inv_eq_self] using k.property.2
      have hsq : ((k : X) * t) ^ 2 = 1 := by
        rw [pow_two]
        calc
          ((k : X) * t) * ((k : X) * t) =
              (k : X) * (t * (k : X) * t) := by group
          _ = (k : X) * (k : X)⁻¹ := by rw [htk]
          _ = 1 := by simp
      refine ⟨?_, hsq⟩
      intro hone
      apply htM
      have hkM : (k : X) ∈ M := k.property.1.1
      have htEq : t = (k : X)⁻¹ * ((k : X) * t) := by simp
      rw [htEq, hone]
      simpa using M.inv_mem hkM
    have hs1Inv : IsInvolution s1 := by simpa [s1] using hsInv k1
    have hs2Inv : IsInvolution s2 := by simpa [s2] using hsInv k2
    have hs2notM : s2 ∉ M := by
      intro hs2M
      apply htM
      have hk2M : (k2 : X) ∈ M := k2.property.1.1
      have htEq : t = (k2 : X)⁻¹ * s2 := by simp [s2]
      rw [htEq]
      exact M.mul_mem (M.inv_mem hk2M) hs2M
    have hcoset : s1 * s2⁻¹ ∈
        Subgroup.centralizer ({z} : Set X) := by
      have heq : s1 * s2⁻¹ = (k1 : X) * (k2 : X)⁻¹ := by
        simp [s1, s2]
      rw [heq]
      exact hcentral
    obtain ⟨u, hu, huUnique⟩ :=
      hM.existsUnique_involution_in_centralizer_rightCoset
        hzM hz hs2notM
    have hs1u : s1 = u := huUnique s1 ⟨hcoset, hs1Inv⟩
    have hs2u : s2 = u := huUnique s2 ⟨by simp, hs2Inv⟩
    apply Subtype.ext
    have hs12 : s1 = s2 := hs1u.trans hs2u.symm
    have hcancel := congrArg (fun x : X => x * t⁻¹) hs12
    simpa [s1, s2, mul_assoc] using hcancel
  exact Nat.card_congr (Equiv.ofBijective F ⟨hFinj, hFsurj⟩)

/-- If the Peterfalvi set lies in a subgroup preserving a Sylow `2`-subgroup
of the involution core, then the core is elementary abelian of order `2^b`
for some `b ≥ 2`, and the Peterfalvi set has order `2^b - 1`. -/
public theorem lemma113_invariant_sylow_two_forces_core_card
    {X : Type u} [Group X] [Finite X]
    {M H : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hHnormC : H ≤ Subgroup.normalizer
      ((involutionCoreIn M : Subgroup X) : Set X))
    (S : Sylow 2 (involutionCoreIn M))
    (hSinv :
      let _ : Subgroup.Normalizes H (involutionCoreIn M) := ⟨hHnormC⟩
      IsInvariant H (involutionCoreIn M)
        (S : Subgroup (involutionCoreIn M)))
    (hIleH : peterfalviKSet
      (M ⊓ rightConjugate M t) t ⊆ H) :
    ∃ b : ℕ,
      2 ≤ b ∧
        Nat.card (involutionCoreIn M) = 2 ^ b ∧
        Nat.card {k : X // k ∈ peterfalviKSet
          (M ⊓ rightConjugate M t) t} = 2 ^ b - 1 := by
  classical
  let C : Subgroup X := involutionCoreIn M
  let S0 : Subgroup C := (S : Subgroup C)
  have hCM : C ≤ M := by
    simpa [C] using involutionCoreIn_le M
  let fX : involutionCore M →* X :=
    M.subtype.comp (involutionCore M).subtype
  let fC : involutionCore M →* C :=
    fX.codRestrict C (by
      intro z
      exact Subgroup.mem_map_of_mem M.subtype z.property)
  have hfC : Function.Injective fC := by
    intro a b hab
    have habX : ((a : M) : X) = ((b : M) : X) := by
      change fX a = fX b
      exact congrArg (fun z : C => (z : X)) hab
    exact Subtype.ext (Subtype.ext habX)
  have hrankC : TwoRankAtLeastTwo C :=
    hrank.map_of_injective fC hfC
  obtain ⟨E, hEcard, _hEsq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hrankC
  have htwoC : 2 ∣ Nat.card C := by
    have hfourC : 4 ∣ Nat.card C := by
      simpa [hEcard] using Subgroup.card_subgroup_dvd_card E
    exact dvd_trans (by norm_num : 2 ∣ 4) hfourC
  have hSne : S0 ≠ ⊥ := by
    simpa [S0] using S.ne_bot_of_dvd_card htwoC
  letI : Nontrivial S0 :=
    (Subgroup.nontrivial_iff_ne_bot S0).2 hSne
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCenterNontrivial : Nontrivial (Subgroup.center S0) := by
    simpa [S0] using S.isPGroup'.center_nontrivial
  have hCenterTwo : IsPGroup 2 (Subgroup.center S0) := by
    have hS0p : IsPGroup 2 S0 := by
      simpa [S0] using S.isPGroup'
    exact hS0p.to_subgroup (Subgroup.center S0)
  have htwoCenter : 2 ∣ Nat.card (Subgroup.center S0) := by
    rcases (IsPGroup.nontrivial_iff_card
      (p := 2) (G := Subgroup.center S0) hCenterTwo).mp
        hCenterNontrivial with ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hn)
  obtain ⟨z0, hzOrder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := Subgroup.center S0) 2 htwoCenter
  let zS : S0 := (z0 : S0)
  let zC : C := (zS : C)
  let z : X := (zC : X)
  have hzOrderS : orderOf zS = 2 := by
    simpa [zS] using (Subgroup.orderOf_coe z0).trans hzOrder
  have hzData := orderOf_eq_prime_iff.mp hzOrderS
  have hzInvS : IsInvolution zS := ⟨hzData.2, hzData.1⟩
  have hzInvC : IsInvolution zC :=
    IsInvolution.map_of_injective hzInvS S0.subtype
      S0.subtype_injective
  have hzInv : IsInvolution z :=
    IsInvolution.map_of_injective hzInvC C.subtype
      C.subtype_injective
  have hzM : z ∈ M := hCM zC.property
  letI : Subgroup.Normalizes H C :=
    ⟨by simpa [C] using hHnormC⟩
  have hSinv' : IsInvariant H C S0 := by
    simpa [C, S0] using hSinv
  letI : IsInvariant H C S0 := hSinv'
  letI : IsInvariant H S0 (Subgroup.center S0) := center_isInvariant
  let ZS : Subgroup C := (Subgroup.center S0).map S0.subtype
  have hZSinv : IsInvariant H C ZS := by
    simpa [ZS] using
      (isInvariant_map_subtype S0 (Subgroup.center S0))
  letI : IsInvariant H C ZS := hZSinv
  have hzZS : zC ∈ ZS := by
    exact Subgroup.mem_map.mpr ⟨zS, z0.property, rfl⟩
  have hInvolutionsLeZS :
      ∀ (y : X) (hyM : y ∈ M) (hyInv : IsInvolution y),
        (⟨y, involution_mem_involutionCoreIn hyM hyInv⟩ : C) ∈ ZS := by
    intro y hyM hyInv
    obtain ⟨k, hkI, hzk⟩ :=
      hM.exists_mem_peterfalviKSet_of_involution_mem
        hzM hzInv ht htM hyM hyInv
    let kH : H := ⟨k, hIleH hkI⟩
    let yC : C := ⟨y, involution_mem_involutionCoreIn hyM hyInv⟩
    have hsmul : kH⁻¹ • zC ∈ ZS :=
      (IsInvariant.invariant
        (A := H) (G := C) (H := ZS) kH⁻¹ zC).1 hzZS
    have hsmulEq : kH⁻¹ • zC = yC := by
      apply Subtype.ext
      change ((kH⁻¹ • zC : C) : X) = y
      rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      simpa [rightConjugateElem, kH, zC, z] using hzk
    rwa [hsmulEq] at hsmul
  have hcoreLeZS : involutionCore C ≤ ZS := by
    rw [involutionCore_eq_closure, Subgroup.closure_le]
    intro x hx
    have hxInv : IsInvolution (x : X) :=
      IsInvolution.map_of_injective hx C.subtype C.subtype_injective
    have hxM : (x : X) ∈ M := hCM x.property
    simpa using hInvolutionsLeZS (x : X) hxM hxInv
  have hZSeq : ZS = ⊤ := by
    apply top_unique
    rw [← involutionCore_involutionCoreIn_eq_top M]
    simpa [C] using hcoreLeZS
  have hS0eq : S0 = ⊤ := by
    apply top_unique
    rw [← hZSeq]
    exact Subgroup.map_subtype_le (Subgroup.center S0)
  have hCcomm : IsMulCommutative C := by
    have hZScomm : IsMulCommutative ZS := by
      dsimp [ZS]
      infer_instance
    letI : IsMulCommutative ZS := hZScomm
    refine ⟨⟨?_⟩⟩
    intro x y
    let xZ : ZS := ⟨x, by rw [hZSeq]; exact Subgroup.mem_top x⟩
    let yZ : ZS := ⟨y, by rw [hZSeq]; exact Subgroup.mem_top y⟩
    exact congrArg Subtype.val (hZScomm.is_comm.comm xZ yZ)
  letI : IsMulCommutative C := hCcomm
  have hsqC : ∀ x : C, x ^ 2 = 1 := by
    intro x
    have hxcore : x ∈ involutionCore C := by
      rw [show involutionCore C = ⊤ by
        simpa [C] using involutionCore_involutionCoreIn_eq_top M]
      exact Subgroup.mem_top x
    rw [involutionCore_eq_closure] at hxcore
    exact Subgroup.closure_induction
      (p := fun y _hy => y ^ 2 = 1)
      (fun y hy => (show IsInvolution y from hy).sq_eq_one)
      (by simp)
      (by
        intro a b _ha _hb ha hb
        have habpow : (a * b) ^ 2 = a ^ 2 * b ^ 2 :=
          ((commute_iff_eq a b).mpr (hCcomm.is_comm.comm a b)).mul_pow 2
        rw [habpow]
        simp [ha, hb])
      (by
        intro a _ha ha
        simp [inv_pow, ha])
      hxcore
  obtain ⟨b, hScard⟩ := S.isPGroup'.exists_card_eq
  have hCcard : Nat.card C = 2 ^ b := by
    have hScard' : Nat.card S0 = 2 ^ b := by
      simpa [S0] using hScard
    rw [hS0eq] at hScard'
    simpa using hScard'
  have hb : 2 ≤ b := by
    have hfourLeC : 4 ≤ Nat.card C := by
      simpa [hEcard] using
        Nat.card_le_card_of_injective E.subtype E.subtype_injective
    rw [hCcard] at hfourLeC
    by_contra hnot
    have hb' : b = 0 ∨ b = 1 := by omega
    rcases hb' with rfl | rfl <;> norm_num at hfourLeC
  let Z := {y : X // y ∈ involutionsInSet M}
  let Csharp := {c : C // c ≠ 1}
  let eZC : Z ≃ Csharp :=
    { toFun := fun y =>
        ⟨⟨(y : X), involution_mem_involutionCoreIn
            y.property.1 y.property.2⟩,
          by
            intro hyOne
            exact y.property.2.ne_one
              (congrArg (fun q : C => (q : X)) hyOne)⟩
      invFun := fun c =>
        ⟨((c : C) : X),
          ⟨hCM (c : C).property,
            ⟨by
                intro hcOne
                exact c.property (Subtype.ext hcOne),
              congrArg Subtype.val (hsqC (c : C))⟩⟩⟩
      left_inv := by
        intro y
        rfl
      right_inv := by
        intro c
        rfl }
  have hZcard : Nat.card Z = Nat.card C - 1 := by
    calc
      Nat.card Z = Nat.card Csharp := Nat.card_congr eZC
      _ = Nat.card C - 1 := by
        letI : Fintype C := Fintype.ofFinite C
        letI : Fintype Csharp := Fintype.ofFinite Csharp
        simpa [Csharp, Nat.card_eq_fintype_card] using
          (Fintype.card_subtype_compl (fun c : C => c = 1))
  have hIcard : Nat.card {k : X // k ∈ peterfalviKSet
      (M ⊓ rightConjugate M t) t} = 2 ^ b - 1 := by
    calc
      Nat.card {k : X // k ∈ peterfalviKSet
          (M ⊓ rightConjugate M t) t} = Nat.card Z := by
        simpa [Z] using
          lemma113_peterfalviKSet_card_eq_involutionsInSet
            hM hzM hzInv ht htM
      _ = Nat.card C - 1 := hZcard
      _ = 2 ^ b - 1 := by rw [hCcard]
  exact ⟨b, hb, by simpa [C] using hCcard, hIcard⟩

/-- In the disjoint branch, the existing Sylow-coprimality and invariant
Sylow reductions supply the hypotheses of the preceding cardinal theorem. -/
public theorem lemma113_disjoint_branch_endpoint
    {X : Type u} [Group X] [Finite X]
    {r : ℕ} {M H : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (hr : r.Prime)
    (hHleM : H ≤ M)
    (hHsyl : theorem4bIsSylowSubgroupOf r H M)
    (hCnormal :
      ((involutionCoreIn M).subgroupOf M).Normal)
    (hinf : involutionCoreIn M ⊓ H = ⊥)
    (hHnormC : H ≤ Subgroup.normalizer
      ((involutionCoreIn M : Subgroup X) : Set X))
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hIleH : peterfalviKSet
      (M ⊓ rightConjugate M t) t ⊆ H) :
    ∃ b : ℕ,
      2 ≤ b ∧
        Nat.card (involutionCoreIn M) = 2 ^ b ∧
        Nat.card {k : X // k ∈ peterfalviKSet
          (M ⊓ rightConjugate M t) t} = 2 ^ b - 1 := by
  have hcop : Nat.Coprime r (Nat.card (involutionCoreIn M)) :=
    lemma113_coprime_card_of_normal_disjoint_sylow
      hr (involutionCoreIn_le M) hHleM hHsyl hCnormal hinf
  have hHp : IsPGroup r H := by
    rcases hHsyl with ⟨P, rfl⟩
    exact P.isPGroup'.map M.subtype
  obtain ⟨S, hSinv⟩ :=
    lemma113_exists_invariant_sylow_two
      hr hHp hHnormC hcop
  exact lemma113_invariant_sylow_two_forces_core_card
    hM ht htM hrank hHnormC S hSinv hIleH

end CFSG.BenderSuzuki
