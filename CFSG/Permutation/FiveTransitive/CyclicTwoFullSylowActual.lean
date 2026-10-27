module

public import CFSG.Permutation.FiveTransitive.CyclicTwoActualSemiregular
public import CFSG.Permutation.FiveTransitive.CyclicTwoFullSylowSemiregular
public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionEven

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoFullSylowActual

open MulAction FixedNormalizerAction

theorem exists_sylow_semiregular
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (v : Normalizer Q) (hv : orderOf v.val = 2)
    (hlocal : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 3)
    (hfour : (fixedBy X v.val \ fixedPoints Q X).ncard = 4)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) :
    ∃ A : Sylow 2 (Normalizer Q), Nat.card A = 32 ∧
      ∀ (g : A) (t : X), t ∉ fixedPoints Q X → v.val • t ≠ t →
        g.val.val • t = t → g = 1 := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  obtain ⟨e,P,hvf,hp,hIB,hvB,hm,hk,hcomm,hcard,hfreeB,_⟩ :=
    CyclicTwoActualSemiregular.exists_sylow_semiregular
      heven hdegree hmax Q hQ hseven hfree S hS himage v hv hlocal hfour hzero
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let B := SylowPreimageNormalizer.ambient f V P
  let D := NormalizerFixedComplement.Domain (X := X) Q
  change IsPGroup 2 B at hp
  change Inside Q ≤ B at hIB
  change v ∈ B at hvB
  change B.map f = V at hm
  change B ⊓ f.ker = Inside Q at hk
  change IsMulCommutative B at hcomm
  change Nat.card B = 16 at hcard
  have hI : Nat.card (Inside Q) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  obtain ⟨a,ha,_⟩ := (Nat.card_eq_two_iff' (1 : Inside Q)).mp hI
  let J : Subgroup G := B.map (Normalizer Q).subtype
  have hQJ : Q ≤ J := by
    intro q hq
    exact ⟨⟨q,Q.le_normalizer hq⟩,hIB hq,rfl⟩
  have hJp : IsPGroup 2 J := hp.map _
  have hsingle (u : B) (p r : Fixed (X := X) Q) (hpr : p ≠ r)
      (hu : f u.val = Equiv.swap p r) : u.val ^ 2 = a.val := by
    have huQ : u.val.val ∉ Q := by
      intro huQ
      have huf : f u.val = 1 := FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q huQ
      rw [hu] at huf
      exact hpr (Equiv.swap_eq_one_iff.mp huf)
    have hloc := ThreeSwapEvenCounts.local_five Q hseven u.val p r hpr hu
    have hr0 := hzero J hQJ hJp u.val ⟨u.val,u.property,rfl⟩ huQ hloc
    exact CyclicTwoSwapSquare.square_eq_generator heven hdegree hmax Q hQ hseven
      B hk a ha u p r hpr hu hr0
  have ht0 : Equiv.swap (e 0) (e 1) ∈ V := Subgroup.subset_closure (by simp)
  obtain ⟨x,hxB,hxf⟩ := hm.ge ht0
  let x₀ : B := ⟨x,hxB⟩
  have hx2 : x₀.val ^ 2 = a.val := hsingle x₀ _ _ (e.injective.ne (by decide)) hxf
  let aB : B := ⟨a.val,hIB a.property⟩
  have haB2 : aB ^ 2 = 1 := Subtype.ext (congrArg (fun q : Inside Q => q.val) (show a ^ 2 = 1 by
    rw [← hI]; exact pow_card_eq_one' (x := a)))
  have haBne : aB ≠ 1 := fun he => ha (Subtype.ext (congrArg (fun b : B => b.val) he))
  have hafree (t : D) : aB • t ≠ t := by
    intro he
    exact ha (NormalizerFixedComplement.free_inside Q hfree a t he)
  obtain ⟨hxo,hxfree⟩ := CyclicTwoComplementCounts.free_zpowers_of_square
    x₀ aB haB2 haBne (Subtype.ext hx2) hafree
  obtain ⟨A,hBA,hkA,hkrA⟩ := FixedNormalizerFullSylow.exists_containing Q S hS B hp hIB
  have hAcard := FixedNormalizerFullSylow.card_eq_thirty_two Q hQ hseven himage A
    (hIB.trans hBA) hkrA
  let vB : B := ⟨v,hvB⟩
  have hvne : vB ≠ 1 := by
    intro he
    have hv1 : v.val = 1 := congrArg (fun b : B => b.val.val) he
    rw [hv1,orderOf_one] at hv
    omega
  have hvfour : (fixedBy D vB).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact (NormalizerFixedComplement.fixed_card Q v).trans hfour
  have hlocalEven : ∀ u : Normalizer Q, u ^ 2 = 1 → Equiv.Perm.sign (f u) = 1 :=
    NormalizerInvolutionEven.sign_eq_one heven hdegree hmax Q hQ hseven hfree S hS himage hzero
  have hfreeA := CyclicTwoFullSylowSemiregular.semiregular hmax Q hQ hfree A B hBA
    hAcard hcard hcomm hkA hk e hm a ha hlocalEven hsingle
    (fun u hu => CyclicTwoDoubleFibres.square_eq_one Q hQ himage e P hk v hv hvB hvf u hu)
    x₀ hxo hx2 hxfree vB hvne hvfour hfreeB
  refine ⟨A,hAcard,?_⟩
  intro g t ht hvnot hgt
  apply hfreeA g ⟨t,ht⟩
  · intro hh
    exact hvnot (congrArg Subtype.val hh)
  · exact Subtype.ext hgt

end FiveTransitive.CyclicTwoFullSylowActual

end CFSG
