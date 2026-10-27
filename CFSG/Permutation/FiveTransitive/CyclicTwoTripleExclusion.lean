module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerTripleSwapSylow
public import CFSG.Permutation.FiveTransitive.CyclicTwoSwapSquare
public import CFSG.Permutation.FiveTransitive.CentralTwoTripleCommutation
public import CFSG.Permutation.FiveTransitive.CentralKernelSquareTransport
public import CFSG.Permutation.FiveTransitive.ThreeSwapNormalizerConjugators
public import CFSG.Permutation.FiveTransitive.NormalizerTwoElementInvolution
public import CFSG.Permutation.FiveTransitive.ZeroOrbitGeneratedFree
public import CFSG.Permutation.FiveTransitive.CentralFreeFixedDivisibility

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoTripleExclusion

open MulAction FixedNormalizerAction

private theorem four_dvd_complement
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
    (hlocal : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 1)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) :
    4 ∣ (fixedBy X v.val \ fixedPoints Q X).ncard := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, P, hvf, hp, hIP, hvP, hm, hk, hn, x, z, hxf, hzf⟩ :=
    FixedNormalizerTripleSwapSylow.exists_sylow Q hseven S hS himage v hv hlocal
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let B := SylowPreimageNormalizer.ambient f V P
  change B.map f = V at hm
  change B ⊓ f.ker = Inside Q at hk
  change IsPGroup 2 B at hp
  change Inside Q ≤ B at hIP
  have hcentral : ∀ q : Inside Q, ∀ g : Normalizer Q, Commute q.val g := by
    intro q g
    apply Subtype.ext
    exact NormalizerTwoElementInvolution.central_of_card_two Q hQ g ⟨q.val.val, q.property⟩
  have hI : Nat.card (Inside Q) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  have hQsq : ∀ q : Inside Q, q.val ^ 2 = 1 := by
    intro q
    have h : q ^ 2 = 1 := by rw [← hI]; exact pow_card_eq_one' (x := q)
    exact congrArg Subtype.val h
  obtain ⟨a, hane, _⟩ := (Nat.card_eq_two_iff' (1 : Inside Q)).mp hI
  let A : Subgroup G := B.map (Normalizer Q).subtype
  have hQA : Q ≤ A := by
    intro q hq
    exact ⟨⟨q, Q.le_normalizer hq⟩, hIP hq, rfl⟩
  have hAp : IsPGroup 2 A := hp.map _
  have hsingle (u : B) (p r : Fixed (X := X) Q) (hpr : p ≠ r)
      (hu : f u.val = Equiv.swap p r) :
      u.val ^ 2 = a.val ∧ Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u.val)) = 0 := by
    have huQ : u.val.val ∉ Q := by
      intro huQ
      have huf : f u.val = 1 := FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q huQ
      rw [hu] at huf
      exact hpr (Equiv.swap_eq_one_iff.mp huf)
    have hloc := ThreeSwapEvenCounts.local_five Q hseven u.val p r hpr hu
    have hr0 := hzero A hQA hAp u.val ⟨u.val, u.property, rfl⟩ huQ hloc
    exact ⟨CyclicTwoSwapSquare.square_eq_generator heven hdegree hmax Q hQ hseven
      B hk a hane u p r hpr hu hr0, hr0⟩
  have ht1 : Equiv.swap (e 2) (e 3) ∈ V := Subgroup.subset_closure (by simp)
  obtain ⟨y0, hyB, hyf⟩ := hm.ge ht1
  let y : B := ⟨y0, hyB⟩
  change f x.val = Equiv.swap (e 0) (e 1) at hxf
  change f z.val = Equiv.swap (e 4) (e 5) at hzf
  change f y.val = Equiv.swap (e 2) (e 3) at hyf
  change f v = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5) at hvf
  obtain ⟨hxsq, hxzero⟩ := hsingle x (e 0) (e 1) (e.injective.ne (by decide)) hxf
  have hysq := (hsingle y (e 2) (e 3) (e.injective.ne (by decide)) hyf).1
  have hzsq := (hsingle z (e 4) (e 5) (e.injective.ne (by decide)) hzf).1
  obtain ⟨_, _, c, _, _, hc, _⟩ := ThreeSwapNormalizerConjugators.exists_conjugators e
  obtain ⟨g, hg, hfg⟩ := hn.ge c.property
  change f g = c.val at hfg
  have himsq : (f (x.val * y.val)) ^ 2 = 1 := by
    exact congrArg Subtype.val ((ThreeSwapTwoGroup.isTwoGroup e).2
      ⟨f (x.val * y.val), hm.le ⟨x.val * y.val, B.mul_mem x.property y.property, rfl⟩⟩)
  have hconj : f (g * (x.val * y.val) * g⁻¹) = f (x.val * z.val) := by
    simpa only [map_mul, map_inv, hfg, hxf, hyf, hzf] using hc
  have hpair := CentralKernelSquareTransport.square_eq_of_image_conjugacy f B (Inside Q)
    hk (fun q t => (hcentral q t).eq) hQsq (x.val * y.val) (x.val * z.val) g
    (B.mul_mem x.property y.property) (B.mul_mem x.property z.property) hg himsq hconj
  have hcomm : Commute (f x.val) (f y.val) := by
    rw [hxf, hyf]
    exact (Equiv.Perm.disjoint_swap_swap (by
      simpa only [List.map_cons, List.map_nil] using
        (show ([0, 1, 2, 3] : List (Fin 6)).Nodup by decide).map e.injective)).commute
  have hxv : Commute x.val v := CentralTwoTripleCommutation.commute_triple_fibre
    f B (Inside Q) hk hcentral hQsq a.val x.val y.val z.val v (hQsq a)
    x.property y.property z.property hvP hxsq hysq hzsq hpair hcomm (by
      rw [map_mul, map_mul, hxf, hyf, hzf]; exact hvf)
  let I := Inside Q
  let D := NormalizerFixedComplement.Domain (X := X) Q
  let R := I ⊔ Subgroup.zpowers x.val
  have hno : ∀ t : D, x.val • t ∉ orbit I t := by
    intro t ht
    have hf : NormalizerSevenOrbitCount.orbitPerm (X := X) Q x.val (Quotient.mk'' t) =
        Quotient.mk'' t := by
      change Quotient.mk'' (x.val • t) = Quotient.mk'' t
      exact Quotient.sound ht
    have hpos : 0 < Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x.val)) :=
      Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' t, hf⟩⟩
    omega
  have hRfree := ZeroOrbitGeneratedFree.generated_free I x.val
    (by rw [hxsq]; exact a.property) (NormalizerFixedComplement.free_inside Q hfree) hno
  let L := Subgroup.zpowers x.val
  have hLfree : ∀ (l : L) (t : D), l • t = t → l = 1 := by
    intro l t ht
    have hr : (⟨l.val, (le_sup_right : L ≤ R) l.property⟩ : R) = 1 := hRfree _ t ht
    exact Subtype.ext (congrArg (fun r : R => r.val) hr)
  have horder : orderOf x.val = 4 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one, hxsq] using (fun he => hane (Subtype.ext he) : a.val ≠ 1)
    · change x.val ^ (2 * 2) = 1
      rw [pow_mul, hxsq, hQsq a]
  have hLcard : Nat.card L = 4 := (Nat.card_zpowers x.val).trans horder
  have hLv : ∀ l : L, Commute l.val v := by
    intro l
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp l.property
    rw [← hn]
    exact hxv.zpow_left n
  have hd := CentralFreeFixedDivisibility.fixed_dvd hLfree (fun t : D => v • t) (by
    intro l t
    apply Subtype.ext
    change v.val • (l.val.val • t.val) = l.val.val • (v.val • t.val)
    have hcG : l.val.val * v.val = v.val * l.val.val :=
      congrArg (fun n : Normalizer Q => n.val) (hLv l).eq
    rw [← mul_smul, ← hcG, mul_smul])
  change Nat.card L ∣ Nat.card (fixedBy D v) at hd
  rw [hLcard, NormalizerFixedComplement.fixed_card] at hd
  exact hd

theorem not_six
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
    (hlocal : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 1)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) :
    (fixedBy X v.val \ fixedPoints Q X).ncard ≠ 6 := by
  have hd := four_dvd_complement heven hdegree hmax Q hQ hseven hfree S hS himage v hv hlocal hzero
  intro he
  rw [he] at hd
  norm_num at hd

theorem false_of_local_one
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
    (hlocal : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 1)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) : False := by
  classical
  have hd := four_dvd_complement heven hdegree hmax Q hQ hseven hfree S hS himage v hv hlocal hzero
  have hsum := Set.ncard_inter_add_ncard_sdiff_eq_ncard (fixedBy X v.val) (fixedPoints Q X)
  have hmod := EvenInvolutionFixed.card_mod_four v.val hv (heven v.val)
  have hbound := hmax v.val hv
  omega

end FiveTransitive.CyclicTwoTripleExclusion

end CFSG
