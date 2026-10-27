module

public import CFSG.Permutation.FiveTransitive.CyclicTwoTripleExclusion

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.NormalizerInvolutionEven

open MulAction FixedNormalizerAction

private theorem local_cases {F : Type*} [Fintype F] [DecidableEq F]
    (hseven : Nat.card F = 7) (u : Equiv.Perm F) (hu : u ^ 2 = 1) :
    Equiv.Perm.sign u = 1 ∨ Nat.card (Function.fixedPoints u) = 5 ∨
      Nat.card (Function.fixedPoints u) = 1 := by
  have htype := Equiv.Perm.cycleType_of_pow_prime_eq_one hu
  have hcount := u.card_fixedPoints
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hseven, htype,
    Multiset.sum_replicate, nsmul_eq_mul] at hcount
  have hbound := u.sum_cycleType_le
  rw [htype, Multiset.sum_replicate, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hseven] at hbound
  simp only [Nat.cast_id] at hcount hbound
  have hcases : u.cycleType.card = 0 ∨ u.cycleType.card = 1 ∨
      u.cycleType.card = 2 ∨ u.cycleType.card = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · left; rw [Equiv.Perm.sign_of_cycleType, htype, h0]; norm_num
  · exact Or.inr (Or.inl (by omega))
  · left; rw [Equiv.Perm.sign_of_cycleType, htype, h2]; norm_num; decide
  · exact Or.inr (Or.inr (by omega))

theorem sign_eq_one
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)]
    (hQ : Nat.card Q = 2) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0)
    (v : Normalizer Q) (hv2 : v ^ 2 = 1) :
    Equiv.Perm.sign (toPermHom (Normalizer Q) (Fixed (X := X) Q) v) = 1 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hv : v = 1
  · rw [hv, map_one, map_one]
  have hvorder : orderOf v.val = 2 := orderOf_eq_prime
    (congrArg (fun n : Normalizer Q => n.val) hv2) (fun he => hv (Subtype.ext he))
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hfv2 : (f v) ^ 2 = 1 := by rw [← map_pow, hv2, map_one]
  rcases local_cases hseven (f v) hfv2 with he | hlocal | hlocal
  · exact he
  · obtain ⟨⟨p, r, hpr, hvf⟩, _⟩ := SevenFivePermutationSquare.isSwap_and_square hseven (f v) hlocal
    have hvQ : v.val ∉ Q := by
      intro h
      have he : f v = 1 := FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q h
      rw [hvf] at he
      exact hpr (Equiv.swap_eq_one_iff.mp he)
    have hQp : IsPGroup 2 Q := by rw [← hS]; exact S.isPGroup'.map _
    have hvN : orderOf v = 2 := (Subgroup.orderOf_coe v).symm.trans hvorder
    have hvp : IsPGroup 2 (Subgroup.zpowers v) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hvN, pow_one])
    let R := Inside Q ⊔ Subgroup.zpowers v
    have hIp : IsPGroup 2 (Inside Q) := hQp.comap_subtype
    have hRp : IsPGroup 2 R := hIp.to_sup_of_normal_left hvp
    let A := R.map (Normalizer Q).subtype
    have hQA : Q ≤ A := by
      intro q hq
      exact ⟨⟨q, Q.le_normalizer hq⟩, (le_sup_left : Inside Q ≤ R) hq, rfl⟩
    have hvA : v.val ∈ A :=
      ⟨v, (le_sup_right : Subgroup.zpowers v ≤ R) (Subgroup.mem_zpowers v), rfl⟩
    have hloc : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 5 :=
      (FixedNormalizerLocalCard.fixed_card Q v).symm.trans hlocal
    have hr0 := hzero A hQA (hRp.map _) v hvA hvQ hloc
    exact False.elim (CyclicTwoSwapSquare.square_ne_one heven hdegree hmax Q hseven
      v p r hpr hvf hr0 hv2)
  · have hloc : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 1 :=
      (FixedNormalizerLocalCard.fixed_card Q v).symm.trans hlocal
    exact False.elim (CyclicTwoTripleExclusion.false_of_local_one heven hdegree hmax
      Q hQ hseven hfree S hS himage v hvorder hloc hzero)

end FiveTransitive.NormalizerInvolutionEven

end CFSG
