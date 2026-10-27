module

public import CFSG.Permutation.FiveTransitive.CyclicTwoFullSylowCentralizer
public import CFSG.Permutation.FiveTransitive.ThreeSwapNormalizerFixedPair
public import CFSG.Permutation.FiveTransitive.FixedNormalizerFullSylow
public import CFSG.Permutation.FiveTransitive.IndexTwoSemiregularExtension

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoFullSylowSemiregular

open MulAction FixedNormalizerAction

theorem semiregular
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)] (hQ : Nat.card Q = 2)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (A B : Subgroup (Normalizer Q)) (hBA : B ≤ A)
    (hAcard : Nat.card A = 32) (hBcard : Nat.card B = 16) (hcomm : IsMulCommutative B)
    (hkA : A ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (hkB : B ⊓ (toPermHom (Normalizer Q) (Fixed (X := X) Q)).ker = Inside Q)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (hm : B.map (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ThreeSwapTwoGroup.subgroup e)
    (a : Inside Q) (ha : a ≠ 1)
    (heven : ∀ u : Normalizer Q, u ^ 2 = 1 →
      Equiv.Perm.sign (toPermHom (Normalizer Q) (Fixed (X := X) Q) u) = 1)
    (hsingle : ∀ (u : B) (p r : Fixed (X := X) Q), p ≠ r →
      toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val = Equiv.swap p r → u.val ^ 2 = a.val)
    (hdouble : ∀ u : B,
      (toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∨
       toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5) ∨
       toPermHom (Normalizer Q) (Fixed (X := X) Q) u.val = Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5)) → u ^ 2 = 1)
    (x₀ : B) (hx₀ : orderOf x₀ = 4) (hx₀2 : x₀.val ^ 2 = a.val)
    (hxfree : ∀ (q : Subgroup.zpowers x₀) (t : NormalizerFixedComplement.Domain (X := X) Q),
      q • t = t → q = 1)
    (v : B) (hv : v ≠ 1)
    (hfour : (fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v).ncard = 4)
    (hfreeB : ∀ (b : B) (t : NormalizerFixedComplement.Domain (X := X) Q),
      t ∉ fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v → b • t = t → b = 1) :
    ∀ (u : A) (t : NormalizerFixedComplement.Domain (X := X) Q),
      t ∉ fixedBy (NormalizerFixedComplement.Domain (X := X) Q) v → u • t = t → u = 1 := by
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let D := NormalizerFixedComplement.Domain (X := X) Q
  change B.map f = V at hm
  obtain ⟨_,hn,hsq⟩ := FixedNormalizerFullSylow.index_two A B hBA hAcard hBcard
  have hN : A ≤ Subgroup.normalizer (B : Set (Normalizer Q)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBA).mp hn
  apply IndexTwoSemiregularExtension.semiregular_subgroup A B (fixedBy D v) 7
    (fun u => hsq u) hfreeB
  · intro u hu
    have humax := hmax u.val ((Subgroup.orderOf_coe u).trans hu)
    rw [← Nat.card_coe_set_eq, NormalizerFixedComplement.fixed_card]
    exact (Set.ncard_le_ncard Set.sdiff_subset).trans humax
  · intro s _ hs
    have hsN : s.val ∈ Subgroup.normalizer (B : Set (Normalizer Q)) := hN s.property
    have hfsN : f s.val ∈ Subgroup.normalizer (V : Set _) := by
      rw [← hm]
      exact Subgroup.le_normalizer_map f ⟨s.val,hsN,rfl⟩
    have hfs2 : (f s.val) ^ 2 = 1 := by rw [← map_pow,hs,map_one]
    have hpair (i j k l m n : Fin 6) (hnod : [i,j,k,l,m,n].Nodup)
        (hdcase : Equiv.swap (e k) (e l) * Equiv.swap (e m) (e n) =
            Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∨
          Equiv.swap (e k) (e l) * Equiv.swap (e m) (e n) =
            Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5) ∨
          Equiv.swap (e k) (e l) * Equiv.swap (e m) (e n) =
            Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5))
        (hi : Equiv.swap (e i) (e j) ∈ V)
        (hc : Commute (f s.val) (Equiv.swap (e i) (e j)))
        (hd : Commute (f s.val) (Equiv.swap (e k) (e l) * Equiv.swap (e m) (e n))) :
        7 < Nat.card ((Subgroup.centralizer ({s.val} : Set (Normalizer Q))).subgroupOf B) := by
      have hdV : Equiv.swap (e k) (e l) * Equiv.swap (e m) (e n) ∈ V := by
        rcases hdcase with h|h|h <;> rw [h] <;> apply V.mul_mem <;>
          apply Subgroup.subset_closure <;> simp
      obtain ⟨x,hxB,hxf⟩ := hm.ge hi
      obtain ⟨w,hwB,hwf⟩ := hm.ge hdV
      have hij : e i ≠ e j := e.injective.ne (by
        have hh := hnod
        simp only [List.nodup_cons,List.mem_cons,not_or] at hh
        tauto)
      have hne : Equiv.swap (e k) (e l) * Equiv.swap (e m) (e n) ≠ (1 : Equiv.Perm (Fixed (X := X) Q)) := by
        intro h
        have hh := congrArg (fun p : Equiv.Perm (Fixed (X := X) Q) => p (e k)) h
        simp only [List.nodup_cons, List.mem_cons, not_or] at hnod
        simp [Equiv.Perm.mul_apply,Equiv.swap_apply_def,e.injective.eq_iff] at hh
        aesop
      have hbound := CyclicTwoFullSylowCentralizer.eight_le_card Q hQ hfree A B hBA hcomm
        hkA hkB a ha heven x₀ hx₀ hx₀2 hxfree v hv hfour hfreeB s hs hsN
        ⟨x,hxB⟩ ⟨w,hwB⟩ (hsingle ⟨x,hxB⟩ _ _ hij hxf)
        (hdouble ⟨w,hwB⟩ (by
          change f w = _ ∨ f w = _ ∨ f w = _
          rwa [hwf]))
        (by rw [hxf,Equiv.Perm.sign_swap hij]) (by rwa [hwf])
        (by rwa [hxf]) (by rwa [hwf])
      omega
    rcases ThreeSwapNormalizerFixedPair.fixed_pair e (f s.val) hfsN hfs2 with h|h|h
    · exact hpair 0 1 2 3 4 5 (by decide) (Or.inr (Or.inr rfl))
        (Subgroup.subset_closure (by simp)) h.1 h.2
    · exact hpair 2 3 0 1 4 5 (by decide) (Or.inr (Or.inl rfl))
        (Subgroup.subset_closure (by simp)) h.1 h.2
    · exact hpair 4 5 0 1 2 3 (by decide) (Or.inl rfl)
        (Subgroup.subset_closure (by simp)) h.1 h.2

end FiveTransitive.CyclicTwoFullSylowSemiregular

end CFSG
