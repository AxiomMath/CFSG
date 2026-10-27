module

public import CFSG.Permutation.FiveTransitive.HighDegreeRegularFourSeed
public import CFSG.Permutation.FiveTransitive.SetwiseTripleThreeSwapTransport
public import CFSG.Permutation.FiveTransitive.PairFixedExceptionTransport

public section

namespace CFSG

open scoped Pointwise

namespace FiveTransitive.HighDegreePairExceptionContradiction

open MulAction FixedNormalizerAction Research.HallRegularOrbits

theorem contradiction
    {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7)
    (Q : Subgroup G) [Fintype (Fixed (X := X) Q)] [DecidableEq (Fixed (X := X) Q)]
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (hfree : ∀ (q : Q) (y : X), y ∉ fixedPoints Q X → q • y = y → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (e : Fin 6 ↪ Fixed (X := X) Q)
    (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
      (toPermHom (Normalizer Q) (Fixed (X := X) Q))))
    (a : Q) (ha : orderOf a.val = 2) (x : Normalizer Q)
    (hx : orderOf x.val = 2) (hxQ : x.val ∉ Q) (hax : Commute a.val x.val)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (O : Set X)
    (hO : ∀ y ∈ O, y ∉ fixedPoints Q X ∧
      (x.val • y = y ∨ (a.val * x.val) • y = y))
    (hsemifree : ∀ b : SylowPreimageNormalizer.ambient
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P,
      ∀ y : X, y ∉ fixedPoints Q X → y ∉ O → b.val.val • y = y → b = 1) : False := by
  classical
  have hne : a.val ≠ x.val := fun he => hxQ (he ▸ a.property)
  obtain ⟨z, u, _, hzout, _, _, huorder, huz, hua, hux⟩ :=
    HighDegreeRegularFourSeed.exists_fixing_regular_four hcard h5 hmax a.val x.val ha hx hax hne
  have hzS : z ∈ regularFourSet a.val x.val z := by simp only [regularFourSet, Set.mem_insert_iff, true_or]
  have hfixa : fixedPoints Q X = fixedBy X a.val := by
    ext y
    constructor
    · intro hy
      exact hy a
    · intro hy
      by_contra hout
      have he : a.val = 1 := congrArg Subtype.val (hfree a y hout hy)
      rw [he, orderOf_one] at ha
      omega
  have ha2 : a.val ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a.val
  have hx2 : x.val ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x.val
  have hu2 : u ^ 2 = 1 := by simpa only [huorder] using pow_orderOf_eq_one u
  let H := Subgroup.closure ({a.val, x.val, u} : Set G)
  have hHp : IsPGroup 2 H := by
    apply (ThreeSwapTwoGroup.closure_two_group _ ?_ ?_).1
    · intro b hb c hc hbc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
      rcases hb with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
      all_goals first | exact Commute.refl _ | exact hax | exact hax.symm | exact hua | exact hua.symm | exact hux | exact hux.symm
    · intro b hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl | rfl <;> assumption
  have hC : H ≤ Subgroup.centralizer ({a.val} : Set G) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change g ∈ Subgroup.centralizer ({a.val} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg
    · rw [hg]
    · rw [hg]; exact hax.symm.eq
    · rw [hg]; exact hua.eq
  have hpreserves : ∀ h : H, ∀ y : X,
      y ∈ fixedPoints Q X ↔ h.val • y ∈ fixedPoints Q X := by
    intro h y
    rw [hfixa]
    have hc : Commute h.val a.val := Subgroup.mem_centralizer_singleton_iff.mp (hC h.property)
    have hs : h.val • fixedBy X a.val = fixedBy X a.val := by
      simpa only [zpow_one] using (smul_zpow_fixedBy_eq_of_commute (α := X) hc.symm (1 : ℤ))
    exact (smul_mem_of_set_mem_fixedBy (show fixedBy X a.val ∈ fixedBy (Set X) h.val from hs)).symm
  obtain ⟨c, hcF, hc⟩ := SetwiseTripleThreeSwapTransport.exists_conjugate
    Q hseven S hS himage e P H hHp hpreserves a.val x.val u
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) ha2 hx2 hu2 hax hua.symm hux.symm
    (fun y hy => hy a) hlocal
  let B := SylowPreimageNormalizer.ambient
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P
  let C := B.map (Normalizer Q).subtype
  have hsemiC : ∀ b : C, ∀ y : X,
      y ∉ fixedPoints Q X → y ∉ O → b.val • y = y → b = 1 := by
    intro b y hyF hyO hb
    obtain ⟨v, hv, he⟩ := b.property
    change v.val = b.val at he
    have hvfix : v.val • y = y := by rw [he]; exact hb
    have hvone := hsemifree ⟨v, hv⟩ y hyF hyO hvfix
    apply Subtype.ext
    exact he.symm.trans (congrArg (fun b : B => b.val.val) hvone)
  have hxne : x.val ≠ 1 := by intro he; rw [he, orderOf_one] at hx; omega
  have haxne : a.val * x.val ≠ 1 := by
    intro he
    have hxa : x.val = a.val⁻¹ := by
      calc
        x.val = a.val⁻¹ * (a.val * x.val) := by group
        _ = a.val⁻¹ := by rw [he, mul_one]
    exact hxQ (hxa ▸ Q.inv_mem a.property)
  have hune : u ≠ 1 := by intro he; rw [he, orderOf_one] at huorder; omega
  have hzF : z ∉ fixedPoints Q X := by
    intro hz
    exact hzout hzS (Or.inl (Or.inl (hz a)))
  have hzO : z ∉ O := by
    intro hz
    rcases (hO z hz).2 with h | h
    · exact hzout hzS (Or.inl (Or.inr h))
    · exact hzout hzS (Or.inr h)
  exact PairFixedExceptionTransport.contradiction C (fixedPoints Q X) O a.val x.val u c z
    hsemiC hO hxne haxne hune hzF hzO (huz z hzS) hcF
    (hc a.val (by simp)) (hc x.val (by simp)) (hc u (by simp))

end FiveTransitive.HighDegreePairExceptionContradiction

end CFSG
