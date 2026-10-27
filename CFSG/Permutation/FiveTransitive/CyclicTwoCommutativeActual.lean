module

public import CFSG.Permutation.FiveTransitive.CyclicTwoDoubleFibres
public import CFSG.Permutation.FiveTransitive.CyclicTwoSwapSquare
public import CFSG.Permutation.FiveTransitive.CyclicTwoCommutativeGroup
public import CFSG.Permutation.FiveTransitive.EqualSquareCommutation

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicTwoCommutativeActual

open MulAction FixedNormalizerAction

theorem exists_sylow
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ g : G, orderOf g = 2 → (fixedBy X g).ncard ≤ 7)
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (v : Normalizer Q) (hv : orderOf v.val = 2)
    (hlocal : (fixedBy X v.val ∩ fixedPoints Q X).ncard = 3)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ u : Normalizer Q, u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0) :
    ∃ (e : Fin 6 ↪ Fixed (X := X) Q)
      (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)))),
      let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
      let V := ThreeSwapTwoGroup.subgroup e
      let B := SylowPreimageNormalizer.ambient f V P
      f v = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∧
      IsPGroup 2 B ∧ Inside Q ≤ B ∧ v ∈ B ∧ B.map f = V ∧ B ⊓ f.ker = Inside Q ∧
      (f.comp B.subtype).ker = (Inside Q).subgroupOf B ∧
      (Subgroup.normalizer (B : Set (Normalizer Q))).map f = Subgroup.normalizer (V : Set _) ∧
      ∃ a : Inside Q, a ≠ 1 ∧ orderOf a.val = 2 ∧ Inside Q = Subgroup.zpowers a.val ∧
        (∀ (u : B) (p r : Fixed (X := X) Q), p ≠ r →
          f u.val = Equiv.swap p r → u.val ^ 2 = a.val) ∧
        (∀ u : B,
          (f u.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 2) (e 3) ∨
           f u.val = Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5) ∨
           f u.val = Equiv.swap (e 2) (e 3) * Equiv.swap (e 4) (e 5)) → u ^ 2 = 1) ∧
        ∃ x y z : B,
          f x.val = Equiv.swap (e 0) (e 1) ∧ f y.val = Equiv.swap (e 2) (e 3) ∧
          f z.val = Equiv.swap (e 4) (e 5) ∧
          Commute x.val y.val ∧ Commute x.val z.val ∧ Commute y.val z.val ∧
          B = Subgroup.closure ({a.val, x.val, y.val, z.val} : Set (Normalizer Q)) ∧
          IsMulCommutative B ∧ Nat.card B = 16 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, P, hvf, hp, hIP, hvP, hm, hk, hn, hxz, hdouble⟩ :=
    CyclicTwoDoubleFibres.exists_sylow Q hQ hseven S hS himage v hv hlocal
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let B := SylowPreimageNormalizer.ambient f V P
  change B.map f = V at hm
  change B ⊓ f.ker = Inside Q at hk
  change IsPGroup 2 B at hp
  change Inside Q ≤ B at hIP
  have hkr : (f.comp B.subtype).ker = (Inside Q).subgroupOf B := by
    ext b
    change f b.val = 1 ↔ b.val ∈ Inside Q
    constructor
    · intro hb; exact hk.le ⟨b.property, hb⟩
    · intro hb; exact (hk.ge hb).2
  have hI : Nat.card (Inside Q) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  obtain ⟨a, hane, hall⟩ := (Nat.card_eq_two_iff' (1 : Inside Q)).mp hI
  have hasq : a.val ^ 2 = 1 := by
    have h : a ^ 2 = 1 := by rw [← hI]; exact pow_card_eq_one' (x := a)
    exact congrArg Subtype.val h
  have haorder : orderOf a.val = 2 := orderOf_eq_prime hasq
    (fun h => hane (Subtype.ext h))
  have hagen : Inside Q = Subgroup.zpowers a.val := by
    apply le_antisymm _ (Subgroup.zpowers_le.mpr a.property)
    intro q hq
    by_cases he : (⟨q, hq⟩ : Inside Q) = 1
    · have he' : q = 1 := congrArg Subtype.val he
      rw [he']; exact Subgroup.one_mem _
    · have he' : q = a.val := congrArg Subtype.val (hall _ he)
      rw [he']; exact Subgroup.mem_zpowers _
  let A : Subgroup G := B.map (Normalizer Q).subtype
  have hQA : Q ≤ A := by
    intro q hq
    exact ⟨⟨q, Q.le_normalizer hq⟩, hIP hq, rfl⟩
  have hAp : IsPGroup 2 A := hp.map _
  have hsingle (u : B) (p r : Fixed (X := X) Q) (hpr : p ≠ r)
      (hu : f u.val = Equiv.swap p r) : u.val ^ 2 = a.val := by
    have huQ : u.val.val ∉ Q := by
      intro huQ
      have huf : f u.val = 1 := FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q huQ
      rw [hu] at huf
      exact hpr (Equiv.swap_eq_one_iff.mp huf)
    have hloc := ThreeSwapEvenCounts.local_five Q hseven u.val p r hpr hu
    have hr0 := hzero A hQA hAp u.val ⟨u.val, u.property, rfl⟩ huQ hloc
    exact CyclicTwoSwapSquare.square_eq_generator heven hdegree hmax Q hQ hseven
      B hk a hane u p r hpr hu hr0
  obtain ⟨x, z, hxf, hzf⟩ := hxz
  have ht1 : Equiv.swap (e 2) (e 3) ∈ V := Subgroup.subset_closure (by simp)
  obtain ⟨y0, hyB, hyf⟩ := hm.ge ht1
  let y : B := ⟨y0, hyB⟩
  change f x.val = Equiv.swap (e 0) (e 1) at hxf
  change f z.val = Equiv.swap (e 4) (e 5) at hzf
  change f y.val = Equiv.swap (e 2) (e 3) at hyf
  have hxsq := hsingle x (e 0) (e 1) (e.injective.ne (by decide)) hxf
  have hysq := hsingle y (e 2) (e 3) (e.injective.ne (by decide)) hyf
  have hzsq := hsingle z (e 4) (e 5) (e.injective.ne (by decide)) hzf
  have hxy2 : (x.val * y.val) ^ 2 = 1 :=
    congrArg Subtype.val (hdouble (x * y) (Or.inl (by
      change f (x.val * y.val) = _
      rw [map_mul, hxf, hyf])))
  have hxz2 : (x.val * z.val) ^ 2 = 1 :=
    congrArg Subtype.val (hdouble (x * z) (Or.inr (Or.inl (by
      change f (x.val * z.val) = _
      rw [map_mul, hxf, hzf]))))
  have hyz2 : (y.val * z.val) ^ 2 = 1 :=
    congrArg Subtype.val (hdouble (y * z) (Or.inr (Or.inr (by
      change f (y.val * z.val) = _
      rw [map_mul, hyf, hzf]))))
  have hxy := EqualSquareCommutation.commute_of_equal_squares a.val x.val y.val hasq hxsq hysq hxy2
  have hxz := EqualSquareCommutation.commute_of_equal_squares a.val x.val z.val hasq hxsq hzsq hxz2
  have hyz := EqualSquareCommutation.commute_of_equal_squares a.val y.val z.val hasq hysq hzsq hyz2
  have hgenim : B.map f = Subgroup.closure (f '' ({x.val, y.val, z.val} : Set (Normalizer Q))) := by
    rw [hm]
    simp only [Set.image_insert_eq, Set.image_singleton, hxf, hyf, hzf]
    rfl
  obtain ⟨hgen, hcomm⟩ := CyclicTwoCommutativeGroup.generated_commutative Q hQ f B hk
    a.val a.property hagen x.val y.val z.val x.property y.property z.property hxy hxz hyz hgenim
  have hcard := CyclicTwoCommutativeGroup.card_sixteen f B (Inside Q) hI hk e hm
  exact ⟨e, P, hvf, hp, hIP, hvP, hm, hk, hkr, hn, a, hane, haorder, hagen,
    hsingle, hdouble, x, y, z, hxf, hyf, hzf, hxy, hxz, hyz, hgen, hcomm, hcard⟩

end FiveTransitive.CyclicTwoCommutativeActual

end CFSG
