module

public import CFSG.Permutation.FiveTransitive.FixedNormalizerDoubleSwapSylow
public import CFSG.Permutation.FiveTransitive.NormalizerZeroOrbitGeometry
public import CFSG.Permutation.FiveTransitive.CyclicNormalizerCommutatorPair
public import CFSG.Permutation.FiveTransitive.CyclicFourCommutingDouble

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.CyclicFourZeroOrbitExclusion

open MulAction FixedNormalizerAction

theorem false_of_double_seed
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q : Subgroup G) (hcyclic : IsCyclic Q) (hQ : Nat.card Q = 4)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (hdiv : 8 ∣ Nat.card X - 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (hcentral : ∀ n : Normalizer Q, ∀ q : Q, Commute n.val q.val)
    (hzero : ∀ (A : Subgroup G), Q ≤ A → IsPGroup 2 A →
      ∀ (u : Normalizer Q), u.val ∈ A → u.val ∉ Q →
      (fixedBy X u.val ∩ fixedPoints Q X).ncard = 5 →
      Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) = 0)
    (b : Q) (hb : orderOf b = 4) (y : Normalizer Q) (hy : orderOf y.val = 2)
    (hlocal : (fixedBy X y.val ∩ fixedPoints Q X).ncard = 3)
    (hypos : ∃ t : X, t ∉ fixedPoints Q X ∧ y.val • t = t) : False := by
  classical
  let _ := Fintype.ofFinite (Fixed (X := X) Q)
  have hseven' : Nat.card (Fixed (X := X) Q) = 7 := by simpa only [fixed_eq Q] using hseven
  obtain ⟨e, P, hyf, hB, hIB, hyB, hmap, hker, _, x, z, hxf, hzf⟩ :=
    FixedNormalizerDoubleSwapSylow.exists_sylow Q hseven' S hS himage y hy hlocal
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  let V := ThreeSwapTwoGroup.subgroup e
  let B := SylowPreimageNormalizer.ambient f V P
  let A := B.map (Normalizer Q).subtype
  have hQA : Q ≤ A := by
    intro q hq
    exact ⟨⟨q, Q.le_normalizer hq⟩, hIB hq, rfl⟩
  have hzeroSwap (s : B) (hs : (f s.val).IsSwap) :
      Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q s.val)) = 0 := by
    apply hzero A hQA (hB.map _) s.val ⟨s.val, s.property, rfl⟩
      (FixedNormalizerLocalCard.not_mem_of_local_order_two Q s.val hs.orderOf)
    rw [← FixedNormalizerLocalCard.fixed_card Q s.val, Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints, Equiv.Perm.isSwap_iff_cycleType.mp hs,
      ← Nat.card_eq_fintype_card, hseven']
    rfl
  obtain ⟨_, _, _, _, _, t, _, hyt, _, hO, _⟩ :=
    CyclicFourDoubleSwapGeometry.exists_two_orbits hmax Q hQ hseven hfree hdiv b hb y hy
      (fun q => (hcentral y q).symm) hlocal hypos
  have hxy : ¬ Commute x.val.val y.val := NormalizerZeroOrbitGeometry.not_commute Q x.val y
    (hzeroSwap x ⟨e 0, e 1, e.injective.ne (by decide), hxf⟩) t hO
  have hzy : ¬ Commute z.val.val y.val := NormalizerZeroOrbitGeometry.not_commute Q z.val y
    (hzeroSwap z ⟨e 4, e 5, e.injective.ne (by decide), hzf⟩) t hO
  have hVcomm : IsMulCommutative (B.map f) := by
    rw [hmap]
    apply isMulCommutative_iff.mpr
    have hinv (u : V) : u⁻¹ = u := by
      apply inv_eq_of_mul_eq_one_right
      simpa only [pow_two] using (ThreeSwapTwoGroup.isTwoGroup e).2 u
    intro u v
    calc
      u * v = (u * v)⁻¹ := (hinv _).symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev _ _
      _ = v * u := by rw [hinv, hinv]
  obtain ⟨_, _, _, _, hpair⟩ := CyclicNormalizerCommutatorPair.exists_pair_eq_and_commute
    Q hcyclic B hker hVcomm (fun u q => hcentral u.val q)
      x z ⟨y, hyB⟩ (hy ▸ pow_orderOf_eq_one y.val) hxy hzy
  let v : Normalizer Q := x.val * z.val
  obtain ⟨q, hwt⟩ := NormalizerZeroOrbitGeometry.exists_fixed_representative Q v y hpair t hO
  let w : Normalizer Q := q.val * v
  have hwB : w ∈ B := B.mul_mem (hIB q.property) (B.mul_mem x.property z.property)
  have hfw : f w = Equiv.swap (e 0) (e 1) * Equiv.swap (e 4) (e 5) := by
    change f (q.val * (x.val * z.val)) = _
    rw [map_mul, map_mul, hxf, hzf,
      show f q.val = 1 from FixedNormalizerCyclicPreimageSylow.inside_le_kernel Q q.property,
      one_mul]
  have hw2Q : w.val ^ 2 ∈ Q := by
    have hwmap : f w ∈ V := hmap.le ⟨w, hwB, rfl⟩
    have hsq : (f w) ^ 2 = 1 := congrArg Subtype.val ((ThreeSwapTwoGroup.isTwoGroup e).2 ⟨f w, hwmap⟩)
    have hkerw : w ^ 2 ∈ (B ⊓ f.ker) := ⟨B.pow_mem hwB 2, by
      change f (w ^ 2) = 1
      rw [map_pow]; exact hsq⟩
    exact hker.le hkerw
  have hw2 : w.val ^ 2 = 1 := by
    have hfix : (⟨w.val ^ 2, hw2Q⟩ : Q) • t.val = t.val := by
      change (w.val ^ 2) • t.val = t.val
      simp only [pow_two, mul_smul, show w.val • t.val = t.val from congrArg Subtype.val hwt]
    exact congrArg Subtype.val (hfree ⟨w.val ^ 2, hw2Q⟩ t.val t.property hfix)
  have hneq : y.val ≠ w.val := by
    intro h
    have hn : y = w := Subtype.ext h
    have he := congrArg (fun n => f n (e 2)) hn
    rw [hyf, hfw] at he
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at he
    have h30 : e 3 ≠ e 0 := e.injective.ne (by decide)
    have h31 : e 3 ≠ e 1 := e.injective.ne (by decide)
    have h24 : e 2 ≠ e 4 := e.injective.ne (by decide)
    have h25 : e 2 ≠ e 5 := e.injective.ne (by decide)
    have h20 : e 2 ≠ e 0 := e.injective.ne (by decide)
    have h21 : e 2 ≠ e 1 := e.injective.ne (by decide)
    rw [Equiv.swap_apply_of_ne_of_ne h30 h31, Equiv.swap_apply_of_ne_of_ne h24 h25,
      Equiv.swap_apply_of_ne_of_ne h20 h21] at he
    exact (e.injective.ne (by decide : (3 : Fin 6) ≠ 2)) he
  have hwne : w.val ≠ 1 := by
    intro hw
    have hf1 : f w = 1 := by rw [show w = 1 from Subtype.ext hw, map_one]
    have he := congrArg (fun σ => σ (e 0)) (hfw.symm.trans hf1)
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at he
    rw [Equiv.swap_apply_of_ne_of_ne (e.injective.ne (by decide))
      (e.injective.ne (by decide)), Equiv.swap_apply_left] at he
    exact (e.injective.ne (by decide : (1 : Fin 6) ≠ 0)) he
  have hwy : Commute w.val y.val :=
    (hcentral y ⟨q.val.val, q.property⟩).symm.mul_left hpair
  exact CyclicFourCommutingDouble.contradiction hmax Q hQ hseven hfree hdiv b hb y w hy
    (orderOf_eq_prime hw2 hwne) (fun q => (hcentral y q).symm)
    (fun q => (hcentral w q).symm) hwy.symm hneq hlocal t.val t.property hyt
    (congrArg Subtype.val hwt)

end FiveTransitive.CyclicFourZeroOrbitExclusion

end CFSG
