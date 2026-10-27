module

public import CFSG.Permutation.FiveTransitive.CentralOddKernelTwoLifts
public import CFSG.Permutation.FiveTransitive.EvenSixSylowDihedral

public section

namespace CFSG

namespace FiveTransitive.CentralExtensionUniqueSquare

theorem mem_of_two_element_mem_kernel
    {G A : Type*} [Group G] [Finite G] [Group A]
    (f : G →* A) (Q : Subgroup G) [Q.Normal]
    (hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' Q))))
    (x : G) (k : ℕ) (hx : x ^ (2 ^ k) = 1) (hfx : f x = 1) : x ∈ Q := by
  let pi : G →* G ⧸ Q := QuotientGroup.mk' Q
  let R := f.ker.map pi
  let y : R := ⟨pi x, Subgroup.mem_map.mpr ⟨x, hfx, rfl⟩⟩
  have hy : y ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    change (pi x) ^ (2 ^ k) = 1
    rw [← map_pow, hx, map_one]
  have hcop : (Nat.card R).Coprime (2 ^ k) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat).symm).pow_right k
  have hord : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_natCard y) (orderOf_dvd_of_pow_eq_one hy)
  exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val (orderOf_eq_one_iff.mp hord))

private theorem square_eq_of_mod_central
    {G : Type*} [Group G] (Q : Subgroup G)
    (hcentral : ∀ q : Q, ∀ g : G, (q : G) * g = g * q)
    (hQsq : ∀ q : Q, q ^ 2 = 1)
    (x a : G) (h : x * a⁻¹ ∈ Q) : x ^ 2 = a ^ 2 := by
  let q : Q := ⟨x * a⁻¹, h⟩
  have he : x = (q : G) * a := by dsimp [q]; group
  have hc : Commute (q : G) a := hcentral q a
  have hq : (q : G) ^ 2 = 1 := congrArg Subtype.val (hQsq q)
  rw [he, hc.mul_pow, hq, one_mul]

theorem exists_sylow_unique_square
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X]
    (f : G →* Equiv.Perm X) (hX : Fintype.card X = 6)
    (hf : f.range = alternatingGroup X)
    (Q : Subgroup G) [Q.Normal] (hQ : Q ≤ f.ker) (hcard : Nat.card Q = 2)
    (hodd : Odd (Nat.card (f.ker.map (QuotientGroup.mk' Q))))
    (hcentral : ∀ q : Q, ∀ g : G, (q : G) * g = g * q)
    (a : G) (ha : orderOf a = 4) (hfa : orderOf (f a) = 4) :
    ∃ P : Sylow 2 G, a ∈ P ∧ Q ≤ (P : Subgroup G) ∧
      ∀ x : P, (x : G) ^ 2 = 1 ∨ (x : G) ^ 2 = a ^ 2 := by
  classical
  have hQsq : ∀ q : Q, q ^ 2 = 1 := by
    intro q
    rw [← hcard]
    exact pow_card_eq_one' (x := q)
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hap : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ha]; norm_num)
  obtain ⟨P, hP⟩ := hap.exists_le_sylow
  have haP : a ∈ P := hP (Subgroup.mem_zpowers a)
  refine ⟨P, haP, hQp.le_sylow_of_normal P, ?_⟩
  let aP : P := ⟨a, haP⟩
  let fA : G →* alternatingGroup X := f.codRestrict _ (by
    intro g
    rw [← hf]
    exact ⟨g, rfl⟩)
  have hfA : Function.Surjective fA := by
    intro y
    have hm : y.val ∈ f.range := by rw [hf]; exact y.property
    obtain ⟨g, hg⟩ := hm
    exact ⟨g, Subtype.ext hg⟩
  let D : Sylow 2 (alternatingGroup X) := Sylow.mapSurjective hfA P
  have him (x : P) : fA x ∈ D := by
    change fA x ∈ (D : Subgroup (alternatingGroup X))
    rw [show (D : Subgroup (alternatingGroup X)) = (P : Subgroup G).map fA from
      Sylow.coe_mapSurjective hfA P]
    exact Subgroup.mem_map_of_mem fA x.property
  let phi : P →* D :=
    { toFun := fun x => ⟨fA x, him x⟩
      map_one' := Subtype.ext (map_one fA)
      map_mul' := fun x y => Subtype.ext (map_mul fA (x : G) (y : G)) }
  have hphi : orderOf (phi aP) = 4 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hfa
  have hkernel (x : P) (hx : f x = 1) : (x : G) ∈ Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' x
    apply mem_of_two_element_mem_kernel f Q hodd x k _ hx
    have hp : x ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
    exact congrArg Subtype.val hp
  have hsquare (x y : P) (he : f x = f y) : (x : G) ^ 2 = (y : G) ^ 2 := by
    apply square_eq_of_mod_central Q hcentral hQsq
    apply hkernel (x * y⁻¹)
    change f ((x : G) * (y : G)⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  have ha4 : a ^ 4 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hz : (a ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact ha4
  have hfz : f (a ^ 2) ≠ 1 := by
    rw [map_pow]
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hfa] at hd
    norm_num at hd
  intro x
  rcases EvenSixSylowDihedral.square_eq_one_or_eq_or_eq_inv X hX D
      (phi aP) (phi x) hphi with hx | hx | hx
  · left
    have hfx : (f x) ^ 2 = 1 := congrArg (fun t : D => ((t : alternatingGroup X) : Equiv.Perm X)) hx
    by_cases hne : f x = 1
    · exact congrArg Subtype.val (hQsq ⟨x.val, hkernel x hne⟩)
    · obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' x
      have hp : (x : G) ^ (2 ^ k) = 1 := by
        have hp' : x ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
        exact congrArg Subtype.val hp'
      exact CentralOddKernelTwoLifts.square_eq_one_of_even_six_image f hX hf Q hQ hodd
        hcentral hQsq (a ^ 2) hz hfz x k hp hfx hne
  · right
    exact hsquare x aP (congrArg (fun t : D => ((t : alternatingGroup X) : Equiv.Perm X)) hx)
  · right
    have he : f x = f ((aP⁻¹ : P) : G) := by
      have hh := congrArg (fun t : D => ((t : alternatingGroup X) : Equiv.Perm X)) hx
      change f x = (f a)⁻¹ at hh
      change f x = f (a⁻¹)
      rw [map_inv]
      exact hh
    rw [hsquare x aP⁻¹ he]
    change (a⁻¹) ^ 2 = a ^ 2
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hz)

end FiveTransitive.CentralExtensionUniqueSquare

end CFSG
