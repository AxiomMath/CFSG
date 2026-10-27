module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.Classical

variable {G Q : Type*} [Group G] [Group Q] {p : ℕ}

theorem eq_of_map_eq_of_pow_eq_one_of_coprime [Finite G] (π : G →* Q)
    (hc : π.ker ≤ Subgroup.center G) (hcop : Nat.Coprime (Nat.card π.ker) p) {x y : G}
    {a b : ℕ} (hx : x ^ p ^ a = 1) (hy : y ^ p ^ b = 1) (hxy : π x = π y) : x = y := by
  set z := x⁻¹ * y with hz
  have hzK : z ∈ π.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hxy, inv_mul_cancel]
  have hzc : z ∈ Subgroup.center G := hc hzK
  have hyz : y = x * z := by rw [hz, mul_inv_cancel_left]
  have hzN : z ^ p ^ (a + b) = 1 := by
    have h1 : y ^ p ^ (a + b) = 1 := by rw [pow_add, mul_comm, pow_mul, hy, one_pow]
    have h2 : x ^ p ^ (a + b) = 1 := by rw [pow_add, pow_mul, hx, one_pow]
    rw [hyz, Commute.mul_pow (Subgroup.mem_center_iff.mp hzc x), h2, one_mul] at h1
    exact h1
  have hzcard : z ^ Nat.card π.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hzK⟩ : π.ker)))
  have hz1 : z = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hzcard, hzN⟩
    rwa [(hcop.pow_right (a + b)).gcd_eq_one, pow_one] at this
  rw [hyz, hz1, mul_one]

theorem natCard_comap_eq_mul [Finite G] (π : G →* Q) (hπ : Function.Surjective π)
    (A : Subgroup Q) : Nat.card (A.comap π) = Nat.card π.ker * Nat.card A := by
  let φ : A.comap π →* A := (π.comp (A.comap π).subtype).codRestrict A fun x => x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    obtain ⟨g, rfl⟩ := hπ a
    exact ⟨⟨g, ha⟩, rfl⟩
  have hker : φ.ker = π.ker.subgroupOf (A.comap π) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hle : π.ker ≤ A.comap π := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact A.one_mem
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, mul_comm]

theorem exists_sylow_lift_of_ker_le_center [Finite G] (hp : p.Prime) (π : G →* Q)
    (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center G)
    (hcop : Nat.Coprime (Nat.card π.ker) p) (A : Subgroup Q) (hA : IsPGroup p A) :
    ∃ Ã : Subgroup G, Ã ≤ A.comap π ∧
      (∀ P : Sylow p (A.comap π), (P : Subgroup (A.comap π)).map (A.comap π).subtype = Ã) ∧
      ∃ e : Ã ≃* A, ∀ x : Ã, (e x : Q) = π x := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite Q := Finite.of_surjective π hπ
  set M := A.comap π with hMdef
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hA
  have hcard : ∀ P : Sylow p M, Nat.card ((P : Subgroup M).map M.subtype) = Nat.card A := by
    intro P
    rw [Subgroup.card_map_of_injective M.subtype_injective, Sylow.card_eq_multiplicity,
      natCard_comap_eq_mul π hπ A, hk, Nat.factorization_mul (Nat.card_pos.ne')
        (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply, hp.factorization_pow,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd, zero_add]
    exact fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop.symm h)
  have hpow : ∀ P : Sylow p M, ∀ x ∈ (P : Subgroup M).map M.subtype, ∃ a : ℕ, x ^ p ^ a = 1 := by
    intro P x hx
    obtain ⟨a, ha⟩ := (P.isPGroup'.map M.subtype) ⟨x, hx⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  have hinj : ∀ P : Sylow p M, ∀ x ∈ (P : Subgroup M).map M.subtype,
      ∀ y ∈ (P : Subgroup M).map M.subtype, π x = π y → x = y := by
    intro P x hx y hy hxy
    obtain ⟨a, ha⟩ := hpow P x hx
    obtain ⟨b, hb⟩ := hpow P y hy
    exact eq_of_map_eq_of_pow_eq_one_of_coprime π hc hcop ha hb hxy
  have hle : ∀ P : Sylow p M, (P : Subgroup M).map M.subtype ≤ M := by
    rintro P _ ⟨x, -, rfl⟩
    exact x.2
  have himage : ∀ P : Sylow p M, ((P : Subgroup M).map M.subtype).map π = A := by
    intro P
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hle P hx
    · rw [← hcard P]
      refine le_of_eq (Nat.card_congr (Equiv.ofBijective
        (fun x : (P : Subgroup M).map M.subtype =>
          (⟨π x, x, x.2, rfl⟩ : ((P : Subgroup M).map M.subtype).map π)) ⟨?_, ?_⟩))
      · intro x y hxy
        exact Subtype.ext (hinj P x x.2 y y.2 (congrArg Subtype.val hxy))
      · rintro ⟨_, x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p M))
  set Ã := (P₀ : Subgroup M).map M.subtype with hÃdef
  have huniq : ∀ P : Sylow p M, (P : Subgroup M).map M.subtype = Ã := by
    intro P
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      have hxA : π x ∈ Ã.map π := by
        rw [himage P₀]
        exact hle P hx
      obtain ⟨y, hy, hyx⟩ := hxA
      obtain ⟨a, ha⟩ := hpow P x hx
      obtain ⟨b, hb⟩ := hpow P₀ y hy
      rw [eq_of_map_eq_of_pow_eq_one_of_coprime π hc hcop ha hb hyx.symm]
      exact hy
    · rw [hcard P, hcard P₀]
  refine ⟨Ã, hle P₀, huniq, ?_⟩
  let f : Ã →* A := (π.comp Ã.subtype).codRestrict A fun x => hle P₀ x.2
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => Subtype.ext (hinj P₀ x x.2 y y.2 (congrArg Subtype.val hxy)), ?_⟩
    rintro ⟨a, ha⟩
    rw [← himage P₀] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨MulEquiv.ofBijective f hf, fun x => rfl⟩

theorem existsUnique_lift_pow_eq_one [Finite G] (π : G →* Q) (hc : π.ker ≤ Subgroup.center G)
    (hcop : Nat.Coprime (Nat.card π.ker) p) {A : Subgroup Q} (hA : ∀ a ∈ A, a ^ p = 1)
    {Ã : Subgroup G} (e : Ã ≃* A) (he : ∀ x : Ã, (e x : Q) = π x) :
    ∀ a ∈ A, ∃! x : G, π x = a ∧ x ^ p = 1 := by
  intro a ha
  refine ⟨e.symm ⟨a, ha⟩, ⟨?_, ?_⟩, fun y ⟨hy, hyp⟩ => ?_⟩
  · rw [← he, MulEquiv.apply_symm_apply]
  · have h1 : e ((e.symm ⟨a, ha⟩) ^ p) = 1 := by
      rw [map_pow, MulEquiv.apply_symm_apply]
      exact Subtype.ext (hA a ha)
    rw [← Subgroup.coe_pow, (map_eq_one_iff e e.injective).mp h1, Subgroup.coe_one]
  · have hx1 : ((e.symm ⟨a, ha⟩ : Ã) : G) ^ p ^ 1 = 1 := by
      rw [pow_one, ← Subgroup.coe_pow]
      have h1 : e ((e.symm ⟨a, ha⟩) ^ p) = 1 := by
        rw [map_pow, MulEquiv.apply_symm_apply]
        exact Subtype.ext (hA a ha)
      rw [(map_eq_one_iff e e.injective).mp h1, Subgroup.coe_one]
    refine eq_of_map_eq_of_pow_eq_one_of_coprime π hc hcop (a := 1) (b := 1)
      (by rwa [pow_one]) hx1 ?_
    rw [hy, ← he, MulEquiv.apply_symm_apply]

end CFSG.RankThree.Classical
