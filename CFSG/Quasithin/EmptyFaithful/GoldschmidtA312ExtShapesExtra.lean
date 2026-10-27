module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312ExtShapesBase

public section

namespace CFSG.Quasithin.A312ExtShapes

open CFSG.Quasithin

theorem isExtraspecial2_of_central_involution {V : Type} [Group V] [Finite V] (z : V)
    (hz1 : z ≠ 1) (hzc : ∀ y : V, y * z = z * y) (hsq : ∀ x : V, x * x = 1 ∨ x * x = z)
    (hcomm : ∀ x y : V, x * y = y * x ∨ x * y = z * (y * x))
    (hcen : ∀ x : V, (∀ y : V, x * y = y * x) → x = 1 ∨ x = z) {m : ℕ}
    (hcard : Nat.card V = 2 ^ (1 + 2 * m)) (hm : 1 ≤ m) : IsExtraspecial2 m V := by
  have hzz : z * z = 1 := by
    rcases hsq z with h | h
    · exact h
    · exact absurd (mul_eq_right.mp h) hz1
  have hmemC : ∀ x : V, x ∈ Subgroup.center V ↔ x = 1 ∨ x = z := by
    intro x
    rw [Subgroup.mem_center_iff]
    constructor
    · intro h
      exact hcen x fun y => (h y).symm
    · rintro (rfl | rfl) y
      · simp
      · exact hzc y
  have hcenter : (Subgroup.center V : Set V) = {1, z} := by
    ext x
    simpa using hmemC x
  have hc2 : Nat.card ↥(Subgroup.center V) = 2 := by
    show Nat.card ((Subgroup.center V : Set V)) = 2
    rw [Nat.card_coe_set_eq, hcenter]
    exact Set.ncard_pair hz1.symm
  have hsqC : ∀ x : V, x * x ∈ Subgroup.center V := fun x => by
    rcases hsq x with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact (hmemC z).mpr (Or.inr rfl)
  refine ⟨⟨hc2, ?_, ?_⟩, hcard⟩
  · have : IsMulCommutative (V ⧸ Subgroup.center V) := ⟨⟨fun a b => by
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rcases hcomm x y with h | h
      · rw [h]; simp
      · have hc : Commute (y * x) z := hzc (y * x)
        have h2 : (z * (y * x))⁻¹ * (y * x) = z⁻¹ := by
          calc (z * (y * x))⁻¹ * (y * x) = (y * x)⁻¹ * (z⁻¹ * (y * x)) := by group
            _ = (y * x)⁻¹ * ((y * x) * z⁻¹) := by rw [hc.inv_right.eq]
            _ = z⁻¹ := by group
        rw [h, h2]
        exact Subgroup.inv_mem _ ((hmemC z).mpr (Or.inr rfl))⟩⟩
    exact ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
      induction a using QuotientGroup.induction_on with | H x => ?_
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
      exact hsqC x⟩
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center V)
    rw [hc2, hcard] at h1
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    have hq : Nat.card (V ⧸ Subgroup.center V) = 2 ^ (2 * m) := by
      have h2 : 2 ^ (1 + 2 * m) = 2 ^ (2 * m) * 2 := by ring
      omega
    rw [hq]
    exact Nat.one_lt_two_pow (by omega)

open CFSG.QuasithinUnique.Vol2Native.A312L

theorem isExt_extraspecial_sl3 {A : Type} [Group A] (V : Subgroup A) [V.Normal]
    (hV : IsExtraspecial2 3 ↥V) (e : A ⧸ V ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    IsExt A (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) :=
  ⟨V, inferInstance, hV, Seven.isPSL_three_two e⟩

theorem isExt_extraspecial_sl3_of_lFamily {G : Type} [Group G] [Finite G]
    {T B Z A : Subgroup G} (hB : B ∈ lFamily T) (hZ : B ⊔ T = Z) (hAZ : A ≤ Z)
    (hcomm : ⁅Z, Z⁆ ≤ A) (hperf : ⁅A, A⁆ = A) (V : Subgroup ↥A) [V.Normal]
    (hV : IsExtraspecial2 3 ↥V) (e : ↥A ⧸ V ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsExtraspecial 2 ↥V := hV.1
  have hV2 : IsPGroup 2 ↥V := CFSG.IsExtraspecial.isPGroup 2 ↥V
  have : Group.IsNilpotent ↥V := hV2.isNilpotent
  have hf : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' V)) :=
    e.surjective.comp (QuotientGroup.mk'_surjective V)
  have hkerle : (e.toMonoidHom.comp (QuotientGroup.mk' V)).ker ≤ V := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff x).mp (e.injective (hx.trans e.map_one.symm))
  have hsolv : Group.IsSolvable (e.toMonoidHom.comp (QuotientGroup.mk' V)).ker :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hkerle)
      (Subgroup.inclusion_injective hkerle)
  have := Seven.slThree_isSimple
  exact isExt_of_perfect_simple_quotient hB hZ hAZ hcomm hperf Seven.slThree_nonabelian _ hf hsolv
    (fun V W _ _ e h => IsExtraspecial2.of_mulEquiv e h) (fun V W _ _ e h => IsPSL.of_mulEquiv e h)
    V hV (Seven.isPSL_three_two e)

end CFSG.Quasithin.A312ExtShapes
