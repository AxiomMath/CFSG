module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Fan86

namespace P74

variable {G : Type*} [Group G]

theorem exists_fixed_of_not_dvd {x : G} (hx : x ^ 5 = 1) {S : Set G}
    (hS : ∀ s ∈ S, x * s * x⁻¹ ∈ S) (hfin : S.Finite) (hn : ¬ 5 ∣ S.ncard) :
    ∃ s ∈ S, x * s * x⁻¹ = s := by
  have : Finite S := hfin.to_subtype
  have : Fintype S := Fintype.ofFinite S
  have hinj : Function.Injective (fun s : S => (⟨x * s * x⁻¹, hS s s.2⟩ : S)) := by
    intro a b h
    have h1 : x * (a : G) * x⁻¹ = x * (b : G) * x⁻¹ := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  let σ : Equiv.Perm S := Equiv.ofBijective _ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have hσapp : ∀ s : S, (σ s : G) = x * s * x⁻¹ := fun s => rfl
  have hσ : σ ^ 5 ^ 1 = 1 := by
    ext s
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.coe_one,
      id_eq, hσapp]
    have hx' : x * x * x * x * x = 1 := by simpa [pow_succ, mul_assoc] using hx
    calc x * (x * (x * (x * (x * (s : G) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹) * x⁻¹
        = (x * x * x * x * x) * (s : G) * (x * x * x * x * x)⁻¹ := by group
      _ = s := by rw [hx']; simp
  have hp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : ¬ 5 ∣ Fintype.card S := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hσ
  refine ⟨s, s.2, ?_⟩
  have := congrArg Subtype.val hs
  rwa [hσapp] at this

theorem exists_centralized_involution {H M : Subgroup G} (hH : IsPGroup 2 H) (hM : IsPGroup 2 M)
    [Finite M] (hnorm : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) (hne : M ≠ ⊥) :
    ∃ m ∈ M, m ≠ 1 ∧ m * m = 1 ∧ ∀ h ∈ H, h * m = m * h := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction H M :=
    { smul := fun h m => ⟨h * m * h⁻¹, hnorm h h.2 m m.2⟩
      one_smul := fun m => Subtype.ext (by simp [HSMul.hSMul, SMul.smul])
      mul_smul := fun a b m => Subtype.ext (by simp [HSMul.hSMul, SMul.smul, mul_assoc]) }
  have hMeven : 2 ∣ Nat.card M := by
    have hnt : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hne
    obtain ⟨n, hn, hcard⟩ := (hM.nontrivial_iff_card).1 hnt
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  have hmod := hH.card_modEq_card_fixedPoints M
  have hfix : ∀ (z : G) (hz : z ∈ M), (⟨z, hz⟩ : M) ∈ MulAction.fixedPoints H M ↔
      ∀ h ∈ H, h * z = z * h := by
    intro z hz
    constructor
    · intro hf h hh
      have := congrArg Subtype.val (hf ⟨h, hh⟩)
      have h2 : h * z * h⁻¹ = z := this
      calc h * z = h * z * h⁻¹ * h := by group
        _ = z * h := by rw [h2]
    · intro hf h
      apply Subtype.ext
      show (h : G) * z * (h : G)⁻¹ = z
      rw [hf h h.2]
      group
  have hZcard : Nat.card (M ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) =
      Nat.card (MulAction.fixedPoints H M) := by
    refine Nat.card_congr
      { toFun := fun z => ⟨⟨z.1, z.2.1⟩, (hfix z.1 z.2.1).2 (fun h hh =>
          Subgroup.mem_centralizer_iff.1 z.2.2 h hh)⟩
        invFun := fun m => ⟨m.1.1, m.1.2, Subgroup.mem_centralizer_iff.2
          ((hfix m.1.1 m.1.2).1 m.2)⟩
        left_inv := fun z => rfl
        right_inv := fun m => rfl }
  have hZeven : 2 ∣ Nat.card (M ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) := by
    rw [hZcard]
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hMeven))
  have : Finite (M ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) :=
    Finite.of_injective (fun z => (⟨z.1, z.2.1⟩ : M)) (fun a b h =>
      Subtype.ext (show (a : G) = b from congrArg (fun m : M => (m : G)) h))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hZeven
  refine ⟨z.1, z.2.1, ?_, ?_, fun h hh => Subgroup.mem_centralizer_iff.1 z.2.2 h hh⟩
  · intro h1
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · have h2 : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hz])
    have := congrArg Subtype.val h2
    simpa [pow_two] using this

end P74

end CFSG.Quasithin.Fan86
