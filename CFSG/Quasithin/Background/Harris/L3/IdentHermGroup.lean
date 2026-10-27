module

public import CFSG.Quasithin.Background.Harris.L3.IdentHerm
public import CFSG.Quasithin.Background.HL3NineNorm

public section

namespace CFSG.Quasithin.G11.Harris.L3

set_option linter.unusedSectionVars false

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem map_center_of_involutive {G : Type*} [Group G] (ψ : G →* G) (hψ : ∀ g, ψ (ψ g) = g)
    {z : G} (hz : z ∈ Subgroup.center G) : ψ z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro h
  have := hz (ψ h)
  calc h * ψ z = ψ (ψ h) * ψ z := by rw [hψ]
    _ = ψ (ψ h * z) := by rw [map_mul]
    _ = ψ (z * ψ h) := by rw [this]
    _ = ψ z * h := by rw [map_mul, hψ]

theorem eq_bot_or_eq_center {F : Type} [Field F] {N : Subgroup SL(3, F)}
    (hN : N ≤ Subgroup.center SL(3, F)) : N = ⊥ ∨ N = Subgroup.center SL(3, F) := by
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨⟨x, hxN⟩, hx1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
  have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
  have hxc := hN hxN
  obtain ⟨s, hs3, hsx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hxc
  rw [Fintype.card_fin] at hs3
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hx1
    apply Subtype.ext
    rw [← hsx]
    simp
  have h1 : s ^ 2 + s + 1 = 0 := by
    have : (s - 1) * (s ^ 2 + s + 1) = 0 := by linear_combination hs3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hs1)
  refine le_antisymm hN fun z hz => ?_
  obtain ⟨r, hr3, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr3
  have hprod : (r - 1) * (r - s) * (r - s ^ 2) = 0 := by
    linear_combination hr3 - (r ^ 2 - r) * h1 + (r - 1) * hs3
  have hxx : x * x ∈ N := N.mul_mem hxN hxN
  rcases mul_eq_zero.1 hprod with h | h
  · rcases mul_eq_zero.1 h with h | h
    · have : r = 1 := sub_eq_zero.1 h
      subst this
      have : z = 1 := Subtype.ext (by rw [← hrz]; simp)
      rw [this]
      exact N.one_mem
    · have : r = s := sub_eq_zero.1 h
      subst this
      have : z = x := Subtype.ext (by rw [← hrz, ← hsx])
      rw [this]
      exact hxN
  · have : r = s ^ 2 := sub_eq_zero.1 h
    subst this
    have : z = x * x := Subtype.ext (by
      rw [← hrz, Matrix.SpecialLinearGroup.coe_mul, ← hsx, ← map_mul, sq])
    rw [this]
    exact hxx

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem ker_le_center_herm {L : Subgroup (GLV V)} {π : SL(3, F) →* ↥L}
    (hK : Nat.card F = (2 ^ n) ^ 2) {ψ : SL(3, F) →* SL(3, F)} (hψ : ∀ g, ψ (ψ g) = g)
    {E : Multiplicative V ≃* HMod n F}
    (hE : ∀ g u, E (Multiplicative.ofAdd (repOfHom L π g u)) =
      rho hK (ψ g) (E (Multiplicative.ofAdd u))) :
    π.ker ≤ Subgroup.center SL(3, F) := by
  intro g hg
  have hπ : π g = 1 := hg
  have h1 : rho hK (ψ g) = 1 := by
    refine MulEquiv.ext fun x => ?_
    have := hE g (Multiplicative.toAdd (E.symm x))
    rw [repOfHom_apply, hπ] at this
    simp only [OneMemClass.coe_one, LinearEquiv.coe_one, id_eq, ofAdd_toAdd,
      MulEquiv.apply_symm_apply] at this
    rw [MulAut.one_apply]
    exact this.symm
  have h2 := mem_scalars_of_rho_eq_one hK h1
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center] at h2
  have := map_center_of_involutive ψ hψ h2
  rwa [hψ] at this

theorem isSL3_of_injective {L : Subgroup (GLV V)} {n : ℕ} (hn : 1 ≤ n)
    {π : SL(3, GaloisField 2 (2 * n)) →* ↥L} (hπ : Function.Surjective π)
    (hinj : Function.Injective π) : IsSL3 (2 ^ (2 * n)) ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨GaloisField 2 (2 * n), inferInstance, inferInstance,
    GaloisField.card 2 (2 * n) (by omega), ⟨?_⟩⟩
  exact (MulEquiv.ofBijective π ⟨hinj, hπ⟩).symm.trans
    (specialLinearGroupEquivStatedSL 3 (GaloisField 2 (2 * n)))

theorem isPSL_of_ker_eq_center {L : Subgroup (GLV V)} {n : ℕ} (hn : 1 ≤ n)
    {π : SL(3, GaloisField 2 (2 * n)) →* ↥L} (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center SL(3, GaloisField 2 (2 * n))) : IsPSL 3 2 (2 * n) ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩, GaloisField 2 (2 * n), inferInstance,
    inferInstance, GaloisField.card 2 (2 * n) (by omega), ⟨?_⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    have : 2 ^ 1 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    have : 2 ^ 1 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · exact ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField 2 (2 * n)))

theorem isSL3_or_isPSL_herm {L : Subgroup (GLV V)} {n : ℕ} (hn : 1 ≤ n)
    {π : SL(3, GaloisField 2 (2 * n)) →* ↥L} (hπ : Function.Surjective π)
    (hK : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2)
    {ψ : SL(3, GaloisField 2 (2 * n)) →* SL(3, GaloisField 2 (2 * n))}
    (hψ : ∀ g, ψ (ψ g) = g) {E : Multiplicative V ≃* HMod n (GaloisField 2 (2 * n))}
    (hE : ∀ g u, E (Multiplicative.ofAdd (repOfHom L π g u)) =
      rho hK (ψ g) (E (Multiplicative.ofAdd u))) :
    IsSL3 (2 ^ (2 * n)) ↥L ∨ IsPSL 3 2 (2 * n) ↥L := by
  rcases eq_bot_or_eq_center (ker_le_center_herm hK hψ hE) with h | h
  · exact Or.inl (isSL3_of_injective hn hπ ((MonoidHom.ker_eq_bot_iff π).1 h))
  · exact Or.inr (isPSL_of_ker_eq_center hn hπ h)

theorem isHermitianTensorModule_herm {L : Subgroup (GLV V)} {n : ℕ}
    {π : SL(3, GaloisField 2 (2 * n)) →* ↥L} (hπ : Function.Surjective π)
    (hK : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2)
    {ψ : SL(3, GaloisField 2 (2 * n)) →* SL(3, GaloisField 2 (2 * n))}
    (hψ : ∀ g, ψ (ψ g) = g) {E : Multiplicative V ≃* HMod n (GaloisField 2 (2 * n))}
    (hE : ∀ g u, E (Multiplicative.ofAdd (repOfHom L π g u)) =
      rho hK (ψ g) (E (Multiplicative.ofAdd u))) :
    IsHermitianTensorModule L n := by
  let s := specialLinearGroupEquivStatedSL 3 (GaloisField 2 (2 * n))
  have hψs : Function.Surjective ψ := fun g => ⟨ψ g, hψ g⟩
  refine ⟨π.comp (ψ.comp s.symm.toMonoidHom), AddMonoidHom.toZModLinearMap 2 (hmu E),
    hπ.comp (hψs.comp s.symm.surjective), hmu_injective E, fun X => ⟨?_, ?_⟩, fun g v => ?_⟩
  · rintro ⟨v, rfl⟩ i j
    have := hmu_bar E v i j
    rw [bar_apply] at this
    exact this.symm
  · intro hX
    refine exists_hmu_eq E ?_
    ext i j
    simp only [conjM, Matrix.transpose_apply, Matrix.map_apply, bar_apply]
    exact (hX i j).symm
  · have := hmu_act hK hψ hE (s.symm g) v
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at *
    show hmu E _ = _
    rw [this, tw, conjM_eq_map_pow]
    have hg : (((s.symm g : SL(3, GaloisField 2 (2 * n))) : Matrix (Fin 3) (Fin 3)
        (GaloisField 2 (2 * n)))) = ((g : GL (Fin 3) (GaloisField 2 (2 * n))) :
          Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))) := by
      conv_rhs => rw [← s.apply_symm_apply g]
      rfl
    rw [hg]
    rfl

end CFSG.Quasithin.G11.Harris.L3
