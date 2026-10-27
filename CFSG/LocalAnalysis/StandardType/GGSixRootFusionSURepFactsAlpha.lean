module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSURepResidual
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionAlpha

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)

theorem ggCentOTwoPrime_conj_le {G : Type*} [Group G] {G₀ : Subgroup G} {g : G} (hg : g ∈ G₀)
    (s : G) :
    ggCentOTwoPrime G₀ (g * s * g⁻¹) ≤
      (ggCentOTwoPrime G₀ s).comap (MulAut.conj g⁻¹).toMonoidHom := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hy, hys, k, hyk⟩
  refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨?_, ?_, k, ?_⟩)
  · change g⁻¹ * y * g⁻¹⁻¹ ∈ G₀
    exact G₀.mul_mem (G₀.mul_mem (G₀.inv_mem hg) hy) (G₀.inv_mem (G₀.inv_mem hg))
  · change g⁻¹ * y * g⁻¹⁻¹ * s = s * (g⁻¹ * y * g⁻¹⁻¹)
    rw [inv_inv]
    calc g⁻¹ * y * g * s = g⁻¹ * (y * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * y) * g := by rw [hys]
      _ = s * (g⁻¹ * y * g) := by group
  · change (g⁻¹ * y * g⁻¹⁻¹) ^ 2 ^ k = 1
    rw [conj_pow, hyk, mul_one, mul_inv_cancel]

theorem exists_injective_ggCentOTwoPrime_conj {G : Type*} [Group G] {G₀ : Subgroup G} {g : G}
    (hg : g ∈ G₀) {s s' : G} (hs : s' = g * s * g⁻¹) :
    ∃ φ : ↥(ggCentOTwoPrime G₀ s') →* ↥(ggCentOTwoPrime G₀ s), Function.Injective φ := by
  subst hs
  refine ⟨((MulAut.conj g⁻¹).toMonoidHom.comp (ggCentOTwoPrime G₀ (g * s * g⁻¹)).subtype).codRestrict
    _ fun x => ggCentOTwoPrime_conj_le hg s x.2, fun x y hxy => ?_⟩
  have h : (MulAut.conj g⁻¹) (x : G) = (MulAut.conj g⁻¹) (y : G) := congrArg Subtype.val hxy
  exact Subtype.ext ((MulAut.conj g⁻¹).injective h)

@[expose] def GGSUSixHSideInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ)
    (ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 →* G),
    ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6) →
      2 ^ (12 * (f + 1)) ≤ ordProj[2] (Nat.card ↥(ggCentOTwoPrime ψ.range
        (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 3)))) ∧
      ∀ N : Subgroup ↥(ggCentOTwoPrime ψ.range
          (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 3))),
        N.Normal → IsPGroup 2 N → ∀ x ∈ N, ∀ y ∈ N, x * y = y * x

@[expose] def GGSUSixKSideInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f : ℕ)
    (ψ : SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 →* G),
    ψ.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6) →
      ∃ Q : Subgroup ↥(ggCentOTwoPrime ψ.range
          (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 1))),
        Q.Normal ∧ IsPGroup 2 Q ∧
        (∀ A : Subgroup ↥(ggCentOTwoPrime ψ.range
            (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 1))),
          A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → Nat.card A ≤ 2 ^ (5 * (f + 1))) ∧
        ordProj[2] (Nat.card (↥(ggCentOTwoPrime ψ.range
          (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 1))) ⧸ Q)) ≤
          2 ^ (6 * (f + 1))

theorem ggSUSixAlphaInput_of_sides (hH : GGSUSixHSideInput) (hK : GGSUSixKSideInput) :
    GGSUSixAlphaInput := by
  intro G _ _ f n hn ψ hker a
  subst hn
  rintro ⟨φ, hφ⟩
  have hconj : ψ (a * ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 1 *
      a⁻¹) = ψ a * ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 1) *
        (ψ a)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  obtain ⟨φ', hφ'⟩ := exists_injective_ggCentOTwoPrime_conj
    (MonoidHom.mem_range.mpr ⟨a, rfl⟩ : ψ a ∈ ψ.range) hconj
  obtain ⟨hH12, hHab⟩ := hH G f ψ hker
  obtain ⟨Q, hQn, hQ2, hQab, hQq⟩ := hK G f ψ hker
  have hKfin : Finite ↥(ggCentOTwoPrime ψ.range
      (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 1))) :=
    inferInstance
  have hlt : 2 ^ (5 * (f + 1)) * ordProj[2] (Nat.card (↥(ggCentOTwoPrime ψ.range
      (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 1))) ⧸ Q)) <
      ordProj[2] (Nat.card ↥(ggCentOTwoPrime ψ.range
        (ψ (ggInvSU (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1)) 6 3)))) := by
    calc _ ≤ 2 ^ (5 * (f + 1)) * 2 ^ (6 * (f + 1)) := Nat.mul_le_mul_left _ hQq
      _ = 2 ^ (11 * (f + 1)) := by rw [← pow_add]; congr 1; ring
      _ < 2 ^ (12 * (f + 1)) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ _ := hH12
  exact not_exists_injective_of_ordProj_two_lt Q hQ2 hQab hHab hlt ⟨φ'.comp φ, hφ'.comp hφ⟩

end CFSG.StandardType
