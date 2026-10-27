module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1ParabBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

theorem isPGroup_ker_comp_equiv {A B C : Type*} [Group A] [Group B] [Group C] (ψ : A ≃* B)
    (f : B →* C) (hf : IsPGroup 2 f.ker) : IsPGroup 2 (f.comp ψ.toMonoidHom).ker := by
  intro x
  obtain ⟨k, hk⟩ := hf ⟨ψ x.1, x.2⟩
  refine ⟨k, Subtype.ext (ψ.injective ?_)⟩
  have h1 : (ψ x.1) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  change ψ (x.1 ^ 2 ^ k) = ψ 1
  rw [map_pow, map_one]
  exact h1

section Levi

variable {K : Type} [Field K] [Finite K]

theorem exists_perfect_sl2_image [CharP K 2] {f : ℕ} (hf : Nat.card K = 2 ^ f) (j : Fin 2)
    {H : Subgroup (projectiveSL 3 K)} (hHP : H ≤ (Q3 K j).map (proj 3 K)) (hH : ⁅H, H⁆ = H)
    (hne : H ≠ ⊥) :
    ∃ A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), ⁅A, A⁆ = A ∧ A ≠ ⊥ ∧
      Nat.card A ∣ Nat.card H := by
  have hinj : ∀ x ∈ perfectCore (Q3 K j), ∀ y ∈ perfectCore (Q3 K j),
      proj 3 K x = proj 3 K y → x = y := fun x hx y hy hxy => by
    have hz : x⁻¹ * y ∈ (proj 3 K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    exact inv_mul_eq_one.mp (congrArg Subtype.val (blk3_scalars j
      ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩ ((ker_proj 3 K).le hz)))
  set C := perfectCore ((Q3 K j).map (proj 3 K)) with hC
  let g : ↥C →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (blk3 j).comp (perfectCoreMapEquiv (proj 3 K) (Q3 K j) hinj).symm.toMonoidHom
  have hker : IsPGroup 2 g.ker :=
    isPGroup_ker_comp_equiv _ (blk3 j) (blk3_ker_isPGroup ⟨f, hf⟩ j)
  have hHC : H ≤ C := le_perfectCore_of_perfect hHP hH
  have hH₀ : ⁅H.subgroupOf C, H.subgroupOf C⁆ = H.subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hHC, hH]
  refine ⟨(H.subgroupOf C).map g, by rw [← Subgroup.map_commutator, hH₀], fun hbot => ?_, ?_⟩
  · have hle : H.subgroupOf C ≤ g.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    haveI : Group.IsSolvable g.ker := by
      have := hker.isNilpotent
      infer_instance
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hHC, eq_bot_of_perfect_of_le_solvable hle hH₀,
      Subgroup.map_bot]
  · exact (Subgroup.card_map_dvd (H.subgroupOf C) g).trans
      (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv))

theorem exists_prime_of_perfect_parabolic (hD : DicksonSL2) [CharP K 2] {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hodd : Odd f) {d : ℕ} (hd : d = 1 ∨ d = 2)
    {H : Subgroup (projectiveSL 3 K)} (hHP : H ≤ projStabilizer (flagSpace 3 K d))
    (hH : ⁅H, H⁆ = H) (hne : H ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card H ∧ r ∣ Nat.card K - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j : Fin 2, (j : ℕ) + 1 = d :=
    ⟨⟨d - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨A, hA, hAne, hdvd⟩ := exists_perfect_sl2_image hf j hHP hH hne
  obtain ⟨r, hr, h5, hrA, hrK⟩ := hD K f hf hodd A hA hAne
  exact ⟨r, hr, h5, hrA.trans hdvd, hrK⟩

end Levi

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
