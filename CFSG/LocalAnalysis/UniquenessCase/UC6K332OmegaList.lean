module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieBlockFrame
import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathPair
import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathFrame
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaMatrix
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePslNonab
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResOrthWeir

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.ClassicalGroups.Orthogonal Module QuadraticMap
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

theorem exists_mem_commutator_pairInv {C G : Type} [Group C] [Group G] {r : ℕ}
    (F : BlockFrame C r G) {i j : Fin r} (hij : i ≠ j) :
    ∃ g ∈ commutator G, ∀ c, g * F.T c * g⁻¹ =
      F.T (Function.update (Function.update c i (c i ^ (-1 : ℤ))) j (c j ^ (-1 : ℤ))) := by
  obtain ⟨u, hu⟩ := F.exists_inv i
  have hff : ∀ d : Fin r → C,
      Function.update (Function.update d i (d i)⁻¹) i ((Function.update d i (d i)⁻¹) i)⁻¹ = d := by
    intro d
    simp
  have hinv : ∀ d : Fin r → C, u⁻¹ * F.T d * u = F.T (Function.update d i (d i)⁻¹) := by
    intro d
    have h := hu (Function.update d i (d i)⁻¹)
    rw [hff] at h
    rw [← h]
    group
  have hA : ∀ c : Fin r → C, (F.S (Equiv.swap i j))⁻¹ * F.T c * F.S (Equiv.swap i j) =
      F.T (c ∘ ⇑(Equiv.swap i j)) := by
    intro c
    have h := F.S_conj (Equiv.swap i j)⁻¹ c
    simp only [map_inv, inv_inv] at h
    exact h
  have hC : ∀ e : Fin r → C, F.S (Equiv.swap i j) * F.T e * (F.S (Equiv.swap i j))⁻¹ =
      F.T (e ∘ ⇑(Equiv.swap i j)) := by
    intro e
    have h := F.S_conj (Equiv.swap i j) e
    rw [Equiv.swap_inv] at h
    exact h
  refine ⟨u * F.S (Equiv.swap i j) * u⁻¹ * (F.S (Equiv.swap i j))⁻¹, ?_, fun c => ?_⟩
  · rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · have e1 : u * F.S (Equiv.swap i j) * u⁻¹ * (F.S (Equiv.swap i j))⁻¹ * F.T c *
          (u * F.S (Equiv.swap i j) * u⁻¹ * (F.S (Equiv.swap i j))⁻¹)⁻¹ =
        u * (F.S (Equiv.swap i j) * (u⁻¹ * ((F.S (Equiv.swap i j))⁻¹ * F.T c *
          F.S (Equiv.swap i j)) * u) * (F.S (Equiv.swap i j))⁻¹) * u⁻¹ := by
      group
    rw [e1, hA c, hinv, hC, hu]
    congr 1
    funext k
    by_cases hki : k = i
    · simp [hki, Equiv.swap_apply_left, Equiv.swap_apply_right, hij, Ne.symm hij]
    by_cases hkj : k = j
    · simp [hkj, Equiv.swap_apply_left, Equiv.swap_apply_right, Ne.symm hij]
    · simp [Function.update_apply, Equiv.swap_apply_of_ne_of_ne, hki, hkj]

theorem listRow_projOmega_of_blockFrame {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : QuadraticForm F (ι → F)} {Q₀ : (ι → F) → F} (hQ0 : ⇑Q = Q₀)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule F (ι → F), finrank F T = 3 ∧ ∀ x ∈ T, Q x = 0) {a : ℕ} (ha : 1 ≤ a)
    (B : BlockFrame (Multiplicative (ZMod (3 ^ a))) 3 ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
    (hcard : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q)).factorization 3 = 3 * a + 1) :
    ListRow (StatedProj (StatedOmega Q₀)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero (3 ^ a) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨pj, hsurj, hker, hsq⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.exists_pj hQ0 hQ hT
  have : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := Finite.of_injective
    (fun g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q) =>
      ((g : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) → (ι → F)))
    (fun x y h => Subtype.ext (LinearEquiv.coe_injective (by simpa using h)))
  have hTmem : ∀ c, B.T c ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := fun c =>
    mem_commutator_of_odd_pow_eq_one hsq ((by decide : Odd 3).pow : Odd (3 ^ a))
      (by rw [← map_pow, pow_pPow_eq_one_pi, map_one])
  let T' := B.T.codRestrict (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) hTmem
  let φ := pj.comp T'
  have hconj : ∀ (g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
      (hg : g ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))
      (c d : Fin 3 → Multiplicative (ZMod (3 ^ a))),
      g * B.T c * g⁻¹ = B.T d → pj ⟨g, hg⟩ * φ c * (pj ⟨g, hg⟩)⁻¹ = φ d := by
    intro g hg c d h
    show pj ⟨g, hg⟩ * pj (T' c) * (pj ⟨g, hg⟩)⁻¹ = pj (T' d)
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg pj (Subtype.ext h)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have h2 : T' c ^ 2 = 1 := hker (T' c) hc
    have h3 : T' c ^ 3 ^ a = 1 := by rw [← map_pow, pow_pPow_eq_one_pi, map_one]
    have h4 := eq_one_of_sq_eq_one_of_pow_eq_one (by norm_num : (3 : ℕ) ≠ 2) h2 h3
    exact B.T_injective (by rw [map_one]; exact congrArg Subtype.val h4)
  have hcardP : (Nat.card (StatedProj (StatedOmega Q₀))).factorization 3 = 3 * a + 1 := by
    rw [factorization_card_of_surjective (p := 3) (by norm_num) pj hsurj hker,
      factorization_card_commutator (p := 3) (by norm_num) hsq, hcard]
  have hS : ¬ 3 ^ (3 * a + 2) ∣ Nat.card (StatedProj (StatedOmega Q₀)) := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne', hcardP]
    omega
  have hC : Nat.card (Multiplicative (ZMod (3 ^ a))) = 3 ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hS3 : B.S (finRotate 3) ^ 3 = 1 := by
    rw [← map_pow, show finRotate 3 ^ 3 = 1 by decide, map_one]
  have hSΩ : B.S (finRotate 3) ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
    mem_commutator_of_odd_pow_eq_one hsq (by decide : Odd 3) hS3
  have hS3' : (⟨_, hSΩ⟩ : ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q))) ^ 3 = 1 :=
    Subtype.ext hS3
  refine Wreath.listRow_of_wreath_pair ha hC hφ (μ := -1) (by norm_num) ?_
    (s := pj ⟨_, hSΩ⟩) ?_ ?_ hS
  · intro i j hij
    obtain ⟨g, hg, hgc⟩ := exists_mem_commutator_pairInv B hij
    exact ⟨pj ⟨g, hg⟩, fun c => hconj g hg c _ (hgc c)⟩
  · rw [← map_pow, hS3', map_one]
  · intro x
    refine hconj _ hSΩ x _ ?_
    rw [B.S_conj]
    congr 1
    funext i
    show x (((finRotate 3)⁻¹ : Equiv.Perm (Fin 3)) i) = x (i - 1)
    rw [Wreath.finRotate_three_inv_apply]

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
