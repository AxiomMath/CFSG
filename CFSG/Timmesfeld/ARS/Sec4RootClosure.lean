module

public import CFSG.Timmesfeld.ARS.Sec4RadicalLines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

section Normal

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hZ : Subgroup.center G = ⊥) {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ omegaSet R A)
include hR hiso hnd hZ hA hB

theorem normalizer_gen_radPart_eq_top :
    Subgroup.normalizer ((gen ((fun X => radPart R X) ''
      insert B (insert A (lambdaSet R A ∩ omegaSet R B))) : Subgroup G) : Set G) = ⊤ := by
  set S := insert B (insert A (lambdaSet R A ∩ omegaSet R B)) with hS
  set M := gen ((fun X => radPart R X) '' S) with hM
  have hBR : B ∈ R := hB.1
  have hAB : Opposite A B := hB.2
  have hSR : ∀ X ∈ S, X ∈ R := by
    rintro X (rfl | rfl | ⟨hX, -⟩)
    · exact hBR
    · exact hA
    · exact hX.1.1
  have hle : ∀ X ∈ S, radPart R X ≤ M := fun X hX => le_gen (Set.mem_image_of_mem _ hX)
  have hBS : B ∈ S := Or.inl rfl
  have hAS : A ∈ S := Or.inr (Or.inl rfl)
  have hΛ : ∀ C ∈ lambdaSet R A, radPart R C ≤ M := by
    intro C hC
    have hBC : ¬ Commuting B C := not_commuting_of_opposite_of_mem_lambdaSet hR hBR hAB.symm hC
    have hne : B ≠ C := fun e => hBC (e ▸ hR.commuting_self hBR)
    rcases hR.rel B hBR C hC.1.1 hne with h | h | h
    · exact absurd h hBC
    · exact hle C (Or.inr (Or.inr ⟨hC, hC.1.1, h⟩))
    · obtain ⟨P, hPR, P', hP'R, hPle, hP'le, hPC, hP'C, hCle⟩ :=
        radPart_le_sup_of_special hR hiso hnd hZ hA hB hC h
      have hpt : ∀ T ∈ R, T ≤ A ⊔ C → T ≠ C → radPart R T ≤ M := by
        intro T hT hTle hTC
        by_cases hTA : T = A
        · exact hTA ▸ hle A hAS
        · have hTΛ :=
            (mem_lambdaSet_of_le_sup hR hiso hA hC hA le_sup_left hT hTle (Ne.symm hTA)).1
          have hBT := opposite_of_le_sup_of_special hR hiso hA hC hA le_sup_left hBR hAB
            hC.1.1 le_sup_right h hT hTle hTC
          exact hle T (Or.inr (Or.inr ⟨hTΛ, hT, hBT⟩))
      exact hCle.trans (sup_le (hpt P hPR hPle hPC) (hpt P' hP'R hP'le hP'C))
  have hnorm : ∀ F : Subgroup G, (∀ f ∈ F, ∀ X ∈ S, conjSub (radPart R X) f ≤ M) →
      F ≤ Subgroup.normalizer (M : Set G) := by
    intro F hF
    refine le_normalizer_of_conjSub_le fun f hf => ?_
    rw [hM, conjSub_gen]
    refine gen_le ?_
    rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    exact hF f hf X hX
  have hcomm_le : ∀ {f : G} {X : Subgroup G}, X ∈ S → (∀ n ∈ radPart R X, ⁅f, n⁆ ∈ M) →
      conjSub (radPart R X) f ≤ M := by
    intro f X hX h
    rintro _ ⟨n, hn, rfl⟩
    change f * n * f⁻¹ ∈ M
    rw [conj_eq_commutator_mul]
    exact M.mul_mem (h n hn) (hle X hX hn)
  have hSB : ∀ X ∈ S, X ≠ B → B ∈ omegaSet R X := by
    rintro X (rfl | rfl | ⟨-, -, hBX⟩) hXB
    · exact absurd rfl hXB
    · exact hB
    · exact ⟨hBR, hBX.symm⟩
  have hBn : B ≤ Subgroup.normalizer (M : Set G) := by
    refine hnorm B fun f hf X hX => ?_
    by_cases hXB : X = B
    · subst hXB
      rw [conjSub_of_forall_commute fun n hn => commuting_gen_rootClosure hR hBR f
        (le_gen (mem_rootClosure_self hBR) hf) n (radPart_le_gen X hn)]
      exact hle X hX
    · refine hcomm_le hX fun n hn => ?_
      rw [← commutatorElement_inv]
      exact M.inv_mem (hle B hBS (commutatorElement_mem_radPart hR hiso hnd hZ (hSR X hX)
        (hSB X hX hXB) hn (le_gen (mem_rootClosure_self hBR) hf)))
  have hAn : A ≤ Subgroup.normalizer (M : Set G) := by
    refine hnorm A fun f hf X hX => ?_
    have hX0 := hX
    rcases hX with rfl | rfl | ⟨hXΛ, -⟩
    · refine hcomm_le hX0 fun n hn => ?_
      rw [← commutatorElement_inv]
      exact M.inv_mem (hle A hAS (commutatorElement_mem_radPart hR hiso hnd hZ hBR
        ⟨hA, hAB.symm⟩ hn (le_gen (mem_rootClosure_self hA) hf)))
    · rw [conjSub_of_forall_commute fun n hn => commuting_gen_rootClosure hR hA f
        (le_gen (mem_rootClosure_self hA) hf) n (radPart_le_gen _ hn)]
      exact hle _ hX0
    · rw [conjSub_radPart hR, conjSub_of_forall_commute fun x hx => hXΛ.1.2.2 f hf x hx]
      exact hle _ hX0
  have hCn : ∀ C ∈ lambdaSet R A ∩ omegaSet R B, C ≤ Subgroup.normalizer (M : Set G) := by
    rintro C ⟨hCΛ, hCR, hBC⟩
    refine hnorm C fun f hf X hX => ?_
    have hX0 := hX
    rcases hX with rfl | rfl | ⟨hXΛ, -⟩
    · refine hcomm_le hX0 fun n hn => ?_
      rw [← commutatorElement_inv]
      exact M.inv_mem (hle C (Or.inr (Or.inr ⟨hCΛ, hCR, hBC⟩))
        (commutatorElement_mem_radPart hR hiso hnd hZ hBR ⟨hCR, hBC⟩ hn
          (le_gen (mem_rootClosure_self hCR) hf)))
    · rw [conjSub_of_forall_commute fun n hn =>
        ((commuting_gen_rootClosure_of_mem_centralSet ⟨hCR, hCΛ.1.2.2⟩) n
          (radPart_le_gen _ hn) f hf).symm]
      exact hle _ hX0
    · rw [conjSub_radPart hR]
      refine hΛ _ ?_
      have := conjSub_mem_lambdaSet hR hXΛ f
      rwa [conjSub_of_forall_commute fun a ha => (hCΛ.1.2.2 a ha f hf).symm] at this
  have hΛn : ∀ C ∈ lambdaSet R A, C ≤ Subgroup.normalizer (M : Set G) := by
    intro C hC
    have hBC : ¬ Commuting B C := not_commuting_of_opposite_of_mem_lambdaSet hR hBR hAB.symm hC
    have hne : B ≠ C := fun e => hBC (e ▸ hR.commuting_self hBR)
    rcases hR.rel B hBR C hC.1.1 hne with h | h | h
    · exact absurd h hBC
    · exact hCn C ⟨hC, hC.1.1, h⟩
    · obtain ⟨P, hPR, hPle, hPA, hPC⟩ := exists_mem_le_sup_ne_ne hR hiso hA hC A C
      obtain ⟨hPΛ, hsup⟩ :=
        mem_lambdaSet_of_le_sup hR hiso hA hC hA le_sup_left hPR hPle (Ne.symm hPA)
      have hBP := opposite_of_le_sup_of_special hR hiso hA hC hA le_sup_left hBR hAB hC.1.1
        le_sup_right h hPR hPle hPC
      calc C ≤ A ⊔ C := le_sup_right
        _ = A ⊔ P := hsup.symm
        _ ≤ _ := sup_le hAn (hCn P ⟨hPΛ, hPR, hBP⟩)
  rw [eq_top_iff, ← gen_lambdaSet_sup_eq_top_of hR hiso hnd hA hB]
  exact sup_le (gen_le hΛn) hBn

theorem commuting_gen_radPart :
    Commuting (gen ((fun X => radPart R X) '' insert B (insert A (lambdaSet R A ∩ omegaSet R B))))
      (gen ((fun X => radPart R X) '' insert B (insert A (lambdaSet R A ∩ omegaSet R B)))) := by
  set S := insert B (insert A (lambdaSet R A ∩ omegaSet R B)) with hS
  set M := gen ((fun X => radPart R X) '' S) with hM
  have hN := normalizer_gen_radPart_eq_top hR hiso hnd hZ hA hB
  have hBR : B ∈ R := hB.1
  have hAB : Opposite A B := hB.2
  have hSR : ∀ X ∈ S, X ∈ R := by
    rintro X (rfl | rfl | ⟨hX, -⟩)
    · exact hBR
    · exact hA
    · exact hX.1.1
  have hSB : ∀ X ∈ S, X ≠ B → B ∈ omegaSet R X := by
    rintro X (rfl | rfl | ⟨-, -, hBX⟩) hXB
    · exact absurd rfl hXB
    · exact hB
    · exact ⟨hBR, hBX.symm⟩
  have hBc : Commuting (radPart R B) M := by
    rw [commuting_iff_le_centralizer]
    refine gen_le ?_
    rintro _ ⟨X, hX, rfl⟩
    rw [← commuting_iff_le_centralizer]
    intro m hm n hn
    by_cases hXB : X = B
    · subst hXB
      exact commuting_gen_rootClosure hR hBR m (radPart_le_gen X hm) n (radPart_le_gen X hn)
    · exact (commute_of_mem_radPart hR hiso hnd hZ (hSR X hX) (hSB X hX hXB) hn hm).symm
  have hall : ∀ X ∈ R, Commuting (radPart R X) M := by
    intro X hX
    obtain ⟨g, rfl⟩ := hR.exists_conjSub_eq hBR hX
    have hMg : conjSub M g = M := conjSub_eq_self_iff.2 (hN ▸ Subgroup.mem_top g)
    have := hBc.conjSub g
    rwa [hMg, conjSub_radPart hR] at this
  rw [commuting_iff_le_centralizer]
  refine gen_le ?_
  rintro _ ⟨X, hX, rfl⟩
  rw [← commuting_iff_le_centralizer]
  exact (hall X (hSR X hX)).symm

end Normal

section Main

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hZ : Subgroup.center G = ⊥) (htwo : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
include hR hiso hnd hZ htwo

theorem radPart_eq_bot_of {A : Subgroup G} (hA : A ∈ R) : radPart R A = ⊥ := by
  obtain ⟨B, hBR, hAB⟩ := hiso A hA
  have hB : B ∈ omegaSet R A := ⟨hBR, hAB⟩
  set S := insert B (insert A (lambdaSet R A ∩ omegaSet R B)) with hS
  set M := gen ((fun X => radPart R X) '' S) with hM
  have hSR : ∀ X ∈ S, X ∈ R := by
    rintro X (rfl | rfl | ⟨hX, -⟩)
    · exact hBR
    · exact hA
    · exact hX.1.1
  have hNM : M.Normal := Subgroup.normalizer_eq_top_iff.1
    (normalizer_gen_radPart_eq_top hR hiso hnd hZ hA hB)
  have hcM := commuting_gen_radPart hR hiso hnd hZ hA hB
  have hsq : ∀ x ∈ M, x * x = 1 := by
    intro x hx
    refine (gen_induction (p := fun y => y ∈ M ∧ y * y = 1) hx ?_ ⟨one_mem _, mul_one 1⟩
      fun y z ⟨hy, hyy⟩ ⟨hz, hzz⟩ => ⟨Subgroup.mul_mem _ hy hz, ?_⟩).2
    · rintro _ ⟨X, hX, rfl⟩ y hy
      exact ⟨le_gen (Set.mem_image_of_mem _ hX) hy,
        mul_self_of_mem_gen_rootClosure hR (hSR X hX) (radPart_le_gen X hy)⟩
    · calc y * z * (y * z) = y * (z * y) * z := by group
        _ = y * (y * z) * z := by rw [(hcM z hz y hy).eq]
        _ = 1 := by rw [← mul_assoc, hyy, one_mul, hzz]
  have hP : IsPGroup 2 M := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, pow_two, OneMemClass.coe_one]
    exact hsq x x.2)⟩
  have hM1 := htwo M hNM hP
  exact le_bot_iff.1 (hM1 ▸ le_gen (Set.mem_image_of_mem _ (Or.inr (Or.inl rfl) : A ∈ S)))

theorem radical_eq_bot_of : radical R = ⊥ :=
  le_bot_iff.1 (iSup₂_le fun _ hA => (radPart_eq_bot_of hR hiso hnd hZ htwo hA).le)

theorem rootClosure_eq_singleton_of {A : Subgroup G} (hA : A ∈ R) : rootClosure R A = {A} := by
  obtain ⟨B, hBR, hAB⟩ := hiso A hA
  have hN : rootNorm R A B = ⊥ := by
    rw [rootNorm_eq_radPart hR hiso hnd hZ hA ⟨hBR, hAB⟩,
      radPart_eq_bot_of hR hiso hnd hZ htwo hA]
  ext A'
  rw [Set.mem_singleton_iff]
  constructor
  · intro hA'
    obtain ⟨a', ha', ha'1⟩ := hR.exists_ne_one hA'.1
    obtain ⟨a, ha, ha1, han⟩ := exists_inv_mul_mem_rootNorm hR hiso hA hBR hAB hA' ha' ha'1
    rw [hN, Subgroup.mem_bot, inv_mul_eq_one] at han
    by_contra hne
    have hmem : a ∈ A ⊓ A' := Subgroup.mem_inf.2 ⟨ha, han ▸ ha'⟩
    rw [inf_eq_bot hR hiso hA hA'.1 (fun h => hne h.symm), Subgroup.mem_bot] at hmem
    exact ha1 hmem
  · rintro rfl
    exact mem_rootClosure_self hA

end Main

theorem radical_eq_bot (h : Hyp G R) : radical R = ⊥ := by
  have := h.finite
  exact radical_eq_bot_of h.root h.noIsolated h.nondeg h.center h.twoCore

theorem rootClosure_eq_singleton (h : Hyp G R) {A : Subgroup G} (hA : A ∈ R) :
    rootClosure R A = {A} := by
  have := h.finite
  exact rootClosure_eq_singleton_of h.root h.noIsolated h.nondeg h.center h.twoCore hA

theorem eq_of_omegaSet_eq (h : Hyp G R) {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ R)
    (hΩ : omegaSet R D = omegaSet R A) : D = A := by
  have := h.finite
  have hmem := mem_rootClosure_of_omegaSet_eq h.root h.noIsolated hA hD hΩ
  rwa [rootClosure_eq_singleton h hA, Set.mem_singleton_iff] at hmem

end CFSG.Timmesfeld.ARS
