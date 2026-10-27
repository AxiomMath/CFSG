module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfC
public import CFSG.Quasithin.Background.C35InspSp4
public import CFSG.Quasithin.H13.NQCatParabolicSp4

public section

namespace CFSG.Quasithin.H13.Ch9.F112Pf

open CFSG.Open (pCoreOf pCore)
open CFSG.QuasithinUnique CFSG.Quasithin Matrix CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.C35Pf CFSG.Quasithin.H13.NQCat.Sp4
open scoped commutatorElement

section Sp4

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "⟪" x "⟫" => spMat (x : StatedSp 2 K)

omit [Finite K] [CharP K 2] in
theorem xC_inv (s : K) : (xC s)⁻¹ = xC (-s) :=
  ((root_matrix_data (r := 2) (K := K)).1 _ _ (by simp) 0 s).2.2.1

omit [Finite K] [CharP K 2] in
theorem xAB_inv (s : K) : (xAB s)⁻¹ = xAB (-s) :=
  ((root_matrix_data (r := 2) (K := K)).1 _ _ (by simp) 0 s).2.2.1

omit [CharP K 2] in
theorem eq_xC_of_spc0 (r : ↥(perfectCore (Q2 K 0))) (hr : blkN 0 r = 1) (h0 : spc0 r = 0) :
    (r : StatedSp 2 K) = xC (⟪r⟫ (Sum.inl 0) (Sum.inr 0)) := by
  obtain ⟨r00, r10, r20, r30, r21, r22, r23⟩ := sp0_entries r
  obtain ⟨r11, r13, r31, r33, r12, r32⟩ := sp0_rad r hr
  have ha : ⟪r⟫ (Sum.inl 0) (Sum.inl 1) = 0 := congrFun h0 0
  have hb : ⟪r⟫ (Sum.inl 0) (Sum.inr 1) = 0 := congrFun h0 1
  rw [ha, neg_zero] at r32
  rw [hb] at r12
  apply statedSp_ext
  change ⟪r⟫ = spMat (xC _)
  rw [spMat_xC]
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [r00, r10, r20, r30, r21, r22, r23, r11, r13, r31, r33, r12, r32, ha, hb]

omit [CharP K 2] in
theorem eq_xAB_of_spc1 (r : ↥(perfectCore (Q2 K 1))) (hr : blkN 1 r = 1) (h0 : spc1 r = 0) :
    (r : StatedSp 2 K) = xAB (⟪r⟫ (Sum.inl 0) (Sum.inr 1)) := by
  obtain ⟨hrm, hsym⟩ := sp1_rad r hr
  have h00 : ⟪r⟫ (Sum.inl 0) (Sum.inr 0) = 0 := congrFun h0 0
  have h11 : ⟪r⟫ (Sum.inl 1) (Sum.inr 1) = 0 := congrFun h0 1
  have hsym01 : ⟪r⟫ (Sum.inl 1) (Sum.inr 0) = ⟪r⟫ (Sum.inl 0) (Sum.inr 1) := by
    have := congrFun (congrFun hsym 0) 1
    simpa [Matrix.toBlocks₁₂, Matrix.transpose_apply] using this
  have he : ∀ p q, ⟪r⟫ p q = fromBlocks 1 ⟪r⟫.toBlocks₁₂ 0 1 p q := fun p q => by rw [← hrm]
  apply statedSp_ext
  change ⟪r⟫ = spMat (xAB _)
  rw [spMat_xAB]
  ext p q
  rw [he]
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [Matrix.toBlocks₁₂, h00, h11, hsym01]

variable (hK4 : ∃ s : Finset K, s.card = 4)
include hK4

theorem xC_mem_commutator (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (s : K) :
    xC s ∈ ⁅pCoreOf 2 (perfectCore (Q2 K 0)), perfectCore (Q2 K 0)⁆ := by
  set D := perfectCore (Q2 K 0) with hD
  have hOk := pCore_eq_ker hK4 (blkN 0) (blkN_surjective hK4 0) (blkN_ker_isPGroup hK 0)
  have hU := unipotent_le_perfectCore hK4 (0 : Fin 2)
  have hAO : ∀ t : K, xA t ∈ pCoreOf 2 D := by
    intro t
    refine ⟨⟨xA t, hU (xA_mem t)⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, hOk, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [blkN0_eq]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [spMat_xA]
  have h1 : ∀ t u : K, xAB (t * u) * xC (t ^ 2 * u) ∈ ⁅pCoreOf 2 D, D⁆ := fun t u => by
    rw [← comm_xA_xB]
    exact Subgroup.commutator_mem_commutator (hAO t) (hU (xB_mem u))
  obtain ⟨l, hl1⟩ := NQCat.exists_unit_ne_one hK4
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have h1l : (1 : K) - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
  set a := s / (1 - l) with ha
  have hg := Subgroup.mul_mem _ (Subgroup.inv_mem _ (h1 l (a / l))) (h1 1 a)
  have e1 : (l : K) * (a / l) = a := by field_simp
  have e2 : (l : K) ^ 2 * (a / l) = l * a := by field_simp
  rw [e1, e2, one_mul, one_pow, one_mul] at hg
  have e3 : (xAB a * xC (l * a))⁻¹ * (xAB a * xC a) = xC s := by
    have : (xAB a * xC (l * a))⁻¹ * (xAB a * xC a) = (xC (l * a))⁻¹ * xC a := by group
    rw [this, xC_inv, xC_mul]
    congr 1
    rw [ha]
    field_simp
    ring
  rw [e3] at hg
  exact hg

theorem xAB_mem_commutator (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (s : K) :
    xAB s ∈ ⁅pCoreOf 2 (perfectCore (Q2 K 1)), perfectCore (Q2 K 1)⁆ := by
  set D := perfectCore (Q2 K 1) with hD
  have hOk := pCore_eq_ker hK4 (blkN 1) (blkN_surjective hK4 1) (blkN_ker_isPGroup hK 1)
  have hU := unipotent_le_perfectCore hK4 (1 : Fin 2)
  have hBO : ∀ u : K, xB u ∈ pCoreOf 2 D := by
    intro u
    refine ⟨⟨xB u, hU (xB_mem u)⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, hOk, MonoidHom.mem_ker]
    apply Subtype.ext
    rw [blkN1_eq]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [spMat_xB, Matrix.toBlocks₁₁, Matrix.one_apply]
  have h1 : ∀ t u : K, xAB (t * u) * xC (t ^ 2 * u) ∈ ⁅pCoreOf 2 D, D⁆ := fun t u => by
    rw [← comm_xA_xB, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (hU (xA_mem t)) (hBO u)
  obtain ⟨l, hl1⟩ := NQCat.exists_unit_ne_one hK4
  have hl0 : (l : K) ≠ 0 := l.ne_zero
  have hl1' : (l : K) - 1 ≠ 0 := sub_ne_zero.mpr hl1
  set c := s * l / (l - 1) with hc
  have hg := Subgroup.mul_mem _ (h1 1 c) (Subgroup.inv_mem _ (h1 l (c / l ^ 2)))
  have e2 : (l : K) ^ 2 * (c / l ^ 2) = c := by field_simp
  rw [e2, one_mul, one_pow, one_mul] at hg
  have e3 : xAB c * xC c * (xAB (l * (c / l ^ 2)) * xC c)⁻¹ = xAB s := by
    have : xAB c * xC c * (xAB (l * (c / l ^ 2)) * xC c)⁻¹ =
        xAB c * (xAB (l * (c / l ^ 2)))⁻¹ := by group
    rw [this, xAB_inv, xAB_mul]
    congr 1
    rw [hc]
    field_simp
    ring
  rw [e3] at hg
  exact hg

theorem genComm_Q2 (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (j : Fin 2) :
    GenComm (perfectCore (Q2 K j)) := by
  fin_cases j
  · let τ := (CFSG.Quasithin.JonesParshall.invTransposeSL 2 K).toMonoidHom.comp (blkN 0)
    have hτ : ∀ r, τ r = 1 ↔ blkN 0 r = 1 := fun r => by
      simp only [τ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    have hker : IsPGroup 2 τ.ker := by
      rintro ⟨r, hr⟩
      obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK 0 ⟨r, (hτ r).1 hr⟩
      have h : r ^ 2 ^ k = 1 := (SubgroupClass.coe_pow _ _).symm.trans (congrArg Subtype.val hk)
      exact ⟨k, Subtype.ext ((SubgroupClass.coe_pow _ _).trans h)⟩
    refine genComm_of_coord hK4 τ
      ((CFSG.Quasithin.JonesParshall.invTransposeSL 2 K).surjective.comp (blkN_surjective hK4 0))
      hker spc0 (fun r s hr hs => spc0_mul r s ((hτ r).1 hr) ((hτ s).1 hs))
      (fun n r hr => by rw [sp0_conj n r ((hτ r).1 hr)]; rfl) fun r hr h0 => ?_
    rw [eq_xC_of_spc0 r ((hτ r).1 hr) h0]
    exact xC_mem_commutator hK4 hK _
  · let τ := (frobSL (F := K)).comp (blkN 1)
    have hτ : ∀ r, τ r = 1 ↔ blkN 1 r = 1 := fun r => by
      rw [MonoidHom.comp_apply]
      exact map_eq_one_iff _ frobSL_bijective.1
    have hker : IsPGroup 2 τ.ker := by
      rintro ⟨r, hr⟩
      obtain ⟨k, hk⟩ := blkN_ker_isPGroup hK 1 ⟨r, (hτ r).1 hr⟩
      have h : r ^ 2 ^ k = 1 := (SubgroupClass.coe_pow _ _).symm.trans (congrArg Subtype.val hk)
      exact ⟨k, Subtype.ext ((SubgroupClass.coe_pow _ _).trans h)⟩
    refine genComm_of_coord hK4 τ (frobSL_bijective.2.comp (blkN_surjective hK4 1)) hker spc1
      (fun r s hr hs => spc1_mul r s ((hτ r).1 hr) ((hτ s).1 hs))
      (fun n r hr => sp1_conj n r ((hτ r).1 hr)) fun r hr h0 => ?_
    rw [eq_xAB_of_spc1 r ((hτ r).1 hr) h0]
    exact xAB_mem_commutator hK4 hK _

end Sp4

theorem hasModelFacts_sp4 (f : ℕ) (hf : 2 ≤ f) : HasModelFacts (IsSp4Over f) := by
  intro Y _ hY
  have hX : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSp 2 2 f := by
    rcases hY with ⟨h, -⟩ | ⟨-, hL⟩
    · omega
    · rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      all_goals exact absurd h (by norm_num)
  have hfin : Finite Y := by
    obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hX
    exact Finite.of_equiv _ e.symm.toEquiv
  refine ⟨hfin, fun T hT => ?_⟩
  obtain ⟨K, _, _, _, φ, hcard, hφ, hres, -⟩ := even_rank_two_residual_symplectic hX hT
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hcard⟩
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨_, hres, fun j => ⟨?_, ?_⟩⟩
  · have hT' : T = (projUnipotent 2 K).map φ.symm.toMonoidHom := by
      rw [← hφ, Subgroup.map_map]
      have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Y := by
        ext
        simp
      rw [e, Subgroup.map_id]
    have h1 : projUnipotent 2 K ≤ perfectCore ((Q2 K j).map (proj 2 K)) := by
      rw [← map_perfectCore]
      exact Subgroup.map_mono (unipotent_le_perfectCore hK4 j)
    show T ≤ perfectCore (((Q2 K j).map (proj 2 K)).map φ.symm.toMonoidHom)
    rw [hT', ← map_perfectCore]
    exact Subgroup.map_mono h1
  · show GenComm (perfectCore (((Q2 K j).map (proj 2 K)).map φ.symm.toMonoidHom))
    rw [← map_perfectCore, genComm_map_iff φ.symm.injective, ← map_perfectCore,
      genComm_map_iff proj_injective_charTwo]
    exact genComm_Q2 hK4 hK j

end CFSG.Quasithin.H13.Ch9.F112Pf
