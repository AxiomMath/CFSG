module

public import CFSG.Quasithin.H13.NQCatA314LieGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem lieP_f4
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (f : ℕ)
    (hf : 3 ≤ f) (hL : Is2F4 f ↥L) (hP : IsMaxParabolic2 L P) :
    LieP False (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine lieP_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hL
  subst hfa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  have hUsyl : IsSylowTwoOf (F4.reeFixedPosUnipotent K a) (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU₀ := isSylowTwoOf_subgroupOf_top hUsyl
  have hUp : IsPGroup 2 ↥(F4.reeFixedPosUnipotent K a) := hUsyl.2.1
  have hcases : ∀ i : Fin F4.fixedOrbitCount, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
    intro i
    rcases i with ⟨i, hi⟩
    have hi2 : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨⟨h0eq, -, -⟩, ⟨h1eq, -, -⟩⟩ :=
    large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hq8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine lieP_perfectCore_of_equiv e ?_
  refine lieP_perfectCore_parabolic hU₀ (large_Ree_residualOvergroupsAt hK) (fun j => ?_)
    (isParabolic2_top_map_equiv e hpa) (CFSG.QuasithinUnique.A5.G3.map_ne_top_of_equiv e hna)
  rcases hcases (f4Index j) with hj | hj
  ·
    have := (isSimpleGroup_rankOneGroupOne ha hK).1
    obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupOne K a) (by rw [hj]; exact h0eq) (isSimpleGroup_rankOneGroupOne ha hK).2
    refine lieP_of_hom (isSimpleGroup_rankOneGroupOne ha hK).2 g hg hk fun _ h60 => ?_
    exfalso
    rw [← Nat.card_congr (rankOneEquivSL K a hK).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK] at h60
    have h1 : 63 ≤ (2 ^ (2 * a + 1)) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
      omega
    have : 8 * 63 ≤ 2 ^ (2 * a + 1) * ((2 ^ (2 * a + 1)) ^ 2 - 1) := Nat.mul_le_mul hq8 h1
    omega
  ·
    have := (isSimpleGroup_rankOneGroupTwo ha hK).1
    obtain ⟨g, hg, hk⟩ := ree_levi_hom (K := K) (a := a) hUp (f4Index j)
      (M := rankOneGroupTwo K a) (by rw [hj]; exact h1eq) (isSimpleGroup_rankOneGroupTwo ha hK).2
    refine lieP_of_hom (isSimpleGroup_rankOneGroupTwo ha hK).2 g hg hk fun _ h60 => ?_
    exfalso
    rw [Nat.card_congr (rankOneEquivSuzuki K a ha hK).toEquiv,
      CFSG.LieType.Ree.suzuki_order hK] at h60
    have h1 : 64 ≤ (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
    have h2 : 1 ≤ 2 ^ (2 * a + 1) - 1 := by omega
    have h3 : 1 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := by omega
    have : 64 * 1 * 1 ≤ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
        ((2 ^ (2 * a + 1)) ^ 2 + 1) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    omega

theorem lieP_tits
    {G : Type} [Group G] [Finite G] (L P : Subgroup G) (hL : IsTits ↥L)
    (hP : IsMaxParabolic2 L P) : LieP False (perfectCore P) := by
  obtain ⟨hpar, hne, -⟩ := hP
  refine lieP_perfectCore_of_subgroupOf hpar hne fun Pa hpa hna => ?_
  obtain ⟨-, S₁, hS₁, hN⟩ := hpa
  have hS₁P : S₁ ≤ Pa := fun x hx => hN ⟨Subgroup.mem_top x, Subgroup.le_normalizer hx⟩
  obtain ⟨H, N, -, -, -, -, -, hlat, hHs, hNs⟩ := titsSylowOvergroupLattice ↥L hL S₁ hS₁
  have hs : Group.IsSolvable ↥Pa := by
    rcases hlat Pa hS₁P with rfl | rfl | rfl | rfl
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := hS₁.2.1.isNilpotent
      infer_instance
    · exact hHs
    · exact hNs
    · exact absurd rfl hna
  rw [(isSolvable_iff_perfectCore_eq_bot Pa).mp hs]
  exact lieP_bot _

end CFSG.Quasithin.H13.NQCat.A314D
