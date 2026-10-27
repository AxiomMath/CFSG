module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2UnitStatements
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGTableBLinear
import CFSG.LocalAnalysis.StandardType.GGQ2UnitFrameExists

public section

namespace CFSG.StandardType.GGQ2Frame.OrthPlacement

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Open (IsElemAbelian)

private theorem osr_three_pow_lt_of_dvd {X : Type*} [Group X] [Finite X] {N : ℕ}
    (hX : IsPGroup 3 X) (hdiv : Nat.card X ∣ N) (hN : N = 20160 ∨ N = 180) :
    Nat.card X < 3 ^ 4 := by
  obtain ⟨n, hn⟩ := (@IsPGroup.iff_card 3 X _ ⟨Nat.prime_three⟩ _).mp hX
  have hnot : ¬ 3 ^ 4 ∣ N := by
    rintro h
    rcases hN with rfl | rfl <;> norm_num at h
  have hn3 : n ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ n := by omega
    exact hnot ((pow_dvd_pow 3 h4).trans (hn ▸ hdiv))
  rw [hn]
  calc 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    _ < 3 ^ 4 := by norm_num

private theorem osr_card_GL_eq {K : Type} [Field K] {d : ℕ} (hF : Fintype K)
    (hcase : (d = 4 ∧ Nat.card K = 2) ∨ (d = 2 ∧ Nat.card K = 4)) :
    Nat.card (GL (Fin d) K) = 20160 ∨ Nat.card (GL (Fin d) K) = 180 := by
  rcases hcase with ⟨rfl, hK2⟩ | ⟨rfl, hK4⟩
  · left
    have h2 : @Fintype.card K hF = 2 := by
      rw [← @Nat.card_eq_fintype_card K hF]
      exact hK2
    rw [@Matrix.card_GL_field K _ hF, h2]
    norm_num [Fin.prod_univ_four]
  · right
    have h4 : @Fintype.card K hF = 4 := by
      rw [← @Nat.card_eq_fintype_card K hF]
      exact hK4
    rw [@Matrix.card_GL_field K _ hF, h4]
    norm_num [Fin.prod_univ_two]

theorem card_lt_three_pow_four_of_linearRecipe {G : Type} [Group G] [Finite G]
    {H E : Subgroup G} {K : Type} [Field K] [Finite K] {d : ℕ}
    (hcase : (d = 4 ∧ Nat.card K = 2) ∨ (d = 2 ∧ Nat.card K = 4))
    (hperf : commutator H = ⊤) (hE : IsElemAbelian 3 E)
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (hbot : E ⊓ Subgroup.centralizer (H : Set G) = ⊥)
    {θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)}
    (hInd : ∀ b ∈ E, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    Nat.card E < 3 ^ 4 := by
  classical
  let κ : GL (Fin d) K →* MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    TableB.linConjAut (Fin d) K
  let g : ↥E →* MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    (ggLAut H θ).comp (Subgroup.inclusion hEN)
  have hker : g.ker = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    change ggLAut H θ ⟨(b : G), hEN b.2⟩ = 1 at hb
    have hcent : (b : G) ∈ Subgroup.centralizer (H : Set G) :=
      mem_centralizer_of_ggLAut_eq_one H θ hperf hb
    have hmem : (b : G) ∈ E ⊓ Subgroup.centralizer (H : Set G) := ⟨b.2, hcent⟩
    rw [hbot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hcard : Nat.card ↥E = Nat.card g.range := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hker] at h
    simpa using h.symm
  have hle : g.range ≤ κ.range := by
    rintro _ ⟨b, rfl⟩
    have hmem : ggLAut H θ ⟨(b : G), hEN b.2⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ :=
      ggLAut_mem_of_induces H θ hEN hInd b.2
    obtain ⟨A, hA⟩ := TableB.exists_eq_linConjAut hmem
    exact ⟨A, hA.symm⟩
  have hdiv : Nat.card E ∣ Nat.card (GL (Fin d) K) := by
    have h1 : Nat.card ↥E ∣ Nat.card ↥κ.range := by
      rw [hcard]
      exact Subgroup.card_dvd_of_le hle
    exact h1.trans (Subgroup.card_range_dvd κ)
  exact osr_three_pow_lt_of_dvd hE.isPGroup hdiv (osr_card_GL_eq (Fintype.ofFinite K) hcase)

private theorem osr_centralizer_inf_eq_bot {G : Type} [Group G] {H E : Subgroup G}
    (hE : IsElemAbelian 3 E)
    (hC : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) :
    E ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxC : x ∈ Subgroup.centralizer (H : Set G) := hx.2
  have hx3 : x ^ 3 = 1 := hE.2 x hx.1
  have hcop : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer (H : Set G))) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr hC
  have hdvdC : orderOf x ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) :=
    Subgroup.orderOf_dvd_natCard _ hxC
  have hdvd3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hord1 : orderOf x = 1 :=
    (Nat.coprime_comm.mp (hcop.coprime_dvd_right hdvdC)).eq_one_of_dvd hdvd3
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hord1)

private theorem osr_le_of_inLambda2_D {r : ℕ}
    (h : LargeEvenInLambda2 (⟨.D, r, 1⟩ : LargeEvenLabel)) : 3 ≤ r := by
  simpa [LargeEvenInLambda2] using h.2

private theorem osr_le_of_inLambda2_twD {r : ℕ}
    (h : LargeEvenInLambda2 (⟨.twD, r, 1⟩ : LargeEvenLabel)) : 2 ≤ r := by
  simpa [LargeEvenInLambda2] using h.2

theorem orthSmallRankVacuous_of_existsUnitFrame (hU : UnitPlacement.ExistsUnitFrame) :
    OrthSmallRankVacuous := by
  intro G _ _ H E t δ hInn hts hE _hSC hC
  obtain ⟨hperf, lab, hlab, hraw⟩ := hInn
  obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hS, _, _⟩ := hQ
  change lab = planeAmbientLabel (.orthogonal δ) t at hS
  subst lab
  have hbot := osr_centralizer_inf_eq_bot hE hC
  by_cases ht : Even t
  · have hlab' := hlab
    simp only [planeAmbientLabel, if_pos ht] at hlab'
    have hrank : t + δ.val = 3 := by
      have h3 := osr_le_of_inLambda2_D hlab'
      omega
    have hraw' := hraw
    simp only [planeAmbientLabel, if_pos ht] at hraw'
    simp only [LargeEvenRawDatumLegacy, if_pos hrank] at hraw'
    obtain ⟨K, _, _, hK, hQK⟩ := hraw'
    obtain ⟨_, _, θ, _, hEN, hInd⟩ := hQK
    have hK2 : Nat.card K = 2 := by
      norm_num at hK
      exact hK
    exact card_lt_three_pow_four_of_linearRecipe (Or.inl ⟨rfl, hK2⟩) hperf hE hEN hbot hInd
  · have hlab' := hlab
    simp only [planeAmbientLabel, if_neg ht] at hlab'
    have hraw' := hraw
    simp only [planeAmbientLabel, if_neg ht] at hraw'
    by_cases h2 : t + δ.val = 2
    · simp only [LargeEvenRawDatumLegacy, if_pos h2] at hraw'
      obtain ⟨K, _, _, hK, hQK⟩ := hraw'
      obtain ⟨_, _, θ, _, hEN, hInd⟩ := hQK
      have hK4 : Nat.card K = 4 := by
        norm_num at hK
        exact hK
      exact card_lt_three_pow_four_of_linearRecipe (Or.inr ⟨rfl, hK4⟩) hperf hE hEN hbot hInd
    · have h3 : t + δ.val = 3 := by
        have h2' := osr_le_of_inLambda2_twD hlab'
        omega
      simp only [LargeEvenRawDatumLegacy, if_neg h2, if_pos h3] at hraw'
      obtain ⟨K, _, _, hK, hQK⟩ := hraw'
      obtain ⟨_, _, θ, _, hEN, hInd⟩ := hQK
      have hK4 : Nat.card K = 4 := by
        norm_num at hK
        exact hK
      have hI4 : ∀ (b : G) (hb : b ∈ E),
          ggLAut H θ ⟨b, hEN hb⟩ ∈
            LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K 2))
              (LargeEvenGUSet (Fin 4) K (2 ^ 1)) := by
        intro b hb
        exact ggLAut_mem_of_induces H θ hEN hInd hb
      by_contra hge
      rw [not_lt] at hge
      have hN3 : 3 ∣ 4 → 3 ^ (4 - 3) ≤ Nat.card E := fun h => absurd h (by norm_num)
      obtain ⟨ζ, _, h5, _⟩ := hU (N := 4) θ hK4 (by norm_num) hperf hE hEN hI4 hC hge hN3
      omega

theorem orthSmallRankVacuous_holds : OrthSmallRankVacuous :=
  orthSmallRankVacuous_of_existsUnitFrame UnitPlacement.existsUnitFrame_holds

end CFSG.StandardType.GGQ2Frame.OrthPlacement
