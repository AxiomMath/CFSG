module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLinearCore
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Steinberg.PartBAssembly
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification

namespace LayerCC

theorem charP_two_of_natCard {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

theorem not_two_dvd_card_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hG : IsPGroup p G) : ¬ 2 ∣ Nat.card G := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
  rw [hk]
  intro h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h2)).symm

end LayerCC

open LayerCC in
theorem ggPSections_sl_two
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : GGPSections p (SpecialLinearGroup (Fin 2) K) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.SectionRank.EvenCover.sl2_existsUnique_section (p := 2) hη hker
    (not_two_dvd_card_of_isPGroup hp hp2 hpk)).exists

open LayerCC in
theorem ggPSections_sl_succ
    {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (SpecialLinearGroup (Fin (m + 1)) K) := by
  intro E _ _ η hη hker hpk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := not_two_dvd_card_of_isPGroup hp hp2 hpk
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).isFiniteType
    (Dv := (CFSG.LieType.Universal.SpecialLinear.rootDatum m K).divisible) rfl
  have hE := CFSG.LieType.Steinberg.SL.chevalleyExtras (F := K) hm O
    CFSG.LieType.Steinberg.SL.commC (CFSG.LieType.Steinberg.SL.commutatorFormula O)
  exact (CFSG.LieType.Steinberg.existsUnique_section_of_sl2_lift
    (CFSG.LieType.Universal.SpecialLinear.isCTGroupDatum m K)
    (CFSG.LieType.Universal.SpecialLinear.steinbergExtras m K) hE.param hE.rankOne hη hker hC
    fun ρ => by
      obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hη hker hC ρ
      exact ⟨ρ', fun g => congrArg (· g) hρ'⟩).exists

theorem ggPSections_sl
    {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGPSections p (SpecialLinearGroup (Fin d) K) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rcases Nat.lt_or_ge m 2 with hm | hm
  · obtain rfl : m = 1 := by omega
    exact ggPSections_sl_two hp hp2
  · exact ggPSections_sl_succ hm hp hp2

open LayerCC in
theorem ggLayerCenterCyclic_projectiveSL {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hperf : commutator (SpecialLinearGroup (Fin d) K) = ⊤)
    (hsec : GGPSections p (SpecialLinearGroup (Fin d) K)) :
    GGLayerCenterCyclic p (projectiveSL d K) (Set.range (conjAut d K)) := by
  refine ggLayerCenterCyclic_of_model hp (proj d K) (proj_surjective d K)
    (by rw [ker_proj]; exact scalars_le_center d K) hperf hsec ?_
  rintro _ ⟨B, rfl⟩
  exact ⟨CatalogueBHigherLinearAction.slConjugation d K B, fun h => (conjAut_proj B h).symm,
    ggModelLayerCyclic_slConjugation hp hp2 B⟩

open LayerCC in
theorem ggLayerCenterCyclic_recipeLinear {d : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hperf : commutator (SpecialLinearGroup (Fin d) K) = ⊤)
    (hsec : GGPSections p (SpecialLinearGroup (Fin d) K)) :
    GGLayerCenterCyclic p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) :=
  ggLayerCenterCyclic_of_mulEquiv (TypeA.recipeEquiv d K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (ggLayerCenterCyclic_projectiveSL hp hp2 hperf hsec)

open LayerCC in
theorem recipeLinear_layerCenterCyclic
    {d f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 2 ≤ d)
    (hd2 : d = 2 → 2 ≤ f) {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d (2 ^ f) Q) :
    LargeEvenRecipeLinear d (2 ^ f) fun R _ I F => Q R I F ∧
      LargeEvenSimpleGuard (fun R _ I _ => GGLayerCenterCyclic p R I) R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_natCard hK
  have hperf : commutator (SpecialLinearGroup (Fin d) K) = ⊤ := by
    refine (CFSG.LinearGroups.special_linear_isPerfect hd ?_).commutator_eq_top
    rcases Nat.lt_or_ge d 3 with h3 | h3
    · right
      have hf := hd2 (by omega)
      have : Fintype K := Fintype.ofFinite K
      have h4 : 4 ≤ (Finset.univ : Finset K).card := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq h4
      exact ⟨s, hs⟩
    · exact Or.inl h3
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun _ _ =>
    ggLayerCenterCyclic_recipeLinear hp hp2 hperf (ggPSections_sl hd hp hp2)⟩

@[expose] def GGLayerLinearLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2)

theorem largeEvenLabelAll_layerCenterCyclic_linear
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGLayerLinearLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hlab⟩ := hlab
  intro Q hQ
  rcases h with h | ⟨h, hl⟩ | ⟨h, hl⟩
  · dsimp only at h
    subst h
    obtain ⟨hl1, hl2⟩ := hlab
    exact recipeLinear_layerCenterCyclic hp hp2 (by omega)
      (fun h2 => hl2 (by omega)) hQ
  · dsimp only at h hl
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [ite_true] at hQ ⊢
    exact recipeLinear_layerCenterCyclic hp hp2 (by omega) (by omega) hQ
  · dsimp only at h hl
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [ite_true] at hQ ⊢
    rw [← pow_mul] at hQ ⊢
    exact recipeLinear_layerCenterCyclic hp hp2 (le_refl 2)
      (fun _ => by dsimp only at hn; omega) hQ

end CFSG.StandardType

end
