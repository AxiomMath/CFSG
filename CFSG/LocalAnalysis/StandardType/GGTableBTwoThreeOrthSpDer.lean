module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneAlt6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Sp4TwoRootSix
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.Monster.Existence.Defs
public import CFSG.Open.MonsterY443Defs
public import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore

public section

namespace CFSG.StandardType.TwoThreeOrth

open CFSG.Assembly.LowTwoRank CFSG.SeitzReduction.SymplecticPilot

variable {K : Type} [Field K] [Finite K]

theorem isQuasisimple_commutator_statedSp (hK : Nat.card K = 2) {k : ℕ} (hk : 2 ≤ k) :
    CFSG.IsQuasisimple (commutator (StatedSp k K)) := by
  rcases Nat.lt_or_ge k 3 with h | h
  · obtain rfl : k = 2 := by omega
    exact (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour
      (CFSG.SeitzReduction.F4Pilot.sp4EquivSympFour hK)).1
  · have hperf := CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp k K (Or.inr (Or.inr ⟨hK, h⟩))
    rw [hperf.commutator_eq_top]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm
      (CFSG.LieType.Universal.Symplectic.isQuasisimple k K (by omega) (Or.inr (Or.inr ⟨hK, h⟩)))

theorem center_ne_top_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    Subgroup.center Q ≠ ⊤ := by
  intro htop
  obtain ⟨-, -, a, b, hab⟩ := hQ
  apply hab
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      have hx : x ∈ Subgroup.center Q := htop ▸ Subgroup.mem_top x
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.mp hx y)]

theorem le_center_of_normal_of_card_le_two {G : Type*} [Group G] {C : Subgroup G} [C.Normal]
    [Finite C] (hC : Nat.card C ≤ 2) : C ≤ Subgroup.center G := by
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro g
  by_contra hne
  have hc1 : c ≠ 1 := by
    rintro rfl
    simp at hne
  have hgc : g * c * g⁻¹ ∈ C := Subgroup.Normal.conj_mem inferInstance c hc g
  have hgc1 : g * c * g⁻¹ ≠ 1 := by
    intro h
    apply hc1
    have : c = g⁻¹ * (g * c * g⁻¹) * g := by group
    rw [this, h]
    group
  have hgcc : g * c * g⁻¹ ≠ c := by
    intro h
    apply hne
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [h]
  set f : Fin 3 → C := ![1, ⟨c, hc⟩, ⟨g * c * g⁻¹, hgc⟩] with hf
  have hinj : Function.Injective f := by
    intro i j hij
    have hv := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [hf] at hv ⊢ <;>
      first
      | exact absurd hv.symm hc1
      | exact absurd hv hc1
      | exact absurd hv.symm hgc1
      | exact absurd hv hgc1
      | exact absurd hv hgcc
      | exact absurd hv.symm hgcc
  have := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_fin] at this
  omega

variable [CharP K 2]

theorem eq_one_of_commute_commutator_statedSp_two (hK : Nat.card K = 2) {y : StatedSp 2 K}
    (hy : ∀ j ∈ commutator (StatedSp 2 K), y * j = j * y) : y = 1 := by
  set e := CFSG.SeitzReduction.F4Pilot.sp4EquivSympFour (K := K) hK with he
  set D := commutator (StatedSp 2 K) with hD
  have hq : CFSG.IsQuasisimple D := (CFSG.RankThree.PartOne.derived_of_mulEquiv_sympFour e).1
  have hidx : D.index = 2 := (CFSG.RankThree.PartOne.derived_alt_index_of_mulEquiv_sympFour e).2
  have hsimp : IsSimpleGroup D := by
    have hmap : D.map e.toMonoidHom =
        commutator CFSG.ComponentClassification.PresentationLocal.sympFour := by
      rw [hD, _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
    have : IsSimpleGroup (commutator CFSG.ComponentClassification.PresentationLocal.sympFour) :=
      CFSG.ComponentClassification.PresentationLocal.isSimpleGroup_commutator_sympFour
    exact ((D.equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)).isSimpleGroup_congr.2 this
  have hZ : Subgroup.center D = ⊥ := by
    rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center D) with h | h
    · exact h
    · exact absurd h (center_ne_top_of_isQuasisimple hq)
  set C := Subgroup.centralizer (D : Set (StatedSp 2 K)) with hCdef
  have hyC : y ∈ C := Subgroup.mem_centralizer_iff.mpr fun j hj => (hy j hj).symm
  have hCD : ∀ z ∈ C, z ∈ D → z = 1 := by
    intro z hzC hzD
    have hzZ : (⟨z, hzD⟩ : D) ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro j
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC j j.2)
    rw [hZ, Subgroup.mem_bot] at hzZ
    exact congrArg Subtype.val hzZ
  have hCcard : Nat.card C ≤ 2 := by
    set φ : C →* StatedSp 2 K ⧸ D := (QuotientGroup.mk' D).comp C.subtype with hφ
    have hφinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have h1 : (z : StatedSp 2 K) ∈ D := (QuotientGroup.eq_one_iff _).mp hz
      exact Subtype.ext (hCD z z.2 h1)
    have h := Nat.card_le_card_of_injective φ hφinj
    rwa [← Subgroup.index, hidx] at h
  have hCZ := le_center_of_normal_of_card_le_two hCcard
  have hyZ := hCZ hyC
  rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hyZ
  exact hyZ

theorem eq_one_of_commute_commutator_statedSp (hK : Nat.card K = 2) {k : ℕ} (hk : 2 ≤ k)
    {y : StatedSp k K} (hy : ∀ j ∈ commutator (StatedSp k K), y * j = j * y) : y = 1 := by
  rcases Nat.lt_or_ge k 3 with h | h
  · obtain rfl : k = 2 := by omega
    exact eq_one_of_commute_commutator_statedSp_two hK hy
  · have hperf := CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp k K (Or.inr (Or.inr ⟨hK, h⟩))
    have hyZ : y ∈ Subgroup.center (StatedSp k K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (hy g (by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top g)).symm
    rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hyZ
    exact hyZ

section Transport

variable {G : Type*} [Group G] {k : ℕ} {D : Subgroup G}

omit [Finite K] [CharP K 2] in
theorem map_commutator_of_mulEquiv (e : StatedSp k K ≃* D) :
    (commutator (StatedSp k K)).map (D.subtype.comp e.toMonoidHom) = ⁅D, D⁆ := by
  have hr : (D.subtype.comp e.toMonoidHom).range = D := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hr]

omit [CharP K 2] in
theorem isQuasisimple_commutator_of_mulEquiv (hK : Nat.card K = 2) (hk : 2 ≤ k)
    (e : StatedSp k K ≃* D) : CFSG.IsQuasisimple (⁅D, D⁆ : Subgroup G) := by
  have hinj : Function.Injective (D.subtype.comp e.toMonoidHom) :=
    D.subtype_injective.comp e.injective
  rw [← map_commutator_of_mulEquiv e]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((commutator (StatedSp k K)).equivMapOfInjective _ hinj)
    (isQuasisimple_commutator_statedSp hK hk)

theorem eq_one_of_commute_commutator_of_mulEquiv (hK : Nat.card K = 2) (hk : 2 ≤ k)
    (e : StatedSp k K ≃* D) {y : G} (hyD : y ∈ D) (hy : ∀ j ∈ ⁅D, D⁆, y * j = j * y) :
    y = 1 := by
  have h1 : e.symm ⟨y, hyD⟩ = 1 := by
    refine eq_one_of_commute_commutator_statedSp hK hk fun j hj => ?_
    have hjD : ((e j : D) : G) ∈ ⁅D, D⁆ := by
      rw [← map_commutator_of_mulEquiv e]
      exact ⟨j, hj, rfl⟩
    have h2 := hy _ hjD
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply]
    exact h2
  have h3 : (⟨y, hyD⟩ : D) = 1 := by
    rw [← e.apply_symm_apply ⟨y, hyD⟩, h1, map_one]
  exact congrArg Subtype.val h3

end Transport

end CFSG.StandardType.TwoThreeOrth
