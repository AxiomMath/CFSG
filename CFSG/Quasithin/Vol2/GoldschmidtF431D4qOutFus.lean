module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocCenter
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructSyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocRep

public section

namespace CFSG.Quasithin.H13.F431.D4q.OutAsm

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem exists_conj_Pst1_Vr {a b c d e f : K} (ha0 : a ≠ 0) (hb : σ b = b)
    (hu2 : d4x₁ K σ a * d4v K σ b c d e f * (d4x₁ K σ a * d4v K σ b c d e f) = 1) :
    ∃ g : ModGL TwistTag.D4.tag K, g ∈ d4C K σ ∧
      g ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom
        {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} ∧
      ∃ D E F : K, g * (d4x₁ K σ a * d4v K σ b c d e f) * g⁻¹ = d4v K σ 0 a D E F := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : d4x₁ K σ a * d4v K σ b c d e f * (d4x₁ K σ a * d4v K σ b c d e f) =
      d4x₁ K σ a * d4v K σ b c d e f * (d4x₁ K σ a)⁻¹ * d4v K σ b c d e f := by
    rw [d4x₁_inv]
    group
  obtain ⟨F₀, hF₀⟩ := d4x₁_conj_d4v σ hσ a b c d e f hb
  rw [hsq, hF₀, d4v_mul σ hσ, ← d4v_zero σ] at hu2
  obtain ⟨-, hc', hd', -, -⟩ := d4v_injective σ hu2
  have hb0 : b = 0 := by
    have h : b * a = 0 := by linear_combination hc' - c * h2
    exact (mul_eq_zero.1 h).resolve_right ha0
  subst hb0
  have hac : σ a * σ (σ c) + σ (σ a) * σ c = 0 := by
    simp only [zero_mul, add_zero] at hd'
    linear_combination hd' - d * h2
  obtain ⟨l, hl⟩ : ∃ l : K, l = c * a⁻¹ := ⟨_, rfl⟩
  have hca : c = l * a := by rw [hl, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  have hσa : σ a ≠ 0 := (map_ne_zero σ).2 ha0
  have hσσa : σ (σ a) ≠ 0 := (map_ne_zero σ).2 hσa
  have hlσ : σ l = l := by
    rw [hca] at hac
    simp only [map_mul] at hac
    have h3 : σ a * σ (σ a) * (σ (σ l) + σ l) = 0 := by linear_combination hac
    have h4 : σ (σ l) + σ l = 0 := (mul_eq_zero.1 h3).resolve_left (mul_ne_zero hσa hσσa)
    have h5 : σ (σ l) = σ l := by linear_combination h4 - σ l * h2
    exact σ.injective h5
  obtain ⟨F₁, hF₁⟩ := comm_d4x₁_d4x₂_eq_d4v σ hσ a hlσ
  have hx₂ : d4x₂ K l * (d4x₁ K σ a * d4v K σ 0 c d e f) * (d4x₂ K l)⁻¹ =
      d4x₁ K σ a * (⁅d4x₁ K σ a, d4x₂ K l⁆ *
        (d4x₂ K l * d4v K σ 0 c d e f * (d4x₂ K l)⁻¹)) := by
    have h1 : d4x₁ K σ a * d4x₁ K σ a = 1 := d4x₁_mul_self σ a
    simp only [commutatorElement_def]
    rw [d4x₁_inv]
    calc d4x₂ K l * (d4x₁ K σ a * d4v K σ 0 c d e f) * (d4x₂ K l)⁻¹ =
        (d4x₁ K σ a * d4x₁ K σ a) * d4x₂ K l * d4x₁ K σ a * (d4x₂ K l)⁻¹ *
          (d4x₂ K l * d4v K σ 0 c d e f * (d4x₂ K l)⁻¹) := by rw [h1]; group
      _ = _ := by group
  rw [hF₁, d4x₂_conj_d4v σ hσ l 0 c d e f, d4v_mul σ hσ] at hx₂
  have hc0 : 0 + 0 = (0 : K) ∧ l * a + c = 0 := by
    refine ⟨add_zero 0, ?_⟩
    rw [hca]
    linear_combination (l * a) * h2
  rw [hc0.1, hc0.2] at hx₂
  have hna : ∀ D' E' G : K, trialityMiddleRep K * (d4x₁ K σ a * d4v K σ 0 0 D' E' G) *
      (trialityMiddleRep K)⁻¹ = d4v K σ 0 a D' G E' := by
    intro D' E' G
    rw [← MulAut.conj_apply, map_mul, MulAut.conj_apply, MulAut.conj_apply,
      trialityMiddleRep_conj_d4x₁, trialityMiddleRep_conj_d4v σ hσ, d4x₃_eq_d4v σ, d4v_mul σ hσ]
    refine d4v_congr σ (by ring) (by ring) (by ring) (by ring) ?_
    simp only [mul_zero, map_zero, add_zero, zero_add]
  have hn : trialityMiddleRep K ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨⟨1, by decide⟩, rfl, rfl⟩)
  have hx₂U : d4x₂ K l ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [d4x₂_eq_d4v σ l]
    exact Loc.d4v_mem_graphFixedPosUnipotent σ hσ hlσ (map_zero σ) (map_zero σ)
  have hx₂P : d4x₂ K l ∈ graphFixedParabolic TwistTag.D4 K σ.toRingHom
      {(⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} :=
    graphFixedRootBorel_le_graphFixedParabolic _ _ _ _
      (graphFixedPosUnipotent_le_graphFixedRootBorel hx₂U)
  have hconj : trialityMiddleRep K * d4x₂ K l * (d4x₁ K σ a * d4v K σ 0 c d e f) *
      (trialityMiddleRep K * d4x₂ K l)⁻¹ = trialityMiddleRep K *
      (d4x₂ K l * (d4x₁ K σ a * d4v K σ 0 c d e f) * (d4x₂ K l)⁻¹) *
      (trialityMiddleRep K)⁻¹ := by group
  rw [hx₂] at hconj
  exact ⟨trialityMiddleRep K * d4x₂ K l,
    mul_mem (trialityRep_mem σ).2 (d4x_long_mem σ hlσ).1, mul_mem hn hx₂P, _, _, _,
    hconj.trans (hna _ _ _)⟩

end Conj

section Cm

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def VrC : Subgroup (Cm σ) :=
  (d4Vr K σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)

theorem mem_VrC {x : Cm σ} : x ∈ VrC σ ↔ (x : ModGL TwistTag.D4.tag K) ∈ d4Vr K σ := Iff.rfl

include hσ in
theorem exists_mem_Pst1_conj_VrC {u : Cm σ} (hu : u ∈ Ust σ) (hu2 : u * u = 1)
    (hnV : u ∉ VrC σ) : ∃ g ∈ Pst1 σ, g * u * g⁻¹ ∈ VrC σ := by
  have hσ3 := toRingHom_pow_three_d4 σ hσ
  obtain ⟨a, b, c, d, e, f, hb, he, hf, hu'⟩ :=
    exists_d4coord σ hσ3 (Subgroup.mem_subgroupOf.mp hu)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hnV
    rw [mem_VrC, hu', d4x₁_zero, one_mul]
    exact d4v_mem_d4Vr σ hσ3 hb he hf
  have hu2' : d4x₁ K σ a * d4v K σ b c d e f * (d4x₁ K σ a * d4v K σ b c d e f) = 1 := by
    have := congrArg (fun y : Cm σ => (y : ModGL TwistTag.D4.tag K)) hu2
    simpa [Subgroup.coe_mul, hu'] using this
  obtain ⟨g, hgC, hgP, D, E, F, hg⟩ := exists_conj_Pst1_Vr σ hσ ha0 hb hu2'
  refine ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.mpr hgP, ?_⟩
  have hv : ((⟨g, hgC⟩ * u * ⟨g, hgC⟩⁻¹ : Cm σ) : ModGL TwistTag.D4.tag K) =
      d4v K σ 0 a D E F := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu']
    exact hg
  have hmem : d4v K σ 0 a D E F ∈ d4C K σ := hv ▸ (⟨g, hgC⟩ * u * ⟨g, hgC⟩⁻¹ : Cm σ).2
  obtain ⟨-, hE, hF⟩ := fixed_coords_of_mem_d4C σ hσ hmem
  rw [mem_VrC, hv]
  exact d4v_mem_d4Vr σ hσ3 (map_zero σ) hE hF

end Cm

section KLevel

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c) (Kb : Subgroup (MulAut (Cm σ)))
  (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

open Classical in
@[expose] noncomputable def invSet : Finset ↥Kb :=
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  ((Set.toFinite {y : Cm σ | y ∈ VrC σ ∧ y * y = 1 ∧ y ≠ 1}).toFinset).image (Loc.conjK σ Kb hinn)

theorem mem_invSet {i : ↥Kb} :
    i ∈ invSet σ Kb hinn ↔ ∃ y ∈ VrC σ, y * y = 1 ∧ y ≠ 1 ∧ Loc.conjK σ Kb hinn y = i := by
  classical
  simp only [invSet, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨y, h1, h2, h3, rfl⟩
  · rintro ⟨y, h1, h2, h3, rfl⟩
    exact ⟨y, ⟨h1, h2, h3⟩, rfl⟩

include hσ in
theorem fusion_Kb {x : ↥Kb} (hx : x ∈ (Tsub σ ⊥).subgroupOf Kb) (hx2 : orderOf x = 2) :
    ∃ i ∈ invSet σ Kb hinn, (∃ m ∈ Loc.MbSt σ Kb (Pst0 σ), m * x * m⁻¹ = i) ∨
      (∃ m ∈ Loc.MbSt σ Kb (Pst1 σ), m * x * m⁻¹ = i) := by
  obtain ⟨u, hu, δ, hδ, hα⟩ := (mem_Tsub_iff σ ⊥ _).1 (Subgroup.mem_subgroupOf.1 hx)
  rw [Subgroup.mem_bot.1 hδ, fieldActor_one, mul_one] at hα
  have hxe : x = Loc.conjK σ Kb hinn u := Subtype.ext hα
  have hxx : x * x = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.1 (hx2 ▸ dvd_rfl)
  have hu2 : u * u = 1 :=
    Loc.conjK_injective σ Kb hinn (by rw [map_mul, map_one, ← hxe]; exact hxx)
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [map_one] at hxe
    rw [hxe, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  by_cases hV : u ∈ VrC σ
  · exact ⟨x, (mem_invSet σ Kb hinn).2 ⟨u, hV, hu2, hu1, hxe.symm⟩, Or.inl ⟨1, one_mem _, by simp⟩⟩
  · obtain ⟨g, hg, hgV⟩ := exists_mem_Pst1_conj_VrC σ hσ hu hu2 hV
    have hi2 : g * u * g⁻¹ * (g * u * g⁻¹) = 1 := by
      calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    have hi1 : g * u * g⁻¹ ≠ 1 := fun h => hu1 (by
      have : u = g⁻¹ * (g * u * g⁻¹) * g := by group
      rw [this, h]; group)
    refine ⟨Loc.conjK σ Kb hinn (g * u * g⁻¹),
      (mem_invSet σ Kb hinn).2 ⟨_, hgV, hi2, hi1, rfl⟩, Or.inr ⟨Loc.conjK σ Kb hinn g,
        (Loc.mem_MbSt σ).2 (Loc.conj_mem_autStab_of_mem hg), ?_⟩⟩
    rw [hxe, ← map_inv, ← map_mul, ← map_mul]

end KLevel

end CFSG.Quasithin.H13.F431.D4q.OutAsm
