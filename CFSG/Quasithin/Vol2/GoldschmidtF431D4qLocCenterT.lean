module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocStd

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


section Root

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def x1S (s : K) : Cm σ :=
  ⟨d4x₁ K σ s, (d4x_short_mem σ (toRingHom_pow_three_d4 σ hσ) s).1⟩

theorem coe_x1S (s : K) : ((x1S σ hσ s : Cm σ) : ModGL TwistTag.D4.tag K) = d4x₁ K σ s := rfl

include hσ in
theorem x1S_mem_Ust (s : K) : x1S σ hσ s ∈ Ust σ := by
  have hs : s ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ := by
    rw [orbitField_D4_zero_eq_top σ hσ]
    trivial
  have h := orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom ⟨0, by decide⟩ ⟨s, hs⟩
  rw [coe_orbitX_zero_d4] at h
  exact Subgroup.mem_subgroupOf.2 h

theorem entry_pinnedX (δ : K ≃+* K) (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom δ.toRingHom) (pinnedX TwistTag.D4.tag K α c) =
      pinnedX TwistTag.D4.tag K α (δ c) :=
  Units.ext (entrywise_pinnedX δ.toRingHom α c)

theorem entry_d4x₁ (δ : K ≃+* K) (s : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4x₁ K σ s) = d4x₁ K σ (δ s) := by
  rw [d4x₁, d4x₁, coe_trialityOrbitProd, coe_trialityOrbitProd, map_mul, map_mul, entry_pinnedX,
    entry_pinnedX, entry_pinnedX]
  have h1 : δ (σ s) = σ (δ s) := ringEquiv_comm_of_finite σ δ s
  have h2 : δ (σ (σ s)) = σ (σ (δ s)) := by rw [ringEquiv_comm_of_finite σ δ, h1]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h1, h2]

theorem fieldActor_x1S (δ : K ≃+* K) (s : K) :
    fieldActor σ δ (x1S σ hσ s) = x1S σ hσ (δ s) :=
  Subtype.ext (by rw [coe_fieldActor]; exact entry_d4x₁ σ δ s)

include hσ in
theorem eq_zero_of_d4x₁_mem_Vr {t : K} (ht : d4x₁ K σ t ∈ d4Vr K σ) : t = 0 := by
  obtain ⟨b, c, d, e, f, -, -, -, h⟩ := exists_d4v σ (toRingHom_pow_three_d4 σ hσ) ht
  have h' : d4x₁ K σ t * d4v K σ 0 0 0 0 0 = d4x₁ K σ 0 * d4v K σ b c d e f := by
    rw [d4v_zero σ, d4x₁_zero, one_mul, mul_one, h]
  exact (d4coord_injective σ h').1

include hσ in
theorem Ust_conj_Vr {g v : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) (hv : v ∈ d4Vr K σ) :
    g * v * g⁻¹ ∈ d4Vr K σ := by
  have hvU : v ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    graphFixedSimpleComplement_le _ hv
  have h := (graphFixedSimpleComplement_subgroupOf_normal (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) ⟨0, by decide⟩).conj_mem ⟨v, hvU⟩ (Subgroup.mem_subgroupOf.2 hv) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.1 h

include hσ in
theorem conj_x1S_mem {u : Cm σ} (hu : u ∈ Ust σ) (s : K) :
    ∃ y ∈ d4Vr K σ,
      ((u⁻¹ * x1S σ hσ s * u : Cm σ) : ModGL TwistTag.D4.tag K) = d4x₁ K σ s * y := by
  obtain ⟨a, b, c, d, e, f, hb, he, hf, hu'⟩ :=
    exists_d4coord σ (toRingHom_pow_three_d4 σ hσ) (Subgroup.mem_subgroupOf.mp hu)
  have hvV : d4v K σ b c d e f ∈ d4Vr K σ :=
    d4v_mem_d4Vr σ (toRingHom_pow_three_d4 σ hσ) hb he hf
  have hcomm : d4x₁ K σ a * d4x₁ K σ s * d4x₁ K σ a = d4x₁ K σ s := by
    rw [← d4x₁_add, ← d4x₁_add, add_assoc, add_comm s a, ← add_assoc, add_comm a a,
      add_self_d4, zero_add]
  have h1 : ((u⁻¹ * x1S σ hσ s * u : Cm σ) : ModGL TwistTag.D4.tag K) =
      (d4v K σ b c d e f)⁻¹ * d4x₁ K σ s * d4v K σ b c d e f := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hu', mul_inv_rev, d4x₁_inv σ a,
      coe_x1S]
    calc (d4v K σ b c d e f)⁻¹ * d4x₁ K σ a * d4x₁ K σ s * (d4x₁ K σ a * d4v K σ b c d e f)
        = (d4v K σ b c d e f)⁻¹ * (d4x₁ K σ a * d4x₁ K σ s * d4x₁ K σ a) * d4v K σ b c d e f := by
          group
      _ = _ := by rw [hcomm]
  refine ⟨(d4x₁ K σ s)⁻¹ * (d4v K σ b c d e f)⁻¹ * d4x₁ K σ s * d4v K σ b c d e f, ?_, ?_⟩
  · have hU1 : (d4x₁ K σ s)⁻¹ ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
      inv_mem (Subgroup.mem_subgroupOf.mp (x1S_mem_Ust σ hσ s))
    have h2 := Ust_conj_Vr σ hσ hU1 (inv_mem hvV)
    rw [inv_inv] at h2
    exact mul_mem h2 hvV
  · rw [h1]
    group

end Root

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  (Kb : Subgroup (MulAut (Cm σ))) (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)

include hσ hf hK hσq hinn in
theorem center_T_K {S2 : Subgroup (K ≃+* K)} {w : ↥Kb} (hw : w ∈ (Tsub σ S2).subgroupOf Kb)
    (hc : ∀ y ∈ (Tsub σ S2).subgroupOf Kb, y * w = w * y) (hne : w ≠ 1) :
    ∃ m ∈ MbSt σ Kb (Pst0 σ), m * zK σ Kb hinn * m⁻¹ = w := by
  obtain ⟨u, hu, δ, hδ, hwd⟩ := (mem_Tsub_iff σ S2 _).1 (Subgroup.mem_subgroupOf.1 hw)
  have hE : ∀ x ∈ Ust σ, x * u = u * fieldActor σ δ x := by
    intro x hx
    have hy : conjK σ Kb hinn x ∈ (Tsub σ S2).subgroupOf Kb :=
      Subgroup.mem_subgroupOf.2 ((mem_Tsub_iff σ S2 _).2
        ⟨x, hx, 1, S2.one_mem, by rw [fieldActor_one, mul_one]; rfl⟩)
    have h := congrArg (fun y : ↥Kb => (y : MulAut (Cm σ))) (hc _ hy)
    simp only [Subgroup.coe_mul, coe_conjK, hwd] at h
    have h2 : MulAut.conj (x * u) * fieldActor σ δ =
        MulAut.conj (u * fieldActor σ δ x) * fieldActor σ δ := by
      calc MulAut.conj (x * u) * fieldActor σ δ
          = MulAut.conj x * (MulAut.conj u * fieldActor σ δ) := by rw [map_mul, mul_assoc]
        _ = MulAut.conj u * fieldActor σ δ * MulAut.conj x := h
        _ = MulAut.conj u * (fieldActor σ δ * MulAut.conj x) := mul_assoc _ _ _
        _ = MulAut.conj u * (MulAut.conj (fieldActor σ δ x) * fieldActor σ δ) := by
          rw [mulAut_mul_conj σ]
        _ = MulAut.conj (u * fieldActor σ δ x) * fieldActor σ δ := by rw [map_mul, mul_assoc]
    exact conj_injective σ (mul_right_cancel h2)
  have hδ1 : δ = 1 := by
    refine RingEquiv.ext fun s => ?_
    obtain ⟨y, hy, hyeq⟩ := conj_x1S_mem σ hσ hu s
    have h := hE (x1S σ hσ s) (x1S_mem_Ust σ hσ s)
    have h2 : fieldActor σ δ (x1S σ hσ s) = u⁻¹ * x1S σ hσ s * u := by
      calc fieldActor σ δ (x1S σ hσ s) = u⁻¹ * (u * fieldActor σ δ (x1S σ hσ s)) := by group
        _ = u⁻¹ * (x1S σ hσ s * u) := by rw [h]
        _ = u⁻¹ * x1S σ hσ s * u := by group
    have h3 : d4x₁ K σ (δ s) = d4x₁ K σ s * y := by
      have := congrArg Subtype.val h2
      rw [fieldActor_x1S σ hσ, coe_x1S, hyeq] at this
      exact this
    have h4 : y = d4x₁ K σ (s + δ s) := by
      rw [d4x₁_add]
      have : y = (d4x₁ K σ s)⁻¹ * d4x₁ K σ (δ s) := by rw [h3]; group
      rw [this, d4x₁_inv σ s]
    rw [h4] at hy
    have h5 := eq_zero_of_d4x₁_mem_Vr σ hσ hy
    show δ s = s
    exact (CharTwo.add_eq_zero.1 h5).symm
  subst hδ1
  rw [fieldActor_one, mul_one] at hwd
  have hwe : w = conjK σ Kb hinn u := Subtype.ext hwd
  have hcu : ∀ y ∈ Ust σ, y * u = u * y := fun y hy => by
    have := hE y hy
    rw [fieldActor_one] at this
    exact this
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hne (by rw [hwe, map_one])
  obtain ⟨h, hh, hhz⟩ := center_d4 σ hσ hu hcu hu1
  refine ⟨conjK σ Kb hinn h, (mem_MbSt σ).2 (conj_mem_autStab_of_mem (Subgroup.mem_inf.1 hh).1),
    ?_⟩
  rw [hwe, zK, ← map_inv, ← map_mul, ← map_mul, hhz]

end Main

end CFSG.Quasithin.H13.F431.D4q.Loc
