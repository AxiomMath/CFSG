module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocVNorm
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocCent
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructAut

public section

namespace CFSG.Quasithin.H13.F431.D4q.StdLoc

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc
  CFSG.Quasithin.H13.F431.D4q.NFq


set_option linter.unusedSectionVars false

section Normalized

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem centralizer_d4t_le_normalizer_d4Va :
    d4C K σ ⊓ Subgroup.centralizer {d4t K σ} ≤
      Subgroup.normalizer (d4Va σ : Set (ModGL TwistTag.D4.tag K)) := by
  rw [centralizer_d4t_eq σ hσ]
  refine sup_le (fun u hu => posUnipotent_le_normalizer_d4Va σ hσ ?_)
    (d4Ma_le_normalizer_d4Va σ hσ)
  exact (inf_le_left.trans (graphFixedSimpleComplement_le _) : d4U0t K σ ≤
    graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) hu

include hσ in
theorem VaC_normalized {g : Cm σ} (hg : g * tC σ hσ = tC σ hσ * g) {v : Cm σ} (hv : v ∈ VaC σ) :
    g * v * g⁻¹ ∈ VaC σ := by
  have hg' : (g : ModGL TwistTag.D4.tag K) * d4t K σ = d4t K σ * g := by
    have := congrArg Subtype.val hg
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_tC σ hσ] at this
  have hN := centralizer_d4t_le_normalizer_d4Va σ hσ
    (Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 hg'⟩)
  exact (mem_VaC σ).2 ((Subgroup.mem_normalizer_iff.1 hN _).1 ((mem_VaC σ).1 hv))

end Normalized

section FieldActor

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ δ : K ≃+* K)

theorem map_entrywise_mem_d4Va {g : ModGL TwistTag.D4.tag K} (hg : g ∈ d4Va σ) :
    Units.map (entrywiseHom δ.toRingHom) g ∈ d4Va σ := by
  have hk : ∀ c : d4k K σ, σ (δ c) = δ c := fun c => by
    rw [← ringEquiv_comm_of_finite σ δ c, (mem_d4k σ).1 c.2]
  refine Subgroup.closure_induction
    (p := fun g _ => Units.map (entrywiseHom δ.toRingHom) g ∈ d4Va σ) ?_ ?_ ?_ ?_ hg
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · have : Units.map (entrywiseHom δ.toRingHom) (d4x₅ K c) = d4x₅ K (δ c) :=
        Units.ext (entrywise_pinnedX δ.toRingHom _ c)
      rw [this]
      exact d4x₅_mem_d4Va σ ⟨δ c, (mem_d4k σ).2 (hk c)⟩
    · have : Units.map (entrywiseHom δ.toRingHom) (d4x₆ K c) = d4x₆ K (δ c) :=
        Units.ext (entrywise_pinnedX δ.toRingHom _ c)
      rw [this]
      exact d4x₆_mem_d4Va σ ⟨δ c, (mem_d4k σ).2 (hk c)⟩
  · rw [map_one]
    exact one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact inv_mem hx

theorem fieldActor_mem_VaC {v : Cm σ} (hv : v ∈ VaC σ) : fieldActor σ δ v ∈ VaC σ :=
  (mem_VaC σ).2 (by
    rw [coe_fieldActor]
    exact map_entrywise_mem_d4Va σ δ ((mem_VaC σ).1 hv))

end FieldActor

section Aut

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hσ hf hK hσq in
theorem VaC_aut :
    ∀ φ : MulAut (Cm σ), φ (tC σ hσ) = tC σ hσ → ∀ v ∈ VaC σ, φ v ∈ VaC σ := by
  intro φ hφ v hv
  obtain ⟨-, -, hex, -⟩ := exists_theta σ hf hK hσq
  obtain ⟨g, δ, rfl⟩ := hex φ
  rw [MulAut.mul_apply, fieldActor_tC σ hσ, MulAut.conj_apply] at hφ
  have hgt : g * tC σ hσ = tC σ hσ * g := by
    calc g * tC σ hσ = (g * tC σ hσ * g⁻¹) * g := by group
      _ = tC σ hσ * g := by rw [hφ]
  rw [MulAut.mul_apply, MulAut.conj_apply]
  exact VaC_normalized σ hσ hgt (fieldActor_mem_VaC σ δ hv)

end Aut

end CFSG.Quasithin.H13.F431.D4q.StdLoc
