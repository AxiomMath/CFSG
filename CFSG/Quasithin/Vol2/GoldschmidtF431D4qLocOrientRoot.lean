module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocOrient
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocWeyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431NFTI

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open scoped commutatorElement
open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin

set_option linter.unusedSectionVars false

section Elements

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

@[expose] noncomputable def x2C (b : K) (hb : σ b = b) : Cm σ :=
  ⟨d4x₂ K b, (d4x_long_mem σ hb).1⟩

@[expose] noncomputable def x5C (e : K) (he : σ e = e) : Cm σ :=
  ⟨d4x₅ K e, (d4x_long_mem σ he).2.1⟩

@[expose] noncomputable def x6C (f : K) (hf : σ f = f) : Cm σ :=
  ⟨d4x₆ K f, (d4x_long_mem σ hf).2.2⟩

theorem x2C_mem (b : K) (hb : σ b = b) : x2C σ b hb ∈ XC σ :=
  (mem_XC σ).2 (Subgroup.subset_closure ⟨⟨b, hb⟩, rfl⟩)

theorem x5C_mem (e : K) (he : σ e = e) : x5C σ e he ∈ YC σ :=
  (mem_YC σ).2 (Subgroup.subset_closure ⟨⟨e, he⟩, rfl⟩)

theorem x6C_mem (f : K) (hf : σ f = f) : x6C σ f hf ∈ ZC σ :=
  (mem_ZC σ).2 (Subgroup.subset_closure ⟨⟨f, hf⟩, rfl⟩)

include hσ in
theorem exists_x2 {x : Cm σ} (hx : x ∈ XC σ) :
    ∃ b : K, σ b = b ∧ (x : ModGL TwistTag.D4.tag K) = d4x₂ K b := by
  obtain ⟨b, hb⟩ := (NFq.mem_X2_iff σ hσ).1 ((mem_XC σ).1 hx)
  exact ⟨b, b.2, by rw [hb, ← NFq.x2_eq_vmk]⟩

include hσ in
theorem exists_x5 {x : Cm σ} (hx : x ∈ YC σ) :
    ∃ e : K, σ e = e ∧ (x : ModGL TwistTag.D4.tag K) = d4x₅ K e := by
  obtain ⟨e, he⟩ := (NFq.mem_X5_iff σ hσ).1 ((mem_YC σ).1 hx)
  exact ⟨e, e.2, by rw [he, ← NFq.x5_eq_vmk]⟩

include hσ in
theorem XC_le_QC : XC σ ≤ QC σ := fun x hx => by
  obtain ⟨b, hb⟩ := (NFq.mem_X2_iff σ hσ).1 ((mem_XC σ).1 hx)
  exact (mem_QC σ).2 (by rw [hb]; exact NFq.vmk_mem σ hσ _ _)

include hσ in
theorem YC_le_QC : YC σ ≤ QC σ := fun x hx => by
  obtain ⟨e, he⟩ := (NFq.mem_X5_iff σ hσ).1 ((mem_YC σ).1 hx)
  exact (mem_QC σ).2 (by rw [he]; exact NFq.vmk_mem σ hσ _ _)

end Elements

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem X_eq_cj : XC σ = NF.cj (nrC σ) (YC σ) := by
  ext x
  rw [NF.mem_cj]
  constructor
  · intro hx
    obtain ⟨b, hb, hx'⟩ := exists_x2 σ hσ hx
    have h : ((nrC σ)⁻¹ * x * nrC σ : Cm σ) = x5C σ b hb :=
      Subtype.ext (by
        show (trialityOuterRep K)⁻¹ * (x : ModGL TwistTag.D4.tag K) * trialityOuterRep K =
          d4x₅ K b
        rw [hx', ← trialityOuterRep_conj_d4x₅ b]
        group)
    rw [h]
    exact x5C_mem σ b hb
  · intro hx
    obtain ⟨e, he, hx'⟩ := exists_x5 σ hσ hx
    have h : (x : ModGL TwistTag.D4.tag K) = d4x₂ K e := by
      rw [← trialityOuterRep_conj_d4x₅ e, ← hx']
      show (x : ModGL TwistTag.D4.tag K) =
        trialityOuterRep K * ((trialityOuterRep K)⁻¹ * (x : ModGL TwistTag.D4.tag K) *
          trialityOuterRep K) * (trialityOuterRep K)⁻¹
      group
    exact (mem_XC σ).2 (h ▸ (mem_XC σ).1 (x2C_mem σ e he))

include hσ in
theorem Y_eq_cj : YC σ = NF.cj (naC σ) (ZC σ) := by
  ext x
  rw [NF.mem_cj]
  constructor
  · intro hx
    obtain ⟨e, he, hx'⟩ := exists_x5 σ hσ hx
    have h : ((naC σ)⁻¹ * x * naC σ : Cm σ) = x6C σ e he :=
      Subtype.ext (by
        show (trialityMiddleRep K)⁻¹ * (x : ModGL TwistTag.D4.tag K) * trialityMiddleRep K =
          d4x₆ K e
        rw [hx', ← trialityMiddleRep_conj_d4x₆ e]
        group)
    rw [h]
    exact x6C_mem σ e he
  · intro hx
    obtain ⟨f, hf, hx'⟩ := exists_x6 σ hσ hx
    have h : (x : ModGL TwistTag.D4.tag K) = d4x₅ K f := by
      rw [← trialityMiddleRep_conj_d4x₆ f, ← hx']
      show (x : ModGL TwistTag.D4.tag K) =
        trialityMiddleRep K * ((trialityMiddleRep K)⁻¹ * (x : ModGL TwistTag.D4.tag K) *
          trialityMiddleRep K) * (trialityMiddleRep K)⁻¹
      group
    exact (mem_YC σ).2 (h ▸ (mem_YC σ).1 (x5C_mem σ f hf))

include hσ in
theorem ZC_le_comm : ZC σ ≤ ⁅XC σ, YC σ⁆ := fun x hx => by
  obtain ⟨f, hf, hx'⟩ := exists_x6 σ hσ hx
  have hxe : x = ⁅x5C σ f hf, x2C σ 1 (map_one σ)⁆ :=
    Subtype.ext (by
      show (x : ModGL TwistTag.D4.tag K) = ⁅d4x₅ K f, d4x₂ K 1⁆
      rw [hx', comm_d4x₅_d4x₂, mul_one])
  rw [hxe, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (x5C_mem σ f hf) (x2C_mem σ 1 (map_one σ))

end Conj

section Tee

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem tC_mem_QC : tC σ hσ ∈ QC σ :=
  (mem_QC σ).2 (by
    show d4x₄ K σ 1 ∈ d4Vr K σ
    rw [d4x₄_eq_d4v σ]
    exact d4v_mem_d4Vr σ (toRingHom_pow_three_d4 σ hσ) (map_zero σ) (map_zero σ) (map_zero σ))

include hσ in
theorem tC_not_mem_ZC : tC σ hσ ∉ ZC σ := fun h => by
  obtain ⟨f, hf⟩ := (NFq.mem_Zg_iff σ hσ).1 ((mem_ZC σ).1 h)
  have h1 : (tC σ hσ : ModGL TwistTag.D4.tag K) =
      NFq.vmk σ ((0 : d4k K σ), (0 : K), (1 : K), (0 : d4k K σ)) 0 := d4x₄_eq_d4v σ 1
  have h2 := (NFq.vmk_inj σ (hf.symm.trans h1)).1
  have h3 := congrArg (fun y : NFq.Vc σ => y.2.2.1) h2
  exact one_ne_zero h3.symm

include hσ in
theorem tC_comm_X {a : Cm σ} (ha : a ∈ XC σ) : a * tC σ hσ = tC σ hσ * a := by
  obtain ⟨b, -, hb⟩ := exists_x2 σ hσ ha
  exact Subtype.ext (by
    show (a : ModGL TwistTag.D4.tag K) * d4x₄ K σ 1 = d4x₄ K σ 1 * (a : ModGL TwistTag.D4.tag K)
    rw [hb]
    exact (commute_d4x₄_d4x₂ σ 1 b).symm.eq)

include hσ in
theorem tC_comm_Y {a : Cm σ} (ha : a ∈ YC σ) : a * tC σ hσ = tC σ hσ * a := by
  obtain ⟨e, -, he⟩ := exists_x5 σ hσ ha
  exact Subtype.ext (by
    show (a : ModGL TwistTag.D4.tag K) * d4x₄ K σ 1 = d4x₄ K σ 1 * (a : ModGL TwistTag.D4.tag K)
    rw [he]
    exact (commute_d4x₅_d4x₄ σ e 1).eq)

end Tee

end CFSG.Quasithin.H13.F431.D4q.Loc
