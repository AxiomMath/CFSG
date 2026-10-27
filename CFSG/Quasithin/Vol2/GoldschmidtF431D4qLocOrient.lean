module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocCenter

public section

namespace CFSG.Quasithin.H13.F431.D4q.Loc

open scoped commutatorElement
open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin

set_option linter.unusedSectionVars false


section Defs

variable {K : Type} [Field K] (σ : K ≃+* K)

noncomputable abbrev ZC : Subgroup (Cm σ) := (d4Zz K σ).subgroupOf (d4C K σ)

noncomputable abbrev QC : Subgroup (Cm σ) := (d4Vr K σ).subgroupOf (d4C K σ)

noncomputable abbrev XC : Subgroup (Cm σ) := (NFq.d4X2 σ).subgroupOf (d4C K σ)

noncomputable abbrev YC : Subgroup (Cm σ) := (NFq.d4X5 σ).subgroupOf (d4C K σ)

theorem mem_ZC {x : Cm σ} : x ∈ ZC σ ↔ (x : ModGL TwistTag.D4.tag K) ∈ d4Zz K σ :=
  Subgroup.mem_subgroupOf

theorem mem_QC {x : Cm σ} : x ∈ QC σ ↔ (x : ModGL TwistTag.D4.tag K) ∈ d4Vr K σ :=
  Subgroup.mem_subgroupOf

theorem mem_XC {x : Cm σ} : x ∈ XC σ ↔ (x : ModGL TwistTag.D4.tag K) ∈ NFq.d4X2 σ :=
  Subgroup.mem_subgroupOf

theorem mem_YC {x : Cm σ} : x ∈ YC σ ↔ (x : ModGL TwistTag.D4.tag K) ∈ NFq.d4X5 σ :=
  Subgroup.mem_subgroupOf

end Defs

section Basic

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

theorem Vr_le_C : d4Vr K σ ≤ d4C K σ :=
  (graphFixedSimpleComplement_le _).trans (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)

include hσ in
theorem Zz_le_C : d4Zz K σ ≤ d4C K σ := (NFq.Zg_le_Qg σ hσ).trans (Vr_le_C σ)

include hσ in
theorem ZC_le_QC : ZC σ ≤ QC σ := fun _ hx => (mem_QC σ).2 (NFq.Zg_le_Qg σ hσ ((mem_ZC σ).1 hx))

theorem QC_le_Ust : QC σ ≤ Ust σ := fun _ hx =>
  Subgroup.mem_subgroupOf.2 (graphFixedSimpleComplement_le _ ((mem_QC σ).1 hx))

include hσ in
theorem QC_norm {s x : Cm σ} (hs : s ∈ Ust σ) (hx : x ∈ QC σ) : s * x * s⁻¹ ∈ QC σ :=
  (mem_QC σ).2 (NFq.Qg_conj_U σ hσ (Subgroup.mem_subgroupOf.1 hs) ((mem_QC σ).1 hx))

include hσ in
theorem ZC_central {x s : Cm σ} (hx : x ∈ ZC σ) (hs : s ∈ Ust σ) : s * x = x * s :=
  Subtype.ext (NFq.Zg_central_U σ hσ (Subgroup.mem_subgroupOf.1 hs) ((mem_ZC σ).1 hx))

include hσ in
theorem exists_x6 {x : Cm σ} (hx : x ∈ ZC σ) :
    ∃ f : K, σ f = f ∧ (x : ModGL TwistTag.D4.tag K) = d4x₆ K f := by
  obtain ⟨f, hf⟩ := (NFq.mem_Zg_iff σ hσ).1 ((mem_ZC σ).1 hx)
  exact ⟨f, f.2, by rw [hf, ← NFq.x6_eq_vmk]⟩

include hσ in
theorem ZC_exp {x : Cm σ} (hx : x ∈ ZC σ) : x * x = 1 := by
  obtain ⟨f, -, hf⟩ := exists_x6 σ hσ hx
  exact Subtype.ext (by rw [Subgroup.coe_mul, hf]; exact d4x₆_mul_self K f)

include hσ in
theorem QC_comm {x y : Cm σ} (hx : x ∈ QC σ) (hy : y ∈ QC σ) : ⁅x, y⁆ ∈ ZC σ :=
  (mem_ZC σ).2 (NFq.commutator_mem_Zg σ hσ ((mem_QC σ).1 hx) ((mem_QC σ).1 hy))

include hσ in
theorem QC_sq {x : Cm σ} (hx : x ∈ QC σ) : x * x ∈ ZC σ :=
  (mem_ZC σ).2 (NFq.sq_mem_Zg σ hσ ((mem_QC σ).1 hx))

include hσ in
theorem Ust_comm {x y : Cm σ} (hx : x ∈ Ust σ) (hy : y ∈ Ust σ) : ⁅x, y⁆ ∈ QC σ :=
  (mem_QC σ).2 (NFq.commutator_U_mem_Qg σ hσ (Subgroup.mem_subgroupOf.1 hx)
    (Subgroup.mem_subgroupOf.1 hy))

include hσ in
theorem zC_mem_ZC : zC σ ∈ ZC σ :=
  (mem_ZC σ).2 (Subgroup.subset_closure ⟨⟨1, map_one σ⟩, rfl⟩)

end Basic

section Cards

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
  {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hσq : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hσ hf hK hσq in
theorem card_ZC : Nat.card (ZC σ) = 2 ^ f := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Zz_le_C σ hσ)).toEquiv]
  exact NFq.card_Zg σ hf hK hσq

include hf hK hσq in
theorem card_QC : Nat.card (QC σ) = (2 ^ f) ^ 9 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Vr_le_C σ)).toEquiv]
  exact NFq.card_Qg σ hf hK hσq

include hf hK hσq in
theorem card_Ust : Nat.card (Ust σ) = (2 ^ f) ^ 12 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (graphFixedPosUnipotent_le_graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).toEquiv]
  exact NFq.card_U σ hf hK hσq

include hσ hf hK hσq in
theorem card_le_elem {E : Subgroup (Cm σ)} (hEQ : E ≤ QC σ)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ (2 ^ f) ^ 5 := by
  have e : Nat.card (E.map (d4C K σ).subtype) = Nat.card E :=
    Subgroup.card_map_of_injective (d4C K σ).subtype_injective
  rw [← e]
  refine NFq.card_le_of_abelian σ hσ hK (NFq.card_d4k σ hf hK hσq) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_QC σ).1 (hEQ hx)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hab x hx y hy)

include hσ hf hK hσq in
theorem aut_ZC {φ : MulAut (Cm σ)} (hφ : φ ∈ autStab (Pst0 σ)) {x : Cm σ} (hx : x ∈ ZC σ) :
    φ x ∈ ZC σ :=
  (mem_ZC σ).2 (NFq.aut_Zg σ hf hK hσq hφ ((mem_ZC σ).1 hx))

include hf hK hσq in
theorem aut_QC {φ : MulAut (Cm σ)} (hφ : φ ∈ autStab (Pst0 σ)) {x : Cm σ} (hx : x ∈ QC σ) :
    φ x ∈ QC σ :=
  (mem_QC σ).2 (NFq.aut_Qg σ hf hK hσq hφ ((mem_QC σ).1 hx))

end Cards

section Trans

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem trans_ZC {x y : Cm σ} (hx : x ∈ ZC σ) (hy : y ∈ ZC σ) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ d ∈ Pst0 σ, d * x * d⁻¹ = y := by
  obtain ⟨f1, hf1, hx'⟩ := exists_x6 σ hσ hx
  obtain ⟨f2, hf2, hy'⟩ := exists_x6 σ hσ hy
  have hf10 : f1 ≠ 0 := fun h => hx1 (Subtype.ext (by rw [hx', h, d4x₆_zero]; rfl))
  have hf20 : f2 ≠ 0 := fun h => hy1 (Subtype.ext (by rw [hy', h, d4x₆_zero]; rfl))
  obtain ⟨h1, hP1, -, hh1⟩ := exists_torus_zC σ hσ hf1 hf10
  obtain ⟨h2, hP2, -, hh2⟩ := exists_torus_zC σ hσ hf2 hf20
  have hxe : x = h1 * zC σ * h1⁻¹ := Subtype.ext (hx'.trans hh1.symm)
  have hye : y = h2 * zC σ * h2⁻¹ := Subtype.ext (hy'.trans hh2.symm)
  refine ⟨h2 * h1⁻¹, mul_mem hP2 (inv_mem hP1), ?_⟩
  rw [hxe, hye]
  group

end Trans

end CFSG.Quasithin.H13.F431.D4q.Loc
