module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Cell
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructOdd

public section

namespace CFSG.Quasithin.H13.F431.D4q.NFq

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct

variable {K : Type} [Field K] (σ : K ≃+* K)

@[expose] def trT (c : K) : K := c + σ c + σ (σ c)

theorem mem_d4k {c : K} : c ∈ d4k K σ ↔ σ c = c := Iff.rfl

theorem trT_mem (hσ : ∀ c, σ (σ (σ c)) = c) (c : K) : trT σ c ∈ d4k K σ := by
  rw [mem_d4k]
  unfold trT
  rw [map_add, map_add, hσ]
  ring

theorem trT_add (a b : K) : trT σ (a + b) = trT σ a + trT σ b := by
  unfold trT
  rw [map_add, map_add]
  ring

theorem trT_smul {l : K} (hl : σ l = l) (c : K) : trT σ (l * c) = l * trT σ c := by
  unfold trT
  simp only [map_mul, hl]
  ring

theorem trT_one [CharP K 2] : trT σ 1 = 1 := by
  unfold trT
  rw [map_one, map_one]
  have : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [add_assoc, this, add_zero]


set_option linter.unusedSectionVars false

variable [Finite K] [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c)

abbrev Vc : Type := d4k K σ × K × K × d4k K σ

@[expose] noncomputable def vmk (x : Vc σ) (f : d4k K σ) : ModGL TwistTag.D4.tag K :=
  d4v K σ x.1 x.2.1 x.2.2.1 x.2.2.2 f

include hσ in
theorem vmk_mem (x : Vc σ) (f : d4k K σ) : vmk σ x f ∈ d4Vr K σ :=
  d4v_mem_d4Vr σ (toRingHom_pow_three_d4 σ hσ) x.1.2 x.2.2.2.2 f.2

theorem vmk_inj {x y : Vc σ} {f f' : d4k K σ} (h : vmk σ x f = vmk σ y f') : x = y ∧ f = f' := by
  have h' : d4x₁ K σ 0 * d4v K σ x.1 x.2.1 x.2.2.1 x.2.2.2 f =
      d4x₁ K σ 0 * d4v K σ y.1 y.2.1 y.2.2.1 y.2.2.2 f' := by
    rw [d4x₁_zero, one_mul, one_mul]
    exact h
  obtain ⟨-, hb, hc, hd, he, hf⟩ := d4coord_injective σ h'
  exact ⟨Prod.ext (Subtype.ext hb) (Prod.ext hc (Prod.ext hd (Subtype.ext he))),
    Subtype.ext hf⟩

include hσ in
theorem exists_vmk {g : ModGL TwistTag.D4.tag K} (hg : g ∈ d4Vr K σ) :
    ∃ (x : Vc σ) (f : d4k K σ), g = vmk σ x f := by
  obtain ⟨b, c, d, e, f, hb, he, hf, rfl⟩ := exists_d4v σ (toRingHom_pow_three_d4 σ hσ) hg
  exact ⟨(⟨b, hb⟩, c, d, ⟨e, he⟩), ⟨f, hf⟩, rfl⟩

include hσ in
@[expose] def beta (x y : Vc σ) : d4k K σ :=
  ⟨trT σ (x.2.2.1 * y.2.1) + x.2.2.2 * y.1,
    add_mem (trT_mem σ hσ _) (mul_mem x.2.2.2.2 y.1.2)⟩

include hσ in
@[expose] def gam (x : Vc σ) : d4k K σ :=
  ⟨x.1 * x.2.2.2 + trT σ (x.2.1 * x.2.2.1),
    add_mem (mul_mem x.1.2 x.2.2.2.2) (trT_mem σ hσ _)⟩

include hσ in
theorem vmk_mul (x y : Vc σ) (f f' : d4k K σ) :
    vmk σ x f * vmk σ y f' = vmk σ (x + y) (beta σ hσ x y + f + f') := by
  unfold vmk
  rw [d4v_mul σ hσ]
  congr 1
  unfold beta trT
  push_cast
  ring

include hσ in
theorem vmk_inv (x : Vc σ) (f : d4k K σ) : (vmk σ x f)⁻¹ = vmk σ x (gam σ hσ x + f) := by
  unfold vmk
  rw [d4v_inv σ hσ]
  rfl

theorem vmk_zero : vmk σ 0 0 = 1 := d4v_zero σ

@[expose] noncomputable def d4X2 : Subgroup (ModGL TwistTag.D4.tag K) :=
  Subgroup.closure (Set.range fun c : d4k K σ => d4x₂ K c)

@[expose] noncomputable def d4X5 : Subgroup (ModGL TwistTag.D4.tag K) :=
  Subgroup.closure (Set.range fun c : d4k K σ => d4x₅ K c)

theorem x2_eq_vmk (c : d4k K σ) : d4x₂ K c = vmk σ (c, 0, 0, 0) 0 := (d4v_single σ c).1.symm

theorem x5_eq_vmk (c : d4k K σ) : d4x₅ K c = vmk σ (0, 0, 0, c) 0 := (d4v_single σ c).2.2.2.1.symm

theorem x6_eq_vmk (c : d4k K σ) : d4x₆ K c = vmk σ 0 c := (d4v_single σ c).2.2.2.2.symm

include hσ in
theorem mem_Zg_iff {g : ModGL TwistTag.D4.tag K} :
    g ∈ d4Zz K σ ↔ ∃ f : d4k K σ, g = vmk σ 0 f := by
  have h0 : beta σ hσ 0 0 = 0 := Subtype.ext (by simp [beta, trT])
  have hg0 : gam σ hσ 0 = 0 := Subtype.ext (by simp [gam, trT])
  constructor
  · intro hg
    refine Subgroup.closure_induction (p := fun g _ => ∃ f : d4k K σ, g = vmk σ 0 f) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨c, rfl⟩
      exact ⟨c, x6_eq_vmk σ c⟩
    · exact ⟨0, (vmk_zero σ).symm⟩
    · rintro _ _ _ _ ⟨f, rfl⟩ ⟨f', rfl⟩
      refine ⟨f + f', ?_⟩
      rw [vmk_mul σ hσ, h0, add_zero, zero_add]
    · rintro _ _ ⟨f, rfl⟩
      exact ⟨f, by rw [vmk_inv σ hσ, hg0, zero_add]⟩
  · rintro ⟨f, rfl⟩
    exact Subgroup.subset_closure ⟨f, x6_eq_vmk σ f⟩

include hσ in
theorem mem_X2_iff {g : ModGL TwistTag.D4.tag K} :
    g ∈ d4X2 σ ↔ ∃ b : d4k K σ, g = vmk σ (b, 0, 0, 0) 0 := by
  have hb : ∀ b b' : d4k K σ, beta σ hσ (b, 0, 0, 0) (b', 0, 0, 0) = 0 := fun b b' =>
    Subtype.ext (by simp [beta, trT])
  have hgm : ∀ b : d4k K σ, gam σ hσ (b, 0, 0, 0) = 0 := fun b =>
    Subtype.ext (by simp [gam, trT])
  constructor
  · intro hg
    refine Subgroup.closure_induction (p := fun g _ => ∃ b : d4k K σ, g = vmk σ (b, 0, 0, 0) 0)
      ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨c, rfl⟩
      exact ⟨c, x2_eq_vmk σ c⟩
    · exact ⟨0, (vmk_zero σ).symm⟩
    · rintro _ _ _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
      refine ⟨b + b', ?_⟩
      rw [vmk_mul σ hσ, hb]
      simp
    · rintro _ _ ⟨b, rfl⟩
      exact ⟨b, by rw [vmk_inv σ hσ, hgm, zero_add]⟩
  · rintro ⟨b, rfl⟩
    exact Subgroup.subset_closure ⟨b, x2_eq_vmk σ b⟩

include hσ in
theorem mem_X5_iff {g : ModGL TwistTag.D4.tag K} :
    g ∈ d4X5 σ ↔ ∃ e : d4k K σ, g = vmk σ (0, 0, 0, e) 0 := by
  have hb : ∀ e e' : d4k K σ, beta σ hσ (0, 0, 0, e) (0, 0, 0, e') = 0 := fun e e' =>
    Subtype.ext (by simp [beta, trT])
  have hgm : ∀ e : d4k K σ, gam σ hσ (0, 0, 0, e) = 0 := fun e =>
    Subtype.ext (by simp [gam, trT])
  constructor
  · intro hg
    refine Subgroup.closure_induction (p := fun g _ => ∃ e : d4k K σ, g = vmk σ (0, 0, 0, e) 0)
      ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨c, rfl⟩
      exact ⟨c, x5_eq_vmk σ c⟩
    · exact ⟨0, (vmk_zero σ).symm⟩
    · rintro _ _ _ _ ⟨e, rfl⟩ ⟨e', rfl⟩
      refine ⟨e + e', ?_⟩
      rw [vmk_mul σ hσ, hb]
      simp
    · rintro _ _ ⟨e, rfl⟩
      exact ⟨e, by rw [vmk_inv σ hσ, hgm, zero_add]⟩
  · rintro ⟨e, rfl⟩
    exact Subgroup.subset_closure ⟨e, x5_eq_vmk σ e⟩

end CFSG.Quasithin.H13.F431.D4q.NFq
