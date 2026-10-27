module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNc
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.H13.L829N

open Module
open scoped commutatorElement

section SMV

variable {G : Type} [Group G] {Lu V : Subgroup G} {M : Type} [AddCommGroup M]
  [Module (ZMod 2) M]

private abbrev toM_LNe (a : Multiplicative M) : M := Additive.ofMul a

private lemma ofMul_mem_sub_iff_LNe (SM : SectionModule Lu ⊥ V M) (K : Subgroup G) (x : ↥V) :
    toM_LNe (SM.π x) ∈ SM.sub K ↔ (x : G) ∈ K := by
  refine ⟨fun h => ?_, fun h => SM.mem_sub_of_mem h⟩
  obtain ⟨y, hy, hyx⟩ := SM.mem_sub.mp h
  have hyx' : y = x := SM.π_injective_of_bot rfl (Additive.ofMul.injective hyx)
  rw [← hyx']
  exact hy

private lemma two_pow_finrank_sub_LNe [Finite M] (SM : SectionModule Lu ⊥ V M) {K : Subgroup G}
    (hK : K ≤ V) : 2 ^ finrank (ZMod 2) (SM.sub K) = Nat.card K := by
  haveI : Module.Finite (ZMod 2) M := inferInstance
  have hbij : Function.Bijective (fun c : ↥K =>
      (⟨toM_LNe (SM.π ⟨c.1, hK c.2⟩), SM.mem_sub_of_mem (x := ⟨c.1, hK c.2⟩) c.2⟩ :
        ↥(SM.sub K))) := by
    refine ⟨fun c c' h => ?_, fun w => ?_⟩
    · have h' : toM_LNe (SM.π ⟨c.1, hK c.2⟩) = toM_LNe (SM.π ⟨c'.1, hK c'.2⟩) :=
        congrArg Subtype.val h
      have hx : (⟨c.1, hK c.2⟩ : ↥V) = ⟨c'.1, hK c'.2⟩ :=
        SM.π_injective_of_bot rfl (Additive.ofMul.injective h')
      have hx' : c.1 = c'.1 := by
        have h2 := congrArg Subtype.val hx
        exact h2
      exact Subtype.ext hx'
    · obtain ⟨x, hx, hxw⟩ := SM.mem_sub.mp w.2
      exact ⟨⟨x.1, hx⟩, Subtype.ext hxw⟩
  have hcard : Nat.card K = Nat.card (SM.sub K) := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

lemma finrank_sub_eq_add_four_LNe [Finite M] (SM : SectionModule Lu ⊥ V M) {U B₁ : Subgroup G}
    (hB₁ : B₁ ≤ V) (hcard : Nat.card B₁ = 16 * Nat.card U) (hU : U ≤ V) :
    finrank (ZMod 2) (SM.sub B₁) = finrank (ZMod 2) (SM.sub U) + 4 := by
  have h : 2 ^ finrank (ZMod 2) (SM.sub B₁) = 2 ^ (finrank (ZMod 2) (SM.sub U) + 4) := by
    rw [two_pow_finrank_sub_LNe SM hB₁, hcard, ← two_pow_finrank_sub_LNe SM hU]
    ring
  exact Nat.pow_right_injective (le_refl 2) h

lemma finrank_sub_le_add_one_LNe [Finite M] (SM : SectionModule Lu ⊥ V M) {B B₁ : Subgroup G}
    (hB : B ≤ V) (hB₁ : B₁ ≤ V) (hcard : Nat.card B ≤ 2 * Nat.card B₁) :
    finrank (ZMod 2) (SM.sub B) ≤ finrank (ZMod 2) (SM.sub B₁) + 1 := by
  have h : 2 ^ finrank (ZMod 2) (SM.sub B) ≤ 2 ^ (finrank (ZMod 2) (SM.sub B₁) + 1) := by
    rw [two_pow_finrank_sub_LNe SM hB, pow_succ, two_pow_finrank_sub_LNe SM hB₁]
    omega
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

lemma sub_ne_LNe (SM : SectionModule Lu ⊥ V M) {U B₁ : Subgroup G} (hB₁ : B₁ ≤ V)
    (hlt : U < B₁) : SM.sub U ≠ SM.sub B₁ := by
  obtain ⟨b, hb, hbU⟩ := SetLike.exists_of_lt hlt
  intro h
  have h1 : toM_LNe (SM.π ⟨b, hB₁ hb⟩) ∈ SM.sub B₁ := SM.mem_sub_of_mem (x := ⟨b, hB₁ hb⟩) hb
  rw [← h] at h1
  exact hbU ((ofMul_mem_sub_iff_LNe SM U ⟨b, hB₁ hb⟩).mp h1)

lemma sub_inv_norm_LNe (SM : SectionModule Lu ⊥ V M) (K : Subgroup G)
    (hK : Lu ≤ Subgroup.normalizer (K : Set G)) (g : ↥Lu) (w : M) (hw : w ∈ SM.sub K) :
    SM.ρ g w ∈ SM.sub K :=
  SM.sub_inv K g (fun c hc => (Subgroup.mem_normalizer_iff.mp (hK g.2) c).mp hc) w hw

private lemma rho_comp_LNe (SM : SectionModule Lu ⊥ V M) (a b : ↥Lu) (w : M) :
    SM.ρ a (SM.ρ b w) = SM.ρ (a * b) w := by
  rw [map_mul]
  rfl

private lemma comm_formula_LNe (SM : SectionModule Lu ⊥ V M) (s s' : ↥Lu) (v : M) :
    SM.ρ s (SM.ρ s' (SM.ρ (s' * s)⁻¹ v)) - SM.ρ s' (SM.ρ s (SM.ρ (s' * s)⁻¹ v)) =
      SM.ρ (s * s' * s⁻¹ * s'⁻¹) v - v := by
  have h1 : SM.ρ s' (SM.ρ s (SM.ρ (s' * s)⁻¹ v)) = v := by
    rw [rho_comp_LNe SM s' s, rho_comp_LNe SM (s' * s) (s' * s)⁻¹ v, mul_inv_cancel, map_one]
    rfl
  have h2 : SM.ρ s (SM.ρ s' (SM.ρ (s' * s)⁻¹ v)) = SM.ρ (s * s' * s⁻¹ * s'⁻¹) v := by
    rw [rho_comp_LNe SM s s' (SM.ρ (s' * s)⁻¹ v), rho_comp_LNe SM (s * s') (s' * s)⁻¹ v]
    have e : s * s' * (s' * s)⁻¹ = s * s' * s⁻¹ * s'⁻¹ := by group
    rw [e]
  rw [h1, h2]

private lemma rho_sub_LNe (SM : SectionModule Lu ⊥ V M) (hLuV : Lu ≤ Subgroup.normalizer (V : Set G))
    (c : ↥Lu) {b : G} (hbV : b ∈ V) :
    ∃ hcb : (c : G) * b * (c : G)⁻¹ * b⁻¹ ∈ V,
      SM.ρ c (toM_LNe (SM.π ⟨b, hbV⟩)) - toM_LNe (SM.π ⟨b, hbV⟩) =
        toM_LNe (SM.π ⟨(c : G) * b * (c : G)⁻¹ * b⁻¹, hcb⟩) := by
  have hcb : (c : G) * b * (c : G)⁻¹ * b⁻¹ ∈ V :=
    V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLuV c.2) b).mp hbV) (V.inv_mem hbV)
  exact ⟨hcb, SM.ρ_sub_self c ⟨b, hbV⟩ hcb⟩

lemma hnonab_sm_LNe (SM : SectionModule Lu ⊥ V M) {U B₁ : Subgroup G}
    (hLuV : Lu ≤ Subgroup.normalizer (V : Set G)) (hLuB₁ : Lu ≤ Subgroup.normalizer (B₁ : Set G))
    (hB₁V : B₁ ≤ V) (hnonab : ∃ x ∈ Lu, ∃ y ∈ Lu, ∃ b ∈ B₁, ⁅⁅x, y⁆, b⁆ ∉ U) :
    ∃ s s' : ↥Lu, ∃ b ∈ SM.sub B₁,
      SM.ρ s (SM.ρ s' b) - SM.ρ s' (SM.ρ s b) ∉ SM.sub U := by
  obtain ⟨x, hx, y, hy, b, hb, hbU⟩ := hnonab
  have hbV : b ∈ V := hB₁V hb
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, SM.ρ (⟨y, hy⟩ * ⟨x, hx⟩)⁻¹ (toM_LNe (SM.π ⟨b, hbV⟩)),
    sub_inv_norm_LNe SM B₁ hLuB₁ _ _ (SM.mem_sub_of_mem (x := ⟨b, hbV⟩) hb), ?_⟩
  rw [comm_formula_LNe SM ⟨x, hx⟩ ⟨y, hy⟩ (toM_LNe (SM.π ⟨b, hbV⟩))]
  obtain ⟨hcb, hdiff⟩ := rho_sub_LNe SM hLuV (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) hbV
  rw [hdiff, ofMul_mem_sub_iff_LNe]
  exact hbU

private def preSub_LNe (SM : SectionModule Lu ⊥ V M) (C : Submodule (ZMod 2) M) :
    Subgroup G where
  carrier := {x | ∃ hx : x ∈ V, toM_LNe (SM.π ⟨x, hx⟩) ∈ C}
  one_mem' := by
    show ∃ hx : (1 : G) ∈ V, toM_LNe (SM.π ⟨1, hx⟩) ∈ C
    refine ⟨V.one_mem, ?_⟩
    rw [show (⟨1, V.one_mem⟩ : ↥V) = 1 from rfl, map_one]
    exact C.zero_mem
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hxV, hxC⟩ := hx
    obtain ⟨hyV, hyC⟩ := hy
    show ∃ hz : x * y ∈ V, toM_LNe (SM.π ⟨x * y, hz⟩) ∈ C
    refine ⟨V.mul_mem hxV hyV, ?_⟩
    rw [show (⟨x * y, V.mul_mem hxV hyV⟩ : ↥V) = ⟨x, hxV⟩ * ⟨y, hyV⟩ from rfl, map_mul]
    exact C.add_mem hxC hyC
  inv_mem' := by
    intro x hx
    obtain ⟨hxV, hxC⟩ := hx
    show ∃ hz : x⁻¹ ∈ V, toM_LNe (SM.π ⟨x⁻¹, hz⟩) ∈ C
    refine ⟨V.inv_mem hxV, ?_⟩
    rw [show (⟨x⁻¹, V.inv_mem hxV⟩ : ↥V) = (⟨x, hxV⟩ : ↥V)⁻¹ from rfl, map_inv]
    exact C.neg_mem hxC

private lemma mem_preSub_LNe (SM : SectionModule Lu ⊥ V M) (C : Submodule (ZMod 2) M) (x : G) :
    x ∈ preSub_LNe SM C ↔ ∃ hx : x ∈ V, toM_LNe (SM.π ⟨x, hx⟩) ∈ C := Iff.rfl

lemma hirr_sm_LNe (SM : SectionModule Lu ⊥ V M) {U B₁ : Subgroup G}
    (hLuV : Lu ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V) (hB₁V : B₁ ≤ V)
    (hirr : ∀ D : Subgroup G, U ≤ D → D ≤ B₁ → Lu ≤ Subgroup.normalizer (D : Set G) →
      D = U ∨ D = B₁)
    (C : Submodule (ZMod 2) M) (hUC : SM.sub U ≤ C) (hCB : C ≤ SM.sub B₁)
    (hCinv : ∀ s : ↥Lu, ∀ m ∈ C, SM.ρ s m ∈ C) : C = SM.sub U ∨ C = SM.sub B₁ := by
  have hmemV : ∀ x : ↥V, (x : G) ∈ preSub_LNe SM C ↔ toM_LNe (SM.π x) ∈ C := by
    intro x
    rw [mem_preSub_LNe]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩
  have hD_inv : ∀ s : ↥Lu, ∀ x : G, x ∈ preSub_LNe SM C →
      (s : G) * x * (s : G)⁻¹ ∈ preSub_LNe SM C := by
    intro s x hx
    obtain ⟨hxV, hxC⟩ := (mem_preSub_LNe SM C x).mp hx
    have hsxV : (s : G) * x * (s : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hLuV s.2) x).mp hxV
    rw [mem_preSub_LNe]
    refine ⟨hsxV, ?_⟩
    have h2 : toM_LNe (SM.π ⟨(s : G) * x * (s : G)⁻¹, hsxV⟩) =
        SM.ρ s (toM_LNe (SM.π ⟨x, hxV⟩)) :=
      (SM.act s ⟨x, hxV⟩ hsxV).symm
    rw [h2]
    exact hCinv s _ hxC
  have hLuD : Lu ≤ Subgroup.normalizer (preSub_LNe SM C : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hD_inv ⟨s, hs⟩ h hh
    · intro hh
      have key : (s⁻¹ : G) * (s * h * s⁻¹) * (s⁻¹)⁻¹ = h := by group
      rw [← key]
      exact hD_inv ⟨s⁻¹, Lu.inv_mem hs⟩ (s * h * s⁻¹) hh
  have hUD : U ≤ preSub_LNe SM C := by
    intro u hu
    rw [mem_preSub_LNe]
    exact ⟨hUV hu, hUC (SM.mem_sub_of_mem (x := ⟨u, hUV hu⟩) hu)⟩
  have hDB : preSub_LNe SM C ≤ B₁ := by
    intro x hx
    obtain ⟨hxV, hxC⟩ := (mem_preSub_LNe SM C x).mp hx
    obtain ⟨b, hbB, hb⟩ := SM.mem_sub.mp (hCB hxC)
    have hbx : b = ⟨x, hxV⟩ := SM.π_injective_of_bot rfl (Additive.ofMul.injective hb)
    have hbx' : (b : G) = x := by
      have h2 := congrArg Subtype.val hbx
      exact h2
    rw [← hbx']
    exact hbB
  rcases hirr (preSub_LNe SM C) hUD hDB hLuD with hD | hD
  · left
    refine le_antisymm ?_ hUC
    intro w hw
    obtain ⟨b, hbB, hb⟩ := SM.mem_sub.mp (hCB hw)
    have hb' : toM_LNe (SM.π b) = w := hb
    have hbD : (b : G) ∈ preSub_LNe SM C := (hmemV b).mpr (by rw [hb']; exact hw)
    rw [hD] at hbD
    rw [← hb']
    exact SM.mem_sub_of_mem (x := b) hbD
  · right
    refine le_antisymm hCB ?_
    intro w hw
    obtain ⟨b, hbB, hb⟩ := SM.mem_sub.mp hw
    have hb' : toM_LNe (SM.π b) = w := hb
    have hbD : (b : G) ∈ preSub_LNe SM C := by
      rw [hD]
      exact hbB
    rw [← hb']
    exact (hmemV b).mp hbD

end SMV

end CFSG.Quasithin.H13.L829N
