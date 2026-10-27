module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

theorem conj_mem_pCoreOf {J : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    {y : G} (hy : y ∈ pCoreOf 2 J) : g * y * g⁻¹ ∈ pCoreOf 2 J :=
  (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_pCoreOf 2 J hg) y).mp hy

@[expose] def cMod (J : Subgroup G) : Subgroup G where
  carrier := {c | c ∈ Subgroup.normalizer (J : Set G) ∧ ∀ x ∈ J, ⁅x, c⁆ ∈ pCoreOf 2 J}
  one_mem' := ⟨one_mem _, fun x _ => by simp [one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (ha' x hx) (conj_mem_pCoreOf ha (hb' x hx))
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_pCoreOf (inv_mem ha) (inv_mem (ha' x hx))

theorem mem_cMod {J : Subgroup G} {c : G} :
    c ∈ cMod J ↔ c ∈ Subgroup.normalizer (J : Set G) ∧ ∀ x ∈ J, ⁅x, c⁆ ∈ pCoreOf 2 J :=
  Iff.rfl

theorem normalizer_le_normalizer_cMod (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (cMod J : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ c ∈ cMod J, g * c * g⁻¹ ∈ cMod J := by
    intro g hg c hc
    refine ⟨mul_mem (mul_mem hg hc.1) (inv_mem hg), fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    rw [inv_inv] at hx'
    have e : ⁅x, g * c * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, c⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_pCoreOf hg (hc.2 _ hx')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  have h := key g⁻¹ (inv_mem hg) _ hc
  simpa [mul_assoc] using h

@[expose] def innerSub (J : Subgroup G) : Subgroup G := J ⊔ cMod J

theorem mem_innerSub_iff {J : Subgroup G} {k : G} :
    k ∈ innerSub J ↔ ∃ j ∈ J, ∃ c ∈ cMod J, k = j * c := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right J (cMod J)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_cMod J))
  rw [innerSub, ← SetLike.mem_coe, h]
  constructor
  · intro hk
    obtain ⟨j, hj, c, hc, rfl⟩ := Set.mem_mul.mp hk
    exact ⟨j, hj, c, hc, rfl⟩
  · rintro ⟨j, hj, c, hc, rfl⟩
    exact Set.mul_mem_mul hj hc

theorem mem_innerSub_of_mem_J {J : Subgroup G} {k : G} (hk : k ∈ J) : k ∈ innerSub J :=
  Subgroup.mem_sup_left hk

theorem mem_innerSub_of_mem_cMod {J : Subgroup G} {k : G} (hk : k ∈ cMod J) : k ∈ innerSub J :=
  Subgroup.mem_sup_right hk

theorem exists_five_not_mem_innerSub {K J : Subgroup G}
    (hgen : K ≤ Subgroup.closure {x | x ∈ K ∧ orderOf x = 5}) (h : ¬ K ≤ innerSub J) :
    ∃ k ∈ K, orderOf k = 5 ∧ k ∉ innerSub J := by
  by_contra hcon
  push Not at hcon
  exact h (hgen.trans ((Subgroup.closure_le _).mpr fun x hx => hcon x hx.1 hx.2))

theorem exists_pow_mul_eq {C : Subgroup G} {g c : G} (hg : g ∈ Subgroup.normalizer (C : Set G))
    (hc : c ∈ C) (m : ℕ) : ∃ c' ∈ C, (g * c) ^ m = g ^ m * c' := by
  induction m with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ m ih =>
    obtain ⟨c', hc', h⟩ := ih
    have h1 : g⁻¹ * c' * g⁻¹⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) c').mp hc'
    rw [inv_inv] at h1
    refine ⟨g⁻¹ * c' * g * c, mul_mem h1 hc, ?_⟩
    rw [pow_succ (g * c), h, pow_succ g]
    group

theorem mem_cMod_of_orderOf_five [Finite G] {J : Subgroup G} (hno : ∀ a ∈ J, orderOf a ≠ 5)
    {k : G} (hk5 : orderOf k = 5) (hk : k ∈ innerSub J) : k ∈ cMod J := by
  obtain ⟨j, hj, c, hc, rfl⟩ := mem_innerSub_iff.mp hk
  have hjN : j ∈ Subgroup.normalizer (cMod J : Set G) :=
    normalizer_le_normalizer_cMod J (Subgroup.le_normalizer hj)
  obtain ⟨c', hc', h⟩ := exists_pow_mul_eq hjN hc 5
  have h1 : (j * c) ^ 5 = 1 := by
    have := pow_orderOf_eq_one (j * c)
    rwa [hk5] at this
  rw [h1] at h
  have hj5 : j ^ 5 ∈ J ⊓ cMod J := by
    refine Subgroup.mem_inf.mpr ⟨pow_mem hj 5, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h.symm]
    exact inv_mem hc'
  have hdvd : ¬ 5 ∣ orderOf j := fun hd =>
    hno _ (pow_mem hj _) (orderOf_pow_orderOf_div (orderOf_pos j).ne' hd)
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hdvd)
  have hjZ : j ∈ J ⊓ cMod J := by
    rw [← hr]
    exact pow_mem hj5 r
  exact mul_mem hjZ.2 hc

theorem exists_five_of_le_innerSub [Finite G] {K J : Subgroup G}
    (hgen : K ≤ Subgroup.closure {x | x ∈ K ∧ orderOf x = 5}) (hin : K ≤ innerSub J)
    (hnc : ¬ ⁅J, K⁆ ≤ pCoreOf 2 J) : ∃ a ∈ J, orderOf a = 5 := by
  by_contra hcon
  push Not at hcon
  apply hnc
  have hKc : K ≤ cMod J :=
    hgen.trans ((Subgroup.closure_le _).mpr fun x hx =>
      mem_cMod_of_orderOf_five hcon hx.2 (hin hx.1))
  exact Subgroup.commutator_le.mpr fun x hx k hk => (hKc hk).2 x hx

theorem innerSub_sup_of_le {J K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ innerSub J) (h₂ : K₂ ≤ cMod J) :
    K₁ ⊔ K₂ ≤ innerSub J :=
  sup_le h₁ (h₂.trans le_sup_right)

end SBc17

end CFSG.Quasithin
