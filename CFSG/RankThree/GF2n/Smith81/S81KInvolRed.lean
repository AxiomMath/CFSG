module

public import CFSG.RankThree.GF2n.Smith81.S81KSylow
public import CFSG.RankThree.GF2n.Smith81.S81TCond
public import CFSG.RankThree.GF2n.Smith81.S81E7Cent2

public section

namespace CFSG.RankThree.GF2n.Smith81.SK

section Invol

open CFSG.RankThree.GF2n.Smith81.D6Spin CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.MinuscT
  CFSG.RankThree.GF2n.Smith81.E7Model


@[expose] def LamClassListStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ x : Gp K, x ∈ LamG K → x * x = 1 → x ≠ 1 →
      ∃ h ∈ LamG K, ∃ S ∈ e4Reps, h * x * h⁻¹ = (⟨tS K S, tS_mem S⟩ : Gp K)

theorem eq_one_of_indW_one
    {K : Type} [Field K] [Finite K] [CharP K 2] {x : Gp K}
    (hx : x ∈ LamG K) (h : IndW x 1) : x = 1 := by
  apply Subtype.ext
  apply Lam_faithful_V0 (K := K) hx
  intro v hv
  obtain ⟨w, rfl⟩ := exists_emb_eq hv
  simpa using (h w).symm

theorem e4InvolClasses_of_lam (hcl : LamClassListStatement) : E4InvolClassesStatement := by
  intro K _ _ _ hq t ht ht2 ht1
  obtain ⟨x, hxL, hxt⟩ := (mem_EAut0_iff (K := K)).1 ht
  have hx2 : x * x = 1 := by
    have hind : IndW (x * x) (t * t) := hxt.mul hxt
    rw [ht2] at hind
    exact eq_one_of_indW_one (mul_mem hxL hxL) hind
  have hx1 : x ≠ 1 := by
    intro h
    apply ht1
    rw [h] at hxt
    exact hxt.unique IndW.one
  obtain ⟨h, hhL, S, hS, hconj⟩ := hcl K hq x hxL hx2 hx1
  obtain ⟨g, hg⟩ := exists_indW (K := K) hhL
  refine ⟨g, (mem_EAut0_iff (K := K)).2 ⟨h, hhL, hg⟩, S, hS, fun w => ?_⟩
  have hgg : IndW (h * x * h⁻¹) (g * t * g⁻¹) := (hg.mul hxt).mul hg.inv
  rw [hconj] at hgg
  rw [hgg w]
  exact congrArg (fun f : Module.End K (V K) => f (emb K w)) (tS_val S)

end Invol

section LamClassList

open CFSG.RankThree.GF2n.Smith81.D6Spin CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.MinuscT
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.Blueprint.Chevalley

open CFSG.LieType.Steinberg.Minuscule


@[expose] def cascadeD6 : List Rt :=
  [![0, 1, 1, 2, 2, 2, 1], ![0, 1, 1, 2, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0]]

@[expose] def LamCascadeProdStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (x : Gp K), x ∈ ULG K → x * x = 1 →
    ∃ h ∈ LamG K, ∃ S : List Rt, S.Sublist cascadeD6 ∧ ∃ c : Rt → K, (∀ σ ∈ S, c σ ≠ 0) ∧
      h * x * h⁻¹ = (S.map fun σ => e7Data_valid.xm K σ (c σ)).prod

@[expose] def LamTorusNormalizeStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (S : List Rt), S.Sublist cascadeD6 →
    ∀ c : Rt → K, (∀ σ ∈ S, c σ ≠ 0) →
      ∃ t ∈ LamG K, t * (S.map fun σ => e7Data_valid.xm K σ (c σ)).prod * t⁻¹ =
        (⟨tS K S, tS_mem S⟩ : Gp K)

@[expose] def LamFrameWalkStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (S : List Rt), S.Sublist cascadeD6 → S ≠ [] →
    ∃ T ∈ e4Reps, ∃ g ∈ LamG K,
      g * (⟨tS K S, tS_mem S⟩ : Gp K) * g⁻¹ = (⟨tS K T, tS_mem T⟩ : Gp K)

theorem lamClassList_of_helpers (hCascade : LamCascadeProdStatement)
    (hTorus : LamTorusNormalizeStatement) (hWalk : LamFrameWalkStatement) :
    LamClassListStatement := by
  intro K _ _ _ hq x hxL hx2 hx1
  have hpg : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hx2, one_zpow]
  obtain ⟨g₁, hg₁, hconj₁⟩ := lam_conj_into_ULG (K := K) (Subgroup.zpowers x)
    ((Subgroup.zpowers_le).2 hxL) hpg
  have hx' : g₁ * x * g₁⁻¹ ∈ ULG K := hconj₁ ⟨x, Subgroup.mem_zpowers x, rfl⟩
  have hx'2 : (g₁ * x * g₁⁻¹) * (g₁ * x * g₁⁻¹) = 1 := by
    calc (g₁ * x * g₁⁻¹) * (g₁ * x * g₁⁻¹) = g₁ * (x * x) * g₁⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  obtain ⟨h₂, hh₂, S, hS, c, hc, hconj₂⟩ := hCascade K _ hx' hx'2
  have hSne : S ≠ [] := by
    rintro rfl
    apply hx1
    have h1 : h₂ * (g₁ * x * g₁⁻¹) * h₂⁻¹ = 1 := by rw [hconj₂]; rfl
    calc x = (h₂ * g₁)⁻¹ * (h₂ * (g₁ * x * g₁⁻¹) * h₂⁻¹) * (h₂ * g₁) := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨t, ht, hconj₃⟩ := hTorus K S hS c hc
  obtain ⟨T, hT, g₄, hg₄, hconj₄⟩ := hWalk K S hS hSne
  refine ⟨g₄ * t * h₂ * g₁, mul_mem (mul_mem (mul_mem hg₄ ht) hh₂) hg₁, T, hT, ?_⟩
  calc g₄ * t * h₂ * g₁ * x * (g₄ * t * h₂ * g₁)⁻¹
      = g₄ * (t * (h₂ * (g₁ * x * g₁⁻¹) * h₂⁻¹) * t⁻¹) * g₄⁻¹ := by group
    _ = g₄ * (⟨tS K S, tS_mem S⟩ : Gp K) * g₄⁻¹ := by rw [hconj₂, hconj₃]
    _ = (⟨tS K T, tS_mem T⟩ : Gp K) := hconj₄

end LamClassList

end CFSG.RankThree.GF2n.Smith81.SK
