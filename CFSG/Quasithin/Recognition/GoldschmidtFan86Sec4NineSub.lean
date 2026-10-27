module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4NineDefs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Norm
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Lam
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Fan23Main

public section

namespace CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} (T : Track Γ G)

theorem Track.inv_smul_vert (i : ℤ) : T.τ⁻¹ • T.line.vert i = T.line.vert (i - 2) := by
  rw [inv_smul_eq_iff]
  have := T.trans (i - 2)
  rw [show i - 2 + 2 = i by omega] at this
  exact this.symm

theorem IsLenTwoReflection.conj_zpow {k : ℤ} {f : G} (h : IsLenTwoReflection T.line k f) (m : ℤ) :
    IsLenTwoReflection T.line (k + 2 * m) (T.τ ^ m * f * (T.τ ^ m)⁻¹) := by
  have hinv : ∀ i : ℤ, (T.τ ^ m)⁻¹ • T.line.vert (i + 2 * m) = T.line.vert i := fun i => by
    rw [inv_smul_eq_iff, T.zpow_smul_vert]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc T.τ ^ m * f * (T.τ ^ m)⁻¹ * (T.τ ^ m * f * (T.τ ^ m)⁻¹)
        = T.τ ^ m * (f * f) * (T.τ ^ m)⁻¹ := by group
      _ = 1 := by rw [h.1]; simp
  · rw [mul_smul, mul_smul, hinv k, h.2.1, T.zpow_smul_vert]
  · rw [show k + 2 * m + 1 = (k + 1) + 2 * m by omega, mul_smul, mul_smul, hinv (k + 1), h.2.2.1,
      T.zpow_smul_vert]
    congr 1
    omega
  · rw [show k + 2 * m + 2 = (k + 2) + 2 * m by omega, mul_smul, mul_smul, hinv (k + 2), h.2.2.2,
      T.zpow_smul_vert]
    congr 1
    omega

variable {T} {a b : ℤ}

theorem swap_mem {f : G} (hfL : f ∈ Subgroup.normalizer (omega1 T.fixer : Set G))
    (hf : IsLenTwoReflection T.line a f) :
    f * T.τ⁻¹ ∈ Lcirc (Subgroup.normalizer (omega1 T.fixer : Set G)) (T.line.vert a)
      (T.line.vert (a + 1)) (T.line.vert (a + 2)) ∧
      (f * T.τ⁻¹) • T.line.vert a = T.line.vert (a + 2) := by
  have hrev : ∀ v : V, f • f • v = v := fun v => by rw [← mul_smul, hf.1, one_smul]
  have hτL : T.τ ∈ Subgroup.normalizer (omega1 T.fixer : Set G) := by
    simpa using T.zpow_mem_normalizer 1
  have h1 : (f * T.τ⁻¹) • T.line.vert a = T.line.vert (a + 2) := by
    rw [mul_smul, T.inv_smul_vert, ← hf.2.2.2, hrev]
  have h2 : (f * T.τ⁻¹) • T.line.vert (a + 1) = T.line.vert (a + 1) := by
    rw [mul_smul, T.inv_smul_vert, show a + 1 - 2 = a - 1 by omega, ← hf.2.2.1, hrev]
  have h3 : (f * T.τ⁻¹) • T.line.vert (a + 2) = T.line.vert a := by
    rw [mul_smul, T.inv_smul_vert, show a + 2 - 2 = a by omega, hf.2.1]
  exact ⟨mem_lcirc_iff.2 ⟨(Subgroup.normalizer (omega1 T.fixer : Set G)).mul_mem hfL
    ((Subgroup.normalizer (omega1 T.fixer : Set G)).inv_mem hτL), h2, Or.inr ⟨h1, h3⟩⟩, h1⟩

theorem H48_inf (F : FanTree Γ G) (hPi : TrackInPi T) (hθ : IsTArc T a b) :
    H48 T a ⊓ MulAction.stabilizer G (T.line.vert a) =
        Subgroup.normalizer (omega1 T.fixer : Set G) ⊓ MulAction.stabilizer G (T.line.vert a) ∧
      H48 T a ⊓ MulAction.stabilizer G (T.line.vert (a + 1)) =
        Lcirc (Subgroup.normalizer (omega1 T.fixer : Set G)) (T.line.vert a)
          (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
  have hL := (fan45_2_lam T F hPi.1 hPi.2 hθ (Or.inl rfl)).1
  have hab : Γ.Adj (T.line.vert a) (T.line.vert (a + 1)) := T.line.adj a
  have hac : T.line.vert a ≠ T.line.vert (a + 2) := T.line.nb a
  have hba₂ : Γ.Adj (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    have := T.line.adj (a + 1)
    rwa [show a + 1 + 1 = a + 2 by omega] at this
  have h41 := fan41_1 F hab hac hL
  refine fan23 F.isTree F.adj_smul (T.line.vert a) (T.line.vert (a + 1)) hab _ _ inf_le_right
    (fun g hg => MulAction.mem_stabilizer_iff.2 (mem_lcirc_iff.1 hg).2.1) ?_
  ext g
  constructor
  · intro hg
    have hK : g ∈ _ ⊓ nbrStab Γ G (T.line.vert (a + 1)) := h41 ▸ hg
    have hgα : g • T.line.vert a = T.line.vert a := MulAction.mem_stabilizer_iff.1 hg.1.2
    have hgβ : g • T.line.vert (a + 1) = T.line.vert (a + 1) :=
      MulAction.mem_stabilizer_iff.1 hg.2
    exact ⟨mem_lcirc_iff.2 ⟨hK.1, hgβ, Or.inl ⟨hgα, hK.2 _ hba₂⟩⟩, hg.1.2⟩
  · intro hg
    obtain ⟨hgL, hgβ, -⟩ := mem_lcirc_iff.1 hg.1
    exact ⟨⟨hgL, hg.2⟩, MulAction.mem_stabilizer_iff.2 hgβ⟩

theorem subgraph48 (F : FanTree Γ G) (hPi : TrackInPi T) (hθ : IsTArc T a b) {f : G}
    (hfL : f ∈ Subgroup.normalizer (omega1 T.fixer : Set G))
    (hf : IsLenTwoReflection T.line a f) : SubgraphProp T a b (H48 T a) := by
  obtain ⟨hinfα, hinfβ⟩ := H48_inf F hPi hθ
  obtain ⟨hgL, -⟩ := swap_mem hfL hf
  refine ⟨hθ, ⟨_, (fan45_2_lam T F hPi.1 hPi.2 hθ (Or.inl rfl)).1, H48_le_normalizer T a⟩,
    fun h hh hβ => ?_, fun g hg => ?_, ?_, ?_⟩
  · have hmem : h ∈ H48 T a ⊓ MulAction.stabilizer G (T.line.vert (a + 1)) :=
      ⟨hh, MulAction.mem_stabilizer_iff.2 hβ⟩
    rw [hinfβ] at hmem
    rcases (mem_lcirc_iff.1 hmem).2.2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  · exact inf_le_H48 T a ⟨(IsQuasiTArc.fixer_normal T F (hθ.isQuasi T)).2 hg,
      MulAction.mem_stabilizer_iff.2 ((T.mem_subFixer).1 hg a le_rfl hθ.1.le)⟩
  · have hg := lcirc_le_H48 T a hgL
    have hf' : f ∈ H48 T a := inf_le_H48 T a ⟨hfL, MulAction.mem_stabilizer_iff.2 hf.2.1⟩
    have := (H48 T a).mul_mem ((H48 T a).inv_mem hg) hf'
    rwa [show (f * T.τ⁻¹)⁻¹ * f = T.τ by group] at this
  · rw [hinfα, hinfβ]
    rfl

end CFSG.Quasithin.Fan86
