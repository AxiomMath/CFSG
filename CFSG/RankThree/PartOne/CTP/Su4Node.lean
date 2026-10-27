module

public import CFSG.RankThree.PartOne.CTP.Su4Geom
public import CFSG.RankThree.PartOne.CTP.SpGeom

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {p : ℕ} [NeZero p] {ζ : K}

theorem smul_mem_eigU {g a : SUid σ 4} (hc : a * g = g * a) {l : K} {v : Fin 4 → K}
    (hv : v ∈ eigU g l) : a • v ∈ eigU g l := by
  rw [mem_eigU] at hv ⊢
  calc g • a • v = (g * a) • v := (mul_smul g a v).symm
    _ = (a * g) • v := by rw [hc]
    _ = a • g • v := mul_smul a g v
    _ = a • l • v := by rw [hv]
    _ = l • a • v := smul_comm a l v

theorem perfect_smul_eq_of_finrank_eq_one {g : SUid σ 4} (A : Subgroup (SUid σ 4))
    [Group.IsPerfect A] (hc : ∀ a ∈ A, a * g = g * a) {l : K}
    (hd : Module.finrank K (eigU g l) = 1) {z : Fin 4 → K} (hz : z ∈ eigU g l) :
    ∀ a ∈ A, a • z = z := by
  intro a ha
  by_cases hz0 : z = 0
  · rw [hz0, smul_zero]
  have hline : ∀ b : A, ∃ c : K, ((actU σ 4).comp A.subtype) b z = c • z := by
    intro b
    have hb : (b : SUid σ 4) • z ∈ eigU g l := smul_mem_eigU (hc b b.2) hz
    obtain ⟨c, hcv⟩ := (finrank_eq_one_iff_of_nonzero' (⟨z, hz⟩ : eigU g l)
      (fun h => hz0 (congrArg Subtype.val h))).mp hd ⟨_, hb⟩
    exact ⟨c, (congrArg Subtype.val hcv).symm⟩
  exact perfect_fix_of_line ((actU σ 4).comp A.subtype) hz0 hline ⟨a, ha⟩

theorem two_le_finrank_eigU_of_moved {g : SUid σ 4} (A : Subgroup (SUid σ 4))
    [Group.IsPerfect A] (hc : ∀ a ∈ A, a * g = g * a) {l : K} {a : SUid σ 4} (ha : a ∈ A)
    {v : Fin 4 → K} (hv : v ∈ eigU g l) (hmov : a • v ≠ v) :
    2 ≤ Module.finrank K (eigU g l) := by
  by_contra hlt
  have hv0 : v ≠ 0 := fun h => hmov (by rw [h, smul_zero])
  have hpos : 0 < Module.finrank K (eigU g l) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have h1 : Module.finrank K (eigU g l) = 1 := by omega
  exact hmov (perfect_smul_eq_of_finrank_eq_one A hc h1 hv a ha)

theorem su4_node [CharP K 2] (hσ : ∀ c, σ (σ c) = c) (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ l : K, l ^ p = 1 → σ l = l) {g : SUid σ 4} (hg : g ^ p = 1) (hg1 : g ≠ 1)
    (A : Subgroup (SUid σ 4)) [Group.IsPerfect A] (hA1 : A ≠ ⊥)
    (hc : ∀ a ∈ A, a * g = g * a) :
    (Module.finrank K (eigU g 1) = 2 ∧ ∀ a ∈ A, ∀ v ∈ movU g, a • v = v) ∨
      ∃ l : K, l ≠ 1 ∧ l ^ p = 1 ∧ Module.finrank K (eigU g l) = 2 ∧
        Module.finrank K (eigU g l⁻¹) = 2 ∧ IsCompl (eigU g l) (eigU g l⁻¹) ∧
        ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eigU g μ = ⊥ := by
  classical
  have hind : iSupIndep (fun m : K => eigU g m) := Module.End.eigenspaces_iSupIndep _
  obtain ⟨l, a, ha, v, hv, hmv⟩ : ∃ l : K, ∃ a ∈ A, ∃ v ∈ eigU g l, a • v ≠ v := by
    by_contra hcon
    push Not at hcon
    apply hA1
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have hle : (⊤ : Submodule K (Fin 4 → K)) ≤
        Module.End.eigenspace (Matrix.mulVecLin (matU a)) 1 := by
      rw [← iSup_eigU_eq_top hζ hg]
      refine iSup_le fun l v hv => ?_
      rw [Module.End.mem_eigenspace_iff, one_smul]
      exact hcon l a ha v hv
    refine ext_smul σ fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.mulVecLin (matU a)) 1 := hle Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff, one_smul] at hv
    rw [one_smul]
    exact hv
  have h2 := two_le_finrank_eigU_of_moved A hc ha hv hmv
  have hv0 : v ≠ 0 := fun h => hmv (by rw [h, smul_zero])
  by_cases hl : l = 1
  · subst hl
    left
    have hmovne : movU g ≠ ⊥ := by
      intro hb
      apply hg1
      have hE1 : eigU g 1 = ⊤ := by
        have h := (isCompl_eigU_one_movU hζ hg).codisjoint
        rw [codisjoint_iff, hb, sup_bot_eq] at h
        exact h
      refine ext_smul σ fun w => ?_
      have hw : w ∈ eigU g 1 := by rw [hE1]; exact Submodule.mem_top
      rw [mem_eigU, one_smul] at hw
      rw [one_smul]
      exact hw
    obtain ⟨μ, hμ1, hμne⟩ : ∃ μ : K, μ ≠ 1 ∧ eigU g μ ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      exact hmovne (iSup₂_eq_bot.mpr fun μ hμ => hcon μ hμ)
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμne
    have hμp : μ ^ p = 1 := pow_eq_one_of_mem_eigU hg hw hw0
    have hμ0 := ne_zero_of_pow_eq_one' hμp
    have hμinv : μ ≠ μ⁻¹ := by
      intro h
      apply hμ1
      refine eq_one_of_mul_self_eq_one' ?_
      calc μ * μ = μ * μ⁻¹ := congrArg (μ * ·) h
        _ = 1 := mul_inv_cancel₀ hμ0
    have hd1 : 1 ≤ Module.finrank K (eigU g μ) := by
      have : 0 < Module.finrank K (eigU g μ) :=
        Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨w, hw⟩, fun h => hw0 (congrArg Subtype.val h)⟩
      omega
    have hdeq := finrank_eigU_inv hσ hζ hg hfix hμp
    have hdisj := disjoint_eigU (g := g) hμinv
    have hsupmov : eigU g μ ⊔ eigU g μ⁻¹ ≤ movU g :=
      sup_le (eigU_le_movU hμ1) (eigU_le_movU (inv_ne_one.mpr hμ1))
    have hdimsup : Module.finrank K (↥(eigU g μ ⊔ eigU g μ⁻¹)) =
        Module.finrank K (eigU g μ) + Module.finrank K (eigU g μ⁻¹) := by
      have := Submodule.finrank_sup_add_finrank_inf_eq (eigU g μ) (eigU g μ⁻¹)
      rw [hdisj.eq_bot, finrank_bot] at this
      omega
    have hmovle := Submodule.finrank_mono hsupmov
    have hE1 := finrank_eigU_one_add_movU hζ hg
    have hE1eq : Module.finrank K (eigU g 1) = 2 := by omega
    have hmovdim : Module.finrank K (movU g) = 2 := by omega
    have hdμ : Module.finrank K (eigU g μ) = 1 := by omega
    have hmoveq : eigU g μ ⊔ eigU g μ⁻¹ = movU g :=
      Submodule.eq_of_le_of_finrank_eq hsupmov (by omega)
    refine ⟨hE1eq, fun a' ha' v' hv' => ?_⟩
    rw [← hmoveq] at hv'
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv'
    rw [smul_add, perfect_smul_eq_of_finrank_eq_one A hc hdμ hx a' ha',
      perfect_smul_eq_of_finrank_eq_one A hc (g := g) (l := μ⁻¹) (by omega) hy a' ha']
  · right
    have hlp : l ^ p = 1 := pow_eq_one_of_mem_eigU hg hv hv0
    have hl0 := ne_zero_of_pow_eq_one' hlp
    have hσl := hfix l hlp
    have hd2 : Module.finrank K (eigU g l) = 2 :=
      le_antisymm (finrank_eigU_le_two hσ g hl hσl) h2
    have hd2' : Module.finrank K (eigU g l⁻¹) = 2 :=
      (finrank_eigU_inv hσ hζ hg hfix hlp).symm.trans hd2
    have hlinv : l ≠ l⁻¹ := by
      intro h
      apply hl
      refine eq_one_of_mul_self_eq_one' ?_
      calc l * l = l * l⁻¹ := congrArg (l * ·) h
        _ = 1 := mul_inv_cancel₀ hl0
    have hdisj : Disjoint (eigU g l) (eigU g l⁻¹) := disjoint_eigU hlinv
    have hsupTop : eigU g l ⊔ eigU g l⁻¹ = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have := Submodule.finrank_sup_add_finrank_inf_eq (eigU g l) (eigU g l⁻¹)
      rw [hdisj.eq_bot, finrank_bot] at this
      simp only [Module.finrank_fin_fun]
      omega
    refine ⟨l, hl, hlp, hd2, hd2', ⟨hdisj, codisjoint_iff.mpr hsupTop⟩, ?_⟩
    intro μ hμl hμi
    have hle : eigU g l ⊔ eigU g l⁻¹ ≤ ⨆ (ν : K) (_ : ν ≠ μ), eigU g ν :=
      sup_le (le_iSup₂_of_le l (Ne.symm hμl) le_rfl) (le_iSup₂_of_le l⁻¹ (Ne.symm hμi) le_rfl)
    have hdis := (hind μ).mono_right hle
    rw [hsupTop] at hdis
    exact disjoint_top.mp hdis

end CFSG.RankThree.PartOne.CTP
