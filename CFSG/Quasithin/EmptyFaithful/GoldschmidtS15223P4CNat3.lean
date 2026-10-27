module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.FLc2Rho
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNotLe

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_mem_normalizer_of_card_two {A : Subgroup G} (hA : Nat.card A = 2)
    {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  by_cases h1 : w = 1
  · rw [h1]
    simp
  · have hconj : g * w * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg w).1 hw
    have hne : g * w * g⁻¹ ≠ 1 := by
      intro h
      apply h1
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).1 hA
    have e1 : (⟨g * w * g⁻¹, hconj⟩ : ↥A) = y := huniq _ (fun h => hne (congrArg Subtype.val h))
    have e2 : (⟨w, hw⟩ : ↥A) = y := huniq _ (fun h => h1 (congrArg Subtype.val h))
    have h3 : g * w * g⁻¹ = w := congrArg Subtype.val (e1.trans e2.symm)
    calc w * g = (g * w * g⁻¹) * g := by rw [h3]
      _ = g * w := by group

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem mem_centralizer_of_rho (hF : ¬ X ≤ Mc) {n : ℕ} {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) n W) (hn : 1 < n)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1) {x : G} (hx : x ∈ X)
    (h : D.rho ⟨x, Subgroup.mem_sup_left hx⟩ ∈ QI n {1}) :
    x ∈ Subgroup.centralizer (zSOf T Mc M B₀ : Set G) := by
  have hF' := d.facts15128 hF
  have hN : x ∈ Subgroup.normalizer (W 1 : Set G) :=
    (D.mem_normalizer_W_iff le_rfl hn ⟨x, Subgroup.mem_sup_left hx⟩).2
      ((mem_flagStabilizer.1 h) 1 (Set.mem_singleton 1))
  have hC : x ∈ Subgroup.centralizer (W 1 : Set G) :=
    mem_centralizer_of_mem_normalizer_of_card_two (by rw [D.W_card 1 le_rfl hn, pow_one]) hN
  rw [← hZW] at hC
  exact (FLc.centralizer_zU_eq hF'.decomp hF'.ZU hF'.ULU x hx).2 hC

theorem exists_rho_not_mem (hF : ¬ X ≤ Mc) {n : ℕ} {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) n W) (hn : 1 < n)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1) :
    ∃ y : G, ∃ hy : y ∈ X ⊓ (M ⊓ I), D.rho ⟨y, Subgroup.mem_sup_left hy.1⟩ ∉ QI n {1} := by
  obtain ⟨y, hy, hyMc⟩ := d.exists_three_elt_not_Mc
  refine ⟨y, hy, fun h => hyMc ?_⟩
  exact (centralizer_zS_le_inf152 d.c.inputs (d.mem_centralizer_of_rho hF D hn hZW hy.1 h)).1

theorem parab_le_NI (hF : ¬ X ≤ Mc) {n : ℕ} {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) n W) (hn : 1 < n)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1) :
    parab (X ⊔ sOf152 T Mc M B₀) n W 1 ≤ M ⊓ I := by
  set S := sOf152 T Mc M B₀ with hS
  set H' : Subgroup G := (X ⊔ S) ⊓ (M ⊓ I) with hH'
  have hSH' : S ≤ H' := le_inf le_sup_right d.c.S_le_N
  obtain ⟨y, hy, hρy⟩ := d.exists_rho_not_mem hF D hn hZW
  have hUJ : Ut n ≤ D.Theta H' := D.Ut_le_Theta hSH'
  have hJ := eq_QI_cuts hUJ
  have h1 : 1 ∉ cuts (D.Theta H') := by
    intro h1
    apply hρy
    have hyJ : D.rho ⟨y, Subgroup.mem_sup_left hy.1⟩ ∈ D.Theta H' :=
      ⟨⟨y, Subgroup.mem_sup_left hy.1⟩, Subgroup.mem_subgroupOf.2
        ⟨Subgroup.mem_sup_left hy.1, hy.2⟩, rfl⟩
    have hyJ' : D.rho ⟨y, Subgroup.mem_sup_left hy.1⟩ ∈ QI n (cuts (D.Theta H')) := by
      rw [← hJ]
      exact hyJ
    have hle : QI n (cuts (D.Theta H')) ≤ QI n {1} :=
      (QI_le_QI_iff (fun j hj => by
        rw [Set.mem_singleton_iff] at hj
        subst hj
        exact ⟨le_rfl, hn⟩)).2 (by simpa using h1)
    exact hle hyJ'
  have hPX : parab (X ⊔ S) n W 1 ≤ X ⊔ S := parab_le _ _ _ _
  have hPH : parab (X ⊔ S) n W 1 ≤ H' := by
    refine D.le_of_Theta_le hSH' hPX ?_
    rw [D.Theta_parab 1]
    rw [hJ]
    refine (QI_le_QI_iff (fun j hj => isNode_of_mem_cuts hj)).2 fun j hj => ?_
    exact ⟨(isNode_of_mem_cuts hj).1, (isNode_of_mem_cuts hj).2, fun h => h1 (h ▸ hj)⟩
  exact hPH.trans inf_le_right

theorem not_parab_le_Mc (hF : ¬ X ≤ Mc) {n : ℕ} {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) n W) (hn : 1 < n)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1) :
    ¬ parab (X ⊔ sOf152 T Mc M B₀) n W 1 ≤ Mc ⊓ I := by
  intro hPM
  set S := sOf152 T Mc M B₀ with hS
  set H'' : Subgroup G := (X ⊔ S) ⊓ (Mc ⊓ I) with hH''
  have hSMc : S ≤ Mc := S_le_T152.trans d.c.setting.qtfe.t_le_mc
  have hSH'' : S ≤ H'' := le_inf le_sup_right (le_inf hSMc (S_le_I152 d.c.inputs))
  have hPX : parab (X ⊔ S) n W 1 ≤ X ⊔ S := parab_le _ _ _ _
  have hPH : parab (X ⊔ S) n W 1 ≤ H'' := le_inf hPX hPM
  have hUJ : Ut n ≤ D.Theta H'' := D.Ut_le_Theta hSH''
  have hJ := eq_QI_cuts hUJ
  have hQ1 : QI n {1} ≤ D.Theta H'' := by
    intro g hg
    obtain ⟨l, hl⟩ := D.surj g
    have hρ : D.rho ⟨(l : G), Subgroup.mem_sup_left l.2⟩ = g := by rw [D.rho_apply_L, hl]
    have hC := d.mem_centralizer_of_rho hF D hn hZW l.2 (by rw [hρ]; exact hg)
    exact ⟨⟨(l : G), Subgroup.mem_sup_left l.2⟩, Subgroup.mem_subgroupOf.2
      ⟨Subgroup.mem_sup_left l.2, centralizer_zS_le_inf152 d.c.inputs hC⟩, hρ⟩
  have hc1 : cuts (D.Theta H'') ⊆ {1} := by
    have h : QI n {1} ≤ QI n (cuts (D.Theta H'')) := by
      rw [← hJ]
      exact hQ1
    exact (QI_le_QI_iff (fun j hj => isNode_of_mem_cuts hj)).1 h
  have hc2 : cuts (D.Theta H'') ⊆ {j | 1 ≤ j ∧ j < n ∧ j ≠ 1} := by
    have h : QI n {j | 1 ≤ j ∧ j < n ∧ j ≠ 1} ≤ QI n (cuts (D.Theta H'')) := by
      rw [← hJ, ← D.Theta_parab 1]
      exact D.Theta_mono hPH
    exact (QI_le_QI_iff (fun j hj => isNode_of_mem_cuts hj)).1 h
  have hempty : cuts (D.Theta H'') = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun j hj => ?_
    have h1 : j = 1 := hc1 hj
    exact (hc2 hj).2.2 h1
  have hJtop : D.Theta H'' = ⊤ := by
    rw [hJ, hempty]
    simp [QI, flagStabilizer]
  have hXS : D.Theta (X ⊔ S) = ⊤ := by
    refine eq_top_iff.2 fun g _ => ?_
    obtain ⟨x, rfl⟩ := D.rho_surjective g
    exact ⟨x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  have hEq : H'' = X ⊔ S := D.eq_of_Theta_eq hSH'' le_sup_right inf_le_left le_rfl
    (hJtop.trans hXS.symm)
  apply hF
  intro x hx
  have : x ∈ H'' := hEq ▸ Subgroup.mem_sup_left hx
  exact this.2.1

end CData

end C

end S15223P4

end CFSG.Quasithin
