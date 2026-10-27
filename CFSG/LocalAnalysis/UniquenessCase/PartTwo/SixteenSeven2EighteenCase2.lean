module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Ge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenMod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

theorem s16c167_center_of_isSym_three {A : Type} [Group A] (h : IsSym A 3) :
    ∀ κ : A, (∀ y : A, y * κ = κ * y) → κ = 1 := by
  obtain ⟨e⟩ := h
  intro κ hκ
  have hc : ∀ y : Equiv.Perm (Fin 3), y * e κ = e κ * y := by
    intro y
    have h1 := congrArg e (hκ (e.symm y))
    simpa using h1
  have hs : ∀ σ : Equiv.Perm (Fin 3), (∀ y : Equiv.Perm (Fin 3), y * σ = σ * y) → σ = 1 := by
    decide
  exact e.injective (by rw [hs _ hc, map_one])

variable {G : Type} [Group G] [Finite G]

theorem s16c167_insp18_case2 (D : Data G) (hk : D.k = 1) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Setting16 D ⊥ V L) (hconc : Conc4_136 D ⊥ V hV L)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hC : Concl1617 D ⊥ V hV L A g Δ)
    (h2 : Case168_2 D ⊥ V hV L) : Insp18 D ⊥ V hV L g Δ := by
  obtain ⟨hn, hle, hi, hs, hirr, -, -⟩ := hC
  have hM : D.M ≤ normalizer (V : Set G) := hS.hyp16.hyp125.normalizer_eq.ge
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  obtain ⟨hn2, hind, hsup⟩ := s16c167_imgTil_decomp hV hn hle hi hs
  obtain ⟨a, b, hab, hΔ⟩ := Set.ncard_eq_two.1 hn
  subst hΔ
  have hne : imgTil ⊥ V hV a ≠ imgTil ⊥ V hV b := by
    intro h
    rw [Set.image_pair, h, Set.pair_eq_singleton, Set.ncard_singleton] at hn2
    exact absurd hn2 (by norm_num)
  have hdisj : Disjoint (imgTil ⊥ V hV a) (imgTil ⊥ V hV b) := by
    rw [Set.image_pair] at hind
    exact (sSupIndep_pair hne).1 hind
  have hinf : imgTil ⊥ V hV a ⊓ imgTil ⊥ V hV b = ⊥ := disjoint_iff.1 hdisj
  have hsup' : imgTil ⊥ V hV a ⊔ imgTil ⊥ V hV b = ⊤ := by
    rw [Set.image_pair, sSup_pair] at hsup
    exact hsup
  have hirra : imgTil ⊥ V hV a ∈ irrSet (barSub ⊥ V hV L) := hirr h2 a (by simp)
  have hirrb : imgTil ⊥ V hV b ∈ irrSet (barSub ⊥ V hV L) := hirr h2 b (by simp)
  have hLX : barSub ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hS.hyp151.le
  have hsimple : IsSimpleGroup ↥(barSub ⊥ V hV L) := s16c167_cfg2_simple D h2
  have hfix : fixV (barSub ⊥ V hV L) = ⊥ := s16c167_cfg2_fix D h2
  have hall : commSub ⊤ (barSub ⊥ V hV L) = ⊤ := by
    refine top_le_iff.1 (hsup'.symm.le.trans (sup_le ?_ ?_))
    · calc imgTil ⊥ V hV a = commSub (imgTil ⊥ V hV a) (barSub ⊥ V hV L) := hirra.1.symm
        _ ≤ commSub ⊤ (barSub ⊥ V hV L) := commSub_mono le_top le_rfl
    · calc imgTil ⊥ V hV b = commSub (imgTil ⊥ V hV b) (barSub ⊥ V hV L) := hirrb.1.symm
        _ ≤ commSub ⊤ (barSub ⊥ V hV L) := commSub_mono le_top le_rfl
  have hLbot : barSub ⊥ V hV L ≠ ⊥ := by
    haveI := hsimple.toNontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hnorm : ∀ x ∈ Mbar D.M ⊥ V hV,
      (barSub ⊥ V hV L).map (MulAut.conj x).toMonoidHom = barSub ⊥ V hV L := by
    obtain ⟨t, -, -, -, -, hW136⟩ := hconc
    exact s16c167_cfg2_normal hLbot hall hW136
  have hcenter : ∀ κ ∈ kBar D.M ⊥ V hV L,
      (∀ y ∈ kBar D.M ⊥ V hV L, y * κ = κ * y) → κ = 1 := by
    intro κ hκ hc
    have h1 := s16c167_center_of_isSym_three h2.1 ⟨κ, hκ⟩ (fun y => Subtype.ext (hc y y.2))
    simpa using congrArg Subtype.val h1
  have hperf : ⁅barSub ⊥ V hV L, barSub ⊥ V hV L⁆ = barSub ⊥ V hV L :=
    s16c167_cfg2_perfect hLX hsimple rfl hcenter
  have F : Cfg2Setting (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) (imgTil ⊥ V hV a)
      (imgTil ⊥ V hV b) := ⟨hW, hnorm, hsimple, hperf, hfix, hirra, hirrb, hinf, hsup'⟩
  have hodd : 2 ≤ rk (Vtil ⊥ V hV) := by
    have h3 := s16c167_cfg2_rk_ge_three F hirra
    have h4 : rk ↥(imgTil ⊥ V hV a) ≤ rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) := rk_mono le_top
    rw [rk_top] at h4
    omega
  refine s16c167_insp18_of_tilde D hM hle ?_ ?_ ?_ ?_ ?_ ?_
  · show D.k + 1 ≤ E3.mParam (Mbar D.M ⊥ V hV)
    rw [hk]
    exact s16c167_le_mParam _ (fun t ht _ ht1 => s16c167_cfg2_ge F ht ht1) hodd
  · intro I hI
    rw [hk]
    have := s16c167_cfg2_rk_ge_three F (hirr h2 I hI)
    omega
  · exact s16c167_disj_of_tilde hM hle
      (fun t ht I hI => s16c167_cfg2_disj F (hirr h2 I hI) ht)
  · exact fun _ => hk
  · intro _ t ht _ hr _ I hI
    rw [hk] at hr
    obtain ⟨h0, h1⟩ := s16c167_cfg2_nc F ht hr
    rcases hI with rfl | rfl
    · exact h0
    · exact h1
  · exact fun h => absurd h2 h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
