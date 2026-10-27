module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenAssembly

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_insp18_case4 (D : Data G) (hk : D.k = 1) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Setting16 D ⊥ V L) (hconc : Conc4_136 D ⊥ V hV L)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hC : Concl1617 D ⊥ V hV L A g Δ)
    (hc2 : ¬ Case168_2 D ⊥ V hV L) (h4 : Case168_4At D ⊥ V hV L 3 3) :
    Insp18 D ⊥ V hV L g Δ := by
  obtain ⟨hn, hle, hi, hs, -, h4cl, -⟩ := hC
  obtain ⟨-, hperm_u, hpairs⟩ := h4cl h4
  have hM : D.M ≤ normalizer (V : Set G) := hS.hyp16.hyp125.normalizer_eq.ge
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hdParam : dParam 3 = 2 := by
    unfold dParam
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  obtain ⟨hLab, -, -⟩ := h4
  obtain ⟨Z, hZ, hind, hsup, hncard, hperm, hpairs'⟩ := hpairs
  rw [hdParam] at hZ
  have hrk8 := s16c167_cfg4_rk_top hZ hind hsup hncard
  obtain ⟨t, htM, -, -, -, hW136⟩ := hconc
  have hnorm := s16c167_cfg4_normal hW hLab hrk8 hW136
  have hLX : barSub ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hS.hyp151.le
  have F : Cfg4Setting (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L) Z :=
    ⟨hW, hLab, hLX, hnorm, hZ, hind, hsup, hncard, hperm⟩
  obtain ⟨h1, h2, h3⟩ := s16c167_cfg4_abstract F
  have hmem : ∀ I ∈ Δ, ∃ Y₁ ∈ conjSubs (Mbar D.M ⊥ V hV) Z,
      ∃ Y₂ ∈ conjSubs (Mbar D.M ⊥ V hV) Z,
      Y₁ ≠ Y₂ ∧ imgTil ⊥ V hV I = Y₁ ⊔ Y₂ :=
    fun I hI => hpairs' _ (Set.mem_image_of_mem _ hI)
  refine s16c167_insp18_of_tilde D hM hle ?_ ?_ ?_ ?_ ?_ ?_
  · show D.k + 1 ≤ E3.mParam (Mbar D.M ⊥ V hV)
    rw [hk]
    exact h1
  · intro I hI
    obtain ⟨Y₁, hY₁, Y₂, hY₂, hne, hI'⟩ := hmem I hI
    rw [hI', hk, h2 Y₁ hY₁ Y₂ hY₂ hne]
    norm_num
  · exact fun u hu J hJ => s16c167_disj_of_perm hn hi (hperm_u u hu) J hJ
  · exact fun _ => hk
  · exact fun h => absurd h hc2
  · intro _ t ht ht2 I hI hIt
    obtain ⟨Y₁, hY₁, Y₂, hY₂, hne, hI'⟩ := hmem I hI
    rw [hI'] at hIt ⊢
    rw [hk]
    exact h3 t ht ht2 Y₁ hY₁ Y₂ hY₂ hne hIt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
