module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenSecond
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg4Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_nineteen_case4 (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Setting16 D ⊥ V L) (hconc : Conc4_136 D ⊥ V hV L)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hC : Concl1617 D ⊥ V hV L A g Δ)
    (h4 : Case168_4At D ⊥ V hV L 3 3) (hAM : A ≤ D.M) (hAel : IsElemAbelian 2 A)
    (hrk : 2 < rk ↥(barSub ⊥ V hV A)) : Unique19 D V g Δ ∧ Second19 V A := by
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
  have hmem : ∀ I ∈ Δ, imgTil ⊥ V hV I ∈
      {J : Subgroup (Vtil ⊥ V hV) | ∃ Y₁ ∈ conjSubs (Mbar D.M ⊥ V hV) Z,
        ∃ Y₂ ∈ conjSubs (Mbar D.M ⊥ V hV) Z, Y₁ ≠ Y₂ ∧ J = Y₁ ⊔ Y₂} :=
    fun I hI => hpairs' _ (Set.mem_image_of_mem _ hI)
  exact ⟨s16c167_unique_of_tilde D hV hM hle hmem (s16c167_cfg4_uniq19 F),
    s16c167_second_of_tilde D hV hM hAM hAel hrk (s16c167_cfg4_two19 F)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
