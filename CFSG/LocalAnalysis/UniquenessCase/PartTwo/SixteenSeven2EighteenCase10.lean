module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_insp18_case10 (D : Data G) (hk : D.k = 1) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Setting16 D ⊥ V L) {A : Subgroup G} {g : G}
    {Δ : Set (Subgroup G)} (hC : Concl1617 D ⊥ V hV L A g Δ)
    (hc2 : ¬ Case168_2 D ⊥ V hV L) (h10 : Case168_10At D ⊥ V hV L 3) :
    Insp18 D ⊥ V hV L g Δ := by
  obtain ⟨hn, hle, hi, hs, -, -, h910⟩ := hC
  have h10' : Case168_10 D ⊥ V hV L := ⟨3, Or.inl rfl, h10⟩
  have hΔ : Δ = wConj D.M ⊥ V hV L := h910 (Or.inr h10')
  have hM : D.M ≤ normalizer (V : Set G) := hS.hyp16.hyp125.normalizer_eq.ge
  obtain ⟨hcyc, hrk, hs15, -, -⟩ := h10
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hdParam : dParam 3 = 2 := by
    unfold dParam
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by decide) (by decide)
  have hrk4 : rk ↥(commSub ⊤ (barSub ⊥ V hV L)) = 4 := by
    show rk ↥(wTil (⊥ : Subgroup G) V hV L) = 4
    rw [hrk, hdParam]
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV, Y = (barSub ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    unfold s15 at hs15
    exact hs15
  have hcj : imgTil ⊥ V hV '' Δ =
      conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (barSub ⊥ V hV L)) := by
    rw [hΔ]
    exact s16c167_imgTil_wConj hV hM L
  obtain ⟨hn2, hind, hsup⟩ := s16c167_imgTil_decomp hV hn hle hi hs
  rw [hcj] at hn2 hind hsup
  obtain ⟨h1, h2, h3, h4⟩ :=
    s16c167_cfg10_abstract (W := Vtil (⊥ : Subgroup G) V hV)
      (X := Mbar D.M ⊥ V hV) (L := barSub ⊥ V hV L) hW hcyc hrk4 hcls hn2 hind hsup
  have hmem : ∀ I ∈ Δ,
      imgTil ⊥ V hV I ∈ conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (barSub ⊥ V hV L)) :=
    fun I hI => hcj ▸ Set.mem_image_of_mem _ hI
  refine s16c167_insp18_of_tilde D hM hle ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hk]
    exact h4
  · intro I hI
    rw [hk, h1 _ (hmem I hI)]
    norm_num
  · exact s16c167_disj_of_tilde hM hle
      (fun t ht I hI => h2 t ht (imgTil ⊥ V hV I) (hmem I hI))
  · exact fun _ => hk
  · exact fun h => absurd h hc2
  · intro _ t ht ht2 I hI hIt
    rw [hk]
    exact h3 t ht ht2 (imgTil ⊥ V hV I) (hmem I hI) hIt

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
