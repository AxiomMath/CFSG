module

public import CFSG.LocalAnalysis.StandardType.GGFinModelExists
public import CFSG.LocalAnalysis.StandardType.GGFinModelInput
public import CFSG.LocalAnalysis.StandardType.GGFinModelTorusMem
public import CFSG.LocalAnalysis.StandardType.GGFinModelEps
public import CFSG.RankThree.PartOne.KF4.A2Frame
public import CFSG.LocalAnalysis.StandardType.GGResidualA2Pair

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.StandardType CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE8F
open scoped MatrixGroups

section ToralKernel

theorem permLattice_ne_neg_of_isRoot {τ : Tag} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (π : Equiv.Perm (Fin τ.rank)) :
    permLattice π α ≠ -α := by
  intro he
  apply hα.ne_zero
  funext k
  have hk := congrFun he k
  change α (π.symm k) = -α k at hk
  change α k = 0
  rcases hα.nonneg_or_nonpos with hpos | hneg
  · have h1 := hpos k
    have h2 := hpos (π.symm k)
    omega
  · have h1 := hneg k
    have h2 := hneg (π.symm k)
    omega

theorem frob_famKernel_stable {τ : Tag} {L : Type} [Field L]
    {D : LangDatum τ L} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap D ρ) (F : Set (Fin τ.rank → Lˣ))
    (hF : ∀ a ∈ F, rootDiagUnit τ a ∈ D.torus) :
    Set.MapsTo ρ (famKernel F) (famKernel F) := by
  intro α hα
  refine ⟨(hρ.isRoot_iff α).2 hα.1, ?_⟩
  intro a ha
  rw [hρ.rootChar_eq a (hF a ha) α hα.1, hα.2 a ha, one_pow]

theorem reversal_of_toral_two_root_kernel {τ : Tag} {L : Type} [Field L]
    {D : LangDatum τ L} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    (hρ : FrobRootMap D ρ) (F : Set (Fin τ.rank → Lˣ))
    (hF : ∀ a ∈ F, rootDiagUnit τ a ∈ D.torus)
    {α : Fin τ.rank → ℤ} (hk : famKernel F = {α, -α})
    (π : Equiv.Perm (Fin τ.rank)) (hlaw : ρ α = -permLattice π α) :
    ρ α = -α := by
  have hα : α ∈ famKernel F := by rw [hk]; simp
  have hmem := frob_famKernel_stable hρ F hF hα
  rw [hk, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hfix | hrev
  · have hbad : permLattice π α = -α := by
      have h := congrArg Neg.neg (hlaw.symm.trans hfix)
      simpa using h
    exact (permLattice_ne_neg_of_isRoot hα.1 π hbad).elim
  · exact hrev

theorem reversal_frame_of_two_roots {τ : Tag} {L : Type} [Field L]
    {j : Matrix.SpecialLinearGroup (Fin 3) L →* ModGL τ L}
    {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (π : Equiv.Perm (Fin τ.rank))
    (hlaw : ∀ α, IsRoot τ α → ρ α = -permLattice π α)
    (h01 : ρ (σ 0 1) = -σ 0 1) (h12 : ρ (σ 1 2) = -σ 1 2) :
    ∀ i k : Fin 3, i ≠ k → ρ (σ i k) = σ k i := by
  have hp01 : permLattice π (σ 0 1) = σ 0 1 :=
    neg_injective ((hlaw _ (hpair.isRoot 0 1 (by decide))).symm.trans h01)
  have hp12 : permLattice π (σ 1 2) = σ 1 2 :=
    neg_injective ((hlaw _ (hpair.isRoot 1 2 (by decide))).symm.trans h12)
  have hp02 : permLattice π (σ 0 2) = σ 0 2 := by
    rw [← hpair.add 0 1 2]
    funext k
    change (σ 0 1) (π.symm k) + (σ 1 2) (π.symm k) = (σ 0 1) k + (σ 1 2) k
    rw [show (σ 0 1) (π.symm k) = (σ 0 1) k from congrFun hp01 k,
      show (σ 1 2) (π.symm k) = (σ 1 2) k from congrFun hp12 k]
  have hpneg : ∀ α : Fin τ.rank → ℤ, permLattice π α = α → permLattice π (-α) = -α := by
    intro α hα
    funext k
    exact congrArg Neg.neg (congrFun hα k)
  intro i k hik
  rw [hlaw _ (hpair.isRoot i k hik), hpair.neg i k]
  apply congrArg Neg.neg
  fin_cases i <;> fin_cases k
  · exact (hik rfl).elim
  · exact hp01
  · exact hp02
  · change permLattice π (σ 1 0) = σ 1 0
    rw [hpair.neg 0 1]; exact hpneg _ hp01
  · exact (hik rfl).elim
  · exact hp12
  · change permLattice π (σ 2 0) = σ 2 0
    rw [hpair.neg 0 2]; exact hpneg _ hp02
  · change permLattice π (σ 2 1) = σ 2 1
    rw [hpair.neg 1 2]; exact hpneg _ hp12
  · exact (hik rfl).elim

end ToralKernel

theorem exists_frobRootMap_model {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) :
    ∃ ρ : Equiv.Perm (Fin (langTag t).rank → ℤ), FrobRootMap M.D ρ :=
  CFSG.HardMathSupport.Timmesfeld.LangTorus.frobeniusOnRoots_proved (langTag t) GGL M.D

theorem rho_eq_eps_permLattice_model {t : StatedLieTag} {f p : ℕ} {ht : GGExcFive t}
    (M : GGDatumModel t f p ht) {ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)}
    (hρ : FrobRootMap M.D ρ) {α : Fin (langTag t).rank → ℤ}
    (hα : IsRoot (langTag t) α) :
    ρ α = eps p f • permLattice ((finCongr (rank_eq_langTag f ht)).permCongr
      (piB t p f)) α := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ggRho_untw M.D M.w M.hΦ M.hn _ M.hw ρ hρ hα
  · exact ggRho_untw M.D M.w M.hΦ M.hn _ M.hw ρ hρ hα
  · exact ggRho_untw M.D M.w M.hΦ M.hn _ M.hw ρ hρ hα
  · exact ggRho_untw M.D M.w M.hΦ M.hn _ M.hw ρ hρ hα
  · exact ggRho_tw M.D M.w M.hΦ M.hn _ M.hw ρ hρ hα

theorem reversal_model_of_toral_two_root_kernel {t : StatedLieTag} {f p : ℕ}
    {ht : GGExcFive t} (M : GGDatumModel t f p ht)
    {ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)} (hρ : FrobRootMap M.D ρ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    (F : Set (Fin (langTag t).rank → GGLˣ))
    (hF : ∀ a ∈ F, rootDiagUnit (langTag t) a ∈ M.D.torus)
    {α : Fin (langTag t).rank → ℤ} (hk : famKernel F = {α, -α}) :
    ρ α = -α := by
  have hα : IsRoot (langTag t) α := by
    have hmem : α ∈ famKernel F := by rw [hk]; simp
    exact hmem.1
  apply reversal_of_toral_two_root_kernel hρ F hF hk
    ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f))
  have heps : eps p f = -1 := (eps_eq_neg_one_iff hp hp2 f (Or.inr hplus)).2 hplus
  simpa [heps] using rho_eq_eps_permLattice_model M hρ hα

theorem reversal_frame_of_toral_kernels {t : StatedLieTag} {f p : ℕ}
    {ht : GGExcFive t} (M : GGDatumModel t f p ht)
    {ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)} (hρ : FrobRootMap M.D ρ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hplus : p ∣ 2 ^ f + 1)
    {j : Matrix.SpecialLinearGroup (Fin 3) GGL →* ModGL (langTag t) GGL}
    {σ : Fin 3 → Fin 3 → Fin (langTag t).rank → ℤ}
    (hpair : CFSG.RankThree.PartOne.KF4.IsA2Frame j σ)
    (F₀ F₁ : Set (Fin (langTag t).rank → GGLˣ))
    (hF₀ : ∀ a ∈ F₀, rootDiagUnit (langTag t) a ∈ M.D.torus)
    (hF₁ : ∀ a ∈ F₁, rootDiagUnit (langTag t) a ∈ M.D.torus)
    (hk₀ : famKernel F₀ = {σ 0 1, -σ 0 1})
    (hk₁ : famKernel F₁ = {σ 1 2, -σ 1 2}) :
    ∀ i k : Fin 3, i ≠ k → ρ (σ i k) = σ k i := by
  have heps : eps p f = -1 := (eps_eq_neg_one_iff hp hp2 f (Or.inr hplus)).2 hplus
  apply reversal_frame_of_two_roots hpair ρ
    ((finCongr (rank_eq_langTag f ht)).permCongr (piB t p f))
    (fun α hα => by simpa [heps] using rho_eq_eps_permLattice_model M hρ hα)
  · exact reversal_model_of_toral_two_root_kernel M hρ hp hp2 hplus F₀ hF₀ hk₀
  · exact reversal_model_of_toral_two_root_kernel M hρ hp hp2 hplus F₁ hF₁ hk₁

end CFSG.StandardType.GGFinModel

end

