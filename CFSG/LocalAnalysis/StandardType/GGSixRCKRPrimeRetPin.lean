module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetIota
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetPinAux
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.CharTwoSteinberg
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.Timmesfeld
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

private def rckPn_L {τ : Tag} (β : Fin 6 → Fin τ.rank → ℤ)
    (γ' : Fin Tag.E6.rank → ℤ) : Fin τ.rank → ℤ :=
  ∑ j : Fin Tag.E6.rank, γ' j • β j

private theorem rckPn_L_add {τ : Tag} (β : Fin 6 → Fin τ.rank → ℤ)
    (x y : Fin Tag.E6.rank → ℤ) :
    rckPn_L β (x + y) = rckPn_L β x + rckPn_L β y := by
  simp only [rckPn_L]
  rw [show (∑ j : Fin Tag.E6.rank, (x + y) j • β j) =
      ∑ j : Fin Tag.E6.rank, (x j • β j + y j • β j) from
    Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, add_smul]]
  rw [Finset.sum_add_distrib]

private theorem rckPn_beta_mem {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    (hroot : ∀ b, IsRoot τ (β b)) (j : Fin 6) : β j ∈ rootsOfFam β Set.univ := by
  refine ⟨hroot j, fun b => if b = j then 1 else 0, fun b _ => Set.mem_univ b, Or.inl ?_⟩
  simp [ite_smul, Finset.sum_ite_eq']

private theorem rckPn_L_isRoot {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {γ' : Fin Tag.E6.rank → ℤ} (hγ' : IsRoot Tag.E6 γ') : IsRoot τ (rckPn_L β γ') := by
  obtain ⟨γ, hγ, hιγ⟩ := hι.1.2.2 hγ'
  have hL : rckPn_L β γ' = γ := by
    rw [← hιγ]
    exact hι.2.2.1 γ hγ
  rw [hL]
  exact hγ.1

private theorem rckPn_L_mem_rootsOfFam {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {γ' : Fin Tag.E6.rank → ℤ} (hγ' : IsRoot Tag.E6 γ') :
    rckPn_L β γ' ∈ rootsOfFam β Set.univ := by
  obtain ⟨γ, hγ, hιγ⟩ := hι.1.2.2 hγ'
  have hL : rckPn_L β γ' = γ := by
    rw [← hιγ]
    exact hι.2.2.1 γ hγ
  rw [hL]
  exact hγ

private theorem rckPn_iota_L {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {γ' : Fin Tag.E6.rank → ℤ} (hγ' : IsRoot Tag.E6 γ') : ι (rckPn_L β γ') = γ' := by
  obtain ⟨γ, hγ, hιγ⟩ := hι.1.2.2 hγ'
  have hL : rckPn_L β γ' = γ := by
    rw [← hιγ]
    exact hι.2.2.1 γ hγ
  rw [hL, hιγ]

private theorem rckPn_rootsOfFam_eq_image {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι) :
    rootsOfFam β Set.univ = rckPn_L β '' {γ' | IsRoot Tag.E6 γ'} := by
  ext γ
  constructor
  · intro hγ
    exact ⟨ι γ, hι.1.1 hγ, hι.2.2.1 γ hγ⟩
  · rintro ⟨γ', hγ', hL⟩
    rw [← hL]
    exact rckPn_L_mem_rootsOfFam hι hγ'

private theorem rckPn_L_iform_self
    {τ : Tag} {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    (hroot : ∀ b, IsRoot τ (β b)) (x : Fin Tag.E6.rank → ℤ) :
    iform (rckPn_L β x) (rckPn_L β x) = iform x x := by
  let u : Fin Tag.E6.rank → Fin τ.rank → ℤ := fun i => β i
  let e : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ := fun i => Pi.single i (1 : ℤ)
  have hgram : ∀ i j : Fin Tag.E6.rank, iform (u i) (u j) = iform (e i) (e j) := by
    intro i j
    change iform (β i) (β j) =
      iform (τ := Tag.E6) (Pi.single i (1 : ℤ)) (Pi.single j (1 : ℤ))
    have h := hι.2.2.2.2 (β i) (rckPn_beta_mem hroot i) (β j) (rckPn_beta_mem hroot j)
    rw [hι.2.1 i, hι.2.1 j] at h
    exact h.symm
  have hx : x = ∑ i : Fin Tag.E6.rank, x i • e i := by
    funext k
    show x k = (∑ i : Fin Tag.E6.rank, x i • e i) k
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp [e]
    · intro b _ hb
      simp [e, Pi.smul_apply, Pi.single_eq_of_ne, hb]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hL : rckPn_L β x = ∑ i : Fin Tag.E6.rank, x i • u i := rfl
  calc iform (rckPn_L β x) (rckPn_L β x)
      = iform (∑ i : Fin Tag.E6.rank, x i • u i)
          (∑ i : Fin Tag.E6.rank, x i • u i) := by rw [hL]
    _ = ∑ i : Fin Tag.E6.rank, ∑ j : Fin Tag.E6.rank, x i * x j * iform (u i) (u j) :=
        CFSG.HardMathSupport.Timmesfeld.RootAut.iform_sum_smul_sum_smul Finset.univ x u
    _ = ∑ i : Fin Tag.E6.rank, ∑ j : Fin Tag.E6.rank, x i * x j * iform (e i) (e j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hgram i j]
    _ = iform (∑ i : Fin Tag.E6.rank, x i • e i)
          (∑ i : Fin Tag.E6.rank, x i • e i) :=
        (CFSG.HardMathSupport.Timmesfeld.RootAut.iform_sum_smul_sum_smul Finset.univ x e).symm
    _ = iform x x := by rw [← hx]

private theorem rckPn_rootSpan_eq_closure
    {τ : Tag} {k K : Type} [Field k] [Field K]
    (e : k ≃+* K) {β : Fin 6 → Fin τ.rank → ℤ}
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι) :
    rootSpan τ K (rootsOfFam β Set.univ) =
      Subgroup.closure {g : ModGL τ K | ∃ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ' ∧
        ∃ c : k, pinnedX τ K (rckPn_L β γ') (e c) = g} := by
  apply le_antisymm
  · refine iSup₂_le fun α hα => ?_
    obtain ⟨γ', hγ', hL⟩ := rckPn_rootsOfFam_eq_image hι ▸ hα
    rw [← hL, rootSubgroup, Subgroup.closure_le]
    rintro g ⟨c, rfl⟩
    exact Subgroup.subset_closure ⟨γ', hγ', e.symm c, by rw [e.apply_symm_apply]⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨γ', hγ', c, rfl⟩
    exact le_iSup₂ (f := fun γ (_ : γ ∈ rootsOfFam β Set.univ) => rootSubgroup τ K γ)
      (rckPn_L β γ') (rckPn_L_mem_rootsOfFam hι hγ')
      (Subgroup.subset_closure ⟨e c, rfl⟩)

theorem rckE6_pinCanon
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {β : Fin 6 → Fin τ.rank → ℤ} (hroot : ∀ b, IsRoot τ (β b))
    {ι : (Fin τ.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hι : RetIotaSpec β ι)
    {k K : Type} [Field k] [Finite k] [Field K] [CharP K 2] (e : k ≃+* K) :
    ∃ Ψ : ↥(e6Data_valid.minGroup k) →* ModGL τ K,
      (∀ γ' : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ' → ∀ c : k,
        Ψ (e6Data_valid.xm k γ' c) = pinnedX τ K (∑ j : Fin 6, γ' j • β j) (e c)) ∧
      Ψ.range = rootSpan τ K (rootsOfFam β Set.univ) ∧
      Ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup k) := by
  classical
  haveI : CharP k 2 := (RingHom.charP_iff_charP (e : k →+* K) 2).2 inferInstance
  let Φ : CFSG.LieType.Steinberg.RootSystem (Fin Tag.E6.rank) :=
    CFSG.LieType.Steinberg.RootSystem.ofCartan (e6Datum k).isFiniteType (e6Datum k).divisible
  have hΦ : Φ.roots = {γ | IsRoot Tag.E6 γ} := roots_eq (τ := .E6) isFiniteType_cartan_E6
  let y : (Fin Tag.E6.rank → ℤ) → k → ModGL τ K :=
    fun γ' c => pinnedX τ K (rckPn_L β γ') (e c)
  have hys : CFSG.GroupTheory.GomiLeviExc.IsCharTwoSteinberg Φ.roots y := by
    refine ⟨?_, ?_⟩
    · intro γ' _ c d
      show pinnedX τ K (rckPn_L β γ') (e (c + d)) =
        pinnedX τ K (rckPn_L β γ') (e c) * pinnedX τ K (rckPn_L β γ') (e d)
      rw [map_add, pinnedX_add]
    · intro α hα δ hδ hne c d
      change ⁅pinnedX τ K (rckPn_L β α) (e c), pinnedX τ K (rckPn_L β δ) (e d)⁆ =
        (if α + δ ∈ Φ.roots then pinnedX τ K (rckPn_L β (α + δ)) (e (c * d)) else 1)
      have hα' : IsRoot Tag.E6 α := by rwa [hΦ] at hα
      have hδ' : IsRoot Tag.E6 δ := by rwa [hΦ] at hδ
      have ha : IsRoot τ (rckPn_L β α) := rckPn_L_isRoot hι hα'
      have hb : IsRoot τ (rckPn_L β δ) := rckPn_L_isRoot hι hδ'
      have hne' : rckPn_L β α + rckPn_L β δ ≠ 0 := by
        intro h0
        have hneg : rckPn_L β α = -rckPn_L β δ := by
          rw [eq_neg_iff_add_eq_zero]
          exact h0
        have hαδ : α = -δ := by
          calc α = ι (rckPn_L β α) := (rckPn_iota_L hι hα').symm
            _ = ι (-rckPn_L β δ) := by rw [hneg]
            _ = -ι (rckPn_L β δ) :=
              hι.2.2.2.1 (rckPn_L β δ) (rckPn_L_mem_rootsOfFam hι hδ')
            _ = -δ := by rw [rckPn_iota_L hι hδ']
        exact hne (by rw [hαδ]; abel)
      have hiff : IsRoot τ (rckPn_L β α + rckPn_L β δ) ↔ α + δ ∈ Φ.roots := by
        rw [← rckPn_L_add β α δ]
        constructor
        · intro h
          have h3 : iform (rckPn_L β (α + δ)) (rckPn_L β (α + δ)) = 2 :=
            CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two (Or.inr hτ) h
          rw [rckPn_L_iform_self hι hroot (α + δ)] at h3
          have hroot' : IsRoot Tag.E6 (α + δ) := rckRet_isRoot_E6_of_norm_two h3
          rwa [hΦ]
        · intro h
          have hroot' : IsRoot Tag.E6 (α + δ) := by
            rw [hΦ] at h
            exact h
          exact rckPn_L_isRoot hι hroot'
      have hcomm := rckPn_pinnedX_commutator (K := K) hτ ha hb hne' (e c) (e d)
      rw [hcomm]
      by_cases hr : IsRoot τ (rckPn_L β α + rckPn_L β δ)
      · have hmem : α + δ ∈ Φ.roots := hiff.mp hr
        rw [if_pos hr, if_pos hmem, rckPn_L_add β α δ, map_mul]
      · have hmem : α + δ ∉ Φ.roots := fun h => hr (hiff.mpr h)
        rw [if_neg hr, if_neg hmem]
  have hsl : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 →
      ∀ p ∈ CFSG.LieType.Steinberg.expPairs Φ α β, p = (1, 1) := by
    intro α hα β hβ hne p hp
    have hα' : IsRoot Tag.E6 α := by rwa [hΦ] at hα
    have hβ' : IsRoot Tag.E6 β := by rwa [hΦ] at hβ
    exact ((mem_expPairs_iff posDef_cartan_E6 Φ hΦ hα' hβ' hne p).1 hp).2
  have hxs : CFSG.GroupTheory.GomiLeviExc.IsCharTwoSteinberg Φ.roots (e6Data_valid.xm k) := by
    refine ⟨fun γ _ c d => e6Data_valid.xm_add k γ c d, ?_⟩
    intro α hα β hβ hne c d
    have hα' : IsRoot Tag.E6 α := by rwa [hΦ] at hα
    have hβ' : IsRoot Tag.E6 β := by rwa [hΦ] at hβ
    by_cases hr : IsRoot Tag.E6 (α + β)
    · obtain ⟨σ, hσ, hcomm⟩ := (e6Data_valid.commutator_xm k hα' hβ' hne).1 hr
      rw [if_pos (by rw [hΦ]; exact hr), hcomm]
      congr 1
      rcases hσ with h | h
      · rw [h, one_mul]
      · rw [h, CharTwo.neg_eq, one_mul]
    · rw [if_neg (by rw [hΦ]; exact hr)]
      exact (e6Data_valid.commutator_xm k hα' hβ' hne).2 hr c d
  have hO : Nonempty (CFSG.LieType.Steinberg.CommOrder Φ) := e6_nonempty_commOrder k
  have hx : CFSG.LieType.Steinberg.PresentationB (Φ := Φ) (e6Data_valid.xm k) :=
    e6_presentationB k
  obtain ⟨Ψ, hΨ⟩ :=
    CFSG.GroupTheory.GomiLeviExc.exists_hom_of_isCharTwoSteinberg hsl hO hx hxs hys
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro γ' hγ' c
    exact hΨ γ' (by rw [hΦ]; exact hγ') c
  · rw [CFSG.GroupTheory.GomiLeviExc.range_eq_closure_of_presentationB hO hx Ψ hΨ,
      rckPn_rootSpan_eq_closure e hι]
    congr 1
    ext h
    constructor
    · rintro ⟨γ, hγ, c, rfl⟩
      exact ⟨γ, by rw [hΦ] at hγ; exact hγ, c, rfl⟩
    · rintro ⟨γ', hγ', c, rfl⟩
      exact ⟨γ', by rw [hΦ]; exact hγ', c, rfl⟩
  · refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      (CFSG.LieType.CurtisTits.isQuasisimple_e6 k) ?_
    refine ⟨e6Data_valid.xm k (Pi.single (0 : Fin 6) 1) 1, ?_⟩
    intro h1
    have h2 : pinnedX τ K (rckPn_L β (Pi.single (0 : Fin 6) 1)) (e 1) = 1 := by
      show y (Pi.single (0 : Fin 6) 1) 1 = 1
      rw [← hΨ (Pi.single (0 : Fin 6) 1)
        (by rw [hΦ]; exact isRoot_single Tag.E6 (0 : Fin 6)) 1]
      exact h1
    have h0 : pinnedX τ K (rckPn_L β (Pi.single (0 : Fin 6) 1)) (e 1) =
        pinnedX τ K (rckPn_L β (Pi.single (0 : Fin 6) 1)) 0 := by
      rw [h2, pinnedX_zero]
    have := pinnedX_injective (τ := τ) (R := K) (rckPn_L β (Pi.single (0 : Fin 6) 1)) h0
    rw [map_one] at this
    exact one_ne_zero this

end CFSG.StandardType.RCKRP

end
