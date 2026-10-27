module

public import CFSG.LocalAnalysis.StandardType.GGFieldFiveE8Centralizer
public import CFSG.LocalAnalysis.StandardType.GGFieldFiveE8Classes
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompKac
public import CFSG.LieType.AlgebraicGroups.ToralRootCover
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.OmNonsplit
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace E8TwoFiveFin

@[expose] def rootsL : List (List ℤ) := Tag.E8.artifactRoots

@[expose] def dotL (u v : List ℤ) : ℤ := (List.zipWith (· * ·) u v).sum

@[expose] def cartanL : List (List ℤ) :=
  [[2, 0, -1, 0, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0, 0], [-1, 0, 2, -1, 0, 0, 0, 0],
   [0, -1, -1, 2, -1, 0, 0, 0], [0, 0, 0, -1, 2, -1, 0, 0], [0, 0, 0, 0, -1, 2, -1, 0],
   [0, 0, 0, 0, 0, -1, 2, -1], [0, 0, 0, 0, 0, 0, -1, 2]]

theorem isRoot_iff_mem_rootsL (γ : Fin 8 → ℤ) :
    IsRoot Tag.E8 γ ↔ List.ofFn γ ∈ rootsL := by
  unfold rootsL
  exact isRoot_iff_mem_artifactRoots

theorem dotProduct_eq_dotL (γ μ : Fin 8 → ℤ) : γ ⬝ᵥ μ = dotL (List.ofFn γ) (List.ofFn μ) := by
  have hzip : List.zipWith (· * ·) (List.ofFn γ) (List.ofFn μ) =
      List.ofFn (fun i => γ i * μ i) := by
    apply List.ext_getElem
    · rw [List.length_zipWith, List.length_ofFn, List.length_ofFn, List.length_ofFn]
      simp
    · intro n h1 h2
      rw [List.getElem_zipWith, List.getElem_ofFn, List.getElem_ofFn, List.getElem_ofFn]
  rw [dotL, hzip, List.sum_ofFn]
  simp only [dotProduct]

private theorem symmCartan_eq_cartanL (i j : Fin 8) :
    Tag.E8.symmetrizedCartan i j = (cartanL.getD i.val []).getD j.val 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem symmCartan_E8_symm (i j : Fin 8) :
    Tag.E8.symmetrizedCartan i j = Tag.E8.symmetrizedCartan j i := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem iform_eq_dotL_fin8 (β γ : Fin 8 → ℤ) :
    iform (τ := Tag.E8) β γ =
      dotL (cartanL.map fun row => dotL row (List.ofFn β)) (List.ofFn γ) := by
  have hw : cartanL.map (fun row => dotL row (List.ofFn β)) =
      List.ofFn (fun i : Fin 8 => ∑ j : Fin 8, Tag.E8.symmetrizedCartan i j * β j) := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_ofFn]
      decide +kernel
    · intro n h1 h2
      have hn : n < 8 := by simpa using h2
      interval_cases n <;>
        rw [List.getElem_map, List.getElem_ofFn] <;>
        rw [show List.ofFn β = [β 0, β 1, β 2, β 3, β 4, β 5, β 6, β 7] from rfl] <;>
        simp only [cartanL, dotL, List.getElem_cons_zero, List.getElem_cons_succ,
          symmCartan_eq_cartanL] <;>
        norm_num [Fin.sum_univ_eight] <;>
        ring_nf
  rw [hw]
  rw [show dotL (List.ofFn (fun i : Fin 8 => ∑ j : Fin 8, Tag.E8.symmetrizedCartan i j * β j))
        (List.ofFn γ) =
      (fun i : Fin 8 => ∑ j : Fin 8, Tag.E8.symmetrizedCartan i j * β j) ⬝ᵥ γ from
    (dotProduct_eq_dotL _ _).symm]
  simp only [dotProduct, iform, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmCartan_E8_symm j i]
  ring

theorem iform_eq_dotL (β γ : Fin Tag.E8.rank → ℤ) :
    iform β γ = dotL (cartanL.map fun row => dotL row (List.ofFn β)) (List.ofFn γ) :=
  iform_eq_dotL_fin8 β γ

@[expose] def cntVal (μ : List ℤ) (l : ℤ) : ℕ := rootsL.countP fun γ => dotL γ μ % 5 == l

@[expose] def vCount (μ : List ℤ) (l c : ℤ) : ℕ :=
  ((rootsL.filter fun β => dotL β μ % 5 == 0).map fun β =>
    let bβ := cartanL.map fun row => dotL row β
    rootsL.countP fun γ => dotL γ μ % 5 == l && dotL bβ γ == c).sum

@[expose] def excl (μ : List ℤ) : Bool := cntVal μ 1 != cntVal μ 2 || vCount μ 1 0 != vCount μ 2 0

@[expose] def kacCands : List (List ℤ) :=
  [[0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,1], [0,0,0,0,0,0,0,2], [0,0,0,0,0,0,1,0],
   [0,0,0,0,0,0,1,1], [0,0,0,0,0,1,0,0], [0,0,0,0,1,0,0,0], [0,0,1,0,0,0,0,0],
   [0,1,0,0,0,0,0,0], [0,1,0,0,0,0,0,1], [1,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,1],
   [1,0,0,0,0,0,1,0], [1,1,0,0,0,0,0,0], [2,0,0,0,0,0,0,0]]

theorem fstable_cands :
    kacCands.tail.filter (fun μ => !excl μ) = [[0,0,0,0,1,0,0,0], [1,0,0,0,0,0,0,1]] := by
  decide +kernel

theorem normal_mem_kacCands (μ : Fin 8 → ℤ)
    (hμ : kacE8.IsNormal 5 μ) : List.ofFn μ ∈ kacCands := by
  obtain ⟨hμ0, hμ5⟩ := hμ
  have h0 : 0 ≤ μ 0 := hμ0 (0 : Fin 8)
  have h1 : 0 ≤ μ 1 := hμ0 (1 : Fin 8)
  have h2 : 0 ≤ μ 2 := hμ0 (2 : Fin 8)
  have h3 : 0 ≤ μ 3 := hμ0 (3 : Fin 8)
  have h4 : 0 ≤ μ 4 := hμ0 (4 : Fin 8)
  have h5 : 0 ≤ μ 5 := hμ0 (5 : Fin 8)
  have h6 : 0 ≤ μ 6 := hμ0 (6 : Fin 8)
  have h7 : 0 ≤ μ 7 := hμ0 (7 : Fin 8)
  have hdot : kacE8.θ ⬝ᵥ μ =
      2 * μ 0 + 3 * μ 1 + 4 * μ 2 + 6 * μ 3 + 5 * μ 4 + 4 * μ 5 + 3 * μ 6 + 2 * μ 7 := by
    change (∑ i : Fin 8, ![2, 3, 4, 6, 5, 4, 3, 2] i * μ i) =
      2 * μ 0 + 3 * μ 1 + 4 * μ 2 + 6 * μ 3 + 5 * μ 4 + 4 * μ 5 + 3 * μ 6 + 2 * μ 7
    rw [Fin.sum_univ_eight]
    norm_num
  rw [hdot] at hμ5
  have b0 : μ 0 ≤ 2 := by omega
  have b1 : μ 1 ≤ 1 := by omega
  have b2 : μ 2 ≤ 1 := by omega
  have b3 : μ 3 ≤ 0 := by omega
  have b4 : μ 4 ≤ 1 := by omega
  have b5 : μ 5 ≤ 1 := by omega
  have b6 : μ 6 ≤ 1 := by omega
  have b7 : μ 7 ≤ 2 := by omega
  rw [show List.ofFn μ = [μ 0, μ 1, μ 2, μ 3, μ 4, μ 5, μ 6, μ 7] from rfl]
  interval_cases μ 0 <;> interval_cases μ 1 <;> interval_cases μ 2 <;> interval_cases μ 3 <;>
    interval_cases μ 4 <;> interval_cases μ 5 <;> interval_cases μ 6 <;> interval_cases μ 7 <;>
    first | omega | decide

private def toFn (l : List ℤ) : Fin 8 → ℤ := fun i => l.getD i.val 0

private theorem toFn_ofFn (γ : Fin 8 → ℤ) : toFn (List.ofFn γ) = γ := by
  funext i
  simp only [toFn]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn]

private theorem ofFn_toFn {l : List ℤ} (hl : l.length = 8) : List.ofFn (toFn l) = l := by
  apply List.ext_getElem
  · rw [List.length_ofFn, hl]
  · intro n h1 h2
    rw [List.getElem_ofFn]
    simp only [toFn]
    rw [List.getD_eq_getElem l 0 h2]

private theorem rootsL_nodup : rootsL.Nodup :=
  nodup_artifactRoots Tag.E8

private theorem countP_toFinset (q : List ℤ → Bool) :
    rootsL.countP q = (rootsL.toFinset.filter (fun l => q l = true)).card := by
  rw [List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (List.Nodup.filter q rootsL_nodup), List.toFinset_filter]

private def CL (μ : Fin 8 → ℤ) (l : ℤ) : Finset (List ℤ) :=
  rootsL.toFinset.filter fun γ => dotL γ (List.ofFn μ) % 5 = l

private def VLcond (μ : Fin 8 → ℤ) (l c : ℤ) (p : List ℤ × List ℤ) : Prop :=
  dotL p.2 (List.ofFn μ) % 5 = l ∧
    dotL (cartanL.map fun row => dotL row p.1) p.2 = c

private instance instDecidablePredVLcond (μ : Fin 8 → ℤ) (l c : ℤ) :
    DecidablePred (VLcond μ l c) :=
  fun p => by unfold VLcond; infer_instance

private def BD (μ : Fin 8 → ℤ) (l c : ℤ) (β : List ℤ) : Finset (List ℤ) :=
  rootsL.toFinset.filter fun γ => VLcond μ l c (β, γ)

private theorem cntVal_eq (μ : Fin 8 → ℤ) (l : ℤ) :
    cntVal (List.ofFn μ) l = (CL μ l).card := by
  unfold cntVal CL
  rw [countP_toFinset]
  apply congrArg Finset.card
  apply Finset.ext
  intro γ
  simp only [Finset.mem_filter, beq_iff_eq]

private theorem vCount_eq (μ : Fin 8 → ℤ) (l c : ℤ) :
    vCount (List.ofFn μ) l c = ∑ β ∈ CL μ 0, (BD μ l c β).card := by
  classical
  unfold vCount
  rw [← List.sum_toFinset _ (List.Nodup.filter _ rootsL_nodup), List.toFinset_filter]
  rw [Finset.sum_filter]
  have hinner : ∀ β ∈ rootsL.toFinset,
      rootsL.countP (fun γ => dotL γ (List.ofFn μ) % 5 == l &&
          dotL (cartanL.map fun row => dotL row β) γ == c) =
      (BD μ l c β).card := by
    intro β hβ
    rw [countP_toFinset, BD]
    apply congrArg Finset.card
    apply Finset.ext
    intro γ
    simp [VLcond]
  rw [Finset.sum_congr rfl (fun β hβ => by rw [hinner β hβ])]
  rw [← Finset.sum_filter]
  have hA : rootsL.toFinset.filter (fun β => (dotL β (List.ofFn μ) % 5 == 0) = true) =
      CL μ 0 := by
    unfold CL
    apply Finset.filter_congr
    intro β hβ
    exact beq_iff_eq
  rw [hA]

theorem counts_eq {μ : Fin 8 → ℤ}
    (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (hσr : ∀ γ, IsRoot Tag.E8 (σ γ) ↔ IsRoot Tag.E8 γ)
    (hσi : ∀ γ δ, iform (σ γ) (σ δ) = iform γ δ)
    (hσμ : ∀ δ, IsRoot Tag.E8 δ → (σ δ ⬝ᵥ μ) ≡ 2 * (δ ⬝ᵥ μ) [ZMOD 5]) :
    cntVal (List.ofFn μ) 1 = cntVal (List.ofFn μ) 2 ∧
      vCount (List.ofFn μ) 1 0 = vCount (List.ofFn μ) 2 0 := by
  let σ8 : Equiv.Perm (Fin 8 → ℤ) := σ
  have hσr8 : ∀ γ : Fin 8 → ℤ, IsRoot Tag.E8 (σ8 γ) ↔ IsRoot Tag.E8 γ := hσr
  have hσi8 : ∀ γ δ : Fin 8 → ℤ,
      iform (τ := Tag.E8) (σ8 γ) (σ8 δ) = iform (τ := Tag.E8) γ δ := hσi
  have hσμ8 : ∀ δ : Fin 8 → ℤ, IsRoot Tag.E8 δ →
      (σ8 δ ⬝ᵥ μ) ≡ 2 * (δ ⬝ᵥ μ) [ZMOD 5] := hσμ
  let σL : List ℤ → List ℤ := fun l => List.ofFn (σ8 (toFn l))
  have htoFn_σL : ∀ l, toFn (σL l) = σ8 (toFn l) := fun l => toFn_ofFn _
  have hσL_mem : ∀ l ∈ rootsL, σL l ∈ rootsL := by
    intro l hl
    show List.ofFn (σ8 (toFn l)) ∈ rootsL
    rw [← isRoot_iff_mem_rootsL, hσr8 (toFn l), isRoot_iff_mem_rootsL,
      ofFn_toFn (length_of_mem_artifactRoots hl)]
    exact hl
  have hσL_inj : Set.InjOn σL {l : List ℤ | l ∈ rootsL} := by
    intro l hl l' hl' h
    have h1 : σ8 (toFn l) = σ8 (toFn l') := List.ofFn_injective h
    have h2 : toFn l = toFn l' := σ8.injective h1
    rw [← ofFn_toFn (length_of_mem_artifactRoots hl), h2,
      ofFn_toFn (length_of_mem_artifactRoots hl')]
  have hiform_σL : ∀ β γ, β ∈ rootsL → γ ∈ rootsL →
      dotL (cartanL.map fun row => dotL row (σL β)) (σL γ) =
      dotL (cartanL.map fun row => dotL row β) γ := by
    intro β γ hβ hγ
    have hL : dotL (cartanL.map fun row => dotL row (σL β)) (σL γ) =
        iform (τ := Tag.E8) (toFn (σL β)) (toFn (σL γ)) := by
      have h := iform_eq_dotL_fin8 (toFn (σL β)) (toFn (σL γ))
      rw [ofFn_toFn (length_of_mem_artifactRoots (hσL_mem β hβ)),
        ofFn_toFn (length_of_mem_artifactRoots (hσL_mem γ hγ))] at h
      exact h.symm
    have hR : dotL (cartanL.map fun row => dotL row β) γ =
        iform (τ := Tag.E8) (toFn β) (toFn γ) := by
      have h := iform_eq_dotL_fin8 (toFn β) (toFn γ)
      rw [ofFn_toFn (length_of_mem_artifactRoots hβ),
        ofFn_toFn (length_of_mem_artifactRoots hγ)] at h
      exact h.symm
    rw [hL, hR, htoFn_σL β, htoFn_σL γ]
    exact hσi8 (toFn β) (toFn γ)
  have hCL_mapsto : ∀ l γ, γ ∈ CL μ l → σL γ ∈ CL μ (2 * l % 5) := by
    intro l γ hγ
    rw [CL, Finset.mem_filter] at hγ ⊢
    obtain ⟨hγroot, hγl⟩ := hγ
    have hγroot' : γ ∈ rootsL := List.mem_toFinset.mp hγroot
    refine ⟨?_, ?_⟩
    · rw [List.mem_toFinset]
      exact hσL_mem γ hγroot'
    · have hisRoot : IsRoot Tag.E8 (toFn γ) := by
        rw [isRoot_iff_mem_rootsL, ofFn_toFn (length_of_mem_artifactRoots hγroot')]
        exact hγroot'
      have hmod := hσμ8 (toFn γ) hisRoot
      have hdot : toFn γ ⬝ᵥ μ = dotL γ (List.ofFn μ) := by
        rw [← ofFn_toFn (length_of_mem_artifactRoots hγroot')]
        exact dotProduct_eq_dotL (toFn γ) μ
      have hval : dotL (σL γ) (List.ofFn μ) = σ8 (toFn γ) ⬝ᵥ μ := by
        change dotL (List.ofFn (σ8 (toFn γ))) (List.ofFn μ) = σ8 (toFn γ) ⬝ᵥ μ
        exact (dotProduct_eq_dotL (σ8 (toFn γ)) μ).symm
      rw [hval, Int.ModEq.eq hmod, hdot, Int.mul_emod, hγl]
      norm_num
  have hCL_le : ∀ l : ℤ, (CL μ l).card ≤ (CL μ (2 * l % 5)).card := by
    intro l
    exact Finset.card_le_card_of_injOn σL (fun γ hγ => hCL_mapsto l γ hγ)
      (hσL_inj.mono fun x hx => List.mem_toFinset.mp (Finset.mem_filter.mp hx).1)
  have hCL1 : (CL μ 1).card ≤ (CL μ 2).card := by
    have h := hCL_le 1
    norm_num at h
    exact h
  have hCL2 : (CL μ 2).card ≤ (CL μ 4).card := by
    have h := hCL_le 2
    norm_num at h
    exact h
  have hCL4 : (CL μ 4).card ≤ (CL μ 3).card := by
    have h := hCL_le 4
    norm_num at h
    exact h
  have hCL3 : (CL μ 3).card ≤ (CL μ 1).card := by
    have h := hCL_le 3
    norm_num at h
    exact h
  have hC12 : (CL μ 1).card = (CL μ 2).card :=
    le_antisymm hCL1 (hCL2.trans (hCL4.trans hCL3))
  have hB_mapsto : ∀ l β, β ∈ CL μ 0 → ∀ γ ∈ BD μ l 0 β, σL γ ∈ BD μ (2 * l % 5) 0 (σL β) := by
    intro l β hβ γ hγ
    rw [BD, Finset.mem_filter] at hγ ⊢
    unfold VLcond at hγ ⊢
    obtain ⟨hγroot, hγl, hγc⟩ := hγ
    have hβroot : β ∈ rootsL := List.mem_toFinset.mp (Finset.mem_filter.mp hβ).1
    have hγroot' : γ ∈ rootsL := List.mem_toFinset.mp hγroot
    refine ⟨?_, ?_, ?_⟩
    · rw [List.mem_toFinset]
      exact hσL_mem γ hγroot'
    · have hisRoot : IsRoot Tag.E8 (toFn γ) := by
        rw [isRoot_iff_mem_rootsL, ofFn_toFn (length_of_mem_artifactRoots hγroot')]
        exact hγroot'
      have hmod := hσμ8 (toFn γ) hisRoot
      have hdot : toFn γ ⬝ᵥ μ = dotL γ (List.ofFn μ) := by
        rw [← ofFn_toFn (length_of_mem_artifactRoots hγroot')]
        exact dotProduct_eq_dotL (toFn γ) μ
      have hval : dotL (σL γ) (List.ofFn μ) = σ8 (toFn γ) ⬝ᵥ μ := by
        change dotL (List.ofFn (σ8 (toFn γ))) (List.ofFn μ) = σ8 (toFn γ) ⬝ᵥ μ
        exact (dotProduct_eq_dotL (σ8 (toFn γ)) μ).symm
      rw [hval, Int.ModEq.eq hmod, hdot, Int.mul_emod, hγl]
      norm_num
    · rw [hiform_σL β γ hβroot hγroot']
      exact hγc
  have hB_le : ∀ l : ℤ, (∑ β ∈ CL μ 0, (BD μ l 0 β).card) ≤
      ∑ β ∈ CL μ 0, (BD μ (2 * l % 5) 0 (σL β)).card := by
    intro l
    apply Finset.sum_le_sum
    intro β hβ
    apply Finset.card_le_card_of_injOn σL
    · intro γ hγ
      exact hB_mapsto l β hβ γ hγ
    · exact hσL_inj.mono fun x hx =>
        List.mem_toFinset.mp (Finset.mem_filter.mp hx).1
  have hreindex : ∀ l : ℤ, (∑ β ∈ CL μ 0, (BD μ (2 * l % 5) 0 (σL β)).card) =
      ∑ β ∈ CL μ 0, (BD μ (2 * l % 5) 0 β).card := by
    intro l
    have hinj : Set.InjOn σL ↑(CL μ 0) :=
      hσL_inj.mono fun x hx => List.mem_toFinset.mp (Finset.mem_filter.mp hx).1
    have himg : (CL μ 0).image σL = CL μ 0 := by
      apply Finset.eq_of_subset_of_card_le
      · rw [Finset.image_subset_iff]
        intro β hβ
        exact hCL_mapsto 0 β hβ
      · rw [Finset.card_image_of_injOn hinj]
    rw [← Finset.sum_image (g := σL) (f := fun β => (BD μ (2 * l % 5) 0 β).card) hinj, himg]
  have hV1 : (∑ β ∈ CL μ 0, (BD μ 1 0 β).card) ≤ ∑ β ∈ CL μ 0, (BD μ 2 0 β).card :=
    (hB_le 1).trans (le_of_eq (hreindex 1))
  have hV2 : (∑ β ∈ CL μ 0, (BD μ 2 0 β).card) ≤ ∑ β ∈ CL μ 0, (BD μ 4 0 β).card :=
    (hB_le 2).trans (le_of_eq (hreindex 2))
  have hV4 : (∑ β ∈ CL μ 0, (BD μ 4 0 β).card) ≤ ∑ β ∈ CL μ 0, (BD μ 3 0 β).card :=
    (hB_le 4).trans (le_of_eq (hreindex 4))
  have hV3 : (∑ β ∈ CL μ 0, (BD μ 3 0 β).card) ≤ ∑ β ∈ CL μ 0, (BD μ 1 0 β).card :=
    (hB_le 3).trans (le_of_eq (hreindex 3))
  have hV12 : (∑ β ∈ CL μ 0, (BD μ 1 0 β).card) = ∑ β ∈ CL μ 0, (BD μ 2 0 β).card :=
    le_antisymm hV1 (hV2.trans (hV4.trans hV3))
  constructor
  · rw [cntVal_eq μ 1, cntVal_eq μ 2]
    exact hC12
  · rw [vCount_eq μ 1 0, vCount_eq μ 2 0]
    exact hV12

@[expose] def vecOf (l : List ℤ) : Fin Tag.E8.rank → ℤ := fun i => l.getD i 0

@[expose] def formL (x y : List ℤ) : ℤ := dotL (cartanL.map fun row => dotL row x) y

theorem length_of_mem_rootsL {l : List ℤ} (h : l ∈ rootsL) : l.length = 8 :=
  length_of_mem_artifactRoots h

theorem vecOf_ofFn (γ : Fin Tag.E8.rank → ℤ) : vecOf (List.ofFn γ) = γ := by
  funext i
  simp [vecOf, List.getD_eq_getElem?_getD]

theorem ofFn_vecOf {l : List ℤ} (h : l.length = 8) : List.ofFn (vecOf l) = l := by
  refine List.ext_getElem (by simp [h]; rfl) fun n h1 h2 => ?_
  simp [vecOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem iform_vecOf {x y : List ℤ} (hx : x ∈ rootsL) (hy : y ∈ rootsL) :
    iform (vecOf x) (vecOf y) = formL x y := by
  rw [iform_eq_dotL, ofFn_vecOf (length_of_mem_rootsL hx), ofFn_vecOf (length_of_mem_rootsL hy)]
  rfl

theorem isRoot_vecOf {l : List ℤ} (h : l ∈ rootsL) :
    IsRoot Tag.E8 (vecOf l) := by
  have h2 : List.ofFn (n := Tag.E8.rank) (vecOf l) ∈ rootsL := by
    rw [ofFn_vecOf (length_of_mem_rootsL h)]
    exact h
  exact (isRoot_iff_mem_rootsL _).2 h2

theorem forall_root_iff (q : (Fin Tag.E8.rank → ℤ) → Prop) :
    (∀ γ, IsRoot Tag.E8 γ → q γ) ↔ ∀ l ∈ rootsL, q (vecOf l) := by
  constructor
  · intro H l hl
    exact H _ (isRoot_vecOf hl)
  · intro H γ hγ
    have h1 : List.ofFn (n := Tag.E8.rank) γ ∈ rootsL := (isRoot_iff_mem_rootsL γ).1 hγ
    have h2 := H _ h1
    rwa [vecOf_ofFn] at h2

theorem exists_root_iff (q : (Fin Tag.E8.rank → ℤ) → Prop) :
    (∃ γ, IsRoot Tag.E8 γ ∧ q γ) ↔ ∃ l ∈ rootsL, q (vecOf l) := by
  constructor
  · rintro ⟨γ, hγ, hq⟩
    have h1 : List.ofFn (n := Tag.E8.rank) γ ∈ rootsL := (isRoot_iff_mem_rootsL γ).1 hγ
    exact ⟨_, h1, by rwa [vecOf_ofFn]⟩
  · rintro ⟨l, hl, hq⟩
    exact ⟨_, isRoot_vecOf hl, hq⟩

theorem ncard_root_filter (P : (Fin Tag.E8.rank → ℤ) → Prop)
    [DecidablePred fun l : List ℤ => P (vecOf l)] :
    {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ ∧ P γ}.ncard =
      (rootsL.filter fun l => decide (P (vecOf l))).length := by
  have hset : {γ : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 γ ∧ P γ} =
      vecOf '' {l | l ∈ rootsL ∧ P (vecOf l)} := by
    ext γ
    constructor
    · rintro ⟨hγ, hP⟩
      have h1 : List.ofFn (n := Tag.E8.rank) γ ∈ rootsL := (isRoot_iff_mem_rootsL γ).1 hγ
      exact ⟨List.ofFn γ, ⟨h1, by rwa [vecOf_ofFn]⟩, vecOf_ofFn γ⟩
    · rintro ⟨l, ⟨hl, hP⟩, rfl⟩
      exact ⟨isRoot_vecOf hl, hP⟩
  have hinj : Set.InjOn vecOf {l | l ∈ rootsL ∧ P (vecOf l)} := by
    intro l₁ h₁ l₂ h₂ h
    rw [← ofFn_vecOf (length_of_mem_rootsL h₁.1), ← ofFn_vecOf (length_of_mem_rootsL h₂.1), h]
  have hfin : {l | l ∈ rootsL ∧ P (vecOf l)} =
      ↑((rootsL.filter fun l => decide (P (vecOf l))).toFinset) := by
    ext l
    simp
  rw [hset, hinj.ncard_image, hfin, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup]
  exact (nodup_artifactRoots Tag.E8).filter _

end E8TwoFiveFin

def e8TwoFiveKac5A : Fin 8 → ℤ := ![0, 0, 0, 0, 1, 0, 0, 0]

def e8TwoFiveKac5B : Fin 8 → ℤ := ![1, 0, 0, 0, 0, 0, 0, 1]

theorem dotProduct_e8TwoFiveKac5A (γ : Fin Tag.E8.rank → ℤ) :
    γ ⬝ᵥ e8TwoFiveKac5A = γ (4 : Fin 8) := by
  show ∑ i : Fin 8, γ i * e8TwoFiveKac5A i = _
  simp [e8TwoFiveKac5A, Fin.sum_univ_eight]

theorem dotProduct_e8TwoFiveKac5B (γ : Fin Tag.E8.rank → ℤ) :
    γ ⬝ᵥ e8TwoFiveKac5B = γ (0 : Fin 8) + γ (7 : Fin 8) := by
  show ∑ i : Fin 8, γ i * e8TwoFiveKac5B i = _
  simp [e8TwoFiveKac5B, Fin.sum_univ_eight]

theorem e8TwoFive_fstable_kac (μ : Fin 8 → ℤ)
    (hμ : kacE8.IsNormal 5 μ) (hμ0 : μ ≠ 0) (σ : Equiv.Perm (Fin Tag.E8.rank → ℤ))
    (hσr : ∀ γ, IsRoot Tag.E8 (σ γ) ↔ IsRoot Tag.E8 γ)
    (hσi : ∀ γ δ, iform (σ γ) (σ δ) = iform γ δ)
    (hσμ : ∀ δ, IsRoot Tag.E8 δ → (σ δ ⬝ᵥ μ) ≡ 2 * (δ ⬝ᵥ μ) [ZMOD 5]) :
    μ = e8TwoFiveKac5A ∨ μ = e8TwoFiveKac5B := by
  have hmem := E8TwoFiveFin.normal_mem_kacCands μ hμ
  have hcnt := E8TwoFiveFin.counts_eq σ hσr hσi hσμ
  have hex : E8TwoFiveFin.excl (List.ofFn μ) = false := by
    unfold E8TwoFiveFin.excl
    rw [hcnt.1, hcnt.2]
    simp
  have hne : List.ofFn μ ≠ [0, 0, 0, 0, 0, 0, 0, 0] := by
    intro h
    apply hμ0
    refine List.ofFn_injective (n := 8) ?_
    rw [h]
    rfl
  have hmem' : List.ofFn μ ∈ E8TwoFiveFin.kacCands.tail := by
    unfold E8TwoFiveFin.kacCands at hmem ⊢
    simp only [List.tail_cons, List.mem_cons] at hmem ⊢
    rcases hmem with h | h
    · exact absurd h hne
    · exact h
  have hfil : List.ofFn μ ∈ E8TwoFiveFin.kacCands.tail.filter (fun μ => !E8TwoFiveFin.excl μ) :=
    List.mem_filter.2 ⟨hmem', by show (!E8TwoFiveFin.excl (List.ofFn μ)) = true; rw [hex]; rfl⟩
  rw [E8TwoFiveFin.fstable_cands] at hfil
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfil
  rcases hfil with h | h
  · left
    exact List.ofFn_injective (n := 8) (by rw [h]; rfl)
  · right
    exact List.ofFn_injective (n := 8) (by rw [h]; rfl)

@[expose] def IsFiveBIn {H : Type} [Group H] (X : Subgroup H) (y : H) (K₀ : Subgroup H) : Prop :=
  IsComponentOf K₀ X ∧ (∀ c ∈ X, ∃ n : ℤ, y ^ n * c ∈ K₀) ∧ Subgroup.center K₀ = ⊥ ∧
    5 ∣ Nat.card K₀ ∧ OmModel (GaloisField 2 1) K₀

theorem IsFiveBIn.comap {G H : Type} [Group G] [Group H] {ψ : H →* G}
    (hψ : Function.Injective ψ) {X K₀ : Subgroup G} {y : H} (hX : X ≤ ψ.range)
    (h : IsFiveBIn X (ψ y) K₀) : IsFiveBIn (X.comap ψ) y (K₀.comap ψ) := by
  have hKr : K₀ ≤ ψ.range := h.1.1.trans hX
  let e : ↥(K₀.comap ψ) ≃* ↥K₀ :=
    (Subgroup.equivMapOfInjective (K₀.comap ψ) ψ hψ).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hKr))
  refine ⟨⟨Subgroup.comap_mono h.1.1, CFSG.Assembly.IsSubnormal.comap ψ h.1.2.1,
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e h.1.2.2⟩, ?_, ?_, ?_, ?_⟩
  ·
    intro c hc
    have hψc : ψ c ∈ X := (Subgroup.mem_comap).mp hc
    obtain ⟨n, hn⟩ := h.2.1 (ψ c) hψc
    refine ⟨n, ?_⟩
    show ψ (y ^ n * c) ∈ K₀
    rw [map_mul, map_zpow]
    exact hn
  ·
    have hmap : Subgroup.map (e : ↥(K₀.comap ψ) →* ↥K₀)
        (Subgroup.center ↥(K₀.comap ψ)) = ⊥ := by
      rw [Subgroup.map_center_eq e, h.2.2.1]
    have hle := (Subgroup.map_eq_bot_iff (Subgroup.center ↥(K₀.comap ψ))).mp hmap
    have hker : (e : ↥(K₀.comap ψ) →* ↥K₀).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr e.injective
    rw [hker, le_bot_iff] at hle
    exact hle
  ·
    rw [Nat.card_congr e.toEquiv]
    exact h.2.2.2.1
  ·
    exact OmModel.of_mulEquiv e h.2.2.2.2

theorem IsFiveB.not_isQuasisimple_centralizer {H : Type} [Group H] {y : H} {K₀ : Subgroup H}
    (h : IsFiveB y K₀) (hy : y ≠ 1) : ¬ IsQuasisimple ↥(Subgroup.centralizer {y}) := by
  intro hJ
  have hle : Subgroup.centralizer ({y} : Set H) ≤ K₀ :=
    le_of_isFiveB_of_isQuasisimple h le_rfl hJ
  have hyC : y ∈ Subgroup.centralizer ({y} : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rfl
  have hyK : y ∈ K₀ := hle hyC
  have hycenter : (⟨y, hyK⟩ : ↥K₀) ∈ Subgroup.center ↥K₀ := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (h.1.1 k.2) y (Set.mem_singleton y)).symm
  have hy1 : (⟨y, hyK⟩ : ↥K₀) = 1 := by
    have hc := hycenter
    rw [h.2.2.1, Subgroup.mem_bot] at hc
    exact hc
  exact hy (Subtype.ext_iff.mp hy1)

private theorem card_zmod5_solutions :
    ∀ x y : ZMod 5,
      (Finset.univ.filter fun p : ZMod 5 × ZMod 5 =>
        p ≠ (0, 0) ∧ p.1 * x + p.2 * y = 0).card = if x = 0 ∧ y = 0 then 24 else 4 := by
  decide +kernel

private theorem card_nonzero_zmod5_pairs :
    (Finset.univ.filter fun p : ZMod 5 × ZMod 5 => p ≠ (0, 0)).card = 24 := by
  decide +kernel

theorem e8TwoFive_plane_root_count {R : Type} [Fintype R] [DecidableEq R]
    (hR : Fintype.card R = 240) (u v : R → ZMod 5)
    (h : ∀ i j : ZMod 5, (i, j) ≠ (0, 0) →
      (Finset.univ.filter fun r => i * u r + j * v r = 0).card = 40) :
    ∀ r, ¬ (u r = 0 ∧ v r = 0) := by
  classical
  set P : Finset (ZMod 5 × ZMod 5) := Finset.univ.filter fun p => p ≠ (0, 0) with hP
  let D : ℕ := Finset.sum P fun p => Finset.sum Finset.univ fun r =>
    if p.1 * u r + p.2 * v r = 0 then 1 else 0
  have hD1 : D = Finset.sum P (fun p =>
      (Finset.univ.filter fun r => p.1 * u r + p.2 * v r = 0).card) := by
    dsimp only [D]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  have hD2 : D = Finset.sum Finset.univ (fun r : R =>
      (P.filter fun p => p.1 * u r + p.2 * v r = 0).card) := by
    dsimp only [D]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.card_filter]
  have hdouble : Finset.sum P (fun p =>
      (Finset.univ.filter fun r => p.1 * u r + p.2 * v r = 0).card)
      = Finset.sum Finset.univ (fun r : R =>
        (P.filter fun p => p.1 * u r + p.2 * v r = 0).card) :=
    hD1.symm.trans hD2
  have hPcard : P.card = 24 := by rw [hP]; exact card_nonzero_zmod5_pairs
  have hfirst : Finset.sum P (fun p =>
      (Finset.univ.filter fun r => p.1 * u r + p.2 * v r = 0).card) = 960 := by
    have h40 : ∀ p ∈ P,
        (Finset.univ.filter fun r => p.1 * u r + p.2 * v r = 0).card = 40 := by
      intro p hp
      rw [hP] at hp
      exact h p.1 p.2 (by simpa using (Finset.mem_filter.mp hp).2)
    calc Finset.sum P (fun p => (Finset.univ.filter fun r => p.1 * u r + p.2 * v r = 0).card)
        = Finset.sum P (fun _ => (40 : ℕ)) := Finset.sum_congr rfl h40
      _ = 960 := by rw [Finset.sum_const, hPcard]; norm_num
  have hper : ∀ r : R, (P.filter fun p => p.1 * u r + p.2 * v r = 0).card
      = if u r = 0 ∧ v r = 0 then 24 else 4 := by
    intro r
    rw [hP, Finset.filter_filter]
    exact card_zmod5_solutions (u r) (v r)
  have hsecond : Finset.sum Finset.univ (fun r : R =>
      (P.filter fun p => p.1 * u r + p.2 * v r = 0).card)
      = 960 + 20 * (Finset.univ.filter fun r => u r = 0 ∧ v r = 0).card := by
    have hpt : ∀ r : R, (if u r = 0 ∧ v r = 0 then (24 : ℕ) else 4)
        = 4 + (if u r = 0 ∧ v r = 0 then 20 else 0) := by
      intro r
      split_ifs <;> norm_num
    calc Finset.sum Finset.univ (fun r : R =>
            (P.filter fun p => p.1 * u r + p.2 * v r = 0).card)
        = Finset.sum Finset.univ (fun r : R =>
            (if u r = 0 ∧ v r = 0 then (24 : ℕ) else 4)) :=
          Finset.sum_congr rfl fun r _ => hper r
      _ = Finset.sum Finset.univ (fun r : R =>
            (4 + (if u r = 0 ∧ v r = 0 then 20 else 0))) :=
          Finset.sum_congr rfl fun r _ => hpt r
      _ = Finset.sum Finset.univ (fun _ : R => (4 : ℕ)) +
            Finset.sum Finset.univ (fun r : R =>
              if u r = 0 ∧ v r = 0 then 20 else 0) :=
          Finset.sum_add_distrib
      _ = 960 + 20 * (Finset.univ.filter fun r => u r = 0 ∧ v r = 0).card := by
          have h4 : Finset.sum Finset.univ (fun _ : R => (4 : ℕ)) = 960 := by
            rw [Finset.sum_const, Finset.card_univ, hR]; norm_num
          have h20 : Finset.sum Finset.univ (fun r : R =>
              if u r = 0 ∧ v r = 0 then 20 else 0)
              = 20 * (Finset.univ.filter fun r => u r = 0 ∧ v r = 0).card := by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
          rw [h4, h20]
  have hkey : (Finset.univ.filter fun r => u r = 0 ∧ v r = 0).card = 0 := by
    have hEq : (960 : ℕ) = 960 + 20 * (Finset.univ.filter fun r => u r = 0 ∧ v r = 0).card :=
      hfirst.symm.trans (hdouble.trans hsecond)
    omega
  intro r hr
  have hmem : r ∈ Finset.univ.filter (fun r => u r = 0 ∧ v r = 0) := by
    rw [Finset.mem_filter]; exact ⟨Finset.mem_univ r, hr⟩
  rw [Finset.card_eq_zero.mp hkey] at hmem
  simpa using hmem

private theorem rootChar_pow_five_eq_one {τ : Tag} {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} (ha : ∀ i, a i ^ 5 = 1) (v : Fin τ.rank → ℤ) :
    rootChar a v ^ 5 = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast (a i ^ v i) 5, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, ha i, one_zpow]

private theorem rootChar_mul_pow {τ : Tag} {L : Type} [Field L]
    (a b : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ) (I J : ℕ) :
    rootChar (a ^ I * b ^ J) v = rootChar a v ^ I * rootChar b v ^ J := by
  rw [rootChar]
  simp only [Pi.mul_apply, Pi.pow_apply, mul_zpow]
  rw [Finset.prod_mul_distrib]
  simp only [rootChar]
  congr 1
  · rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast (a i) I, ← zpow_mul, mul_comm (I : ℤ) (v i), zpow_mul, zpow_natCast]
  · rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast (b i) J, ← zpow_mul, mul_comm (J : ℤ) (v i), zpow_mul, zpow_natCast]

theorem e8TwoFive_plane_roots_nontrivial {L : Type} [Field L]
    [IsAlgClosed L] (h5 : (5 : L) ≠ 0)
    {a b : Fin Tag.E8.rank → Lˣ} (ha : ∀ i, a i ^ 5 = 1) (hb : ∀ i, b i ^ 5 = 1)
    (h : ∀ i j : ℕ, ¬ (5 ∣ i ∧ 5 ∣ j) →
      (kernelRoots (rootCharHom (a ^ i * b ^ j))).ncard = 40) :
    ∀ β, IsRoot Tag.E8 β → rootChar a β ≠ 1 ∨ rootChar b β ≠ 1 := by
  classical
  haveI : NeZero ((5 : ℕ) : L) := ⟨by simpa using h5⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  have hunit : IsUnit ζ := hζ.isUnit (by norm_num)
  let ζu : Lˣ := hunit.unit
  have hζu : IsPrimitiveRoot ζu 5 := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    change IsPrimitiveRoot (↑hunit.unit : L) 5
    rw [hunit.unit_spec]
    exact hζ
  have hex_a : ∀ β : Fin Tag.E8.rank → ℤ, ∃ k < 5, ζu ^ k = rootChar a β := by
    intro β
    exact hζu.eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity 5 (rootChar a β)).mpr (rootChar_pow_five_eq_one ha β))
  have hex_b : ∀ β : Fin Tag.E8.rank → ℤ, ∃ k < 5, ζu ^ k = rootChar b β := by
    intro β
    exact hζu.eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity 5 (rootChar b β)).mpr (rootChar_pow_five_eq_one hb β))
  let ka : (Fin Tag.E8.rank → ℤ) → ℕ := fun β => Classical.choose (hex_a β)
  let kb : (Fin Tag.E8.rank → ℤ) → ℕ := fun β => Classical.choose (hex_b β)
  have hka : ∀ β, ζu ^ (ka β) = rootChar a β := fun β => (Classical.choose_spec (hex_a β)).2
  have hkb : ∀ β, ζu ^ (kb β) = rootChar b β := fun β => (Classical.choose_spec (hex_b β)).2
  let uval : (Fin Tag.E8.rank → ℤ) → ZMod 5 := fun β => (ka β : ZMod 5)
  let vval : (Fin Tag.E8.rank → ℤ) → ZMod 5 := fun β => (kb β : ZMod 5)
  have hu_zero : ∀ β, uval β = 0 ↔ rootChar a β = 1 := by
    intro β
    dsimp only [uval]
    rw [ZMod.natCast_eq_zero_iff, ← hka β]
    exact (hζu.pow_eq_one_iff_dvd (ka β)).symm
  have hv_zero : ∀ β, vval β = 0 ↔ rootChar b β = 1 := by
    intro β
    dsimp only [vval]
    rw [ZMod.natCast_eq_zero_iff, ← hkb β]
    exact (hζu.pow_eq_one_iff_dvd (kb β)).symm
  let R := {β : Fin Tag.E8.rank → ℤ // IsRoot Tag.E8 β}
  have hRcard : Fintype.card R = 240 := by
    dsimp only [R]
    rw [card_isRoot Tag.E8]
    rfl
  have hcount : ∀ i j : ZMod 5, (i, j) ≠ (0, 0) →
      (Finset.univ.filter fun r : R => i * uval r.1 + j * vval r.1 = 0).card = 40 := by
    intro i j hij
    have hnot : ¬ (5 ∣ i.val ∧ 5 ∣ j.val) := by
      rintro ⟨hi, hj⟩
      have hi0 : i = 0 := by
        rw [← ZMod.natCast_zmod_val i]
        exact (ZMod.natCast_eq_zero_iff i.val 5).mpr hi
      have hj0 : j = 0 := by
        rw [← ZMod.natCast_zmod_val j]
        exact (ZMod.natCast_eq_zero_iff j.val 5).mpr hj
      exact hij (by rw [hi0, hj0])
    have hh := h i.val j.val hnot
    have hS : kernelRoots (rootCharHom (a ^ i.val * b ^ j.val))
        = {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
            i * uval β + j * vval β = 0} := by
      ext β
      rw [kernelRoots_rootCharHom]
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun _ => ?_
      have hL : rootChar (a ^ i.val * b ^ j.val) β = 1 ↔
          5 ∣ (i.val * ka β + j.val * kb β) := by
        rw [rootChar_mul_pow, ← hka β, ← hkb β, ← pow_mul, ← pow_mul, ← pow_add]
        rw [IsPrimitiveRoot.pow_eq_one_iff_dvd hζu]
        rw [mul_comm (ka β) i.val, mul_comm (kb β) j.val]
      have heq : ((i.val * ka β + j.val * kb β : ℕ) : ZMod 5)
          = i * uval β + j * vval β := by
        dsimp only [uval, vval]
        push_cast
        rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j]
      have hR : i * uval β + j * vval β = 0 ↔
          5 ∣ (i.val * ka β + j.val * kb β) := by
        rw [← heq, ZMod.natCast_eq_zero_iff]
      exact hL.trans hR.symm
    haveI : Fintype ↑({β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
        i * uval β + j * vval β = 0} : Set (Fin Tag.E8.rank → ℤ)) :=
      Set.Finite.fintype ((finite_setOf_isRoot Tag.E8).subset fun β hβ => hβ.1)
    rw [← hh, hS]
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    rw [← Fintype.card_subtype (fun r : R => i * uval r.1 + j * vval r.1 = 0)]
    exact Fintype.card_congr
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun β : Fin Tag.E8.rank → ℤ => IsRoot Tag.E8 β)
        (fun β => i * uval β + j * vval β = 0))
  have hnc := e8TwoFive_plane_root_count hRcard
    (fun r : R => uval r.1) (fun r : R => vval r.1) hcount
  intro β hβ
  by_contra hcon
  push Not at hcon
  exact hnc ⟨β, hβ⟩ ⟨(hu_zero β).mpr hcon.1, (hv_zero β).mpr hcon.2⟩

theorem e8TwoFive_plane_pow_mul_ne_one {G : Type} [Group G] {a b : G} (ha5 : a ^ 5 = 1)
    (hb5 : b ^ 5 = 1) (hab : Commute a b) (ha1 : a ≠ 1) (hb : b ∉ Subgroup.zpowers a) {i j : ℕ}
    (h : ¬ (5 ∣ i ∧ 5 ∣ j)) : a ^ i * b ^ j ≠ 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro hprod
  have hb1 : b ≠ 1 := fun hb1 => hb (by rw [hb1]; exact Subgroup.one_mem _)
  have hordb : orderOf b = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 (orderOf_dvd_of_pow_eq_one hb5) with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hb1
    · exact h5
  have hpba : b ^ j ∈ Subgroup.zpowers a := by
    have hbj : b ^ j = (a ^ i)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [hbj]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers a) i)
  by_cases h5j : 5 ∣ j
  ·
    have hbj1 : b ^ j = 1 := by
      obtain ⟨k, hk⟩ := h5j
      rw [hk, pow_mul, hb5, one_pow]
    rw [hbj1, mul_one] at hprod
    have horda : orderOf a = 5 := orderOf_eq_prime ha5 ha1
    have hdvd : orderOf a ∣ i := orderOf_dvd_of_pow_eq_one hprod
    rw [horda] at hdvd
    exact h ⟨hdvd, h5j⟩
  ·
    have hcop : j.Coprime (orderOf b) := by
      rw [hordb]
      exact ((Nat.prime_five.coprime_iff_not_dvd).mpr h5j).symm
    have hbzp : b ∈ Subgroup.zpowers (b ^ j) :=
      mem_zpowers_pow_iff.mpr (Nat.coprime_iff_gcd_eq_one.mp hcop)
    have hle : Subgroup.zpowers (b ^ j) ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hpba
    exact hb (hle hbzp)

end FieldFiveE8

end CFSG.StandardType
