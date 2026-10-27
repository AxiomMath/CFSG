module

public import CFSG.RankThree.GF2n.Smith81.S81XD6Def
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinPair
import all CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.MinLead

public section

namespace CFSG.RankThree.GF2n.Smith81.SK

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.D6X


variable {K : Type} [Field K]

theorem ULG_le_posUnip : ULG K ≤ posUnip e7Data_valid K := by
  have hle : UL K ≤ (posUnip e7Data_valid K).map (e7Data_valid.minGroup K).subtype := by
    rw [UL, Subgroup.closure_le]
    rintro _ ⟨β, hβ, -, hpos, c, rfl⟩
    refine ⟨e7Data_valid.xm K β c, ?_, rfl⟩
    exact Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem (show β ∈
      {γ : Fin (Tag.rank .E7) → ℤ | IsRoot .E7 γ ∧ 0 < ht γ} from ⟨hβ, hpos⟩)
      (e7Data_valid.xm_mem_rootGroup K β c))
  intro g hg
  obtain ⟨y, hy, hyg⟩ := hle ((mem_ULG (K := K)).1 hg)
  have hyg' : y = g := Subtype.ext hyg
  rw [← hyg']
  exact hy

theorem perp_of_mem_leadSet [CharP K 2] {A : Subgroup (Gp K)} (hA : A ≤ ULG K)
    {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : γ ∈ leadSet (X := e7Data_valid.rootGroup K) (lev := fWt (Tag.rank .E7))
      (posRoots_finite (τ := Tag.E7) (f := fWt (Tag.rank .E7))) A) : γ ∈ Perp := by
  have hc0 : 0 < (Tag.cartan .E7).det := MinData.det_cartan_pos posDef_cartan_E7
  have hLD := levelData (hV := e7Data_valid) (k := K) (f := fWt (Tag.rank .E7)) posData_E7.inj
  obtain ⟨hγP, -⟩ := mem_leadSet.1 hγ
  obtain ⟨a, haA, ha1, ha2⟩ := exists_of_mem_leadSet hγ
  obtain ⟨c, hc, κ, hκ, rfl⟩ := lead_decomp hLD hγP ha1 ha2
  have hGG : PresPiece (endoE (e7Data_valid.xm K γ c * κ)) := by
    have h1 : ((e7Data_valid.xm K γ c * κ : Gp K) : (Module.End K (V K))ˣ) ∈ GG K :=
      UL_le_GG ((mem_ULG (K := K)).1 (hA haA))
    have h2 : PresPiece (((e7Data_valid.xm K γ c * κ : Gp K) : (Module.End K (V K))ˣ) :
        Module.End K (V K)) ∧ PresPiece ((((e7Data_valid.xm K γ c * κ : Gp K) :
        (Module.End K (V K))ˣ)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := h1
    exact h2.1
  by_contra hnot
  have hne : MinData.toWeight γ ⬝ᵥ theta ≠ 0 := fun h => hnot ⟨hγP.1, h⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin e7Data.d, pr b γ = -1 := by
    have h12 := (card_pr hγP.1).2.1
    obtain ⟨b, hb⟩ := Finset.card_pos.1
      (show 0 < (Finset.univ.filter fun a : Fin e7Data.d => pr a γ = -1).card by omega)
    exact ⟨b, (Finset.mem_filter.1 hb).2⟩
  have hwt : e7Data.wt (shift γ b) = e7Data.wt b + MinData.toWeight γ := wt_shift hγP.1 hb
  have hprt : pr (shift γ b) theta = pr b theta + MinData.toWeight γ ⬝ᵥ theta :=
    pr_shift hγP.1 hb theta
  have htb : pr (shift γ b) theta ≠ pr b theta := by omega
  have hv : (Finsupp.single b 1 : V K) ∈ Piece K (pr b theta) := mem_Piece_iff.2 fun b' hb' => by
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact hb' rfl
  have h1 : (e7Data_valid.endo K (e7Data_valid.xm K γ c * κ) (Finsupp.single b 1)) (shift γ b) =
      0 := mem_Piece_iff.1 (hGG _ _ hv) (shift γ b) htb
  have hsa := shift_sub_lead hc0 hγP c hκ
  have hvF : (Finsupp.single b 1 : V K) ∈ filt (e7Data.fgrade (fWt (Tag.rank .E7)))
      (e7Data.fgrade (fWt (Tag.rank .E7)) b) := single_mem_filt le_rfl
  have hφ := hsa _ _ hvF
  have hF := e7Data.isGrading_fgrade (fWt (Tag.rank .E7)) b (shift γ b) γ hwt
  have hlt : e7Data.fgrade (fWt (Tag.rank .E7)) (shift γ b) <
      e7Data.fgrade (fWt (Tag.rank .E7)) b + (Tag.cartan .E7).det * (fWt (Tag.rank .E7) γ + 1) := by
    rw [hF, mul_add, mul_one, ← add_assoc]
    exact lt_add_of_pos_right _ hc0
  have hφt := apply_eq_zero_of_mem_filt hφ (b := shift γ b) hlt
  have hroot : (e7Data.rootOp K γ (Finsupp.single b 1)) (shift γ b) = 1 := by
    rw [rootOp_single hγP.1, if_pos hb, Finsupp.single_eq_same]
  have hvt : (Finsupp.single b 1 : V K) (shift γ b) = 0 := by
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact htb (by rw [← h])
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, smul_eq_mul, hroot, hvt, h1] at hφt
  apply hc
  simpa using hφt

theorem card_le_pow_leadRoots [Finite K] [CharP K 2] (A : Subgroup (Gp K))
    (hA : A ≤ ULG K) (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∃ X : Finset (Fin (Tag.rank .E7) → ℤ),
      (∀ γ ∈ X, γ ∈ Perp ∧ 0 < CFSG.LieType.Steinberg.ht γ) ∧
      (∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E7 (γ + δ)) ∧ Nat.card A ≤ Nat.card K ^ X.card := by
  have hc0 : 0 < (Tag.cartan .E7).det := MinData.det_cartan_pos posDef_cartan_E7
  have hLD := levelData (hV := e7Data_valid) (k := K) (f := fWt (Tag.rank .E7)) posData_E7.inj
  have hP := posRoots_finite (τ := Tag.E7) (f := fWt (Tag.rank .E7))
  have hfin := finite_minGroup (hV := e7Data_valid) (k := K)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hAU : A ≤ lvlU e7Data_valid K (fWt (Tag.rank .E7)) 1 := by
    rw [lvlU_one_eq e7Data_valid posData_E7 K]
    exact hA.trans ULG_le_posUnip
  refine ⟨leadSet (X := e7Data_valid.rootGroup K) (lev := fWt (Tag.rank .E7)) hP A, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hγP, -⟩ := mem_leadSet.1 hγ
    exact ⟨perp_of_mem_leadSet hA hγ, (posData_E7.pos γ hγP.1).1 hγP.2⟩
  · intro γ hγ δ hδ
    exact not_isRoot_add_of_lead hc0 hLD hP hc hγ hδ
  · exact card_le_pow_leadSet hLD hP hq1 (fun γ _ => card_rootGroup_le γ) hAU

end CFSG.RankThree.GF2n.Smith81.SK
