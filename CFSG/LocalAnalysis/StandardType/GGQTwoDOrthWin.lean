module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthCentr
public import CFSG.LocalAnalysis.StandardType.GGUnitaryTwoResidual
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.ClassicalInvolution.Phan.PhanDn.PanelStab
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.StandardType.PhanEBridgeGeom
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg
open CFSG.RankThree.Classical2 (orthDerived)

section Win

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

@[expose] def qtwoWinTorus (σ : K ≃+* K) (n k d : ℕ) : Subgroup (Fin n → normOne σ) where
  carrier := {t | ∀ a b : Fin n, k ≤ a.val → a.val < k + d → k ≤ b.val → b.val < k + d →
    t a = t b}
  mul_mem' := fun {s t} hs ht a b ha1 ha2 hb1 hb2 => by
    simp only [Pi.mul_apply, hs a b ha1 ha2 hb1 hb2, ht a b ha1 ha2 hb1 hb2]
  one_mem' := fun a b _ _ _ _ => rfl
  inv_mem' := fun {t} ht a b ha1 ha2 hb1 hb2 => by
    simp only [Pi.inv_apply, ht a b ha1 ha2 hb1 hb2]

private theorem pmow_qtwoStdWin_apply_window (m k d : ℕ) (h : k + d ≤ m + 1)
    (s : Su K 2 1 d) (v : Fin (m + 1) → K) (x : Fin d) :
    (qtwoStdWin (F := F) (K := K) m k d h s) v (blockIdx k h x) =
      ((((s : Su K 2 1 d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec
        (fun y => v (blockIdx k h y))) x := by
  change (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
    (blockEmb K 2 1 (m + 1) d k h s)) v (blockIdx k h x) = _
  rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blockEmb]
  exact blockMat_mulVec_blockIdx h _ _ x

private theorem pmow_qtwoStdWin_apply_not_mem (m k d : ℕ) (h : k + d ≤ m + 1)
    (s : Su K 2 1 d) (v : Fin (m + 1) → K) (i : Fin (m + 1))
    (hi : ¬ (k ≤ i.val ∧ i.val < k + d)) :
    (qtwoStdWin (F := F) (K := K) m k d h s) v i = v i := by
  change (suEndN (F := F) (unitaryInvolution K 2 1) (m + 1)
    (blockEmb K 2 1 (m + 1) d k h s)) v i = _
  rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blockEmb]
  exact blockMat_mulVec_of_not_mem _ _ hi

private theorem pmow_diagHom_comm_qtwoStdWin (m k d : ℕ) (h : k + d ≤ m + 1)
    (u : Fin (m + 1) → normOne (unitaryInvolution K 2 1))
    (hu : u ∈ qtwoWinTorus (unitaryInvolution K 2 1) (m + 1) k d) (s : Su K 2 1 d) :
    diagHom F (unitaryInvolution K 2 1) (m + 1) u *
        qtwoStdWin (F := F) (K := K) m k d h s =
      qtwoStdWin (F := F) (K := K) m k d h s *
        diagHom F (unitaryInvolution K 2 1) (m + 1) u := by
  apply LinearEquiv.ext; intro v; funext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, diagHom_apply]
  by_cases hi : k ≤ i.val ∧ i.val < k + d
  · have hix : i = blockIdx k h ⟨i.val - k, by omega⟩ := by
      ext; simp only [blockIdx_val]; omega
    rw [hix, pmow_qtwoStdWin_apply_window, pmow_qtwoStdWin_apply_window]
    simp only [diagHom_apply]
    have hv : (fun y : Fin d =>
          (((u (blockIdx k h y) : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) *
            v (blockIdx k h y)) =
        ((((u (blockIdx k h ⟨i.val - k, by omega⟩) :
              normOne (unitaryInvolution K 2 1)) : Kˣ) : K)) •
          (fun y => v (blockIdx k h y)) := by
      funext y
      rw [Pi.smul_apply]
      congr 1
      exact congrArg (fun z : normOne (unitaryInvolution K 2 1) => ((z : Kˣ) : K))
        (hu (blockIdx k h y) (blockIdx k h ⟨i.val - k, by omega⟩)
          (by simp only [blockIdx_val]; omega) (by simp only [blockIdx_val]; omega)
          (by simp only [blockIdx_val]; omega) (by simp only [blockIdx_val]; omega))
    rw [hv, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  · rw [pmow_qtwoStdWin_apply_not_mem m k d h s v i hi,
      pmow_qtwoStdWin_apply_not_mem m k d h s
        (diagHom F (unitaryInvolution K 2 1) (m + 1) u v) i hi,
      diagHom_apply]

theorem qtwoOrth_win_eq (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    (hK : Nat.card K = 4) (m k d : ℕ) (hm : 3 ≤ m) (hd : 2 ≤ d) (h : k + d ≤ m + 1) :
    ggOTwoPrime (orthDerived (Qn E (m + 1)) ⊓ Subgroup.centralizer
      (((qtwoWinTorus (unitaryInvolution K 2 1) (m + 1) k d).map
        (diagHom F (unitaryInvolution K 2 1) (m + 1)) :
          Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) :
        Set ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))) =
      (qtwoStdWin (F := F) (K := K) m k d h).range := by
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have horthDerived : orthDerived (Qn E (m + 1)) ≤
      TauCeti.QuadraticMap.orthogonalGroup (Qn E (m + 1)) :=
    Subgroup.commutator_le_self _
  have hwinΩ : (qtwoStdWin (F := F) (K := K) m k d h).range ≤
      orthDerived (Qn E (m + 1)) := by
    rintro g ⟨s, rfl⟩
    exact suEndN_mem_orthDerived E (by omega : 4 ≤ m + 1)
      (blockEmb K 2 1 (m + 1) d k h s)
  have hwinCent : (qtwoStdWin (F := F) (K := K) m k d h).range ≤
      Subgroup.centralizer
        ((((qtwoWinTorus (unitaryInvolution K 2 1) (m + 1) k d).map
          (diagHom F (unitaryInvolution K 2 1) (m + 1)) :
            Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) :
          Set ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))) := by
    rintro g ⟨s, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
    exact pmow_diagHom_comm_qtwoStdWin m k d h u hu s
  have hsup : (qtwoStdWin (F := F) (K := K) m k d h).range ≤
      ggOTwoPrime (orthDerived (Qn E (m + 1)) ⊓ Subgroup.centralizer
        (((qtwoWinTorus (unitaryInvolution K 2 1) (m + 1) k d).map
          (diagHom F (unitaryInvolution K 2 1) (m + 1)) :
            Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) :
          Set ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))) :=
    ggSu_range_le_ggOTwoPrime hK' hd (qtwoStdWin (F := F) (K := K) m k d h)
      (le_inf hwinΩ hwinCent)
  have hcard : Nat.card (normOne (unitaryInvolution K 2 1)) = 3 := by
    have h3 := card_normOne (K := K) (p := 2) (f := 1) hK'
    simpa using h3
  haveI : Nontrivial (normOne (unitaryInvolution K 2 1)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨ζ, hζ⟩ := exists_ne (1 : normOne (unitaryInvolution K 2 1))
  have hsub : ggOTwoPrime (orthDerived (Qn E (m + 1)) ⊓ Subgroup.centralizer
        (((qtwoWinTorus (unitaryInvolution K 2 1) (m + 1) k d).map
          (diagHom F (unitaryInvolution K 2 1) (m + 1)) :
            Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) :
          Set ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)))) ≤
      (qtwoStdWin (F := F) (K := K) m k d h).range := by
    rw [ggOTwoPrime, Subgroup.closure_le]
    rintro g ⟨hgC, e, hge⟩
    have hmem_glob : diagHom F (unitaryInvolution K 2 1) (m + 1) (fun _ => ζ) ∈
        ((qtwoWinTorus (unitaryInvolution K 2 1) (m + 1) k d).map
          (diagHom F (unitaryInvolution K 2 1) (m + 1)) :
            Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) :=
      Subgroup.mem_map.mpr ⟨fun _ => ζ, fun _ _ _ _ _ _ => rfl, rfl⟩
    have hmem_out : ∀ l : Fin (m + 1), (l.val < k ∨ k + d ≤ l.val) →
        diagHom F (unitaryInvolution K 2 1) (m + 1) (Pi.mulSingle l ζ) ∈
          ((qtwoWinTorus (unitaryInvolution K 2 1) (m + 1) k d).map
            (diagHom F (unitaryInvolution K 2 1) (m + 1)) :
              Subgroup ((Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) := by
      intro l hl
      refine Subgroup.mem_map.mpr
        ⟨Pi.mulSingle (M := fun _ => normOne (unitaryInvolution K 2 1)) l ζ, ?_, rfl⟩
      intro a b ha1 ha2 hb1 hb2
      have ha : a ≠ l := fun h => by have := congrArg Fin.val h; omega
      have hb : b ≠ l := fun h => by have := congrArg Fin.val h; omega
      exact (Pi.mulSingle_eq_of_ne
          (M := fun _ => normOne (unitaryInvolution K 2 1)) ha ζ).trans
        (Pi.mulSingle_eq_of_ne
          (M := fun _ => normOne (unitaryInvolution K 2 1)) hb ζ).symm
    exact qtwoOrth_centr_window E hF m k d hd h ζ hζ g
      (horthDerived hgC.1) ⟨e, hge⟩
      ((Subgroup.mem_centralizer_iff.mp hgC.2 _ hmem_glob).symm)
      (fun l hl => (Subgroup.mem_centralizer_iff.mp hgC.2 _ (hmem_out l hl)).symm)
  exact le_antisymm hsub hsup

end Win

end CFSG.StandardType.QTwo

end
