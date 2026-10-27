module

public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftDiag
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftFar
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftGlue
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftNe
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftPsi
public import CFSG.LocalAnalysis.StandardType.GGTypeACrossLiftCross
public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverCoord

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix TypeAReflOver

theorem ggTypeACrossLift_of_known (hCD : GGTypeACompatDiagBInput) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {y : G} {K : Subgroup G} {y₃ : G} {K₃ : Subgroup G}
    (hNC : GGTypeANbrCfg p B Bs x L D J n f y K) (hN₃ : GGTypeANbr p B Bs x L D J n f y₃ K₃)
    (hK₃ : ¬ K₃ ≤ L ⊔ K) :
    ∃ φ₁ φ₂ φ₃ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J ∧
      φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      φ₃.range = K₃ ∧
      φ₃.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₃.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      ∀ j : Fin n, j.val + 1 = n →
        (φ₃ (weylRep n (GaloisField 2 f) j) * φ₂ (weylRep n (GaloisField 2 f) j)) ^ 3 = 1 ∧
        ∀ g, φ₂ (weylRep n (GaloisField 2 f) j) * φ₃ (weylRep n (GaloisField 2 f) j) *
            φ₂ (weylRep n (GaloisField 2 f) j) * φ₁ g =
          φ₁ g * (φ₂ (weylRep n (GaloisField 2 f) j) * φ₃ (weylRep n (GaloisField 2 f) j) *
            φ₂ (weylRep n (GaloisField 2 f) j)) := by
  classical
  have hNC₃ : GGTypeANbrCfg p B Bs x L D J n f y₃ K₃ :=
    ⟨hNC.1, hNC.2.1, hNC.2.2.1, hNC.2.2.2.1, hN₃⟩
  have hn : 3 ≤ n := hNC.three_le
  obtain ⟨φ₁, φ₂, hL, hk₁, hK, hk₂, hJ, hc₂, hdiag⟩ := hCD G p B Bs x L D J n f y K hNC
  obtain ⟨φ₁', φ₃', -, -, hK₃', hk₃', hJ', hc₃', hdiag'⟩ :=
    hCD G p B Bs x L D J n f y₃ K₃ hNC₃
  have hJ₃ : (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range =
      (φ₃'.comp (slUpperBlockHom n (GaloisField 2 f))).range := by
    rw [hJ, ← hc₃', hJ']
  obtain ⟨φ₃, hK₃r, hk₃, hc₃, hdiag₃⟩ := exists_slCompat_lift_actsDiag hn hk₁ hk₃' hJ₃
    (S := (Bs : Set G)) (fun b hb => (hdiag b hb).1) (fun b hb => (hdiag' b hb).2)
  have hK₃φ : φ₃.range = K₃ := hK₃r.trans hK₃'
  refine ⟨φ₁, φ₂, φ₃, hL, hk₁, hJ, hK, hk₂, hc₂, hK₃φ, hk₃, hc₃, fun j hj => ?_⟩
  have hdiag₁₃ : ∀ c ∈ Bs, GGActsDiag φ₁ c ∧ GGActsDiag φ₃ c :=
    fun c hc => ⟨(hdiag c hc).1, hdiag₃ c hc⟩
  have hX : GGFarCtx p Bs φ₁ φ₂ x y := ggFarCtx_of_cfg hNC hL hk₁ hK hk₂ hc₂ hdiag
  have hX₃ : GGFarCtx p Bs φ₁ φ₃ x y₃ := ggFarCtx_of_cfg hNC₃ hL hk₁ hK₃φ hk₃ hc₃ hdiag₁₃
  let i : Fin n := ⟨0, by omega⟩
  have hi : i.val = 0 := rfl
  have hfar₂ := hNC.commute_weylRep_of_diag hL hk₁ hK hk₂ hJ hc₂ hdiag hi hj
  have hfar₃ := hNC₃.commute_weylRep_of_diag hL hk₁ hK₃φ hk₃ hJ hc₃ hdiag₁₃ hi hj
  have hBs : IsElemAbelian p Bs := hNC.1.2.1.2.1
  have hic : i.castSucc = 0 := Fin.ext rfl
  have his : i.succ = 1 := Fin.ext (by
    rw [Fin.val_succ, Fin.val_one', Nat.mod_eq_of_lt (by omega)])
  have hfarA : hX.permAut₁ (Equiv.swap 0 1) * hX.permAut₂ (Equiv.swap j.castSucc j.succ) =
      hX.permAut₂ (Equiv.swap j.castSucc j.succ) * hX.permAut₁ (Equiv.swap 0 1) := by
    refine hX.permAut_commute_of_commute ?_
    rw [← hic, ← his, slPerm_swap_castSucc_succ, slPerm_swap_castSucc_succ]
    exact hfar₂
  obtain ⟨κ, hκ₁, hκ₂, -⟩ := hX.exists_coordEquiv hBs j hj hfarA
  have hcomm : ∀ σ : Equiv.Perm (Fin (n + 1)), σ (Fin.last n) = Fin.last n →
      hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) * hX.permAut₁ σ =
        hX.permAut₁ σ * hX₃.permAut₂ (Equiv.swap j.castSucc j.succ) :=
    fun σ hσ => hX₃.permAut₂_last_commute hi hj hfar₃ σ hσ
  have hrne := GGFarCtx.permAut₂_swap_ne_of_cross hNC hN₃ hK₃ hX hX₃ hK hK₃φ j κ hκ₁ hκ₂
  obtain ⟨hp3, hκ₃⟩ :=
    GGFarCtx.eq_kThreeRefl_of_cross hLB hNC hX hX₃ hL hJ j hj κ hκ₁ hκ₂ hcomm hrne
  have hY := hX.rotCtx hX₃ j κ hκ₁ hκ₂ hκ₃
  have hCu := hX.rot_abab_mem_centralizer hX₃ hp3 hi hj κ hκ₁ hκ₂ hκ₃
  have hPL : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) φ₂.range := by
    rw [hK]
    exact hNC.pComponent_K
  have hPK : LargeEvenPComponent p (Subgroup.centralizer
      ({φ₂ (slPerm hX.two (finRotate (n + 1))) * y₃ *
        (φ₂ (slPerm hX.two (finRotate (n + 1))))⁻¹} : Set G))
      (ggRotLift hX.two φ₂ φ₃).range := by
    rw [ggRotLift_range, hK₃φ]
    exact largeEvenPComponent_conj_centralizer_singleton hNC₃.pComponent_K _
  have hfar' := hY.commute_weylRep_of_pComponents hNC.dvd_natCard_units hPL hPK hi hj hCu
  exact ggCross_of_far hX.two hn hc₂ hc₃ hi hj hfar₂ hfar₃ hfar'

theorem ggTypeACrossLiftInput_of_known (hCD : GGTypeACompatDiagBInput)
    (hLB : GGLBalanceInput) : GGTypeACrossLiftInput := by
  intro G _ _ p B Bs x L D J n f y K y₃ K₃ hNC hN₃ _ hK₃
  exact ggTypeACrossLift_of_known hCD hLB hNC hN₃ hK₃

end CFSG.StandardType
