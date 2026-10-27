module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniDefs
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniLFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKFrameCore
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootModel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniModelTwoCenter
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneCharts
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.ClassicalInvolution.WeakCT.SpSpGlue
import CFSG.LieType.Universal.Symplectic
import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock spEmbed)


theorem GGSecFiveBPermUniSpCell.exists_frames (hMp : GGInnerDiagMpInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {r : ℕ} (hr : 2 ≤ r)
    {eta : ↥Bs ≃* (Fin (r + 2) → Multiplicative (ZMod p))}
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull (r + 2) p)
    {f : ℕ} {K : Subgroup G} {i0 : Fin (r + 2)} (hf : 1 ≤ f)
    (hz : f = 1 → Line63.H5.twoCenter L = ⊥)
    (hcell : GGSecFiveBPermUniSpCell p Bs L 𝒦 (r + 2) eta f K i0) :
    ∃ y ∈ Bs, CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) ∧
      ∃ π : Equiv.Perm (Fin (r + 2)), π 0 = i0 ∧
        (∃ (κ : StatedSp (r + 1) (GaloisField 2 f) →* G)
          (ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)),
          GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ) ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : ↥(unitarySU 2 f F (r + 2)) →* G)
          (χ : Multiplicative (ZMod p) →* Fˣ),
          CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F ∧
            GGSecFiveBPermUniLFrame Bs L eta π σ χ := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hlab, hK𝒦, ⟨eK⟩, hAK⟩ := hcell
  obtain ⟨y, hNy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hyBs : y ∈ Bs := hR.1.1.2.1.1 hNy.1.2.1
  have hKp : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K := hNy.1.2.2.2.2.1
  have hSq : CFSG.Open.IsQuasisimple (StatedSp (r + 1) (GaloisField 2 f)) := by
    have hadm : StatedLieAdmissible .PSp (r + 1) 2 f := ⟨Nat.prime_two, hf, by omega, by
      intro h
      rw [Prod.mk.injEq] at h
      exact absurd h.1 (by omega)⟩
    have hq := Symplectic.isQuasisimple_of_admissible (r + 1) (GaloisField 2 f) hadm
      (GaloisField.card 2 f (by omega))
    have := hq.1
    exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩
  have hKc : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    ⟨hKp.1, isSubnormal_iff_open.mp hKp.2.1, CFSG.Open.IsQuasisimple.of_mulEquiv eK hSq⟩
  obtain ⟨π, hπ0, κ, ζ, hκ⟩ := ggSecFiveBPermSpK_exists_planeFrame_of_conj hMp hp2 (by omega) hr
    hR.1.1.2.1 (hR.1.2.2.1.2 y K hNy) eK eta hAK
  obtain ⟨-, F, hF, hFin, _, hN, φ, -, hM, hdiag⟩ :=
    exists_unitary_model_of_uniLabel_of_twoCenter hR (by omega) hz hlab
  obtain ⟨-, hBsE, -, -, -⟩ := hR.1.1.tableB_facts
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  obtain ⟨σ, χ, hLF⟩ := exists_uniLFrame_of_model hp hp2 hBsE hBsC
    hR.1.1.card_bstar_inf_centralizer_L.le (by omega) eta hA hN φ hM hdiag π
  exact ⟨y, hyBs, hKc, π, hπ0, ⟨κ, ζ, hκ⟩, F, hF, hFin, σ, χ, hM.field, hLF⟩

theorem ggSecFiveBPermUniSpChartInput_of_mp (hMp : GGInnerDiagMpInput) :
    GGSecFiveBPermUniSpChartInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ h5 eta _ hAfull _ _ _ f K i0 hf hcell
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, rfl⟩ : ∃ s, n = s + 3 := ⟨n - 3, by omega⟩
  obtain ⟨y, hyBs, hKc, π, _, ⟨κ, ζ, hκ⟩, _, _, _, _, _, hUF, hLF⟩ :=
    GGSecFiveBPermUniSpCell.exists_frames hMp hR (r := s + 1) (by omega) hAfull (by omega)
      (fun h => absurd h (by omega)) hcell
  have hF4 : 4 ≤ Nat.card (GaloisField 2 f) := TagsExc.four_le_card_galoisField hf
  have hBsC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hR.1.1.2.1.2.2.2
  have h01 : π 0 ≠ π 1 := π.injective.ne (Fin.ne_of_val_ne (by simp))
  have h03 : π 0 ≠ π 3 := π.injective.ne (Fin.ne_of_val_ne (by
    rw [Fin.val_zero]
    show 0 ≠ 3 % (s + 1 + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
    omega))
  obtain ⟨g, hgL, hg, hgη⟩ := exists_mem_conjAut_eq_permAut_swap hAfull h01
  obtain ⟨w, -, hw, hwη⟩ := exists_mem_conjAut_eq_permAut_swap hAfull h03
  obtain ⟨κ₂, hκ₂, hκ₂r, hov, hlong, hcross⟩ :=
    ggSecFiveBPermZeta_overlap_of_swap (s := s) hp2 hF4 (by omega) hBsC hyBs hKc hκ hg hgη hw hwη
  obtain ⟨κ₂', hκ₂', hκ₂'r, hsh, hlo, hc1, hc2⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_spSpCharts_of_overlap (s := s) (by omega) hκ.1 hκ₂
      hov hlong hcross
  have hMK : ∀ c d : Fin (s + 3), c ≠ d → c ≠ π 0 → d ≠ π 0 →
      ggBlockComm Bs eta {c, d} ≤ K := by
    intro c d hcd hc hd
    have ha : π.symm c ≠ 0 := fun h => hc (by rw [← h, Equiv.apply_symm_apply])
    have hb : π.symm d ≠ 0 := fun h => hd (by rw [← h, Equiv.apply_symm_apply])
    let τ : Fin 2 → Fin (s + 2) := ![(π.symm c).pred ha, (π.symm d).pred hb]
    have h0 : π (τ 0).succ = c := by simp [τ]
    have h1 : π (τ 1).succ = d := by simp [τ]
    have hne : τ 0 ≠ τ 1 := fun h => hcd (by rw [← h0, ← h1, h])
    have hτ : Function.Injective τ := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij hne
      · exact absurd hij.symm hne
      · rfl
    have hτs : ¬ Function.Surjective τ := by
      intro h
      have := Fintype.card_le_of_surjective τ h
      simp only [Fintype.card_fin] at this
      omega
    have hset : (Set.range fun l => π (τ l).succ) = ({c, d} : Set (Fin (s + 3))) := by
      ext z
      simp only [Set.mem_range, Fin.exists_fin_two, h0, h1, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
    rw [← hset, ggSecFiveBPermZeta_commutator_centralizer_eq hp2 hF4 hBsC hyBs hKc hκ τ hτ hτs]
    rw [MonoidHom.range_comp]
    exact (Subgroup.map_le_range _ _).trans hκ.2.1.le
  have hjoin : K ⊔ K.map (MulAut.conj g).toMonoidHom = L ⊔ K :=
    hLF.sup_map_conj_eq hUF hf hp (by omega) h01 hgL hg hgη hMK
  refine ⟨s, rfl, κ, κ₂', hκ.1, hκ₂', ?_, hsh, hlo, hc1, hc2⟩
  rw [hκ.2.1, hκ₂'r, hκ₂r, hjoin]

end CFSG.StandardType

end
