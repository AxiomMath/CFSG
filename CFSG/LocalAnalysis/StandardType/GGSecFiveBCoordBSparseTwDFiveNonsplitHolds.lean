module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBRestLeafDefs
import CFSG.LocalAnalysis.StandardType.GGOrthAnchorOverlap
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSparseNonsplitFrames
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermOmKCrossing
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorExt
import CFSG.LocalAnalysis.StandardType.GGNormOmegaSpinCover
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Extension
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega


theorem ggSecFiveBCoordBSparseTwDFiveNonsplitInput_holds :
    GGSecFiveBCoordBSparseTwDFiveNonsplitInput := by
  intro _hMp _hLBal _hStd hX hTCJ hRig hTPn hA8 hraw hiso hFC hBJ
  intro G _ _ p B Bs x L D J 𝒦 hR _hT1 n e hP hn eta i0 h𝒦 hL hLab hB hRM _hG0
    _hSpC _hSpSpC _hOmC hDense
  classical
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  haveI : Fact p.Prime := ⟨hp⟩
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have h5 : 5 ≤ n := by
    obtain ⟨-, lab, -, hdat⟩ := hLab
    obtain ⟨_, _, _, _, _, _, _, hS, _⟩ := largeEvenRawDatum_exists hdat
    exact hS.2.1
  obtain ⟨hEven, hZ, hN, f, Kf, _, _, _, _, E, hf, hpq, -, π', hπ', κ, χ, hframe, hnbr⟩ :=
    hR.exists_omKFrames_of_twDNonsplit_of_noDenseNbr hX hTCJ hRig hTPn hA8 hraw hiso hFC
      (by omega) eta i0 h𝒦 hL hLab hB hRM hDense
  obtain ⟨K, hKmem, -⟩ := exists_mem_not_le_ggAutomizer_of_bSignedFull hp hp2 eta h𝒦 hL
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hKmem
  obtain ⟨-, j, hj, -, w, hw, -, hact, hKeq, hAK, -, hframe₂⟩ := hnbr y K hnb
  have hLK : ggG0 p B x L D J = L ⊔ K :=
    ggG0_eq_sup_of_bCoordinateBlocks hBJ hR e hP (by omega) h𝒦 hL hRM hKmem hj hAK
  subst hKeq
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hk : 2 ≤ k := by
    obtain ⟨r, hr⟩ := hEven
    omega
  obtain ⟨-, hBsEA, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp
      (hcfg.1.2.2.2.2.2.2.1.2.2.2.1 : CFSG.Assembly.IsComponentOf L
        (Subgroup.centralizer ({x} : Set G)))
  have hcut : ∀ b : ↥Bs, ((b : G) ∈ L ↔ eta b i0 = 1) :=
    ggBs_mem_iff_coord_eq_one_of_bCoordinateBlock hp hp2 hBsEA hxBs hx1 hLx hZ hN eta i0 hL
  have hπ'' : π' (Fin.last (k + 3)) = i0 := hπ'
  have hBmap : Bs.map (MulAut.conj w).toMonoidHom = Bs :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  have hy₂ : w * x * w⁻¹ ∈ Bs := by
    rw [← hBmap]
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hxBs
  have hLwc : CFSG.Open.IsComponentOf (L.map (MulAut.conj w).toMonoidHom)
      (Subgroup.centralizer ({w * x * w⁻¹} : Set G)) := by
    have h := CFSG.isComponentOf_map_mulEquiv (MulAut.conj w) hLc
    rw [CFSG.centralizer_singleton_map] at h
    exact h
  have hX₁ : ∀ b : ↥Bs, (b : G) ∈ L → eta b (π' (Fin.last (k + 3))) = 1 := by
    intro b hb
    simpa [hπ''] using (hcut b).mp hb
  have hX₂ : ∀ b : ↥Bs, (b : G) ∈ L.map (MulAut.conj w).toMonoidHom →
      eta b ((π'.trans (Equiv.swap i0 j)) (Fin.last (k + 3))) = 1 := by
    intro b hb
    have hbj : eta b (Equiv.swap i0 j i0) = 1 :=
      (mem_map_conj_iff_coord_eq_one hw hact hcut b).mp hb
    simpa [Equiv.trans_apply, hπ'', Equiv.swap_apply_left] using hbj
  have hne : π' (Fin.last (k + 3)) ≠
      (π'.trans (Equiv.swap i0 j)) (Fin.last (k + 3)) := by
    rw [Equiv.trans_apply, hπ'', Equiv.swap_apply_left]
    exact fun h => hj h.symm
  obtain ⟨π₁, π₂, κ₁, κ₂, h₁, h₂, hπ₁_last, hπ₂_last, hπ₂_eq, hpoint, hperm⟩ :=
    GGSecFiveBPermOmKFrame.exists_overlap_calibration_of_component_of_dvd
      (X₁ := L) (X₂ := L.map (MulAut.conj w).toMonoidHom) (y₁ := x) (y₂ := w * x * w⁻¹)
      (by omega) hpq hframe hframe₂ hSC hxBs hLc hy₂ hLwc hX₁ hX₂ hne
  obtain ⟨t, ht₁, ht₂⟩ := GGSecFiveBPermOmKFrame.exists_permHom_of_overlap_of_join
    hSC hxBs hLc hy₂ hLwc h𝒦 h₁ h₂ hk hπ₂_eq hperm
  have hπ₂j : (π'.trans (Equiv.swap i0 j)) (Fin.last (k + 3)) = j := by
    simp [Equiv.trans_apply, hπ'']
  have hπ₁_zero : π₁ 0 = j := by
    have h := hπ₂_last
    rw [hπ₂_eq, Equiv.trans_apply, finRotate_last, hπ₂j] at h
    exact h
  have h₂' : GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj w).toMonoidHom) eta
      ((finRotate (k + 4)).trans π₁) κ₂ χ := hπ₂_eq ▸ h₂
  have hX0 : ∀ b : ↥Bs, (b : G) ∈ L.map (MulAut.conj w).toMonoidHom → eta b (π₁ 0) = 1 := by
    intro b hb
    have hbj : eta b (Equiv.swap i0 j i0) = 1 :=
      (mem_map_conj_iff_coord_eq_one hw hact hcut b).mp hb
    simpa [hπ₁_zero, Equiv.swap_apply_left] using hbj
  obtain ⟨Ψ, hΨinj, -, -, hΨrange⟩ :=
    GGSecFiveBPermOmKFrame.exists_normOmega_hom_of_permHom_of_dvd (by omega) hpq hSC h₁ hxBs
      hLc h₂' hX0 ht₁ ht₂
  have hκ₁range : κ₁.range = L := h₁.2.1
  have hκ₂range : κ₂.range = L.map (MulAut.conj w).toMonoidHom := h₂.2.1
  have hrange : Ψ.range = ggG0 p B x L D J := by
    rw [hΨrange, hLK]
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [CFSG.Permutation.SymmetricCoxeter.range_eq_sup ht₁ ht₂]
      refine sup_le ?_ ?_
      · rintro _ ⟨σ, rfl⟩
        refine Subgroup.mem_sup_left ?_
        rw [← hκ₁range]
        exact ⟨_, rfl⟩
      · rintro _ ⟨σ, rfl⟩
        refine Subgroup.mem_sup_right ?_
        rw [← hκ₂range]
        exact ⟨_, rfl⟩
    · refine sup_le le_sup_left ?_
      rw [← hκ₂range, MonoidHom.range_eq_map,
        ← range_normOmegaCast_sup_range_normPerm (E := E) (m := k + 2) (by omega),
        Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        refine Subgroup.mem_sup_left ?_
        rw [← hκ₁range]
        exact ⟨_, hpoint a⟩
      · rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
        refine Subgroup.mem_sup_right ?_
        refine ⟨Equiv.Perm.viaEmbeddingHom (Fin.succEmb (k + 3)) σ, ?_⟩
        have h := DFunLike.congr_fun ht₂ σ
        simpa only [MonoidHom.comp_apply] using h
  have hodd : Odd (k + 3) := by
    obtain ⟨r, hr⟩ := hEven
    exact ⟨r - 1, by omega⟩
  exact ggSecFiveData_POmegaPlus_of_injective_normOmega_of_card (m := k + 3) (by omega) hodd
    (by omega) (GaloisField.card 2 f (by omega)) hΨinj hrange

end CFSG.StandardType

end
