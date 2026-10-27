module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.Quasithin.Background.C1PackImage

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem conj_le_of_one {T L R K : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) (hTR : T ≤ normalizer (R : Set G))
    {t₀ : T} (hle : K.map (MulAut.conj (t₀ : G)).toMonoidHom ≤
      R ⊔ CFSG.Open.pCoreOf 2 L) :
    ∀ t : T, K.map (MulAut.conj (t : G)).toMonoidHom ≤
      R ⊔ CFSG.Open.pCoreOf 2 L := by
  intro t
  have hsT : (t : G) * (t₀ : G)⁻¹ ∈ T := T.mul_mem t.2 (T.inv_mem t₀.2)
  have hcomp : (K.map (MulAut.conj (t₀ : G)).toMonoidHom).map
      (MulAut.conj ((t : G) * (t₀ : G)⁻¹)).toMonoidHom =
      K.map (MulAut.conj (t : G)).toMonoidHom := by
    rw [Subgroup.map_conj_map_conj]
    congr 1
    group
  have hRmap : R.map (MulAut.conj ((t : G) * (t₀ : G)⁻¹)).toMonoidHom = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (hTR hsT)
  have hOmap : (CFSG.Open.pCoreOf 2 L).map
      (MulAut.conj ((t : G) * (t₀ : G)⁻¹)).toMonoidHom = CFSG.Open.pCoreOf 2 L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1
      ((hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)) hsT)
  have hsupmap : (R ⊔ CFSG.Open.pCoreOf 2 L).map
      (MulAut.conj ((t : G) * (t₀ : G)⁻¹)).toMonoidHom =
      R ⊔ CFSG.Open.pCoreOf 2 L := by
    rw [Subgroup.map_sup, hRmap, hOmap]
  calc K.map (MulAut.conj (t : G)).toMonoidHom
      = (K.map (MulAut.conj (t₀ : G)).toMonoidHom).map
          (MulAut.conj ((t : G) * (t₀ : G)⁻¹)).toMonoidHom := hcomp.symm
    _ ≤ (R ⊔ CFSG.Open.pCoreOf 2 L).map
          (MulAut.conj ((t : G) * (t₀ : G)⁻¹)).toMonoidHom := Subgroup.map_mono hle
    _ = R ⊔ CFSG.Open.pCoreOf 2 L := hsupmap

private theorem commutator_barImage_eq_bot_of_mem_calL {T L R K : Subgroup G}
    (hTL : T ≤ normalizer (L : Set G)) (hTR : T ≤ normalizer (R : Set G))
    (hLR : L ≤ normalizer (R : Set G)) (hRL : R ≤ L) (hK : K ∈ calC L)
    (hLK : L = ⨆ t : T, K.map (MulAut.conj (t : G)).toMonoidHom)
    (hR : ¬ L ≤ R ⊔ CFSG.Open.pCoreOf 2 L) :
    ∀ t : T, ⁅barImage L (K.map (MulAut.conj (t : G)).toMonoidHom),
      barImage L R⁆ = ⊥ := by
  have hRn : (R.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRL).mpr hLR
  have hbarRn : (barImage L R).Normal := by
    simpa only [barImage] using hRn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _)
  have hno : ∀ t : T,
      ¬ K.map (MulAut.conj (t : G)).toMonoidHom ≤ R ⊔ CFSG.Open.pCoreOf 2 L := by
    intro t hle
    refine hR ?_
    conv_lhs => rw [hLK]
    exact iSup_le (fun t' => conj_le_of_one hTL hTR hle t')
  intro t
  have hKt : K.map (MulAut.conj (t : G)).toMonoidHom ∈ calC L :=
    UC6S846.calC_map L (MulAut.conj (t : G))
      (Subgroup.mem_normalizer_iff_map_conj_eq.1 (hTL t.2)) hK
  have hFle : K.map (MulAut.conj (t : G)).toMonoidHom ≤ L := by
    rw [hLK]
    exact le_iSup (fun t : T => K.map (MulAut.conj (t : G)).toMonoidHom) t
  rcases CFSG.LocalCores.component_normal_subgroup (uc22p22l_barImage_isComponent hKt) hbarRn
    with hle | hcomm
  · exact absurd (CFSG.Quasithin.C1Pack.le_sup_pCoreOf_of_barImage_le hFle
      (by simpa only [CFSG.Quasithin.C1Pack.barImage, barImage] using hle)) (hno t)
  · exact hcomm

theorem barImage_le_center_of_mem_calL {T M L R : Subgroup G} (hL : L ∈ calL T M)
    (hRL : R ≤ L) (hLR : L ≤ normalizer (R : Set G))
    (hTR : T ≤ normalizer (R : Set G)) (hR : ¬ L ≤ R ⊔ CFSG.Open.pCoreOf 2 L) :
    barImage L R ≤ Subgroup.center (Bar2 L) := by
  obtain ⟨K, hK, hLK⟩ := hL.2.2.2
  have hFle : ∀ t : T, K.map (MulAut.conj (t : G)).toMonoidHom ≤ L := by
    intro t
    rw [hLK]
    exact le_iSup (fun t : T => K.map (MulAut.conj (t : G)).toMonoidHom) t
  have hsub : (⨆ t : T, (K.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf L) = ⊤ := by
    rw [← CFSG.subgroupOf_iSup (fun t : T => K.map (MulAut.conj (t : G)).toMonoidHom) hFle,
      ← hLK]
    exact Subgroup.subgroupOf_self L
  have hjoin : (⨆ t : T, barImage L (K.map (MulAut.conj (t : G)).toMonoidHom)) = ⊤ := by
    have hmap : (⨆ t : T, barImage L (K.map (MulAut.conj (t : G)).toMonoidHom)) =
        (⨆ t : T, (K.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf L).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      simp only [barImage]
      exact (Subgroup.map_iSup _ _).symm
    rw [hmap, hsub, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hcomm := commutator_barImage_eq_bot_of_mem_calL hL.1 hTR hLR hRL hK hLK hR
  have hcent : (⊤ : Subgroup (Bar2 L)) ≤
      Subgroup.centralizer (barImage L R : Set (Bar2 L)) := by
    rw [← hjoin]
    exact iSup_le fun t => Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm t)
  exact Subgroup.centralizer_eq_top_iff_subset.mp (top_le_iff.mp hcent)

theorem commutator_mem_pCoreOf_of_mem_calL {T M L R : Subgroup G} (hL : L ∈ calL T M)
    (hRL : R ≤ L) (hLR : L ≤ normalizer (R : Set G))
    (hTR : T ≤ normalizer (R : Set G)) (hR : ¬ L ≤ R ⊔ CFSG.Open.pCoreOf 2 L) :
    ∀ x ∈ R, ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  have hbar := barImage_le_center_of_mem_calL hL hRL hLR hTR hR
  have hbar' : CFSG.Quasithin.C1Pack.barImage L R ≤ Subgroup.center (Bar2 L) := by
    simpa only [CFSG.Quasithin.C1Pack.barImage, barImage] using hbar
  have hcomm : ⁅CFSG.Quasithin.C1Pack.barImage L R,
      CFSG.Quasithin.C1Pack.barImage L L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hbar'.trans (Subgroup.center_le_centralizer _)
  exact CFSG.Quasithin.C1Pack.commutator_mem_pCoreOf_of_barImage hRL le_rfl hcomm

end CFSG.LocalAnalysis.UniquenessCase.UC22
