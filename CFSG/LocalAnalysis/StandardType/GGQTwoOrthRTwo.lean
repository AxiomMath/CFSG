module

public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthSupportTwoComponent
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.QTwoRTwoModel
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.ThreePlaneFourierGeneration
import CFSG.LocalAnalysis.ComponentInitial.ComponentNormalizeCentralize
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthAnchorRecal
import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalBlocks
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.GroupTheory.CentralizerMap
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.PhanDn
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits

private theorem transported_frame_facts
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G}
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin 4}
    {κ₁ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    {t : Equiv.Perm (Fin 4) →* G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (htN : t (Equiv.swap 2 3) ∈ Subgroup.normalizer (Bs : Set G))
    (htAct : MulAut.congr eta (ggConjAut Bs htN) =
      SpCoord.permAut (Equiv.swap (π 2) (π (Fin.last 3)))) :
    Bs.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom = Bs ∧
      t (Equiv.swap 2 3) * x * (t (Equiv.swap 2 3))⁻¹ ∈ Bs ∧
      CFSG.Open.IsComponentOf (L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom)
        (Subgroup.centralizer ({t (Equiv.swap 2 3) * x * (t (Equiv.swap 2 3))⁻¹} : Set G)) ∧
      GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom) eta
        (π.trans (Equiv.swap (π 2) (π (Fin.last 3))))
        ((MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom.comp κ₁) χ := by
  classical
  obtain ⟨-, -, hxBs, -, -⟩ := hcfg.tableB_facts
  have hLc : CFSG.Open.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp
      (hcfg.1.2.2.2.2.2.2.1.2.2.2.1 : CFSG.Assembly.IsComponentOf L
        (Subgroup.centralizer ({x} : Set G)))
  have hBmap : Bs.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom = Bs :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp htN
  have hyB : t (Equiv.swap 2 3) * x * (t (Equiv.swap 2 3))⁻¹ ∈ Bs := by
    rw [← hBmap]
    exact Subgroup.mem_map_of_mem _ hxBs
  have hL₃c : CFSG.Open.IsComponentOf (L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom)
      (Subgroup.centralizer ({t (Equiv.swap 2 3) * x * (t (Equiv.swap 2 3))⁻¹} : Set G)) := by
    have h := CFSG.isComponentOf_map_mulEquiv (MulAut.conj (t (Equiv.swap 2 3))) hLc
    rw [CFSG.centralizer_singleton_map] at h
    exact h
  exact ⟨hBmap, hyB, hL₃c, h₁.conj_transporter htN htAct⟩

private theorem qTwoRTwoA_support
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G}
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin 4} {i0 : Fin 4}
    {κ₁ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    (hcfg : GGConfig 3 B Bs x L D J)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (hπ : π (Fin.last 3) = i0)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0)
    (hZ : Subgroup.center L = ⊥) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (aG : G) (haG : aG ∈ Bs) (haGdef : aG = κ₁ (qTwoRTwoA E χ)) :
    (∀ c ∈ ({π 0, π (Fin.last 3)} : Finset (Fin 4)), eta ⟨aG, haG⟩ c = 1) ∧
      (∀ c ∉ ({π 0, π (Fin.last 3)} : Finset (Fin 4)), eta ⟨aG, haG⟩ c ≠ 1) := by
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  have hAcoord (i : Fin 3) :
      eta ⟨aG, haG⟩ (π i.castSucc) = ![1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2] i := by
    have h := h₁.coords_normPlaneTorus (E₁ := E) (hr := by norm_num) (hSC := hSC)
      (u := ![1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2]) i
    simpa [haGdef, qTwoRTwoA] using h
  have hAlast : eta ⟨aG, haG⟩ (π (Fin.last 3)) = 1 := by
    have h := h₁.normPlaneTorus_coord_last (E := E) (hr := by norm_num) hcfg hZ hN
      (hLeta := hL) (v := ![1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2])
    simpa [haGdef, qTwoRTwoA, ← hπ] using h
  constructor
  · intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · simpa using hAcoord 0
    · simpa using hAlast
  · intro c hc
    have hc0 : c ≠ π 0 := fun h => hc (by simp [h])
    have hcl : c ≠ π (Fin.last 3) := fun h => hc (by simp [h])
    obtain ⟨j, rfl⟩ := π.surjective c
    have hj0 : j ≠ 0 := fun h => hc0 (by rw [h])
    have hjl : j ≠ Fin.last 3 := fun h => hcl (by rw [h])
    have hj : j = 1 ∨ j = 2 := by
      revert hj0 hjl
      fin_cases j <;> simp
    rcases hj with rfl | rfl
    · rw [show π (1 : Fin 4) = π (Fin.castSucc (1 : Fin 3)) from rfl, hAcoord 1]
      have hu : ![1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2] (1 : Fin 3) =
          Multiplicative.ofAdd (1 : ZMod 3) := rfl
      rw [hu]
      intro h
      have h' : (1 : ZMod 3) = 0 := by simpa using congrArg Multiplicative.toAdd h
      exact one_ne_zero h'
    · rw [show π (2 : Fin 4) = π (Fin.castSucc (2 : Fin 3)) from rfl, hAcoord 2]
      have hu : ![1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2] (2 : Fin 3) =
          Multiplicative.ofAdd (2 : ZMod 3) := rfl
      rw [hu]
      intro h
      have h' : (2 : ZMod 3) = 0 := by simpa using congrArg Multiplicative.toAdd h
      exact (Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; norm_num)) h'

private theorem plane_image_facts (π : Fin 4 ≃ Fin 4) :
    (Equiv.swap (π 2) (π (Fin.last 3))) (π 0) = π 0 ∧
      (Equiv.swap (π 2) (π (Fin.last 3))) (π 1) = π 1 ∧
      (Equiv.swap (π 2) (π (Fin.last 3))) (π 2) = π (Fin.last 3) ∧
      (Equiv.swap (π 2) (π (Fin.last 3))) (π (Fin.last 3)) = π 2 ∧
      ((fun i : Fin 3 => (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) i.castSucc) ''
        (({0, 2} : Finset (Fin 3)) : Set (Fin 3)) =
        (({π 0, π (Fin.last 3)} : Finset (Fin 4)) : Set (Fin 4))) := by
  let τ : Equiv.Perm (Fin 4) := Equiv.swap (π 2) (π (Fin.last 3))
  have hτ0 : τ (π 0) = π 0 := by
    refine Equiv.swap_apply_of_ne_of_ne (a := π 2) (b := π (Fin.last 3)) (x := π 0) ?_ ?_
    · intro h
      exact (by decide : (0 : Fin 4) ≠ 2) (π.injective h)
    · intro h
      exact (by decide : (0 : Fin 4) ≠ Fin.last 3) (π.injective h)
  have hτ1 : τ (π 1) = π 1 := by
    refine Equiv.swap_apply_of_ne_of_ne (a := π 2) (b := π (Fin.last 3)) (x := π 1) ?_ ?_
    · intro h
      exact (by decide : (1 : Fin 4) ≠ 2) (π.injective h)
    · intro h
      exact (by decide : (1 : Fin 4) ≠ Fin.last 3) (π.injective h)
  have hτ2 : τ (π 2) = π (Fin.last 3) := by
    change Equiv.swap (π 2) (π (Fin.last 3)) (π 2) = π (Fin.last 3)
    exact Equiv.swap_apply_left _ _
  have hτ3 : τ (π (Fin.last 3)) = π 2 := by
    change Equiv.swap (π 2) (π (Fin.last 3)) (π (Fin.last 3)) = π 2
    exact Equiv.swap_apply_right _ _
  have hπ₃0 : (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) (Fin.castSucc (0 : Fin 3)) =
      π 0 := by
    change (Equiv.swap (π 2) (π (Fin.last 3))) (π 0) = π 0
    exact hτ0
  have hπ₃2 : (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) (Fin.castSucc (2 : Fin 3)) =
      π (Fin.last 3) := by
    change (Equiv.swap (π 2) (π (Fin.last 3))) (π 2) = π (Fin.last 3)
    exact hτ2
  refine ⟨hτ0, hτ1, hτ2, hτ3, ?_⟩
  ext j
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i = 0 ∨ i = 2 := by
      simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using hi
    rcases hi' with rfl | rfl
    · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hπ₃0
    · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr hπ₃2
  · intro hj
    change j ∈ ({π 0, π (Fin.last 3)} : Finset (Fin 4)) at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ⟨0, by simp, hπ₃0⟩
    · exact ⟨2, by simp, hπ₃2⟩

private theorem map_normBlock_zero_two_eq_ggBlockComm
    {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G} {x : G}
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin 4}
    {κ₃ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    {t : Equiv.Perm (Fin 4) →* G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (h₃ : GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom)
      eta (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) κ₃ χ)
    (hyB : t (Equiv.swap 2 3) * x * (t (Equiv.swap 2 3))⁻¹ ∈ Bs)
    (hL₃c : CFSG.Open.IsComponentOf (L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom)
      (Subgroup.centralizer ({t (Equiv.swap 2 3) * x * (t (Equiv.swap 2 3))⁻¹} : Set G)))
    (hset : ((fun i : Fin 3 => (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) i.castSucc) ''
        ((({0, 2} : Finset (Fin 3)) : Set (Fin 3)))) =
        (({π 0, π (Fin.last 3)} : Finset (Fin 4)) : Set (Fin 4))) :
    (normBlock E 3 ({0, 2} : Finset (Fin 3))).map κ₃ =
      ggBlockComm Bs eta (({π 0, π (Fin.last 3)} : Finset (Fin 4)) : Set (Fin 4)) := by
  have h := GGSecFiveBPermOmKFrame.blockComm_eq_map_normBlock
    (G := G) (p := 3) (E := E) (Bs := Bs)
    (X := L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom)
    (y := t (Equiv.swap 2 3) * x * (t (Equiv.swap 2 3))⁻¹)
    hSC hyB hL₃c (eta := eta) (π := π.trans (Equiv.swap (π 2) (π (Fin.last 3))))
    (κ := κ₃) (χ := χ) h₃ (S := ({0, 2} : Finset (Fin 3))) (by norm_num) (by norm_num)
  rw [hset] at h
  exact h.symm

private theorem center_map_normBlock_two_eq_bot
    {G : Type} [Group G]
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {κ : normOmega E 3 →* G} (hκ : Function.Injective κ) :
    Subgroup.center ((normBlock E 3 ({2} : Finset (Fin 3))).map κ) = ⊥ := by
  have hA_simple : IsSimpleGroup ↥((normBlock E 3 ({2} : Finset (Fin 3))).map κ) := by
    have : IsSimpleGroup ↥(normBlock E 3 ({2} : Finset (Fin 3))) :=
      isSimpleGroup_normBlock E (by norm_num) _ (by simp)
    exact (Subgroup.equivMapOfInjective (normBlock E 3 ({2})) κ hκ).symm.isSimpleGroup
  have hA_perfect : Group.IsPerfect ↥((normBlock E 3 ({2} : Finset (Fin 3))).map κ) := by
    have : Group.IsPerfect ↥(normBlock E 3 ({2} : Finset (Fin 3))) :=
      isPerfect_normBlock E (by norm_num) _ (by simp)
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.equivMapOfInjective (normBlock E 3 ({2})) κ hκ).toMonoidHom)
      (Subgroup.equivMapOfInjective (normBlock E 3 ({2})) κ hκ).surjective
  have hnc : ¬ IsMulCommutative ↥((normBlock E 3 ({2} : Finset (Fin 3))).map κ) :=
    Group.IsPerfect.not_isMulCommutative
      (G := ↥((normBlock E 3 ({2} : Finset (Fin 3))).map κ))
  rw [isMulCommutative_iff] at hnc
  push Not at hnc
  obtain ⟨a, b, hab⟩ := hnc
  rcases (inferInstance : (Subgroup.center
    ↥((normBlock E 3 ({2} : Finset (Fin 3))).map κ)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab

private theorem isComponentOf_centralizer_map_qTwoRTwoU
    {G : Type} [Group G] [Finite G]
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {κ₁ κ₂ κ₃ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    {t : Equiv.Perm (Fin 4) →* G}
    (hκ₃ : ∀ b, κ₃ b = t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹)
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) = κ₂.comp (normPerm E le_rfl))
    (hpoint : ∀ y : normOmega E 2, κ₁ (normPerm E le_rfl (finRotate 3) *
        normOmegaCast E (by norm_num) y * (normPerm E le_rfl (finRotate 3))⁻¹) =
      κ₂ (normOmegaCast E (by norm_num) y))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ₁, Commute (t (Equiv.swap 2 3)) y)
    (hAcomp : CFSG.Assembly.IsComponentOf
      ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃)
      (Subgroup.centralizer ({κ₁ (qTwoRTwoA E χ)} : Set G) ⊓
        Subgroup.centralizer ({κ₁ (qTwoRTwoD E χ)} : Set G))) :
    CFSG.Assembly.IsComponentOf ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃)
      (Subgroup.centralizer (((qTwoRTwoU E χ).map κ₁ : Subgroup G) : Set G)) := by
  let UG : Subgroup G := (qTwoRTwoU E χ).map κ₁
  let aG : G := κ₁ (qTwoRTwoA E χ)
  let dG : G := κ₁ (qTwoRTwoD E χ)
  have haG_UG : aG ∈ UG := by
    refine Subgroup.mem_map_of_mem κ₁ ?_
    exact Subgroup.subset_closure (by simp [qTwoRTwoA])
  have hdG_UG : dG ∈ UG := by
    refine Subgroup.mem_map_of_mem κ₁ ?_
    exact Subgroup.subset_closure (by simp [qTwoRTwoD])
  have hcent_pieces : qTwoRTwoU E χ ≤ Subgroup.comap κ₁
      (Subgroup.centralizer (((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ : Subgroup G) :
        Set G)) := by
    refine (qTwoRTwoU_le_iSup_pairs E χ).trans ?_
    refine iSup_le fun S => iSup_le fun hS => ?_
    intro n hn
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hκ₃ b]
    exact (commute_conj_of_mem_normBlock_inf_normAnchorFixing_three (E := E) ht₂ hpoint
        hC hS hn hb).symm
  have hA_le_CUG : ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃) ≤
      Subgroup.centralizer (UG : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hu
    have hcn := hcent_pieces hn
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hcn
    exact (hcn y hy).symm
  have hCUG_le : Subgroup.centralizer (UG : Set G) ≤
      Subgroup.centralizer ({aG} : Set G) ⊓ Subgroup.centralizer ({dG} : Set G) := by
    refine le_inf ?_ ?_
    · exact Subgroup.centralizer_le (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact haG_UG)
    · exact Subgroup.centralizer_le (by
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst z
        exact hdG_UG)
  exact CFSG.Assembly.IsComponentOf.of_le_of_le hAcomp hA_le_CUG hCUG_le

private theorem isComponentOf_centralizer_inf_qTwoRTwoD
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G}
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin 4} {i0 : Fin 4}
    {κ₁ κ₃ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    {t : Equiv.Perm (Fin 4) →* G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (hπ : π (Fin.last 3) = i0)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0)
    (hZ : Subgroup.center L = ⊥) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (h₃ : GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom)
      eta (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) κ₃ χ)
    (hA : CFSG.Assembly.IsComponentOf
      (ggBlockComm Bs eta (({π 0, π (Fin.last 3)} : Finset (Fin 4)) : Set (Fin 4)))
      (Subgroup.centralizer ({κ₁ (qTwoRTwoA E χ)} : Set G)))
    (hblock : (normBlock E 3 ({0, 2} : Finset (Fin 3))).map κ₃ =
      ggBlockComm Bs eta (({π 0, π (Fin.last 3)} : Finset (Fin 4)) : Set (Fin 4)))
    (hτ0 : (Equiv.swap (π 2) (π (Fin.last 3))) (π 0) = π 0)
    (hτ2 : (Equiv.swap (π 2) (π (Fin.last 3))) (π 2) = π (Fin.last 3)) :
    CFSG.Assembly.IsComponentOf ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃)
      (Subgroup.centralizer ({κ₁ (qTwoRTwoA E χ)} : Set G) ⊓
        Subgroup.centralizer ({κ₁ (qTwoRTwoD E χ)} : Set G)) := by
  let uD : Fin 3 → Multiplicative (ZMod 3) := fun _ => Multiplicative.ofAdd 1
  let dG : G := κ₁ (qTwoRTwoD E χ)
  have hdG : dG ∈ Bs := by
    have h := h₁.normPlaneTorus_mem_Bs (E₁ := E) (hr := by norm_num) (hSC := hSC) uD
    simpa [dG, qTwoRTwoD, uD] using h
  have hDcoord (i : Fin 3) : eta ⟨dG, hdG⟩ (π i.castSucc) = uD i := by
    have h := h₁.coords_normPlaneTorus (E₁ := E) (hr := by norm_num) (hSC := hSC) (u := uD) i
    simpa [dG, qTwoRTwoD, uD] using h
  have hDlast : eta ⟨dG, hdG⟩ (π (Fin.last 3)) = 1 := by
    have h := h₁.normPlaneTorus_coord_last (E := E) (hr := by norm_num) hcfg hZ hN
      (hLeta := hL) (v := uD)
    simpa [dG, qTwoRTwoD, uD, ← hπ] using h
  have hQ : CFSG.Assembly.IsSubnormal ((normBlock E 3 ({0, 2} : Finset (Fin 3))).map κ₃)
      (Subgroup.centralizer ({κ₁ (qTwoRTwoA E χ)} : Set G)) := by
    rw [hblock]
    exact hA.2.1
  have hπ₃0 : (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) (Fin.castSucc (0 : Fin 3)) = π 0 := by
    change (Equiv.swap (π 2) (π (Fin.last 3))) (π 0) = π 0
    exact hτ0
  have hπ₃2 : (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) (Fin.castSucc (2 : Fin 3)) =
      π (Fin.last 3) := by
    change (Equiv.swap (π 2) (π (Fin.last 3))) (π 2) = π (Fin.last 3)
    exact hτ2
  refine GGSecFiveBPermOmKFrame.isComponentOf_map_normBlock_inf_centralizer_of_subset
    (E := E) (Bs := Bs) (X := L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom)
    (eta := eta) (π := π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) (κ := κ₃) (χ := χ)
    (Y := Subgroup.centralizer ({κ₁ (qTwoRTwoA E χ)} : Set G))
    (Q := ({0, 2} : Finset (Fin 3))) (d := dG) (by norm_num : 3 ≤ 3)
    (by norm_num : 3 ∣ 2 ^ 1 + 1) h₃ hQ hdG ({2} : Finset (Fin 3)) (by simp)
    (by intro j hj; rw [Finset.mem_singleton] at hj; subst j; simp) ?_
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · rw [hπ₃0]
    have hd0 : eta ⟨dG, hdG⟩ (π 0) = Multiplicative.ofAdd (1 : ZMod 3) := by
      simpa [uD] using hDcoord 0
    rw [hd0]
    simp only [Finset.mem_singleton]
    refine ⟨fun h => ?_, fun h => absurd h (by omega)⟩
    have h' : (1 : ZMod 3) = 0 := by simpa using congrArg Multiplicative.toAdd h
    exact (one_ne_zero h').elim
  · rw [hπ₃2, hDlast]
    simp

private theorem map_normAnchorFixing_le_normalizer_block
    {G : Type} [Group G]
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {κ₁ κ₂ κ₃ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    {t : Equiv.Perm (Fin 4) →* G}
    (hκ₃ : ∀ b, κ₃ b = t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹)
    (hF2 : Nat.card F = 2)
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) = κ₂.comp (normPerm E le_rfl))
    (hpoint : ∀ y : normOmega E 2, κ₁ (normPerm E le_rfl (finRotate 3) *
        normOmegaCast E (by norm_num) y * (normPerm E le_rfl (finRotate 3))⁻¹) =
      κ₂ (normOmegaCast E (by norm_num) y))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ₁, Commute (t (Equiv.swap 2 3)) y)
    (hσ : unitaryInvolution Kf 2 1 ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) =
      ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) ^ 2)
    (hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) +
      ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) ^ 2 = 0)
    (hNormA : ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃).map
        (MulAut.conj (κ₁ (threePlaneFourier E hσ hs))).toMonoidHom =
      (normBlock E 3 ({2} : Finset (Fin 3))).map κ₃) :
    (normAnchorFixing E 3).map κ₁ ≤ Subgroup.normalizer
      (((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ : Subgroup G) : Set G) := by
  have hP : ∀ S : Finset (Fin 3), S.card = 2 →
      (normBlock E 3 S ⊓ normAnchorFixing E 3).map κ₁ ≤
        Subgroup.normalizer (((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ : Subgroup G) :
          Set G) := by
    intro S hS
    rintro z ⟨n, hn, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hκ₃ b]
    exact (commute_conj_of_mem_normBlock_inf_normAnchorFixing_three (E := E) ht₂ hpoint
      hC hS hn hb).symm
  have hFou : κ₁ (threePlaneFourier E hσ hs) ∈ Subgroup.normalizer
      (((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hNormA
  exact map_normAnchorFixing_three_le_of_pairs (E := E) (G := G)
    κ₁ hF2 hσ hs hP hFou

private theorem map_normAnchorFixing_le_centralizer_block
    {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G}
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin 4}
    {κ₁ κ₃ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    (hF2 : Nat.card F = 2)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (hAcomp : CFSG.Assembly.IsComponentOf
      ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃)
      (Subgroup.centralizer ({κ₁ (qTwoRTwoA E χ)} : Set G) ⊓
        Subgroup.centralizer ({κ₁ (qTwoRTwoD E χ)} : Set G)))
    (hYnorm : (normAnchorFixing E 3).map κ₁ ≤ Subgroup.normalizer
      (((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ : Subgroup G) : Set G)) :
    (normAnchorFixing E 3).map κ₁ ≤ Subgroup.centralizer
      (((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ : Subgroup G) : Set G) := by
  let Y : Subgroup G := (normAnchorFixing E 3).map κ₁
  let dG : G := κ₁ (qTwoRTwoD E χ)
  let uD : Fin 3 → Multiplicative (ZMod 3) := fun _ => Multiplicative.ofAdd 1
  have hdG_ne : dG ≠ 1 := by
    intro h
    have hD : qTwoRTwoD E χ = 1 := h₁.1 (by simpa [dG] using h)
    have h1 : normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ uD = 1 := by
      simpa [qTwoRTwoD, uD] using hD
    have hu : uD = 1 :=
      normPlaneTorus_injective E (by norm_num : 2 ≤ 3)
        (by decide : 3 ∣ 2 ^ 1 + 1) h₁.2.2.1 (h1.trans (map_one _).symm)
    have h2 : Multiplicative.ofAdd (1 : ZMod 3) = 1 := by simpa [uD] using congrFun hu 0
    have hg1 : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 := by
      intro h'
      have h'' := congrArg Multiplicative.toAdd h'
      simp at h''
    exact hg1 h2
  have hdG_Y : dG ∈ Y := by
    refine Subgroup.mem_map_of_mem κ₁ ?_
    rw [mem_normAnchorFixing_iff]
    intro w
    have hDdef : qTwoRTwoD E χ = normPlaneTorus E (by norm_num : 2 ≤ 3)
        (by decide : 3 ∣ 2 ^ 1 + 1) χ uD := rfl
    rw [hDdef, normPlaneTorus_apply]
    exact Prod.ext rfl (funext fun i => by simp)
  have hYsimple : IsSimpleGroup Y := by
    have : IsSimpleGroup ↥(normAnchorFixing E 3) := isSimpleGroup_normAnchorFixing_three E hF2
    exact (Subgroup.equivMapOfInjective (normAnchorFixing E 3) κ₁ h₁.1).symm.isSimpleGroup
  let N : Subgroup G := Subgroup.zpowers dG
  have hNY : N ≤ Y := Subgroup.zpowers_le.mpr hdG_Y
  have hNA : N ≤ Subgroup.centralizer
      (((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hcomm := (hAcomp.1 hy).2
    change y ∈ Subgroup.centralizer ({dG} : Set G) at hcomm
    rw [Subgroup.mem_centralizer_singleton_iff] at hcomm
    exact hcomm
  have hNne : N ≠ ⊥ := by
    change Subgroup.zpowers dG ≠ ⊥
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hdG_ne
  have : IsSimpleGroup Y := hYsimple
  exact CFSG.LocalAnalysis.ComponentInitial.le_centralizer_of_le_normalizer
    hYnorm hNY hNA hNne

private theorem commute_normPureBlock_conj_of_le_centralizer
    {G : Type} [Group G]
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {κ₁ κ₃ : normOmega E 3 →* G} {t : Equiv.Perm (Fin 4) →* G}
    (hκ₃ : ∀ b, κ₃ b = t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹)
    (hYcent : (normAnchorFixing E 3).map κ₁ ≤ Subgroup.centralizer
      (((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ : Subgroup G) : Set G)) :
    ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ₁ a) (t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹) := by
  intro a ha b hb
  have haY : κ₁ a ∈ (normAnchorFixing E 3).map κ₁ :=
    Subgroup.mem_map_of_mem κ₁ (normPureBlock_le_normAnchorFixing E 3 Finset.univ ha)
  have hacent := hYcent haY
  rw [Subgroup.mem_centralizer_iff] at hacent
  have hbA : κ₃ b ∈ (normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ :=
    Subgroup.mem_map_of_mem κ₃ hb
  have hbA' : t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹ ∈
      (normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ := by
    simpa [hκ₃ b] using hbA
  exact (hacent _ hbA').symm

private theorem block_element_coords
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G}
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin 4} {i0 : Fin 4}
    {κ₁ κ₃ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    {t : Equiv.Perm (Fin 4) →* G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (hπ : π (Fin.last 3) = i0)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0)
    (hZ : Subgroup.center L = ⊥) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (htN : t (Equiv.swap 2 3) ∈ Subgroup.normalizer (Bs : Set G))
    (htAct : MulAut.congr eta (ggConjAut Bs htN) =
      SpCoord.permAut (Equiv.swap (π 2) (π (Fin.last 3))))
    (hBmap : Bs.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom = Bs)
    (hτ0 : (Equiv.swap (π 2) (π (Fin.last 3))) (π 0) = π 0)
    (hτ1 : (Equiv.swap (π 2) (π (Fin.last 3))) (π 1) = π 1)
    (hτ3 : (Equiv.swap (π 2) (π (Fin.last 3))) (π (Fin.last 3)) = π 2)
    (hκ₃ : ∀ b, κ₃ b = t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹)
    (e : G)
    (he : e = κ₃ (normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ
      (Pi.mulSingle 2 (Multiplicative.ofAdd 1)))) :
    e ∈ Bs ∧ (∀ (heBs : e ∈ Bs) (i : Fin 3), eta ⟨e, heBs⟩ (π i.castSucc) = 1) := by
  subst e
  let uE : Fin 3 → Multiplicative (ZMod 3) := Pi.mulSingle 2 (Multiplicative.ofAdd 1)
  let tE : normOmega E 3 := normPlaneTorus E (by norm_num : 2 ≤ 3)
    (by decide : 3 ∣ 2 ^ 1 + 1) χ uE
  have htE_Bs : κ₁ tE ∈ Bs :=
    h₁.normPlaneTorus_mem_Bs (E₁ := E) (hr := by norm_num) (hSC := hcfg.2.1.2.2.2) uE
  have heBs : κ₃ tE ∈ Bs := by
    have hmem : (MulAut.conj (t (Equiv.swap 2 3))) (κ₁ tE) ∈
        Bs.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom :=
      Subgroup.mem_map_of_mem _ htE_Bs
    rw [hBmap] at hmem
    simpa [hκ₃ tE] using hmem
  have htE_coord (i : Fin 3) : eta ⟨κ₁ tE, htE_Bs⟩ (π i.castSucc) = uE i := by
    have h := h₁.coords_normPlaneTorus (E₁ := E) (hr := by norm_num)
      (hSC := hcfg.2.1.2.2.2) (u := uE) i
    simpa [tE] using h
  have htElast : eta ⟨κ₁ tE, htE_Bs⟩ (π (Fin.last 3)) = 1 := by
    have h := h₁.normPlaneTorus_coord_last (E := E) (hr := by norm_num) hcfg hZ hN
      (hLeta := hL) (v := uE)
    simpa [tE, ← hπ] using h
  have he_eq : (ggConjAut Bs htN ⟨κ₁ tE, htE_Bs⟩ : ↥Bs) = ⟨κ₃ tE, heBs⟩ := by
    apply Subtype.ext
    simp only [ggConjAut_apply, hκ₃ tE]
  have hcoord_conj (j : Fin 4) :
      eta ⟨κ₃ tE, heBs⟩ ((Equiv.swap (π 2) (π (Fin.last 3))) j) = eta ⟨κ₁ tE, htE_Bs⟩ j := by
    rw [← he_eq]
    exact eta_ggConjAut_apply_of_permAut htN htAct _ j
  have he_coord (i : Fin 3) : eta ⟨κ₃ tE, heBs⟩ (π i.castSucc) = 1 := by
    fin_cases i
    · change eta ⟨κ₃ tE, heBs⟩ (π 0) = 1
      have h := hcoord_conj (π 0)
      rw [hτ0] at h
      have hb0 : eta ⟨κ₁ tE, htE_Bs⟩ (π 0) = 1 := by simpa [uE] using htE_coord 0
      rw [h, hb0]
    · change eta ⟨κ₃ tE, heBs⟩ (π 1) = 1
      have h := hcoord_conj (π 1)
      rw [hτ1] at h
      have hb1 : eta ⟨κ₁ tE, htE_Bs⟩ (π 1) = 1 := by simpa [uE] using htE_coord 1
      rw [h, hb1]
    · change eta ⟨κ₃ tE, heBs⟩ (π 2) = 1
      have h := hcoord_conj (π (Fin.last 3))
      rw [hτ3] at h
      rw [h, htElast]
  exact ⟨heBs, fun heBs' i => he_coord i⟩

private theorem block_element_nontrivial
    {G : Type} [Group G] [Finite G]
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {κ₃ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    (hχ : Function.Injective χ) (hκ₃inj : Function.Injective κ₃)
    (e : G)
    (he : e = κ₃ (normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ
      (Pi.mulSingle 2 (Multiplicative.ofAdd 1)))) :
    e ∈ (normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ ∧ e ≠ 1 := by
  subst e
  let uE : Fin 3 → Multiplicative (ZMod 3) := Pi.mulSingle 2 (Multiplicative.ofAdd 1)
  let tE : normOmega E 3 := normPlaneTorus E (by norm_num : 2 ≤ 3)
    (by decide : 3 ∣ 2 ^ 1 + 1) χ uE
  constructor
  · refine Subgroup.mem_map_of_mem κ₃ ?_
    have huE : ∀ i, i ∉ ({2} : Finset (Fin 3)) → uE i = 1 := by
      intro i hi
      rw [Finset.mem_singleton] at hi
      simp [uE, hi]
    simpa [tE] using normPlaneTorus_mem_normBlock_of_support E (by norm_num : 2 ≤ 3) χ
      ({2} : Finset (Fin 3)) uE huE
  · have hg1 : Multiplicative.ofAdd (1 : ZMod 3) ≠ 1 := by
      intro h'
      have h'' := congrArg Multiplicative.toAdd h'
      simp at h''
    intro h
    have ht : tE = 1 := hκ₃inj (by simpa [tE] using h)
    have hu : uE = 1 := normPlaneTorus_injective E (by norm_num : 2 ≤ 3)
      (by decide : 3 ∣ 2 ^ 1 + 1) hχ (by
        rw [show normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ uE =
          1 from by simpa [tE] using ht, map_one])
    have h2 : Multiplicative.ofAdd (1 : ZMod 3) = 1 := by simpa [uE] using congrFun hu 2
    exact hg1 h2

private theorem fourier_fixes_block_element
    {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G}
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin 4}
    {κ₁ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (hσ : unitaryInvolution Kf 2 1 ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) =
      ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) ^ 2)
    (hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) +
      ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) ^ 2 = 0)
    (e : G) (heBs : e ∈ Bs)
    (he_coord : ∀ i : Fin 3, eta ⟨e, heBs⟩ (π i.castSucc) = 1) :
    κ₁ (threePlaneFourier E hσ hs) * e * (κ₁ (threePlaneFourier E hσ hs))⁻¹ = e := by
  obtain ⟨T, hTv, hTc⟩ := h₁.2.2.2 ⟨e, heBs⟩
  have hT1 : T = 1 := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hTv v]
    refine Prod.ext rfl (funext fun i => ?_)
    simp [he_coord i]
  have he_comm (s : normOmega E 3) : e * κ₁ s * e⁻¹ = κ₁ s := by
    have h := hTc s
    rw [hT1] at h
    simpa using h
  have hee : e * κ₁ (threePlaneFourier E hσ hs) * e⁻¹ = κ₁ (threePlaneFourier E hσ hs) :=
    he_comm _
  have hge : κ₁ (threePlaneFourier E hσ hs) * e * (κ₁ (threePlaneFourier E hσ hs))⁻¹ = e := by
    have h1 : e * κ₁ (threePlaneFourier E hσ hs) = κ₁ (threePlaneFourier E hσ hs) * e := by
      calc e * κ₁ (threePlaneFourier E hσ hs)
          = (e * κ₁ (threePlaneFourier E hσ hs) * e⁻¹) * e := by group
        _ = κ₁ (threePlaneFourier E hσ hs) * e := by rw [hee]
    calc κ₁ (threePlaneFourier E hσ hs) * e * (κ₁ (threePlaneFourier E hσ hs))⁻¹
        = e * κ₁ (threePlaneFourier E hσ hs) * (κ₁ (threePlaneFourier E hσ hs))⁻¹ := by
          rw [← h1]
      _ = e := by group
  exact hge

private theorem map_conj_threePlaneFourier_block
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G}
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))} {π : Fin 4 ≃ Fin 4} {i0 : Fin 4}
    {κ₁ κ₃ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    {t : Equiv.Perm (Fin 4) →* G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (h₃ : GGSecFiveBPermOmKFrame E Bs (L.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom)
      eta (π.trans (Equiv.swap (π 2) (π (Fin.last 3)))) κ₃ χ)
    (hπ : π (Fin.last 3) = i0)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0)
    (hZ : Subgroup.center L = ⊥) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (htN : t (Equiv.swap 2 3) ∈ Subgroup.normalizer (Bs : Set G))
    (htAct : MulAut.congr eta (ggConjAut Bs htN) =
      SpCoord.permAut (Equiv.swap (π 2) (π (Fin.last 3))))
    (hBmap : Bs.map (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom = Bs)
    (hτ0 : (Equiv.swap (π 2) (π (Fin.last 3))) (π 0) = π 0)
    (hτ1 : (Equiv.swap (π 2) (π (Fin.last 3))) (π 1) = π 1)
    (hτ3 : (Equiv.swap (π 2) (π (Fin.last 3))) (π (Fin.last 3)) = π 2)
    (hκ₃ : ∀ b, κ₃ b = t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹)
    (hAcompUG : CFSG.Assembly.IsComponentOf
      ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃)
      (Subgroup.centralizer (((qTwoRTwoU E χ).map κ₁ : Subgroup G) : Set G)))
    (hAcenter : Subgroup.center ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃) = ⊥)
    (hσ : unitaryInvolution Kf 2 1 ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) =
      ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) ^ 2)
    (hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) +
      ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) ^ 2 = 0) :
    ((normBlock E 3 ({2} : Finset (Fin 3))).map κ₃).map
        (MulAut.conj (κ₁ (threePlaneFourier E hσ hs))).toMonoidHom =
      (normBlock E 3 ({2} : Finset (Fin 3))).map κ₃ := by
  let Φ : normOmega E 3 := threePlaneFourier E hσ hs
  let ĝ : G := κ₁ Φ
  have hmapU := map_conj_threePlaneFourier_qTwoRTwoU E χ hσ hs
  have hgU : ((qTwoRTwoU E χ).map κ₁).map (MulAut.conj ĝ).toMonoidHom =
      (qTwoRTwoU E χ).map κ₁ := by
    have hcomp : (MulAut.conj ĝ).toMonoidHom.comp κ₁ =
        κ₁.comp (MulAut.conj Φ).toMonoidHom := by
      ext n
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv, ĝ, Φ]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hmapU]
  let e : G := κ₃ (normPlaneTorus E (by norm_num : 2 ≤ 3) (by decide : 3 ∣ 2 ^ 1 + 1) χ
    (Pi.mulSingle 2 (Multiplicative.ofAdd 1)))
  obtain ⟨heBs, he_coord⟩ := block_element_coords hcfg h₁ hπ hL hZ hN htN htAct hBmap
    hτ0 hτ1 hτ3 hκ₃ e rfl
  obtain ⟨heA, he1⟩ := block_element_nontrivial (κ₃ := κ₃) h₁.2.2.1 h₃.1 e rfl
  have hge : ĝ * e * ĝ⁻¹ = e := by
    simpa [ĝ, Φ] using fourier_fixes_block_element h₁ hσ hs e heBs (fun i => he_coord heBs i)
  exact CFSG.LocalAnalysis.ComponentInitial.map_conj_eq_of_isComponentOf_centralizer
    hAcompUG hAcenter hgU heA he1 hge
section Context


private theorem isComponentOf_ggBlockComm_centralizer_four
    {G : Type} [Group G] [Finite G]
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hLB : GGLBalanceInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))) (i0 : Fin 4)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 3)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L)
    (hAll : ∀ (y : G) (M : Subgroup G), GGNbr 3 B x D J y M →
      ggAutomizer M Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ M ∈ 𝒦, M)
    (S : Finset (Fin 4)) (hS : S.card = 2) {aG : G} (haG : aG ∈ Bs)
    (hdS : ∀ c ∈ S, eta ⟨aG, haG⟩ c = 1)
    (hdSc : ∀ c ∉ S, eta ⟨aG, haG⟩ c ≠ 1) :
    CFSG.Assembly.IsComponentOf (ggBlockComm Bs eta (S : Set (Fin 4)))
      (Subgroup.centralizer ({aG} : Set G)) :=
  GGSecFiveRouteCfg.isComponentOf_ggBlockComm_centralizer_of_qTwoOrth_four
    (p := 3) (B := B) (Bs := Bs) (x := x) (L := L) (D := D) (J := J) (𝒦 := 𝒦)
    (hX := hX) (hTCJ := hTCJ) (hRig := hRig) (hTPn := hTPn) (hA8 := hA8)
    (hraw := hraw) (hiso := hiso) (hFC := hFC) (hLB := hLB) (hR := hR) (hB := hB)
    (eta := eta) (i0 := i0) (h𝒦 := h𝒦) (hL := hL) (hLab := hLab) (hAll := hAll)
    (hG0 := hG0) (S := S) (hS := hS) (d := aG) (hd := haG) (hdS := hdS) (hdSc := hdSc)

private theorem isComponentOf_ggBlockComm_centralizer_qTwoRTwoA
    {G : Type} [Group G] [Finite G]
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) (hLB : GGLBalanceInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))) (i0 : Fin 4)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 3)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L)
    (hAll : ∀ (y : G) (M : Subgroup G), GGNbr 3 B x D J y M →
      ggAutomizer M Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ M ∈ 𝒦, M)
    (hZ : Subgroup.center L = ⊥) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)}
    {π : Fin 4 ≃ Fin 4} {κ₁ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    (hπ : π (Fin.last 3) = i0)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ) :
    CFSG.Assembly.IsComponentOf
      (ggBlockComm Bs eta (({π 0, π (Fin.last 3)} : Finset (Fin 4)) : Set (Fin 4)))
      (Subgroup.centralizer ({κ₁ (qTwoRTwoA E χ)} : Set G)) := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  have haG : κ₁ (qTwoRTwoA E χ) ∈ Bs := by
    simpa [qTwoRTwoA] using
      (h₁.normPlaneTorus_mem_Bs (E₁ := E) (hr := by norm_num)
        (hSC := hcfg.2.1.2.2.2) (u := ![1, Multiplicative.ofAdd 1, Multiplicative.ofAdd 2]))
  obtain ⟨hdS, hdSc⟩ := qTwoRTwoA_support hcfg h₁ hπ hL hZ hN
    (κ₁ (qTwoRTwoA E χ)) haG rfl
  have hS2 : ({π 0, π (Fin.last 3)} : Finset (Fin 4)).card = 2 :=
    Finset.card_pair (fun h => (by decide : (0 : Fin 4) ≠ Fin.last 3) (π.injective h))
  exact isComponentOf_ggBlockComm_centralizer_four hX hTCJ hRig hTPn hA8 hraw hiso hFC hLB
    hR hB eta i0 h𝒦 hL hLab hAll hG0 ({π 0, π (Fin.last 3)}) hS2 haG hdS hdSc

theorem GGSecFiveRouteCfg.commute_normPureBlock_conj_of_qTwoOrth_four
    {G : Type} [Group G] [Finite G]
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hLB : GGLBalanceInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hB : B = Bs)
    (eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod 3))) (i0 : Fin 4)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull 4 3)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 3 i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel 4 p lab ∧
      (lab.n = 1 ∧ (lab.tag = .twD ∨ lab.tag = .D))) 3 Bs L)
    (hAll : ∀ (y : G) (M : Subgroup G), GGNbr 3 B x D J y M →
      ggAutomizer M Bs ≤ ggAutomizerJoin L Bs 𝒦)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ M ∈ 𝒦, M)
    (hZ : Subgroup.center L = ⊥) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {F Kf : Type} [Field F] [Field Kf] [Algebra F Kf] [Finite Kf] [CharP Kf 2]
    {E : QuadExt F Kf (unitaryInvolution Kf 2 1)} (hF2 : Nat.card F = 2)
    {π : Fin 4 ≃ Fin 4} {κ₁ κ₂ : normOmega E 3 →* G} {χ : Multiplicative (ZMod 3) →* Kfˣ}
    {t : Equiv.Perm (Fin 4) →* G} (hπ : π (Fin.last 3) = i0)
    (h₁ : GGSecFiveBPermOmKFrame E Bs L eta π κ₁ χ)
    (ht₂ : t.comp (Equiv.Perm.viaEmbeddingHom (Fin.succEmb 3)) = κ₂.comp (normPerm E le_rfl))
    (hpoint : ∀ y : normOmega E 2, κ₁ (normPerm E le_rfl (finRotate 3) *
        normOmegaCast E (by norm_num) y * (normPerm E le_rfl (finRotate 3))⁻¹) =
      κ₂ (normOmegaCast E (by norm_num) y))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ₁, Commute (t (Equiv.swap 2 3)) y)
    (htN : t (Equiv.swap 2 3) ∈ Subgroup.normalizer (Bs : Set G))
    (htAct : MulAut.congr eta (ggConjAut Bs htN) =
      SpCoord.permAut (Equiv.swap (π 2) (π (Fin.last 3)))) :
    ∀ a ∈ normPureBlock E 3 Finset.univ, ∀ b ∈ normBlock E 3 {2},
      Commute (κ₁ a) (t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹) := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hR.1.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hBmap, hyB, hL₃c, h₃⟩ := transported_frame_facts hcfg h₁ htN htAct
  let κ₃ : normOmega E 3 →* G := (MulAut.conj (t (Equiv.swap 2 3))).toMonoidHom.comp κ₁
  have hκ₃ : ∀ b, κ₃ b = t (Equiv.swap 2 3) * κ₁ b * (t (Equiv.swap 2 3))⁻¹ :=
    fun b => by simp [κ₃, MulAut.conj_apply]
  have hcompA := isComponentOf_ggBlockComm_centralizer_qTwoRTwoA hX hTCJ hRig hTPn hA8 hraw hiso
    hFC hLB hR hB eta i0 h𝒦 hL hLab hAll hG0 hZ hN hπ h₁
  obtain ⟨hτ0, hτ1, hτ2, hτ3, hset⟩ := plane_image_facts π
  have hblock := map_normBlock_zero_two_eq_ggBlockComm hSC h₃ hyB hL₃c hset
  have hAcomp := isComponentOf_centralizer_inf_qTwoRTwoD hcfg hSC h₁ hπ hL hZ hN h₃ hcompA hblock
    hτ0 hτ2
  have hAcompUG := isComponentOf_centralizer_map_qTwoRTwoU hκ₃ ht₂ hpoint hC hAcomp
  have hAcenter := center_map_normBlock_two_eq_bot (E := E) (κ := κ₃) h₃.1
  have hσ : unitaryInvolution Kf 2 1 ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) =
      ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) ^ 2 := unitaryInvolution_two_one_apply _
  have hs : 1 + ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) +
      ((χ (Multiplicative.ofAdd 1) : Kfˣ) : Kf) ^ 2 = 0 :=
    one_add_add_sq_eq_zero_of_injective h₁.2.2.1
  have hNormA := map_conj_threePlaneFourier_block hcfg h₁ h₃ hπ hL hZ hN htN htAct hBmap
    hτ0 hτ1 hτ3 hκ₃ hAcompUG hAcenter hσ hs
  have hYnorm := map_normAnchorFixing_le_normalizer_block hκ₃ hF2 ht₂ hpoint hC hσ hs hNormA
  have hYcent := map_normAnchorFixing_le_centralizer_block hF2 h₁ hAcomp hYnorm
  exact commute_normPureBlock_conj_of_le_centralizer hκ₃ hYcent

end Context

end CFSG.StandardType
