module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Defs
public import CFSG.LocalAnalysis.WeakClosure81.W18KernPack
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx188

variable {D : Data G} {V₀ V H : Subgroup G} {i j : ℕ}

theorem w183b2ed_eOmegaZ_le_conj_M (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) : eOmegaZ H D.T ≤ conjSubgroup D.M g := by
  have hbot := x.inf_ne_bot_of_gam183 hg
  obtain ⟨w, hw, hwbot⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hbot)
  have hw1 : w ≠ 1 := fun h1 => hwbot (Subgroup.mem_bot.mpr h1)
  have hwCent : eOmegaZ H D.T ≤ Subgroup.centralizer ({w} : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr x.hyp.isElemAbelian_eOmegaZ.1).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw.1))
  exact hwCent.trans (centralizer_le_conj_M x.hyp.setting x.hyp.ne_bot g hw.2 hw1)

noncomputable def w183b2ed_EDgCore (x : Ctx188 D V₀ V H i j) (g : G)
    (hg : Gam183 V H (eOmegaZ H D.T) i g) : Subgroup G where
  carrier := {e | e ∈ eOmegaZ H D.T ∧
    ∀ v ∈ conjSubgroup V g, ⁅v, e⁆ ∈ conjSubgroup V₀ g}
  mul_mem' := by
    rintro e₁ e₂ ⟨he₁E, he₁⟩ ⟨he₂E, he₂⟩
    have hE : eOmegaZ H D.T ≤ conjSubgroup D.M g := x.w183b2ed_eOmegaZ_le_conj_M hg
    have hMnorm : conjSubgroup D.M g ≤
        Subgroup.normalizer (conjSubgroup V₀ g : Set G) := by
      rw [← E3.conjSubgroup_normalizer, x.hyp.setting.normalizer₀ x.hyp.ne_bot]
    refine ⟨(eOmegaZ H D.T).mul_mem he₁E he₂E, fun v hv => ?_⟩
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : ⁅v, e₁⁆ ∈ conjSubgroup V₀ g := he₁ v hv
    have h2 : e₁ * ⁅v, e₂⁆ * e₁⁻¹ ∈ conjSubgroup V₀ g :=
      ((Subgroup.mem_normalizer_iff.mp (hMnorm (hE he₁E))) (⁅v, e₂⁆)).mp (he₂ v hv)
    simpa only [mul_assoc] using (conjSubgroup V₀ g).mul_mem h1 h2
  one_mem' := ⟨(eOmegaZ H D.T).one_mem, fun v _ => by
    rw [commutatorElement_one_right]; exact (conjSubgroup V₀ g).one_mem⟩
  inv_mem' := by
    rintro e ⟨heE, he⟩
    have he2 : e * e = 1 := by
      simpa [pow_two] using x.hyp.isElemAbelian_eOmegaZ.2 e heE
    have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    refine ⟨(eOmegaZ H D.T).inv_mem heE, fun v hv => ?_⟩
    rw [heinv]
    exact he v hv

noncomputable def w183b2ed_EDg (x : Ctx188 D V₀ V H i j) (g : G) : Subgroup G := by
  classical
  exact if hg : Gam183 V H (eOmegaZ H D.T) i g then x.w183b2ed_EDgCore g hg else ⊥

theorem w183b2ed_mem_EDg (x : Ctx188 D V₀ V H i j) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) i g) {e : G} :
    e ∈ x.w183b2ed_EDg g ↔ e ∈ eOmegaZ H D.T ∧
      ∀ v ∈ conjSubgroup V g, ⁅v, e⁆ ∈ conjSubgroup V₀ g := by
  classical
  unfold w183b2ed_EDg
  rw [dif_pos hg]
  rfl

variable {M : ModDataE H (eOmegaZ H D.T)}

noncomputable def w183b2ed_ED (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    (A : Subgroup (LGL 2 M.W)) : Submodule (ZMod 2) M.W := by
  classical
  exact if h : ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧
      M.img (vInH V H g) = A ∧
      E3.mQuot (conjSubgroup V g) (vInH V H g) = packDeltaU D V H i M A
    then M.sp (x.w183b2ed_EDg (Classical.choose h))
    else ⊥

theorem w183b2ed_ED_eq (x : Ctx188 D V₀ V H i j) (M : ModDataE H (eOmegaZ H D.T))
    {A : Subgroup (LGL 2 M.W)}
    (hex : ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧ M.img (vInH V H g) = A ∧
      E3.mQuot (conjSubgroup V g) (vInH V H g) = packDeltaU D V H i M A) :
    x.w183b2ed_ED M A = M.sp (x.w183b2ed_EDg (Classical.choose hex)) := by
  unfold w183b2ed_ED
  rw [dif_pos hex]

theorem w183b2ed_exists_attaining (x : Ctx188 D V₀ V H i j)
    (M : ModDataE H (eOmegaZ H D.T)) {A : Subgroup (LGL 2 M.W)}
    (hA : A ∈ packFamilyU D V H i M) :
    ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧ M.img (vInH V H g) = A ∧
      E3.mQuot (conjSubgroup V g) (vInH V H g) = packDeltaU D V H i M A := by
  obtain ⟨g, hg, rfl⟩ := hA
  have hne : ({k | ∃ g' : G, Gam183 V H (eOmegaZ H D.T) i g' ∧
      M.img (vInH V H g') = M.img (vInH V H g) ∧
      E3.mQuot (conjSubgroup V g') (vInH V H g') = k} : Set ℕ).Nonempty :=
    ⟨_, g, hg, rfl, rfl⟩
  have hmem : packDeltaU D V H i M (M.img (vInH V H g)) ∈
      {k | ∃ g' : G, Gam183 V H (eOmegaZ H D.T) i g' ∧
        M.img (vInH V H g') = M.img (vInH V H g) ∧
        E3.mQuot (conjSubgroup V g') (vInH V H g') = k} := by
    rw [packDeltaU]
    exact Nat.sInf_mem hne
  obtain ⟨g', hg', himg, hdelta⟩ := hmem
  exact ⟨g', hg', himg, hdelta⟩

theorem w183b2ed_comm_le (x : Ctx188 D V₀ V H i j)
    (M : ModDataE H (eOmegaZ H D.T)) :
    ∀ A ∈ packFamilyU D V H i M,
      CFSG.Quasithin.G11.commSpace A (x.w183b2ed_ED M A) ≤
        packSpaceU D V₀ V H i M A := by
  intro A hA
  obtain ⟨g, hg, himg, hdelta⟩ := x.w183b2ed_exists_attaining M hA
  have hex : ∃ g : G, Gam183 V H (eOmegaZ H D.T) i g ∧ M.img (vInH V H g) = A ∧
      E3.mQuot (conjSubgroup V g) (vInH V H g) = packDeltaU D V H i M A :=
    ⟨g, hg, himg, hdelta⟩
  have hspec := Classical.choose_spec hex
  rw [w183b2ed_ED, dif_pos hex]
  have hmem : ⁅x.w183b2ed_EDg (Classical.choose hex) ⊓ eOmegaZ H D.T,
      vInH V H (Classical.choose hex)⁆ ≤ conjSubgroup V₀ (Classical.choose hex) := by
    refine Subgroup.commutator_le.2 fun e he d hd => ?_
    obtain ⟨heED, -⟩ := Subgroup.mem_inf.1 he
    have hcond := ((x.w183b2ed_mem_EDg hspec.1).1 heED).2
    have hdV : d ∈ conjSubgroup V (Classical.choose hex) := (Subgroup.mem_inf.1 hd).1
    have h1 : ⁅d, e⁆ ∈ conjSubgroup V₀ (Classical.choose hex) := hcond d hdV
    rw [← commutatorElement_inv]
    exact (conjSubgroup V₀ (Classical.choose hex)).inv_mem h1
  have hcomm := M.commSpace_img_sp_le (A := vInH V H (Classical.choose hex))
    (X := x.w183b2ed_EDg (Classical.choose hex))
    (S := conjSubgroup V₀ (Classical.choose hex)) inf_le_right hmem
  rw [hspec.2.1] at hcomm
  refine hcomm.trans ?_
  exact le_iSup (fun g' : {g' : G // Gam183 V H (eOmegaZ H D.T) i g' ∧
      M.img (vInH V H g') = A} =>
        M.sp (conjSubgroup V₀ g'.1)) ⟨Classical.choose hex, hspec.1, hspec.2.1⟩

end Ctx188

end CFSG.LocalAnalysis.WeakClosure81

end
