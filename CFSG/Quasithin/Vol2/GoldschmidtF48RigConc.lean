module

public import CFSG.Quasithin.Vol2.GoldschmidtF48RigEqv
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigExt

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion

universe u

section Generic

variable {S : LieSetting.{u, 0}} {Y : Type} [Group Y] (β : S.α.Completion Y)

theorem isEquivalent_of_equiv (θ : β.G0 ≃* S.ι.G0)
    (h1 : ∀ p, θ (f1 (c := β) p) = f1 (c := S.ι) p)
    (h2 : ∀ q, θ (f2 (c := β) q) = f2 (c := S.ι) q) :
    Amalgam.Completion.IsEquivalent β.toCompletion S.ι.toCompletion := by
  let eβ : β.G0 ≃* Y := (MulEquiv.subgroupCongr β.gen).trans Subgroup.topEquiv
  let eι : S.ι.G0 ≃* S.Yb := (MulEquiv.subgroupCongr S.ι.gen).trans Subgroup.topEquiv
  have hφ1 : ∀ p, (eβ.symm.trans (θ.trans eι)) (β.φ1 p) = S.ι.φ1 p := fun p => by
    have : eβ.symm (β.φ1 p) = f1 (c := β) p := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, h1]
    rfl
  have hφ2 : ∀ q, (eβ.symm.trans (θ.trans eι)) (β.φ2 q) = S.ι.φ2 q := fun q => by
    have : eβ.symm (β.φ2 q) = f2 (c := β) q := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [MulEquiv.trans_apply, this, h2]
    rfl
  refine ⟨eβ.symm.trans (θ.trans eι), fun d x => ?_⟩
  cases d
  · exact hφ1 x
  · exact hφ2 x
  · have e1 := hφ1 (S.α.α1 (x : S.α.G12))
    have e2 := congrArg (eβ.symm.trans (θ.trans eι)) (β.comm1 (x : S.α.G12))
    exact (e2.symm.trans e1).trans (S.ι.comm1 (x : S.α.G12))

theorem f48Concl_of_equiv (θ : β.G0 ≃* S.ι.G0) (h1 : ∀ p, θ (f1 (c := β) p) = f1 (c := S.ι) p)
    (h2 : ∀ q, θ (f2 (c := β) q) = f2 (c := S.ι) q) (hext : S.IsExtension S.Yb) :
    S.F48Concl β := by
  have heq := isEquivalent_of_equiv β θ h1 h2
  refine ⟨⟨S.Yb, inferInstance, S.ι, S.hι, heq, hext⟩, fun _ => ?_⟩
  rw [Amalgam.Completion.isQuasiEquivalent_iff_exists_act]
  exact ⟨1, by rw [Amalgam.Completion.act_one]; exact heq⟩

end Generic

theorem f431F48_of_model {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hm : F431ModelFacts t m f) (h45 : F431Facts45 t m f hm) (hgen : F431Generation t m f)
    (hT : ∀ (D : Type) [Group D] (hD : CFSG.Blueprint.LieModel D t m 2 f) (A : LieAmalgamExt D),
      (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).CartanFPF)
    (hF : ∀ (D : Type) [Group D] (hD : CFSG.Blueprint.LieModel D t m 2 f) (A : LieAmalgamExt D),
      (A.setting (hm D hD).1 (polyNumber t) (three_le_polyNumber t)).FaithfulOnType
        (decide (Odd (polyNumber t)))) :
    F431F48 t m f hm := by
  intro D _ hD A Y _ _ β hβ hs
  obtain ⟨θ, h1, h2⟩ := exists_equiv_small (h45 D hD A) β hβ hs (hT D hD A) (hF D hD A)
  exact f48Concl_of_equiv β θ h1 h2
    (isExtension_setting A (hm D hD).1 (polyNumber t) (three_le_polyNumber t) (hm D hD).2
      (hgen D hD A))

end CFSG.Quasithin.H13.F48Rig
