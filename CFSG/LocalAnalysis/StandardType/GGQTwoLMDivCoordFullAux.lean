module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.UCoord
open Multiplicative

abbrev qTwoLMDivF_oneVec (m : ℕ) : Fin m → Multiplicative (ZMod 3) :=
  fun _ => Multiplicative.ofAdd (1 : ZMod 3)

theorem qTwoLMDivF_permAut_oneVec (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    SpCoord.permAut (p := 3) σ (qTwoLMDivF_oneVec m) = qTwoLMDivF_oneVec m := by
  funext i
  simp [qTwoLMDivF_oneVec, SpCoord.permAut_apply]

theorem qTwoLMDivF_permAut_map (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    (Subgroup.zpowers (qTwoLMDivF_oneVec m)).map
        (SpCoord.permAut (p := 3) σ :
          (Fin m → Multiplicative (ZMod 3)) →* (Fin m → Multiplicative (ZMod 3))) =
      Subgroup.zpowers (qTwoLMDivF_oneVec m) := by
  rw [MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers (qTwoLMDivF_permAut_oneVec m σ)

theorem qTwoLMDivF_permAut_mul (m : ℕ) (σ τ : Equiv.Perm (Fin m)) :
    (SpCoord.permAut (p := 3) (σ * τ) : MulAut (Fin m → Multiplicative (ZMod 3))) =
      SpCoord.permAut (p := 3) σ * SpCoord.permAut (p := 3) τ := by
  refine MulEquiv.ext fun f => ?_
  funext i
  simp only [MulAut.mul_apply, SpCoord.permAut_apply, Function.comp_apply, mul_inv_rev,
    Equiv.Perm.mul_apply]

noncomputable def qTwoLMDivF_permQ (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    MulAut (QTwoQm m) :=
  QuotientGroup.congr (Subgroup.zpowers (qTwoLMDivF_oneVec m))
    (Subgroup.zpowers (qTwoLMDivF_oneVec m)) (SpCoord.permAut (p := 3) σ)
    (qTwoLMDivF_permAut_map m σ)

theorem qTwoLMDivF_permQ_mk (m : ℕ) (σ : Equiv.Perm (Fin m))
    (v : Fin m → Multiplicative (ZMod 3)) :
    qTwoLMDivF_permQ m σ (QuotientGroup.mk v) =
      QuotientGroup.mk (SpCoord.permAut (p := 3) σ v) := by
  show QuotientGroup.congr (Subgroup.zpowers (qTwoLMDivF_oneVec m))
      (Subgroup.zpowers (qTwoLMDivF_oneVec m)) (SpCoord.permAut (p := 3) σ)
      (qTwoLMDivF_permAut_map m σ) (QuotientGroup.mk v) = _
  rw [QuotientGroup.congr_mk]

theorem qTwoLMDivF_permQ_mul (m : ℕ) (σ τ : Equiv.Perm (Fin m)) :
    qTwoLMDivF_permQ m (σ * τ) = qTwoLMDivF_permQ m σ * qTwoLMDivF_permQ m τ := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x fun g => ?_
  show QuotientGroup.congr (Subgroup.zpowers (qTwoLMDivF_oneVec m))
      (Subgroup.zpowers (qTwoLMDivF_oneVec m)) (SpCoord.permAut (p := 3) (σ * τ))
      (qTwoLMDivF_permAut_map m (σ * τ)) (QuotientGroup.mk g) =
    (QuotientGroup.congr (Subgroup.zpowers (qTwoLMDivF_oneVec m))
      (Subgroup.zpowers (qTwoLMDivF_oneVec m)) (SpCoord.permAut (p := 3) σ)
      (qTwoLMDivF_permAut_map m σ) *
    QuotientGroup.congr (Subgroup.zpowers (qTwoLMDivF_oneVec m))
      (Subgroup.zpowers (qTwoLMDivF_oneVec m)) (SpCoord.permAut (p := 3) τ)
      (qTwoLMDivF_permAut_map m τ)) (QuotientGroup.mk g)
  rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
    qTwoLMDivF_permAut_mul, MulAut.mul_apply]

@[expose] noncomputable def qTwoLMDivF_permQHom (m : ℕ) :
    Equiv.Perm (Fin m) →* MulAut (QTwoQm m) :=
  MonoidHom.mk' (fun σ => qTwoLMDivF_permQ m σ) (qTwoLMDivF_permQ_mul m)

theorem qTwoLMDivF_isQmModel (m : ℕ) :
    IsQmModel m (QTwoQm m) (qTwoLMDivF_permQHom m) := by
  refine ⟨QuotientGroup.mk' (Subgroup.zpowers (qTwoLMDivF_oneVec m)),
    QuotientGroup.mk'_surjective _, ?_, ?_⟩
  · intro v
    exact QuotientGroup.eq_one_iff v
  · intro σ v
    exact (qTwoLMDivF_permQ_mk m σ v).symm

theorem qTwoLMDivF_permAutV_oneVec (m : ℕ) (h3 : 3 ∣ m) (σ : Equiv.Perm (Fin m)) :
    permAutVHom m 3 σ (qTwoOneVec m h3) = qTwoOneVec m h3 := by
  rw [permAutVHom_apply]
  apply ext_crd
  intro k
  rw [crd_permAutV]
  rfl

theorem qTwoLMDivF_permAutV_map (m : ℕ) (h3 : 3 ∣ m) (σ : Equiv.Perm (Fin m)) :
    (Subgroup.zpowers (qTwoOneVec m h3)).map
        (permAutVHom m 3 σ : ↥(sumZero m 3) →* ↥(sumZero m 3)) =
      Subgroup.zpowers (qTwoOneVec m h3) := by
  rw [MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers (qTwoLMDivF_permAutV_oneVec m h3 σ)

noncomputable def qTwoLMDivF_permH (m : ℕ) (h3 : 3 ∣ m) (σ : Equiv.Perm (Fin m)) :
    MulAut (QTwoHm m h3) :=
  QuotientGroup.congr (Subgroup.zpowers (qTwoOneVec m h3))
    (Subgroup.zpowers (qTwoOneVec m h3)) (permAutVHom m 3 σ)
    (qTwoLMDivF_permAutV_map m h3 σ)

theorem qTwoLMDivF_permH_mk (m : ℕ) (h3 : 3 ∣ m) (σ : Equiv.Perm (Fin m))
    (v : ↥(sumZero m 3)) :
    qTwoLMDivF_permH m h3 σ (QuotientGroup.mk v) =
      QuotientGroup.mk (permAutVHom m 3 σ v) := by
  show QuotientGroup.congr (Subgroup.zpowers (qTwoOneVec m h3))
      (Subgroup.zpowers (qTwoOneVec m h3)) (permAutVHom m 3 σ)
      (qTwoLMDivF_permAutV_map m h3 σ) (QuotientGroup.mk v) = _
  rw [QuotientGroup.congr_mk]

theorem qTwoLMDivF_permH_mul (m : ℕ) (h3 : 3 ∣ m) (σ τ : Equiv.Perm (Fin m)) :
    qTwoLMDivF_permH m h3 (σ * τ) = qTwoLMDivF_permH m h3 σ * qTwoLMDivF_permH m h3 τ := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x fun g => ?_
  show QuotientGroup.congr (Subgroup.zpowers (qTwoOneVec m h3))
      (Subgroup.zpowers (qTwoOneVec m h3)) (permAutVHom m 3 (σ * τ))
      (qTwoLMDivF_permAutV_map m h3 (σ * τ)) (QuotientGroup.mk g) =
    (QuotientGroup.congr (Subgroup.zpowers (qTwoOneVec m h3))
      (Subgroup.zpowers (qTwoOneVec m h3)) (permAutVHom m 3 σ)
      (qTwoLMDivF_permAutV_map m h3 σ) *
    QuotientGroup.congr (Subgroup.zpowers (qTwoOneVec m h3))
      (Subgroup.zpowers (qTwoOneVec m h3)) (permAutVHom m 3 τ)
      (qTwoLMDivF_permAutV_map m h3 τ)) (QuotientGroup.mk g)
  rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
    permAutVHom_apply, permAutV_mul, MulAut.mul_apply]
  rfl

@[expose] noncomputable def qTwoLMDivF_permHHom (m : ℕ) (h3 : 3 ∣ m) :
    Equiv.Perm (Fin m) →* MulAut (QTwoHm m h3) :=
  MonoidHom.mk' (fun σ => qTwoLMDivF_permH m h3 σ) (qTwoLMDivF_permH_mul m h3)

theorem qTwoLMDivF_isHmModel (m : ℕ) (h3 : 3 ∣ m) :
    IsHmModel m h3 (QTwoHm m h3) (qTwoLMDivF_permHHom m h3) := by
  refine ⟨QuotientGroup.mk' (Subgroup.zpowers (qTwoOneVec m h3)),
    QuotientGroup.mk'_surjective _, ?_, ?_⟩
  · intro v
    exact QuotientGroup.eq_one_iff v
  · intro σ v
    exact (qTwoLMDivF_permH_mk m h3 σ v).symm

theorem qTwoLMDivF_isAugModel (m : ℕ) :
    IsAugModel m ↥(sumZero m 3) (permAutVHom m 3) :=
  ⟨MulEquiv.refl _, fun σ v => by
    show permAutV σ v = permAutVHom m 3 σ v
    rw [permAutVHom_apply]⟩

end CFSG.StandardType.QTwo

end
