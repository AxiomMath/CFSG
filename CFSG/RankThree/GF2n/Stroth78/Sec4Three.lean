module

public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeAct
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeStepA
public import CFSG.GroupTheory.ThreeTranspositions.StarRigidity
public import CFSG.Fischer.Classification.FischerTypeLocal

import CFSG.RankThree.GF2n.Stroth78.Sec4Bound
import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeNotSymp
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.GroupTheory.ThreeTranspositions.FischerResidualCentralizer
import CFSG.Fischer.Classification.Orthogonal3.LocalData

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

local instance instNormalXsubThree (S : Setting z E F) (a : G) : (Xsub S a).Normal :=
  Xsub_normal S a

@[expose] noncomputable def alphaBar (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    ↥(threeResidualQuot (alphaInX S h hα)) :=
  ⟨QuotientGroup.mk (alphaInX S h hα), mk_mem_threeResidualQuot_self _⟩

@[simp] theorem coe_alphaBar (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    ((alphaBar S h hα : ↥(threeResidualQuot (alphaInX S h hα))) :
        ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) = QuotientGroup.mk (alphaInX S h hα) :=
  rfl

theorem alphaBar_mem (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    alphaBar S h hα ∈ threeResidualClass (alphaInX S h hα) := by
  rw [threeResidualClass, Set.mem_preimage]
  exact ⟨1, Subgroup.one_mem _, by simp [alphaBar]⟩

theorem hyp_Wbar (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1) :
    CFSG.Fischer.Classification.Hyp ↥(threeResidualQuot (alphaInX S h hα))
      (threeResidualClass (alphaInX S h hα)) := by
  have hαT : α ∈ Tset S a := h.mem_Tset_of_mem_Rbar hα hα1
  have hd : alphaInX S h hα =
      (⟨α, subset_Xsub S a (Tset_subset_Eset S a hαT)⟩ : ↥(Xsub S a)) := Subtype.ext rfl
  rw [hd]
  exact hyp_stroth78_36 S h h217 h3 hαT

theorem residualSelf_alphaInX_sq (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    (residualSelf (alphaInX S h hα)) ^ 2 = 1 := by
  have hsq : ((alphaInX S h hα : ↥(Xsub S a)) : Hbar z) ^ 2 = 1 :=
    sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Rbar_le_Lbar S a hα)
  apply Subtype.ext
  show ((alphaInX S h hα : ↥(Xsub S a))) ^ 2 = 1
  exact Subtype.ext (by simpa using hsq)

theorem localPerfectResidual_le_map_J0W (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    localPerfectResidual (threeResidualClass (alphaInX S h hα)) (alphaBar S h hα) ≤
      (J0W (alphaInX S h hα)).map (residualProj (alphaInX S h hα)) := by
  refine (localPerfectResidual_le_centralizer).trans (le_of_eq ?_)
  exact (map_perfectResidual_centralizer_eq_of_odd_ker (residualProj (alphaInX S h hα))
    (residualProj_surjective _) (residualProj_ker_le_center _)
    (odd_card_ker_residualProj _ (odd_card_center_Xsub S a))
    (residualSelf_alphaInX_sq S h hα)).symm

theorem Lbar_le_centralizer_alphaInX (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) :
    Lbar S a ≤ Subgroup.centralizer ({(alphaInX S h hα : Hbar z)} : Set (Hbar z)) :=
  Lbar_le_centralizer S h hα

theorem actL_eq_residualConj (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) (ℓ : ↥(Lbar S a)) :
    actL S h hα ℓ = residualConj (alphaInX S h hα)
      (Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα) ℓ) := by
  ext x
  rcases x with ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
  rw [actL_apply S h hα ℓ n hy,
    residualConj_apply_mk (d := alphaInX S h hα)
      (Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα) ℓ) n hy]
  rfl

theorem exists_actL_conj_of_ker (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    (hker : derivedSeries ↥(threeResidualJoin (alphaInX S h hα)) 2 ≤
      (rhoW S a (alphaInX S h hα)).ker)
    {j : ↥(threeResidualJoin (alphaInX S h hα))} (hj : j ∈ J0W (alphaInX S h hα))
    (ℓ : ↥(Lbar S a)) :
    ∃ ℓ' : ↥(Lbar S a),
      MulAut.conj (residualProj (alphaInX S h hα) j) * actL S h hα ℓ *
          (MulAut.conj (residualProj (alphaInX S h hα) j))⁻¹ = actL S h hα ℓ' := by
  have hjJ0 : ((j : ↥(Xsub S a)) : Hbar z) ∈ J0 S a (alphaInX S h hα) :=
    Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
  have hcommH : ((j : ↥(Xsub S a)) : Hbar z) * (alphaInX S h hα : Hbar z) =
      (alphaInX S h hα : Hbar z) * ((j : ↥(Xsub S a)) : Hbar z) :=
    commute_of_mem_J0 S a (alphaInX S h hα) hjJ0
  have hnorm := J0_le_normalizer_Lbar_of_ker S h (alphaInX S h hα) hα hα1 hker hjJ0
  have hℓ'mem : ((j : ↥(Xsub S a)) : Hbar z) * (ℓ : Hbar z) *
      (((j : ↥(Xsub S a)) : Hbar z))⁻¹ ∈ Lbar S a :=
    (Subgroup.mem_normalizer_iff.mp hnorm (ℓ : Hbar z)).mp ℓ.2
  let ℓ' : ↥(Lbar S a) :=
    ⟨((j : ↥(Xsub S a)) : Hbar z) * (ℓ : Hbar z) *
      (((j : ↥(Xsub S a)) : Hbar z))⁻¹, hℓ'mem⟩
  let cJ : ↥(Subgroup.centralizer ({(alphaInX S h hα : Hbar z)} : Set (Hbar z))) :=
    ⟨((j : ↥(Xsub S a)) : Hbar z), Subgroup.mem_centralizer_singleton_iff.mpr hcommH⟩
  have hconjJ : residualConj (alphaInX S h hα) cJ =
      MulAut.conj (residualProj (alphaInX S h hα) j) := by
    rw [residualConj_eq_conj (G := Hbar z) (X := Xsub S a) (d := alphaInX S h hα)
      cJ (j : ↥(Xsub S a)).2 j.2]
    have hval : (⟨QuotientGroup.mk ⟨(cJ : Hbar z), (j : ↥(Xsub S a)).2⟩,
        mk_mem_threeResidualQuot_of_mem (j.2)⟩ :
          ↥(threeResidualQuot (alphaInX S h hα))) =
        residualProj (alphaInX S h hα) j := by
      apply Subtype.ext
      rw [residualProj_apply]
    rw [hval]
  have hincl : Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα) ℓ' =
      cJ * Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα) ℓ * cJ⁻¹ := by
    apply Subtype.ext
    rfl
  refine ⟨ℓ', ?_⟩
  calc MulAut.conj (residualProj (alphaInX S h hα) j) * actL S h hα ℓ *
        (MulAut.conj (residualProj (alphaInX S h hα) j))⁻¹
      = residualConj (alphaInX S h hα) cJ *
          residualConj (alphaInX S h hα)
            (Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα) ℓ) *
          (residualConj (alphaInX S h hα) cJ)⁻¹ := by
          rw [← hconjJ, actL_eq_residualConj S h hα ℓ]
    _ = residualConj (alphaInX S h hα)
          (cJ * Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα) ℓ * cJ⁻¹) := by
          rw [map_mul, map_mul, map_inv]
    _ = residualConj (alphaInX S h hα)
          (Subgroup.inclusion (Lbar_le_centralizer_alphaInX S h hα) ℓ') := by rw [hincl]
    _ = actL S h hα ℓ' := (actL_eq_residualConj S h hα ℓ').symm

theorem false_of_stroth78_43_data_of_ker (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    (hker : derivedSeries ↥(threeResidualJoin (alphaInX S h hα)) 2 ≤
      (rhoW S a (alphaInX S h hα)).ker)
    (hT : CFSG.Fischer.Classification.TripleProperty
      (threeResidualClass (alphaInX S h hα)))
    (hna : CFSG.Fischer.Classification.NonabelianCommutator
      ↥(threeResidualQuot (alphaInX S h hα)))
    (hloc : ∀ e ∈ threeResidualClass (alphaInX S h hα),
      IsSimpleGroup (commutator (LocalQuotient (threeResidualClass (alphaInX S h hα)) e)) ∧
        ∃ x y : commutator (LocalQuotient (threeResidualClass (alphaInX S h hα)) e),
          x * y ≠ y * x) : False := by
  have hH : CFSG.Fischer.Classification.Hyp ↥(threeResidualQuot (alphaInX S h hα))
      (threeResidualClass (alphaInX S h hα)) := hyp_Wbar S h h217 h3 hα hα1
  obtain ⟨hLS, hLna⟩ := hloc (alphaBar S h hα) (alphaBar_mem S h hα)
  have hA2 : Nat.card (actL S h hα).range ≤ 2 :=
    card_le_two_of_isPGroup_normalized (F := threeResidualClass (alphaInX S h hα))
      (d := alphaBar S h hα)
      (M := localPerfectResidual (threeResidualClass (alphaInX S h hα)) (alphaBar S h hα))
      hH hna hT (alphaBar_mem S h hα) hLS hLna
      (localPerfectResidual_le_localGroup _ _)
      (fun c hc => centralizer_normalizes_localPerfectResidual hH hc)
      (commutator_le_map_localPerfectResidual hLS hLna)
      (isPGroup_range_actL S h hα)
      (fun β hβ e he => by
        obtain ⟨ℓ, rfl⟩ := MonoidHom.mem_range.mp hβ
        exact actL_mem_threeResidualClass S h hα ℓ he)
      (fun β hβ => by
        obtain ⟨ℓ, rfl⟩ := MonoidHom.mem_range.mp hβ
        exact actL_fix S h hα ℓ)
      (fun m hm β hβ => by
        have hm' : m ∈ (J0W (alphaInX S h hα)).map (residualProj (alphaInX S h hα)) :=
          localPerfectResidual_le_map_J0W S h hα hm
        obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hm'
        obtain ⟨ℓ, rfl⟩ := MonoidHom.mem_range.mp hβ
        obtain ⟨ℓ', hℓ'⟩ := exists_actL_conj_of_ker S h hα hα1 hker hj ℓ
        exact MonoidHom.mem_range.mpr ⟨ℓ', hℓ'.symm⟩)
  have h2 : Nat.card (Lbar S a) ≤ 2 * Nat.card (actL S h hα).range :=
    card_Lbar_le_two_mul_card_range_actL S h h217 h3 hα hα1
  have h4 : Nat.card (Lbar S a) ≤ 4 := by
    have := Nat.mul_le_mul_left 2 hA2
    omega
  exact false_of_card_Lbar_le_four S h h4

theorem false_of_stroth78_43_data (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1)
    (hnot : ¬ CFSG.Fischer.Classification.IsSymplecticType
      (threeResidualClass (alphaInX S h hα)))
    (hT : CFSG.Fischer.Classification.TripleProperty
      (threeResidualClass (alphaInX S h hα)))
    (hna : CFSG.Fischer.Classification.NonabelianCommutator
      ↥(threeResidualQuot (alphaInX S h hα)))
    (hloc : ∀ e ∈ threeResidualClass (alphaInX S h hα),
      IsSimpleGroup (commutator (LocalQuotient (threeResidualClass (alphaInX S h hα)) e)) ∧
        ∃ x y : commutator (LocalQuotient (threeResidualClass (alphaInX S h hα)) e),
          x * y ≠ y * x) : False :=
  false_of_stroth78_43_data_of_ker S h h217 h3 hα hα1
    (derivedSeries_two_le_ker_rhoW S h h217 h3 hα hα1 hnot) hT hna hloc

section Certificates

theorem stroth78_43_hasType (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1) (k : Fin 3) :
    ¬ HasType k ↥(threeResidualQuot (alphaInX S h hα))
      (threeResidualClass (alphaInX S h hα)) := by
  intro hk
  have hH : CFSG.Fischer.Classification.Hyp ↥(threeResidualQuot (alphaInX S h hα))
      (threeResidualClass (alphaInX S h hα)) := hyp_Wbar S h h217 h3 hα hα1
  exact false_of_stroth78_43_data S h h217 h3 hα hα1
    (hasType_not_isSymplecticType hk) (hasType_tripleProperty hH hk)
    (hasType_nonabelianCommutator hH hk) (hasType_localQuotient_simple hH hk)

end Certificates

theorem stroth78_43_orthogonal (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Rbar S a) (hα1 : α ≠ 1) {m : ℕ} (hm : 6 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0) :
    ¬ CFSG.Open.fischerCentralQuotientModel
      (threeResidualClass (alphaInX S h hα))
      (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => f x y)
        fun v => f v v = 1))
      (CFSG.Open.fischerTransvections (fun x y => f x y) fun v => f v v = 1) := by
  intro hmod
  have hH : CFSG.Fischer.Classification.Hyp ↥(threeResidualQuot (alphaInX S h hα))
      (threeResidualClass (alphaInX S h hα)) := hyp_Wbar S h h217 h3 hα hα1
  exact false_of_stroth78_43_data S h h217 h3 hα hα1
    (reflection_not_isSymplecticType hm hsymm hnd hmod)
    (reflection_tripleProperty hm hsymm hnd hmod)
    (reflection_nonabelianCommutator hH hm hsymm hnd hmod)
    (reflection_localQuotient_simple hH hm hsymm hnd hmod)

end CFSG.RankThree.GF2n.Stroth78
