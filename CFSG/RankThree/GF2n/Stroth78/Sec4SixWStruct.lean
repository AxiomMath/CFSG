module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualDirect
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualTop
public import CFSG.RankThree.GF2n.Stroth78.Sec4SixW
public import CFSG.RankThree.GF2n.Tim79a34GriessSpS6

import CFSG.RankThree.GF2n.Stroth78.Sec4Six
import CFSG.RankThree.GF2n.Tim78a.GriessSpMultiplier
import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSpAut
import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaLocal
import CFSG.Fischer.Classification.Orthogonal2.SpModel
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.Open.StatedZModTwo
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification Matrix

namespace Sec4SixW

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem allInner_of_mulEquiv_statedSp_zmod {Y : Type} [Group Y] {m : ℕ} (hm : 3 ≤ m)
    (e : Y ≃* StatedSp m (ZMod 2)) : ∀ φ : MulAut Y, ∃ g : Y, φ = MulAut.conj g := by
  have hsub : (StatedScalars (Fin m ⊕ Fin m) (ZMod 2)).subgroupOf (StatedSp m (ZMod 2)) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two (Nat.card_zmod 2),
      Subgroup.bot_subgroupOf]
  let eP : StatedProj (StatedSp m (ZMod 2)) ≃* StatedSp m (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot
  exact CFSG.SeitzReduction.SporadicRefine.allInner_of_mulEquiv e
    (CFSG.SeitzReduction.SporadicRefine.allInner_of_mulEquiv eP.symm
      (CFSG.SeitzReduction.SporadicRefine.allInner_statedProjSp_of_card_two hm
        (Nat.card_zmod 2)))

noncomputable def statedSpRingEquiv {K L : Type} [Field K] [Field L] (φ : K ≃+* L) (n : ℕ) :
    StatedSp n K ≃* StatedSp n L :=
  ((MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic).trans
    (MonoidHom.toMulEquiv (TauCeti.GLSymplectic.map (Fin n) (φ : K →+* L))
      (TauCeti.GLSymplectic.map (Fin n) (φ.symm : L →+* K))
      (by
        rw [← TauCeti.GLSymplectic.map_comp, show ((φ.symm : L →+* K).comp (φ : K →+* L)) =
          RingHom.id K from RingHom.ext fun x => φ.symm_apply_apply x,
          TauCeti.GLSymplectic.map_id])
      (by
        rw [← TauCeti.GLSymplectic.map_comp, show ((φ : K →+* L).comp (φ.symm : L →+* K)) =
          RingHom.id L from RingHom.ext fun x => φ.apply_symm_apply x,
          TauCeti.GLSymplectic.map_id]))).trans
    (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

theorem threeResidualQuot_eq_top_of_sp (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hd : (d : Hbar z) ∈ Eset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel (threeResidualClass d)
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    threeResidualQuot d = ⊤ := by
  obtain ⟨Φ, -⟩ := Orth2.exists_mulEquiv_isometryGroup_of_fischerLinearModel halt hsp
  have hb : b.IsAlt := halt
  have hbn := Orth2.nondegenerate_of_isAlt halt hnd
  have : IsSimpleGroup (TauCeti.BilinForm.isometryGroup b) :=
    Recognition.SymO.isSimpleGroup_isometryGroup b hb hbn (Module.finrank_fin_fun _) hm
  have : IsSimpleGroup ↥(threeResidualQuot d) := Φ.isSimpleGroup
  exact threeResidualQuot_eq_top_of_isSimpleGroup (pair_Xsub S h h217 h3) (twoCore_Xsub S)
    (threeCore_Xsub S h h217) (d := d) hd inferInstance

@[expose] noncomputable def quotCenterEquiv {X : Type} [Group X]
    {W : Subgroup (X ⧸ Subgroup.center X)} (hW : W = ⊤) : (X ⧸ Subgroup.center X) ≃* W :=
  ((MulEquiv.subgroupCongr hW).trans Subgroup.topEquiv).symm

theorem coe_quotCenterEquiv {X : Type} [Group X] {W : Subgroup (X ⧸ Subgroup.center X)}
    (hW : W = ⊤) (y : X ⧸ Subgroup.center X) :
    ((quotCenterEquiv hW y : W) : X ⧸ Subgroup.center X) = y :=
  rfl

theorem commutator_Xsub_eq_top (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hd : (d : Hbar z) ∈ Eset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel (threeResidualClass d)
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    commutator ↥(Xsub S a) = ⊤ := by
  have hW := threeResidualQuot_eq_top_of_sp S h h217 h3 hd hm halt hnd hsp
  obtain ⟨Φ, -⟩ := Orth2.exists_mulEquiv_isometryGroup_of_fischerLinearModel halt hsp
  have hperf := Orth2.commutator_eq_top_of_mulEquiv_isometryGroup hm halt hnd
    ((quotCenterEquiv hW).trans Φ)
  exact CFSG.RankThree.GF2n.Stroth80.commutator_eq_top_of_closure_sq_eq_one
    (Group.isPerfect_def.2 hperf) (odd_card_center_Xsub S a) (closure_involutions_Xsub S a)
    fun _ hs => hs

theorem exists_hom_statedSp_galois (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hd : (d : Hbar z) ∈ Eset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel (threeResidualClass d)
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    ∃ φ : ↥(Xsub S a) →* StatedSp m (GaloisField 2 1), Function.Surjective φ ∧
      φ.ker = Subgroup.center ↥(Xsub S a) := by
  have hW := threeResidualQuot_eq_top_of_sp S h h217 h3 hd hm halt hnd hsp
  obtain ⟨e⟩ := Sec4Six.exists_mulEquiv_statedSp_of_fischerLinearModel halt hnd hsp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eZ : ZMod 2 ≃+* GaloisField 2 1 := (GaloisField.equivZmodP 2).toRingEquiv.symm
  let eT : (↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) ≃* StatedSp m (GaloisField 2 1) :=
    ((quotCenterEquiv hW).trans e).trans (statedSpRingEquiv eZ m)
  refine ⟨eT.toMonoidHom.comp (QuotientGroup.mk' _),
    eT.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem center_Xsub_eq_bot_of_four_le (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hd : (d : Hbar z) ∈ Eset S a) {m : ℕ} (hm : 4 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel (threeResidualClass d)
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    Subgroup.center ↥(Xsub S a) = ⊥ := by
  obtain ⟨φ, hφ, hker⟩ := exists_hom_statedSp_galois S h h217 h3 hd (by omega) halt hnd hsp
  have hcom := commutator_Xsub_eq_top S h h217 h3 hd (by omega) halt hnd hsp
  rw [← hker]
  refine griessSpMultiplierStatement_holds m 1 (by omega) le_rfl ?_ ?_ ?_ ?_ _ φ hφ
    hker.le (by rw [hcom]; exact le_top)
  all_goals
    intro hmf
    rw [Prod.mk.injEq] at hmf
    omega

theorem center_Xsub_eq_bot
    (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hd : (d : Hbar z) ∈ Eset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel (threeResidualClass d)
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) :
    Subgroup.center ↥(Xsub S a) = ⊥ := by
  rcases Nat.lt_or_ge m 4 with hlt | hge
  · obtain rfl : m = 3 := by omega
    obtain ⟨φ, hφ, hker⟩ := exists_hom_statedSp_galois S h h217 h3 hd hm halt hnd hsp
    have hcom := commutator_Xsub_eq_top S h h217 h3 hd hm halt hnd hsp
    have h2 : Nat.card φ.ker ≤ 2 :=
      (griessSpMultiplierExceptionStatement_holds 3 1 (Or.inr (Or.inr rfl))).1 _ φ hφ
        hker.le (by rw [hcom]; exact le_top)
    rw [hker] at h2
    have hodd := odd_card_center_Xsub S a
    have h1 : Nat.card (Subgroup.center ↥(Xsub S a)) = 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact Subgroup.eq_bot_of_card_eq _ h1
  · exact center_Xsub_eq_bot_of_four_le S h h217 h3 hd hge halt hnd hsp

theorem nonempty_mulEquiv_Xsub_of_center_eq_bot (S : Setting z E F) {a : G}
    (hZ : Subgroup.center ↥(Xsub S a) = ⊥) {d : ↥(Xsub S a)} (hW : threeResidualQuot d = ⊤) :
    Nonempty (↥(Xsub S a) ≃* ↥(threeResidualQuot d)) :=
  ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    (quotCenterEquiv hW)⟩

theorem exists_mulEquiv_Hbar_prod (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hd : (d : Hbar z) ∈ Eset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel (threeResidualClass d)
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZ : Subgroup.center ↥(Xsub S a) = ⊥) :
    ∃ ψ : Hbar z ≃* ↥(Xsub S a) × Subgroup.centralizer (Xsub S a : Set (Hbar z)),
      ∀ p, ψ.symm p = (p.1 : Hbar z) * p.2 := by
  have hW := threeResidualQuot_eq_top_of_sp S h h217 h3 hd hm halt hnd hsp
  obtain ⟨eX⟩ := nonempty_mulEquiv_Xsub_of_center_eq_bot S hZ hW
  obtain ⟨e⟩ := Sec4Six.exists_mulEquiv_statedSp_of_fischerLinearModel halt hnd hsp
  exact exists_mulEquiv_prod_centralizer (Xsub S a) hZ
    (allInner_of_mulEquiv_statedSp_zmod hm (eX.trans e))

theorem commute_of_mem_derived_two (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZ : Subgroup.center ↥(Xsub S a) = ⊥) :
    ∀ x ∈ ⁅⁅H z, H z⁆, ⁅H z, H z⁆⁆, ∀ y ∈ ZQ z, Commute x y := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Hbar_prod S h h217 h3 (Tset_subset_Eset S a hα) hm halt hnd
    hsp hZ
  let C := Subgroup.centralizer (Xsub S a : Set (Hbar z))
  let q : ↥(H z) →* C := ((MonoidHom.snd _ _).comp ψ.toMonoidHom).comp
    (QuotientGroup.mk' ((Q z).subgroupOf (H z)))
  have hC2 : ⁅commutator C, commutator C⁆ = ⊥ :=
    CFSG.EvenSmallLie.UnitarySix.Yamada.commutator_commutator_eq_bot_of_card_dvd_six
      (card_centralizer_Xsub_dvd_six S h h217)
  let T : Subgroup ↥(H z) := ⊤
  have hq : ∀ x' ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)), q x' = 1 := by
    intro x' hx'
    have hmem : q x' ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)).map q :=
      Subgroup.mem_map_of_mem q hx'
    rw [Subgroup.map_commutator, Subgroup.map_commutator] at hmem
    have hle : ⁅⁅T.map q, T.map q⁆, ⁅T.map q, T.map q⁆⁆ ≤ ⁅commutator C, commutator C⁆ := by
      rw [commutator_def]
      exact Subgroup.commutator_mono (Subgroup.commutator_mono le_top le_top)
        (Subgroup.commutator_mono le_top le_top)
    rw [hC2] at hle
    exact Subgroup.mem_bot.mp (hle hmem)
  intro x hx y hy
  have hT : T.map (H z).subtype = H z := by
    rw [show T = ⊤ from rfl, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hx' : x ∈ (⁅⁅T, T⁆, ⁅T, T⁆⁆ : Subgroup ↥(H z)).map (H z).subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hT]
    exact hx
  obtain ⟨x', hx'm, rfl⟩ := hx'
  have hqx := hq x' hx'm
  have hX : (QuotientGroup.mk x' : Hbar z) ∈ Xsub S a := by
    have h1 := hψ (ψ (QuotientGroup.mk x'))
    rw [MulEquiv.symm_apply_apply] at h1
    have hu2 : (ψ (QuotientGroup.mk x')).2 = 1 := hqx
    rw [h1, hu2, OneMemClass.coe_one, mul_one]
    exact (ψ (QuotientGroup.mk x')).1.2
  exact commute_of_mem_Xsub S h h217 h3 hα hm halt hnd hsp x' hX hy

theorem nonempty_mulEquiv_prod_of_even (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hd : (d : Hbar z) ∈ Eset S a) {m : ℕ} (hm : 3 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hsp : fischerLinearModel (threeResidualClass d)
      (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
      (fischerTransvections (fun x y => b x y) fun v => v ≠ 0))
    (hZ : Subgroup.center ↥(Xsub S a) = ⊥)
    (heven : Even (Nat.card (Subgroup.centralizer (Xsub S a : Set (Hbar z))))) :
    Nonempty (Hbar z ≃* ↥(threeResidualQuot d) × Equiv.Perm (Fin 3)) := by
  obtain ⟨ψ, -⟩ := exists_mulEquiv_Hbar_prod S h h217 h3 hd hm halt hnd hsp hZ
  have hW := threeResidualQuot_eq_top_of_sp S h h217 h3 hd hm halt hnd hsp
  obtain ⟨eX⟩ := nonempty_mulEquiv_Xsub_of_center_eq_bot S hZ hW
  obtain ⟨eC⟩ := nonempty_mulEquiv_perm_three_centralizer_Xsub S h h217 heven
  exact ⟨ψ.trans (MulEquiv.prodCongr eX eC)⟩

end Sec4SixW

end CFSG.RankThree.GF2n.Stroth78
