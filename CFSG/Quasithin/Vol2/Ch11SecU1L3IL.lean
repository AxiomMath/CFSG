module

public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.Quasithin.EmptyFaithful.E22PTr
public import CFSG.Quasithin.Vol2.Ch11SecBNPAut
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2PGL

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open CFSG.GorensteinWalter
open CFSG.Quasithin.Vol2.Ch11.SecB (rangeConjEquiv centralizer_range_conj_eq_bot
  normal_range_conj conj_injective)
open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 (pslRange)
open scoped MatrixGroups commutatorElement

section Action

@[expose] noncomputable def autQuotCenter (Y : Type) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ Subgroup.center Y) where
  toFun σ := QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) σ
    (Subgroup.map_center_eq σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

variable {H : Type} [Group H] (Y : Subgroup H) [Y.Normal]

@[expose] noncomputable def conjQuotCenter : H →* MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
  (autQuotCenter ↥Y).comp MulAut.conjNormal

theorem conjQuotCenter_apply_mk (h : H) (y : ↥Y) :
    conjQuotCenter Y h (y : ↥Y ⧸ Subgroup.center ↥Y) =
      ((MulAut.conjNormal h y : ↥Y) : ↥Y ⧸ Subgroup.center ↥Y) := rfl

theorem conjQuotCenter_coe (y : ↥Y) :
    conjQuotCenter Y (y : H) = MulAut.conj (y : ↥Y ⧸ Subgroup.center ↥Y) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotCenter_apply_mk, MulAut.conjNormal_val, MulAut.conj_apply, MulAut.conj_apply]
    rfl

theorem mem_centralizer_of_mem_ker (hY : commutator ↥Y = ⊤) {h : H}
    (hh : h ∈ (conjQuotCenter Y).ker) : h ∈ Subgroup.centralizer (Y : Set H) := by
  have hc : ∀ y : ↥Y, ∃ c ∈ Subgroup.center ↥Y, MulAut.conjNormal h y = y * c := by
    intro y
    have h1 := congrArg (fun σ : MulAut (↥Y ⧸ Subgroup.center ↥Y) =>
      σ (y : ↥Y ⧸ Subgroup.center ↥Y)) (MonoidHom.mem_ker.mp hh)
    simp only [conjQuotCenter_apply_mk, MulAut.one_apply] at h1
    have h2 := QuotientGroup.eq.mp h1
    refine ⟨y⁻¹ * MulAut.conjNormal h y, ?_, by group⟩
    have h3 := Subgroup.inv_mem _ h2
    simpa using h3
  set S : Subgroup ↥Y := (Subgroup.centralizer ({h} : Set H)).comap Y.subtype with hS
  have hcomm : ∀ a b : ↥Y, ⁅a, b⁆ ∈ S := by
    intro a b
    obtain ⟨ca, hca, ha⟩ := hc a
    obtain ⟨cb, hcb, hb⟩ := hc b
    have key : MulAut.conjNormal h ⁅a, b⁆ = ⁅a, b⁆ := by
      rw [map_commutatorElement, ha, hb]
      have hca' := Subgroup.mem_center_iff.mp hca
      have hcb' := Subgroup.mem_center_iff.mp hcb
      simp only [commutatorElement_def]
      calc a * ca * (b * cb) * (a * ca)⁻¹ * (b * cb)⁻¹
          = a * (ca * (b * cb)) * (ca⁻¹ * a⁻¹) * (cb⁻¹ * b⁻¹) := by group
        _ = a * (b * cb * ca) * (ca⁻¹ * a⁻¹) * (cb⁻¹ * b⁻¹) := by rw [hca' (b * cb)]
        _ = a * b * (cb * a⁻¹ * cb⁻¹) * b⁻¹ := by group
        _ = a * b * (a⁻¹ * cb * cb⁻¹) * b⁻¹ := by
            rw [show cb * a⁻¹ = a⁻¹ * cb from (hcb' a⁻¹).symm]
        _ = a * b * a⁻¹ * b⁻¹ := by group
    have key' := congrArg Subtype.val key
    rw [MulAut.conjNormal_apply] at key'
    show ((⁅a, b⁆ : ↥Y) : H) ∈ Subgroup.centralizer ({h} : Set H)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ((⁅a, b⁆ : ↥Y) : H) * h = (h * (⁅a, b⁆ : ↥Y) * h⁻¹) * h := by rw [key']
      _ = h * (⁅a, b⁆ : ↥Y) := by group
  have hall : S = ⊤ := by
    rw [eq_top_iff, ← hY, commutator_def, Subgroup.commutator_le]
    exact fun a _ b _ => hcomm a b
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyS : (⟨y, hy⟩ : ↥Y) ∈ S := hall ▸ Subgroup.mem_top _
  exact (Subgroup.mem_centralizer_singleton_iff.mp hyS)

end Action

section Embed

variable {F : Type} [Field F] [Finite F]

@[expose] noncomputable def quotCenterEquiv {Y : Type} [Group Y] (e : Y ≃* SL(2, F)) :
    Y ⧸ Subgroup.center Y ≃* PSL2 F :=
  QuotientGroup.congr (Subgroup.center Y) (Subgroup.center SL(2, F)) e
    (Subgroup.map_center_eq e)

@[expose] noncomputable def pGammaL2EquivPGL2 (F : Type) [Field F] [Subsingleton (F ≃+* F)] :
    PGammaL2 F ≃* PGL2 F :=
  Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr
    (E22L2.e22ptr_pGammaL2PGLRange_eq_top F).symm).trans (pGammaL2PGLRangeEquiv F).symm)

omit [Finite F] in
theorem pGammaL2EquivPGL2_inl [Subsingleton (F ≃+* F)] (g : PGL2 F) :
    pGammaL2EquivPGL2 F (SemidirectProduct.inl g) = g := by
  apply (pGammaL2PGLRangeEquiv F).injective
  apply Subtype.ext
  simp [pGammaL2EquivPGL2]

omit [Finite F] in
theorem mem_pslRange_iff_pGammaL2 [Subsingleton (F ≃+* F)] (x : PGammaL2 F) :
    pGammaL2EquivPGL2 F x ∈ pslRange F ↔ x ∈ pGammaL2PSLRange F := by
  constructor
  · rintro ⟨s, hs⟩
    refine (mem_pGammaL2PSLRange_iff F x).mpr ⟨s, ?_⟩
    apply (pGammaL2EquivPGL2 F).injective
    rw [pGammaL2EquivPGL2_inl, hs]
  · intro hx
    obtain ⟨s, rfl⟩ := (mem_pGammaL2PSLRange_iff F x).mp hx
    rw [pGammaL2EquivPGL2_inl]
    exact ⟨s, rfl⟩

variable {H : Type} [Group H]

theorem exists_hom_pgl2_of_normal_sl2 [Subsingleton (F ≃+* F)]
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F) (Y : Subgroup H) [Y.Normal]
    (e : ↥Y ≃* SL(2, F)) :
    ∃ φ : H →* PGL2 F, φ.ker ≤ Subgroup.centralizer (Y : Set H) ∧ Y.map φ = pslRange F ∧
      ∀ h : H, φ h ∈ pslRange F → ∃ y ∈ Y, y⁻¹ * h ∈ Subgroup.centralizer (Y : Set H) := by
  set Q := ↥Y ⧸ Subgroup.center ↥Y
  have hZ : Subgroup.center Q = ⊥ := by
    have h := Subgroup.map_center_eq (quotCenterEquiv e)
    rw [psl2_center_eq_bot] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (quotCenterEquiv e).injective).mp h
  set N := (MulAut.conj : Q →* MulAut Q).range with hN
  have : N.Normal := normal_range_conj Q
  let eN : N ≃* PSL2 F := (rangeConjEquiv hZ).symm.trans (quotCenterEquiv e)
  obtain ⟨ι, hι, hPSL, hcore⟩ := CFSG.ABGDGroups.exists_embedding_of_normal_psl2 hF hcard eN
    (centralizer_range_conj_eq_bot hZ)
  have hperf : commutator ↥Y = ⊤ := by
    have h4 : 4 ≤ Nat.card F := by omega
    have hSL := (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4)
    have h1 := Subgroup.map_commutator (⊤ : Subgroup SL(2, F)) ⊤ e.symm.toMonoidHom
    rw [Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
    rw [commutator_def, ← h1, ← commutator_def, hSL.commutator_eq_top,
      Subgroup.map_top_of_surjective _ e.symm.surjective]
  refine ⟨(pGammaL2EquivPGL2 F).toMonoidHom.comp (ι.comp (conjQuotCenter Y)), ?_, ?_, ?_⟩
  · intro h hh
    apply mem_centralizer_of_mem_ker Y hperf
    rw [MonoidHom.mem_ker] at hh ⊢
    apply hι
    apply (pGammaL2EquivPGL2 F).injective
    rw [map_one, map_one]
    exact hh
  ·
    have hN' : ∀ σ : MulAut Q, σ ∈ N ↔ ι σ ∈ pGammaL2PSLRange F := fun σ => by
      rw [← hcore]
      rfl
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mem_pslRange_iff_pGammaL2,
        MonoidHom.comp_apply, ← hN']
      have h1 := conjQuotCenter_coe Y ⟨y, hy⟩
      simp only at h1
      rw [h1]
      exact ⟨_, rfl⟩
    · intro w hw
      set x := (pGammaL2EquivPGL2 F).symm w with hx
      have hxw : pGammaL2EquivPGL2 F x = w := by rw [hx, MulEquiv.apply_symm_apply]
      have hxP : x ∈ pGammaL2PSLRange F := (mem_pslRange_iff_pGammaL2 x).mp (hxw ▸ hw)
      obtain ⟨σ, hσ⟩ := hPSL hxP
      obtain ⟨q, hq⟩ := (hN' σ).mpr (hσ ▸ hxP)
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨y, y.2, ?_⟩
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, conjQuotCenter_coe Y y, hq, hσ,
        MulEquiv.coe_toMonoidHom, hxw]
  ·
    intro h hh
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mem_pslRange_iff_pGammaL2,
      MonoidHom.comp_apply] at hh
    have hmem : conjQuotCenter Y h ∈ N := by
      rw [← hcore]
      exact hh
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨y, y.2, mem_centralizer_of_mem_ker Y hperf ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, conjQuotCenter_coe Y y, hq, inv_mul_cancel]

end Embed

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
