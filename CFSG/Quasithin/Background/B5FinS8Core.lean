module

public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5FinWedge
public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.Quasithin.Background.B5FinPerm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.GH74.Exceptional CFSG.ComponentClassification.PresentationLocal
  CFSG.Quasithin.B5FinWedge CFSG.Assembly.LowTwoRank Matrix

namespace B5FinS8

private theorem exists_alphaHom : ∃ φ : alternatingGroup (Fin 8) →* GL (Fin 4) (ZMod 2),
    ∀ k, φ (carmichaelCycle k) = l42Gen k :=
  exists_hom_carmichaelCycle (by norm_num) l42Gen l42Gen_pow_three l42Gen_mul_sq

noncomputable def alphaHom : alternatingGroup (Fin 8) →* GL (Fin 4) (ZMod 2) :=
  exists_alphaHom.choose

theorem alphaHom_carmichaelCycle (k : CarmichaelIndex 8) :
    alphaHom (carmichaelCycle k) = l42Gen k :=
  exists_alphaHom.choose_spec k

theorem alphaHom_bijective : Function.Bijective alphaHom := by
  have hinj : Function.Injective alphaHom := by
    have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
      alternatingGroup.isSimpleGroup (by simp)
    rcases (MonoidHom.normal_ker alphaHom).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff alphaHom).mp h
    · exfalso
      let k₀ : CarmichaelIndex 8 := ⟨2, by decide⟩
      have hk : carmichaelCycle k₀ ∈ alphaHom.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, alphaHom_carmichaelCycle] at hk
      have : l42Mat 0 = 1 := by
        have := congrArg Units.val hk
        simpa [l42Gen, l42Unit, carmichaelIndexToFin6, k₀] using this
      exact absurd this (by decide)
  have hcard : Nat.card (alternatingGroup (Fin 8)) = Nat.card (GL (Fin 4) (ZMod 2)) := by
    rw [card_GL_four_two, nat_card_alternatingGroup, Nat.card_fin]
    decide
  exact Function.Injective.bijective_of_nat_card_le hinj hcard.ge

@[expose] noncomputable def slEquiv : ↥(StatedSL 4 (ZMod 2)) ≃* GL (Fin 4) (ZMod 2) :=
  (MulEquiv.subgroupCongr (statedSL_eq_top_of_card_two (K := ZMod 2) (by simp) 4)).trans
    Subgroup.topEquiv

theorem slEquiv_apply (g : ↥(StatedSL 4 (ZMod 2))) : slEquiv g = (g : GL (Fin 4) (ZMod 2)) := rfl

@[expose] noncomputable def alpha : alternatingGroup (Fin 8) →* ↥(StatedSL 4 (ZMod 2)) :=
  slEquiv.symm.toMonoidHom.comp alphaHom

theorem coe_alpha (σ : alternatingGroup (Fin 8)) :
    ((alpha σ : ↥(StatedSL 4 (ZMod 2))) : GL (Fin 4) (ZMod 2)) = alphaHom σ := by
  rw [← slEquiv_apply]
  exact slEquiv.apply_symm_apply _

theorem alpha_surjective : Function.Surjective alpha :=
  slEquiv.symm.surjective.comp alphaHom_bijective.2

@[expose] def qmat : Matrix (Fin 6) (Fin 8) (ZMod 2) :=
  !![1, 1, 1, 0, 1, 0, 0, 0;
    1, 1, 0, 1, 0, 1, 0, 0;
    1, 0, 0, 0, 1, 1, 1, 0;
    1, 0, 0, 1, 1, 0, 1, 0;
    1, 0, 1, 1, 0, 1, 0, 0;
    1, 1, 1, 0, 0, 0, 1, 0]

@[expose] def qform (x : Fin 8 → ZMod 2) : Fin 6 → ZMod 2 := qmat *ᵥ x

theorem qform_add (x y : Fin 8 → ZMod 2) : qform (x + y) = qform x + qform y :=
  Matrix.mulVec_add _ _ _

theorem qform_zero : qform 0 = 0 := Matrix.mulVec_zero _

theorem qform_eq_zero_iff : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 →
    (qform x = 0 ↔ (x = 0 ∨ x = fun _ => 1)) := by
  decide +kernel

theorem exists_qform_eq :
    ∀ y : Fin 6 → ZMod 2, ∃ x : Fin 8 → ZMod 2, ∑ i, x i = 0 ∧ qform x = y := by
  decide +kernel

theorem qform_gen : ∀ k : CarmichaelIndex 8, ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 →
    qform (fun i => x ((carmichaelPerm k)⁻¹ i)) =
      wedgeMat4 (l42Mat (carmichaelIndexToFin6 k)) *ᵥ qform x := by
  decide +kernel

abbrev LamAmb : Type := Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2))

@[expose] noncomputable def qAdd : (Fin 8 → ZMod 2) →+ ⋀[ZMod 2]^2 (Fin 4 → ZMod 2) :=
  (wedgeEquiv4 (ZMod 2)).symm.toLinearMap.toAddMonoidHom.comp
    (Matrix.mulVecLin qmat).toAddMonoidHom

@[expose] noncomputable def qHom : G6.PermMod 8 →* LamAmb :=
  AddMonoidHom.toMultiplicative qAdd

theorem qHom_apply (x : G6.PermMod 8) :
    qHom x = Multiplicative.ofAdd ((wedgeEquiv4 (ZMod 2)).symm (qform (Multiplicative.toAdd x))) :=
  rfl

@[expose] noncomputable def ehat8 :
    ↥(G6.coreMod 8) →* ↥(FFModel.extSq (ZMod 2) 4).sec :=
  (qHom.comp (G6.coreMod 8).subtype).codRestrict (FFModel.extSq (ZMod 2) 4).sec fun _ => trivial

theorem coe_ehat8 (m : ↥(G6.coreMod 8)) : (ehat8 m).1 = qHom m.1 := rfl

theorem ehat8_surjective : Function.Surjective ehat8 := by
  rintro ⟨t, -⟩
  let t' : LamAmb := t
  obtain ⟨x, hx, hxq⟩ := exists_qform_eq ((wedgeEquiv4 (ZMod 2)) (Multiplicative.toAdd t'))
  refine ⟨⟨Multiplicative.ofAdd x, (G6.mem_coreMod).2 hx⟩, Subtype.ext ?_⟩
  change qHom (Multiplicative.ofAdd x) = t'
  rw [qHom_apply, toAdd_ofAdd, hxq, LinearEquiv.symm_apply_apply, ofAdd_toAdd]

theorem ehat8_ker : ∀ m : ↥(G6.coreMod 8),
    (ehat8 m).1 ∈ (FFModel.extSq (ZMod 2) 4).ker ↔ m.1 ∈ (FFModel.symDn 8).ker := by
  rintro ⟨m, hm⟩
  have hm' : ∑ i, Multiplicative.toAdd m i = 0 := (G6.mem_coreMod).1 hm
  change qHom m ∈ (⊥ : Subgroup LamAmb) ↔ m ∈ Subgroup.zpowers (G6.allOnes 8) ⊓ G6.coreMod 8
  rw [Subgroup.mem_bot, Subgroup.mem_inf, B5FinPerm.mem_zpowers_allOnes_iff]
  have h1 : qHom m = 1 ↔ qform (Multiplicative.toAdd m) = 0 := by
    constructor
    · intro h
      rw [qHom_apply] at h
      have h' := congrArg Multiplicative.toAdd h
      rw [toAdd_ofAdd, toAdd_one] at h'
      exact (LinearEquiv.map_eq_zero_iff _).1 h'
    · intro h
      rw [qHom_apply, h, map_zero, ofAdd_zero]
  rw [h1, qform_eq_zero_iff _ hm']
  constructor
  · rintro (h | h)
    · exact ⟨Or.inl (Multiplicative.toAdd.injective h), hm⟩
    · exact ⟨Or.inr (Multiplicative.toAdd.injective h), hm⟩
  · rintro ⟨h | h, -⟩
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr (by rw [h]; rfl)

@[expose] noncomputable def G8 :
    (FFModel.symDn 8).Mod ≃* (FFModel.extSq (ZMod 2) 4).Mod :=
  FFModel.modEquivOfSurj ehat8 ehat8_surjective ehat8_ker

theorem qHom_gen (k : CarmichaelIndex 8) (x : G6.PermMod 8) (hx : x ∈ G6.coreMod 8) :
    qHom (G6.permAct 8 (carmichaelPerm k) x) =
      extSqAct (ZMod 2) 4 (alpha (carmichaelCycle k)) (qHom x) := by
  have hm : ∑ i, Multiplicative.toAdd x i = 0 := (G6.mem_coreMod).1 hx
  apply Multiplicative.toAdd.injective
  apply (wedgeEquiv4 (ZMod 2)).injective
  change wedgeCoord4 ((wedgeEquiv4 (ZMod 2)).symm (qform (fun i =>
      Multiplicative.toAdd x ((carmichaelPerm k)⁻¹ i)))) =
    wedgeCoord4 (exteriorPower.map 2 (Matrix.toLin' (((alpha (carmichaelCycle k) :
      ↥(StatedSL 4 (ZMod 2))) : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)))
      ((wedgeEquiv4 (ZMod 2)).symm (qform (Multiplicative.toAdd x))))
  rw [wedgeCoord4_map, ← wedgeEquiv4_apply, ← wedgeEquiv4_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, coe_alpha, alphaHom_carmichaelCycle]
  exact qform_gen k _ hm

theorem qHom_alt (σ : alternatingGroup (Fin 8)) (x : G6.PermMod 8) (hx : x ∈ G6.coreMod 8) :
    qHom (G6.permAct 8 (σ : Equiv.Perm (Fin 8)) x) = extSqAct (ZMod 2) 4 (alpha σ) (qHom x) := by
  let S : Subgroup (alternatingGroup (Fin 8)) :=
    { carrier := {σ | ∀ x : G6.PermMod 8, x ∈ G6.coreMod 8 →
        qHom (G6.permAct 8 (σ : Equiv.Perm (Fin 8)) x) = extSqAct (ZMod 2) 4 (alpha σ) (qHom x)}
      one_mem' := by
        intro x _
        rw [OneMemClass.coe_one, permAct_one_act, map_one, extSqAct_one]
      mul_mem' := by
        intro σ τ hσ hτ x hx
        rw [Subgroup.coe_mul, permAct_mul_act, hσ _ (G6.permAct_mem_coreMod _ hx), hτ _ hx,
          map_mul, extSqAct_mul_act]
      inv_mem' := by
        intro σ hσ x hx
        have hx' : G6.permAct 8 (((σ⁻¹ : alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) x ∈
            G6.coreMod 8 := G6.permAct_mem_coreMod _ hx
        have h0 := hσ _ hx'
        have h1 : G6.permAct 8 (σ : Equiv.Perm (Fin 8))
            (G6.permAct 8 (((σ⁻¹ : alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) x) = x := by
          rw [← permAct_mul_act, Subgroup.coe_inv, mul_inv_cancel, permAct_one_act]
        rw [h1] at h0
        have h2 := congrArg (extSqAct (ZMod 2) 4 (alpha σ⁻¹)) h0
        rw [← extSqAct_mul_act, ← map_mul, inv_mul_cancel, map_one, extSqAct_one] at h2
        exact h2.symm }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← closure_range_carmichaelCycle (by norm_num : 3 ≤ 8), Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩ x hx
    exact qHom_gen k x hx
  have : σ ∈ S := hS ▸ Subgroup.mem_top σ
  exact this x hx

theorem G8_modAct (σ : alternatingGroup (Fin 8)) (q : (FFModel.symDn 8).Mod) :
    G8 ((FFModel.symDn_isActionModel 8).modAct (σ : Equiv.Perm (Fin 8)) q) =
      (FFModel.extSq_isActionModel (ZMod 2) 4).modAct (alpha σ) (G8 q) := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  change QuotientGroup.mk (ehat8 ((FFModel.symDn_isActionModel 8).actSec (σ : Equiv.Perm (Fin 8)) m)) =
    QuotientGroup.mk ((FFModel.extSq_isActionModel (ZMod 2) 4).actSec (alpha σ) (ehat8 m))
  congr 1
  exact Subtype.ext (qHom_alt σ m.1 m.2)

end B5FinS8

end CFSG.Quasithin
