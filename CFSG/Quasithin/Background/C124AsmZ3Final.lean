module

public import CFSG.Quasithin.Background.C124AsmFinal
public import CFSG.Quasithin.Background.C124AsmZ3Setup
public import CFSG.Quasithin.Background.C124AsmZ3Lift

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV) {Γ : Type} [Group Γ]
  {Ys : Subgroup (MulAut (IntMod V hV))}

include E

theorem exists_yData_of_xBar (B : XBar X V hV E.hXN Γ) (h : StarZ3 X V L R hV Ys) (hm : 5 ≤ m)
    (e : ↥(autI hV L) ≃* ↥(alternatingGroup (Fin m))) :
    ∃ Y : Subgroup G, YData X V L R hV Y := by
  obtain ⟨A, hA1, hA2, hA3, hA4, hnc⟩ := E.exists_A B h hm e
  obtain ⟨Y, hYL, hres, hQY, hSY, hidx, hYs⟩ := E.exists_Y B hA1 hA2 hA3 hA4
  have hYX : Y ≤ X := hYL.trans E.hLX
  have hYnC : ¬ Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter (Z3.R₁ X R) : Set G) := by
    intro hYC
    apply h.not_cent
    intro v hv φ hφ
    obtain ⟨⟨y, hyN⟩, hyY, rfl⟩ := (mem_autI hV).1 (hYs hφ)
    apply IntMod.val_injective
    rw [convI_apply_val]
    have := Subgroup.mem_centralizer_iff.1 (hYC hyY) v.val (E.fixV_J_le_R₁ hv)
    calc y * v.val * y⁻¹ = (y * v.val) * y⁻¹ := rfl
      _ = (v.val * y) * y⁻¹ := by rw [this]
      _ = v.val := by group
  have hsetup : Z3.Setup X R Y :=
    { charTwo := E.charTwo, R_le := E.R_le_X, R_pGroup := E.R_pGroup, Q_le := E.QR,
      Y_le := hYX, Y_res := hres, Y_index := hidx, Q_norm := hQY, S_norm := hSY,
      Y_not_C := hYnC }
  have hnc' : ∃ y ∈ Y, ∃ l ∈ L, y * l * y⁻¹ * l⁻¹ ∉ Subgroup.centralizer (V : Set G) := by
    obtain ⟨a, haY, b, hbL, hab⟩ := hnc
    obtain ⟨⟨y, hyN⟩, hyY, hya⟩ := (mem_autI hV).1 (hYs haY)
    obtain ⟨⟨l, hlN⟩, hlL, hlb⟩ := (mem_autI hV).1 hbL
    refine ⟨y, hyY, l, hlL, fun hc => hab ?_⟩
    have h1 : convI hV (⟨y, hyN⟩ * ⟨l, hlN⟩ * ⟨y, hyN⟩⁻¹ * ⟨l, hlN⟩⁻¹) = 1 :=
      (convI_eq_one_iff hV _).2 hc
    simp only [map_mul, map_inv, hya, hlb] at h1
    have h2 : a * b * a⁻¹ = b := mul_inv_eq_one.1 h1
    calc a * b = (a * b * a⁻¹) * a := by group
      _ = b * a := by rw [h2]
  refine ⟨Y, ⟨Or.inr hsetup, hYL, E.gen_lift hYL hYs h.gen, ?_, E.closure_lift hYL hnc', hQY⟩⟩
  intro hc
  have h0 : autI hV Y = ⊥ := autI_eq_bot_of_le_centralizer hV hc
  have hYs' : Ys ≤ ⊥ := h0 ▸ hYs
  have hcard := h.card
  rw [le_bot_iff.1 hYs', Subgroup.card_bot] at hcard
  omega

theorem exists_yData_of_starZ3 (h : StarZ3 X V L R hV Ys) (hm : 5 ≤ m)
    (e : ↥(autI hV L) ≃* ↥(alternatingGroup (Fin m))) :
    ∃ Y : Subgroup G, YData X V L R hV Y := by
  have hQn : ((pCoreOf 2 X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 X)).2
      (le_normalizer_pCoreOf 2 X)
  let B : XBar X V hV E.hXN (↥X ⧸ (pCoreOf 2 X).subgroupOf X) :=
    { π := QuotientGroup.mk' _
      ρ := QuotientGroup.lift _ (convHom hV X E.hXN) (fun q hq => by
        rw [MonoidHom.mem_ker, convHom_apply, convI_eq_one_iff]
        exact pCoreOf_le_centralizer E.red (Subgroup.mem_subgroupOf.1 hq))
      ker := fun g => by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf
      act := fun g => rfl }
  exact E.exists_yData_of_xBar B h hm e

end EntryPlus

theorem liftZ3_holds : LiftZ3 := by
  intro G _ _ X T V L R m hV Ys E hm e h
  exact E.exists_yData_of_starZ3 h (by omega) e.some

theorem c124StatementSQTK_of_spec_props (hGN : TheoremC118) (hE23 : E2.E23Statement)
    (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection) (hA36 : AsA36NoOddCover)
    (h4bL2 : Spec4bL2) (h4bAlt5 : Spec4bAlt5)
    (h4bAlt6b : Spec4bAlt6b) (h4bAlt6c : Spec4bAlt6c) (h4bAlt7 : Spec4bAlt7)
    (h4bHat6 : Spec4bHat6) (h4bA7Four : Spec4bA7Four) (h4cL2 : Spec4cL2) (h4cAlt5 : Spec4cAlt5)
    (h4cAlt6 : Spec4cAlt6) (h4cAlt7 : Spec4cAlt7) (h4cHat6 : Spec4cHat6)
    (h4cA7Four : Spec4cA7Four) (G : Type) [Group G] [Finite G] :
    C124StatementSQTK (G := G) :=
  c124StatementSQTK_of_specs hGN hE23 hI hA21 hA36 liftZ3_holds h4bL2 h4bAlt5 h4bAlt6b
    h4bAlt6c h4bAlt7 h4bHat6 h4bA7Four h4cL2 h4cAlt5 h4cAlt6 h4cAlt7 h4cHat6 h4cA7Four G

end CFSG.Quasithin.C124
