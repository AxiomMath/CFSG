module

public import CFSG.Quasithin.Background.C124AsmLiftBase
public import CFSG.Quasithin.Background.C124AsmPre
public import CFSG.Quasithin.Background.C1GNA7Base

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV)

include E

theorem fixV_J_le {v : IntMod V hV} (hv : v ∈ fixV (autI hV (thompsonJ R))) :
    v.val ∈ quasithinOmegaOneCenter (baum R) := by
  refine E.mem_omegaOneCenter_baum v.val_mem fun j hj => ?_
  have hjN : j ∈ Subgroup.normalizer (V : Set G) :=
    E.hXN (E.R_le_X (thompsonJ_le_self R hj))
  have h2 := congrArg IntMod.val (hv (convI hV ⟨j, hjN⟩) (convI_mem_autI hV hj hjN))
  rw [convI_apply_val] at h2
  calc j * v.val = (j * v.val * j⁻¹) * j := by group
    _ = v.val * j := by rw [h2]

theorem exists_yData_of_starL2 {Ys : Subgroup (MulAut (IntMod V hV))}
    (h : StarL2 X V L R hV Ys) : ∃ Y : Subgroup G, YData X V L R hV Y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.sl2
  obtain ⟨-, hperf, h60, hnc⟩ := sl2_four_facts hF e
  set Y₁ := preI hV L E.hLN Ys with hY₁
  set Y := perfectCore Y₁ with hY
  have hY₁L : Y₁ ≤ L := preI_le hV
  have hYY₁ : Y ≤ Y₁ := perfectCore_le Y₁
  have hYL : Y ≤ L := hYY₁.trans hY₁L
  have hYX : Y ≤ X := hYL.trans E.hLX
  have hautY₁ : autI hV Y₁ = Ys := autI_preI hV h.le_L
  have hYsperf : ⁅Ys, Ys⁆ = Ys := Subgroup.isPerfect_iff.mp hperf
  have hautY : autI hV Y = Ys := by
    rw [hY, autI_perfectCore E.hLN hY₁L, hautY₁]
    exact perfectCore_eq_self_of_perfect hYsperf
  have hnormY : ∀ (x : G) (hx : x ∈ X), convI hV ⟨x, E.hXN hx⟩ ∈
      Subgroup.normalizer (Ys : Set (MulAut (IntMod V hV))) →
      x ∈ Subgroup.normalizer (Y : Set G) := fun x hx hxn =>
    normalizer_le_normalizer_perfectCore Y₁ (E.mem_normalizer_preI hx hxn)
  have hQY : pCoreOf 2 X ≤ Subgroup.normalizer (Y : Set G) := fun q hq =>
    hnormY q (pCoreOf_le 2 X hq) (by
      have : convI hV ⟨q, E.hXN (pCoreOf_le 2 X hq)⟩ = 1 :=
        (convI_eq_one_iff hV _).2 (pCoreOf_le_centralizer E.red hq)
      rw [this]
      exact Subgroup.one_mem _)
  have hSY : baum R ≤ Subgroup.normalizer (Y : Set G) := fun s hs =>
    hnormY s (E.R_le_X (E.baum_le_R hs)) (Subgroup.le_normalizer
      (h.sylow.1 (convI_mem_autI hV hs _)))
  have hYC : ⁅Y ⊓ Subgroup.centralizer (V : Set G), Y⁆ ≤ pCoreOf 2 X := by
    refine Subgroup.commutator_le.2 fun d hd y hy => ?_
    exact E.pCoreOf_L_le_Q (E.comm_C_L d ⟨hYX hd.1, hd.2⟩ y (hYL hy))
  have hsylY₁ := E.isSylowTwoOf_inf_preI h.le_L h.sylow
  have hsylY : IsSylowTwoOf (R ⊓ Y) Y := by
    have := B6.isSylowTwoOf_inf_normal hsylY₁ hYY₁
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore Y₁))
    rwa [inf_assoc, inf_eq_right.2 hYY₁] at this
  have hYnC : ¬ Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter (baum R) : Set G) := by
    intro hYC'
    apply h.not_cent
    intro v hv φ hφ
    obtain ⟨⟨y, hyN⟩, hyY, rfl⟩ := (mem_autI hV).1 (hautY.ge hφ)
    apply IntMod.val_injective
    rw [convI_apply_val]
    have := Subgroup.mem_centralizer_iff.1 (hYC' hyY) v.val (E.fixV_J_le hv)
    calc y * v.val * y⁻¹ = (y * v.val) * y⁻¹ := rfl
      _ = (v.val * y) * y⁻¹ := by rw [this]
      _ = v.val := by group
  have hnc' : ∃ y ∈ Y, ∃ l ∈ L, y * l * y⁻¹ * l⁻¹ ∉ Subgroup.centralizer (V : Set G) := by
    obtain ⟨a, b, hab⟩ := hnc
    obtain ⟨⟨y, hyN⟩, hyY, hya⟩ := (mem_autI hV).1 (hautY.ge a.2)
    obtain ⟨⟨l, hlN⟩, hlY, hlb⟩ := (mem_autI hV).1 (hautY.ge b.2)
    refine ⟨y, hyY, l, hYL hlY, fun hc => hab (Subtype.ext ?_)⟩
    have h1 : convI hV (⟨y, hyN⟩ * ⟨l, hlN⟩ * ⟨y, hyN⟩⁻¹ * ⟨l, hlN⟩⁻¹) = 1 :=
      (convI_eq_one_iff hV _).2 hc
    simp only [map_mul, map_inv, hya, hlb] at h1
    have h2 : (a : MulAut (IntMod V hV)) * b * (a : MulAut (IntMod V hV))⁻¹ = b :=
      mul_inv_eq_one.1 h1
    show (a : MulAut (IntMod V hV)) * b = b * a
    calc (a : MulAut (IntMod V hV)) * b
        = ((a : MulAut (IntMod V hV)) * b * (a : MulAut (IntMod V hV))⁻¹) * a := by group
      _ = b * a := by rw [h2]
  have hsetup : L2P.Setup X R Y V hV :=
    { charTwo := E.charTwo, sqtk := C1GN.isSQTKTC_iff_sqtkGroup.2 E.sqtk, red := E.red
      R_le := E.R_le_X, R_pGroup := E.R_pGroup, Q_le := E.QR, hJ := E.hJ, Y_le := hYX
      Y_perf := perfectCore_perfect Y₁, Q_norm := hQY, S_norm := hSY, Y_C := hYC
      RY_syl := hsylY, S_star := h.sylow.1.trans hautY.ge, Y_not_C := hYnC
      sl2 := ⟨F, inferInstance, inferInstance, hF, ⟨(MulEquiv.subgroupCongr hautY).trans e⟩⟩ }
  refine ⟨Y, ⟨Or.inl hsetup, hYL, E.gen_lift hYL hautY.ge h.gen, ?_,
    E.closure_lift hYL hnc', hQY⟩⟩
  intro hc
  have h0 : autI hV Y = ⊥ := autI_eq_bot_of_le_centralizer hV hc
  rw [h0] at hautY
  rw [← hautY, Subgroup.card_bot] at h60
  omega

end EntryPlus

end CFSG.Quasithin.C124
