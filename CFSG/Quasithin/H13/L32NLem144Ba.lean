module

public import CFSG.Quasithin.H13.L32NLem14411a
public import CFSG.Quasithin.H13.L32NLem14332h
public import CFSG.Quasithin.H13.L32NLem1444a

public section

namespace CFSG.Quasithin.H13.L144B

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411

structure Base (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G) : Prop where
  h1332 : Stmt13_3_2
  h1334 : A6.Stmt13_3_4
  h1222 : Stmt12_2_2
  hyp : Hyp14310One G T L V
  ext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)
  plane : IsL32NPlane T V V₂
  gP : g ∈ p128 T L V
  gH : g ∉ l32nH T V
  zU : centerOf (fsuU T V) = fsuV1 T V
  cHat : l32nCHat T V = pCoreOf 2 (l32nH T V)
  s1282 : Setting1282One G T L V 3 (fsuV1 T V) V₂
  abs : L128A.Setting V₂ (fsuV1 T V) (oTwoUpper (p128 T L V)) T
  uA : L128A.uA V₂ (fsuV1 T V) = fsuU T V
  wwE : ⁅l32nW T V V₂, CFSG.conjugate (l32nW T V V₂) g⁆ ≤ l32nE T V V₂ g
  elemE : IsElemAbelian 2 (l32nE T V V₂ g)
  nWg : l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G) ≤
    Subgroup.normalizer ((CFSG.conjugate (l32nW T V V₂) g ⊔ l32nCHat T V : Subgroup G) : Set G)

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}

theorem exists_base (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h12811 : Lemma12_8_11) (h12812 : Lemma12_8_12_two)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (hV₂ : IsL32NPlane T V V₂)
    (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) : Base G T L V V₂ g := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have hs := h.setting1282One h13322 hV hV₂
  exact
    { h1332 := h1332, h1334 := h1334, h1222 := h1222, hyp := h, ext := hext, plane := hV₂,
      gP := hgP, gH := hgH, zU := L1444.zU_eq h1332 h1334 h1222 h12213 h hext,
      cHat := L1444.cHat_eq h1332 h1334 h1222 h12213 h37 h38 h39 h hext, s1282 := hs,
      abs := L128P.setting128A h1222 h12213 hs, uA := (lemma12_8_8_six h1222 hs).symm,
      wwE := (h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH).1,
      elemE := (h12811 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH).2.1,
      nWg := (h12812 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgH).1 }

namespace Base

variable (C : Base G T L V V₂ g)
include C

theorem UT : fsuU T V ≤ T := C.uA ▸ C.abs.uA_le_T

theorem TH : T ≤ l32nH T V := C.hyp.le_l32nH (stmtL32NModule_of_inputs C.h1332 C.h1334)

theorem UH : fsuU T V ≤ l32nH T V := C.UT.trans C.TH

theorem comm_center : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b * a⁻¹ * b⁻¹ ∈ centerOf (fsuU T V) :=
  L1444.comm_mem_centerOf C.ext

theorem set14 : ∃ _ : IsMulCommutative ↥V, L32NSet14.Setting G T L V V₂ :=
  L14332.exists_setting C.h1332 C.h1334 C.h1222 C.hyp C.plane

theorem V2U : V₂ ≤ fsuU T V := C.uA ▸ L128A.le_uA V₂ (fsuV1 T V)

theorem gV₂ : g ∈ Subgroup.normalizer (V₂ : Set G) :=
  L128P.p128_le_normalizer le_rfl C.plane.1 C.gP

theorem Wg_cent : CFSG.conjugate (l32nW T V V₂) g ≤ Subgroup.centralizer (V₂ : Set G) :=
  L14332.conj_le_centralizer_of_le inf_le_right le_rfl C.gV₂

theorem WgH : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V :=
  (L14332.conj_le_centralizer_of_le inf_le_right C.plane.2 C.gV₂).trans
    (Subgroup.centralizer_le_normalizer _)

theorem V2E : V₂ ≤ l32nE T V V₂ g := by
  obtain ⟨_, S⟩ := C.set14
  have hW : V₂ ≤ l32nW T V V₂ := fun v hv => ⟨C.V2U hv, Subgroup.mem_centralizer_iff.mpr
    fun w hw => S.comm_V (C.plane.1.1 hw) (C.plane.1.1 hv)⟩
  refine le_inf hW fun v hv => ?_
  rw [show CFSG.conjugate (l32nW T V V₂) g = rconj (l32nW T V V₂) g from rfl, mem_rconj]
  exact hW ((Subgroup.mem_normalizer_iff.mp C.gV₂ v).mp hv)

theorem conj_a_mem {a t : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) (ht : t ∈ T) :
    (t * a * t⁻¹)⁻¹ * a ∈ centerOf (fsuU T V) := by
  obtain ⟨_, S⟩ := C.set14
  have htV₂ : t * a * t⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp (C.plane.1.2.2 ht) a).mp ha
  have htV₁ : t * a * t⁻¹ ∉ fsuV1 T V := fun h =>
    haV ((Subgroup.mem_normalizer_iff.mp (C.TH ht) a).mpr h)
  rw [C.zU]
  rcases S.mem_V2 htV₂ htV₁ ha with h | h
  · exact absurd h haV
  · have hsq : (t * a * t⁻¹) * (t * a * t⁻¹) = 1 := S.mul_self_V (C.plane.1.1 htV₂)
    rw [inv_eq_of_mul_eq_one_right hsq]
    exact h

theorem matOf_eq_one_iff (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
    {h : G} (hh : h ∈ l32nH T V) :
    matOf e (D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩) = 1 ↔
      h ∈ pCoreOf 2 (l32nH T V) := by
  rw [← C.cHat, ← L14332.rho_eq_one_iff_mem hh (L14332.l32nH_le_normalizer_fsuU T V hh),
    ← (matOf e).map_one]
  exact (matOf_injective e).eq_iff

theorem UQ (D : HatModelU (fsuU T V)) : fsuU T V ≤ pCoreOf 2 (l32nH T V) := by
  intro u hu
  rw [← C.cHat, ← L14332.rho_eq_one_iff_mem (C.UH hu)
    (L14332.l32nH_le_normalizer_fsuU T V (C.UH hu))]
  exact L128A.HatU.rho_eq_one_of_mem D C.comm_center hu _

theorem conj_center_mem (D : HatModelU (fsuU T V)) {z : G} (hz : z ∈ centerOf (fsuU T V)) :
    g⁻¹ * z * g ∈ pCoreOf 2 (l32nH T V) := by
  have hzV : z ∈ V₂ := C.plane.2 (C.zU ▸ hz)
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ C.gV₂) z).mp hzV
  rw [inv_inv] at this
  exact C.UQ D (C.V2U this)

theorem sq_mem_Q (D : HatModelU (fsuU T V)) {w : G} (hw : w ∈ CFSG.conjugate (l32nW T V V₂) g) :
    w * w ∈ pCoreOf 2 (l32nH T V) := by
  rw [show CFSG.conjugate (l32nW T V V₂) g = rconj (l32nW T V V₂) g from rfl, mem_rconj] at hw
  have huU : g * w * g⁻¹ ∈ fsuU T V := hw.1
  have hsq : (g * w * g⁻¹) * (g * w * g⁻¹) ∈ centerOf (fsuU T V) := by
    rw [← L128A.HatU.π_eq_zero_iff D (Subgroup.mul_mem _ huU huU), D.π_mul _ huU _ huU,
      ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have := C.conj_center_mem D hsq
  rwa [show g⁻¹ * ((g * w * g⁻¹) * (g * w * g⁻¹)) * g = w * w by group] at this

theorem comm_mem_Q (D : HatModelU (fsuU T V)) {w w' : G} (hw : w ∈ CFSG.conjugate (l32nW T V V₂) g)
    (hw' : w' ∈ CFSG.conjugate (l32nW T V V₂) g) :
    w * w' * w⁻¹ * w'⁻¹ ∈ pCoreOf 2 (l32nH T V) := by
  rw [show CFSG.conjugate (l32nW T V V₂) g = rconj (l32nW T V V₂) g from rfl, mem_rconj] at hw hw'
  have := C.conj_center_mem D (C.comm_center _ hw.1 _ hw'.1)
  rwa [show g⁻¹ * ((g * w * g⁻¹) * (g * w' * g⁻¹) * (g * w * g⁻¹)⁻¹ * (g * w' * g⁻¹)⁻¹) * g =
    w * w' * w⁻¹ * w'⁻¹ by group] at this

theorem mem_normalizer_of_fix (D : HatModelU (fsuU T V)) {a h : G} (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hh : h ∈ l32nH T V)
    (hfix : D.ρ ⟨h, L14332.l32nH_le_normalizer_fsuU T V hh⟩ (D.π a) = D.π a) :
    h ∈ Subgroup.normalizer (V₂ : Set G) := by
  obtain ⟨_, S⟩ := C.set14
  have haU := C.V2U ha
  rw [D.ρ_π _ a haU, D.π_eq_iff _ (L128A.HatU.conj_mem (L14332.l32nH_le_normalizer_fsuU T V hh)
    haU) a haU, C.zU] at hfix
  have hha : h * a * h⁻¹ ∈ V₂ := by
    have : h * a * h⁻¹ = a * ((h * a * h⁻¹)⁻¹ * a)⁻¹ := by group
    rw [this]
    exact V₂.mul_mem ha (V₂.inv_mem (C.plane.2 hfix))
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rcases S.mem_V2 ha haV hv with h1 | h1
  · exact C.plane.2 ((Subgroup.mem_normalizer_iff.mp hh v).mp h1)
  · have haa : a * a = 1 := S.mul_self_V (C.plane.1.1 ha)
    have hv' : v = a * (a * v) := by
      rw [← mul_assoc, haa, one_mul]
    rw [hv', show h * (a * (a * v)) * h⁻¹ = (h * a * h⁻¹) * (h * (a * v) * h⁻¹) by group]
    exact V₂.mul_mem hha (C.plane.2 ((Subgroup.mem_normalizer_iff.mp hh _).mp h1))

theorem rho_T_pi_a (D : HatModelU (fsuU T V)) {a t : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (ht : t ∈ T) (htN : t ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨t, htN⟩ (D.π a) = D.π a := by
  have haU := C.V2U ha
  rw [D.ρ_π _ a haU]
  exact ((D.π_eq_iff _ (L128A.HatU.conj_mem htN haU) a haU).mpr (C.conj_a_mem ha haV ht))

theorem rho_Wg_pi_a (D : HatModelU (fsuU T V)) {a w : G} (ha : a ∈ V₂)
    (hw : w ∈ CFSG.conjugate (l32nW T V V₂) g) (hwN : w ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨w, hwN⟩ (D.π a) = D.π a := by
  rw [D.ρ_π _ a (C.V2U ha), (Subgroup.mem_centralizer_iff.mp (C.Wg_cent hw) a ha).symm]
  congr 1
  group

theorem pi_a_ne (D : HatModelU (fsuU T V)) {a : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) :
    D.π a ≠ 0 := by
  rw [Ne, L128A.HatU.π_eq_zero_iff D (C.V2U ha), C.zU]
  exact haV

end Base

end CFSG.Quasithin.H13.L144B
