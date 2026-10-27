module

public import CFSG.Quasithin.H13.L32NLem14323a
public import CFSG.Quasithin.H13.L32NLem1444a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L1444

variable {G : Type} [Group G] [Finite G]

structure Setup2 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) : Prop where
  hyp : Hyp14310One G T L V
  ext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)
  card32 : Nat.card ↥(fsuU T V) = 2 ^ 5
  plane : IsL32NPlane T V V₂
  gP : g ∈ p128 T L V
  gH : g ∉ l32nH T V
  dim : Module.finrank (ZMod 2) D.V = 4
  zU : centerOf (fsuU T V) = fsuV1 T V
  cHat : l32nCHat T V = pCoreOf 2 (l32nH T V)
  elem : IsElemAbelian 2 V
  card8 : Nat.card V = 8
  normV : L ⊔ T ≤ Subgroup.normalizer (V : Set G)
  card2 : Nat.card ↥(fsuV1 T V) = 2
  hatE : D.hat V = D.hat (l32nE T V V₂ g) ∧ Nat.card ↥(D.hat V) = 4
  zUg : (D.img (CFSG.conjugate (centerOf (fsuU T V)) g)).relIndex
    (D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2

theorem exists_setup2 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hRest : Lemma14323Rest) {T L V V₂ : Subgroup G} {g : G} (h : Hyp14310One G T L V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V)) (h32 : Nat.card ↥(fsuU T V) = 2 ^ 5)
    (hV₂ : IsL32NPlane T V V₂) (hgP : g ∈ p128 T L V) (hgH : g ∉ l32nH T V) :
    ∃ D : HatModelU (fsuU T V), Setup2 G T L V V₂ g D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨hVe, hV8, hVN, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU h1222 h12213
  have hZ := zU_eq h1332 h1334 h1222 h12213 h hext
  have hC := cHat_eq h1332 h1334 h1222 h12213 h37 h38 h39 h hext
  have hd : Module.finrank (ZMod 2) D.V = 4 := by
    have hcard := D.card_U
    rw [hZ, hV1, h32] at hcard
    have h16 : Nat.card D.V = 2 ^ 4 := by omega
    have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.V)
    rw [h16, Nat.card_zmod] at hpow
    exact (Nat.pow_right_injective (le_refl 2) hpow).symm
  obtain ⟨hE, -, ⟨hzUg, -⟩, -⟩ := hRest G T L V h V₂ g hV₂ hgP hgH D hd
  exact ⟨D, h, hext, h32, hV₂, hgP, hgH, hd, hZ, hC, hVe, hV8, hVN, hV1, hE, hzUg⟩

omit [Finite G] in
theorem card_eq_card_imageOTwoQuot_mul (H X : Subgroup G) (hXH : X ≤ H) :
    Nat.card X = Nat.card (imageOTwoQuot H X) * Nat.card ↥(X ⊓ pCoreOf 2 H) := by
  set X' := X.subgroupOf H with hX'
  have h1 := Subgroup.card_ker_mul_card_range
    ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)).domRestrict X')
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict, QuotientGroup.ker_mk'] at h1
  have hX : Nat.card X' = Nat.card X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have h2 : Nat.card ((CFSG.Open.pCore 2 ↥H).subgroupOf X') =
      Nat.card ↥(X' ⊓ CFSG.Open.pCore 2 ↥H) := by
    rw [← Subgroup.inf_subgroupOf_left (CFSG.Open.pCore 2 ↥H) X']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : Nat.card ↥(X' ⊓ CFSG.Open.pCore 2 ↥H) = Nat.card ↥(X ⊓ pCoreOf 2 H) := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXH, pCoreOf,
      ← Subgroup.map_inf _ _ _ H.subtype_injective]
    exact (Subgroup.card_map_of_injective H.subtype_injective).symm
  rw [← hX, ← h1, h2, h3, mul_comm]
  rfl

theorem card_imageOTwoQuot_eq {T V : Subgroup G} (D : HatModelU (fsuU T V))
    (hC : l32nCHat T V = pCoreOf 2 (l32nH T V)) {X : Subgroup G} (hX : X ≤ l32nH T V) :
    Nat.card (imageOTwoQuot (l32nH T V) X) = Nat.card (D.img X) := by
  have himg : Nat.card (D.img X) = (l32nCHat T V).relIndex X :=
    L128A.HatU.card_img_eq_relIndex D (hX.trans (L14332.l32nH_le_normalizer_fsuU T V))
      fun x hx => ⟨fun ⟨hxN, h1⟩ => (L14332.rho_eq_one_iff_mem (D := D) (hX hx) hxN).mp h1,
        fun h1 => ⟨L14332.l32nH_le_normalizer_fsuU T V (hX hx),
          (L14332.rho_eq_one_iff_mem (D := D) (hX hx) _).mpr h1⟩⟩
  have h1 := Subgroup.relIndex_mul_card (H := l32nCHat T V) (K := X)
  have h2 := card_eq_card_imageOTwoQuot_mul (l32nH T V) X hX
  rw [← himg, hC, inf_comm] at h1
  have hpos : 0 < Nat.card ↥(X ⊓ pCoreOf 2 (l32nH T V)) := Nat.card_pos
  have h3 : Nat.card (D.img X) * Nat.card ↥(X ⊓ pCoreOf 2 (l32nH T V)) =
      Nat.card (imageOTwoQuot (l32nH T V) X) * Nat.card ↥(X ⊓ pCoreOf 2 (l32nH T V)) := by
    rw [h1, ← h2]
  exact (Nat.eq_of_mul_eq_mul_right hpos h3).symm

omit [Finite G] in
theorem V_le_U {T V : Subgroup G} : V ≤ fsuU T V := le_conjClosure V _

omit [Finite G] in
theorem Wg_le_cent {T V V₂ : Subgroup G} {g : G}
    (hgN : g ∈ Subgroup.normalizer (V₂ : Set G)) :
    CFSG.conjugate (l32nW T V V₂) g ≤ Subgroup.centralizer (V₂ : Set G) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hgv : g * v * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
  have hc := (Subgroup.mem_centralizer_iff.mp hw.2) _ hgv
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc v * (g⁻¹ * w * g) = g⁻¹ * ((g * v * g⁻¹) * w) * g := by group
    _ = g⁻¹ * (w * (g * v * g⁻¹)) * g := by rw [hc]
    _ = g⁻¹ * w * g * v := by group

omit [Finite G] in
theorem Wg_le_H {T V V₂ : Subgroup G} {g : G} (hV₂ : IsL32NPlane T V V₂)
    (hgN : g ∈ Subgroup.normalizer (V₂ : Set G)) :
    CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V := by
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (Wg_le_cent hgN hx)) v (hV₂.2 hv)

namespace Setup2

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}
  (S : Setup2 G T L V V₂ g D)
include S

theorem comm_V {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
  congrArg Subtype.val (S.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem g_normV₂ : g ∈ Subgroup.normalizer (V₂ : Set G) :=
  Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp S.gP.2 V₂) ⟨2, le_rfl, S.plane.1⟩

theorem g_normV : g ∈ Subgroup.normalizer (V : Set G) := S.normV S.gP.1

theorem V_le_W : V ≤ l32nW T V V₂ := fun _ hv =>
  ⟨V_le_U hv, Subgroup.mem_centralizer_iff.mpr fun _ hw => S.comm_V (S.plane.1.1 hw) hv⟩

theorem V_le_Wg : V ≤ CFSG.conjugate (l32nW T V V₂) g := by
  intro v hv
  refine ⟨g * v * g⁻¹, S.V_le_W ((Subgroup.mem_normalizer_iff.mp S.g_normV v).mp hv), ?_⟩
  simp [mul_assoc]

theorem eq_E : V = l32nE T V V₂ g := by
  have hVE : V ≤ l32nE T V V₂ g := le_inf S.V_le_W S.V_le_Wg
  have hEU : l32nE T V V₂ g ≤ fsuU T V := inf_le_left.trans inf_le_left
  have hcard := D.card_eq_mul_range hEU
  rw [← L14323.card_hat_eq D hEU, ← S.hatE.1, S.hatE.2] at hcard
  have h2 : Nat.card ↥(l32nE T V V₂ g ⊓ centerOf (fsuU T V)) ≤ 2 := by
    rw [← S.card2, ← S.zU]
    exact Subgroup.card_le_of_le inf_le_right
  exact Subgroup.eq_of_le_of_card_ge hVE (by rw [S.card8, hcard]; omega)

theorem Wg_le_H : CFSG.conjugate (l32nW T V V₂) g ≤ l32nH T V :=
  L1444.Wg_le_H S.plane S.g_normV₂

theorem img_zUg : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) = ⊥ := by
  have hZgU : CFSG.conjugate (centerOf (fsuU T V)) g ≤ fsuU T V := by
    rintro _ ⟨x, hx, rfl⟩
    rw [S.zU] at hx
    have hxV₂ : x ∈ V₂ := S.plane.2 hx
    have h1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem S.g_normV₂) x).mp
      hxV₂
    exact V_le_U (S.plane.1.1 (by simpa using h1))
  exact img_eq_bot_of_le D (comm_mem_centerOf S.ext) hZgU

theorem card_img_Wg : Nat.card (D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 := by
  have h := S.zUg
  rw [S.img_zUg, Subgroup.relIndex_bot_left] at h
  exact h

theorem card_Wg : Nat.card (imageOTwoQuot (l32nH T V) (CFSG.conjugate (l32nW T V V₂) g)) = 2 :=
  (card_imageOTwoQuot_eq D S.cHat S.Wg_le_H).trans S.card_img_Wg

end Setup2

end L1444

end CFSG.Quasithin.H13
