module

public import CFSG.Quasithin.H13.L32A711b
public import CFSG.Quasithin.H13.L32A711d
public import CFSG.Quasithin.H13.L32NLem14413b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G]

theorem modelIdx_SL22 : ModelIdx SL22.K SL22.P0 SL22.X1 SL22.X2 where
  p2 := SL22.P0_sylow.1
  syl := SL22.P0_sylow.2
  cls := SL22.overgroups_SL22
  le₁ := fun _ hx => SL22.mem_X1.2 (Subgroup.mem_prod.1 hx).2
  le₂ := fun _ hx => SL22.mem_X2.2 (Subgroup.mem_prod.1 hx).1
  inc₁ := SL22.X_incomparable.1
  inc₂ := SL22.X_incomparable.2
  idx₁ := relIndex_eq_of_card
    (show SL22.P0 ≤ SL22.X1 from fun _ hx => SL22.mem_X1.2 (Subgroup.mem_prod.1 hx).2)
    (by rw [SL22.card_X1, SL22.card_P0]) (by rw [SL22.card_P0]; norm_num)
  idx₂ := relIndex_eq_of_card
    (show SL22.P0 ≤ SL22.X2 from fun _ hx => SL22.mem_X2.2 (Subgroup.mem_prod.1 hx).1)
    (by rw [SL22.card_X2, SL22.card_P0]) (by rw [SL22.card_P0]; norm_num)
  nn₁ := not_le_normalizer_of_conj (x := (SL22.s, 1)) (p := (SL22.u, 1))
    (SL22.mem_X1.2 (show SL22.InU 1 by decide +kernel))
    (Subgroup.mem_prod.2 ⟨show SL22.InU SL22.u by decide +kernel,
      show SL22.InU 1 by decide +kernel⟩)
    (fun h => absurd (Subgroup.mem_prod.1 h).1
      (show ¬ SL22.InU (SL22.s * SL22.u * SL22.s⁻¹) by decide +kernel))
  nn₂ := not_le_normalizer_of_conj (x := (1, SL22.s)) (p := (1, SL22.u))
    (SL22.mem_X2.2 (show SL22.InU 1 by decide +kernel))
    (Subgroup.mem_prod.2 ⟨show SL22.InU 1 by decide +kernel,
      show SL22.InU SL22.u by decide +kernel⟩)
    (fun h => absurd (Subgroup.mem_prod.1 h).2
      (show ¬ SL22.InU (SL22.s * SL22.u * SL22.s⁻¹) by decide +kernel))

theorem index_P0_SL22 : SL22.P0.index = 9 := by
  have h := Subgroup.card_mul_index SL22.P0
  rw [SL22.card_P0, SL22.card_K] at h
  omega

theorem exists_L2_cube {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S : L32NSet14.Setting G T L V V₂) {z w b : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hw : w ∈ V₂) (hwV : w ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) :
    ∃ l ∈ L₁Of L V₂, l ^ 3 = 1 ∧ l * z * l⁻¹ = w := by
  have hzV₂ := S.hV2.1 hz
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz).1
  have hwV' : w ∈ V := S.hV2.2.1 hw
  obtain ⟨l, hlL, hl3, -, hlz, hlw⟩ := S.exists_rot hb hzV hwV' hz1
    (fun h => hwV (h ▸ one_mem _)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ hw))
    (fun h => hwV (h ▸ hz)) (fun h => hbV (by
      have := mul_mem hw (inv_mem hzV₂)
      rwa [h, mul_inv_cancel_right] at this))
  have hlN : l ∈ Subgroup.normalizer (V₂ : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    rcases S.mem_V2 hw hwV hv with h | h
    · rcases S.eq_of_mem_V1 hz hz1 h with rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [hlz]
        exact hw
    · rcases S.eq_of_mem_V1 hz hz1 h with h' | h'
      · rw [eq_inv_of_mul_eq_one_right h',
          show l * w⁻¹ * l⁻¹ = (l * w * l⁻¹)⁻¹ by group, hlw]
        exact inv_mem (mul_mem hzV₂ hw)
      · rw [show v = w⁻¹ * z by rw [← h']; group,
          show l * (w⁻¹ * z) * l⁻¹ = (l * w * l⁻¹)⁻¹ * (l * z * l⁻¹) by group, hlw, hlz]
        exact mul_mem (inv_mem (mul_mem hzV₂ hw)) hw
  exact ⟨l, Subgroup.subset_closure ⟨⟨hlL, hlN⟩, 3, by decide, hl3⟩, hl3, hlz⟩

omit [Finite G] in
theorem relIndex_dvd_relIndex {T X Y : Subgroup G} (hTX : T ≤ X) (hXY : X ≤ Y) :
    T.relIndex X ∣ T.relIndex Y :=
  Dvd.intro _ (Subgroup.relIndex_mul_relIndex T X Y hTX hXY)

namespace Ctx711

variable {T L V H V₂ H₂ : Subgroup G} {z a l p : G} (C : Ctx711 T L V H V₂ H₂ z a l p)
include C

theorem LT_SL3 : quasithinO2QuotientIso (L ⊔ T) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have := C.V_comm
  have S14 := Hyp147.set14 C.S.hyp C.h1222 C.h1332 C.h1334 C.hV2
  have htop : autOn (L ⊔ T) V = ⊤ := by
    have h1 : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One S14.h1281
    rw [eq_top_iff, ← h1]
    exact autOn_mono le_sup_left
  exact L14413.quasithinO2QuotientIso_SL3_of (sup_le S14.LV S14.TV) (fun v hv => S14.sq_V hv)
    (by rw [S14.card_V]; norm_num) htop S14.isPGroup_cent_sup

theorem LT_idx : T.relIndex (L ⊔ T) = 21 := by
  obtain ⟨A₁, A₂, -, -, -, -, -, -, -, -, -, -, -, -, h, -, -⟩ :=
    modelIdx_SL3.transport C.LT_SL3 (C.syl le_sup_right)
  rw [h, index_P0_SL3]

theorem d1_idx : T.relIndex (d1 T L H₂ V₂) = 9 := by
  obtain ⟨A₁, A₂, -, -, -, -, -, -, -, -, -, -, -, -, h, -, -⟩ :=
    modelIdx_SL22.transport C.d1_SL22 (C.syl (T_le_d1 T L H₂ V₂))
  rw [h, index_P0_SL22]

theorem l_not_NV1 : l ∉ Subgroup.normalizer (fsuV1 T V : Set G) := fun h => by
  have := (Subgroup.mem_normalizer_iff.mp h z).mp C.hz
  rw [C.hlz] at this
  exact C.haV this

theorem H_inf_d1 (hidx : ¬ T.relIndex H ∣ 9) : H ⊓ d1 T L H₂ V₂ = H₂ := by
  have hle : H₂ ≤ H ⊓ d1 T L H₂ V₂ := le_inf C.H₂H C.H₂_le_d1
  rcases C.cls _ (C.TH₂.trans hle) inf_le_left with h | h | h | h
  · exfalso
    have h1 : T.relIndex H₂ = 1 := Subgroup.relIndex_eq_one.mpr (hle.trans h.le)
    rw [C.idx] at h1
    norm_num at h1
  · exact absurd (hle.trans h.le) C.inc
  · exact h
  · exfalso
    apply hidx
    rw [← C.d1_idx]
    exact relIndex_dvd_relIndex C.TH (h ▸ inf_le_right)

theorem LT_le_M : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer C.TL

theorem H₂_not_le_LT : ¬ H₂ ≤ L ⊔ T := fun h =>
  C.Y_not_le_M (((oTwoUpper_le H₂).trans h).trans C.LT_le_M)

theorem l_not_T : l ∉ T := fun h => C.l_moves (C.T_fix_z h)

theorem l_mem_d1_LT : l ∈ d1 T L H₂ V₂ ⊓ (L ⊔ T) :=
  ⟨L2_le_d1 T L H₂ V₂ C.hl, Subgroup.mem_sup_left (L2_le_L L V₂ C.hl)⟩

theorem l1_not_le_T : ¬ l1 T L V ≤ T := by
  have := C.V_comm
  have S14 := Hyp147.set14 C.S.hyp C.h1222 C.h1332 C.h1334 C.hV2
  have h3 := S14.Lp3
  rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _] at h3
  intro hle
  have hYp : l1 T L V ≤ pCoreOf 2 (l1 T L V) :=
    le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer (C.T2.to_le hle)
  rw [Subgroup.relIndex_eq_one.mpr hYp] at h3
  omega

theorem inf3_eq (hidx : ¬ T.relIndex H ∣ 9) : H ⊓ d1 T L H₂ V₂ ⊓ (L ⊔ T) = T := by
  rw [C.H_inf_d1 hidx]
  have hle : T ≤ H₂ ⊓ (L ⊔ T) := le_inf C.TH₂ le_sup_right
  have hm := Subgroup.relIndex_mul_relIndex T (H₂ ⊓ (L ⊔ T)) H₂ hle inf_le_left
  rw [C.idx] at hm
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ hm) with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hle
  · exfalso
    rw [h] at hm
    have h1 : (H₂ ⊓ (L ⊔ T)).relIndex H₂ = 1 := by omega
    exact C.H₂_not_le_LT ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)

abbrev es (T L H H₂ V₂ : Subgroup G) : Fin 3 → Subgroup G := ![H, d1 T L H₂ V₂, L ⊔ T]

theorem es_syl (hidx : ¬ T.relIndex H ∣ 9) :
    ∀ i : Fin 3, IsSylowTwoOf (es T L H H₂ V₂ 0 ⊓ es T L H H₂ V₂ 1 ⊓ es T L H H₂ V₂ 2)
      (es T L H H₂ V₂ i) := by
  intro i
  change IsSylowTwoOf (H ⊓ d1 T L H₂ V₂ ⊓ (L ⊔ T)) _
  rw [C.inf3_eq hidx]
  fin_cases i
  · exact C.syl C.TH
  · exact C.syl (T_le_d1 T L H₂ V₂)
  · exact C.syl le_sup_right

theorem es_T (hidx : ¬ T.relIndex H ∣ 9) : ∀ i j : Fin 3, i ≠ j →
    es T L H H₂ V₂ i ⊓ es T L H H₂ V₂ j ≠
      es T L H H₂ V₂ 0 ⊓ es T L H H₂ V₂ 1 ⊓ es T L H H₂ V₂ 2 := by
  intro i j hij
  change _ ≠ H ⊓ d1 T L H₂ V₂ ⊓ (L ⊔ T)
  rw [C.inf3_eq hidx]
  have h01 : H ⊓ d1 T L H₂ V₂ ≠ T := by
    rw [C.H_inf_d1 hidx]
    intro h
    have h1 : T.relIndex H₂ = 1 := Subgroup.relIndex_eq_one.mpr h.le
    rw [C.idx] at h1
    norm_num at h1
  have h02 : H ⊓ (L ⊔ T) ≠ T := fun h => C.l1_not_le_T
    ((le_inf C.L1H ((oTwoUpper_le _).trans (inf_le_left.trans le_sup_left))).trans h.le)
  have h12 : d1 T L H₂ V₂ ⊓ (L ⊔ T) ≠ T := fun h => C.l_not_T (h ▸ C.l_mem_d1_LT)
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01
  · exact h02
  · rw [inf_comm]; exact h01
  · exact absurd rfl hij
  · exact h12
  · rw [inf_comm]; exact h02
  · rw [inf_comm]; exact h12
  · exact absurd rfl hij

theorem es_X (hidx : ¬ T.relIndex H ∣ 9) : ∀ i j : Fin 3, i ≠ j →
    es T L H H₂ V₂ i ⊓ es T L H H₂ V₂ j ≠ es T L H H₂ V₂ i := by
  have hlN : l ∈ L ⊔ T := Subgroup.mem_sup_left (L2_le_L L V₂ C.hl)
  have hl1 : l ∈ d1 T L H₂ V₂ := L2_le_d1 T L H₂ V₂ C.hl
  have hH1 : ¬ H ≤ d1 T L H₂ V₂ := fun h => hidx (by
    rw [← C.d1_idx]
    exact relIndex_dvd_relIndex C.TH h)
  have hH2 : ¬ H ≤ L ⊔ T := fun h => C.S.hz.2.2 (h.trans C.LT_le_M)
  have h10 : ¬ d1 T L H₂ V₂ ≤ H := fun h => C.l_not_NV1 (C.S.hz.2.1 (h hl1))
  have h12 : ¬ d1 T L H₂ V₂ ≤ L ⊔ T := fun h =>
    C.Y_not_le_M (((Y_le_d1 T L H₂ V₂).trans h).trans C.LT_le_M)
  have h20 : ¬ L ⊔ T ≤ H := fun h => C.l_not_NV1 (C.S.hz.2.1 (h hlN))
  have h21 : ¬ L ⊔ T ≤ d1 T L H₂ V₂ := fun h => by
    have := relIndex_dvd_relIndex le_sup_right h
    rw [C.LT_idx, C.d1_idx] at this
    norm_num at this
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact fun h => hH1 (inf_eq_left.mp h)
  · exact fun h => hH2 (inf_eq_left.mp h)
  · exact fun h => h10 (inf_eq_left.mp h)
  · exact absurd rfl hij
  · exact fun h => h12 (inf_eq_left.mp h)
  · exact fun h => h20 (inf_eq_left.mp h)
  · exact fun h => h21 (inf_eq_left.mp h)
  · exact absurd rfl hij

theorem es_dist (hidx : ¬ T.relIndex H ∣ 9) : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    es T L H H₂ V₂ i ⊓ es T L H H₂ V₂ j ≠ es T L H H₂ V₂ i ⊓ es T L H H₂ V₂ k := by
  have hHd := C.H_inf_d1 hidx
  have hdH : d1 T L H₂ V₂ ⊓ H = H₂ := by rw [inf_comm]; exact hHd
  have hA : H ⊓ d1 T L H₂ V₂ ≠ H ⊓ (L ⊔ T) := fun h => C.H₂_not_le_LT (by
    rw [← hHd, h]; exact inf_le_right)
  have hB : d1 T L H₂ V₂ ⊓ H ≠ d1 T L H₂ V₂ ⊓ (L ⊔ T) := fun h => C.H₂_not_le_LT (by
    rw [← hdH, h]; exact inf_le_right)
  have hC : (L ⊔ T) ⊓ H ≠ (L ⊔ T) ⊓ d1 T L H₂ V₂ := fun h => by
    have h1 : l1 T L V ⊔ T ≤ (L ⊔ T) ⊓ H :=
      le_inf (sup_le_sup_right ((oTwoUpper_le _).trans inf_le_left) T) (sup_le C.L1H C.TH)
    rw [h] at h1
    apply C.inc'
    rw [← hHd]
    exact le_inf (sup_le C.L1H C.TH) (h1.trans inf_le_right)
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
    | exact absurd rfl hij
    | exact absurd rfl hik
    | exact absurd rfl hjk
    | exact hA
    | exact hA.symm
    | exact hB
    | exact hB.symm
    | exact hC
    | exact hC.symm

theorem es_D4 (hidx : ¬ T.relIndex H ∣ 9) : ∀ N : Subgroup G,
    N ≤ es T L H H₂ V₂ 0 ⊓ es T L H H₂ V₂ 1 ⊓ es T L H H₂ V₂ 2 →
    es T L H H₂ V₂ 0 ⊔ es T L H H₂ V₂ 1 ⊔ es T L H H₂ V₂ 2 ≤ Subgroup.normalizer (N : Set G) →
    N = ⊥ := by
  intro N hN hD
  change N ≤ H ⊓ d1 T L H₂ V₂ ⊓ (L ⊔ T) at hN
  change H ⊔ d1 T L H₂ V₂ ⊔ (L ⊔ T) ≤ Subgroup.normalizer (N : Set G) at hD
  rw [C.inf3_eq hidx] at hN
  by_contra hne
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨N, hne, C.T2.to_le hN, rfl⟩ : IsTwoLocal (Subgroup.normalizer (N : Set G)))
  have hL13 := C.h1332 G T L C.S.hyp.hyp.h13 L C.S.hyp.hyp.h13.faithful
  have hMeq := hL13.2.1.2.2.2 M' hM' ((le_sup_right.trans hD).trans hle)
  apply C.S.hz.2.2
  rw [← hMeq]
  exact ((le_sup_left.trans le_sup_left).trans hD).trans hle

theorem es_D5 : Subgroup.center ↥H ≠ ⊥ := by
  have := C.V_comm
  have S14 := Hyp147.set14 C.S.hyp C.h1222 C.h1332 C.h1334 C.hV2
  have hzT : z ∈ T := (C.hV2.2.1.trans S14.VT) (C.hV2.1 C.hz)
  have hzH : z ∈ H := C.TH hzT
  intro h
  have hc : (⟨z, hzH⟩ : ↥H) ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hg : (g : G) * z * (g : G)⁻¹ ∈ fsuV1 T V :=
      (Subgroup.mem_normalizer_iff.mp (C.S.hz.2.1 g.2) z).mp C.hz
    rcases S14.eq_of_mem_V1 C.hz C.hz1 hg with h1 | h1
    · exfalso
      apply C.hz1
      have := congrArg (fun u => (g : G)⁻¹ * u * g) h1
      simpa [mul_assoc] using this
    · show (g : G) * z = z * g
      calc (g : G) * z = (g * z * (g : G)⁻¹) * g := by group
        _ = z * g := by rw [h1]
  rw [h, Subgroup.mem_bot] at hc
  exact C.hz1 (congrArg Subtype.val hc)

end Ctx711

end CFSG.Quasithin.H13.L32A
