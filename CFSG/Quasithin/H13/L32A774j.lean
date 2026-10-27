module

public import CFSG.Quasithin.H13.L32A774i
public import CFSG.Quasithin.H13.L32A774g
public import CFSG.Quasithin.H13.L32A774h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem exists_mem_v_kz_comm {c : G} (hc : c ∈ pCoreOf 2 L)
    (hcL : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ V) :
    ∃ a ∈ V, ∀ k ∈ kz T V, k * (a * c) = (a * c) * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hUe ha hb
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hKH : kz T V ≤ hz T V := oTwoUpper_le _
  have hKU : kz T V ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    hKH.trans C.hz_le_normalizer_fsuU
  have hcV : c ∈ Subgroup.centralizer (V : Set G) := by
    have h : c ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← C.pCoreOf_eq]
      exact hc
    exact (Subgroup.mem_inf.mp h).2
  have hcU : ∀ u ∈ fsuU T V, c * u = u * c := fun u hu =>
    C.comm_sL_eq_one hc hcL (le_conjClosure _ _ hu)
  have hcH : c ∈ hz T V := by
    show c ∈ Subgroup.centralizer (fsuV1 T V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp hcV w (Subgroup.mem_inf.mp hw).1
  have hcC : c ∈ pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) :=
    Subgroup.mem_inf.mpr ⟨C.mem_QH_of hcH hcU,
      Subgroup.mem_centralizer_iff.mpr fun u hu => (hcU u hu).symm⟩
  have hκU : ∀ k ∈ kz T V, k * c * k⁻¹ * c⁻¹ ∈ fsuU T V := fun k hk => by
    have h := (C.l71 G T L V C.hyp).1.2 (Subgroup.commutator_mem_commutator hcC hk)
    have := inv_mem h
    rwa [commutatorElement_def, show (c * k * c⁻¹ * k⁻¹)⁻¹ = k * c * k⁻¹ * c⁻¹ by group]
      at this
  have hQT : pCoreOf 2 (hz T V) ≤ T := pCoreOf_le_of_le C.hyp hTH
  have hQc : ∀ q ∈ pCoreOf 2 (hz T V), q * c * q⁻¹ * c⁻¹ ∈ fsuV1 T V := by
    intro q hq
    refine C.mem_fsuV1_of_conj_mem fun k hk => ?_
    have hq' : k * q * k⁻¹ ∈ pCoreOf 2 (hz T V) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (hz T V) (hKH hk)) q).mp hq
    have h1 := C.comm_T_mem_v_of_mem_Y hc hcL (hQT hq')
    have h2 := C.comm_mem_fsuV1 hq' (hκU k hk)
    rw [show k * (q * c * q⁻¹ * c⁻¹) * k⁻¹ =
        ((k * q * k⁻¹) * (k * c * k⁻¹ * c⁻¹) * (k * q * k⁻¹)⁻¹ * (k * c * k⁻¹ * c⁻¹)⁻¹) *
          ((k * c * k⁻¹ * c⁻¹) * ((k * q * k⁻¹) * c * (k * q * k⁻¹)⁻¹ * c⁻¹) *
            (k * c * k⁻¹ * c⁻¹)⁻¹) by group,
      hUc _ (hκU k hk) _ (v_le_fsuU h1), mul_inv_cancel_right]
    exact mul_mem (Subgroup.mem_inf.mp h2).1 h1
  have hR1H : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ hz T V :=
    (pCoreOf_le_of_le C.hyp le_sup_right).trans hTH
  have hSN : sL T L V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) := fun s hs =>
    le_normalizer_pCoreOf 2 (hz T V) (hR1H (C.sL_le_R1 hs))
  have hκX : ∀ t ∈ T ⊓ kz T V, t * c * t⁻¹ * c⁻¹ ∈ fsuV1 T V := by
    intro t ht
    have htR : t ∈ ((sL T L V ⊔ pCoreOf 2 (hz T V) : Subgroup G) : Set G) := by
      rw [SetLike.mem_coe, C.sup_eq_R1]
      exact C.T_inf_kz_le_R1 ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSN] at htR
    obtain ⟨s, hs, q, hq, rfl⟩ := htR
    have hsc : c * s = s * c := C.comm_sL_eq_one hc hcL hs
    have h1 := hQc q hq
    have hsv : s * (q * c * q⁻¹ * c⁻¹) = (q * c * q⁻¹ * c⁻¹) * s :=
      Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (C.v_le_centerOf (Subgroup.mem_inf.mp h1).1)).2 s hs
    have hcs : c * s⁻¹ * c⁻¹ = s⁻¹ := by
      calc c * s⁻¹ * c⁻¹ = (c * s * c⁻¹)⁻¹ := by group
        _ = s⁻¹ := by rw [hsc, mul_inv_cancel_right]
    rw [show s * q * c * (s * q)⁻¹ * c⁻¹ = (s * (q * c * q⁻¹ * c⁻¹)) * (c * s⁻¹ * c⁻¹) by group,
      hsv, hcs, mul_inv_cancel_right]
    exact h1
  obtain ⟨a, haU, ha⟩ := exists_coboundary_of_odd (K := kz T V) (X := T ⊓ kz T V)
    (A := fsuU T V) (B := fsuV1 T V) C.odd_relIndex_kz hUc
    (fun a ha => by rw [← pow_two]; exact F7.isElemAbelian_pow_eq_one hUe ha)
    (fun x hx => v_le_fsuU (Subgroup.mem_inf.mp hx).1) hKU
    (fun k hk => by
      rw [normalizer_eq_centralizer_of_card_two hV1]
      exact hKH hk)
    (fun k => k * c * k⁻¹ * c⁻¹) hκU
    (fun k hk k' hk' => by
      have h1 := hUc _ (hκU k hk) _
        ((Subgroup.mem_normalizer_iff.mp (hKU hk) _).mp (hκU k' hk'))
      calc k * k' * c * (k * k')⁻¹ * c⁻¹ =
          (k * (k' * c * k'⁻¹ * c⁻¹) * k⁻¹) * (k * c * k⁻¹ * c⁻¹) := by group
        _ = (k * c * k⁻¹ * c⁻¹) * (k * (k' * c * k'⁻¹ * c⁻¹) * k⁻¹) := h1.symm)
    hκX
  have hKc := C.kz_comm_of (w := a * c) fun k hk => by
    have hka : k * a * k⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKU hk) a).mp haU
    rw [show k * (a * c) * k⁻¹ * (a * c)⁻¹ = (k * a * k⁻¹) * (k * c * k⁻¹ * c⁻¹) * a⁻¹ by group,
      hUc _ hka _ (hκU k hk),
      show k * c * k⁻¹ * c⁻¹ * (k * a * k⁻¹) * a⁻¹ =
        (k * c * k⁻¹ * c⁻¹) * (a * (k * a * k⁻¹)⁻¹)⁻¹ by group]
    exact ha k hk
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  have haV : a ∈ V := by
    by_contra haV
    apply C.comm_not_mem C.u0_eq hxL1 hx3 hx1 haU haV
    have h1 := hKc x (l1_le_kz C.hyp C.hMod hxL1)
    have h2 := inv_mem (hcL x hxL)
    rw [show x * a * x⁻¹ * a⁻¹ = (x * (a * c)) * c⁻¹ * x⁻¹ * a⁻¹ by group, h1,
      show a * c * x * c⁻¹ * x⁻¹ * a⁻¹ = a * (x * c * x⁻¹ * c⁻¹)⁻¹ * a⁻¹ by group,
      hUc a haU _ (v_le_fsuU h2), mul_inv_cancel_right]
    exact h2
  exact ⟨a, haV, hKc⟩

theorem mem_v_of_mem_Y {c : G} (hc : c ∈ pCoreOf 2 L) (hcL : ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ V) :
    c ∈ V := by
  obtain ⟨-, hV8, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hPL : pCoreOf 2 L ≤ L := pCoreOf_le 2 L
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hVP : V ≤ pCoreOf 2 L := fun v hv => C.sL_le_P (v_le_sL hv)
  obtain ⟨a, haV, hKc⟩ := C.exists_mem_v_kz_comm hc hcL
  have hΩc : {x | x * c⁻¹ ∈ V}.ncard = 8 := by
    have he : {x | x * c⁻¹ ∈ V} = (fun v => v * c) '' (V : Set G) := by
      ext x
      constructor
      · intro hx
        exact ⟨x * c⁻¹, hx, by simp⟩
      · rintro ⟨v, hv, rfl⟩
        show v * c * c⁻¹ ∈ V
        rw [mul_inv_cancel_right]
        exact hv
    rw [he, Set.ncard_image_of_injective _ (mul_left_injective c), ← Nat.card_coe_set_eq]
    exact hV8
  have hΩL : ∀ l ∈ L, ∀ w ∈ {x | x * c⁻¹ ∈ V}, l * w * l⁻¹ ∈ {x | x * c⁻¹ ∈ V} := by
    intro l hl w hw
    show l * w * l⁻¹ * c⁻¹ ∈ V
    rw [show l * w * l⁻¹ * c⁻¹ = (l * (w * c⁻¹) * l⁻¹) * (l * c * l⁻¹ * c⁻¹) by group]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp hw) (hcL l hl)
  have hacΩ : a * c ∈ {x | x * c⁻¹ ∈ V} := by
    show a * c * c⁻¹ ∈ V
    rw [mul_inv_cancel_right]
    exact haV
  have hD8 : (Subgroup.centralizer ({a * c} : Set G)).relIndex L ≤ 8 := by
    show ((Subgroup.centralizer ({a * c} : Set G)).subgroupOf L).index ≤ 8
    rw [← ncard_conj_eq_index, ← hΩc]
    refine Set.ncard_le_ncard ?_
    rintro x ⟨l, hl, rfl⟩
    exact hΩL l hl _ hacΩ
  have hDL : L ⊓ Subgroup.centralizer ({a * c} : Set G) ≤ L := inf_le_left
  have hPD : pCoreOf 2 L ≤ L ⊓ Subgroup.centralizer ({a * c} : Set G) := fun p hp => by
    refine Subgroup.mem_inf.mpr ⟨hPL hp, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : p * c = c * p := C.comm_eq_one_of_mem_Y hp hc hcL
    have hpV : p ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      rw [← C.pCoreOf_eq]
      exact hp
    have h2 : p * a = a * p :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hpV).2 a haV).symm
    calc p * (a * c) = (p * a) * c := by group
      _ = (a * p) * c := by rw [h2]
      _ = a * (p * c) := by group
      _ = a * (c * p) := by rw [h1]
      _ = a * c * p := by group
  have hDn : L ⊓ Subgroup.centralizer ({a * c} : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 L : Set G) := hDL.trans (le_normalizer_pCoreOf 2 L)
  obtain ⟨x, y, hxL1, hx3, hxP, hyL1, hyP, hy2⟩ := C.exists_x3_transv
  have hL1D : ∀ g ∈ L₁Of L (fsuV1 T V), g ∈ L ⊓ Subgroup.centralizer ({a * c} : Set G) :=
    fun g hg => Subgroup.mem_inf.mpr ⟨(L32NSet14.Setting.L1_le.trans inf_le_left) hg,
      Subgroup.mem_centralizer_singleton_iff.mpr (hKc g (l1_le_kz C.hyp C.hMod hg))⟩
  have h3 := prime_dvd_relIndex hDn Nat.prime_three (hL1D x hxL1) hxP
    (by rw [hx3]; exact one_mem _)
  have h2 := prime_dvd_relIndex hDn Nat.prime_two (hL1D y hyL1) hyP hy2
  have hmul := Subgroup.relIndex_mul_relIndex (pCoreOf 2 L) _ L hPD hDL
  rw [C.relIndex_pCoreOf, Subgroup.inf_relIndex_left] at hmul
  have h17 := eq_one_or_seven hmul h3 h2 hD8 fun h4 => by
    have h := Subgroup.inf_relIndex_left L (Subgroup.centralizer ({a * c} : Set G))
    rw [C.eq_of_relIndex_le_four hDL (h ▸ h4), Subgroup.relIndex_self] at h
    exact h.symm
  obtain ⟨w, hwΩ, hwL⟩ := exists_fix_of_ncard L hΩc hΩL hacΩ h17
  have hwc : w * c⁻¹ ∈ V := hwΩ
  have hwP : w ∈ pCoreOf 2 L := by
    rw [show w = (w * c⁻¹) * c by group]
    exact mul_mem (hVP hwc) hc
  have hw1 := C.eq_one_of_mem_pCoreOf hwP fun l hl => by
    calc l * w = (l * w * l⁻¹) * l := by group
      _ = w * l := by rw [hwL l hl]
  rw [hw1, one_mul] at hwc
  simpa using inv_mem hwc

theorem pCoreOf_eq_sL : pCoreOf 2 L = sL T L V :=
  C.pCoreOf_eq_sL_of fun _ hq hqL => C.mem_v_of_mem_Y hq hqL

end Ctx73

end CFSG.Quasithin.H13.L32A
