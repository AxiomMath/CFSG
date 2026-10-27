module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModT
import all CFSG.Quasithin.Vol2.Ch12Sec2Ident

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem L_le_MV (h : Hyp1271 G T L V) : L ≤ h.hyp.MV :=
  le_inf Subgroup.le_normalizer (L_le_normalizer h)

omit [IsMulCommutative ↥V] in
theorem T_le_MV (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) : T ≤ h.hyp.MV :=
  le_inf h.hyp.normalizes (T_le_normalizer h1222 h)

omit [IsMulCommutative ↥V] in
theorem MVbar_le_normalizer (h : Hyp1271 G T L V) :
    h.hyp.MVbar ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
  autOn_le_normalizer_autOn inf_le_left inf_le_right (L_le_normalizer h)

theorem gm6_isLin {B : B6} (hB : B ∈ gm6) : IsLin B := by
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  have hall := cert_gmList_mem
  have hAv := (hall A hA).1
  intro v hv
  rw [toB6_app A (wV_lt v hv), toB6_app A hv, Mc.app_wV hAv hv]

theorem MVbar_code
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {m : MulAut ↥V}
    (hm : m ∈ h.hyp.MVbar) :
    C.cB m ∈ nm6 ∧ (∀ c ∈ oVecL, (C.cB m).app c ∈ oVecL) ∧
      (m ∈ autOn L V ↔ IsLin (C.cB m)) ∧ (m ∉ autOn L V → IsSemi (C.cB m)) := by
  have hN := MVbar_le_normalizer h hm
  obtain ⟨hnm, hO, hls⟩ := normalizer_code hC fun a => Subgroup.mem_normalizer_iff.1 hN a
  have hlin : m ∈ autOn L V ↔ IsLin (C.cB m) := by
    constructor
    · intro hmL
      exact gm6_isLin ((hC.1 m).1 hmL)
    · intro hl
      exact (hC.1 m).2 (mem_gm6_of_linear (C.cB_valid m) hl
        (fun u hu u' hu' e => C.cB_app_injective m hu hu' e) hO)
  refine ⟨hnm, hO, hlin, fun hmL => ?_⟩
  rcases hls with hl | hs
  · exact absurd (hlin.2 hl) hmL
  · exact hs

theorem nm6_length : nm6.length = 2160 := by
  have hlen := cert_gmList_length
  simp [nm6, gm6, hlen]

theorem card_MVbar_le
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    Nat.card h.hyp.MVbar ≤ 2160 := by
  classical
  have hinj : Function.Injective (fun m : h.hyp.MVbar =>
      (⟨C.cB m, (MVbar_code h hC m.2).1⟩ : {B : B6 // B ∈ nm6})) :=
    fun a b hab => Subtype.ext (C.cB_injective (congrArg Subtype.val hab))
  have hle := Nat.card_le_card_of_injective _ hinj
  have e2 : {B : B6 // B ∈ nm6} ≃ ↥nm6.toFinset := Equiv.subtypeEquivRight fun B => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard] at hle
  calc Nat.card h.hyp.MVbar ≤ nm6.toFinset.card := hle
    _ ≤ nm6.length := List.toFinset_card_le _
    _ = 2160 := nm6_length

theorem card_MVbar_of_ne
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    (hne : h.hyp.MVbar ≠ autOn L V) : Nat.card h.hyp.MVbar = 2160 := by
  have hle : autOn L V ≤ h.hyp.MVbar := A4.autOn_mono (L_le_MV h)
  have hlt : autOn L V < h.hyp.MVbar := lt_of_le_of_ne hle (Ne.symm hne)
  have hcard := card_autOn_L h.hatA6 (L_le_normalizer h)
  have hi := ((autOn L V).subgroupOf h.hyp.MVbar).card_mul_index
  have hcL : Nat.card ((autOn L V).subgroupOf h.hyp.MVbar) = 1080 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hi2 : ((autOn L V).subgroupOf h.hyp.MVbar).index ≠ 1 := by
    intro e
    rw [Subgroup.index_eq_one] at e
    apply hlt.ne'
    apply le_antisymm _ hle
    intro m hm
    have : (⟨m, hm⟩ : h.hyp.MVbar) ∈ (autOn L V).subgroupOf h.hyp.MVbar := by rw [e]; trivial
    exact this
  have hi0 : ((autOn L V).subgroupOf h.hyp.MVbar).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have := card_MVbar_le h hC
  rw [hcL] at hi
  omega

omit [IsMulCommutative ↥V] in
theorem odd_index_T (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    ¬ 2 ∣ ((autOn T V).subgroupOf h.hyp.MVbar).index := by
  have hMV : h.hyp.MV ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  have hTM := T_le_MV h1222 h
  set f := autOnSurj hMV with hf
  have hmap : (T.subgroupOf h.hyp.MV).map f = (autOn T V).subgroupOf h.hyp.MVbar := by
    ext ⟨a, ha⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨l, hl, hla⟩
      have ha' : a = A4.actionOn V h.hyp.MV hMV l := (congrArg Subtype.val hla).symm
      rw [ha']
      exact (A4.mem_autOn_iff (le_trans hTM hMV)).2 ⟨⟨l, hl⟩, rfl⟩
    · intro h'
      obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff (le_trans hTM hMV)).1 h'
      exact ⟨⟨x, hTM x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  have hdvd := Subgroup.index_map_dvd (T.subgroupOf h.hyp.MV) (autOnSurj_surjective hMV)
  rw [hmap] at hdvd
  intro h2
  apply h.hyp.sylow.2
  have e := Subgroup.relIndex_mul_index hTM
  rw [← e]
  exact Dvd.dvd.mul_right (dvd_trans h2 hdvd) _

theorem exists_T_not_L
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    (hne : h.hyp.MVbar ≠ autOn L V) : ∃ τ ∈ autOn T V, τ ∉ autOn L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  have hc := card_MVbar_of_ne h hC hne
  have hle : autOn T V ≤ h.hyp.MVbar := A4.autOn_mono (T_le_MV h1222 h)
  have hp : IsPGroup 2 (autOn T V) := by
    have h2 : IsPGroup 2 ((T).subgroupOf (Subgroup.normalizer (V : Set G))) :=
      h.hyp.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe (T_le_normalizer h1222 h)).symm
    exact h2.map _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have hi := ((autOn T V).subgroupOf h.hyp.MVbar).card_mul_index
  rw [show Nat.card ((autOn T V).subgroupOf h.hyp.MVbar) = Nat.card (autOn T V) from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hk, hc] at hi
  have hodd := odd_index_T h1222 h
  have hk4 : 4 ≤ k := by
    by_contra hk4
    interval_cases k <;> omega
  have hTL : autOn T V ≤ autOn L V := fun τ hτ => hno τ hτ
  have hd := Subgroup.card_dvd_of_le hTL
  rw [hk, card_autOn_L h.hatA6 (L_le_normalizer h)] at hd
  have : 2 ^ 4 ∣ 1080 := dvd_trans (pow_dvd_pow 2 hk4) hd
  norm_num at this

end CFSG.Quasithin.H13.S127.Mod

end
