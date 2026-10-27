module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33g
public import CFSG.Quasithin.Background.HSecTransfer
public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.F918P4

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin S126 F126
open scoped commutatorElement

attribute [local instance] commGroupOfFact

section Omega

theorem omega4_of_autSub_eq_top {W : Type} [CommGroup W] {X : Subgroup (MulAut W)}
    {U : Subgroup W} (hU : U = ⊤) {n : ℕ} (h : Omega4PlusModule (autSub X U) n) :
    Omega4PlusModule X n := by
  subst hU
  obtain ⟨K, hF, hfin, hc, hR⟩ := h
  let r : ↥X ≃* ↥(autSub X (⊤ : Subgroup W)) :=
    (Subgroup.subgroupOfEquivOfLe (le_stabSub_top X)).symm.trans
      ((X.subgroupOf (stabSub ⊤)).equivMapOfInjective (resHom ⊤) resHom_top_injective)
  exact ⟨K, hF, hfin, hc, CFSG.Quasithin.H.FFModel.realizes_of_equiv
    (fun _ _ _ _ => Subgroup.mem_top _) (MulEquiv.refl _) r (fun _ _ => rfl) hR⟩

theorem omega4_autOn_congr {S : Type} [Group S] {Y E E' : Subgroup S}
    (hE : IsElemAbelian 2 E) (hE' : IsElemAbelian 2 E') (he : E = E') {n : ℕ}
    (h : @Omega4PlusModule _ (commGroupOfElemAbelian hE) (autOn Y E) n) :
    @Omega4PlusModule _ (commGroupOfElemAbelian hE') (autOn Y E') n := by
  subst he
  exact h

end Omega

section Orders

theorem eq_two_of_isPSL_of_dvd {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X)
    (hd : Nat.card X ∣ 60) : n = 2 := by
  obtain ⟨⟨-, hf, -, hne, -⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h1 : n = 1 := by omega
    subst h1
    exact hne rfl
  have hc := Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2) (by norm_num)
  rw [← Nat.card_congr e.toEquiv, hK, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one,
    Finset.Icc_self, Finset.prod_singleton] at hc
  have hle : Nat.card X ≤ 60 := Nat.le_of_dvd (by norm_num) hd
  by_contra hn
  have hn3 : 3 ≤ n := by omega
  have hq : 8 ≤ 2 ^ n :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hg : Nat.gcd 2 (2 ^ n - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd 2 (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h1 : 2 ^ n * ((2 ^ n) ^ 2 - 1) / 2 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) / Nat.gcd 2 (2 ^ n - 1) :=
    Nat.div_le_div_left hg hg0
  have h2 : 504 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    have h64 : 64 ≤ (2 ^ n) ^ 2 :=
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
    have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by omega
    calc 504 = 8 * 63 := by norm_num
      _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul hq h63
  omega

theorem false_of_isPSL_three_two_of_dvd {X : Type} [Group X] (h : IsPSL 3 2 1 X)
    (hd : Nat.card X ∣ 60) : False := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hc := Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3) (by norm_num)
  rw [← Nat.card_congr e.toEquiv, hK] at hc
  have h168 : Nat.card X = 168 := by
    rw [hc]
    decide
  rw [h168] at hd
  norm_num at hd

end Orders

section Module

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem card_autIH_dvd [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {X : Subgroup G} (hXH : X ≤ H) :
    Nat.card ↥(autIH V₁ I H X) ∣ Nat.card ↥(S126.star H X) := by
  have hker : CFSG.pCore 2 ↥H ≤
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)).ker := fun x hx =>
    MonoidHom.mem_ker.2 (h.actH_eq_one_of_mem_pCoreOf hIU
      (mkH_eq_one_iff.1 ((QuotientGroup.eq_one_iff x).2 hx)))
  have e : autIH V₁ I H X = (S126.star H X).map (QuotientGroup.lift (CFSG.pCore 2 ↥H)
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) hker) := by
    rw [autIH_eq_map h hXH, S126.star, Subgroup.map_map, QuotientGroup.lift_comp_mk']
  rw [e]
  exact Subgroup.card_map_dvd _ _

omit [Finite G] in
theorem le_of_tildeOf_le {X Y : Subgroup G} (hXN : X ≤ Subgroup.normalizer (V₁ : Set G))
    (hV₁Y : V₁ ≤ Y) (hle : tildeOf V₁ X ≤ tildeOf V₁ Y) : X ≤ Y := fun x hx =>
  (secMk_mem_secImg_iff hV₁Y).1 (hle (secMk_mem_secImg (x := ⟨x, hXN hx⟩) hx))

theorem tildeOf_conjClosure_ne_bot (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hI : IsIrrPlusTilde V₁ (conjClosure K T) I) : tildeOf V₁ (conjClosure I H) ≠ ⊥ := by
  intro h0
  have hIN := h.conjClosure_le_normalizer_V₁ hIU
  have hIV : I ≤ V₁ := le_of_tildeOf_le (V₁ := V₁) ((le_conjClosure I H).trans hIN) le_rfl (by
    rw [tildeOf_eq_bot_of_le (le_refl V₁), ← h0]
    exact secImg_mono (le_conjClosure I H))
  refine lt_irrefl I (lt_of_le_of_lt (fun x hx => ?_) hI.2.2.1)
  refine ⟨hx, Subgroup.le_normalizer (hIV hx), fun u hu => ?_⟩
  have hu' := Subgroup.mem_normalizer_iff.1 (h.H_le_normalizer_V₁ (h.K₀_le_H hu)) x⁻¹
  have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
  rw [e]
  exact V₁.mul_mem (hIV hx) (hu'.1 (V₁.inv_mem (hIV hx)))

theorem comm_comm_le_of_commV_le [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {Ka Kb : Subgroup G}
    (hKaH : Ka ≤ H) (hKbH : Kb ≤ H)
    (hs : commV (autIH V₁ I H Ka) ≤ fixV (autIH V₁ I H Kb)) :
    ⁅⁅conjClosure I H, Ka⁆, Kb⁆ ≤ V₁ := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hNI := le_normalizer_conjClosure I H
  have hsub : ⁅conjClosure I H, Ka⁆ ≤ ((commV (autIH V₁ I H Ka)).comap
      (tildeHom hIHN)).map (conjClosure I H).subtype := by
    rw [Subgroup.commutator_le]
    intro i hi k hk
    have hkH := hKaH hk
    have hki : k * i * k⁻¹ ∈ conjClosure I H := (Subgroup.mem_normalizer_iff.1 (hNI hkH) i).1 hi
    have hc : ⁅i, k⁆ ∈ conjClosure I H := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine (conjClosure I H).mul_mem hi ?_
      rw [← mul_assoc]
      exact (Subgroup.mem_normalizer_iff.1 (hNI hkH) i⁻¹).1 ((conjClosure I H).inv_mem hi)
    refine ⟨⟨⁅i, k⁆, hc⟩, ?_, rfl⟩
    have e : (⟨⁅i, k⁆, hc⟩ : ↥(conjClosure I H)) = ⟨i, hi⟩ * (⟨k * i * k⁻¹, hki⟩)⁻¹ := by
      apply Subtype.ext
      show ⁅i, k⁆ = i * (k * i * k⁻¹)⁻¹
      rw [commutatorElement_def]
      group
    have hk' : actH h.H_le_normalizer_V₁ hNI ⟨k, hkH⟩ (tildeHom hIHN ⟨i, hi⟩) =
        tildeHom hIHN ⟨k * i * k⁻¹, hki⟩ :=
      actH_modMk h.H_le_normalizer_V₁ hIHN hNI ⟨k, hkH⟩ hi
    have hmem : actH h.H_le_normalizer_V₁ hNI ⟨k, hkH⟩ ∈ autIH V₁ I H Ka := by
      rw [autIH_eq_map h hKaH]
      exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.2 hk, rfl⟩
    show tildeHom hIHN ⟨⁅i, k⁆, hc⟩ ∈ commV (autIH V₁ I H Ka)
    rw [e, map_mul, map_inv, ← hk']
    refine Subgroup.subset_closure ⟨_, hmem, (tildeHom hIHN ⟨i, hi⟩)⁻¹, ?_⟩
    rw [map_inv, inv_inv]
    exact mul_comm _ _
  rw [Subgroup.commutator_le]
  intro x hx b hb
  obtain ⟨⟨y, hyI⟩, hy, rfl⟩ := hsub hx
  have hbH := hKbH hb
  have hbmem : actH h.H_le_normalizer_V₁ hNI ⟨b, hbH⟩ ∈ autIH V₁ I H Kb := by
    rw [autIH_eq_map h hKbH]
    exact ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
  have hfix := h.commutator_mem_of_actH_fix hIU (x := ⟨b, hbH⟩) hyI (hs hy _ hbmem)
  have e : ⁅y, b⁆ = (b * y * b⁻¹ * y⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  show ⁅y, b⁆ ∈ V₁
  rw [e]
  exact V₁.inv_mem hfix

end Module

section Swap

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem comm_comm_swap (h918 : HypF918 T V L V₁ Vp H K) (h2 : Case2 T L H K) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) {IH : Subgroup G}
    (hIH : H ≤ Subgroup.normalizer (IH : Set G))
    (hle : ⁅⁅IH, conjSub t⁻¹ K⁆, K⁆ ≤ V₁) : ⁅⁅IH, K⁆, conjSub t⁻¹ K⁆ ≤ V₁ := by
  have h := h918.toHypF98.toHypF91
  have htH : t ∈ H := h918.T_le_H ht
  have e1 : IH.map (MulAut.conj t).toMonoidHom = IH := A38.map_conj_eq_iff.2 (hIH htH)
  have e2 : (conjSub t⁻¹ K).map (MulAut.conj t).toMonoidHom = K := by
    show (K.map (MulAut.conj t⁻¹).toMonoidHom).map (MulAut.conj t).toMonoidHom = K
    rw [Subgroup.map_map]
    convert Subgroup.map_id K
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have e3 : K.map (MulAut.conj t).toMonoidHom = conjSub t⁻¹ K :=
    conjSub_eq_conjSub_inv h918 h2 ht htK
  have e4 : V₁.map (MulAut.conj t).toMonoidHom = V₁ := A38.map_conj_eq_iff.2 (h.T_normalizes_V₁ ht)
  have key : (⁅⁅IH, conjSub t⁻¹ K⁆, K⁆).map (MulAut.conj t).toMonoidHom =
      ⁅⁅IH, K⁆, conjSub t⁻¹ K⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, e1, e2, e3]
  rw [← key, ← e4]
  exact Subgroup.map_mono hle

end Swap

end CFSG.Quasithin.H13.L1233
