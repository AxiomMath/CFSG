module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicNoncentralONanModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicNoncentral17Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CentralThreeLift
public import CFSG.Sporadic.ONOddCore.OuterQuot
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ON

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore
open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def sncon_Tb :
    Subgroup RM :=
  (onT.subgroupOf onM).map piR

@[expose] def sncon_Cb :
    Subgroup RM :=
  sncon_Tb ⊓ XR

@[expose] def sncon_Pb :
    Subgroup RM :=
  Subgroup.normalizer (sncon_Cb : Set RM)

@[expose] def sncon_P :
    Subgroup Pv :=
  ((sncon_Pb.comap piR).map onM.subtype).subgroupOf Pv

private theorem sncon_T_le_M :
    onT ≤ onM := by
  rw [onM_eq_centralizer_z]
  intro t ht
  refine ⟨onT_le ht, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hz : onz ∈ CFSG.centerIn onT := by
    rw [onT_centerIn]
    exact Subgroup.mem_zpowers _
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 t ht)

private theorem sncon_card_Tb :
    128 ≤ Nat.card sncon_Tb ∧ IsPGroup 2 sncon_Tb := by
  have hT : Nat.card (onT.subgroupOf onM) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sncon_T_le_M).toEquiv, card_onT]
  have hp : IsPGroup 2 (onT.subgroupOf onM) := IsPGroup.of_card (n := 9) (by rw [hT]; norm_num)
  refine ⟨?_, hp.map piR⟩
  have hr : (piR.comp (onT.subgroupOf onM).subtype).range = sncon_Tb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hk : Nat.card (piR.comp (onT.subgroupOf onM).subtype).ker ≤ 4 := by
    have hle : (piR.comp (onT.subgroupOf onM).subtype).ker.map (onT.subgroupOf onM).subtype ≤
        piR.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), ker_piR,
      card_onQ_subgroupOf_M] at h
  have h := card_range_mul_ker (piR.comp (onT.subgroupOf onM).subtype)
  rw [hT, hr] at h
  have h2 : 512 ≤ Nat.card sncon_Tb * 4 :=
    calc 512 = _ := h
      _ ≤ _ := Nat.mul_le_mul_left _ hk
  omega

private theorem sncon_card_Cb :
    Nat.card sncon_Cb = 64 := by
  obtain ⟨h128, hp⟩ := sncon_card_Tb
  have hXR : Nat.card XR = 20160 := by
    rw [← card_onX]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe onX_le_RM).toEquiv
  have hn : sncon_Tb ≤ Subgroup.normalizer (XR : Set RM) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    exact le_top
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hn
  rw [hXR] at h
  have hsup : Nat.card ↥(sncon_Tb ⊔ XR) ≤ 40320 := by
    rw [← card_RM]
    exact Subgroup.card_le_card_group _
  have hlow : 2580480 ≤ 40320 * Nat.card sncon_Cb :=
    calc 2580480 = 128 * 20160 := by norm_num
      _ ≤ Nat.card sncon_Tb * 20160 := Nat.mul_le_mul_right _ h128
      _ = Nat.card ↥(sncon_Tb ⊔ XR) * Nat.card sncon_Cb := h.symm
      _ ≤ 40320 * Nat.card sncon_Cb := Nat.mul_le_mul_right _ hsup
  obtain ⟨k, hk⟩ : ∃ k, Nat.card sncon_Cb = 2 ^ k :=
    (hp.to_le (inf_le_left : sncon_Cb ≤ sncon_Tb)).exists_card_eq
  have hdvd : 2 ^ k ∣ 20160 := by
    rw [← hk, ← hXR]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hk6 : k ≤ 6 := by
    by_contra hk7
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 7 ≤ k)).trans hdvd) (by norm_num)
  have hup : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hk6
  rw [hk] at hlow ⊢
  omega

private theorem sncon_Tb_le_Pb :
    sncon_Tb ≤ sncon_Pb := by
  intro t ht
  rw [sncon_Pb, Subgroup.mem_normalizer_iff]
  intro h
  rw [sncon_Cb, Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_mem (mul_mem ht h1) (inv_mem ht), XR_normal.conj_mem h h2 t⟩
  · rintro ⟨h1, h2⟩
    have e : h = t⁻¹ * (t * h * t⁻¹) * t := by group
    rw [e]
    refine ⟨mul_mem (mul_mem (inv_mem ht) h1) ht, ?_⟩
    have := XR_normal.conj_mem _ h2 t⁻¹
    rwa [inv_inv] at this

theorem sncon_card_Pb :
    Nat.card sncon_Pb = 384 := by
  obtain ⟨h128, hp⟩ := sncon_card_Tb
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hk7 : 7 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 128 ∣ Nat.card sncon_Pb :=
    ((Nat.pow_dvd_pow 2 hk7).trans (hk ▸ Subgroup.card_dvd_of_le sncon_Tb_le_Pb))
  exact sncon_card_normalizer inf_le_right sncon_card_Cb hdvd

theorem sncon_card_P :
    Nat.card sncon_P = 3 * Nat.card (onT.subgroupOf Pv) := by
  have hle : (sncon_Pb.comap piR).map onM.subtype ≤ Pv :=
    (Subgroup.map_subtype_le _).trans onM_le
  rw [sncon_P, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Subgroup.card_map_of_injective onM.subtype_injective,
    CFSG.Quasithin.RonanE43.card_comap_of_surjective _ piR_surjective, ker_piR,
    card_onQ_subgroupOf_M, sncon_card_Pb, card_onT_subgroupOf]

theorem sncon_U_le_P :
    onT.subgroupOf Pv ≤ sncon_P := by
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  rw [sncon_P, Subgroup.mem_subgroupOf]
  refine ⟨⟨x, sncon_T_le_M hx⟩, ?_, rfl⟩
  exact sncon_Tb_le_Pb ⟨⟨x, sncon_T_le_M hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

private theorem sncon_fix_z
    (α : MulAut Pv)
    (hU : ∀ x : Pv, ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onT ↔ (x : Equiv.Perm (Fin N)) ∈ onT) :
    α zP = zP := by
  have hzc : ∀ t ∈ onT, t * onz = onz * t := fun t ht => by
    have hz : onz ∈ CFSG.centerIn onT := by
      rw [onT_centerIn]
      exact Subgroup.mem_zpowers _
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2 t ht
  have hmem : ((α zP : Pv) : Equiv.Perm (Fin N)) ∈ CFSG.centerIn onT := by
    refine Subgroup.mem_inf.2 ⟨(hU zP).2 onz_mem_T, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro t ht
    obtain ⟨x, hx⟩ := α.surjective ⟨t, onT_le ht⟩
    have hxT : (x : Equiv.Perm (Fin N)) ∈ onT := by
      rw [← hU x, hx]
      exact ht
    have hc : x * zP = zP * x := Subtype.ext (hzc _ hxT)
    have := congrArg (fun y : Pv => (y : Equiv.Perm (Fin N))) (congrArg α hc)
    simp only [map_mul, hx, Subgroup.coe_mul] at this
    exact this
  rw [onT_centerIn, mem_zpowers_iff_mem_range_orderOf, orderOf_onz] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hkz⟩ := hmem
  interval_cases k
  · exfalso
    have h1 : α zP = 1 := Subtype.ext (by rw [← hkz, pow_zero]; rfl)
    rw [map_eq_one_iff _ α.injective] at h1
    exact onz_ne_one (congrArg Subtype.val h1)
  · exact Subtype.ext (by rw [← hkz, pow_one]; rfl)

theorem sncon_P_inv
    (α : MulAut Pv)
    (hα : (onT.subgroupOf Pv).map α.toMonoidHom = onT.subgroupOf Pv) :
    sncon_P.map α.toMonoidHom = sncon_P := by
  have hU : ∀ x : Pv, ((α x : Pv) : Equiv.Perm (Fin N)) ∈ onT ↔ (x : Equiv.Perm (Fin N)) ∈ onT :=
    fun x => by
      rw [← Subgroup.mem_subgroupOf, ← Subgroup.mem_subgroupOf]
      conv_lhs => rw [← hα]
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hz := sncon_fix_z α hU
  have hT' : (onT.subgroupOf onM).map (resM α hz).toMonoidHom = onT.subgroupOf onM := by
    ext m
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    conv_rhs => rw [← MulEquiv.apply_symm_apply (resM α hz) m, resM_val, hU]
    rfl
  have hcomp : (descendAut (resM α hz)).toMonoidHom.comp piR = piR.comp (resM α hz).toMonoidHom :=
    MonoidHom.ext fun m => descendAut_piR (resM α hz) m
  have hTb : sncon_Tb.map (descendAut (resM α hz)).toMonoidHom = sncon_Tb := by
    rw [sncon_Tb, Subgroup.map_map, hcomp, ← Subgroup.map_map, hT']
  have hXR : XR.map (descendAut (resM α hz)).toMonoidHom = XR :=
    Subgroup.characteristic_iff_map_eq.1 XR_characteristic _
  have hCb : sncon_Cb.map (descendAut (resM α hz)).toMonoidHom = sncon_Cb := by
    rw [sncon_Cb, Subgroup.map_inf_eq _ _ _ (descendAut (resM α hz)).injective, hTb, hXR]
  have hPb : sncon_Pb.map (descendAut (resM α hz)).toMonoidHom = sncon_Pb := by
    rw [sncon_Pb, Subgroup.map_equiv_normalizer_eq, hCb]
  have hPM : ∀ m : onM, resM α hz m ∈ sncon_Pb.comap piR ↔ m ∈ sncon_Pb.comap piR := fun m => by
    rw [Subgroup.mem_comap, Subgroup.mem_comap, ← descendAut_piR]
    conv_lhs => rw [← hPb]
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hiff : ∀ x : Pv, α x ∈ sncon_P ↔ x ∈ sncon_P := fun x => by
    simp only [sncon_P, Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_subtype]
    constructor
    · rintro ⟨m', hm', hm'x⟩
      have hxM : (x : Equiv.Perm (Fin N)) ∈ onM := (mem_M_map hz x).1 (hm'x ▸ m'.2)
      refine ⟨⟨x, hxM⟩, (hPM _).1 ?_, rfl⟩
      have : resM α hz ⟨x, hxM⟩ = m' := Subtype.ext (by rw [resM_val, hm'x]; rfl)
      rw [this]
      exact hm'
    · rintro ⟨m, hm, hmx⟩
      have hx : toP m = x := Subtype.ext hmx
      exact ⟨resM α hz m, (hPM m).2 hm, by rw [resM_val, hx]⟩
  ext y
  rw [Subgroup.mem_map_equiv, ← hiff, MulEquiv.apply_symm_apply]

theorem sncon_overgroup
    {Y : Type} [Group Y] [Finite Y]
    {K S : Subgroup Y} [K.Normal] (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (e : ↥K ≃* ↥Pv) :
    ∃ H : Subgroup Y, S ≤ H ∧ Nat.card H = 3 * Nat.card S := by
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (onT.subgroupOf Pv) ⊤ :=
    ⟨le_top, onT_isPGroup, by
      rw [show ((onT.subgroupOf Pv).subgroupOf ⊤).index = (onT.subgroupOf Pv).index from
        Subgroup.relIndex_top_right _]
      exact onT_not_dvd_index⟩
  exact exists_overgroup_of_invariant hU sncon_U_le_P 3 sncon_card_P sncon_P_inv e hS

private theorem sncon_card_three {G : Type} [Group G] {E : Subgroup G} (hE : Nat.card E = 3) :
    E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ ∀ x ∈ E, x ^ 3 = 1 := by
  refine ⟨fun h => by rw [h, Subgroup.card_bot] at hE; omega,
    IsPGroup.of_card (n := 1) (by rw [hE, pow_one]), fun x hx => ?_⟩
  have hdvd : orderOf x ∣ 3 := by simpa [hE] using Subgroup.orderOf_dvd_natCard E hx
  exact orderOf_dvd_iff_pow_eq_one.mp hdvd

private theorem sncon_of_equiv
    {Y : Type} [Group Y] [Finite Y]
    {K S : Subgroup Y} (hKY : KYForm Y K S) (e : ↥K ≃* ↥Pv) (hZ : Subgroup.center ↥K = ⊥) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S := by
  have : K.Normal := hKY.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hKY.2.2.2.2.2
  obtain ⟨H, hSH, hHc⟩ := sncon_overgroup hS e
  obtain ⟨E, -, hEK, hEc, -, -, hEP⟩ := exists_permutes_of_overgroup hKY.1 hKY.2.2.2.2.1
    hS.2.1 hSH (p := 3) (n := 1) (by norm_num) (by rw [hHc, pow_one])
  obtain ⟨hE1, hE3, hEe⟩ := sncon_card_three (by rw [hEc, pow_one])
  refine ⟨E, hEK, hE1, hE3, hEe, fun h => hE1 ?_, hEP⟩
  rw [hZ, Subgroup.map_bot] at h
  exact le_bot_iff.1 h

open CFSG.Quasithin.RonanE43 in
private theorem sncon_of_center_three
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} (hKY : KYForm Y K S)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.Blueprint.NativeSporadic.ON)
    (hZ3 : Nat.card (Subgroup.center ↥K) = 3) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S := by
  classical
  have hK : K.Normal := hKY.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKY.2.1.1
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := hKY.2.2.2.2.2
  set Z : Subgroup Y := (Subgroup.center ↥K).map K.subtype with hZdef
  have hZn : Z.Normal := by
    have : (Subgroup.center ↥K).Characteristic := Subgroup.centerCharacteristic
    exact ConjAct.normal_of_characteristic_of_normal (H := K) (K := Subgroup.center ↥K)
  have hZK : Z ≤ K := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hZc : ∀ z ∈ Z, ∀ k ∈ K, z * k = k * z := by
    rintro _ ⟨c, hc, rfl⟩ k hk
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨k, hk⟩)
    simpa using h1.symm
  have hZcard : Nat.card Z = 3 := (Subgroup.card_subtype K (Subgroup.center ↥K)).trans hZ3
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf (S.map (QuotientGroup.mk' Z)) ⊤ :=
    ⟨le_top, hS.2.1.map _, by
      rw [show ((S.map (QuotientGroup.mk' Z)).subgroupOf ⊤).index =
        (S.map (QuotientGroup.mk' Z)).index from Subgroup.relIndex_top_right _]
      exact isSylowIn_map _ hπ hS⟩
  have : (K.map (QuotientGroup.mk' Z)).Normal := hK.map _ hπ
  let ψ : ↥K →* Y ⧸ Z := (QuotientGroup.mk' Z).comp K.subtype
  have hψker : ψ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' Z (x : Y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hψrange : ψ.range = K.map (QuotientGroup.mk' Z) := by
    show ((QuotientGroup.mk' Z).comp K.subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eQ : (↥K ⧸ Subgroup.center ↥K) ≃* ↥ψ.range :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans (QuotientGroup.quotientKerEquivRange ψ)
  let e₀ : ↥(K.map (QuotientGroup.mk' Z)) ≃* ↥Pv :=
    (MulEquiv.subgroupCongr hψrange.symm).trans (eQ.symm.trans (e.trans onEquivPv))
  obtain ⟨Hb, hSHb, hHbc⟩ := sncon_overgroup hS' e₀
  have hZS : Z ⊓ S = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
    rw [hZcard, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hSc : Nat.card (S.map (QuotientGroup.mk' Z)) = Nat.card S := by
    refine card_map_of_injOn _ fun x hx h1 => ?_
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp h1
    have : x ∈ Z ⊓ S := ⟨hxZ, hx⟩
    rw [hZS] at this
    exact Subgroup.mem_bot.mp this
  have eK : ↥(Subgroup.center ↥K) ≃* Multiplicative (ZMod 3) := mulEquivOfPrimeCardEq hZ3
    (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  obtain ⟨f⟩ := CFSG.RankThree.Native.ONTriple.nonempty_equiv_FHat (Subgroup.center ↥K) eK e
  have h9 : ∀ x ∈ K, x ^ 3 ∈ Z → x ^ 3 = 1 := by
    intro x hx hx3
    have hz3 : (x ^ 3) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Z) (x := ⟨x ^ 3, hx3⟩)
      rw [hZcard] at h
      exact congrArg Subtype.val h
    have hk : (⟨x, hx⟩ : ↥K) ^ 3 ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, hz3]
      rfl)
    have := CFSG.RankThree.PartTwo.Sec13.ON134.pow_three_eq_one
      (f.trans CFSG.RankThree.Native.ONTriple.modelEquiv) hk
    simpa using congrArg Subtype.val this
  obtain ⟨X, hXK, -, hXc, hXP, hXZ, -⟩ :=
    exists_permutes_three_of_lift hKY.2.2.2.2.1 hS hZK hZcard hZc h9 hSHb (by rw [hHbc, hSc])
  obtain ⟨hX1, hX3, hXe⟩ := sncon_card_three hXc
  refine ⟨X, hXK, hX1, hX3, hXe, fun h => hX1 ?_, hXP⟩
  rw [← hXZ]
  exact (inf_eq_left.2 h).symm

theorem sporadicNoncentral_ONan :
    SporadicNoncentralThreeAt .ONan := by
  intro Y _ _ K S hKY hK
  obtain ⟨e₀⟩ := hK
  have e : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.Blueprint.NativeSporadic.ON := e₀
  have hq : CFSG.IsQuasisimple ↥K := ⟨⟨hKY.2.1.1⟩, hKY.2.1.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hKY.2.1⟩
  have hdvd := CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.on_center_dvd ↥K hq e
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · have hZ : Subgroup.center ↥K = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    exact sncon_of_equiv hKY (((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).symm.trans (e.trans onEquivPv)) hZ
  · exact sncon_of_center_three hKY e h3

theorem k_SporadicNoncentralThree_holds :
    K_SporadicNoncentralThree :=
  k_SporadicNoncentralThree_of_ONan sporadicNoncentral_ONan

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
