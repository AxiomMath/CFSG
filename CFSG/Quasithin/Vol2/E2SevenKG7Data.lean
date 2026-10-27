module

public import CFSG.Quasithin.Vol2.E2SevenSp4
public import CFSG.Quasithin.Vol2.E2SevenKGAS
public import CFSG.Quasithin.Vol2.Ch3E213MSp4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp antiUnipotent antiUnipotentCenter minorAut antiSpEquiv)
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)
open scoped commutatorElement

namespace E2

open Ch3E213M

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_isSolvable_of_perfect_ne_bot {Q : Type} [Group Q] {L : Subgroup Q}
    (hL : ⁅L, L⁆ = L) (hne : L ≠ ⊥) : ¬ Group.IsSolvable Q := by
  rintro ⟨m, hm⟩
  apply hne
  have h : ∀ i, L ≤ derivedSeries Q i := by
    intro i
    induction i with
    | zero => exact le_top
    | succ i ih =>
      rw [derivedSeries_succ, ← hL]
      exact Subgroup.commutator_mono ih ih
  exact le_bot_iff.mp (hm ▸ h m)

theorem qrcHyp_of_kerIn_eq_bot {X T M V : Subgroup G} (hyp : Hyp28 X T M V) :
    ∃ T' : Sylow 2 X, (T' : Subgroup X) = T.subgroupOf X ∧
      ¬ (T' : Subgroup X).Normal ∧ (T' : Subgroup X) ≤ M.subgroupOf X ∧ M.subgroupOf X < ⊤ ∧
      (∀ Y : Subgroup X, (T' : Subgroup X) ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf X) ∧
      IsElementaryAbelian 2 (V.subgroupOf X) ∧ V.subgroupOf X ≤ T' ∧
      (T' : Subgroup X) ≤ Subgroup.normalizer (V.subgroupOf X : Set X) ∧
      V.subgroupOf X ≤ inSubgroup (CFSG.pCore 2) (M.subgroupOf X) := by
  have hmp := hyp.minParabolic
  have hTH : T ≤ X := hmp.isSylow.1
  have hMH : M ≤ X := hmp.maximal.1.le
  have hVH : V ≤ X := hyp.le_H
  obtain ⟨T', hT'⟩ := exists_sylow_subgroupOf hmp.isSylow
  refine ⟨T', hT', fun hn => hmp.not_normal ?_, hT' ▸ Subgroup.comap_mono hmp.le, ?_,
    fun Y hTY hY => ?_, isElementaryAbelian_subgroupOf hyp.elem,
    hT' ▸ Subgroup.comap_mono hyp.le_T, ?_, fun v hv => ?_⟩
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have key : ∀ (h : X) (z : G), z ∈ T → (h : G) * z * (h : G)⁻¹ ∈ T := fun h z hz => by
      have h1 : (⟨z, hTH hz⟩ : X) ∈ (T' : Subgroup X) := by rw [hT']; exact hz
      have h2 := hn.conj_mem _ h1 h
      rw [hT'] at h2
      exact h2
    refine ⟨key ⟨x, hx⟩ y, fun hy => ?_⟩
    have := key ⟨x, hx⟩⁻¹ _ hy
    simpa [mul_assoc] using this
  · refine lt_of_le_of_ne le_top fun htop => hmp.maximal.1.not_ge fun x hx => ?_
    have : (⟨x, hx⟩ : X) ∈ M.subgroupOf X := htop ▸ Subgroup.mem_top _
    exact this
  · have h1 : Y.map X.subtype ≤ M := by
      refine hmp.le_of_lt ?_ ?_
      · intro t ht
        exact ⟨⟨t, hTH ht⟩, hTY (by rw [hT']; exact ht), rfl⟩
      · refine lt_of_le_of_ne (Subgroup.map_subtype_le Y) fun heq => hY.ne ?_
        apply Subgroup.map_injective X.subtype_injective
        rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    intro y hy
    exact h1 ⟨y, hy, rfl⟩
  · rw [hT']
    intro t ht
    have h1 : (t : G) ∈ X ⊓ Subgroup.normalizer (V : Set G) := ⟨t.2, hyp.normal_T ht⟩
    rw [← CFSG.QuasithinUnique.map_subtype_normalizer hVH] at h1
    obtain ⟨t', ht', htt'⟩ := h1
    rwa [← X.subtype_injective htt']
  · have h1 : (v : G) ∈ pCoreOf 2 M := hyp.le_pCoreOf hv
    rw [← Subgroup.map_subgroupOf_eq_of_le hMH, ← map_subtype_inSubgroup_pCore] at h1
    obtain ⟨w, hw, hwv⟩ := h1
    rwa [← X.subtype_injective hwv]

theorem exists_sp4Data_of_kg7 {X T M V K : Subgroup G} (h : Hyp28 X T M V)
    (hker : kerIn M X = ⊥) (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set G))
    (hC : X ⊓ Subgroup.centralizer (K : Set G) = ⊥) (hKT : K ⊔ T = X) {n : ℕ} (hn : 2 ≤ n)
    (hSp : IsSp4Prime n ↥K) (hV4 : 4 ≤ Nat.card V) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2), Nat.card k = 2 ^ n ∧
      Nonempty (Sp4Data X T M V K k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsK : IsSimpleGroup ↥K := isSimpleGroup_of_isSp4Prime hSp
  have hSp' : IsPSp4 2 n ↥K := by
    have h' := hSp
    unfold IsSp4Prime at h'
    rwa [ite_eq_right (show ¬ n = 1 by omega)] at h'
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hSp'
  have : CharP k 2 := by
    have : Fintype k := Fintype.ofFinite k
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have hmp := h.minParabolic
  have hMX : M ≤ X := hmp.maximal.1.le
  have hVX : V ≤ X := h.le_H
  have hTX : T ≤ X := hmp.isSylow.1
  obtain ⟨T', hT', hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM'⟩ := qrcHyp_of_kerIn_eq_bot h
  have := hel
  have hO2 : pCoreOf 2 X = ⊥ := by
    rw [eq_bot_iff, ← hker]
    exact hmp.pCoreOf_le_kerIn
  have hVQ' : 4 ≤ (V.subgroupOf X ⊓ CFSG.pCore 2 X).relIndex (V.subgroupOf X) := by
    rw [relIndex_subgroupOf_inf_pCore hVX, hO2, inf_bot_eq, Subgroup.relIndex_bot_left]
    exact hV4
  have hKn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  have hsL : IsSimpleGroup ↥(K.subgroupOf X) := (Subgroup.subgroupOfEquivOfLe hKX).isSimpleGroup
  have hperf : ⁅K.subgroupOf X, K.subgroupOf X⁆ = K.subgroupOf X := by
    obtain ⟨a, b, hab⟩ := (asHyp_subgroupOf hmp hKX hXN hC hKT hsK).nonab
    have htop : ⁅(⊤ : Subgroup ↥(K.subgroupOf X)), (⊤ : Subgroup ↥(K.subgroupOf X))⁆ =
        (⊤ : Subgroup ↥(K.subgroupOf X)) := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (⁅(⊤ : Subgroup ↥(K.subgroupOf X)), (⊤ : Subgroup ↥(K.subgroupOf X))⁆) with hb | ht
      · exfalso
        apply hab
        have hc : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup ↥(K.subgroupOf X)), (⊤ : Subgroup ↥(K.subgroupOf X))⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      · exact ht
    have := congrArg (Subgroup.map (K.subgroupOf X).subtype) htop
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have hT2 : IsPGroup 2 (T.subgroupOf X) := hmp.isSylow.2.1.comap_subtype
  have hK₀ : kZero X M = barIn M X K := by
    refine map_oddResidualPreimage_eq (pCore_le_kerIn_subgroupOf h) hperf
      (hKn.map _ (QuotientGroup.mk'_surjective _)) fun x => ?_
    obtain ⟨j, hj⟩ := exists_two_pow_mem_of_sup_eq_top hT2 (subgroupOf_sup_eq_top hKT.symm) x
    exact ⟨j, by rw [← map_pow]; exact Subgroup.mem_map_of_mem _ hj⟩
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMX K
  let θ₀ : ↥(kZero X M) ≃* antiSp k :=
    (MulEquiv.subgroupCongr hK₀).trans ((φ.trans (equivStarOfKerInEqBot hker hKX).symm).trans
      (e.trans ((CFSG.LieType.SteinbergBR.EvenSp.projEquiv (K := k) (n := 2) (by norm_num)).trans
        (antiSpEquiv k).symm)))
  have hQ := sp4Confinement T' hTn hTM' hMH' hmax' hVT' hTV' hVQ' hn hk θ₀
  obtain ⟨-, ι, hιinj, hιapp, -, hsup, θ', -, hsyl, ⟨hVK, hVZ⟩, ⟨-, -, hcard⟩,
    ⟨s, hs, g, j, hj, -, hact⟩, hswap, hnl, hns, -⟩ := hQ
  have hns' : ¬ Group.IsSolvable ↥X := by
    refine not_isSolvable_of_perfect_ne_bot hperf fun hb => ?_
    obtain ⟨a, ha⟩ := exists_ne (1 : ↥(K.subgroupOf X))
    have : a ∈ (⊥ : Subgroup ↥X).subgroupOf (K.subgroupOf X) := by
      rw [Subgroup.mem_subgroupOf, ← hb]
      exact a.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
    exact ha (Subtype.ext this)
  obtain ⟨-, -, -, hKn', -, -, hmaxbar, -, -, -⟩ :=
    CFSG.Quasithin.H13.QRC.bender_section_setup hns' T' hTn hTM' hMH' hmax' hVT' hVM'
  obtain ⟨hsl, hss, -, -, hVsw⟩ := hswap s hs g j hj hact
  rw [hT'] at hsup hsyl hs hmaxbar
  refine ⟨k, inferInstance, inferInstance, inferInstance, hk, ⟨{
    θ := θ'
    ι := ι
    ι_injective := hιinj
    ι_apply := hιapp
    kZero_eq := hK₀
    sup_eq_top := hsup
    sylow := hsyl
    V_le := hVK
    V_le_center := hVZ
    V_not_le_long := hnl
    V_not_le_short := hns
    card_V := hcard.trans (relIndex_subgroupOf_inf_pCore hVX)
    swap := ⟨s, hs, g, j, hj, hact, hsl, hss, hVsw⟩
    uniqueMax := hmaxbar
    borel_le := ?_ }⟩⟩
  set N := Subgroup.normalizer ((barIn M X T ⊓ kZero X M : Subgroup _) :
    Set (↥X ⧸ kerIn (M.subgroupOf X) ⊤)) with hNdef
  have hTN : barIn M X T ≤ N := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht,
      (Subgroup.normalizer_eq_top_iff.mpr hKn').symm ▸ Subgroup.mem_top t⟩
  have hNlt : N < ⊤ := by
    refine lt_of_le_of_ne le_top fun hNtop => ?_
    set w : antiSp k := CFSG.QuasithinUnique.Fin257.Sp4.wS with hw
    apply CFSG.QuasithinUnique.Fin257.Sp4.wS_not_mem_normalizer_U (K := k)
    rw [← hw]
    have hx : ((θ'.symm w : ↥(kZero X M)) : ↥X ⧸ kerIn (M.subgroupOf X) ⊤) ∈ N :=
      hNtop ▸ Subgroup.mem_top _
    have key : ∀ u ∈ antiUnipotent k, w * u * w⁻¹ ∈ antiUnipotent k := by
      intro u hu
      rw [← hsyl] at hu ⊢
      obtain ⟨y, hy, rfl⟩ := hu
      refine ⟨θ'.symm w * y * (θ'.symm w)⁻¹, ?_, by simp⟩
      have hy' : ((y : ↥(kZero X M)) : ↥X ⧸ kerIn (M.subgroupOf X) ⊤) ∈
          barIn M X T ⊓ kZero X M := ⟨hy, y.2⟩
      exact ((Subgroup.mem_normalizer_iff.mp hx _).mp hy').1
    have hww : w * w = 1 := CFSG.QuasithinUnique.Fin257.Sp4.wS_mul_self
    have hwi : w⁻¹ = w := CFSG.QuasithinUnique.Fin257.Sp4.wS_inv
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨key u, fun hu => ?_⟩
    have h1 := key _ hu
    have e' : w * (w * u * w⁻¹) * w⁻¹ = u := by
      rw [hwi]
      calc w * (w * u * w) * w = (w * w) * u * (w * w) := by group
        _ = u := by rw [hww, one_mul, mul_one]
    rwa [e'] at h1
  exact inf_le_right.trans (hmaxbar.2.2 N hTN hNlt)

end E2

end CFSG.Quasithin
