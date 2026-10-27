module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveTwoSplitAct
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapLemmaR
public import CFSG.LocalAnalysis.WeakClosure81.SymSixSpFour
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.PermAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap5_exists_action {V H T U : Subgroup G} (hD : DispatchHyp V H T U) {X : Type}
    [Group X] {φ : ↥(kGenIn V H) →* X}
    (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) :
    ∃ (ρ : ↥U →* MulAut X) (Z₁ : Subgroup X),
      (∀ (u : ↥U) (k k' : ↥(kGenIn V H)), (k' : G) = u * k * u⁻¹ → ρ u (φ k) = φ k') ∧
      Function.Injective ρ ∧
      ActionFacts X (barSub (kGenIn V H) φ V) ρ.range Z₁ (rk ↥V) ∧
      ∀ k : ↥(kGenIn V H),
        φ k ∈ Z₁ ↔ (k : G) ∈ Subgroup.centralizer (eSub V H T : Set G) := by
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hKT := hD.eq_sup
  have hUH : U ≤ H := hD.le_T.trans h83.T_le_H
  have hnK : ∀ u : ↥U, (u : G) ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    fun u => h83.le_normalizer_kGenIn_of_eq_sup hKT (hUH u.2)
  have hmem : ∀ (u : ↥U) (k : ↥(kGenIn V H)), (u : G) * k * (u : G)⁻¹ ∈ kGenIn V H :=
    fun u k => (Subgroup.mem_normalizer_iff.1 (hnK u) k).1 k.2
  let cj : ↥U → ↥(kGenIn V H) → ↥(kGenIn V H) := fun u k => ⟨u * k * u⁻¹, hmem u k⟩
  have hcj_one : ∀ k, cj 1 k = k := fun k => Subtype.ext (by simp [cj])
  have hcj_mul : ∀ a b k, cj (a * b) k = cj a (cj b k) := fun a b k =>
    Subtype.ext (by simp [cj, mul_assoc])
  have hcj_mul' : ∀ u k k', cj u (k * k') = cj u k * cj u k' := fun u k k' =>
    Subtype.ext (by simp [cj, mul_assoc])
  choose ρ₀ hρ₀ using fun u : ↥U => exists_conj_aut h83 hKT hφ (hUH u.2)
  have hρcj : ∀ u k, ρ₀ u (φ k) = φ (cj u k) := fun u k => hρ₀ u k (cj u k) rfl
  let ρ : ↥U →* MulAut X :=
    { toFun := ρ₀
      map_one' := by
        refine MulEquiv.ext fun x => ?_
        obtain ⟨k, rfl⟩ := hφ.surjective x
        rw [hρcj, hcj_one]
        rfl
      map_mul' := fun a b => by
        refine MulEquiv.ext fun x => ?_
        obtain ⟨k, rfl⟩ := hφ.surjective x
        rw [hρcj, hcj_mul]
        change _ = ρ₀ a (ρ₀ b (φ k))
        rw [hρcj, hρcj] }
  have hρ : ∀ u k, ρ u (φ k) = φ (cj u k) := hρcj
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNC : pCoreOf 2 (kGenIn V H) ≤ Subgroup.centralizer (eSub V H T : Set G) :=
    h83.pCoreOf_kGenIn_le_centralizer_eSub
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    let Y : Subgroup G := ρ.ker.map U.subtype
    have hYU : Y ≤ U := Subgroup.map_subtype_le _
    have hYK : ⁅Y, kGenIn V H⁆ ≤ Subgroup.centralizer (eSub V H T : Set G) := by
      rw [Subgroup.commutator_le]
      rintro y ⟨u, hu, rfl⟩ k hk
      have hρu : ρ u = 1 := hu
      let k₀ : ↥(kGenIn V H) := ⟨k, hk⟩
      have h1 : φ (cj u k₀) = φ k₀ := by rw [← hρ, hρu]; rfl
      have h2 : (((cj u k₀) * k₀⁻¹ : ↥(kGenIn V H)) : G) ∈ pCoreOf 2 (kGenIn V H) := by
        rw [← hφ.ker_iff, map_mul, h1, map_inv, mul_inv_cancel]
      apply hNC
      simpa [cj, commutatorElement_def] using h2
    have hY := hD.faithful Y hYU hYK
    intro u hu
    have h1 : (u : G) ∈ Y := ⟨u, hu, rfl⟩
    rw [hY, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot.2 (Subtype.ext h1))
  have hUea : IsElemAbelian 2 U := by
    obtain ⟨g, hg⟩ := hD.conj
    rw [hg]
    exact isElemAbelian_conjSubgroup' h83.elemAbelian g
  have hUV : Nat.card ↥U = Nat.card ↥V := by
    obtain ⟨g, hg⟩ := hD.conj
    rw [hg]
    exact CFSG.Quasithin.E3.card_conjSubgroup V g
  have hVp : IsPGroup 2 ↥V :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian h83.elemAbelian
  have hVpow : Nat.card ↥V = 2 ^ rk ↥V := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hVp
    unfold rk
    rw [hk, padicValNat.prime_pow]
  have hAea : IsElemAbelian 2 ρ.range := by
    rw [MonoidHom.range_eq_map]
    have h1 : IsElemAbelian 2 (U.subgroupOf U) := hUea.subgroupOf U
    rw [Subgroup.subgroupOf_self] at h1
    exact h1.map ρ
  have hAcard : Nat.card ρ.range = 2 ^ rk ↥V := by
    rw [← hVpow, ← hUV]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hlt : Nat.card (barSub (kGenIn V H) φ V) < 2 ^ rk ↥V := by
    rw [h83.card_barSub_eq_two_pow_rankBarV hKT hφ, ← hVpow]
    have h1 := E3.card_eq_two_pow_mul hVp
      (U := V ⊓ Subgroup.centralizer (eSub V H T : Set G)) inf_le_left
    have h2 : 1 < Nat.card ↥(V ⊓ Subgroup.centralizer (eSub V H T : Set G)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 hD.inf_V_ne_bot
    unfold rankBarV
    rw [h1]
    exact lt_mul_of_one_lt_right (by positivity) h2
  refine ⟨ρ, ((Subgroup.centralizer (eSub V H T : Set G)).subgroupOf (kGenIn V H)).map φ,
    ?_, hinj, ⟨hAea, hAcard, hlt, ?_, ?_, ?_⟩, ?_⟩
  · intro u k k' hk'
    rw [hρ]
    congr 1
    exact Subtype.ext (by rw [hk'])
  ·
    rintro a ⟨u, rfl⟩ s hs
    obtain ⟨k, hkV, rfl⟩ := mem_barSub.1 hs
    rw [hρ]
    congr 1
    refine Subtype.ext ?_
    change (u : G) * k * (u : G)⁻¹ = k
    rw [hD.comm_V u u.2 k hkV]
    group
  ·
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨k', rfl⟩ := hφ.surjective x
    have h1 := h83.comm_mem_pCoreOf_of_mem_inf_centralizer hKT (r := (k : G))
      (Subgroup.mem_subgroupOf.1 hk) k' k'.2
    have h2 : φ (k * k' * k⁻¹ * k'⁻¹) = 1 := (hφ.ker_iff _).2 (by simpa using h1)
    simp only [map_mul, map_inv] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.1 (by rwa [commutatorElement_def])).symm
  ·
    intro Q hQodd hQinv a ha q hq
    obtain ⟨u, rfl⟩ := ha
    obtain ⟨k, rfl⟩ := hφ.surjective q
    let Qh : Subgroup G := (Q.comap φ).map (kGenIn V H).subtype
    have hQK : Qh ≤ kGenIn V H := by
      rintro g ⟨k₀, -, rfl⟩
      exact k₀.2
    have hmemQh : ∀ k₀ : ↥(kGenIn V H), (k₀ : G) ∈ Qh ↔ φ k₀ ∈ Q := fun k₀ => by
      constructor
      · rintro ⟨k₁, hk₁, h⟩
        rw [← Subtype.ext h]
        exact hk₁
      · intro h
        exact ⟨k₀, h, rfl⟩
    have key : ∀ u' : ↥U, ∀ g ∈ Qh, (u' : G) * g * (u' : G)⁻¹ ∈ Qh := by
      intro u' g hg
      have hgK : g ∈ kGenIn V H := hQK hg
      have h1 : (u' : G) * g * (u' : G)⁻¹ = ((cj u' ⟨g, hgK⟩ : ↥(kGenIn V H)) : G) := rfl
      rw [h1, hmemQh, ← hρ]
      exact hQinv _ ⟨u', rfl⟩ _ ((hmemQh ⟨g, hgK⟩).1 hg)
    have hUn : U ≤ Subgroup.normalizer (Qh : Set G) := by
      intro u' hu'
      rw [Subgroup.mem_normalizer_iff]
      intro g
      refine ⟨fun hg => key ⟨u', hu'⟩ g hg, fun hg => ?_⟩
      have := key ⟨u'⁻¹, U.inv_mem hu'⟩ _ hg
      simpa [mul_assoc] using this
    have hodd : Odd ((Subgroup.centralizer (eSub V H T : Set G)).relIndex Qh) := by
      have h1 : barSub (kGenIn V H) φ Qh = Q := by
        have h2 : Qh.subgroupOf (kGenIn V H) = Q.comap φ := by
          ext k₀
          rw [Subgroup.mem_subgroupOf, hmemQh, Subgroup.mem_comap]
        change (Qh.subgroupOf (kGenIn V H)).map φ = Q
        rw [h2]
        exact Subgroup.map_comap_eq_self_of_surjective hφ.surjective Q
      have h3 := card_barSub_eq_relIndex_of_isBarMap hQK (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hφ
      rw [h1] at h3
      rw [h3] at hQodd
      exact Odd.of_dvd_nat hQodd (Subgroup.relIndex_dvd_of_le_left Qh hNC)
    have hcomm := hD.odd_comm Qh hQK hUn hodd
    have hkQ : (k : G) ∈ Qh := (hmemQh k).2 hq
    have hc : ⁅(u : G), (k : G)⁆ ∈ Subgroup.centralizer (eSub V H T : Set G) := by
      apply hcomm
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator u.2 hkQ
    rw [hρ, ← map_inv, ← map_mul]
    refine Subgroup.mem_map.2 ⟨cj u k * k⁻¹, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    simpa [cj, commutatorElement_def] using hc
  · intro k
    constructor
    · intro hk
      obtain ⟨k', hk', hkk⟩ := Subgroup.mem_map.1 hk
      have h1 : φ (k'⁻¹ * k) = 1 := by rw [map_mul, map_inv, hkk, inv_mul_cancel]
      have h2 := hNC ((hφ.ker_iff _).1 h1)
      have h3 := (Subgroup.centralizer (eSub V H T : Set G)).mul_mem
        (Subgroup.mem_subgroupOf.1 hk') h2
      simpa using h3
    · intro hk
      exact Subgroup.mem_map.2 ⟨k, Subgroup.mem_subgroupOf.2 hk, rfl⟩

theorem gap5_commutator_mem {V H T : Subgroup G} (h83 : Hyp83 V H T) {h : G} (hh : h ∈ H) {c : G}
    (hc : c ∈ conjSubgroup V h) {e : G} (he : e ∈ eSub V H T) :
    e * c * e⁻¹ * c⁻¹ ∈ eSub V H T ∧ e * c * e⁻¹ * c⁻¹ ∈ conjSubgroup V h := by
  have heC : e ∈ Subgroup.centralizer (eSub V H T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (h83.isMulCommutative_eSub.is_comm.comm ⟨a, ha⟩ ⟨e, he⟩)
  have hN : e ∈ Subgroup.normalizer (conjSubgroup V h : Set G) :=
    h83.mem_normalizer_conjSubgroup_of_mem_centralizer hh heC
  have h1 : e * c * e⁻¹ ∈ conjSubgroup V h := (Subgroup.mem_normalizer_iff.1 hN c).1 hc
  have hcH : c ∈ H := by
    have h2 : h * c * h⁻¹ ∈ V := mem_conjSubgroup_iff.1 hc
    have h3 : h⁻¹ * (h * c * h⁻¹) * h ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hh) (h83.le_H h2)) hh
    rwa [show h⁻¹ * (h * c * h⁻¹) * h = c by group] at h3
  have hE := (Subgroup.normal_subgroupOf_iff h83.eSub_le_H).mp h83.eSub_subgroupOf_normal
  have h4 : c * e⁻¹ * c⁻¹ ∈ eSub V H T := hE e⁻¹ c ((eSub V H T).inv_mem he) hcH
  refine ⟨?_, (conjSubgroup V h).mul_mem h1 ((conjSubgroup V h).inv_mem hc)⟩
  simpa [mul_assoc] using (eSub V H T).mul_mem he h4

theorem gap5_exists_fixed_point {V H T U : Subgroup G} (hD : DispatchHyp V H T U) {h : G}
    (hh : h ∈ H) {c : G} (hc : c ∈ conjSubgroup V h)
    (hcE : c ∉ Subgroup.centralizer (eSub V H T : Set G)) {u : G} (hu : u ∈ U)
    (hcomm : u * c * u⁻¹ * c⁻¹ ∈ Subgroup.centralizer (eSub V H T : Set G)) :
    ∃ p : G, p ≠ 1 ∧ p ∈ eSub V H T ∧ p ∈ conjSubgroup V h ∧ u * p = p * u := by
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hex : ∃ e ∈ eSub V H T, e * c ≠ c * e := by
    by_contra hcon
    apply hcE
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    by_contra hne
    exact hcon ⟨a, ha, hne⟩
  obtain ⟨e, he, hec⟩ := hex
  set d : G := e * c * e⁻¹ * c⁻¹ with hd
  have hdE : d ∈ eSub V H T := by
    rw [hd]
    exact (gap5_commutator_mem h83 hh hc he).1
  have hdV : d ∈ conjSubgroup V h := by
    rw [hd]
    exact (gap5_commutator_mem h83 hh hc he).2
  have hd1 : d ≠ 1 := by
    rw [hd]
    intro h1
    apply hec
    have h2 : e * c * e⁻¹ = c := by
      have h3 := congrArg (· * c) h1
      simpa [mul_assoc] using h3
    calc e * c = (e * c * e⁻¹) * e := by group
      _ = c * e := by rw [h2]
  set e' : G := u * e * u⁻¹ with he'
  have he'E : e' ∈ eSub V H T := by
    rw [he']
    exact (Subgroup.normal_subgroupOf_iff h83.eSub_le_H).mp h83.eSub_subgroupOf_normal e u he
      (h83.T_le_H (hD.le_T hu))
  set d' : G := e' * c * e'⁻¹ * c⁻¹ with hd'
  have hd'E : d' ∈ eSub V H T := by
    rw [hd']
    exact (gap5_commutator_mem h83 hh hc he'E).1
  have hd'V : d' ∈ conjSubgroup V h := by
    rw [hd']
    exact (gap5_commutator_mem h83 hh hc he'E).2
  set z : G := u * c * u⁻¹ * c⁻¹ with hz
  have hzC : z ∈ Subgroup.centralizer (eSub V H T : Set G) := by
    rw [hz]
    exact hcomm
  have hz_e' : z * e' = e' * z := (Subgroup.mem_centralizer_iff.1 hzC e' he'E).symm
  have hz_d' : z * d' * z⁻¹ = d' := by
    rw [(Subgroup.mem_centralizer_iff.1 hzC d' hd'E).symm, mul_assoc, mul_inv_cancel, mul_one]
  have huc : u * c * u⁻¹ = z * c := by
    rw [hz]
    group
  have hUea : IsElemAbelian 2 U := by
    obtain ⟨g, hg⟩ := hD.conj
    rw [hg]
    exact isElemAbelian_conjSubgroup' h83.elemAbelian g
  have huu : u * u = 1 := by
    have h := hUea.2 u hu
    rwa [pow_two] at h
  have hkey : u * d * u⁻¹ = d' := by
    rw [hd]
    have h1 : u * (e * c * e⁻¹ * c⁻¹) * u⁻¹ =
        e' * (u * c * u⁻¹) * e'⁻¹ * (u * c * u⁻¹)⁻¹ := by
      rw [he']
      group
    rw [h1, huc]
    have h2 : e' * (z * c) * e'⁻¹ * (z * c)⁻¹ = z * d' * z⁻¹ := by
      calc e' * (z * c) * e'⁻¹ * (z * c)⁻¹
          = (e' * z) * c * e'⁻¹ * (c⁻¹ * z⁻¹) := by group
        _ = (z * e') * c * e'⁻¹ * (c⁻¹ * z⁻¹) := by rw [hz_e']
        _ = z * (e' * c * e'⁻¹ * c⁻¹) * z⁻¹ := by group
        _ = z * d' * z⁻¹ := by rw [hd']
    rw [h2, hz_d']
  have hkey' : u * d' * u⁻¹ = d := by
    rw [← hkey]
    calc u * (u * d * u⁻¹) * u⁻¹ = (u * u) * d * (u⁻¹ * u⁻¹) := by group
      _ = d := by
            have h2 : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, huu, inv_one]
            rw [huu, h2, one_mul, mul_one]
  by_cases hdd : d' = d
  · refine ⟨d, hd1, hdE, hdV, ?_⟩
    have h := hkey
    rw [hdd] at h
    calc u * d = (u * d * u⁻¹) * u := by group
      _ = d * u := by rw [h]
  · refine ⟨d * d', ?_, (eSub V H T).mul_mem hdE hd'E,
      (conjSubgroup V h).mul_mem hdV hd'V, ?_⟩
    · intro h1
      apply hdd
      have hdsq : d * d = 1 := by
        have h := h83.isElemAbelian_eSub.2 d hdE
        rwa [pow_two] at h
      calc d' = (d * d) * d' := by rw [hdsq, one_mul]
        _ = d * (d * d') := by group
        _ = d * 1 := by rw [h1]
        _ = d := mul_one d
    · have h := calc u * (d * d') * u⁻¹ = (u * d * u⁻¹) * (u * d' * u⁻¹) := by group
          _ = d' * d := by rw [hkey, hkey']
          _ = d * d' := (congrArg Subtype.val
                (h83.isMulCommutative_eSub.is_comm.comm ⟨d, hdE⟩ ⟨d', hd'E⟩)).symm
      calc u * (d * d') = (u * (d * d') * u⁻¹) * u := by group
        _ = (d * d') * u := by rw [h]

theorem gap5_normalizes_of_comm {V H T U : Subgroup G} (hD : DispatchHyp V H T U) {h : G}
    (hh : h ∈ H) {c : G} (hc : c ∈ conjSubgroup V h)
    (hcE : c ∉ Subgroup.centralizer (eSub V H T : Set G)) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1)
    (hcomm : u * c * u⁻¹ * c⁻¹ ∈ Subgroup.centralizer (eSub V H T : Set G)) :
    ∀ u' ∈ U, u' ∈ Subgroup.normalizer ((conjSubgroup V h : Subgroup G) : Set G) := by
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  obtain ⟨p, hp1, hpE, hpW, hup⟩ := gap5_exists_fixed_point hD hh hc hcE hu hcomm
  have hpC : p ∈ eSub V H T ⊓ Subgroup.centralizer ({u} : Set G) :=
    ⟨hpE, Subgroup.mem_centralizer_iff.2 fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hup⟩
  rw [← hD.cent_eq u hu hu1] at hpC
  intro u' hu'
  exact mem_normalizer_of_commute_ne_one (isTI_conjSubgroup_quasithin h83.isTI h) hpW hp1
    (Subgroup.mem_centralizer_iff.1 hpC.2 u' hu')

theorem gap5_dichotomy_X {V H T U : Subgroup G} (hD : DispatchHyp V H T U) {X : Type}
    [Group X] {φ : ↥(kGenIn V H) →* X}
    (hφ : IsBarMap (kGenIn V H) (pCoreOf 2 (kGenIn V H)) φ) {ρ : ↥U →* MulAut X}
    {Z₁ : Subgroup X}
    (hρ : ∀ (u : ↥U) (k k' : ↥(kGenIn V H)), (k' : G) = u * k * u⁻¹ → ρ u (φ k) = φ k')
    (hZ : ∀ k : ↥(kGenIn V H),
      φ k ∈ Z₁ ↔ (k : G) ∈ Subgroup.centralizer (eSub V H T : Set G))
    (x : X) {s : X} (hs : s ∈ barSub (kGenIn V H) φ V) {u : ↥U} (hu1 : u ≠ 1)
    (hxs : x * s * x⁻¹ ∉ Z₁) (hfix : ρ u (x * s * x⁻¹) * (x * s * x⁻¹)⁻¹ ∈ Z₁) :
    ∀ u' : ↥U, ∃ s' ∈ barSub (kGenIn V H) φ V, ρ u' (x * s * x⁻¹) = x * s' * x⁻¹ := by
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hKT := hD.eq_sup
  have hUH : U ≤ H := hD.le_T.trans h83.T_le_H
  have hnormU : ∀ u : ↥U, (u : G) ∈ Subgroup.normalizer ((kGenIn V H : Subgroup G) : Set G) :=
    fun u => h83.le_normalizer_kGenIn_of_eq_sup hKT (hUH u.2)
  let cj : ↥U → ↥(kGenIn V H) → ↥(kGenIn V H) :=
    fun u k => ⟨(u : G) * k * (u : G)⁻¹, (Subgroup.mem_normalizer_iff.1 (hnormU u) k).1 k.2⟩
  have hcj_coe : ∀ (u : ↥U) (k : ↥(kGenIn V H)), (cj u k : G) = (u : G) * k * (u : G)⁻¹ :=
    fun _ _ => rfl
  have hρcj : ∀ (u : ↥U) (k : ↥(kGenIn V H)), ρ u (φ k) = φ (cj u k) :=
    fun u k => hρ u k (cj u k) rfl
  obtain ⟨k₀, rfl⟩ := hφ.surjective x
  obtain ⟨v, hvV, rfl⟩ := mem_barSub.1 hs
  let cK : ↥(kGenIn V H) := ⟨(k₀ : G) * (v : G) * (k₀ : G)⁻¹,
    (kGenIn V H).mul_mem ((kGenIn V H).mul_mem k₀.2 v.2) ((kGenIn V H).inv_mem k₀.2)⟩
  have hcK_eq : cK = k₀ * v * k₀⁻¹ := Subtype.ext rfl
  have hφc : φ cK = φ k₀ * φ v * (φ k₀)⁻¹ := by rw [hcK_eq, map_mul, map_mul, map_inv]
  set h : G := (k₀ : G)⁻¹ with hhdef
  have hhH : h ∈ H := H.inv_mem (kGenIn_le_H h83.le_H k₀.2)
  have hc : (cK : G) ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    rw [show h * (cK : G) * h⁻¹ = (v : G) by
      simp only [hhdef, hcK_eq, Subgroup.coe_mul, Subgroup.coe_inv]
      group]
    exact hvV
  have hcE : (cK : G) ∉ Subgroup.centralizer (eSub V H T : Set G) := by
    intro hcin
    apply hxs
    rw [← hφc]
    exact (hZ cK).2 hcin
  have hmap : ρ u (φ cK) = φ (cj u cK) := hρcj u cK
  have hfix' : φ (cj u cK) * (φ cK)⁻¹ ∈ Z₁ := by
    have h1 : ρ u (φ cK) * (φ cK)⁻¹ ∈ Z₁ := by
      rwa [← hφc] at hfix
    rwa [hmap] at h1
  have hcomm' : (((cj u cK) * cK⁻¹ : ↥(kGenIn V H)) : G) ∈
      Subgroup.centralizer (eSub V H T : Set G) := by
    apply (hZ (cj u cK * cK⁻¹)).1
    rw [map_mul, map_inv]
    exact hfix'
  have hcomm : (u : G) * (cK : G) * (u : G)⁻¹ * (cK : G)⁻¹ ∈
      Subgroup.centralizer (eSub V H T : Set G) := by
    have h1 : (((cj u cK) * cK⁻¹ : ↥(kGenIn V H)) : G) =
        (u : G) * (cK : G) * (u : G)⁻¹ * (cK : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcj_coe]
    rwa [h1] at hcomm'
  have hnorm := gap5_normalizes_of_comm hD hhH hc hcE (u := (u : G)) u.2
    (fun h1 => hu1 (Subtype.ext h1)) hcomm
  intro u'
  have hmem : (u' : G) * (cK : G) * (u' : G)⁻¹ ∈ conjSubgroup V h :=
    (Subgroup.mem_normalizer_iff.1 (hnorm (u' : G) u'.2) (cK : G)).1 hc
  have hv'mem : h * ((u' : G) * (cK : G) * (u' : G)⁻¹) * h⁻¹ ∈ V :=
    mem_conjSubgroup_iff.1 hmem
  let v'K : ↥(kGenIn V H) :=
    ⟨h * ((u' : G) * (cK : G) * (u' : G)⁻¹) * h⁻¹, le_kGenIn_self V H hv'mem⟩
  refine ⟨φ v'K, mem_barSub.2 ⟨v'K, hv'mem, rfl⟩, ?_⟩
  have hcv : (cj u' cK : G) = (u' : G) * (cK : G) * (u' : G)⁻¹ := hcj_coe u' cK
  have hv'k : (v'K : G) = h * ((u' : G) * (cK : G) * (u' : G)⁻¹) * h⁻¹ := rfl
  calc ρ u' (φ k₀ * φ v * (φ k₀)⁻¹) = ρ u' (φ cK) := by rw [hφc]
    _ = φ (cj u' cK) := hρcj u' cK
    _ = φ (k₀ * v'K * k₀⁻¹) := by
          congr 1
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hcv, hv'k, hhdef]
          group
    _ = φ k₀ * φ v'K * (φ k₀)⁻¹ := by rw [map_mul, map_mul, map_inv]

theorem gap5_U_facts {V H T U : Subgroup G} (hD : DispatchHyp V H T U) :
    (∀ u : ↥U, u * u = 1) ∧ ∃ u v : ↥U, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  have h83 : Hyp83 V H T := Hyp83.of_hyp7 hD.hyp7 hD.calH hD.not_calH0 hD.sylow
  have hUea : IsElemAbelian 2 U := by
    obtain ⟨g, hg⟩ := hD.conj
    rw [hg]
    exact isElemAbelian_conjSubgroup' h83.elemAbelian g
  have hUcard : Nat.card ↥U = Nat.card ↥V := by
    obtain ⟨g, hg⟩ := hD.conj
    rw [hg]
    exact CFSG.Quasithin.E3.card_conjSubgroup V g
  have hU2 : 2 < Nat.card ↥U := by rw [hUcard]; exact hD.hyp7.2.1
  refine ⟨fun u => ?_, ?_⟩
  · have h := hUea.2 u u.2
    rw [pow_two] at h
    exact Subtype.ext h
  · classical
    haveI : Fintype ↥U := Fintype.ofFinite _
    have hnt : Nontrivial ↥U := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
    obtain ⟨a, ha1⟩ := exists_ne (1 : ↥U)
    by_cases hall : ∀ x : ↥U, x ≠ 1 → x = a
    · exfalso
      have hsub : (Finset.univ : Finset ↥U) ⊆ ({1, a} : Finset ↥U) := by
        intro x _
        by_cases hx : x = 1
        · simp [hx]
        · simp [hall x hx]
      have hcard : Fintype.card ↥U ≤ 2 := by
        calc Fintype.card ↥U = (Finset.univ : Finset ↥U).card := Finset.card_univ.symm
          _ ≤ ({1, a} : Finset ↥U).card := Finset.card_le_card hsub
          _ ≤ 2 := by
            have h := Finset.card_insert_le (1 : ↥U) ({a} : Finset ↥U)
            simpa using h
      rw [Nat.card_eq_fintype_card] at hU2
      omega
    · push Not at hall
      obtain ⟨b, hb1, hba⟩ := hall
      exact ⟨a, b, ha1, hb1, fun hab => hba hab.symm⟩

theorem gap5_kBarCenterShape_of_symSix {V H T : Subgroup G} {Y : Type} [Group Y]
    (ψ : ↥(kGenIn V H) →* Y) (hψ : Function.Surjective ψ)
    (hk : ∀ k : ↥(kGenIn V H), ψ k = 1 ↔ (k : G) ∈ eCentSet V H T) (hY : IsSymGp Y 6) :
    KBarCenterShape V H T (fun X _ => IsSpGp X 4 1) := by
  obtain ⟨e⟩ := hY
  refine ⟨Y, inferInstance, ψ, hψ, ?_, isSpGp_four_one_of_isSymGp_six ⟨e⟩⟩
  intro k
  constructor
  · intro hk1
    refine ⟨k.2, ?_⟩
    intro x hx
    have h1 : ψ (k * (⟨x, hx⟩ : ↥(kGenIn V H)) * k⁻¹ * (⟨x, hx⟩ : ↥(kGenIn V H))⁻¹) = 1 := by
      simp [map_mul, map_inv, hk1]
    have h2 := (hk (k * (⟨x, hx⟩ : ↥(kGenIn V H)) * k⁻¹
      * (⟨x, hx⟩ : ↥(kGenIn V H))⁻¹)).1 h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
  · intro hk'
    rcases hk' with ⟨-, hcent⟩
    have hcentY : ∀ y : Y, ψ k * y = y * ψ k := by
      intro y
      obtain ⟨x, rfl⟩ := hψ y
      have h1 : ψ (k * x * k⁻¹ * x⁻¹) = 1 :=
        (hk (k * x * k⁻¹ * x⁻¹)).2
          (by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcent x x.2)
      have h2 : ⁅ψ k, ψ x⁆ = 1 := by
        rw [commutatorElement_def]
        simpa only [map_mul, map_inv] using h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h2
    have hcenter : e (ψ k) ∈ Subgroup.center (Equiv.Perm (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro σ
      have h1 : e (ψ k * e.symm σ) = e (e.symm σ * ψ k) := by
        rw [hcentY (e.symm σ)]
      rw [map_mul, map_mul] at h1
      simpa using h1.symm
    have hzero : e (ψ k) = 1 :=
      CFSG.EvenSmallLie.OddTranspAlt.perm_center_trivial (m := 6) (by norm_num) (e (ψ k))
        (fun σ => (Subgroup.mem_center_iff.1 hcenter σ).symm)
    exact MulEquiv.injective e (by rw [hzero, map_one])

end CFSG.LocalAnalysis.WeakClosure81

end
