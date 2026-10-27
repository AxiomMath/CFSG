module

import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmall
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.WeakClosure81.SevenCommI
public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

private theorem triaAmb_card_conj {X : Type} [Group X] (g : X) (A : Subgroup X) :
    Nat.card (conjSubgroup A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem triaAmb_barSub_pCoreOf_eq_bot {K : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K (pCoreOf 2 K) φ) :
    barSub K φ (pCoreOf 2 K) = ⊥ := by
  rw [barSub, Subgroup.map_eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker]
  exact (hφ.ker_iff k).mpr (Subgroup.mem_subgroupOf.mp hk)

private theorem card_barSub_of_mem_omegaSet (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) : Nat.card (barSub (kSub V H E) φ U) = 2 := by
  obtain ⟨k, hk, hUeq⟩ := h.transitive U hU
  let k' : ↥(kSub V H E) := ⟨k, hk⟩
  have hbar : barSub (kSub V H E) φ U =
      conjSubgroup (barSub (kSub V H E) φ V) (φ k') := by
    rw [hUeq]
    exact barSub_conjSubgroup φ V k'
  rw [hbar, triaAmb_card_conj, hS]

private theorem triaAmb_bar_eq_zpowers (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) {d : ↥(kSub V H E)} (hd : (d : G) ∈ U)
    (hd1 : (d : G) ∉ pCoreOf 2 H) :
    φ d ≠ 1 ∧ (φ d) ^ 2 = 1 ∧ φ d ∈ barSub (kSub V H E) φ U ∧
      barSub (kSub V H E) φ U = Subgroup.zpowers (φ d) := by
  have hdJ : (d : G) ∉ pCoreOf 2 (kSub V H E) := fun hJ => hd1 (h.pcore_le hJ)
  have hdne : φ d ≠ 1 := fun h1 => hdJ ((hφ.ker_iff d).mp h1)
  have hUab : IsElemAbelian 2 U := isElemAbelian_of_mem_omegaSet h.elemAbelian hU
  have hd2 : (d : ↥(kSub V H E)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    simpa [pow_two] using elemAbelian_mul_self hUab hd
  have hd2' : (φ d) ^ 2 = 1 := by rw [← map_pow, hd2, map_one]
  have hmem : φ d ∈ barSub (kSub V H E) φ U := mem_barSub.mpr ⟨d, hd, rfl⟩
  have hcard : Nat.card (barSub (kSub V H E) φ U) = 2 :=
    card_barSub_of_mem_omegaSet h hφ hS hU
  exact ⟨hdne, hd2', hmem, (seven_eleven_small_zpowers_eq hcard hmem hdne).symm⟩


theorem commutator_mem_inf_iSub_of_mem_omegaSet (h : Hyp711 V H E) {U : Subgroup G}
    (hU : U ∈ omegaSet V H E) {x u : G} (hx : x ∈ iSub V H E) (hu : u ∈ U) :
    ⁅u, x⁆ ∈ U ⊓ iSub V H E := by
  obtain ⟨k, hk, hUeq⟩ := h.transitive U hU
  have hkH : k ∈ H := kSub_le_of_forall_le h.omega_le hk
  have hIleH : iSub V H E ≤ H :=
    h.iSub_le.trans (h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H))
  have hIN : H ≤ Subgroup.normalizer (iSub V H E : Set G) :=
    le_normalizer_of_subgroupOf_normal hIleH (iSub_subgroupOf_normal h.le h.normal)
  let v : G := k * u * k⁻¹
  let x' : G := k * x * k⁻¹
  have hvV : v ∈ V := by
    change k * u * k⁻¹ ∈ V
    exact mem_conjSubgroup_iff.mp (hUeq ▸ hu)
  have hx'I : x' ∈ iSub V H E := by
    change k * x * k⁻¹ ∈ iSub V H E
    exact (Subgroup.mem_normalizer_iff.mp (hIN hkH) x).mp hx
  have hcomm := commutator_mem_inf_iSub h.elemAbelian h.ti h.abelian h.le h.normal
    h.omega_le h.mem hx'I hvV
  have hzV : ⁅v, x'⁆ ∈ V := by
    rw [← commutatorElement_inv]
    exact V.inv_mem hcomm.1
  have hzI : ⁅v, x'⁆ ∈ iSub V H E := by
    rw [← commutatorElement_inv]
    exact (iSub V H E).inv_mem hcomm.2
  have hzU : k⁻¹ * ⁅v, x'⁆ * k ∈ U := by
    rw [hUeq]
    refine mem_conjSubgroup_iff.mpr ?_
    have hkey : k * (k⁻¹ * ⁅v, x'⁆ * k) * k⁻¹ = ⁅v, x'⁆ := by group
    rw [hkey]
    exact hzV
  have hzI' : k⁻¹ * ⁅v, x'⁆ * k ∈ iSub V H E := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hIN (H.inv_mem hkH)) ⁅v, x'⁆).mp hzI
  have heq : ⁅u, x⁆ = k⁻¹ * ⁅v, x'⁆ * k := by
    change u * x * u⁻¹ * x⁻¹ = k⁻¹ * (v * x' * v⁻¹ * x'⁻¹) * k
    simp only [v, x']
    group
  rw [heq]
  exact ⟨hzU, hzI'⟩

theorem commute_of_commuting_images (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {U W : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hW : W ∈ omegaSet V H E) {d e : ↥(kSub V H E)}
    (hd : (d : G) ∈ U) (he : (e : G) ∈ W) (hd1 : (d : G) ∉ pCoreOf 2 H)
    (he1 : (e : G) ∉ pCoreOf 2 H) (hcomm : φ d * φ e = φ e * φ d) :
    ∀ u ∈ U, ∀ w ∈ W, u * w = w * u := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hd2, -, hdUbar⟩ := triaAmb_bar_eq_zpowers h hφ hS hU hd hd1
  obtain ⟨-, he2, -, heWbar⟩ := triaAmb_bar_eq_zpowers h hφ hS hW he he1
  have hcommC : Commute (φ d) (φ e) := hcomm
  obtain ⟨a, b, hUa, hWb, hN⟩ := nVSub_conj_ne_bot_of_mem_omegaSet h.ti h.abelian hU hW
  have hJK : pCoreOf 2 (kSub V H E) ≤ kSub V H E :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (kSub V H E)
  have hUW : U ⊔ W ≤ kSub V H E := sup_le (le_kSub hU) (le_kSub hW)
  have hP : IsPGroup 2 ↥(U ⊔ W) := by
    let T : Subgroup G := U ⊔ W ⊔ pCoreOf 2 (kSub V H E)
    let T' : Subgroup ↥(kSub V H E) := T.subgroupOf (kSub V H E)
    have hTK : T ≤ kSub V H E := sup_le hUW hJK
    have hT'map : T'.map φ = Subgroup.zpowers (φ d) ⊔ Subgroup.zpowers (φ e) := by
      change barSub (kSub V H E) φ (U ⊔ W ⊔ pCoreOf 2 (kSub V H E)) = _
      rw [barSub_sup (A := U ⊔ W) (B := pCoreOf 2 (kSub V H E)) hUW hJK φ,
        barSub_sup (A := U) (B := W) (le_kSub hU) (le_kSub hW) φ,
        hdUbar, heWbar, triaAmb_barSub_pCoreOf_eq_bot hφ]
      simp
    have hPmap : IsPGroup 2 (T'.map φ) := by
      rw [hT'map]
      refine IsPGroup.to_sup_of_normal_right' ?_ ?_ ?_
      · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
        rw [Nat.card_zpowers]
        simpa using orderOf_dvd_of_pow_eq_one hd2
      · refine IsPGroup.of_card_dvd_pow (n := 1) ?_
        rw [Nat.card_zpowers]
        simpa using orderOf_dvd_of_pow_eq_one he2
      · refine (Subgroup.zpowers_le.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (hcommC.zpow_right n).symm
    have hker_eq : φ.ker = (pCoreOf 2 (kSub V H E)).subgroupOf (kSub V H E) := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hφ.ker_iff k
    have hJ2 : IsPGroup 2 (pCoreOf 2 (kSub V H E)) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kSub V H E)
    have hker2 : IsPGroup 2 φ.ker := by
      rw [hker_eq]
      exact hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe hJK).symm
    have hker_le : φ.ker ≤ T' := by
      intro k hk
      rw [hker_eq] at hk
      change (k : G) ∈ U ⊔ W ⊔ pCoreOf 2 (kSub V H E)
      exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hk)
    have hT'2 : IsPGroup 2 T' := by
      have hh := hPmap.comap_of_ker_isPGroup φ hker2
      rwa [Subgroup.comap_map_eq_self hker_le] at hh
    have hT2 : IsPGroup 2 T := hT'2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK)
    exact hT2.to_le le_sup_left
  have hN' : U ⊓ Subgroup.normalizer (W : Set G) ≠ ⊥ := by
    rw [hUa, hWb]
    exact hN
  intro u hu w hw
  exact commute_of_isPGroup_sup h.elemAbelian h.ti ⟨a, hUa⟩ ⟨b, hWb⟩ hN' hP u hu w hw

theorem orderOf_mul_eq_three_of_images (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hS : Nat.card (barSub (kSub V H E) φ V) = 2) {U W : Subgroup G}
    (hU : U ∈ omegaSet V H E) (hW : W ∈ omegaSet V H E) {d e : ↥(kSub V H E)}
    (hd : (d : G) ∈ U) (he : (e : G) ∈ W) (hd1 : (d : G) ∉ pCoreOf 2 H)
    (he1 : (e : G) ∉ pCoreOf 2 H) (h3 : orderOf (φ d * φ e) = 3) :
    orderOf (d * e) = 3 ∧ U ⊓ W = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnotP : ¬ IsPGroup 2 (Subgroup.closure ({(d : G), (e : G)} : Set G)) := by
    intro hP
    have hmem : (d : G) * (e : G) ∈ Subgroup.closure ({(d : G), (e : G)} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow
      (⟨(d : G) * (e : G), hmem⟩ : ↥(Subgroup.closure ({(d : G), (e : G)} : Set G)))
    have hcoe : orderOf ((d : G) * (e : G)) =
        orderOf (⟨(d : G) * (e : G), hmem⟩ :
          ↥(Subgroup.closure ({(d : G), (e : G)} : Set G))) :=
      Subgroup.orderOf_coe (⟨(d : G) * (e : G), hmem⟩ :
        ↥(Subgroup.closure ({(d : G), (e : G)} : Set G)))
    have hdvd : orderOf (φ d * φ e) ∣ orderOf ((d : G) * (e : G)) := by
      have h1 : orderOf (φ d * φ e) = orderOf (φ (d * e)) := by rw [map_mul]
      have h2 : orderOf (φ (d * e)) ∣ orderOf (d * e : ↥(kSub V H E)) :=
        orderOf_map_dvd φ (d * e)
      have hcoe' : orderOf ((d : G) * (e : G)) = orderOf (d * e : ↥(kSub V H E)) :=
        Subgroup.orderOf_coe (d * e)
      exact h1 ▸ (hcoe' ▸ h2)
    have h3dvd : 3 ∣ orderOf ((d : G) * (e : G)) := by
      rw [← h3]
      exact hdvd
    rw [hcoe, hk] at h3dvd
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3dvd)
  have hodd : Odd (orderOf ((d : G) * (e : G))) :=
    seven_three_A h.elemAbelian h.ti h.abelian hU hW hd he hnotP
  let x : G := (d : G) * (e : G)
  have hxJ : x ^ 3 ∈ pCoreOf 2 (kSub V H E) := by
    have h1 : φ ((d * e) ^ 3) = 1 := by
      rw [map_pow, map_mul, ← h3, pow_orderOf_eq_one]
    have h2 := (hφ.ker_iff ((d * e) ^ 3)).mp h1
    simpa only [Subgroup.coe_pow, Subgroup.coe_mul, x] using h2
  have hzp : IsPGroup 2 (Subgroup.zpowers (x ^ 3)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kSub V H E)).to_le
      (Subgroup.zpowers_le.mpr hxJ)
  obtain ⟨k, hk⟩ := hzp.exists_orderOf_eq_pow
    (⟨x ^ 3, Subgroup.mem_zpowers (x ^ 3)⟩ : ↥(Subgroup.zpowers (x ^ 3)))
  have hk' : orderOf (x ^ 3) = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨x ^ 3, Subgroup.mem_zpowers (x ^ 3)⟩ :
      ↥(Subgroup.zpowers (x ^ 3)))).trans hk
  have hodd3 : Odd (orderOf (x ^ 3)) := hodd.of_dvd_nat (orderOf_pow_dvd 3)
  have hk0 : k = 0 := by
    by_contra hkne
    have heven : Even (orderOf (x ^ 3)) := by
      rw [hk']
      exact Even.pow_of_ne_zero even_two hkne
    exact Nat.not_even_iff_odd.mpr hodd3 heven
  have hx3 : x ^ 3 = 1 := by
    have h1 : orderOf (x ^ 3) = 1 := by rw [hk', hk0, pow_zero]
    exact orderOf_eq_one_iff.mp h1
  have hcube : (d * e) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]
    exact hx3
  have hord3 : orderOf (d * e) = 3 := by
    have hdvd3 : orderOf (d * e) ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
    have hne1 : orderOf (d * e) ≠ 1 := by
      intro h1
      have h1' : d * e = 1 := orderOf_eq_one_iff.mp h1
      have h2 : φ d * φ e = 1 := by rw [← map_mul, h1', map_one]
      rw [h2] at h3
      norm_num at h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have hinf : U ⊓ W = ⊥ := by
    have hUW : U ≠ W := by
      intro heq
      obtain ⟨hdne, hd2, hdmem, -⟩ := triaAmb_bar_eq_zpowers h hφ hS hU hd hd1
      obtain ⟨hene, -, -, -⟩ := triaAmb_bar_eq_zpowers h hφ hS hW he he1
      have heU : φ e ∈ barSub (kSub V H E) φ U := by
        rw [heq]
        exact mem_barSub.mpr ⟨e, he, rfl⟩
      have hcard : Nat.card (barSub (kSub V H E) φ U) = 2 :=
        card_barSub_of_mem_omegaSet h hφ hS hU
      have heqd : φ e = φ d := seven_eleven_small_eq_of_mem hcard hdmem hdne heU hene
      have h1 : φ d * φ e = 1 := by rw [heqd, ← pow_two]; exact hd2
      rw [h1] at h3
      norm_num at h3
    obtain ⟨a, -, hUa⟩ := h.transitive U hU
    obtain ⟨b, -, hWb⟩ := h.transitive W hW
    rcases inf_conjSubgroup_eq_bot_or_eq h.ti a b with hbot | heq
    · rwa [hUa, hWb]
    · exact absurd (hUa.trans (heq.trans hWb.symm)) hUW
  exact ⟨hord3, hinf⟩

end CFSG.LocalAnalysis.WeakClosure81.SevenElevenTri
