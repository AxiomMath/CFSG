module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKFactsBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenThirteen
public import CFSG.LargeExtraspecial.S97RZStar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

private theorem barSub_eq_bot_of_le_ker {K J : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K J φ) {A : Subgroup G} (hA : A ≤ K) (hAJ : A ≤ J) :
    barSub K φ A = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨a, haA, hax⟩ := mem_barSub.mp hx
  rw [← hax]
  exact (hφ.ker_iff a).mpr (hAJ haA)

private theorem conj_commutatorElement (k u r : G) :
    k⁻¹ * ⁅k * u * k⁻¹, k * r * k⁻¹⁆ * k = ⁅u, r⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  group

theorem fusionOddCore_le_center_of_two_lt_card (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hbig : 2 < Nat.card (barSub (kSub V H E) φ V)) :
    fusionOddCore X ≤ Subgroup.center X := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let K : Subgroup G := kSub V H E
  let J : Subgroup G := pCoreOf 2 K
  have hJleK : J ≤ K := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) K
  have hKleH : K ≤ H := kSub_le_of_forall_le h.omega_le
  have hJleH : J ≤ H := hJleK.trans hKleH
  have hKNJ : K ≤ Subgroup.normalizer (J : Set G) :=
    hKleH.trans (le_normalizer_of_subgroupOf_normal hJleH h.jnormal)
  let O : Subgroup X := fusionOddCore X
  let R : Subgroup G := (O.comap φ).map K.subtype
  have hRleK : R ≤ K := Subgroup.map_subtype_le _
  have hRsub : R.subgroupOf K = O.comap φ := by
    change ((O.comap φ).map K.subtype).comap K.subtype = O.comap φ
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hRnormK : (R.subgroupOf K).Normal := by
    rw [hRsub]
    exact Subgroup.Normal.comap (fusionOddCore_normal X) φ
  have hKN : K ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_of_subgroupOf_normal hRleK hRnormK
  have hVN : V ≤ Subgroup.normalizer (R : Set G) := (le_kSub h.mem).trans hKN
  have hbarR : barSub K φ R = O := by
    change (R.subgroupOf K).map φ = O
    rw [hRsub]
    exact Subgroup.map_comap_eq_self_of_surjective hφ.surjective O
  have hJleR : J ≤ R := by
    intro j hj
    have hjK : j ∈ K := hJleK hj
    have hphi : φ ⟨j, hjK⟩ = 1 := (hφ.ker_iff ⟨j, hjK⟩).mpr (by simpa using hj)
    have hmem : (⟨j, hjK⟩ : ↥K) ∈ O.comap φ := by
      rw [Subgroup.mem_comap, hphi]
      exact O.one_mem
    exact Subgroup.mem_map.mpr ⟨⟨j, hjK⟩, hmem, rfl⟩
  have hcardR : Nat.card (barSub K φ R) = J.relIndex R :=
    card_barSub_eq_relIndex_of_isBarMap hRleK hJleK hφ
  have hcardV : Nat.card (barSub K φ V) = J.relIndex V :=
    card_barSub_eq_relIndex_of_isBarMap (le_kSub h.mem) hJleK hφ
  have hoddO : Odd (Nat.card O) :=
    Nat.coprime_two_left.mp (CFSG.LargeExtraspecial.S9.coprime_card_fusionOddCore (K := X))
  have hRodd : Odd (J.relIndex R) := by
    rw [← hcardR, hbarR]
    exact hoddO
  have hVbig : 2 < J.relIndex V := by
    rw [← hcardV]
    exact hbig
  have hcommVR : ⁅V, R⁆ ≤ J :=
    seven_three_five h.elemAbelian h.ti h.abelian h.le h.normal h.mem h.omega_le
      h.pcore_le h.jnormal h.iSub_le hVbig hJleR (hRleK.trans hKleH) hVN hRodd
  have hcomm_conj : ∀ k : ↥K, ⁅conjSubgroup V (k : G), R⁆ ≤ J := by
    intro k
    rw [Subgroup.commutator_le]
    intro u hu r hr
    have hku : (k : G) * u * (k : G)⁻¹ ∈ V := mem_conjSubgroup_iff.mp hu
    have hkr : (k : G) * r * (k : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp (hKN k.2) r).mp hr
    have hmem : ⁅(k : G) * u * (k : G)⁻¹, (k : G) * r * (k : G)⁻¹⁆ ∈ J :=
      hcommVR (Subgroup.commutator_mem_commutator hku hkr)
    have hJinv : (k : G)⁻¹ * ⁅(k : G) * u * (k : G)⁻¹,
        (k : G) * r * (k : G)⁻¹⁆ * (k : G) ∈ J := by
      have h := (Subgroup.mem_normalizer_iff.mp (hKNJ (K.inv_mem k.2))
        ⁅(k : G) * u * (k : G)⁻¹, (k : G) * r * (k : G)⁻¹⁆).mp hmem
      simpa using h
    rw [conj_commutatorElement] at hJinv
    exact hJinv
  have hcentC : ∀ U ∈ omegaSet V H E,
      U.subgroupOf K ≤ (Subgroup.centralizer (O : Set X)).comap φ := by
    intro U hU
    obtain ⟨k0, hk0, hUk⟩ := h.transitive U hU
    intro x hx
    have hxU : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro o ho
    have ho' : o ∈ barSub K φ R := by rw [hbarR]; exact ho
    obtain ⟨r, hrR, hrφ⟩ := mem_barSub.mp ho'
    have hxU' : (x : G) ∈ conjSubgroup V (k0 : G) := by rw [← hUk]; exact hxU
    have hcommxr : ⁅(x : G), (r : G)⁆ ∈ J :=
      Subgroup.commutator_le.mp (hcomm_conj ⟨k0, hk0⟩) (x : G) hxU' (r : G) hrR
    have hphi : φ ⁅x, r⁆ = 1 :=
      (hφ.ker_iff ⁅x, r⁆).mpr (by
        simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hcommxr)
    have hcommphi : ⁅φ x, o⁆ = 1 := by
      rw [← hrφ, ← map_commutatorElement, hphi]
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommphi).symm
  have hCtop : (Subgroup.centralizer (O : Set X)).comap φ = ⊤ := by
    apply le_antisymm le_top
    have hKle : K ≤ ((Subgroup.centralizer (O : Set X)).comap φ).map K.subtype := by
      change kSub V H E ≤ ((Subgroup.centralizer (O : Set X)).comap φ).map K.subtype
      refine iSup₂_le fun U hU => ?_
      intro u hu
      refine Subgroup.mem_map.mpr ⟨⟨u, le_kSub hU hu⟩, ?_, rfl⟩
      exact hcentC U hU (Subgroup.mem_subgroupOf.mpr hu)
    intro x _
    have hxmap : (x : G) ∈ ((Subgroup.centralizer (O : Set X)).comap φ).map K.subtype :=
      hKle x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    exact hy
  have hcenttop : Subgroup.centralizer (O : Set X) = ⊤ := by
    have hmap := Subgroup.map_comap_eq_self_of_surjective hφ.surjective
      (Subgroup.centralizer (O : Set X))
    rw [hCtop, Subgroup.map_top] at hmap
    rw [MonoidHom.range_eq_top.mpr hφ.surjective] at hmap
    exact hmap.symm
  exact Subgroup.centralizer_eq_top_iff_subset.mp hcenttop

theorem isTI_barSub (h : Hyp711 V H E) {X : Type} [Group X] {φ : ↥(kSub V H E) →* X}
    (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) :
    IsTI (barSub (kSub V H E) φ V) := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let K : Subgroup G := kSub V H E
  let J : Subgroup G := pCoreOf 2 K
  have hJleK : J ≤ K := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) K
  have hKleH : K ≤ H := kSub_le_of_forall_le h.omega_le
  let T : Subgroup X := barSub K φ V
  have hT : T = barSub K φ V := rfl
  change IsTI T
  intro g
  obtain ⟨k, rfl⟩ := hφ.surjective g
  by_cases hbot : T ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup (φ k) T = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hwV : (w : X) ∈ T := (Subgroup.mem_inf.mp w.2).1
    have hwC : (w : X) ∈ CFSG.CGT.Timmesfeld75.conjSubgroup (φ k) T :=
      (Subgroup.mem_inf.mp w.2).2
    have hwne' : (w : X) ≠ 1 := fun h => hwne (Subtype.ext h)
    have hwC' : (w : X) ∈ conjSubgroup T (φ k)⁻¹ := by
      rw [← t75_conjSubgroup_eq]
      exact hwC
    have hwT : (φ k)⁻¹ * (w : X) * (φ k) ∈ T := by
      simpa using mem_conjSubgroup_iff.mp hwC'
    obtain ⟨a, haV, haφ⟩ := mem_barSub.mp hwV
    obtain ⟨b, hbV, hbφ⟩ := mem_barSub.mp hwT
    have haJ : (a : G) ∉ J := by
      intro haJ'
      exact hwne' (by rw [← haφ]; exact (hφ.ker_iff a).mpr haJ')
    let a'K : ↥K := k * b * k⁻¹
    have ha' : (a'K : G) ∈ conjSubgroup V (k : G)⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have hkey : (k : G)⁻¹ * (a'K : G) * ((k : G)⁻¹)⁻¹ = (b : G) := by
        change (k : G)⁻¹ * ((k : G) * (b : G) * (k : G)⁻¹) * ((k : G)⁻¹)⁻¹ = (b : G)
        group
      rw [hkey]
      exact hbV
    have hphi_a' : φ a'K = (w : X) := by
      change φ (k * b * k⁻¹) = (w : X)
      rw [map_mul, map_mul, map_inv, hbφ]
      group
    have haJ' : (a : G)⁻¹ * (a'K : G) ∈ J := by
      have h1 : φ (a⁻¹ * a'K) = 1 := by
        rw [map_mul, map_inv, haφ, hphi_a']
        group
      simpa using (hφ.ker_iff (a⁻¹ * a'K)).mp h1
    obtain ⟨y, hyJ, hyEq⟩ :=
      seven_three_four_ti h.elemAbelian h.ti h.abelian h.le h.normal h.mem h.omega_le
        h.pcore_le h.jnormal h.iSub_le (h := (k : G)⁻¹) (hKleH (K.inv_mem k.2))
        haV haJ ha' haJ'
    have hbar1 : barSub K φ (conjSubgroup V (k : G)⁻¹) = conjSubgroup T (φ k)⁻¹ := by
      have hh := barSub_conjSubgroup (K := K) φ V k⁻¹
      simpa [hT] using hh
    have hbar2 : barSub K φ (conjSubgroup V y) = T := by
      have hphi_y : φ (⟨y, hJleK hyJ⟩ : ↥K) = 1 := (hφ.ker_iff _).mpr hyJ
      have hh := barSub_conjSubgroup (K := K) φ V ⟨y, hJleK hyJ⟩
      simpa [hT, hphi_y, CFSG.Quasithin.conjSubgroup_one] using hh
    have hconj : conjSubgroup T (φ k)⁻¹ = T :=
      calc conjSubgroup T (φ k)⁻¹ = barSub K φ (conjSubgroup V (k : G)⁻¹) := hbar1.symm
        _ = barSub K φ (conjSubgroup V y) := by rw [hyEq]
        _ = T := hbar2
    have hconjT : CFSG.CGT.Timmesfeld75.conjSubgroup (φ k) T = T := by
      rw [t75_conjSubgroup_eq]
      exact hconj
    rw [hconjT]
    exact inf_eq_left.mpr le_rfl

theorem normalClosure_barSub_eq_top (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) :
    Subgroup.normalClosure (barSub (kSub V H E) φ V : Set X) = ⊤ := by
  let K : Subgroup G := kSub V H E
  let T : Subgroup X := barSub K φ V
  have hT : T = barSub K φ V := rfl
  let N : Subgroup X := Subgroup.normalClosure (T : Set X)
  have hN : N = Subgroup.normalClosure (T : Set X) := rfl
  have hNnorm : N.Normal := by rw [hN]; exact Subgroup.normalClosure_normal
  have hNconj : ∀ g : X, conjSubgroup N g = N := by
    intro g
    rw [conjSubgroup_eq_iff_mem_normalizer, Subgroup.normalizer_eq_top_iff.mpr hNnorm]
    exact Subgroup.mem_top g
  have hNle : T ≤ N := by rw [hN]; exact Subgroup.subset_normalClosure
  have hKle : K ≤ (N.comap φ).map K.subtype := by
    change kSub V H E ≤ (N.comap φ).map K.subtype
    refine iSup₂_le fun U hU => ?_
    obtain ⟨k, hk, hUk⟩ := h.transitive U hU
    have hbarU : barSub K φ U = conjSubgroup T (φ ⟨k, hk⟩) := by
      rw [hUk]
      simpa [hT] using barSub_conjSubgroup (K := K) φ V ⟨k, hk⟩
    have hleN : barSub K φ U ≤ N := by
      rw [hbarU]
      calc conjSubgroup T (φ ⟨k, hk⟩) ≤ conjSubgroup N (φ ⟨k, hk⟩) :=
            Subgroup.map_mono hNle
        _ = N := hNconj (φ ⟨k, hk⟩)
    intro u hu
    refine Subgroup.mem_map.mpr ⟨⟨u, le_kSub hU hu⟩, ?_, rfl⟩
    exact hleN (mem_barSub.mpr ⟨⟨u, le_kSub hU hu⟩, hu, rfl⟩)
  have hcomap : N.comap φ = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have hxmap : (x : G) ∈ (N.comap φ).map K.subtype := hKle x.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmap
    have hyx' : y = x := Subtype.ext hyx
    rw [hyx'] at hy
    exact hy
  have hmap := Subgroup.map_comap_eq_self_of_surjective hφ.surjective N
  rw [hcomap, Subgroup.map_top, MonoidHom.range_eq_top.mpr hφ.surjective] at hmap
  exact hmap.symm

theorem two_le_card_barSub (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) :
    2 ≤ Nat.card (barSub (kSub V H E) φ V) := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let K : Subgroup G := kSub V H E
  let J : Subgroup G := pCoreOf 2 K
  have hnle : ¬ V ≤ J := not_le_pCoreOf_kSub h
  obtain ⟨v, hvV, hvJ⟩ := Set.not_subset.mp hnle
  have hvK : v ∈ K := le_kSub h.mem hvV
  have hmem : φ ⟨v, hvK⟩ ∈ barSub K φ V := mem_barSub.mpr ⟨⟨v, hvK⟩, hvV, rfl⟩
  have hne1 : φ ⟨v, hvK⟩ ≠ 1 := by
    intro h1
    exact hvJ ((hφ.ker_iff ⟨v, hvK⟩).mp h1)
  have hnebot : barSub K φ V ≠ ⊥ := by
    intro hbot
    exact hne1 (Subgroup.mem_bot.mp (hbot ▸ hmem))
  have h1lt : 1 < Nat.card (barSub K φ V) :=
    (Subgroup.one_lt_card_iff_ne_bot (H := barSub K φ V)).mpr hnebot
  exact Nat.succ_le_of_lt h1lt


theorem isPGroup_barSub_sup_conj_iff (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (k : ↥(kSub V H E)) :
    IsPGroup 2 ↥(barSub (kSub V H E) φ V ⊔
        conjSubgroup (barSub (kSub V H E) φ V) (φ k)) ↔
      ⁅V, conjSubgroup V (k : G)⁆ = ⊥ := by
  let K : Subgroup G := kSub V H E
  let J : Subgroup G := pCoreOf 2 K
  have hJleK : J ≤ K := CFSG.LieType.BorelTits.pCoreOf_le (r := 2) K
  have hKleH : K ≤ H := kSub_le_of_forall_le h.omega_le
  have hVK : V ≤ K := le_kSub h.mem
  have hVkK : conjSubgroup V (k : G) ≤ K := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hx' : (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem k.2) (hVK hx)) k.2
    rwa [show (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) = x by group] at hx'
  have hbarVk : barSub K φ (conjSubgroup V (k : G)) =
      conjSubgroup (barSub K φ V) (φ k) := by
    simpa using barSub_conjSubgroup (K := K) φ V k
  constructor
  · intro hP
    let P : Subgroup G := V ⊔ conjSubgroup V (k : G) ⊔ J
    have hPdef : P = V ⊔ conjSubgroup V (k : G) ⊔ J := rfl
    have hPK : P ≤ K := sup_le (sup_le hVK hVkK) hJleK
    have hJbot : barSub K φ J = ⊥ := barSub_eq_bot_of_le_ker hφ hJleK le_rfl
    have hbarP : barSub K φ P =
        barSub K φ V ⊔ conjSubgroup (barSub K φ V) (φ k) := by
      rw [hPdef, barSub_sup (sup_le hVK hVkK) hJleK φ, barSub_sup hVK hVkK φ,
        hbarVk, hJbot, sup_bot_eq]
    have hmap2 : IsPGroup 2 ((P.subgroupOf K).map φ) := by
      rw [show (P.subgroupOf K).map φ = barSub K φ P from rfl, hbarP]
      exact hP
    have hker : φ.ker = J.subgroupOf K := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact hφ.ker_iff x
    have hJ2 : IsPGroup 2 J := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
    have hker2 : IsPGroup 2 φ.ker := by
      rw [hker]
      exact hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe hJleK).symm
    have hcomap2 : IsPGroup 2 (((P.subgroupOf K).map φ).comap φ) :=
      IsPGroup.comap_of_ker_isPGroup hmap2 φ hker2
    have hPsub : IsPGroup 2 (P.subgroupOf K) :=
      hcomap2.to_le (Subgroup.le_comap_map φ (P.subgroupOf K))
    have hP2 : IsPGroup 2 P := hPsub.of_equiv (Subgroup.subgroupOfEquivOfLe hPK)
    have hcomm := seven_three_one h.elemAbelian h.ti h.abelian h.le h.normal h.mem h.omega_le
      h.pcore_le h.jnormal (h := (k : G)) (hKleH k.2) (by simpa [hPdef] using hP2)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcomm u hu v hv).symm
  · intro hcomm
    have hVp : IsPGroup 2 V :=
      CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian h.elemAbelian
    have hVkp : IsPGroup 2 (conjSubgroup V (k : G)) :=
      CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian
        (isElemAbelian_conjSubgroup' h.elemAbelian (k : G))
    have hle_cent : V ≤ Subgroup.centralizer (conjSubgroup V (k : G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hnorm : V ≤ Subgroup.normalizer (conjSubgroup V (k : G) : Set G) :=
      hle_cent.trans (Subgroup.centralizer_le_normalizer _)
    have hsup2 : IsPGroup 2 (V ⊔ conjSubgroup V (k : G) : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hVp hVkp hnorm
    have hbarP : barSub K φ (V ⊔ conjSubgroup V (k : G)) =
        barSub K φ V ⊔ conjSubgroup (barSub K φ V) (φ k) := by
      rw [barSub_sup hVK hVkK φ, hbarVk]
    have hPsub : IsPGroup 2 ((V ⊔ conjSubgroup V (k : G)).subgroupOf K) :=
      hsup2.of_equiv (Subgroup.subgroupOfEquivOfLe (sup_le hVK hVkK)).symm
    rw [← hbarP]
    exact hPsub.map φ

end CFSG.LocalAnalysis.WeakClosure81
