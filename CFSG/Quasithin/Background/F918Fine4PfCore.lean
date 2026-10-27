module

public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Background.FFC4Small1
public import CFSG.Quasithin.EmptyFaithful.LRed3Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace F918Fine4Pf

section Order

variable {W : Type} [CommGroup W]

theorem false_of_d310Two_of_card {T L : Subgroup (MulAut W)} {U : Subgroup W}
    (h : D310Two T L U) (hc : Nat.card L = 7560 ∨ Nat.card L = 1080) : False := by
  have h16 : ¬ 2 ^ 4 ∣ Nat.card L := by
    rcases hc with hc | hc <;> rw [hc] <;> norm_num
  have hbig : 1080 ≤ Nat.card L := by rcases hc with hc | hc <;> omega
  obtain ⟨hcases, -, -⟩ := h
  rcases hcases with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  ·
    have hn := FFC.one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX0 : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [hX0, card_statedSL_three1527d, hK, ← pow_mul, ← pow_mul]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [hX] at hbig
      norm_num at hbig
    · exact h16 (hX ▸ Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _)
  ·
    have hn := FFC.one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX0 : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
      rw [hX0, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, hI,
        Finset.prod_pair (by norm_num), ← pow_mul, ← pow_mul, ← pow_mul]
      norm_num
    exact h16 (hX ▸ Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _)
  ·
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 6))) π hπ.1
    rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    have h1 : Nat.card ↥L ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 K) :=
      Subgroup.card_dvd_of_surjective (f := π) hπ.1
    rw [card_statedSL1527d (d := 4) (by norm_num), hK] at h1
    norm_num [Finset.prod_Icc_succ_top] at h1
    rcases hc with hc | hc <;> rw [hc] at h1 <;> norm_num at h1
  ·
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX : Nat.card L = Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    rw [hX, card_statedSL1527d (d := 5) (by norm_num), hK] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
  ·
    have h1 : Nat.card ↥L ∣ Nat.card ↥(alternatingGroup (Fin 7)) :=
      Subgroup.card_dvd_of_surjective (f := π) hπ.1
    rw [card_alternatingGroup1527d 7 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    rcases hc with hc | hc <;> rw [hc] at h1 <;> norm_num at h1

end Order

structure HatMod {W : Type} [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W))
    (V : Subgroup W) (Q : Type) [Group Q] : Prop where
  std : D3Std M Mp T L V
  mp : Mp = L
  stab : T ≤ stabSub V
  q : qOf (autSub (Mp ⊔ T) (orbSup T V)) ≤ ((2 : ℚ) : WithTop ℚ)
  fix : V ⊓ fixV L = ⊥
  faith : L ⊓ centSub V = ⊥
  iso : Nonempty (↥(autSub L V) ≃* Q)

section Core

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

@[expose] noncomputable def HatCore (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    Prop :=
  haveI := factElem h hIU
  HatMod (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I) ↥(autIH V₁ Vp H K) ∧
    (toAutI h I).ker = (toAutI h Vp).ker

theorem hatCore_of (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hK : conjClosure K T = K)
    (h310 : D310) (h391 : D391) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU h I W)
    (hfpf : ∀ u ∈ I, (∀ x : ↥K, toAutI h Vp x ∈ Subgroup.center ↥(autIH V₁ Vp H K) →
      (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ V₁) → u ∈ V₁)
    (hq : CFSG.IsQuasisimple ↥(autIH V₁ Vp H K))
    (hZ3 : Nat.card (Subgroup.center ↥(autIH V₁ Vp H K)) = 3)
    (hcard : Nat.card ↥(autIH V₁ Vp H K) = 7560 ∨ Nat.card ↥(autIH V₁ Vp H K) = 1080) :
    T ≤ Subgroup.normalizer (I : Set G) ∧ HatCore h hIU := by
  have hFI := factElem h hIU
  have hFU := factElem h (le_conjClosure Vp H)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hTH : T ≤ H := h.T_le_H
  have hirrT := isIrrPlusTildeT_of_ambient h hIU W hW hirr
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirrT
  have hD := d31_of_hyp h hH hIU hV₁I hirr'
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK]
  have h4 := mod4_core h310 h391 hD hirr' hMp hA
  have hV₁N := h.H_le_normalizer_V₁
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH : H ≤ Subgroup.normalizer (conjClosure I H : Set G) := le_normalizer_conjClosure I H
  have hex : ∃ i ∈ I, i ∉ V₁ := by
    by_contra hcon
    push Not at hcon
    apply hnt
    intro k hk i hi
    have hiV : i ∈ V₁ := hcon i hi
    have h1 : k * i * k⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hV₁N (h.K₀_le_H hk)) i).mp hiV
    exact V₁.mul_mem h1 (V₁.inv_mem hiV)
  have hcontra : ¬ ∀ x : ↥K, toAutI h Vp x ∈ Subgroup.center ↥(autIH V₁ Vp H K) →
      ∀ a ∈ I, (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ V₁ := by
    intro hall
    obtain ⟨i, hi, hiV⟩ := hex
    exact hiV (hfpf i hi fun x hx => hall x hx i hi)
  have hcomm_of_fix : ∀ x : ↥K, (∀ a (ha : a ∈ I),
      (toAutI h I x : MulAut ↥(tildeOf V₁ (conjClosure I H)))
        (modMk hIHN a (le_conjClosure I H ha)) = modMk hIHN a (le_conjClosure I H ha)) →
      ∀ a ∈ I, (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ V₁ :=
    fun x hx a ha => h.commutator_mem_of_actH_fix hIU (x := Subgroup.inclusion hKH x)
      (le_conjClosure I H ha) (hx a ha)
  have hker : (toAutI h I).ker = (toAutI h Vp).ker := by
    refine le_antisymm (fun x hx => ?_) (toAutI_ker_le h hIU)
    have hcen : toAutI h Vp x ∈ Subgroup.center ↥(autIH V₁ Vp H K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x', rfl⟩ := toAutI_surjective h Vp y
      have h1 := toAutI_comm h hIU hnt x hx x'
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : toAutI h Vp x * toAutI h Vp x' = toAutI h Vp x' * toAutI h Vp x := by
        have := congrArg (· * (toAutI h Vp x' * toAutI h Vp x)) h1
        simpa [mul_assoc] using this
      exact h2.symm
    by_contra hne
    apply hcontra
    intro x' hx'
    have hz1 : (⟨toAutI h Vp x, hcen⟩ : ↥(Subgroup.center ↥(autIH V₁ Vp H K))) ≠ 1 := by
      intro h0
      exact hne (MonoidHom.mem_ker.mpr (congrArg Subtype.val h0))
    have hgen := zpowers_eq_top_of_prime_card hZ3 hz1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (hgen ▸ Subgroup.mem_top (⟨toAutI h Vp x', hx'⟩ : ↥(Subgroup.center _)))
    have hn' : toAutI h Vp (x ^ n) = toAutI h Vp x' := by
      rw [map_zpow]
      exact congrArg Subtype.val hn
    have hmem : (x ^ n)⁻¹ * x' ∈ (toAutI h Vp).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hn', inv_mul_cancel]
    have hψ' := toAutI_ker_le h hIU hmem
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, MonoidHom.mem_ker.mp hx, one_zpow,
      inv_one, one_mul] at hψ'
    refine hcomm_of_fix x' fun a ha => ?_
    rw [hψ']
    rfl
  let e₁ : ↥(autIH V₁ I H K) ≃* ↥(autIH V₁ Vp H K) :=
    (QuotientGroup.quotientKerEquivOfSurjective (toAutI h I) (toAutI_surjective h I)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective (toAutI h Vp) (toAutI_surjective h Vp)))
  have he₁ : ∀ x : ↥K, e₁ (toAutI h I x) = toAutI h Vp x := by
    intro x
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective (toAutI h I)
        (toAutI_surjective h I)).symm (toAutI h I x) = (x : ↥K ⧸ (toAutI h I).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [e₁, MulEquiv.trans_apply, h1]
    rfl
  have hcenL : ∀ x : ↥K, toAutI h Vp x ∈ Subgroup.center ↥(autIH V₁ Vp H K) →
      toAutI h I x ∈ Subgroup.center ↥(autIH V₁ I H K) := by
    intro x hx
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    apply e₁.injective
    rw [map_mul, map_mul, he₁]
    exact hx (e₁ y)
  have hqL : CFSG.IsQuasisimple ↥(autIH V₁ I H K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm hq
  have hZL : Nat.card (Subgroup.center ↥(autIH V₁ I H K)) = 3 := by
    rw [← hZ3, ← Subgroup.map_center_eq e₁, Subgroup.card_map_of_injective e₁.injective]
  have hTI : T ≤ Subgroup.normalizer (I : Set G) := by
    rcases h4 with hst | (⟨hVT, -⟩ | h3)
    · rw [autIH_eq_map h (le_refl H)] at hst
      exact hTH.trans ((map_actH_le_stabSub_iff hV₁N hIHN hIH hV₁I).mp hst)
    · intro t ht
      have hst := le_stabSub_orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)
      rw [← hVT] at hst
      have hmem : actH hV₁N hIH ⟨t, hTH ht⟩ ∈ autIH V₁ I H T := by
        rw [autIH_eq_map h hTH]
        exact ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      exact (actH_mem_stabSub_subM_iff hV₁N hIHN hIH hV₁I (le_conjClosure I H)
        ⟨t, hTH ht⟩).mp (hst hmem)
    · exfalso
      have hcL : Nat.card ↥(autIH V₁ I H K) = Nat.card ↥(autIH V₁ Vp H K) :=
        Nat.card_congr e₁.toEquiv
      exact false_of_d310Two_of_card h3 (hcL ▸ hcard)
  have hTst : autIH V₁ I H T ≤ stabSub (subM V₁ (conjClosure I H) I) := by
    rw [autIH_eq_map h hTH]
    rintro _ ⟨t, ht, rfl⟩
    exact (actH_mem_stabSub_subM_iff hV₁N hIHN hIH hV₁I (le_conjClosure I H) t).mpr
      (hTI (Subgroup.mem_subgroupOf.mp ht))
  have hfixV : subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H K) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvI, hvfix⟩
    obtain ⟨a, haI, hav⟩ := mem_secImg.mp hvI
    have haIH : (a : G) ∈ conjClosure I H := le_conjClosure I H haI
    have hv : v = modMk hIHN (a : G) haIH := Subtype.ext hav.symm
    have haV : (a : G) ∈ V₁ := by
      refine hfpf a haI fun x _ => ?_
      have hfx : (toAutI h I x : MulAut ↥(tildeOf V₁ (conjClosure I H))) v = v :=
        hvfix _ (toAutI h I x).2
      rw [hv] at hfx
      exact h.commutator_mem_of_actH_fix hIU (x := Subgroup.inclusion hKH x) haIH hfx
    rw [Subgroup.mem_bot, hv]
    exact Subtype.ext ((secMk_eq_one_iff (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (x := ⟨(a : G), hIHN haIH⟩)).mpr haV)
  have hLs : autIH V₁ I H K ≤ stabSub (subM V₁ (conjClosure I H) I) := insp5a_le_stabSub hD
  have hρinj : Function.Injective (resHomOn (subM V₁ (conjClosure I H) I) hLs) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    obtain ⟨l₀, hl₀, v₀, hv₀, hlv₀⟩ := lred3_exists_ne hD hMp
    have hne : ∃ k, resHomOn (subM V₁ (conjClosure I H) I) hLs k ≠ 1 := by
      refine ⟨⟨l₀, hl₀⟩, fun h1 => hlv₀ ?_⟩
      exact congrArg (fun φ : MulAut ↥(subM V₁ (conjClosure I H) I) =>
        ((φ ⟨v₀, hv₀⟩ : ↥(subM V₁ (conjClosure I H) I)) : ↥(tildeOf V₁ (conjClosure I H)))) h1
    have hlZ : l ∈ Subgroup.center ↥(autIH V₁ I H K) :=
      CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqL hne hl
    have hlc : (l : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
        centSub (subM V₁ (conjClosure I H) I) := by
      intro v hv
      have h1 := congrArg (fun φ : MulAut ↥(subM V₁ (conjClosure I H) I) =>
        ((φ ⟨v, hv⟩ : ↥(subM V₁ (conjClosure I H) I)) : ↥(tildeOf V₁ (conjClosure I H))))
        (MonoidHom.mem_ker.mp hl)
      exact h1
    rw [Subgroup.mem_bot]
    by_contra hl1
    apply hcontra
    intro x hx
    have hz1 : (⟨l, hlZ⟩ : ↥(Subgroup.center ↥(autIH V₁ I H K))) ≠ 1 := by
      intro h0
      exact hl1 (congrArg Subtype.val h0)
    have hgen := zpowers_eq_top_of_prime_card hZL hz1
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (hgen ▸ Subgroup.mem_top (⟨toAutI h I x, hcenL x hx⟩ : ↥(Subgroup.center _)))
    have hn' : l ^ n = toAutI h I x := congrArg Subtype.val hn
    have hxc : (toAutI h I x : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
        centSub (subM V₁ (conjClosure I H) I) := by
      rw [← hn', Subgroup.coe_zpow]
      exact zpow_mem hlc n
    refine hcomm_of_fix x fun a ha => hxc _ ?_
    exact (modMk_mem_subM_iff hIHN hV₁I (le_conjClosure I H ha)).mpr ha
  have hfaith : autIH V₁ I H K ⊓ centSub (subM V₁ (conjClosure I H) I) = ⊥ := by
    rw [eq_bot_iff]
    rintro l ⟨hlL, hlc⟩
    have h1 : resHomOn (subM V₁ (conjClosure I H) I) hLs ⟨l, hlL⟩ = 1 :=
      MulEquiv.ext fun v => Subtype.ext (hlc v v.2)
    have h2 := hρinj (h1.trans (map_one _).symm)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h2)
  let e₂ : ↥(autSub (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) ≃* ↥(autIH V₁ I H K) :=
    (MulEquiv.subgroupCongr (autSub_eq_range_resHomOn hLs)).trans
      (MonoidHom.ofInjective hρinj).symm
  refine ⟨hTI, ?_⟩
  show HatMod (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
      (autIH V₁ I H K) (subM V₁ (conjClosure I H) I) ↥(autIH V₁ Vp H K) ∧
    (toAutI h I).ker = (toAutI h Vp).ker
  exact
    ⟨{ std := ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
       mp := hMp
       stab := hTst
       q := hA.qOf_VT hD.exp
       fix := hfixV
       faith := hfaith
       iso := ⟨e₂.trans e₁⟩ }, hker⟩

end Core

end F918Fine4Pf

end CFSG.Quasithin
