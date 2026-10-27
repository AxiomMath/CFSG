module

public import CFSG.RankThree.PartTwo.Sec17.C174Base

public section

namespace CFSG.RankThree.PartTwo.Sec17.C174

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem isSolvable_centralizer_image_L
    (h : Sec17Std G A c L Y₀) :
    Group.IsSolvable (Subgroup.centralizer
      ((((L.subgroupOf (nH c)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(nH c)))) :
        Subgroup (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c))) :
        Set (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c)))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLH : L ≤ nH c := le_nH_of_mem_lA h.toSec14Std
  have hHN : nH c ≤ Subgroup.normalizer (L : Set G) :=
    normalizer_zpowers_le_normalizer_L h.toSec14Std (three_dvd_card_L h.toSec14Std)
  have hc : c ∈ nH c := Subgroup.le_normalizer (Subgroup.mem_zpowers c)
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.le_centralizer_of_mem_thetaComponentsAt h.mem_lA.1
  have hcard3 : Nat.card (Subgroup.zpowers c) = 3 :=
    (CFSG.RankThree.PartTwo.Sec13.mem_omegaA_iff.mp h.zpowers_mem_omegaA).2.1
  have hord : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hcard3
  have hc3 : c ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have hcopR : Nat.Coprime 3 (Nat.card ↥(CFSG.pPrimeCore 3 ↥(nH c))) :=
    CFSG.pPrimeCore_coprime_card
  have hnd3R : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥(nH c)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcopR
  have hO : CFSG.pPrimeCore 3 (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c)) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  set ψ := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(nH c)) with hψ
  have hψiff : ∀ y : ↥(nH c), ψ y = 1 ↔ y ∈ CFSG.pPrimeCore 3 ↥(nH c) := fun y => by
    rw [hψ]
    exact QuotientGroup.eq_one_iff y
  obtain ⟨k, hk⟩ : ∃ k : ↥(nH c), (k : G) = c := ⟨⟨c, hc⟩, rfl⟩
  have hk3 : k ^ 3 = 1 := by
    apply Subtype.ext
    simp [hk, hc3]
  have hordk : orderOf k = 3 := by
    rw [← Subgroup.orderOf_coe, hk, hord]
  have hz3 : ψ k ^ 3 = 1 := by
    rw [← map_pow, hk3, map_one]
  have hz1 : ψ k ≠ 1 := by
    intro h1
    have hkR : k ∈ CFSG.pPrimeCore 3 ↥(nH c) := (hψiff k).mp h1
    have hdvd := orderOf_dvd_natCard (⟨k, hkR⟩ : ↥(CFSG.pPrimeCore 3 ↥(nH c)))
    rw [Subgroup.orderOf_mk, hordk] at hdvd
    exact hnd3R hdvd
  have hkN : (Subgroup.zpowers k).Normal := by
    constructor
    intro n hn g
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hgk : g * k * g⁻¹ ∈ Subgroup.zpowers k := by
      have hcg : (g : G) * c * (g : G)⁻¹ ∈ Subgroup.zpowers c :=
        (Subgroup.mem_normalizer_iff.mp g.2 c).mp (Subgroup.mem_zpowers c)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hcg
      refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
      apply Subtype.ext
      show (k : G) ^ j = (g : G) * (k : G) * (g : G)⁻¹
      rw [hk, hj]
    rw [← conj_zpow]
    exact zpow_mem hgk m
  have hzN : (Subgroup.zpowers (ψ k)).Normal := by
    rw [← MonoidHom.map_zpowers]
    exact hkN.map ψ (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥(nH c)))
  have hLnorm : (L.subgroupOf (nH c)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  set Lh : Subgroup (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c)) :=
    (L.subgroupOf (nH c)).map ψ with hLh
  haveI hLhN : Lh.Normal :=
    hLnorm.map ψ (QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥(nH c)))
  have hLhz : Lh ≤ Subgroup.centralizer ({ψ k} : Set (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c))) := by
    intro y hy
    rw [hLh] at hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hcu : c * (u : G) = (u : G) * c :=
      Subgroup.mem_centralizer_iff.mp (hLC (Subgroup.mem_subgroupOf.mp hu)) c (Set.mem_singleton c)
    have hku : k * u = u * k := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hk]
      exact hcu)
    rw [← map_mul, ← map_mul, hku]
  obtain ⟨T, hT⟩ : ∃ T : Subgroup G, T = (aschbacherSolvableCore 3 ↥L).map L.subtype :=
    ⟨_, rfl⟩
  have hTL : T ≤ L := by
    rw [hT]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hTH : T ≤ nH c := hTL.trans hLH
  have hconjT : ∀ d ∈ nH c, ∀ t ∈ T, d * t * d⁻¹ ∈ T := by
    intro d hd t ht
    rw [hT] at ht ⊢
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ht
    have hdL : d ∈ Subgroup.normalizer (L : Set G) := hHN hd
    set σ : MulAut ↥L := L.normalizerMonoidHom ⟨d, hdL⟩ with hσ
    have hσx : σ x ∈ aschbacherSolvableCore 3 ↥L := by
      have hm := Subgroup.mem_map_of_mem (σ : ↥L →* ↥L) hx
      rw [CFSG.RankThree.PartTwo.Sec4.map_aschbacherSolvableCore σ] at hm
      exact hm
    exact Subgroup.mem_map.mpr ⟨σ x, hσx, rfl⟩
  have hTnorm : nH c ≤ Subgroup.normalizer (T : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      exact hconjT d hd t ht
    · intro ht
      have h2 := hconjT d⁻¹ (inv_mem hd) _ ht
      have e2 : d⁻¹ * (d * t * d⁻¹) * d⁻¹⁻¹ = t := by group
      rw [e2] at h2
      exact h2
  have hT3 : ¬ 3 ∣ Nat.card T := by
    rw [hT, Subgroup.card_map_of_injective (Subgroup.subtype_injective L)]
    exact CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore
  have hN3 : Nat.Coprime 3 (Nat.card ↥(T.subgroupOf (nH c))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT3
  have hNnorm : (T.subgroupOf (nH c)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTH).mpr hTnorm
  have hTR : T.subgroupOf (nH c) ≤ CFSG.pPrimeCore 3 ↥(nH c) :=
    CFSG.le_pPrimeCore_of_normal_coprime hNnorm hN3
  have hmem : ∀ x : ↥L, (ψ.comp (Subgroup.inclusion hLH)) x ∈ Lh := by
    intro x
    rw [hLh]
    have hx : Subgroup.inclusion hLH x ∈ L.subgroupOf (nH c) :=
      Subgroup.mem_subgroupOf.mpr x.2
    exact Subgroup.mem_map_of_mem ψ hx
  set phi : ↥L →* ↥Lh := (ψ.comp (Subgroup.inclusion hLH)).codRestrict Lh hmem with hphi
  have key : ∀ x : ↥L, phi x = 1 ↔ Subgroup.inclusion hLH x ∈ CFSG.pPrimeCore 3 ↥(nH c) := by
    intro x
    rw [← hψiff]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  have hphisurj : Function.Surjective phi := by
    intro y
    have hy : (y : ↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c)) ∈ (L.subgroupOf (nH c)).map ψ := y.2
    obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨(u : G), Subgroup.mem_subgroupOf.mp hu⟩, ?_⟩
    apply Subtype.ext
    exact huy
  have hcardK : Nat.card phi.ker ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥(nH c)) := by
    have h1 : Nat.card (phi.ker.map (Subgroup.inclusion hLH)) = Nat.card phi.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hLH)
    rw [← h1]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact (key x).mp (MonoidHom.mem_ker.mp hx)
  have hnd3K : ¬ 3 ∣ Nat.card phi.ker := fun hd => hnd3R (dvd_trans hd hcardK)
  have hLbar := lBar_simple_and_pRank h.toSec14Std
  haveI hsimpLbar : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLbar.1
  have hdvdLbar : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥L)
    have h2 : 3 ∣ Nat.card ↥L := three_dvd_card_L h.toSec14Std
    rw [h1] at h2
    exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h2).resolve_right
      CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore
  have hmapbot : (phi.ker).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) = ⊥ :=
    b3_map_eq_bot_of_not_three_dvd hdvdLbar
      (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L)) hnd3K
  have hker : phi.ker = aschbacherSolvableCore 3 ↥L := by
    apply le_antisymm
    · intro x hx
      have hm := Subgroup.mem_map_of_mem (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) hx
      rw [hmapbot, Subgroup.mem_bot] at hm
      exact (QuotientGroup.eq_one_iff x).mp hm
    · intro x hx
      rw [MonoidHom.mem_ker, key]
      refine hTR ?_
      rw [Subgroup.mem_subgroupOf, hT]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have e : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* ↥Lh :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective phi hphisurj)
  haveI hsimpLh : IsSimpleGroup ↥Lh := e.symm.isSimpleGroup
  have hnaLh : ∃ a b : ↥Lh, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := lBar_nonabelian h.toSec14Std
    refine ⟨e a, e b, fun heq => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact heq
  have hZ : Subgroup.center ↥Lh = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Lh) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨a, b, hab⟩ := hnaLh
      apply hab
      have ha : a ∈ Subgroup.center ↥Lh := by
        rw [ht]
        exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
  have hcen : Lh ⊓ Subgroup.centralizer (Lh : Set (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxZ : (⟨x, hx.1⟩ : ↥Lh) ∈ Subgroup.center ↥Lh := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx.2 _ g.2
    rw [hZ, Subgroup.mem_bot] at hxZ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hxZ
  have hΛ : 2 ≤ CFSG.Open.pRank 3 Lh := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e.symm]
    exact hLbar.2
  have hΓ : CFSG.Open.pRank 3 (⊤ : Subgroup (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c))) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore 3 ↥(nH c)) hnd3R,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact pRank_three_le_three h h.normalizer_c_le
  exact isSolvable_centralizer_of_pRank_aux hO hz3 hz1 hzN hLhz hcen hΛ hΓ

@[expose] def SolvMod3' (D : Subgroup G) : Prop :=
  ∃ (N : Subgroup ↥D) (_ : N.Normal), ¬ 3 ∣ Nat.card N ∧ Group.IsSolvable (↥D ⧸ N)

theorem isSolvable_of_two_pow_mem {Δ : Type} [Group Δ] [Finite Δ] (K : Subgroup Δ) [K.Normal]
    [Group.IsSolvable K] (h2 : ∀ d : Δ, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) : Group.IsSolvable Δ := by
  have hp : IsPGroup 2 (Δ ⧸ K) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := h2 d
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  haveI : Group.IsNilpotent (Δ ⧸ K) := hp.isNilpotent
  haveI : Group.IsSolvable (Δ ⧸ K) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient K

theorem exists_pow_two_mem_of_sup {C T : Subgroup G}
    (hC : ∀ g ∈ C ⊔ T, ∀ x ∈ C, g * x * g⁻¹ ∈ C)
    (hT : ∀ t ∈ T, ∃ k : ℕ, t ^ (2 ^ k) = 1) :
    ∀ y ∈ C ⊔ T, ∃ k : ℕ, y ^ (2 ^ k) ∈ C := by
  have hdec : ∀ y ∈ C ⊔ T, ∃ u ∈ C, ∃ t ∈ T, y = u * t := by
    let P : Subgroup G :=
      { carrier := {g | ∃ u ∈ C, ∃ t ∈ T, g = u * t}
        mul_mem' := by
          rintro _ _ ⟨u₁, hu₁, t₁, ht₁, rfl⟩ ⟨u₂, hu₂, t₂, ht₂, rfl⟩
          exact ⟨u₁ * (t₁ * u₂ * t₁⁻¹), C.mul_mem hu₁ (hC t₁ (Subgroup.mem_sup_right ht₁) u₂ hu₂),
            t₁ * t₂, T.mul_mem ht₁ ht₂, by group⟩
        one_mem' := by
          show ∃ u ∈ C, ∃ t ∈ T, (1 : G) = u * t
          exact ⟨1, C.one_mem, 1, T.one_mem, by group⟩
        inv_mem' := by
          rintro _ ⟨u, hu, t, ht, rfl⟩
          have h1 := hC t⁻¹ ((C ⊔ T).inv_mem (Subgroup.mem_sup_right ht)) u⁻¹ (C.inv_mem hu)
          rw [inv_inv] at h1
          exact ⟨t⁻¹ * u⁻¹ * t, h1, t⁻¹, T.inv_mem ht, by group⟩ }
    have hle : C ⊔ T ≤ P :=
      sup_le (fun u hu => ⟨u, hu, 1, T.one_mem, by group⟩)
        (fun t ht => ⟨1, C.one_mem, t, ht, by group⟩)
    intro y hy
    obtain ⟨u, hu, t, ht, hyut⟩ := hle hy
    exact ⟨u, hu, t, ht, hyut⟩
  intro y hy
  obtain ⟨u, hu, t, ht, rfl⟩ := hdec y hy
  obtain ⟨k, hk⟩ := hT t ht
  have key : ∀ n : ℕ, ∃ c ∈ C, (u * t) ^ n = c * t ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, C.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc, hcn⟩ := ih
      refine ⟨c * (t ^ n * u * (t ^ n)⁻¹), C.mul_mem hc
        (hC (t ^ n) (pow_mem (Subgroup.mem_sup_right ht) n) u hu), ?_⟩
      rw [pow_succ, hcn, pow_succ]
      group
  obtain ⟨c, hc, hcn⟩ := key (2 ^ k)
  refine ⟨k, ?_⟩
  rw [hcn, hk, mul_one]
  exact hc

theorem solvMod3'_cQuot_sup_inf_nH
    (h : Sec17Std G A c L Y₀) {T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) : SolvMod3' ((cQuot Y₀ ⊔ T) ⊓ nH c) := by
  have hCN : cQuot Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := by
    intro a ha
    have ha' : a ∈ (cQuot Y₀ : Set G) := ha
    rw [coe_cQuot] at ha'
    exact ha'.1
  have hTN : T ≤ Subgroup.normalizer (Y₀ : Set G) := h.qStar_le T hT
  have hYN : cQuot Y₀ ⊔ T ≤ Subgroup.normalizer (Y₀ : Set G) := sup_le hCN hTN
  have hCY : ∀ g ∈ cQuot Y₀ ⊔ T, ∀ x ∈ cQuot Y₀, g * x * g⁻¹ ∈ cQuot Y₀ := by
    intro g hg x hx
    exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_cQuot Y₀ (hYN hg)) x).mp hx
  have hcommQ : ∀ x ∈ cQuot Y₀, ∀ y ∈ Y₀,
      x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y₀ := by
    intro x hx y hy
    have hx' : x ∈ (cQuot Y₀ : Set G) := hx
    rw [coe_cQuot] at hx'
    exact hx'.2 y hy
  have hT2 : ∀ t ∈ T, ∃ k : ℕ, t ^ (2 ^ k) = 1 := by
    intro t ht
    have hπ := hT.prop.2
    have hord : orderOf (⟨t, ht⟩ : ↥T) ∣ Nat.card ↥T := orderOf_dvd_natCard _
    have hpos : orderOf (⟨t, ht⟩ : ↥T) ≠ 0 := (orderOf_pos _).ne'
    have hform : orderOf (⟨t, ht⟩ : ↥T) =
        2 ^ (orderOf (⟨t, ht⟩ : ↥T)).primeFactorsList.length := by
      refine Nat.eq_prime_pow_of_unique_prime_dvd hpos ?_
      intro d hd hdvd
      exact hπ (Subtype.mk d hd : Nat.Primes) (hdvd.trans hord)
    refine ⟨(orderOf (⟨t, ht⟩ : ↥T)).primeFactorsList.length, ?_⟩
    have h1 : (⟨t, ht⟩ : ↥T) ^ (2 ^ (orderOf (⟨t, ht⟩ : ↥T)).primeFactorsList.length) = 1 := by
      rw [← hform]
      exact pow_orderOf_eq_one _
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have hdec := exists_pow_two_mem_of_sup hCY hT2
  have hHN : nH c ≤ Subgroup.normalizer (Y₀ : Set G) := h.normalizer_c_le
  have hQN : Subgroup.normalizer (Y₀ : Set G) ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have hQ2 : IsPGroup 2 ↥((CFSG.Open.pCoreOf 2 Y₀).subgroupOf (nH c)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀).comap_subtype
  have hQN' : ((CFSG.Open.pCoreOf 2 Y₀).subgroupOf (nH c)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
      hQN (hHN g.2)
    have := (Subgroup.mem_normalizer_iff.mp hg (n : G)).mp hn
    simpa using this
  have hQR : (CFSG.Open.pCoreOf 2 Y₀).subgroupOf (nH c) ≤ CFSG.pPrimeCore 3 ↥(nH c) := by
    obtain ⟨m, hm⟩ := isPGroup_iff_card_dvd_pow.mp hQ2
    have hcop : Nat.Coprime 3 (Nat.card ↥((CFSG.Open.pCoreOf 2 Y₀).subgroupOf (nH c))) :=
      Nat.Coprime.coprime_dvd_right hm (Nat.Coprime.pow_right m (by norm_num))
    exact CFSG.le_pPrimeCore_of_normal_coprime hQN' hcop
  have hDsub : (cQuot Y₀ ⊔ T) ⊓ nH c ≤ nH c := inf_le_right
  have hDC : ∀ d : ↥((cQuot Y₀ ⊔ T) ⊓ nH c), (d : G) ∈ cQuot Y₀ ⊔ T :=
    fun d => (Subgroup.mem_inf.mp d.2).1
  have hDH : ∀ d : ↥((cQuot Y₀ ⊔ T) ⊓ nH c), (d : G) ∈ nH c :=
    fun d => (Subgroup.mem_inf.mp d.2).2
  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ₁ : ↥((cQuot Y₀ ⊔ T) ⊓ nH c) →* ↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c),
      ψ₁ = (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(nH c))).comp (Subgroup.inclusion hDsub) :=
    ⟨_, rfl⟩
  have hψ_apply : ∀ x : ↥((cQuot Y₀ ⊔ T) ⊓ nH c),
      ψ₁ x = QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(nH c)) (Subgroup.inclusion hDsub x) := by
    intro x
    rw [hψ₁]
    rfl
  obtain ⟨Dh, hDh⟩ : ∃ Dh : Subgroup (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c)),
      Dh = Subgroup.centralizer ((((L.subgroupOf (nH c)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(nH c)))) :
        Subgroup (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c))) :
        Set (↥(nH c) ⧸ CFSG.pPrimeCore 3 ↥(nH c))) := ⟨_, rfl⟩
  have hDhS : Group.IsSolvable ↥Dh := by
    rw [hDh]
    exact isSolvable_centralizer_image_L h
  have hψDh : ∀ x : ↥((cQuot Y₀ ⊔ T) ⊓ nH c), (x : G) ∈ cQuot Y₀ → ψ₁ x ∈ Dh := by
    intro x hx
    rw [hDh, Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : s ∈ (L.subgroupOf (nH c)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(nH c))) :=
      hs
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hs'
    have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
    have hyY : (y : G) ∈ Y₀ := h.le_y0 hyL
    have hcm : ⁅Subgroup.inclusion hDsub x, y⁆ ∈ CFSG.pPrimeCore 3 ↥(nH c) := by
      refine hQR ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((⁅Subgroup.inclusion hDsub x, y⁆ : ↥(nH c)) : G) =
          (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ := by
        simp [commutatorElement_def]
      rw [e]
      exact hcommQ (x : G) hx (y : G) hyY
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(nH c)) ⁅Subgroup.inclusion hDsub x, y⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hcm
    rw [map_commutatorElement] at h1
    rw [hψ_apply]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  obtain ⟨KΓ, hKΓ⟩ : ∃ KΓ : Subgroup ↥((cQuot Y₀ ⊔ T) ⊓ nH c),
      KΓ = (cQuot Y₀ ⊓ nH c).subgroupOf ((cQuot Y₀ ⊔ T) ⊓ nH c) := ⟨_, rfl⟩
  have hKD : KΓ.Normal := by
    rw [hKΓ]
    refine ⟨fun x hx d => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hx' := Subgroup.mem_inf.mp hx
    have hdC : (d : G) ∈ cQuot Y₀ ⊔ T := hDC d
    have hdH : (d : G) ∈ nH c := hDH d
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_inf.mpr ⟨hCY (d : G) hdC (x : G) hx'.1,
      (nH c).mul_mem ((nH c).mul_mem hdH hx'.2) ((nH c).inv_mem hdH)⟩
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : Subgroup (↥((cQuot Y₀ ⊔ T) ⊓ nH c) ⧸ ψ₁.ker),
      K₁ = KΓ.map (QuotientGroup.mk' ψ₁.ker) := ⟨_, rfl⟩
  have hK₁n : K₁.Normal := by
    rw [hK₁]
    exact Subgroup.Normal.map hKD _ (QuotientGroup.mk'_surjective _)
  have hK₁s : Group.IsSolvable ↥K₁ := by
    let g₀ := (QuotientGroup.kerLift ψ₁).comp K₁.subtype
    have hg₀ : ∀ z : ↥K₁, g₀ z ∈ Dh := by
      rintro ⟨z, hz⟩
      have hz' := hz
      rw [hK₁] at hz'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz'
      show ψ₁ x ∈ Dh
      rw [hKΓ] at hx
      exact hψDh x (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
    let g₁ := g₀.codRestrict Dh hg₀
    have hinj : Function.Injective g₁ := by
      intro z w hzw
      have h1 : g₀ z = g₀ w := congrArg Subtype.val hzw
      exact Subtype.ext (QuotientGroup.kerLift_injective ψ₁ h1)
    exact Group.isSolvable_of_isSolvable_injective hinj
  unfold SolvMod3'
  refine ⟨ψ₁.ker, inferInstance, ?_, ?_⟩
  ·
    have hR3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥(nH c)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
    have hker : ψ₁.ker.map (Subgroup.inclusion hDsub) ≤ CFSG.pPrimeCore 3 ↥(nH c) := by
      rintro _ ⟨n, hn, rfl⟩
      have hn' : ψ₁ n = 1 := hn
      rw [hψ_apply] at hn'
      exact (QuotientGroup.eq_one_iff _).mp hn'
    have e1 : Nat.card (ψ₁.ker.map (Subgroup.inclusion hDsub)) = Nat.card ψ₁.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hDsub)
    intro h3
    apply hR3
    rw [← e1] at h3
    exact h3.trans (Subgroup.card_dvd_of_le hker)
  ·
    refine isSolvable_of_two_pow_mem K₁ ?_
    intro d
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨k, hk⟩ := hdec (γ : G) (hDC γ)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, hK₁]
    have hmem : γ ^ (2 ^ k) ∈ KΓ := by
      rw [hKΓ, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact Subgroup.mem_inf.mpr ⟨hk, pow_mem (hDH γ) _⟩
    exact Subgroup.mem_map_of_mem _ hmem

end CFSG.RankThree.PartTwo.Sec17.C174
