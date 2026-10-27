module

public import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy
public import CFSG.RankThree.PartTwo.Sec10.Step1012ClaimKProof
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTools

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

variable {Γ : Type} [Group Γ] [Finite Γ]

section PCoreCenter


theorem exists_pCore_center_eq_zpowers {K : Subgroup Γ} (hKq : IsQuasisimple ↥K)
    (hZK : Nat.card (Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K)) = 3) :
    ∃ z : Γ, z ∈ K ∧ K ≤ Subgroup.centralizer {z} ∧ orderOf z = 3 ∧
      inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hKq
    (aschbacherSolvableCore 3 ↥K) (Sec4.aschbacherSolvableCore_le_center hKq)
  have h3 : 3 ∣ Nat.card (Subgroup.center ↥K) := by
    have hdvd := Subgroup.card_map_dvd (Subgroup.center ↥K)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K))
    rw [← hcen, hZK] at hdvd
    exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥K)) 3 h3
  refine ⟨((x : ↥K) : Γ), (x : ↥K).2, ?_, ?_, ?_⟩
  · intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨k, hk⟩)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · have hKz : K ≤ Subgroup.centralizer {((x : ↥K) : Γ)} := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨k, hk⟩)
    have hzo : orderOf ((x : ↥K) : Γ) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    exact Sec10.Step1012ClaimKProof.pCore_center_eq_zpowers hKz (x : ↥K).2 hzo hZK

end PCoreCenter

section Commute

theorem mem_pCore_center_of_pow {K : Subgroup Γ} {w : Γ} (hwK : w ∈ K)
    (hwC : w ∈ Subgroup.centralizer (K : Set Γ)) {k : ℕ} (hwk : w ^ 3 ^ k = 1) :
    w ∈ inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := K ⊓ Subgroup.centralizer (K : Set Γ) with hZdef
  have hwZ : w ∈ Z := ⟨hwK, hwC⟩
  have hZcomm : ∀ u v : Z, u * v = v * u := fun u v =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp v.2.2 u u.2.1)
  refine ⟨⟨w, hwZ⟩, ?_, rfl⟩
  have hN : (Subgroup.zpowers (⟨w, hwZ⟩ : Z)).Normal :=
    ⟨fun n hn g => by rw [hZcomm g n, mul_inv_cancel_right]; exact hn⟩
  have hp : IsPGroup 3 (Subgroup.zpowers (⟨w, hwZ⟩ : Z)) := by
    have hord : orderOf (⟨w, hwZ⟩ : Z) ∣ 3 ^ k := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hwk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  exact (le_sSup ⟨hN, hp⟩ : Subgroup.zpowers _ ≤ CFSG.pCore 3 Z) (Subgroup.mem_zpowers _)

theorem commute_of_mem_normalizer {K : Subgroup Γ} {z a : Γ} (hzK : z ∈ K)
    (hKz : K ≤ Subgroup.centralizer {z}) (hz3 : orderOf z = 3)
    (hZ : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) =
      Subgroup.zpowers z)
    (ha : a ∈ Subgroup.normalizer (K : Set Γ)) (ha3 : a ^ 3 = 1) : a * z = z * a := by
  set w := a * z * a⁻¹ with hw
  have hwK : w ∈ K := (Subgroup.mem_normalizer_iff.mp ha z).mp hzK
  have hwC : w ∈ Subgroup.centralizer (K : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : a⁻¹ * k * a ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) k).mp hk
      simpa using this
    have hc : (a⁻¹ * k * a) * z = z * (a⁻¹ * k * a) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKz hk')
    calc k * w = a * ((a⁻¹ * k * a) * z) * a⁻¹ := by rw [hw]; group
      _ = a * (z * (a⁻¹ * k * a)) * a⁻¹ := by rw [hc]
      _ = w * k := by rw [hw]; group
  have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
  have hw3 : w ^ 3 ^ 1 = 1 := by
    rw [pow_one, hw, conj_pow, hz3']
    group
  have hwz := mem_pCore_center_of_pow hwK hwC hw3
  rw [hZ] at hwz
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hwz
  have hzm : ∀ n : ℤ, z ^ n = z ^ (n % 3) := fun n => by
    rw [← zpow_mod_orderOf, hz3]
    norm_num
  have hconj : ∀ n : ℤ, a * z ^ n * a⁻¹ = w ^ n := fun n => by
    rw [hw, conj_zpow]
  have hmod : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hmod with h0 | h1 | h2
  · exfalso
    have : w = 1 := by rw [← hm, hzm, h0, zpow_zero]
    have hz1 : z = 1 := by
      have h' : a * z * a⁻¹ = 1 := this
      calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
        _ = 1 := by rw [h']; group
    rw [hz1, orderOf_one] at hz3
    exact absurd hz3 (by norm_num)
  · have : w = z := by rw [← hm, hzm, h1, zpow_one]
    calc a * z = w * a := by rw [hw]; group
      _ = z * a := by rw [this]
  · exfalso
    have hwi : w = z⁻¹ := by
      rw [← hm, hzm, h2]
      rw [show (2 : ℤ) = 3 - 1 by norm_num, zpow_sub, zpow_one]
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hz3', one_mul]
    have h1 : a * z * a⁻¹ = z⁻¹ := hwi
    have h2' : a * z⁻¹ * a⁻¹ = z := by
      have := congrArg (·⁻¹) h1
      simpa [mul_assoc] using this
    have h3 : a ^ 3 * z * (a ^ 3)⁻¹ = z⁻¹ := by
      have e1 : a ^ 3 * z * (a ^ 3)⁻¹ = a * (a * (a * z * a⁻¹) * a⁻¹) * a⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
      rw [e1, h1, h2', h1]
    rw [ha3, one_mul, inv_one, mul_one] at h3
    have hz2 : z ^ 2 = 1 := by
      calc z ^ 2 = z * z := pow_two z
        _ = z * z⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel z
    have hd := orderOf_dvd_of_pow_eq_one hz2
    rw [hz3] at hd
    norm_num at hd

end Commute

section Transport

theorem isSubnormal_subgroupOf_subgroupOf {C M K : Subgroup Γ} (hMC : M ≤ C)
    (h : (K.subgroupOf M).IsSubnormal) :
    ((K.subgroupOf C).subgroupOf (M.subgroupOf C)).IsSubnormal := by
  let e : ↥(M.subgroupOf C) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMC
  have heq : (K.subgroupOf M).comap (e : ↥(M.subgroupOf C) →* ↥M) =
      (K.subgroupOf C).subgroupOf (M.subgroupOf C) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  rw [← heq]
  exact h.comap _

theorem subgroupOf_inf_centralizer {C L : Subgroup Γ} {d : Γ} (hdC : d ∈ C) :
    (L ⊓ Subgroup.centralizer {d}).subgroupOf C =
      L.subgroupOf C ⊓ Subgroup.centralizer {(⟨d, hdC⟩ : ↥C)} := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Subtype.ext h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, congrArg Subtype.val h2⟩

end Transport

section Center426


theorem isTripleCover_ON_of_center (h426 : Sec4.Item4_26ThetaA6)
    {C : Subgroup Γ} (hC4 : SectionFourHyp ↥C) (hCθ : aschbacherSolvableCore 3 ↥C = ⊥)
    {A L K : Subgroup Γ} {d : Γ} (hA : Late.IsE27 A) (hLA : L ⊔ A = C) (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hLq : IsQuasisimple ↥L) (hCL : C ≤ Subgroup.normalizer (L : Set Γ))
    (hLd : ¬ L ≤ Subgroup.centralizer {d}) (hKM : K ≤ L ⊓ Subgroup.centralizer {d})
    (hKsn : (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal)
    (hKq : IsQuasisimple ↥K) (hAK : A ≤ Subgroup.normalizer (K : Set Γ))
    (hA6 : IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)))
    (hZL : inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) ≤
      Subgroup.centralizer (L : Set Γ)) :
    IsTripleCover ↥L Blueprint.NativeSporadic.ON := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLC : L ≤ C := hLA ▸ le_sup_left
  have hAC : A ≤ C := hLA ▸ le_sup_right
  have hdC : d ∈ C := hAC hdA
  have hKL : K ≤ L := hKM.trans inf_le_left
  have hKC : K ≤ C := hKL.trans hLC
  have hKd : K ≤ Subgroup.centralizer {d} := hKM.trans inf_le_right
  obtain ⟨z, hzK, hKz, hz3, hZ⟩ := exists_pCore_center_eq_zpowers hKq hA6.1
  have hzZ : z ∈ inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set Γ)) :=
    hZ ▸ Subgroup.mem_zpowers z
  have hCz : C ≤ Subgroup.centralizer {z} := by
    rw [← hLA]
    refine sup_le (fun l hl => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hZL hzZ) l hl
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_of_mem_normalizer hzK hKz hz3 hZ (hAK ha) (hA.1.2 a ha)
  set L₀ : Subgroup ↥C := L.subgroupOf C with hL₀
  set K₀ : Subgroup ↥C := K.subgroupOf C with hK₀
  set d' : ↥C := ⟨d, hdC⟩ with hd'
  let eL : ↥L₀ ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  let eK : ↥K₀ ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKC
  have hL₀q : IsQuasisimple ↥L₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq
  have hL₀n : L₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hCL
  have hL₀c : IsComponent L₀ := ⟨hL₀q, hL₀n.isSubnormal⟩
  have hL₀θ : aschbacherSolvableCore 3 ↥L₀ = ⊥ :=
    RonanK429.theta_eq_bot_of_isComponent hCθ hL₀c
  have hL₀mem : L₀ ∈ thetaComponents 3 ↥C := mem_thetaComponents_of_isComponent3 hL₀c
  have hd'3 : orderOf d' = 3 := by
    rw [hd', Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hA.1.2 d hdA) hd1
  have hMeq := subgroupOf_inf_centralizer (L := L) hdC
  have hK₀M : K₀ ≤ L₀ ⊓ Subgroup.centralizer {d'} := by
    rw [← hMeq]
    exact Subgroup.subgroupOf_mono _ hKM
  have hK₀sn : (K₀.subgroupOf (L₀ ⊓ Subgroup.centralizer {d'})).IsSubnormal := by
    rw [← hMeq]
    exact isSubnormal_subgroupOf_subgroupOf (inf_le_left.trans hLC) hKsn
  have hK₀q : IsQuasisimple ↥K₀ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq
  have hK₀in : K₀ ∈ thetaComponentsIn (L₀ ⊓ Subgroup.centralizer {d'}) := by
    refine mem_thetaComponentsIn_iff.mpr ⟨hK₀M, mem_thetaComponents_of_isComponent3 ⟨?_, hK₀sn⟩⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hK₀M).symm
      hK₀q
  have hK₀A6 : IsTripleCover (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) (alternatingGroup (Fin 6)) :=
    Sec13.isTripleCover_of_mulEquiv (thetaQuotCongr eK.symm) hA6
  have hzC : z ∈ C := hKC hzK
  set z' : ↥C := ⟨z, hzC⟩ with hz'
  have hz'K : z' ∈ K₀ := hzK
  have hz'C : z' ∈ Subgroup.centralizer (K₀ : Set ↥C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKz hk))
  have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
  have hz'3 : z' ^ 3 ^ 1 = 1 := by
    rw [pow_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hz3')
  have hZne : inSubgroup (CFSG.pCore 3) (K₀ ⊓ Subgroup.centralizer (K₀ : Set ↥C)) ≠ ⊥ := by
    intro hbot
    have hmem := mem_pCore_center_of_pow hz'K hz'C hz'3
    rw [hbot, Subgroup.mem_bot] at hmem
    have : z = 1 := congrArg Subtype.val hmem
    rw [this, orderOf_one] at hz3
    exact absurd hz3 (by norm_num)
  have hZc : inSubgroup (CFSG.pCore 3) (K₀ ⊓ Subgroup.centralizer (K₀ : Set ↥C)) ≤
      Subgroup.center ↥C := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3)
      (G := ↥(K₀ ⊓ Subgroup.centralizer (K₀ : Set ↥C)))) ⟨w, hw⟩
    have hwk : (((w : ↥C) : Γ)) ^ 3 ^ k = 1 := by
      have := congrArg (fun u : CFSG.pCore 3 ↥(K₀ ⊓ Subgroup.centralizer (K₀ : Set ↥C)) =>
        (((u : ↥(K₀ ⊓ Subgroup.centralizer (K₀ : Set ↥C))) : ↥C) : Γ)) hk
      simpa using this
    have hwK : (((w : ↥C) : Γ)) ∈ K := w.2.1
    have hwCK : (((w : ↥C) : Γ)) ∈ Subgroup.centralizer (K : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      have hk'0 : (⟨k', hKC hk'⟩ : ↥C) ∈ K₀ := hk'
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp w.2.2 _ hk'0)
    have hwz := mem_pCore_center_of_pow hwK hwCK hwk
    rw [hZ] at hwz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : Γ) * ((w : ↥C) : Γ) = ((w : ↥C) : Γ) * (g : Γ)
    rw [← hm]
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hCz g.2)) m).eq
  rcases h426 ↥C hC4 L₀ hL₀mem d' hd'3 K₀ hK₀in hK₀A6 hZne hZc with h1 | ⟨n, hn, -, hn2⟩ |
    ⟨hON, -⟩
  ·
    exfalso
    have hθ0 : inSubgroup (aschbacherSolvableCore 3) L₀ = ⊥ := by
      rw [inSubgroup, hL₀θ, Subgroup.map_bot]
    rw [hθ0, sup_bot_eq] at h1
    have hLK : L ≤ K := by
      intro l hl
      have hl0 : (⟨l, hLC hl⟩ : ↥C) ∈ L₀ := hl
      rw [h1] at hl0
      exact hl0
    exact hLd (hLK.trans hKd)
  · exact absurd hn2 (Sec13.not_isSLThreePiAt_two_pow (Sec13.card_eq_of_isTripleCover_six hK₀A6) hn)
  · exact Sec13.isTripleCover_of_mulEquiv ((thetaBotEquiv hL₀θ).trans eL) hON

end Center426

end CFSG.RankThree.PartTwo.Sec14.Ronan148S
