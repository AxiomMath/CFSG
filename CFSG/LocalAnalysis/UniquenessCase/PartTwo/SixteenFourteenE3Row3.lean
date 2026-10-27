module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row3T
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3GL6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Nu
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenGap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeCentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrCaseThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1614e3_row3_frame (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (h3 : Case168_3 D ⊥ V hV L)
    (hpr : CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) < 3) :
    ∃ z : MulAut (Vtil ⊥ V hV), z * z * z = 1 ∧ z ≠ 1 ∧
      (∀ x : Vtil ⊥ V hV, z x = x → x = 1) ∧
      (∀ m ∈ Mbar D.M ⊥ V hV, m * z = z * m ∨ m * z = z * z * m) ∧
      (∀ E : Subgroup (MulAut (Vtil ⊥ V hV)), E ≤ Mbar D.M ⊥ V hV →
        IsElemAbelianOfRank 3 2 ↥E → z ∈ E) ∧
      (∀ y ∈ lBar ⊥ V hV L, (∀ w ∈ lBar ⊥ V hV L, w * y = y * w) →
        y ∈ Subgroup.zpowers z) ∧
      (Nat.card ↥(Mbar D.M ⊥ V hV)).factorization 3 = 3 ∧
      (∀ x : Vtil ⊥ V hV, x * x = 1) ∧ Nat.card (Vtil ⊥ V hV) = 2 ^ 6 := by
  classical
  have hWsq : ∀ x : Vtil ⊥ V hV, x * x = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := mkTil_surjective ⊥ V hV x
    rw [← map_mul, ← sq, IntMod.sq_eq_one y, map_one]
  have hcard : Nat.card (Vtil ⊥ V hV) = 2 ^ 6 := by
    have hp : IsPGroup 2 (Vtil ⊥ V hV) := fun x => ⟨1, by simpa [pow_two] using hWsq x⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
    have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
    unfold rk at h6
    rw [Subgroup.card_top, hn, padicValNat.prime_pow] at h6
    rw [hn, h6]
  have hrk6 : rk (Vtil ⊥ V hV) = 6 := by rw [← rk_top]; exact h3.2.1
  have hT : ∀ t : Vtil ⊥ V hV, t ^ 2 = 1 := fun x => by rw [pow_two]; exact hWsq x
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV :=
    barSub_mono ⊥ V hV hc.setting.hyp151.le
  have hMN : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) :=
    s16c167_mbar_le_normalizer_lbar D hV hc h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hext : CFSG.IsExtraspecial 3 ↥(lBar ⊥ V hV L) := h3.1.1
  have hZcard : Nat.card (Subgroup.center ↥(lBar ⊥ V hV L)) = 3 :=
    CFSG.IsExtraspecial.center_order_p 3 ↥(lBar ⊥ V hV L)
  obtain ⟨ℓ, hℓ, hℓ1⟩ :
      ∃ ℓ : ↥(lBar ⊥ V hV L), ℓ ∈ Subgroup.center ↥(lBar ⊥ V hV L) ∧ ℓ ≠ 1 := by
    have hnt : Nontrivial (Subgroup.center ↥(lBar ⊥ V hV L)) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hZcard]
      norm_num
    obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Subgroup.center ↥(lBar ⊥ V hV L))
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  let z : MulAut (Vtil ⊥ V hV) := (ℓ : MulAut (Vtil ⊥ V hV))
  have hz3 : z * z * z = 1 := by
    have h := congrArg (fun y : ↥(lBar ⊥ V hV L) => (y : MulAut (Vtil ⊥ V hV)))
      (h3.1.2.2 ℓ)
    simpa [z, Subgroup.coe_pow, pow_three'] using h
  have hz1 : z ≠ 1 := fun h => hℓ1 (Subtype.ext h)
  have hzfix : ∀ x : Vtil ⊥ V hV, z x = x → x = 1 := fun x hx =>
    s16c167_central_fixed_point_free hWsq hcard h3.1 hℓ hℓ1 hx
  have hzc : ∀ y ∈ lBar ⊥ V hV L, (∀ w ∈ lBar ⊥ V hV L, w * y = y * w) →
      y ∈ Subgroup.zpowers z := by
    intro y hyL hycomm
    have hy3 : y * y * y = 1 := by
      have h := congrArg (fun c : ↥(lBar ⊥ V hV L) => (c : MulAut (Vtil ⊥ V hV)))
        (h3.1.2.2 ⟨y, hyL⟩)
      simpa [Subgroup.coe_pow, pow_three'] using h
    exact s1614_central_eq hWsq hcard h3.1 hℓ hℓ1 hy3 (fun w hw => (hycomm w hw).symm)
  have hN : ∀ m ∈ Mbar D.M ⊥ V hV, m * z = z * m ∨ m * z = z * z * m := by
    intro m hm
    have hmN : m ∈ Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := hMN hm
    have hzcentral : ∀ a ∈ lBar ⊥ V hV L, a * z = z * a := by
      intro a ha
      have h := congrArg (fun c : ↥(lBar ⊥ V hV L) => (c : MulAut (Vtil ⊥ V hV)))
        (Subgroup.mem_center_iff.1 hℓ ⟨a, ha⟩)
      simpa [z, Subgroup.coe_mul] using h
    have hφL : m * z * m⁻¹ ∈ lBar ⊥ V hV L :=
      (Subgroup.mem_normalizer_iff.1 hmN z).1 ℓ.2
    have hφcomm : ∀ w ∈ lBar ⊥ V hV L, w * (m * z * m⁻¹) = (m * z * m⁻¹) * w := by
      intro w hw
      have hwm : m⁻¹ * w * m ∈ lBar ⊥ V hV L := by
        have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hmN) w).1 hw
        simpa using h
      calc w * (m * z * m⁻¹) = m * ((m⁻¹ * w * m) * z) * m⁻¹ := by group
        _ = m * (z * (m⁻¹ * w * m)) * m⁻¹ := by rw [hzcentral _ hwm]
        _ = (m * z * m⁻¹) * w := by group
    have hφmem := hzc (m * z * m⁻¹) hφL hφcomm
    have hφne : m * z * m⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have h1 : m⁻¹ * (m * z * m⁻¹) * m = z := by group
      have := congrArg (fun x => m⁻¹ * x * m) h
      rw [h1, mul_one] at this
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hφmem
    have hpow := zpow_eq_zpow_emod' (x := z) k (n := 3) hz3
    rcases (by omega : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨
      k % ((3 : ℕ) : ℤ) = 2) with h | h | h
    · exact absurd (by rw [← hk, hpow, h, zpow_zero] : m * z * m⁻¹ = 1) hφne
    · left
      have hmz : m * z * m⁻¹ = z := by rw [← hk, hpow, h, zpow_one]
      calc m * z = (m * z * m⁻¹) * m := by group
        _ = z * m := by rw [hmz]
    · right
      have hmz : m * z * m⁻¹ = z * z := by rw [← hk, hpow, h, zpow_two]
      calc m * z = (m * z * m⁻¹) * m := by group
        _ = (z * z) * m := by rw [hmz]
        _ = z * z * m := by group
  have h3div : 27 ∣ Nat.card ↥(Mbar D.M ⊥ V hV) := by
    have hcardL : Nat.card ↥(lBar ⊥ V hV L) = 27 := by
      rw [h3.1.2.1]
      norm_num
    rw [← hcardL]
    exact Subgroup.card_dvd_of_le hLM
  have hfac_le : (Nat.card ↥(Mbar D.M ⊥ V hV)).factorization 3 ≤ 4 :=
    s1614e3_factorization_three_le hT hrk6 _
  have hfac_ge : 3 ≤ (Nat.card ↥(Mbar D.M ⊥ V hV)).factorization 3 := by
    have hdvd : 3 ^ 3 ∣ Nat.card ↥(Mbar D.M ⊥ V hV) := by simpa using h3div
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (Nat.card_pos.ne')).1 hdvd
  have hfac : (Nat.card ↥(Mbar D.M ⊥ V hV)).factorization 3 = 3 := by
    by_contra hne
    have h4 : (Nat.card ↥(Mbar D.M ⊥ V hV)).factorization 3 = 4 := by omega
    have hle := s1614e3_three_le_pRank_of_card hT hrk6 (Mbar D.M ⊥ V hV) h4
    omega
  have hE : ∀ E : Subgroup (MulAut (Vtil ⊥ V hV)), E ≤ Mbar D.M ⊥ V hV →
      IsElemAbelianOfRank 3 2 ↥E → z ∈ E := by
    intro E hEM hEr
    exact (s1614e3_row3_sylow h3.1 hLM hMN hfac).2 E hEM hEr ℓ hℓ
  exact ⟨z, hz3, hz1, hzfix, hN, hE, hzc, hfac, hWsq, hcard⟩

theorem s1614e3_row3_comm_false (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (h3σ : (3 : ℕ) ∈ D.sig) (hk1 : D.k = 1)
    (hpr : CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) ≤ 2) {U : Subgroup G} (hU : Min1614 D V U)
    (hW : ∀ x : Vtil ⊥ V hV, x * x = 1) (hcard : Nat.card (Vtil ⊥ V hV) = 2 ^ 6)
    {z t : MulAut (Vtil ⊥ V hV)} (hz3 : z * z * z = 1) (hz1 : z ≠ 1)
    (hzfix : ∀ x : Vtil ⊥ V hV, z x = x → x = 1)
    (hE : ∀ E : Subgroup (MulAut (Vtil ⊥ V hV)), E ≤ Mbar D.M ⊥ V hV →
      IsElemAbelianOfRank 3 2 ↥E → z ∈ E)
    (ht2 : t * t = 1) (hzt : t * z = z * t) (hk : 1 < rkIdx (fixV (Subgroup.zpowers t)))
    (hUt : imgTil ⊥ V hV U ≤ fixV (Subgroup.zpowers t)) : False := by
  have hle : rkIdx (imgTil ⊥ V hV U) ≤ 3 := by
    have h := s1614_rkIdx_le D hV hU
    rw [hk1] at h
    omega
  obtain ⟨Z, hZ0, hZU, hZz⟩ := s1614e3_row3_lin hW hcard hz3 hzfix ht2 hzt hk hUt hle
  refine s1614e3_false_of_lemmaP D hx h61 h127 hV hc hU h3σ hpr ?_
  intro E hEM hEr
  exact ⟨z, hE E hEM hEr, hz1, Z, hZ0, hZU, hZz⟩

theorem s1614e3_row3_inv_desc (D : Data G) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D ⊥ V L hV) (hk1 : D.k = 1) {U : Subgroup G} (hU : Min1614 D V U)
    (hW : ∀ x : Vtil ⊥ V hV, x * x = 1) (hcard : Nat.card (Vtil ⊥ V hV) = 2 ^ 6)
    {z s : MulAut (Vtil ⊥ V hV)} (hz3 : z * z * z = 1) (hz1 : z ≠ 1)
    (hzfix : ∀ x : Vtil ⊥ V hV, z x = x → x = 1)
    (hN : ∀ m ∈ Mbar D.M ⊥ V hV, m * z = z * m ∨ m * z = z * z * m)
    (hzc : ∀ y ∈ lBar ⊥ V hV L, (∀ w ∈ lBar ⊥ V hV L, w * y = y * w) →
      y ∈ Subgroup.zpowers z)
    (hsM : s ∈ Mbar D.M ⊥ V hV) (hs2 : orderOf s = 2) (hsz : s * z = z * z * s)
    (hUs : imgTil ⊥ V hV U ≤ fixV (Subgroup.zpowers s)) :
    E3.mQuot V U = D.k + 2 ∧ Desc1614Three D V L hV U := by
  classical
  have hs2' : s * s = 1 := by
    rw [← pow_two, ← hs2]
    exact pow_orderOf_eq_one s
  obtain ⟨hrkC, hfix⟩ := s1614e3_row3_inv hW hcard hz3 hzfix hs2' hsz
  have hle : rkIdx (imgTil ⊥ V hV U) ≤ 3 := by
    have h := s1614_rkIdx_le D hV hU
    rw [hk1] at h
    omega
  have hfixle : rkIdx (fixV (Subgroup.zpowers s)) ≤ rkIdx (imgTil ⊥ V hV U) :=
    rkIdx_anti hUs
  have hrkU : rkIdx (imgTil ⊥ V hV U) = 3 := le_antisymm hle (hrkC ▸ hfixle)
  have hT : ∀ x : Vtil ⊥ V hV, x ^ 2 = 1 := fun x => by rw [pow_two]; exact hW x
  have hEq : imgTil ⊥ V hV U = fixV (Subgroup.zpowers s) := by
    refine eq_of_le_of_rk_le hT hUs ?_
    have h1 := rk_add_rkIdx (imgTil ⊥ V hV U)
    have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers s))
    omega
  have hmq : E3.mQuot V U = 3 := by
    rw [s1614e3_mQuot_eq_rkIdx_imgTil hV hU.1, hrkU]
  have hmqk : E3.mQuot V U = D.k + 2 := by rw [hmq, hk1]
  have hMV : D.M ≤ normalizer (V : Set G) := hc.setting.hyp16.hyp125.pairFacts.le_normalizer
  obtain ⟨t, htM, ht2n, htnV, hbar, himg, hmqv, hiff, hUeq⟩ :=
    s1614e3_lift_involution D hV hMV hsM hs2
  have hUt : U = V ⊓ centralizer ({t} : Set G) := hUeq U hU.1 hEq
  have htU : U ≤ centralizer ({t} : Set G) := by rw [hUt]; exact inf_le_right
  have hcent : ∀ m ∈ Mbar D.M ⊥ V hV, (∀ x ∈ imgTil ⊥ V hV U, m x = x) →
      m = 1 ∨ m ∈ barSub ⊥ V hV (Subgroup.zpowers t) := by
    intro m hm hmfix
    have hfix' : ∀ x ∈ fixV (Subgroup.zpowers s), m x = x := by
      intro x hx
      exact hmfix x (by rw [hEq]; exact hx)
    rcases hfix m (hN m hm) hfix' with h1 | hs
    · exact Or.inl h1
    · exact Or.inr (by rw [hbar, hs]; exact Subgroup.mem_zpowers s)
  have hcm : D.M ⊓ centralizer (U : Set G) =
      (D.M ⊓ centralizer (V : Set G)) ⊔ Subgroup.zpowers t :=
    s1614e3_centralizer_eq D hV hMV htM hU.1 htU hcent
  refine ⟨hmqk, ⟨t, htM, ht2n, htnV, hUt, hcm, ?_⟩⟩
  intro z' hz'L hz'comm hz'1 s' hs't hs'1
  have hz'z : z' ∈ Subgroup.zpowers z := hzc z' hz'L hz'comm
  have hs's : s' ∈ Subgroup.zpowers s := by rw [← hbar]; exact hs't
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hs's
  have hspow := zpow_eq_zpow_emod' (x := s) k (n := 2) hs2'
  have hs'eq : s' = s := by
    rcases (by omega : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1) with h | h
    · exfalso
      exact hs'1 (by rw [← hk, hspow, h, zpow_zero])
    · rw [← hk, hspow, h, zpow_one]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hz'z
  have hszinv : s * z * s⁻¹ = z⁻¹ := by
    calc s * z * s⁻¹ = z * z := by rw [hsz]; group
      _ = z⁻¹ := eq_inv_of_mul_eq_one_left hz3
  rw [hs'eq]
  have hconj : (MulAut.conj s) z = z⁻¹ := by
    rw [MulAut.conj_apply]
    exact hszinv
  have h1 : (MulAut.conj s) z' = s * z' * s⁻¹ := MulAut.conj_apply s z'
  rw [← h1, ← hi, map_zpow, hconj, inv_zpow]

theorem s1614e3_row3_close (D : Data G) (hx : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h61 : UC6.R6_1 D) (h127 : R127 D) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV) (h3 : Case168_3 D ⊥ V hV L)
    (hmB : 1 < mBar D.M ⊥ V hV) (hpr : CFSG.Open.pRank 3 (Mbar D.M ⊥ V hV) < 3)
    {U : Subgroup G} (hU : Min1614 D V U) (hUΓ : U ∉ gammaEleven D.M V) :
    E3.mQuot V U = D.k + 2 ∧ Residual1614At D V L hV U := by
  classical
  have hP : PairFacts D.M ⊥ V := hc.setting.hyp16.hyp125.pairFacts
  have h3σ : (3 : ℕ) ∈ D.sig := by
    rw [h3.2.2]
    exact Set.mem_singleton 3
  have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 h3σ
  obtain ⟨z, hz3, hz1, hzfix, hN, hE, hzc, h27, hW, hcard⟩ :=
    s1614e3_row3_frame D hV hc h3 hpr
  have hU0 : U ≠ ⊥ := by
    rintro rfl
    have h1 := s1614_rkIdx_le D hV hU
    have h2 : imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
      unfold imgTil intSub
      rw [Subgroup.bot_subgroupOf]
      exact Subgroup.map_bot _
    rw [h2] at h1
    have h3' := rk_add_rkIdx (⊥ : Subgroup (Vtil ⊥ V hV))
    rw [rk_bot] at h3'
    have h6 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) = 6 := h3.2.1
    rw [rk_top] at h6
    omega
  obtain ⟨s, hsM, hs2, hUs⟩ :=
    s1614_exists_involution D hV hP.le_normalizer hU.1 hU0 hU.2.1 hUΓ
  have hs2' : s * s = 1 := by
    rw [← pow_two, ← hs2]
    exact pow_orderOf_eq_one s
  have hmt : 1 < rkIdx (fixV (Subgroup.zpowers s)) :=
    lt_of_lt_of_le hmB (CFSG.Quasithin.Asc81c.Pf.mParam_le_of_orderOf_two hsM hs2)
  rcases hN s hsM with hcomm | hinv
  · exact (s1614e3_row3_comm_false D hx h61 h127 hV hc h3σ hk1 (by omega) hU hW hcard hz3 hz1
      hzfix hE hs2' hcomm hmt hUs).elim
  · obtain ⟨hmq, hd⟩ :=
      s1614e3_row3_inv_desc D hV hc hk1 hU hW hcard hz3 hz1 hzfix hN hzc hsM hs2 hinv hUs
    exact ⟨hmq, Or.inl ⟨h3, h27, hd⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
