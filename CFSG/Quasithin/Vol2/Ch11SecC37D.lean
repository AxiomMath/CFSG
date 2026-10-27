module

public import CFSG.Quasithin.Vol2.Ch11SecC37K
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Quasithin.Vol2.Ch11StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

theorem mem_of_forall_primePow {S : Subgroup G} {x : G}
    (h : ∀ y ∈ Subgroup.zpowers x, ∀ p k : ℕ, p.Prime → orderOf y = p ^ k → y ∈ S) : x ∈ S := by
  suffices H : ∀ m : ℕ, ∀ x : G, orderOf x = m →
      (∀ y ∈ Subgroup.zpowers x, ∀ p k : ℕ, p.Prime → orderOf y = p ^ k → y ∈ S) → x ∈ S from
    H _ x rfl h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x hxm hx
    by_cases hm1 : m = 1
    · subst hm1
      rw [orderOf_eq_one_iff] at hxm
      rw [hxm]
      exact S.one_mem
    have hm0 : m ≠ 0 := by rw [← hxm]; exact (orderOf_pos x).ne'
    obtain ⟨p, hp, hpm⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ m := ⟨m.minFac, Nat.minFac_prime hm1,
      Nat.minFac_dvd m⟩
    obtain ⟨k, m', hpm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
    by_cases hm'1 : m' = 1
    · exact hx x (Subgroup.mem_zpowers x) p k hp (by rw [hxm, hm, hm'1, mul_one])
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hm
      exact hpm' (hm ▸ hpm)
    have hm'0 : m' ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hm0 hm
    have hcop : Nat.Coprime (p ^ k) m' :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm')
    have hpk0 : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hy : orderOf (x ^ m') = p ^ k := by
      rw [orderOf_pow' x hm'0, hxm, hm, Nat.gcd_mul_left_left, Nat.mul_div_cancel _
        (Nat.pos_of_ne_zero hm'0)]
    have hz : orderOf (x ^ (p ^ k)) = m' := by
      rw [orderOf_pow' x hpk0, hxm, hm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _
        (Nat.pos_of_ne_zero hpk0)]
    have hlt : m' < m := by
      rw [hm]
      have h2 : 2 ≤ p ^ k :=
        le_trans hp.two_le (Nat.le_self_pow hk _)
      nlinarith [Nat.pos_of_ne_zero hm'0]
    have hzS : x ^ (p ^ k) ∈ S := by
      refine ih m' hlt _ hz fun y hy' p j hp' hyj => hx y ?_ p j hp' hyj
      exact (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)) hy'
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hyb : (x ^ m') ^ b ∈ S := by
      have hdvd : orderOf ((x ^ m') ^ b) ∣ p ^ k := by
        rw [← hy]
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
          one_zpow]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      exact hx _ (Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) b)
        _ j hp hj
    have hxeq : x = (x ^ (p ^ k)) ^ a * (x ^ m') ^ b := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm _ a,
        mul_comm _ b, hab, zpow_one]
    rw [hxeq]
    exact S.mul_mem (S.zpow_mem hzS a) hyb

omit [Finite G] in
theorem two_pow_dvd_card_map {K N : Subgroup G} {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) {φ : ↥K →* Matrix.SpecialLinearGroup (Fin 2) F}
    (hφs : Function.Surjective φ) (hodd : ¬ 2 ∣ (N.subgroupOf K).index) :
    2 ^ n ∣ Nat.card ((N.subgroupOf K).map φ) := by
  have hodd' : ¬ 2 ∣ ((N.subgroupOf K).map φ).index :=
    fun h => hodd (h.trans (Subgroup.index_map_dvd (N.subgroupOf K) hφs))
  have hcard := Subgroup.card_mul_index ((N.subgroupOf K).map φ)
  have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  rw [h2] at hcard
  exact (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    hodd')).dvd_of_dvd_mul_right ⟨_, hcard⟩

omit [Finite G] in
theorem le_of_map_eq_top {K N : Subgroup G} {Q : Type} [Group Q] {φ : ↥K →* Q}
    (hker : ∀ y : ↥K, φ y = 1 → (y : G) ∈ N) (htop : (N.subgroupOf K).map φ = ⊤) : K ≤ N := by
  intro k hk
  have hk' : φ ⟨k, hk⟩ ∈ (N.subgroupOf K).map φ := htop ▸ Subgroup.mem_top _
  obtain ⟨b, hb, hbk⟩ := Subgroup.mem_map.mp hk'
  have h1 : φ (b⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hbk, inv_mul_cancel]
  have h3 : (b : G) ∈ N := Subgroup.mem_subgroupOf.mp hb
  have : k = (b : G) * ((b⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
  rw [this]
  exact N.mul_mem h3 (hker _ h1)

omit [Finite G] in
theorem pow_eq_one_of_mem_pGroup {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx : Odd (orderOf x)) {m : ℕ} (hm : x ^ m ∈ P) : x ^ m = 1 := by
  obtain ⟨j, hj⟩ := hP ⟨_, hm⟩
  have hj' : (x ^ m) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have h2 : orderOf (x ^ m) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have h3 : Odd (orderOf (x ^ m)) := hx.of_dvd_nat (orderOf_pow_dvd _)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rcases i with _ | i
  · rwa [pow_zero, orderOf_eq_one_iff] at hi
  · exact absurd (hi ▸ h3) (by rw [Nat.odd_iff, pow_succ]; simp)

variable {T L I : Subgroup G} {n : ℕ}

theorem pow_eq_one_of_mem_hall (h1135 : Stmt11_3_5) (h1136 : Stmt11_3_6) (hB : FactSL2Borel)
    {V₁ H D : Subgroup G} (hyp : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (h31 : Hyp11_3_1 T L I n V₁ H) (hnot : ¬ Concl11_3_2 T L I n V₁ H)
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G)))
    {x : G} (hx : x ∈ D) : x ^ (2 ^ n - 1) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := oTwoUpper_data h1135 h1136 hyp hV₁ h31 hnot
  have hxHM := hD.1 hx
  have hodd : Odd (orderOf x) := by
    have h1 : orderOf x ∣ Nat.card D := by
      rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _
    exact hD.2.1.of_dvd_nat h1
  have hxK : x ∈ oTwoUpper H := mem_oTwoUpper_of_odd (Subgroup.mem_inf.1 hxHM).1 hodd
  have hT := SecA.isSylowTwoOf_of_isHStar hyp h31.hstar
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hyp.normal
  obtain ⟨φ, hφs, hφker⟩ : ∃ φ : ↥(oTwoUpper H) →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective φ ∧ ∀ y, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 (oTwoUpper H) := by
    refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _),
      e.surjective.comp (QuotientGroup.mk'_surjective _), fun y => ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [pCore_eq_subgroupOf, Subgroup.mem_subgroupOf]
  have hPT : pCoreOf 2 (oTwoUpper H) ≤ T :=
    (F7.pCoreOf_mono_of_le_normalizer hKH (le_normalizer_oTwoUpper H)).trans
      (F7.isSylowTwoOf_pCoreOf_le hT)
  have hBtop : ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).map φ ≠ ⊤ := by
    intro hBt
    apply h31.hstar.2.1
    refine (oTwoUpper_sup_eq hT).ge.trans (sup_le (le_of_map_eq_top
      (fun y hy => hTM (hPT ((hφker y).mp hy))) hBt) hTM)
  have hodd' : ¬ 2 ∣ ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).index := by
    have h2 : ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).index ∣
        ((T ⊓ oTwoUpper H).subgroupOf (oTwoUpper H)).index :=
      Subgroup.relIndex_dvd_of_le_left (oTwoUpper H) (inf_le_left.trans hTM)
    have h3 := F7.isSylowTwoOf_odd_relIndex (F7.isSylowTwoOf_inf_normal hT hKH
      (h31.hstar.1.1.trans (le_normalizer_oTwoUpper H)))
    exact fun h => h3 (h.trans h2)
  have hxB : φ ⟨x, hxK⟩ ∈ ((Subgroup.normalizer (L : Set G)).subgroupOf (oTwoUpper H)).map φ :=
    Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.1 hxHM).2)
  have hodd2 : Odd (orderOf (φ ⟨x, hxK⟩)) :=
    hodd.of_dvd_nat ((orderOf_map_dvd φ _).trans (by rw [Subgroup.orderOf_mk]))
  have hpow := hB F n (by have := hyp.one_lt; omega) hF _ hBtop
    (two_pow_dvd_card_map hF hφs hodd') _ hxB hodd2
  rw [← map_pow] at hpow
  have hmem : x ^ (2 ^ n - 1) ∈ pCoreOf 2 (oTwoUpper H) := by
    have := (hφker _).mp hpow
    simpa using this
  exact pow_eq_one_of_mem_pGroup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hodd hmem

omit [Finite G] in
theorem even_of_three_dvd {n : ℕ} (h : 3 ∣ 2 ^ n - 1) : Even n := by
  rcases Nat.even_or_odd n with he | ⟨m, rfl⟩
  · exact he
  · exfalso
    have h4 : ∀ m : ℕ, 2 ^ (2 * m + 1) % 3 = 2 := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
        rw [show 2 ^ (2 * (m + 1) + 1) = 4 * 2 ^ (2 * m + 1) by ring]
        omega
    have hpos : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
    have h4m := h4 m
    generalize 2 ^ (2 * m + 1) = x at h h4m hpos
    omega

theorem d0Of_le (h1104 : Stmt11_0_4) (h1134 : Stmt11_3_4) (h1135 : Stmt11_3_5)
    (h1136 : Stmt11_3_6) (hB : FactSL2Borel) {V₁ H D : Subgroup G} {g : G}
    (hyp : Hyp11 G T L I n) (hJ : L = ⁅L, thompsonJ T⁆) (hV₁ : IsVi T L I n 1 V₁)
    (h31 : Hyp11_3_1 T L I n V₁ H)
    (hnot : ¬ Concl11_3_2 T L I n V₁ H) (hAT : conjSubgroup (fsuV T I) g ≤ T)
    (hAC : ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (VZ T H : Set G))
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G))) :
    d0Of D ≤ L := by
  have hkind := (h1134 G T L I n V₁ H g hyp hV₁ h31 hnot hAT hAC).2.1
  obtain ⟨h04a, h04b⟩ := h1104 G T L I n hyp
  have key : ∀ y ∈ D, ∀ p k : ℕ, p.Prime → orderOf y = p ^ k → (p ≠ 3 ∨ y ^ 3 = 1) →
      y ∈ L := by
    intro y hyD p k hp hy h3
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, orderOf_eq_one_iff] at hy; rw [hy]; exact L.one_mem
    have hyM : y ∈ Subgroup.normalizer (L : Set G) := (Subgroup.mem_inf.1 (hD.1 hyD)).2
    have hpq : p ∣ 2 ^ n - 1 :=
      (dvd_pow_self p hk.ne').trans (hy ▸ orderOf_dvd_of_pow_eq_one
        (pow_eq_one_of_mem_hall h1135 h1136 hB hyp hV₁ h31 hnot hD hyD))
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hn1 : 1 ≤ n := by have := hyp.one_lt; omega
      have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
      have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
      obtain ⟨c, hc⟩ := hpq
      omega
    have hmemO : y ∈ oPrimeResidualOf p (Subgroup.normalizer (L : Set G)) :=
      Subgroup.subset_closure ⟨hyM, k, hy⟩
    rcases hkind with hSL3 | hSp4
    · by_cases hp3 : p = 3
      · subst hp3
        have hy3 : orderOf y = 3 := by
          rcases h3 with h3 | h3
          · exact absurd rfl h3
          · have h1 : 3 ^ k ∣ 3 ^ 1 := by rw [← hy, pow_one]; exact orderOf_dvd_of_pow_eq_one h3
            have hk1 : k ≤ 1 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
            rw [hy, show k = 1 by omega, pow_one]
        exact h04b hSL3 (even_of_three_dvd hpq) y hyM hy3 (Or.inr (Or.inl hJ))
      · have h3p : 3 < p := by
          have := hp.two_le
          omega
        rw [← h04a p hp (Or.inr ⟨hSL3, hpq, h3p⟩)]
        exact hmemO
    · have hpq2 : p ∣ 2 ^ (2 * n) - 1 := by
        refine hpq.trans ?_
        have := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
        rwa [one_pow, ← pow_mul, mul_comm] at this
      rw [← h04a p hp (Or.inl ⟨Or.inl hSp4, hpq2⟩)]
      exact hmemO
  refine sup_le ((Subgroup.closure_le _).mpr fun x hx => ?_)
    ((Subgroup.closure_le _).mpr fun x hx => ?_)
  · refine mem_of_forall_primePow fun y hy p k hp hyk => ?_
    have hyD : y ∈ D := (Subgroup.zpowers_le.mpr hx.1) hy
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, orderOf_eq_one_iff] at hyk; rw [hyk]; exact L.one_mem
    refine key y hyD p k hp hyk (Or.inl fun hp3 => ?_)
    subst hp3
    have h1 : 3 ∣ orderOf x := (dvd_pow_self 3 hk.ne').trans (hyk ▸ orderOf_dvd_of_mem_zpowers hy)
    exact absurd (Nat.Coprime.coprime_dvd_left h1 hx.2) (by norm_num)
  · have hxD : x ∈ D := CFSG.LieType.BorelTits.pCoreOf_le 3 D hx.1
    have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx.2
    have h3' : orderOf x ∣ 3 ^ 1 := by rw [pow_one]; exact h3
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h3'
    exact key x hxD 3 k Nat.prime_three hk (Or.inr hx.2)

end CFSG.Quasithin.Vol2.Ch11.SecC
