module

public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecB35
public import CFSG.Quasithin.Background.E6Hyp

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

section General

variable {G : Type} [Group G] [Finite G]

theorem mem_twoPrimeResidual_of_pow {H : Subgroup G} {x : G} (hx : x ∈ H) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ∈ twoPrimeResidual H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hle : Subgroup.zpowers x ≤ H := Subgroup.zpowers_le.mpr hx
  refine Subgroup.mem_iInf.mpr fun N => Subgroup.mem_iInf.mpr fun hN => ?_
  exact B6.le_of_isPGroup_of_odd_relIndex hle hP hN.1 hN.2.1 hN.2.2 (Subgroup.mem_zpowers x)

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem hypE61_of (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (hyp : Hyp11 G T L I n) :
    E6.HypE61 T (Subgroup.normalizer (L : Set G)) (fsuV T I) := by
  have hLT : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le (L_le_normalizer_fsuV hyp) (T_le_normalizer_fsuV T I)
  have hLTQ := le_normalizer_inf_centralizer h1102 hyp le_rfl hLT
  have hLTM : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hyp.normal
  refine ⟨hyp.fsu.simple, hyp.fsu.nonabelian, hyp.fsu.qtke, hyp.fsu.sylow,
    ⟨isMaxTwoLocal_M h331 hyp, hyp.normal⟩, fsuV_ne_bot hyp, isElemAbelian_fsuV hyp,
    fsuV_le_T hyp, T_le_normalizer_fsuV T I, (h1103 G T L I n hyp).2.2.2.1, ?_⟩
  refine ⟨⟨isMaxTwoLocal_M h331 hyp, inf_le_right.trans inf_le_left⟩, fun M' hM' => ?_⟩
  exact (isUniqueM_LT h331 hyp).2 M' ⟨hM'.1, (le_inf hLTQ (le_inf hLTM hLT)).trans hM'.2⟩

theorem mem_sup_centralizer_of_pow (h1102 : Stmt11_0_2) (h1104 : Stmt11_0_4)
    (hyp : Hyp11 G T L I n) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (fsuV T I : Set G))
    {p : ℕ} (hp : p.Prime) (hpd : p ∣ 2 ^ n - 1)
    (hxp : x ^ p ∈ Subgroup.centralizer (fsuV T I : Set G)) :
    x ∈ L ⊔ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer (fsuV T I : Set G) with hCdef
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hyp.one_lt
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by have := hyp.one_lt; omega)
    generalize 2 ^ n = y at h4 h2 hpd
    omega
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.one_lt.ne'
  have hcop : Nat.Coprime (p ^ a) b :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hb)
  set u := Nat.gcdA (p ^ a) b
  set v := Nat.gcdB (p ^ a) b
  have hbez : ((p ^ a : ℕ) : ℤ) * u + (b : ℤ) * v = 1 := by
    have := Nat.gcd_eq_gcd_ab (p ^ a) b
    rw [hcop] at this
    exact_mod_cast this.symm
  have hxe : x = (x ^ (p ^ a)) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, hbez, zpow_one]
  have hC1 : x ^ (p ^ a) ∈ C := by
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      have h1 : x ∈ Subgroup.zpowers (x ^ p) := by
        have hcp : Nat.Coprime p (orderOf x) := by
          rw [hab, pow_zero, one_mul]
          exact (Nat.Prime.coprime_iff_not_dvd hp).2 hb
        exact A4.mem_zpowers_pow_of_coprime hcp
      simpa using (Subgroup.zpowers_le.mpr hxp) h1
    · have : x ^ (p ^ a) = (x ^ p) ^ (p ^ (a - 1)) := by
        rw [← pow_mul, ← pow_succ']
        congr 2
        omega
      rw [this]
      exact C.pow_mem hxp _
  have hpord : (x ^ b) ^ (p ^ a) = 1 := by
    rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
  have hL1 : x ^ b ∈ L := by
    have h04 := h1104 G T L I n hyp
    have hxM : x ^ b ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hx.1 b
    have hres : p ≠ 3 ∨ ¬ KindSL3 L (fsuV T I) n → x ^ b ∈ L := by
      intro hcase
      have hcond : (KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) ∧ p ∣ 2 ^ (2 * n) - 1 ∨
          KindSL3 L (fsuV T I) n ∧ p ∣ 2 ^ n - 1 ∧ 3 < p := by
        have hpd2 : p ∣ 2 ^ (2 * n) - 1 := by
          refine hpd.trans ⟨2 ^ n + 1, ?_⟩
          have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
          have h3 : 1 ≤ 2 ^ n * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
          rw [two_mul, pow_add]
          zify [h1, h3]
          ring
        rcases kind_cases h1102 hyp with hk | hk | hk
        · rcases hcase with h3 | h3
          · refine Or.inr ⟨hk, hpd, ?_⟩
            have := hp.two_le
            omega
          · exact absurd hk h3
        · exact Or.inl ⟨Or.inl hk, hpd2⟩
        · exact Or.inl ⟨Or.inr hk, hpd2⟩
      rw [← h04.1 p hp hcond]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hpord)
      exact Subgroup.subset_closure ⟨hxM, j, hj⟩
    by_cases hcase : p ≠ 3 ∨ ¬ KindSL3 L (fsuV T I) n
    · exact hres hcase
    push Not at hcase
    obtain ⟨rfl, hk⟩ := hcase
    have hev : Even n := even_of_three_dvd hpd
    have hno3 : ∀ y ∈ Subgroup.normalizer (L : Set G), y ∈ C → orderOf y = 3 → False := by
      intro y hyM hyC hy3
      have hyL := h04.2 hk hev y hyM hy3
        (Or.inl (Subgroup.centralizer_le_normalizer _ hyC))
      have hyO : y ∈ pCoreOf 2 L := by
        rw [← centralizer_eq_pCoreOf h1102 hyp]
        exact ⟨hyL, hyC⟩
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨y, hyO⟩
      have hj' : y ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      have h3 : 3 ∣ 2 ^ j := hy3 ▸ orderOf_dvd_of_pow_eq_one hj'
      exact absurd (Nat.le_of_dvd two_pos (Nat.prime_three.dvd_of_dvd_pow h3)) (by norm_num)
    have hcube : (x ^ b) ^ 3 = 1 := by
      by_contra hne
      set w := (x ^ b) ^ 3 with hwdef
      have hwC : w ∈ C := by
        rw [hwdef, ← pow_mul, mul_comm, pow_mul]
        exact C.pow_mem hxp b
      have hwM : w ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ hxM 3
      have hw3 : w ^ (3 ^ a) = 1 := by
        rw [hwdef, ← pow_mul, mul_comm, pow_mul, hpord, one_pow]
      have hw1 : orderOf w ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hw1
      have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp
        (hq.dvd_of_dvd_pow (hqd.trans (orderOf_dvd_of_pow_eq_one hw3)))
      subst hq3
      exact hno3 _ (Subgroup.pow_mem _ hwM _) (C.pow_mem hwC _)
        (orderOf_pow_orderOf_div (orderOf_pos w).ne' hqd)
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hcube) with h1 | h3
    · rw [orderOf_eq_one_iff.mp h1]
      exact L.one_mem
    · exact h04.2 hk hev _ hxM h3 (Or.inl (Subgroup.pow_mem _ hx.2 b))
  rw [hxe]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (C.zpow_mem hC1 u))
    (Subgroup.mem_sup_left (L.zpow_mem hL1 v))

theorem inf_centralizer_eq_of_lt (hFM : FactMParam) (hFO : FactOddCodim) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1104 : Stmt11_0_4) (hyp : Hyp11 G T L I n) {m : ℕ}
    (hm : KindG2 L (fsuV T I) n ∧ m = 2 * n ∨ ¬ KindG2 L (fsuV T I) n ∧ m = n)
    {U : Subgroup G} (hUV : U ≤ fsuV T I) (hk : E3.mQuot (fsuV T I) U < 2 * m)
    (hres : twoPrimeResidual (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G))
      ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (fsuV T I : Set G)) :
    U ≠ ⊥ ∧ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) =
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set V := fsuV T I with hVdef
  have hV := isElemAbelian_fsuV hyp
  have hLV := L_le_normalizer_fsuV hyp
  have hVL := commutator_fsuV_eq_self hyp
  have hnat := natModuleOf_fsuV h1102 hyp
  have hMN : M ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := inf_le_left
  have hdim := (hFM G L V M n m hV hyp.one_lt hLV hVL hnat hm Subgroup.le_normalizer hMN).2
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    omega
  refine ⟨hU1, le_antisymm ?_ (inf_le_inf_left _ (Subgroup.centralizer_le hUV))⟩
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hxU : x ∈ Subgroup.centralizer (U : Set G) := hx.2
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := by
    by_contra hxN
    have hbot := (h1103 G T L I n hyp).2.2.2.1.2 x hx.1 hxN
    apply hU1
    rw [eq_bot_iff, ← hbot]
    intro u hu
    refine ⟨hUV hu, mem_conjSubgroup_iff.mpr ?_⟩
    rw [← Subgroup.mem_centralizer_iff.mp hxU u hu, mul_inv_cancel_right]
    exact hUV hu
  set φ := conjHomL V (Subgroup.normalizer (V : Set G)) le_rfl with hφdef
  have hker : ∀ y (hy : y ∈ Subgroup.normalizer (V : Set G)),
      φ ⟨y, hy⟩ = 1 ↔ y ∈ Subgroup.centralizer (V : Set G) := by
    intro y hy
    rw [← MonoidHom.mem_ker, ker_conjHomL, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  have hpow : ∀ k : ℕ, φ ⟨x ^ k, Subgroup.pow_mem _ hxN k⟩ = φ ⟨x, hxN⟩ ^ k := by
    intro k
    rw [← map_pow]
    rfl
  by_contra hxC
  set d := orderOf (φ ⟨x, hxN⟩) with hddef
  have hd1 : d ≠ 1 := fun h => hxC ((hker x hxN).mp (orderOf_eq_one_iff.mp h))
  have hdodd : Odd d := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨e, he⟩ := hev
    have h2d : 2 ∣ d := ⟨e, by omega⟩
    have hy2 : orderOf (φ ⟨x, hxN⟩ ^ e) = 2 := by
      have := orderOf_pow_orderOf_div (orderOf_pos (φ ⟨x, hxN⟩)).ne' h2d
      rwa [← hddef, show d / 2 = e by omega] at this
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x ^ e)).ne'
    have hzpow : ((x ^ e) ^ b) ^ 2 ^ a = 1 := by
      rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
    have hzres : (x ^ e) ^ b ∈ twoPrimeResidual (M ⊓ Subgroup.centralizer (U : Set G)) :=
      mem_twoPrimeResidual_of_pow
        ((M ⊓ Subgroup.centralizer (U : Set G)).pow_mem
          ((M ⊓ Subgroup.centralizer (U : Set G)).pow_mem hx e) b) hzpow
    have hzC := (hres hzres).2
    have hφz : φ ⟨(x ^ e) ^ b, Subgroup.pow_mem _ (Subgroup.pow_mem _ hxN e) b⟩ =
        (φ ⟨x, hxN⟩ ^ e) ^ b := by
      rw [← hpow, ← map_pow]
      rfl
    have hne : (φ ⟨x, hxN⟩ ^ e) ^ b ≠ 1 := by
      obtain ⟨c, rfl⟩ := hb
      rw [pow_succ, pow_mul, ← hy2, pow_orderOf_eq_one, one_pow, one_mul]
      intro h
      rw [h, orderOf_one] at hy2
      exact absurd hy2 (by norm_num)
    exact hne (hφz ▸ (hker _ _).mpr hzC)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hdodd) (even_iff_two_dvd.mpr hpd)
  set z := x ^ (d / p) with hzdef
  have hzN : z ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hxN _
  have hzord : orderOf (φ ⟨z, hzN⟩) = p := by
    rw [show φ ⟨z, hzN⟩ = φ ⟨x, hxN⟩ ^ (d / p) from hpow (d / p)]
    exact orderOf_pow_orderOf_div (orderOf_pos _).ne' hpd
  have hzp : z ^ p ∈ Subgroup.centralizer (V : Set G) := by
    refine (hker _ (Subgroup.pow_mem _ hzN p)).mp ?_
    rw [show (⟨z ^ p, Subgroup.pow_mem _ hzN p⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨z, hzN⟩ ^ p from rfl, map_pow, ← hzord, pow_orderOf_eq_one]
  have hzC : z ∉ Subgroup.centralizer (V : Set G) := by
    intro h
    rw [(hker z hzN).mpr h, orderOf_one] at hzord
    exact hp.one_lt.ne' hzord.symm
  have hzU : z ∈ Subgroup.centralizer (U : Set G) := Subgroup.pow_mem _ hxU _
  have hcod := hFO G L V M n m hV hyp.one_lt hLV hVL hnat hm Subgroup.le_normalizer hMN
    (fun y hy q hq hqd hyq => mem_sup_centralizer_of_pow h1102 h1104 hyp hy hq hqd hyq)
    z ⟨Subgroup.pow_mem _ hx.1 _, hzN⟩ p hp hp2 hzp hzC
  have hUz : U ≤ V ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    refine ⟨hUV hu, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    rw [Set.mem_singleton_iff.mp hw]
    exact (Subgroup.mem_centralizer_iff.mp hzU u hu).symm
  have := E3.mQuot_mono (V := V) hUz
  omega

end CFSG.Quasithin.Vol2.Ch11.SecB
