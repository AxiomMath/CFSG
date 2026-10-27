module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBL32Defs
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBV
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBC31B
public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114Excl

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure LHCtx (K LH V : Subgroup G) : Prop where
  le_K : LH ≤ K
  pgroup_Z : IsPGroup 2 ↥(centerOf K)
  V_le : V ≤ LH
  V_pCore : V ≤ pCoreOf 2 LH
  V_cent : V ≤ Subgroup.centralizer (pCoreOf 2 LH : Set G)
  V_inf : V ⊓ centerOf K = ⊥
  card_V : 512 ≤ Nat.card V
  card_s : Nat.card (ModO2 LH) = 168 ∨ Nat.card (ModO2 LH) = 20160

theorem card_psl2_4 {Y : Type} [Group Y] (h : IsPSL 2 2 2 Y) : Nat.card Y = 60 := by
  rw [C489.card_of_isPSL_two_two h]
  norm_num

theorem card_psl3 {Y : Type} [Group Y] (h : IsPSL 3 2 1 Y) : Nat.card Y = 168 := by
  rw [C489.card_of_isPSL_two h]
  decide

theorem card_psl4 {Y : Type} [Group Y] (h : IsPSL 4 2 1 Y) : Nat.card Y = 20160 := by
  rw [C489.card_of_isPSL_two h]
  decide

theorem isPGroup_of_isE2 {Y : Type} [Group Y] [Finite Y] {k : ℕ} (h : IsE2 k Y) :
    IsPGroup 2 Y :=
  IsPGroup.iff_card.mpr ⟨k, C489.card_of_isE2 h⟩

theorem isPGroup_of_special {Y : Type} [Group Y] [Finite Y] {a b : ℕ}
    (h : IsSpecial2Group a b Y) : IsPGroup 2 Y :=
  IsPGroup.iff_card.mpr ⟨a + b, C489.card_of_isSpecial2Group h⟩

theorem isPGroup_of_z4 {Y : Type} [Group Y] [Finite Y] (h : IsZ4Cubed Y) : IsPGroup 2 Y :=
  IsPGroup.iff_card.mpr ⟨6, by rw [C489.card_of_isZ4Cubed h]; norm_num⟩

theorem card_V_of_natural {A V : Subgroup G} {N : Subgroup ↥A} {j : ℕ}
    (h : IsNaturalSection A V ⊥ N (CFSG.Assembly.LowTwoRank.StatedSL j (ZMod 2))) :
    Nat.card V = 2 ^ j := by
  obtain ⟨-, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x ∈ β.ker := MonoidHom.mem_ker.mpr hx
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx'
    exact Subtype.ext (by simpa using hx')
  rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hinj, hβs⟩).toEquiv,
    Nat.card_congr (Multiplicative.ofAdd : (Fin j → ZMod 2) ≃ _).symm, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card, Nat.card_eq_fintype_card (α := Fin j),
    Fintype.card_fin]

theorem false_of_not_dvd {y s e : ℕ} (hs : s = 168 ∨ s = 20160) (hy : y = s * 2 ^ e)
    (h168 : ¬ 168 ∣ y) (h20160 : ¬ 20160 ∣ y) : False := by
  rcases hs with rfl | rfl
  · exact h168 ⟨2 ^ e, hy⟩
  · exact h20160 ⟨2 ^ e, hy⟩

theorem false_of_div_pow_two {y s e c q : ℕ} (hy : y = s * 2 ^ e) (hc : y = s * c)
    (hs0 : 0 < s) (hq : q.Prime) (hq2 : q ≠ 2) (hqc : q ∣ c) : False := by
  have h2 : 2 ^ e = c := Nat.eq_of_mul_eq_mul_left hs0 (hy.symm.trans hc)
  have h3 : q ∣ 2 ^ e := h2 ▸ hqc
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h3))

theorem case1_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case1 H R M LH V K) : False := by
  obtain ⟨n, -, -, -, hpsl, -⟩ := h
  have key : ∀ Y : Subgroup G, Y = LH → IsPSL 2 2 n (ModO2 Y) →
      Nat.card (ModO2 LH) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rintro Y rfl hY
    exact C489.card_of_isPSL_two_two hY
  have hc := key _ hcc hpsl
  have hcard := C.card_s
  rw [hc] at hcard
  have hn : n < 5 := by
    by_contra hn
    have hn5 : 5 ≤ n := by omega
    have h1 : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn5
    have h2 : 32 ≤ 2 ^ n := by simpa using h1
    have h3 : 1024 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h4 : 1023 ≤ (2 ^ n) ^ 2 - 1 := by omega
    have h5 : 32 * 1023 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h2 h4
    generalize 2 ^ n * ((2 ^ n) ^ 2 - 1) = P at hcard h5
    omega
  interval_cases n <;> norm_num at hcard <;> omega

theorem case2_false (H R M LH V K : Subgroup G) (C : LHCtx K LH V)
    (h : C31Case2 H R M LH V K) : False := by
  obtain ⟨n, hn, -, -, -, hdisj⟩ := h
  have hV : 512 ≤ Nat.card V := C.card_V
  rcases hdisj with ⟨-, -, hnat⟩ | ⟨-, -, hnat⟩
  · rw [card_V_of_natural hnat] at hV
    rcases hn with rfl | rfl <;> norm_num at hV
  · rw [card_V_of_natural hnat] at hV
    norm_num at hV

theorem case3_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case3 H R M LH V K) : False := by
  unfold C31Case3 at h
  rw [hcc] at h
  obtain ⟨-, hext | hext | hext⟩ := h
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl2_4 hQ
    obtain ⟨e, he⟩ := ratio_I K LH C.le_K C.pgroup_Z N (isPGroup_of_isE2 hN)
    rw [hy] at he
    exact false_of_not_dvd C.card_s he (by norm_num) (by norm_num)
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := C489.card_of_isAlt hQ
    rw [C489.card_alt6] at hy
    obtain ⟨e, he⟩ := ratio_I K LH C.le_K C.pgroup_Z N (isPGroup_of_isE2 hN)
    rw [hy] at he
    exact false_of_not_dvd C.card_s he (by norm_num) (by norm_num)
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl3 hQ
    rcases C.card_s with hs | hs
    · have hsurv := card_V_le_I K LH V C.le_K C.pgroup_Z C.V_inf C.V_le C.V_pCore N
        (isPGroup_of_isE2 hN) (by rw [hy, hs])
      rw [C489.card_of_isE2 hN] at hsurv
      have h2 : 512 ≤ Nat.card V := C.card_V
      norm_num at hsurv
      omega
    · obtain ⟨e, he⟩ := ratio_I K LH C.le_K C.pgroup_Z N (isPGroup_of_isE2 hN)
      rw [hy, hs] at he
      exact false_of_lt he (by norm_num)

theorem case4_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case4 H R M LH V K) : False := by
  unfold C31Case4 at h
  rw [hcc] at h
  obtain ⟨-, hext | hext | hext⟩ := h
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl2_4 hQ
    obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
    rw [hy] at he
    exact false_of_not_dvd C.card_s he (by norm_num) (by norm_num)
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := C489.card_of_isAlt hQ
    rw [C489.card_alt7] at hy
    obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
    rw [hy] at he
    rcases C.card_s with hs | hs
    · rw [hs] at he
      exact false_of_prime_dvd (q := 5) (by norm_num) (by norm_num) he (by norm_num)
        (by norm_num)
    · rw [hs] at he
      exact false_of_lt he (by norm_num)
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl3 hQ
    rcases C.card_s with hs | hs
    · have hsurv := card_V_le_D C.V_le C.V_pCore N (isPGroup_of_isE2 hN) (by rw [hy, hs])
      rw [C489.card_of_isE2 hN] at hsurv
      have h2 : 512 ≤ Nat.card V := C.card_V
      norm_num at hsurv
      omega
    · obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
      rw [hy, hs] at he
      exact false_of_lt he (by norm_num)

theorem case5_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case5 H R M LH V K) : False := by
  unfold C31Case5 at h
  rw [hcc] at h
  obtain ⟨-, hext | hext | hext⟩ := h
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := C489.card_of_isHat_alt6 hQ
    obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
    rw [hy] at he
    exact false_of_not_dvd C.card_s he (by norm_num) (by norm_num)
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl4 hQ
    obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
    rw [hy] at he
    rcases C.card_s with hs | hs
    · rw [hs] at he
      exact false_of_div_pow_two (c := 120) (q := 3) he (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · have hsurv := card_V_le_D C.V_le C.V_pCore N (isPGroup_of_isE2 hN) (by rw [hy, hs])
      rw [C489.card_of_isE2 hN] at hsurv
      have h2 : 512 ≤ Nat.card V := C.card_V
      norm_num at hsurv
      omega
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl3 hQ
    rcases C.card_s with hs | hs
    · have hsurv := card_V_le_D C.V_le C.V_pCore N (isPGroup_of_isE2 hN) (by rw [hy, hs])
      rw [C489.card_of_isE2 hN] at hsurv
      have h2 : 512 ≤ Nat.card V := C.card_V
      norm_num at hsurv
      omega
    · obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
      rw [hy, hs] at he
      exact false_of_lt he (by norm_num)

theorem case6_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case6 H R M LH V K) : False := by
  unfold C31Case6 at h
  obtain ⟨-, hext | hext | hext⟩ := h
  · unfold C31Case6M24 at hext
    rw [hcc] at hext
    obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    obtain ⟨e⟩ := hQ
    have h23 : 23 ∣ Nat.card (↥LH ⧸ N) := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Quasithin.H13.L34Orders.twentyThree_dvd_card_M24
    obtain ⟨e', he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
    rcases C.card_s with hs | hs <;> rw [hs] at he
    · exact false_of_prime_dvd (q := 23) (by norm_num) (by norm_num) he h23 (by norm_num)
    · exact false_of_prime_dvd (q := 23) (by norm_num) (by norm_num) he h23 (by norm_num)
  · unfold C31Case6L3 at hext
    rw [hcc] at hext
    obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl3 hQ
    rcases C.card_s with hs | hs
    · have hsurv := card_V_le_center_D C.V_le C.V_pCore C.V_cent N (isPGroup_of_special hN)
        (by rw [hy, hs])
      rw [hN.1] at hsurv
      have h2 : 512 ≤ Nat.card V := C.card_V
      norm_num at hsurv
      omega
    · obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_special hN)
      rw [hy, hs] at he
      exact false_of_lt he (by norm_num)
  · unfold C31Case6L5 at hext
    rw [hcc] at hext
    obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have h31 : 31 ∣ Nat.card (↥LH ⧸ N) := by
      rw [C489.card_of_isPSL_two hQ]
      decide
    obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
    rcases C.card_s with hs | hs <;> rw [hs] at he
    · exact false_of_prime_dvd (q := 31) (by norm_num) (by norm_num) he h31 (by norm_num)
    · exact false_of_prime_dvd (q := 31) (by norm_num) (by norm_num) he h31 (by norm_num)

theorem case7_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case7 H R M LH V K) : False := by
  unfold C31Case7 at h
  rw [hcc] at h
  obtain ⟨-, hext | hext⟩ := h
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl3 hQ
    obtain ⟨e, he⟩ := ratio_I K LH C.le_K C.pgroup_Z N (isPGroup_of_z4 hN)
    rw [hy] at he
    rcases C.card_s with hs | hs
    · have hsurv := card_V_le_I K LH V C.le_K C.pgroup_Z C.V_inf C.V_le C.V_pCore N
        (isPGroup_of_z4 hN) (by rw [hy, hs])
      rw [C489.card_of_isZ4Cubed hN] at hsurv
      have h2 : 512 ≤ Nat.card V := C.card_V
      omega
    · rw [hs] at he
      exact false_of_lt he (by norm_num)
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := C489.card_of_isAlt hQ
    rw [C489.card_alt6] at hy
    obtain ⟨e, he⟩ := ratio_I K LH C.le_K C.pgroup_Z N (isPGroup_of_isE2 hN)
    rw [hy] at he
    exact false_of_not_dvd C.card_s he (by norm_num) (by norm_num)

theorem case8_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case8 H R M LH V K) : False := by
  unfold C31Case8 at h
  rw [hcc] at h
  obtain ⟨-, hext⟩ := h
  obtain ⟨N, hNn, hN, hQ⟩ := hext
  haveI := hNn
  have hy := C489.card_of_isHat_alt6 hQ
  obtain ⟨e, he⟩ := ratio_D LH N (isPGroup_of_isE2 hN)
  rw [hy] at he
  exact false_of_not_dvd C.card_s he (by norm_num) (by norm_num)

theorem case9_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case9 H R M LH V K) : False := by
  unfold C31Case9 at h
  rw [hcc] at h
  obtain ⟨-, hext | hext⟩ := h
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := card_psl3 hQ
    obtain ⟨e, he⟩ := ratio_I K LH C.le_K C.pgroup_Z N (isPGroup_of_special hN)
    rw [hy] at he
    rcases C.card_s with hs | hs
    · have hsurv := card_V_le_center_I K LH V C.le_K C.pgroup_Z C.V_inf C.V_le C.V_pCore
        C.V_cent N (isPGroup_of_special hN) (by rw [hy, hs])
      rw [hN.1] at hsurv
      have h2 : 512 ≤ Nat.card V := C.card_V
      norm_num at hsurv
      omega
    · rw [hs] at he
      exact false_of_lt he (by norm_num)
  · obtain ⟨N, hNn, hN, hQ⟩ := hext
    haveI := hNn
    have hy := CFSG.Quasithin.SBc11.card_of_isPSU_three_three hQ
    obtain ⟨e, he⟩ := ratio_I K LH C.le_K C.pgroup_Z N (isPGroup_of_isE2 hN)
    rw [hy] at he
    rcases C.card_s with hs | hs
    · rw [hs] at he
      exact false_of_div_pow_two (c := 36) (q := 3) he (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)
    · rw [hs] at he
      exact false_of_lt he (by norm_num)

theorem case10_false (H R M LH V K : Subgroup G) (hcc : conjClosure LH M = LH)
    (C : LHCtx K LH V) (h : C31Case10 H R M LH V K) : False := by
  obtain ⟨-, -, hB⟩ := h
  rw [hcc] at hB
  obtain ⟨-, -, hcard, -⟩ := hB
  have h2 : 512 ≤ Nat.card V := C.card_V
  rw [hcard] at h2
  norm_num at h2

theorem notC31_holds : NotC31 := by
  intro G _ _ T M L Mm I H K m k hd _hcomp h31
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hm : m = 3 ∨ m = 4 := hd.2.2.2.1
  have hmk : m ≤ k := hd.2.2.2.2.1
  have hPSL := hd.2.2.2.2.2.2.1
  have hsum := hd.2.2.2.2.2.2.2
  have hcc := conjClosure_perfectCore hc
  obtain ⟨-, -, hLK', -, hZ2, hcases⟩ := h31
  have hLK : perfectCore (L ⊓ H) ≤ K := (le_conjClosure _ _).trans hLK'
  have hs : Nat.card (ModO2 (perfectCore (L ⊓ H))) = 168 ∨
      Nat.card (ModO2 (perfectCore (L ⊓ H))) = 20160 := by
    rcases card_modO2_of_isPSL hm hPSL with h | h
    · exact Or.inl h.2
    · exact Or.inr h.2
  have hV512 : 512 ≤ Nat.card (⁅reducedAggregate (L ⊔ T), L⁆ : Subgroup G) := by
    have h9 := nine_le_card_V (by omega) hmk hsum
    norm_num at h9
    exact h9
  let C : LHCtx K (perfectCore (L ⊓ H)) ⁅reducedAggregate (L ⊔ T), L⁆ :=
    { le_K := hLK
      pgroup_Z := hZ2
      V_le := V_le_perfectCore hc
      V_pCore := V_le_pCoreOf hc
      V_cent := V_le_centralizer_pCoreOf hc
      V_inf := V_inf_centerOf hc (V_inf_centralizer hc m k (by omega) hsum)
      card_V := hV512
      card_s := hs }
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · exact case1_false _ _ _ _ _ _ hcc C h1
  · exact case2_false _ _ _ _ _ _ C h2
  · exact case3_false _ _ _ _ _ _ hcc C h3
  · exact case4_false _ _ _ _ _ _ hcc C h4
  · exact case5_false _ _ _ _ _ _ hcc C h5
  · exact case6_false _ _ _ _ _ _ hcc C h6
  · exact case7_false _ _ _ _ _ _ hcc C h7
  · exact case8_false _ _ _ _ _ _ hcc C h8
  · exact case9_false _ _ _ _ _ _ hcc C h9
  · exact case10_false _ _ _ _ _ _ hcc C h10

end CFSG.Quasithin.H13.Ch4.NSB
