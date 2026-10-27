module

public import CFSG.Quasithin.Vol2.Ch11SecB21Odd
public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch11SecBDerived
public import CFSG.Quasithin.Vol2.Ch11SecBDerived35
public import CFSG.Quasithin.Vol2.Ch11SecBFacts35
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Background.A4FourQuot
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm318
public import CFSG.Quasithin.Background.C2Nine
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Vol2.Ch11SecBBasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped Pointwise

section General

variable {G : Type} [Group G] [Finite G]

theorem oTwoUpper_eq_conjClosure {H K T : Subgroup G} (hK : ⁅K, K⁆ = K) (hT : IsPGroup 2 T)
    (hHK : H = K ⊔ T) : oTwoUpper H = conjClosure K H := by
  have hKH : K ≤ H := hHK ▸ le_sup_left
  apply le_antisymm
  · refine oTwoUpper_le_of_pow_mem ?_
    have hCH : conjClosure K H ≤ H := conjClosure_le fun h hh z hz =>
      H.mul_mem (H.mul_mem hh (hKH hz)) (H.inv_mem hh)
    have hsup : T ⊔ conjClosure K H = H :=
      le_antisymm (sup_le (hHK ▸ le_sup_right) hCH)
        (hHK.le.trans (sup_le ((le_conjClosure K H).trans le_sup_right) le_sup_left))
    exact B6.isTwoQuotient_of_sup_eq hT (le_normalizer_conjClosure K H) hsup
  · refine conjClosure_le fun h hh z hz => ?_
    have hzO : z ∈ oTwoUpper H := perfect_le_oTwoUpper hKH (Subgroup.isPerfect_iff.2 hK) hz
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hh) z).mp hzO

omit [Finite G] in
theorem commutator_quotient_eq_top {K : Subgroup G} (hK : ⁅K, K⁆ = K) (N : Subgroup ↥K)
    [N.Normal] : commutator (↥K ⧸ N) = ⊤ := by
  have hXp : commutator ↥K = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hK)
  have hsurj := QuotientGroup.mk'_surjective N
  calc commutator (↥K ⧸ N) = ⁅(⊤ : Subgroup (↥K ⧸ N)), ⊤⁆ := commutator_def _
    _ = ⁅(⊤ : Subgroup ↥K).map (QuotientGroup.mk' N), (⊤ : Subgroup ↥K).map
          (QuotientGroup.mk' N)⁆ := by
        rw [Subgroup.map_top_of_surjective _ hsurj]
    _ = Subgroup.map (QuotientGroup.mk' N) ⁅(⊤ : Subgroup ↥K), ⊤⁆ :=
        (Subgroup.map_commutator _ _ _).symm
    _ = ⊤ := by rw [← commutator_def, hXp, Subgroup.map_top_of_surjective _ hsurj]

omit [Finite G] in
theorem even_of_three_dvd {n : ℕ} (h : 3 ∣ 2 ^ n - 1) : Even n := by
  rcases Nat.even_or_odd n with he | ⟨m, rfl⟩
  · exact he
  · exfalso
    have h1 : 2 ^ (2 * m + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h2 : 1 ≤ 2 ^ (2 * m + 1) := Nat.one_le_two_pow
    generalize 2 ^ (2 * m + 1) = x at h h1 h2
    omega

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem eq_commutator_thompsonJ_of_moves (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hFC : FactCentralizerTwo) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) : L = ⁅L, thompsonJ T⁆ := by
  refine eq_commutator_thompsonJ hFC h1102 hyp fun hJ => hZH ?_
  obtain ⟨hVLT, hVred, hcent⟩ := h3228 G T L I hyp.fsu
  rw [fsuL0_eq hyp] at hVLT hVred hcent
  have h318 : Hyp318 T (Subgroup.normalizer (L : Set G)) L (fsuV T I) :=
    { inM := ⟨isMaxTwoLocal_M h331 hyp, hyp.normal⟩
      nonempty := ⟨H, hH⟩
      perfect := (C2Nine.oTwoUpper_eq_of_perfect hyp.fsu.faithful.1.2.1.2.1).symm
      le_M := Subgroup.le_normalizer
      normal := le_rfl
      unique := isUniqueM_LT h331 hyp
      reduced := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hVred⟩
      centralizer := hcent }
  rcases theorem318_three hC58 h317 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.sylow h318 with h | ⟨-, hZ, -⟩
  · exact absurd hJ h.1
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (hZ H hH).trans inf_le_right

theorem le_of_dvd_two_pow_sub_one (h1102 : Stmt11_0_2) (h1104 : Stmt11_0_4)
    (hyp : Hyp11 G T L I n) (hLJ : L = ⁅L, thompsonJ T⁆) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ 2 ^ n - 1) {Dp : Subgroup G} (hDM : Dp ≤ Subgroup.normalizer (L : Set G))
    (hDp : ∀ x ∈ Dp, x ^ p = 1) : Dp ≤ L := by
  have : Fact p.Prime := ⟨hp⟩
  have h04 := h1104 G T L I n hyp
  have hpd2 : p ∣ 2 ^ (2 * n) - 1 := by
    refine hpd.trans ⟨2 ^ n + 1, ?_⟩
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ n * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [two_mul, pow_add]
    zify [h1, h3]
    ring
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]; exact L.one_mem
  have hord : orderOf x = p := orderOf_eq_prime (hDp x hx) hx1
  have hres : ∀ q : ℕ, q.Prime → oPrimeResidualOf q (Subgroup.normalizer (L : Set G)) = L →
      orderOf x = q → x ∈ L := fun q _ hq hxq => by
    rw [← hq]
    exact Subgroup.subset_closure ⟨hDM hx, 1, by rw [hxq, pow_one]⟩
  rcases kind_cases h1102 hyp with hk | hk | hk
  · by_cases hp3 : p = 3
    · exact h04.2 hk (even_of_three_dvd (hp3 ▸ hpd)) x (hDM hx) (hp3 ▸ hord)
        (Or.inr (Or.inl hLJ))
    · have h3 : 3 < p := by
        have := hp.two_le
        omega
      exact hres p hp (h04.1 p hp (Or.inr ⟨hk, hpd, h3⟩)) hord
  · exact hres p hp (h04.1 p hp (Or.inl ⟨Or.inl hk, hpd2⟩)) hord
  · exact hres p hp (h04.1 p hp (Or.inl ⟨Or.inr hk, hpd2⟩)) hord

theorem stmt11_3_5_of (hNF : NatFacts) (hE22 : E2.E22Statement) (hSchur : InputSchurSL2)
    (hL2 : DerivedL2List) (hTwo : DerivedTwoComponents) (hDHB : DerivedHallBorel)
    (hCP : FactCartanPower) (hFC : FactCentralizerTwo) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2)
    (h1104 : Stmt11_0_4) (h1121 : Stmt11_2_1) (h1122 : Stmt11_2_2) (h1133 : Stmt11_3_3) :
    Stmt11_3_5 := by
  intro G _ _ T L I n V₁ H hyp hV₁ h31 hnot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hH := h31.hstar
  have hLJ := eq_commutator_thompsonJ_of_moves hC58 h317 h3228 hFC h331 h1102 hyp hH h31.moves
  have hk2n : E1.nParam H ≤ (2 * n : ℕ) := by
    rcases h1121 G T L I n hyp H hH with h | h
    · exact h.trans (by exact_mod_cast (by omega : n ≤ 2 * n))
    · exact h.2.2.2.2
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hk2n)
  have hkle : k ≤ 2 * n := by rw [← hk] at hk2n; exact_mod_cast hk2n
  have hkn : n ≤ k := by
    obtain ⟨-, V₂, -, -, hV₂, -⟩ := SecA.exists_isVi hNF h1102 hyp
    have hV := isElemAbelian_fsuV hyp
    have hs := sParam_le_nParam hyp h31 (h1133 G T L I n V₁ H hyp hV₁ h31 hnot) hV
    rw [← hk] at hs
    by_cases hG2 : KindG2 L (fsuV T I) n
    · have hm := (h1122 G T L I n (2 * n) V₁ V₂ hyp hV₁ hV₂ (Or.inl ⟨hG2, rfl⟩)).2.2.2.1 hV
      rw [hm] at hs
      have : 2 * n ≤ k := by exact_mod_cast hs
      omega
    · have hm := (h1122 G T L I n n V₁ V₂ hyp hV₁ hV₂ (Or.inr ⟨hG2, rfl⟩)).2.2.2.1 hV
      rw [hm] at hs
      exact_mod_cast hs
  have hk2 : 2 ≤ k := le_trans hyp.one_lt hkn
  have hk' : E1.nParam H = k := hk.symm
  have hns : ¬ Group.IsSolvable ↥H := fun hsol => by
    have h1 := E1.solvable_nParam_le_one hsol
    rw [hk'] at h1
    have : k ≤ 1 := by exact_mod_cast h1
    omega
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, -⟩ := hE22 G H T (H ⊓ M)
    (minParabolic_of_isHStar h331 hyp hH)
    (sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hH.1.2) hns
  have hKperf : ⁅K, K⁆ = K := (show quasithinIsCComponent K H from hKc).2.1
  have hiso : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
    obtain ⟨F, hF, hFf, hFc, φ, hφs, hφk⟩ :=
      hL2 G T L I n H K k hyp hH h31.moves hk' hk2 hKc hHK hq hcases
    have hinj := hSchur k hk2 F hFc (↥K ⧸ CFSG.pCore 2 ↥K) φ hφs
      (commutator_quotient_eq_top hKperf _)
      (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot) hφk
    exact ⟨F, hF, hFf, hFc, ⟨MulEquiv.ofBijective φ ⟨hinj, hφs⟩⟩⟩
  have hO2 := oTwoUpper_eq_conjClosure hKperf hyp.fsu.sylow.1 hHK
  refine ⟨k, hk', K, hKc, hO2, hiso, fun hk2n' => ?_⟩
  by_contra hne
  have hTK : ¬ T ≤ Subgroup.normalizer (K : Set G) := by
    intro hTK
    apply hne
    have hHN : H ≤ Subgroup.normalizer (K : Set G) := hHK ▸ sup_le Subgroup.le_normalizer hTK
    rw [hO2, conjClosure_eq_of_le_normalizer hHN]
  have hn1 : 1 < E1.nParam H := by rw [hk']; exact_mod_cast (by omega : 1 < k)
  obtain ⟨D, hD, hDab, hTD⟩ := hDHB G T M H hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow ⟨isMaxTwoLocal_M h331 hyp, hyp.normal⟩ (normalizer_T_le h331 hyp) hH hn1
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hyp.one_lt
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have hpk : p ∣ 2 ^ k - 1 := by
    rcases eq_or_lt_of_le hkn with h | h
    · rw [← h]; exact hpd
    · rw [hk2n' h]
      refine hpd.trans ⟨2 ^ n + 1, ?_⟩
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h3 : 1 ≤ 2 ^ n * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      rw [two_mul, pow_add]
      zify [h1, h3]
      ring
  obtain ⟨t, htT, htD, d, hdD, hdp, hdt⟩ := hTwo G T L I n H K D k p hyp hH hKc hHK hcases hTK hk2
    hk' hiso hD hDab hTD hp hp2 hpk
  set Dp := torsionSub D hDab p with hDpdef
  have hdDp : d ∈ Dp := mem_torsionSub.mpr ⟨hdD, hdp⟩
  have hDpM : Dp ≤ M := fun x hx => (hD.1 (mem_torsionSub.mp hx).1).2
  have hDpL : Dp ≤ L :=
    le_of_dvd_two_pow_sub_one h1102 h1104 hyp hLJ hp hp2 hpd hDpM fun x hx =>
      (mem_torsionSub.mp hx).2
  have hNDp : T ⊓ Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Dp : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs z hz
    refine mem_torsionSub.mpr ⟨(Subgroup.mem_normalizer_iff.mp hs.2 z).mp
      (mem_torsionSub.mp hz).1, ?_⟩
    rw [conj_pow, (mem_torsionSub.mp hz).2, mul_one, mul_inv_cancel]
  have hTX : T ≤ H ⊓ M := le_inf hH.1.1 hyp.normal
  have hTS : QuasithinUnique.IsSylowTwoOf T (H ⊓ M) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTX
  have hDpT : (Dp : Set G) * (T : Set G) = (T : Set G) * (Dp : Set G) :=
    mul_comm_sylow_of_normalizes (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M))
      (B6.pCoreOf_two_le_of_isSylowTwoOf hTS) hTX (fun x hx => hD.1 (mem_torsionSub.mp hx).1)
      hTD hNDp
  have htDp : t ∈ Subgroup.normalizer (Dp : Set G) := hNDp ⟨htT, htD⟩
  obtain ⟨r, hr⟩ := hCP G L (fsuV T I) T Dp n p (isElemAbelian_fsuV hyp) hyp.one_lt
    (L_le_normalizer_fsuV hyp) (commutator_fsuV_eq_self hyp) (natModuleOf_fsuV h1102 hyp)
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right) (T_le_normalizer_fsuV T I)
    hyp.normal hp hp2 hDpL (isElemAbelian_torsionSub D hDab p) hDpT t htT htDp
  have hDpC : ∀ x ∈ Dp, x ∈ Subgroup.centralizer (fsuV T I : Set G) → x = 1 := by
    intro x hx hxC
    have hxO : x ∈ pCoreOf 2 L := by
      rw [← centralizer_eq_pCoreOf h1102 hyp]
      exact ⟨hDpL hx, hxC⟩
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨x, hxO⟩
    have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.gcd (2 ^ j) p = 1 :=
      Nat.Coprime.pow_left j ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have := pow_gcd_eq_one.mpr ⟨hj', (mem_torsionSub.mp hx).2⟩
    rwa [hcop, pow_one] at this
  apply hdt
  have h2 : t * d * t⁻¹ * (d ^ r)⁻¹ ∈ Dp :=
    Dp.mul_mem ((Subgroup.mem_normalizer_iff.mp htDp d).mp hdDp) (Dp.inv_mem (Dp.pow_mem hdDp r))
  have h3 := hDpC _ h2 (hr d hdDp)
  rw [mul_inv_eq_one.mp h3]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) r

end CFSG.Quasithin.Vol2.Ch11.SecB
