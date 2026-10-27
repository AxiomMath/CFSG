module

public import CFSG.Quasithin.Vol2.Ch11SecB35C
public import CFSG.Quasithin.Vol2.Ch11SecB35
public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftE22

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped MatrixGroups Pointwise

@[expose] def Field11_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ H K : Subgroup G) (k : ℕ)
    (F : Type) [Field F] [Finite F],
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → Hyp11_3_1 T L I n V₁ H →
    ¬ Concl11_3_2 T L I n V₁ H → K ∈ cComp H → H = K ⊔ T →
    E2.E22LieCases H T (H ⊓ Subgroup.normalizer (L : Set G)) K →
    Nat.card F = 2 ^ k → 2 ≤ k →
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
      (k : ℕ∞) ≤ E1.nParam H

theorem stmt11_3_5_ofF (hNF : NatFacts) (hE22 : E2.E22StatementC) (hSchur : InputSchurSL2)
    (hL2 : DerivedL2ListC) (hFld : Field11_3_5) (hTwo : DerivedTwoComponents)
    (hDHB : DerivedHallBorel)
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
  have hmin := minParabolic_of_isHStar h331 hyp hH
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, -⟩ := E2.E22StatementC.exists_cases hE22 hmin
    (sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hH.1.2) hns
  have hKperf : ⁅K, K⁆ = K := (show quasithinIsCComponent K H from hKc).2.1
  have hn1 : 1 < E1.nParam H := by rw [hk']; exact_mod_cast (by omega : 1 < k)
  obtain ⟨f, hfH, hf2, F, hF, hFf, hFc, φ, hφs, hφk⟩ :=
    hL2 G T L I n H K hyp hH h31.moves hn1 hKc hHK hq hcases
  have hinj := hSchur f hf2 F hFc (↥K ⧸ CFSG.pCore 2 ↥K) φ hφs
    (commutator_quotient_eq_top hKperf _) (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot) hφk
  have hisoF : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨MulEquiv.ofBijective φ ⟨hinj, hφs⟩⟩
  have hfle := hFld G T L I n V₁ H K f F hyp hV₁ h31 hnot hKc hHK
    (e22LieCases_of_e22CasesC hn1 hcases) hFc hf2 hisoF
  have hfk : f = k := by
    rw [hk'] at hfH hfle
    have h1 : k ≤ f := by exact_mod_cast hfH
    have h2 : f ≤ k := by exact_mod_cast hfle
    omega
  have hFk : Nat.card F = 2 ^ k := hfk ▸ hFc
  have hiso : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨F, hF, hFf, hFk, hisoF⟩
  have hO2 := oTwoUpper_eq_conjClosure hKperf hyp.fsu.sylow.1 hHK
  refine ⟨k, hk', K, hKc, hO2, hiso, fun hk2n' => ?_⟩
  by_contra hne
  have hTK : ¬ T ≤ Subgroup.normalizer (K : Set G) := by
    intro hTK
    apply hne
    have hHN : H ≤ Subgroup.normalizer (K : Set G) := hHK ▸ sup_le Subgroup.le_normalizer hTK
    rw [hO2, conjClosure_eq_of_le_normalizer hHN]
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
  have hcases' : E2.E22Cases H T (H ⊓ M) K := by
    have : CharP F 2 := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (f := k) (by rw [← Nat.card_eq_fintype_card, hFk])
    have h4F : 4 ≤ Nat.card F := by
      rw [hFk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    obtain ⟨e⟩ := hisoF
    obtain ⟨⟨eK⟩, -⟩ := E1.RootLift.star_facts (A := ⊥) h4F hmin hKc e bot_le
    exact e22Cases_of_e22CasesC_of_not_le hcases hTK hk2 hk' hFk eK
  obtain ⟨t, htT, htD, d, hdD, hdp, hdt⟩ := hTwo G T L I n H K D k p hyp hH hKc hHK hcases'
    hTK hk2 hk' hiso hD hDab hTD hp hp2 hpk
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
