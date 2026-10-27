module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwA5
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwD4
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwSplit
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwInR
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwTorus
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwConj
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightInput
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwCent
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.LocalAnalysis.WeakClosure81.SU3RankRoots
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoAssembly

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration.ExcHigh
  CFSG.Assembly Multiplicative
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem exists_orderOf_eq_algebraicClosure {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hpq : p ∣ 2 ^ n + 1) :
    ∃ ζ : (AlgebraicClosure K)ˣ, orderOf ζ = p := by
  obtain ⟨ν, hν⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.exists_orderOf_eq_of_dvd_two_pow_add_one hK hpq
  refine ⟨Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (ν : Kˣ), ?_⟩
  rw [orderOf_injective (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom)
    (Units.map_injective fun a b h => (algebraMap K (AlgebraicClosure K)).injective h) (ν : Kˣ),
    ← hν, Subgroup.orderOf_coe]

private theorem mem_graphFixedRootGroup_of_pow_eq_one_twInndiag
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {h : ModGL TwistTag.E6.tag K}
    (hh : h ∈ RecipeExcLang.twInndiagGroup K σ) (hpow : h ^ p = 1) :
    h ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  have h3 := twInndiag_pow_three_mem hn hK σ hσ hh
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (p : ℤ) * a + 3 * b = 1 := by
    refine ⟨Nat.gcdA p 3, Nat.gcdB p 3, ?_⟩
    have h1 := Nat.gcd_eq_gcd_ab p 3
    rw [hcop.gcd_eq_one] at h1
    push_cast at h1
    linarith
  have hh1 : h = (h ^ p) ^ a * (h ^ 3) ^ b := by
    calc h = h ^ ((p : ℤ) * a + 3 * b) := by rw [hab, zpow_one]
      _ = (h ^ p) ^ a * (h ^ 3) ^ b := by
        rw [zpow_add, zpow_mul, zpow_mul]
        simp
  rw [hh1, hpow, one_zpow, one_mul]
  exact zpow_mem h3 b

theorem iSup_phiTwoCompIn_eq_top_twE6_of_prime
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ n + 1) (v : WeylGroup TwistTag.E6.tag)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (hlong : ExcIsLongest TwistTag.E6.tag v)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) :
    (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
      phiTwoCompIn (twistedE6RootGroup K σ) g0 γ.1) = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := by omega
  obtain ⟨ζ, hζo⟩ := exists_orderOf_eq_algebraicClosure hK hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hv : ∀ i : Fin TwistTag.E6.tag.rank,
      v • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        -Pi.single (TwistTag.E6.perm i) 1 := fun i => by
    rw [ggKGTc_eq_w0_E6 hlong]
    exact ggKGTc_w0_smul_E6 i
  obtain ⟨T0, hT0inj, hT0⟩ := exists_phiTwoTorus_twE6 (by omega : 1 ≤ n) hK σ hσ hFr hv hg0C hg0
    hpq hζo hζ
  have hT0R : ∀ x : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p),
      (((T0 x : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K)) ∈
        twistedE6RootGroup K σ := fun x =>
    mem_graphFixedRootGroup_of_pow_eq_one_twInndiag (by omega : 1 ≤ n) hK σ hσ hp hp3 (T0 x).2
      (by
        have h1 : (T0 x) ^ p = 1 := by rw [← map_pow, pow_eq_one_of_multiplicative_zmod, map_one]
        exact congrArg Subtype.val h1)
  let T : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* ↥(twistedE6RootGroup K σ) :=
    (((RecipeExcLang.twInndiagGroup K σ).subtype).comp T0).codRestrict (twistedE6RootGroup K σ)
      hT0R
  have hTcoe : ∀ x, ((T x : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      ((T0 x : ↥(RecipeExcLang.twInndiagGroup K σ)) : ModGL TwistTag.E6.tag K) := fun x => rfl
  have hTinj : Function.Injective T := fun a b hab =>
    hT0inj (Subtype.ext (by rw [← hTcoe, ← hTcoe, hab]))
  obtain ⟨c, ⟨VG, W, hVW, hdim, hVG, hW⟩, ⟨VG', W', hVW', hdim', hVG', hW'⟩⟩ :=
    exists_frame_split_twE6 hn hK σ hσ hp5 hpq hTinj
  let T' : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →* ↥(twistedE6RootGroup K σ) :=
    (MulAut.conj c).toMonoidHom.comp T
  have hT'apply : ∀ x, T' x = c * T x * c⁻¹ := fun x => rfl
  have hT'inj : Function.Injective T' := fun a b hab => by
    have h1 : c * T a * c⁻¹ = c * T b * c⁻¹ := hab
    exact hTinj (mul_left_cancel (mul_right_cancel h1))
  have hRadj : twistedE6RootGroup K σ ≤ adjointGroup TwistTag.E6.tag K := fun g hg =>
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).mp
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hg)).1
  set g0' : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL TwistTag.E6.tag K) * g0 with hg0'
  have hg0'C : g0' ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    mul_mem (CFSG.LocalAnalysis.ComponentInitial.baseChangeGL_mem_adjointGroup
      (algebraMap K (AlgebraicClosure K)) (hRadj c.2)) hg0C
  have hT' : ∀ t : Fin TwistTag.E6.tag.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((T' (ofAdd t) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        g0' * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) * g0'⁻¹ := by
    intro t
    have h1 : ((T' (ofAdd t) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        (c : ModGL TwistTag.E6.tag K) * (T (ofAdd t) : ModGL TwistTag.E6.tag K) *
          (c : ModGL TwistTag.E6.tag K)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hTcoe, hT0 t, hg0']
    group
  have hA5 := orbitRankOneGroup_le_iSup_phiTwoCompIn_a5 hn hK σ hσ hp5 hpq hζo hζ
    hg0'C hT'inj hT' hVW hdim hVG hW
  have hD4 := orbitRankOneGroup_three_le_iSup_phiTwoCompIn_d4 hn hK σ hσ (by omega) hpq
    hζo hζ hg0'C hT'inj hT' hVW' hdim' hVG' hW'
  have htop : (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
      phiTwoCompIn (twistedE6RootGroup K σ) g0' γ.1) = ⊤ := by
    refine eq_top_of_orbitRankOneGroup_le (σ := σ) _ fun a => ?_
    by_cases ha : a.val ≤ 2
    · exact hA5 a ha
    · have h3 : a = ⟨3, by decide⟩ := by
        apply Fin.ext
        have h4 : TwistTag.E6.foldedTag.rank = 4 := by decide
        have h5 : a.val < 4 := lt_of_lt_of_eq a.2 h4
        show a.val = 3
        omega
      rw [h3]
      exact hD4
  have hcinv : (c : ModGL TwistTag.E6.tag K)⁻¹ ∈ Subgroup.normalizer (twistedE6RootGroup K σ) :=
    Subgroup.le_normalizer (inv_mem c.2)
  have h5 := iSup_phiTwoCompIn_eq_top_of_baseChange_mul (R := twistedE6RootGroup K σ) hcinv htop
  have h6 : baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((c : ModGL TwistTag.E6.tag K)⁻¹) * g0' = g0 := by
    rw [hg0', ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [h6] at h5
  exact h5

theorem iSup_phiTwoCompIn_eq_top_twE6_of_four_le
    {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (v : WeylGroup TwistTag.E6.tag)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (hlong : ExcIsLongest TwistTag.E6.tag v)
    (hFr : ∀ c, Fr c = c ^ 2 ^ n) (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) :
    (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
      phiTwoCompIn (twistedE6RootGroup K σ) g0 γ.1) = ⊤ := by
  obtain ⟨p, hp, hp7, hpq⟩ :=
    CFSG.RankThree.PartTwo.Census.exists_prime_seven_le_dvd_two_pow_add_one hn
  exact iSup_phiTwoCompIn_eq_top_twE6_of_prime (by omega) hK σ hσ hp (by omega) hpq v Fr g0
    hlong hFr hg0C hg0

theorem iSup_phiTwoCompIn_eq_top_twE6_of_two
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 2) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 2) (v : WeylGroup TwistTag.E6.tag)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) (hlong : ExcIsLongest TwistTag.E6.tag v)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 2) (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v) :
    (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
      phiTwoCompIn (twistedE6RootGroup K σ) g0 γ.1) = ⊤ :=
  iSup_phiTwoCompIn_eq_top_twE6_of_prime (n := 2) (p := 5) (by norm_num) hK σ hσ (by norm_num)
    (by norm_num) (by norm_num) v Fr g0 hlong hFr hg0C hg0


theorem phiTwoTwE6GenInputNeThree_holds : PhiTwoTwE6GenInputNeThree := by
  intro K _ _ σ n hn hn3 hcard hσ v Fr g0 hv hFr hg0C hg0
  rcases (by omega : n = 2 ∨ 4 ≤ n) with rfl | h4
  · exact iSup_phiTwoCompIn_eq_top_twE6_of_two hcard σ hσ v Fr g0 hv hFr hg0C hg0
  · exact iSup_phiTwoCompIn_eq_top_twE6_of_four_le h4 hcard σ hσ v Fr g0 hv hFr hg0C hg0

theorem phiTwoTwE6GenInput_of_eight' (h8 : PhiTwoTwE6Eight) : PhiTwoTwE6GenInput :=
  phiTwoTwE6GenInput_of_eight h8 phiTwoTwE6GenInputNeThree_holds

end CFSG.StandardType.PhiTwoRootGen

end
