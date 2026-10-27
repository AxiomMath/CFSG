module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S208KCommon
public import CFSG.Quasithin.Vol2.Ch11SecAKE13
import CFSG.LocalAnalysis.UniquenessCase.UC22S208KParab
import CFSG.RankThree.PartOne.S12K.Rigidity
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Blueprint

private theorem s208k_cube_sub_one (x : ℕ) (hx : 1 ≤ x) :
    x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by
  have : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  zify [hx, this]
  ring

theorem s208k_dvd_of_dvd_ordTrialityD4 {m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ∣ CFSG.Open.ordTrialityD4 (2 ^ m)) : r ∣ 2 ^ (m * 12) - 1 := by
  simp only [CFSG.Open.ordTrialityD4, ← pow_mul] at h
  have hd : ∀ k, k ∣ 12 → 2 ^ (m * k) - 1 ∣ 2 ^ (m * 12) - 1 := fun k hk =>
    Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.mul_dvd_mul_left m hk)
  rcases hr.dvd_mul.mp h with h | h
  · rcases hr.dvd_mul.mp h with h | h
    · rcases hr.dvd_mul.mp h with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)) hr2
      · refine h.trans ⟨2 ^ (m * 4) - 1, ?_⟩
        have e3 : 2 ^ (m * 12) = (2 ^ (m * 4)) ^ 3 := by rw [← pow_mul]; ring_nf
        have e2 : 2 ^ (m * 8) = (2 ^ (m * 4)) ^ 2 := by rw [← pow_mul]; ring_nf
        rw [e3, e2, s208k_cube_sub_one _ Nat.one_le_two_pow]
        exact mul_comm _ _
    · exact h.trans (hd 6 (by norm_num))
  · exact h.trans (hd 2 (by norm_num))

theorem s208k_dvd_factor_of_dvd_ordTwistedF4 {m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ∣ CFSG.Open.ordTwistedF4 (2 ^ m)) :
    r ∣ 2 ^ (m * 6) + 1 ∨ r ∣ 2 ^ (m * 4) - 1 ∨ r ∣ 2 ^ (m * 3) + 1 ∨ r ∣ 2 ^ m - 1 := by
  simp only [CFSG.Open.ordTwistedF4, ← pow_mul] at h
  rcases hr.dvd_mul.mp h with h | h
  · rcases hr.dvd_mul.mp h with h | h
    · rcases hr.dvd_mul.mp h with h | h
      · rcases hr.dvd_mul.mp h with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)) hr2
        · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem s208k_dvd_of_dvd_ordTwistedF4 {m r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ∣ CFSG.Open.ordTwistedF4 (2 ^ m)) : r ∣ 2 ^ (m * 12) - 1 := by
  have hd : ∀ k, k ∣ 12 → 2 ^ (m * k) - 1 ∣ 2 ^ (m * 12) - 1 := fun k hk =>
    Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.mul_dvd_mul_left m hk)
  have ha : ∀ k, 2 * k ∣ 12 → 2 ^ (m * k) + 1 ∣ 2 ^ (m * 12) - 1 := fun k hk =>
    (Dvd.intro_left _
      (CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one (m * k)).symm).trans
      (Nat.pow_sub_one_dvd_pow_sub_one 2 (by
        rw [show 2 * (m * k) = m * (2 * k) by ring]
        exact Nat.mul_dvd_mul_left m hk))
  rcases s208k_dvd_factor_of_dvd_ordTwistedF4 hr hr2 h with h | h | h | h
  · exact h.trans (ha 6 (by norm_num))
  · exact h.trans (hd 4 (by norm_num))
  · exact h.trans (ha 3 (by norm_num))
  · exact h.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_right m 12))

theorem s208k_three_dvd_of_seven_dvd_ordTwistedF4 {m : ℕ}
    (h : 7 ∣ CFSG.Open.ordTwistedF4 (2 ^ m)) : 3 ∣ m := by
  have h7 : CFSG.Timmesfeld.IsPrimitivePrimeDivisor 7 3 :=
    ⟨by norm_num, by norm_num, fun j hj0 hj => by interval_cases j <;> norm_num⟩
  rcases s208k_dvd_factor_of_dvd_ordTwistedF4 (by norm_num) (by norm_num) h with h | h | h | h
  · exact absurd ((by norm_num : 3 ∣ 6).mul_left m) ((h7.dvd_add_one_iff (by norm_num) _).mp h).2
  · exact Nat.Coprime.dvd_of_dvd_mul_right (by norm_num)
      ((h7.dvd_sub_one_iff (by norm_num) _).mp h)
  · exact absurd (dvd_mul_left 3 m) ((h7.dvd_add_one_iff (by norm_num) _).mp h).2
  · exact (h7.dvd_sub_one_iff (by norm_num) _).mp h

theorem s208k_two_le_gcd {A : Type} [Group A] {m n : ℕ} (hn : 2 < n) (h3 : ¬ 3 ∣ n)
    (hA : IsL2 A n ∨ IsSz A n)
    (h12 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card A → r ∣ 2 ^ (m * 12) - 1) :
    2 ≤ Nat.gcd n m := by
  have hc3 : Nat.Coprime n 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  have hsq : ∀ k : ℕ, (2 ^ k) ^ 2 = 2 ^ (2 * k) := fun k => by rw [← pow_mul, mul_comm]
  have hdvd : n ∣ m * 2 := by
    rcases hA with hA | hA
    · obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega)
        (by omega)
      have hrA : r ∣ Nat.card A := by
        rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
          (LieModel.statedClassicalModel hA (by decide)), hsq]
        exact dvd_mul_of_dvd_right hr.dvd _
      have h := (hr.dvd_sub_one_iff (by omega) _).mp (h12 r hr.prime (hr.ne_two (by omega)) hrA)
      refine hc3.dvd_of_dvd_mul_right (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) ?_)
      rw [show 2 * (m * 2 * 3) = m * 12 by ring]
      exact h
    · obtain ⟨a, -, rfl, hc⟩ := s208k_card_of_isSz hA
      obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * (2 * a + 1))
        (by omega) (by omega)
      have hr1 : r ∣ 2 ^ (2 * (2 * a + 1)) + 1 := (hr.dvd_add_one_iff (by omega) _).mpr
        ⟨⟨1, by ring⟩, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩
      have hrA : r ∣ Nat.card A := by
        rw [hc, hsq]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hr1 _) _
      have h := (hr.dvd_sub_one_iff (by omega) _).mp (h12 r hr.prime (hr.ne_two (by omega)) hrA)
      refine (hc3.dvd_of_dvd_mul_right
        (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) ?_)).mul_right 2
      rw [show 4 * (m * 3) = m * 12 by ring]
      exact h
  have hg : Nat.gcd n m ≠ 1 := fun hg => by
    have := Nat.le_of_dvd (by norm_num) (Nat.Coprime.dvd_of_dvd_mul_left hg hdvd)
    omega
  have hg0 : Nat.gcd n m ≠ 0 := fun h => by
    rw [Nat.gcd_eq_zero_iff] at h
    omega
  omega

theorem s208k_exists_odd_prime_dvd {d a b : ℕ} (hd : 2 ≤ d) (hda : d ∣ a) (hdb : d ∣ b) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ a - 1 ∧ p ∣ 2 ^ b - 1 := by
  have h4 : 4 ≤ 2 ^ d :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ d - 1 ≠ 1 by omega)
  refine ⟨p, hp, ?_, hpd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hda),
    hpd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hdb)⟩
  rintro rfl
  have h2 : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
  omega

section Phi36

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KLC
open scoped Matrix Polynomial


theorem s208k_d4T36_weyl {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ w : WeylGroup TwistTag.D4.tag,
      ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x := by
  obtain ⟨w, hw⟩ := exists_smul_trialityRho hε
  refine ⟨w, fun x => ?_⟩
  rw [d4T36M_eq]
  refine Eq.symm (Eq.trans (hw (permLattice TwistTag.D4.perm.symm x)) ?_)
  exact congrArg (fun y => w • y) (permLattice_permLattice_symm x)

theorem s208k_d4T36_lang_frame {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ n : ModGL TwistTag.D4.tag L,
      twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) =
        (fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f)).map
          (rootDiagUnitHom TwistTag.D4.tag L) ∧
      ∃ g0 : ModGL TwistTag.D4.tag L, g0 ∈ adjointGroup TwistTag.D4.tag L ∧
        twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n ∧
        ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
          (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
            P ≤ (triEmb K σ L).range := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨w, hw⟩ := s208k_d4T36_weyl hε
  set n : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L w
  have hnM : n ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L w
  have hnW : weylQuotientHom TwistTag.D4.tag L ⟨n, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hnC : n ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hnM
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L n hnC
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr hnM w hnW (d4T36M ε) hw
  have hrange := triEmb_range hℓ hf hK hσ Fr hFr
  refine ⟨n, hT, g0, hg0C, hg0, fun P hPC hPF => ?_⟩
  rw [hrange]
  exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩

theorem s208k_two_le_pRank_triality_phi36 {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) :
    2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨n, hT, g0, hg0C, hg0, hrat⟩ := s208k_d4T36_lang_frame hf hK σ hσ hε (AlgebraicClosure K)
  set L := AlgebraicClosure K
  set Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hpℓ : p ≠ ℓ := by
    rintro rfl
    have h1 : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) ^ 2 + ε * ((p ^ f : ℕ) : ℤ) := by
      have hq : (p : ℤ) ∣ ((p ^ f : ℕ) : ℤ) := by exact_mod_cast dvd_pow_self p (by omega)
      exact dvd_add (dvd_pow hq (by norm_num)) (dvd_mul_of_dvd_right hq _)
    have h2 := (dvd_add_right h1).1 hpd
    have : p ∣ 1 := by exact_mod_cast h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  let Φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL TwistTag.D4.tag L :=
    (rootDiagUnitHom TwistTag.D4.tag L).comp ((d4T36TupleHom ε (ℓ ^ f)).comp
      (MonoidHom.prodMap (rootsOfUnity p L).subtype (rootsOfUnity p L).subtype))
  have hΦ : ∀ z, Φ z =
      rootDiagUnit TwistTag.D4.tag (d4T36Tuple ε (ℓ ^ f) (z.1 : Lˣ) (z.2 : Lˣ)) := fun z => rfl
  have hroot : ∀ z : (rootsOfUnity p L) × (rootsOfUnity p L),
      (z.1 : Lˣ) ^ p = 1 ∧ (z.2 : Lˣ) ^ p = 1 :=
    fun z => ⟨(mem_rootsOfUnity p _).1 z.1.2, (mem_rootsOfUnity p _).1 z.2.2⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hΦ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have h1 := congrArg d4QCoord hb
    rw [d4T36Tuple_coord, map_one] at h1
    have e0 := congrFun h1 0
    have e1 := congrFun h1 1
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e0)
  refine two_le_pRank_triality_of_hom σ hp hpℓ L n g0 hg0C hg0 hrat Φ hinj ?_
  rintro _ ⟨z, rfl⟩
  rw [hΦ, hT]
  obtain ⟨hb, hc⟩ := hroot z
  have hzp : ∀ x : Lˣ, x ^ p = 1 →
      x ^ (((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hpd
    rw [hk, zpow_mul, zpow_natCast, hx, one_zpow]
  exact ⟨_, d4T36Tuple_mem hε hFr (hzp _ hb) (hzp _ hc), rfl⟩

theorem s208k_two_le_pRank_is3D4 {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Quasithin.Is3D4 2 f X) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ 2 ^ f - 1 ∨ p ∣ (2 ^ f) ^ 2 + 2 ^ f + 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model h
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top]
  have h36 : p ∣ (2 ^ f) ^ 2 + 2 ^ f + 1 →
      2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun hd => by
    refine s208k_two_le_pRank_triality_phi36 hf hK σ hσ (ε := 1) (Or.inl rfl) hp ?_
    have := Int.natCast_dvd_natCast.mpr hd
    push_cast at this
    simpa using this
  rcases hpd with hd | hd
  · rcases CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.prime_dvd_two_pow_sub_one hf hp hd with h3 | hp5
    · exact h36 h3
    · exact two_le_pRank_triality_phi1 ⟨hp, hp5, hf, hK, fun c => hσ c, hd⟩
  · exact h36 hd

end Phi36

section Certified


variable {X : Type} [Group X] [Finite X]

theorem s208k_goal_of_is3D4 {m : ℕ} (hX : Is3D4 X m) {P : Subgroup X} {n : ℕ} (hn : 2 < n)
    (hQ : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n) : S208kGoal P n := by
  have hC := LieModel.chevalleyExceptionalModel hX (by decide)
  have hcard : Nat.card X = CFSG.Open.ordTrialityD4 (2 ^ m) :=
    CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_exceptional hC
  have hQX : Nat.card (Bar2 (Hinf P)) ∣ Nat.card X :=
    (card_quotient_dvd_card (CFSG.pCore 2 ↥(Hinf P))).trans (card_subgroup_dvd_card (Hinf P))
  obtain ⟨d, hd, hdn, hdm⟩ : ∃ d, 2 ≤ d ∧ d ∣ n ∧ d ∣ m * 3 := by
    by_cases h3 : 3 ∣ n
    · exact ⟨3, by norm_num, h3, dvd_mul_left 3 m⟩
    · exact ⟨_, s208k_two_le_gcd hn h3 hQ fun r hr hr2 hrQ =>
        s208k_dvd_of_dvd_ordTrialityD4 hr hr2 (hcard ▸ hrQ.trans hQX),
        Nat.gcd_dvd_left _ _, (Nat.gcd_dvd_right _ _).trans (dvd_mul_right m 3)⟩
  obtain ⟨p, hp, hp2, hpn, hpm⟩ := s208k_exists_odd_prime_dvd hd hdn hdm
  rw [pow_mul, s208k_cube_sub_one _ Nat.one_le_two_pow] at hpm
  exact s208k_goal_of_two_le hQ hp hp2 hpn (s208k_two_le_pRank_is3D4 hC hp (hp.dvd_mul.mp hpm))

theorem s208k_goal_of_isF4 {m : ℕ} (hX : LieModel X .twistedF4 0 2 m) {P : Subgroup X} {n : ℕ}
    (hn : 2 < n) (hQ : IsL2 (Bar2 (Hinf P)) n ∨ IsSz (Bar2 (Hinf P)) n) : S208kGoal P n := by
  have hR := (LieModel.reeTitsModel hX (by decide)).2
  have hcard := CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hR
  have hQX : Nat.card (Bar2 (Hinf P)) ∣ Nat.card X :=
    (card_quotient_dvd_card (CFSG.pCore 2 ↥(Hinf P))).trans (card_subgroup_dvd_card (Hinf P))
  obtain ⟨d, hd, hdn, hdm⟩ : ∃ d, 2 ≤ d ∧ d ∣ n ∧ d ∣ m := by
    by_cases h3 : 3 ∣ n
    · have h7 : 7 ∣ Nat.card X := (Nat.pow_sub_one_dvd_pow_sub_one 2 h3 :
        2 ^ 3 - 1 ∣ 2 ^ n - 1).trans ((s208k_two_pow_sub_one_dvd_factor hQ).trans hQX)
      exact ⟨3, by norm_num, h3, s208k_three_dvd_of_seven_dvd_ordTwistedF4 (hcard ▸ h7)⟩
    · exact ⟨_, s208k_two_le_gcd hn h3 hQ fun r hr hr2 hrQ =>
        s208k_dvd_of_dvd_ordTwistedF4 hr hr2 (hcard ▸ hrQ.trans hQX), Nat.gcd_dvd_left _ _,
        Nat.gcd_dvd_right _ _⟩
  obtain ⟨p, hp, hp2, hpn, hpm⟩ := s208k_exists_odd_prime_dvd hd hdn hdm
  exact s208k_goal_of_two_le hQ hp hp2 hpn
    (CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.two_le_pRank_is2F4 hR hp hp2 hpm)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22
