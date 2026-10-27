module

public import CFSG.RankThree.PartTwo.Sec20.SimsYKO3Local
public import CFSG.RankThree.PartTwo.Sec20.SimsKO3Layer
import CFSG.RankThree.PartTwo.Sec20.SimsKO3Five
import CFSG.RankThree.PartTwo.Sec20.SimsYKO3Bridge
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankBridge
import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Main

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step204YKO3CommFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        yTwenty X c ≤ kTwenty M c ⊔ inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c) →
        Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 2 (GaloisField 2 2)) →
        (i = 2 ∨ j = 2) →
          ∀ k ∈ kTwenty M c,
            ∀ o ∈ SimsYKO3.oTwoPCore 5 (inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c)),
              k * o * k⁻¹ * o⁻¹ ∈
                CFSG.Open.pCoreOf 2 (inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c))

namespace SimsYKO3

open CFSG.HardMathSupport.Solomon.UniquenessMaximal (jOf jOneOf omegaOneZ tripleOf)
open CFSG.HardMathSupport.Solomon.Coordinator.I28_8 (pair_zero_two th1J1Factorization)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_le_pCoreOf_two {K O : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (O : Set G)) (h3 : Nat.Coprime 3 (Nat.card O))
    (hs : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) (h3K : 3 ∣ Nat.card (K ⧸ CFSG.pCore 2 K)) :
    K ⊓ O ≤ CFSG.Open.pCoreOf 2 K := by
  set Q := CFSG.pCore 2 K with hQ
  set D : Subgroup K := (K ⊓ O).subgroupOf K with hD
  have hDn : D.Normal := by
    refine ⟨fun x hx h => ?_⟩
    rw [hD, Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨K.mul_mem (K.mul_mem h.2 hx.1) (K.inv_mem h.2),
      (Subgroup.mem_normalizer_iff.mp (hKN h.2) x).mp hx.2⟩
  haveI : (D.map (QuotientGroup.mk' Q)).Normal := hDn.map _ (QuotientGroup.mk'_surjective Q)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.map (QuotientGroup.mk' Q)) with h | h
  · intro x hx
    have h1 : QuotientGroup.mk' Q ⟨x, hx.1⟩ ∈ D.map (QuotientGroup.mk' Q) :=
      ⟨_, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨x, hx.1⟩, h1, rfl⟩
  · have h1 : Nat.card (K ⧸ Q) ∣ Nat.card O := by
      have h2 := Subgroup.card_map_dvd (H := D) (QuotientGroup.mk' Q)
      rw [h, Subgroup.card_top] at h2
      refine h2.trans ?_
      rw [hD, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact absurd (h3K.trans h1) ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3)

theorem comm_mem_oTwoPCore {K O : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (O : Set G)) (h3 : Nat.Coprime 3 (Nat.card O))
    (hs : IsSimpleGroup (K ⧸ CFSG.pCore 2 K)) (h3K : 3 ∣ Nat.card (K ⧸ CFSG.pCore 2 K))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hW : oTwoPCore p O ≤ Subgroup.normalizer (K : Set G))
    {k o : G} (hk : k ∈ K) (ho : o ∈ oTwoPCore p O) :
    k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O := by
  have : Fact p.Prime := ⟨hp⟩
  have hkW : k * o * k⁻¹ ∈ oTwoPCore p O :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoPCore p hKN hk) o).mp ho
  have hok : o * k⁻¹ * o⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hW ho) k⁻¹).mp (K.inv_mem hk)
  have hzW : k * o * k⁻¹ * o⁻¹ ∈ oTwoPCore p O :=
    (oTwoPCore p O).mul_mem hkW ((oTwoPCore p O).inv_mem ho)
  have hzK : k * o * k⁻¹ * o⁻¹ ∈ K := by
    have := K.mul_mem hk hok
    rwa [show k * (o * k⁻¹ * o⁻¹) = k * o * k⁻¹ * o⁻¹ by group] at this
  have hz2 : k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
    inf_le_pCoreOf_two hKN h3 hs h3K ⟨hzK, oTwoPCore_le p O hzW⟩
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hz2⟩
  obtain ⟨w, hw, hwz⟩ := hzW
  obtain ⟨b, hb⟩ := CFSG.pCore_isPGroup (p := p) (G := O ⧸ CFSG.pCore 2 O)
    ⟨QuotientGroup.mk' (CFSG.pCore 2 O) w, hw⟩
  have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 O) w) ∣ 2 ^ a := by
    refine (orderOf_map_dvd _ w).trans ?_
    rw [← Subgroup.orderOf_coe, show (w : G) = k * o * k⁻¹ * o⁻¹ from hwz,
      ← Subgroup.orderOf_mk _ hz2]
    exact orderOf_dvd_of_pow_eq_one ha
  have hpb : orderOf (QuotientGroup.mk' (CFSG.pCore 2 O) w) ∣ p ^ b :=
    orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hb)
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 hpb)
  exact ⟨w, (QuotientGroup.eq_one_iff w).mp h1, hwz⟩

omit [Finite G] in
private theorem fix_of_comm {K O : Subgroup G} (hKN : K ≤ Subgroup.normalizer (O : Set G)) {p : ℕ}
    (h : ∀ k ∈ K, ∀ o ∈ oTwoPCore p O, k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O)
    (k : K) {y : O ⧸ CFSG.pCore 2 O} (hy : y ∈ CFSG.pCore p (O ⧸ CFSG.pCore 2 O)) :
    Res11.quotAction hKN k y = y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 O) y
  exact Res11.quotAction_fix_of_comm_mem hKN k x (h k k.2 x ⟨x, hy, rfl⟩)

private theorem fix_of_L3 {K O : Subgroup G} [Group.IsPerfect K]
    (hK : Nonempty (K ⧸ CFSG.pCore 2 K ≃* projSL 3 (GaloisField 2 1)))
    (hKN : K ≤ Subgroup.normalizer (O : Set G)) (hrank : CFSG.Open.pRank 5 O ≤ 2) (k : K)
    {y : O ⧸ CFSG.pCore 2 O} (hy : y ∈ CFSG.pCore 5 (O ⧸ CFSG.pCore 2 O)) :
    Res11.quotAction hKN k y = y := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P := CFSG.pCore 5 (O ⧸ CFSG.pCore 2 O) with hP
  let ρ : K →* MulAut P := (MulAut.characteristic P).comp (Res11.quotAction hKN)
  have hrankP : CFSG.pRank 5 P ≤ 2 :=
    ((RankThree.PartOne.FixedRank36.pRank_le_of_injective P.subtype P.subtype_injective).trans
      (Res11.pRank_quotient_le O (by norm_num) (by norm_num))).trans hrank
  have hρ : ρ = 1 := eq_one_of_pRank_le_two_five hK CFSG.pCore_isPGroup hrankP ρ
  exact congrArg (fun σ : MulAut P => ((σ ⟨y, hy⟩ : P) : O ⧸ CFSG.pCore 2 O))
    (DFunLike.congr_fun hρ k)

private theorem comm_of_fix {K O : Subgroup G} [Group.IsPerfect K]
    (hKN : K ≤ Subgroup.normalizer (O : Set G)) (h3 : Nat.Coprime 3 (Nat.card O))
    (hP : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ k : K, ∀ y ∈ CFSG.pCore p (O ⧸ CFSG.pCore 2 O),
      Res11.quotAction hKN k y = y)
    (hL : ∀ k ∈ K, ∀ o ∈ oTwoLayer O, k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O) :
    ∀ k ∈ K, ∀ o ∈ O, k * o * k⁻¹ * o⁻¹ ∈ CFSG.Open.pCoreOf 2 O := by
  intro k hk o ho
  set Q := CFSG.pCore 2 O with hQ
  set σ := Res11.quotAction hKN with hσdef
  have hfixP : ∀ p : ℕ, p.Prime → ∀ (k' : K), ∀ y ∈ CFSG.pCore p (O ⧸ Q), σ k' y = y := by
    intro p hp k' y hy
    by_cases hp5 : 5 ≤ p
    · exact hP p hp hp5 k' y hy
    · have hp23 : p = 2 ∨ p = 3 := by
        have := hp.two_le
        interval_cases p
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hp (by decide)
      rcases hp23 with rfl | rfl
      · rw [Sec18.pCore_quotient_pCore_eq_bot, Subgroup.mem_bot] at hy
        rw [hy, map_one]
      · rw [Res11.eq_one_of_mem_pCore_three h3 hy, map_one]
  have hfixF : ∀ (k' : K), ∀ y ∈ CFSG.fittingSubgroup (O ⧸ Q), σ k' y = y := by
    intro k' y hy
    rw [CFSG.fitting_eq_sup_pCore] at hy
    have hle : (⨆ p : (Nat.card (O ⧸ Q)).primeFactors.attach, CFSG.pCore p.1.1 (O ⧸ Q)) ≤
        RankThree.PartOne.FixedRank36.fixedSub (σ k') :=
      iSup_le fun p z hz => hfixP p.1.1 (Nat.prime_of_mem_primeFactors p.1.2) k' z hz
    exact hle hy
  have hfixE : ∀ (k' : K), ∀ y ∈ CFSG.layer (O ⧸ Q), σ k' y = y := by
    intro k' y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q y
    exact Res11.quotAction_fix_of_comm_mem hKN k' x (hL k' k'.2 x ⟨x, hy, rfl⟩)
  have hfix : ∀ k' : K, ∀ y ∈ CFSG.generalizedFitting (O ⧸ Q), σ k' y = y := by
    intro k' y hy
    have hle : CFSG.generalizedFitting (O ⧸ Q) ≤
        RankThree.PartOne.FixedRank36.fixedSub (σ k') :=
      sup_le (fun z hz => hfixF k' z hz) (fun z hz => hfixE k' z hz)
    exact hle hy
  have hσ : σ = 1 := Res11.eq_one_of_fix_generalizedFitting σ hfix
  exact Res11.comm_mem_of_quotAction_fix hKN ⟨k, hk⟩ ⟨o, ho⟩ (by rw [← hσdef, hσ]; rfl)

omit [Finite G] in
theorem le_of_fac {H M A B : Subgroup G} (hA : A ≤ M) (hB : B ≤ M)
    (h : ((A ⊓ H : Subgroup G) : Set G) * ((B ⊓ H : Subgroup G) : Set G) = (H : Set G)) :
    H ≤ M := by
  intro x hx
  rw [← SetLike.mem_coe, ← h] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact M.mul_mem (hA ha.1) (hB hb.1)

private theorem le_of_fourChar {S H M : Subgroup G} (hM : M ≠ ⊤) (hSH : S ≤ H)
    (hS2 : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.relIndex H) (hsol : Group.IsSolvable H)
    (h3 : ¬ 3 ∣ Nat.card H)
    (hO : ∀ N : Subgroup G, N ≤ H → H ≤ Subgroup.normalizer (N : Set G) → ¬ 2 ∣ Nat.card N →
      N = ⊥)
    {i j : Fin 4} (hij : i ≠ j) (hi : i ≠ 3) (hj : j ≠ 3)
    (h5 : ¬ 5 ∣ Nat.card H ∨ (i ≠ 2 ∧ j ≠ 2))
    (hNi : Subgroup.normalizer (Sec18.fourChar S i : Set G) ≤ M)
    (hNj : Subgroup.normalizer (Sec18.fourChar S j : Set G) ≤ M) : H ≤ M := by
  have hne2 : Subgroup.normalizer (Sec18.fourChar S 2 : Set G) ≤ M → Sec18.fourChar S 2 ≠ ⊥ := by
    intro hN hbot
    apply hM
    rw [hbot, Subgroup.normalizer_eq_top] at hN
    exact top_le_iff.mp hN
  have h01 : Subgroup.normalizer (Sec18.fourChar S 0 : Set G) ≤ M →
      Subgroup.normalizer (Sec18.fourChar S 1 : Set G) ≤ M → H ≤ M := fun h0 h1 =>
    le_of_fac (by rwa [fourChar_one_eq S] at h1) (by rwa [fourChar_zero_eq S] at h0)
      (pair_zero_two hsol h3 hO hSH hS2 hidx)
  have h02 : ¬ 5 ∣ Nat.card H → Subgroup.normalizer (Sec18.fourChar S 0 : Set G) ≤ M →
      Subgroup.normalizer (Sec18.fourChar S 2 : Set G) ≤ M → H ≤ M := fun h5 h0 h2 =>
    le_of_fac (A := Subgroup.normalizer (tripleOf S 2 : Set G))
      (by rwa [fourChar_zero_eq S] at h0) (by rwa [fourChar_two_eq S hS2 (hne2 h2)] at h2)
      (th1J1Factorization G H S hsol h3 h5 hO hSH hS2 hidx 2 (by decide))
  have h12 : ¬ 5 ∣ Nat.card H → Subgroup.normalizer (Sec18.fourChar S 1 : Set G) ≤ M →
      Subgroup.normalizer (Sec18.fourChar S 2 : Set G) ≤ M → H ≤ M := fun h5 h1 h2 =>
    le_of_fac (A := Subgroup.normalizer (tripleOf S 0 : Set G))
      (by rwa [fourChar_one_eq S] at h1) (by rwa [fourChar_two_eq S hS2 (hne2 h2)] at h2)
      (th1J1Factorization G H S hsol h3 h5 hO hSH hS2 hidx 0 (by decide))
  have hcases : ∀ i : Fin 4, i ≠ 3 → i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases hcases i hi with rfl | rfl | rfl <;> rcases hcases j hj with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact h01 hNi hNj
  · exact h02 (h5.resolve_right fun h => h.2 rfl) hNi hNj
  · exact h01 hNj hNi
  · exact absurd rfl hij
  · exact h12 (h5.resolve_right fun h => h.2 rfl) hNi hNj
  · exact h02 (h5.resolve_right fun h => h.1 rfl) hNj hNi
  · exact h12 (h5.resolve_right fun h => h.1 rfl) hNj hNi
  · exact absurd rfl hij

private theorem oTwoPCore_le_of_fourChar {X O R M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hOX : O ≤ X) (hXO : X ≤ Subgroup.normalizer (O : Set G))
    (h3 : Nat.Coprime 3 (Nat.card O)) (hR2 : IsPGroup 2 R) (hRX : R ≤ X)
    (hQR : CFSG.Open.pCoreOf 2 O ≤ R) (hX2R : CFSG.Open.pCoreOf 2 X ≤ R)
    (hchar : CFSG.QuasithinUnique.CharTwo X) (hM : M ≠ ⊤)
    {i j : Fin 4} (hij : i ≠ j) (hi : i ≠ 3) (hj : j ≠ 3) (h5 : p ≠ 5 ∨ (i ≠ 2 ∧ j ≠ 2))
    (hNi : Subgroup.normalizer (Sec18.fourChar R i : Set G) ≤ M)
    (hNj : Subgroup.normalizer (Sec18.fourChar R j : Set G) ≤ M) : oTwoPCore p O ≤ M := by
  obtain ⟨hsol, h3', h5', hO, hidx⟩ :=
    oTwoPCore_sup_package hp hp5 hOX hXO h3 hR2 hRX hQR hX2R hchar
  exact le_sup_left.trans (le_of_fourChar hM le_sup_right hR2 hidx hsol h3' hO hij hi hj
    (h5.imp h5' id) hNi hNj)

theorem le_of_mem_max {R Z KT : Subgroup G}
    (hmax : R ∈ maxInvariantPiSubgroups ⊤ KT (piOf 2)) (hZ2 : IsPGroup 2 Z)
    (hKZ : KT ≤ Subgroup.normalizer (Z : Set G)) (hRZ : R ≤ Subgroup.normalizer (Z : Set G)) :
    Z ≤ R := by
  have hmax' := mem_maxInvariantPiSubgroups_iff.mp hmax
  obtain ⟨-, hR2, hKR⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hmax'.1
  have hmem : (Z ⊔ R : Subgroup G) ∈ invariantPiSubgroups ⊤ KT (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr
      ⟨le_top, hZ2.to_sup_of_normal_left' hR2 hRZ,
        fun x hx => Res6.mem_normalizer_sup (hKZ hx) (hKR hx)⟩
  exact le_sup_left.trans (hmax'.2 _ hmem le_sup_right).le

private theorem oTwoPCore_le_M {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P : Subgroup G} (hset : Setting204 G A M L N c T i j P) {X O : Subgroup G}
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) (hOX : O ≤ X)
    (hXO : X ≤ Subgroup.normalizer (O : Set G)) (h3 : Nat.Coprime 3 (Nat.card O)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h5 : p ≠ 5 ∨ (i ≠ 2 ∧ j ≠ 2)) : oTwoPCore p O ≤ M := by
  set R := CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) with hR
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hRX : R ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX
  have hQR : CFSG.Open.pCoreOf 2 O ≤ R :=
    le_of_mem_max hset.maxInvariant (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 O)
      ((hKTX.trans hXO).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O))
      ((hRX.trans hXO).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O))
  have hX2R : CFSG.Open.pCoreOf 2 X ≤ R :=
    le_of_mem_max hset.maxInvariant (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
      (hKTX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
      (hRX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
  have : IsSimpleGroup G := hset.isSimpleGroup
  have hM : M ≠ ⊤ := ne_top_of_pCoreOf_ne_bot hset.nonabelian
    (pCoreOf_ne_bot_of_isMaximalTwoLocal hset.mem_scriptM.1)
  exact oTwoPCore_le_of_fourChar hp hp5 hOX hXO h3 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    hRX hQR hX2R (hset.charTwoType X hX.1.1) hM hset.ne hset.ne_three_left hset.ne_three_right
    h5 hset.normalizer_left hset.normalizer_right

theorem rank_le_two {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4}
    {P : Subgroup G} (hset : Setting204 G A M L N c T i j P) {X O : Subgroup G}
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) (hOX : O ≤ X) :
    ∀ p : ℕ, p.Prime → 5 ≤ p → CFSG.Open.pRank p O ≤ 2 := by
  intro p hp hp5
  have hloc : CFSG.Open.pRank p X ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
    le_csSup ⟨Nat.card G, by
      rintro _ ⟨Z, -, rfl⟩
      exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp Z).trans
        (Subgroup.card_le_card_group Z)⟩ ⟨X, hX.1.1, rfl⟩
  have hlt := hset.localRank_lt p hp (by omega)
  exact (CFSG.SectionRank.pRank_mono hp.one_lt hOX).trans (Nat.lt_succ_iff.mp
    (hloc.trans_lt hlt))

end SimsYKO3

theorem step204YKO3CommSmall_of_five
    (h5 : Step204YKO3CommFive) :
    Step204YKO3CommSmall := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hle htype k hk o ho
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup G := hset.isSimpleGroup
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c with hYdef
  set O := inSubgroup (CFSG.pPrimeCore 3) Y with hOdef
  have hKX : K ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hYX : Y ≤ X := Res6.normalClosureIn_le_self (hKX (self_mem_normalClosureIn M c))
  have hOX : O ≤ X := (Res6.inSubgroup_pPrimeCore_le 3 Y).trans hYX
  have hXtop : X ≠ ⊤ := by
    obtain ⟨Q, hQ1, hQ2, hXQ⟩ := hX.1.1
    rw [hXQ]
    exact Late.normalizer_ne_top_of_isPGroup_two hset.nonabelian hQ2 hQ1
  have hOtop : O ≠ ⊤ := fun h => hXtop (top_le_iff.mp (h ▸ hOX))
  have hperf : Group.IsPerfect K := isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
  have hKO : K ≤ Subgroup.normalizer (O : Set G) :=
    hKY.trans (Res6.le_normalizer_inSubgroup_pPrimeCore 3 Y)
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    (le_normalizer_normalClosureIn X c).trans
      (Res6.normalizer_le_normalizer_inSubgroup_pPrimeCore 3 Y)
  have hO3 : Nat.Coprime 3 (Nat.card O) := Res6.coprime_card_inSubgroup_pPrimeCore 3 Y
  have hrank := SimsYKO3.rank_le_two hset hX hOX
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  obtain ⟨hs, h3K⟩ := SimsYKO3.simple_three_dvd_small htype
  haveI := hperf
  refine SimsYKO3.comm_of_fix hKO hO3 (fun p hp hp5 k' y hy => ?_)
    (SimsYKO3.kO3CentLayer_small hset.kProper hOtop hperf htype hKO hO3 hrank) k hk o ho
  have hW : (p ≠ 5 ∨ (i ≠ 2 ∧ j ≠ 2)) → Res11.quotAction hKO k' y = y := fun hcond =>
    SimsYKO3.fix_of_comm hKO (fun k hk o ho => SimsYKO3.comm_mem_oTwoPCore hKO hO3 hs h3K hp
      (by omega) ((SimsYKO3.oTwoPCore_le_M hset hX hOX hXO hO3 hp hp5 hcond).trans hMK) hk ho)
      k' hy
  rcases eq_or_ne p 5 with rfl | hp5ne
  · rcases htype with he | he
    · exact SimsYKO3.fix_of_L3 he hKO (hrank 5 hp hp5) k' hy
    · by_cases hij2 : i = 2 ∨ j = 2
      · exact SimsYKO3.fix_of_comm hKO
          (h5 G A M L N c T i j P hset X hX hXM hm hle he hij2) k' hy
      · exact hW (Or.inr (not_or.mp hij2))
  · exact hW (Or.inl hp5ne)

end CFSG.RankThree.PartTwo.Sec20
