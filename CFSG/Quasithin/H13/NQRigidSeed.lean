module

public import CFSG.Quasithin.SteinbergCDPrimePlaneSylowNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.NQRigidConjugate
public import CFSG.Quasithin.H13.NQSetupPlaneAction

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) : IsSylowOf 2 T M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨h.t_le, h.sylow.1, fun hdvd => h.sylow.2 ?_⟩
  rw [← relIndex_mul_index h.t_le]
  exact hdvd.mul_right _

theorem isSylowOf_inf_l_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) :
    IsSylowOf 2 (T ⊓ L) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isSylowOf_of_qtnq h).inf_of_le_normalizer h.l_le h.eq_normalizer.le

theorem centralizer_le_of_mem_omegaOneCenter {T L M : Subgroup G} (h : QTNQ T L M) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) : centralizer {z} ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hz2⟩ := QuasithinUnique.mem_quasithinOmegaOneCenter_iff.mp hz
  have hZ1 : zpowers z ≠ ⊥ := by
    intro hb
    apply hz1
    have : z ∈ zpowers z := mem_zpowers z
    rwa [hb, mem_bot] at this
  have hZ2 : IsPGroup 2 (zpowers z) := isPGroup_two_of_card_dvd (k := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hz2)
  have hA : (centralizer (quasithinOmegaOneCenter T : Set G) : Set G) ⊆
      (centralizer (zpowers z : Set G) : Set G) := by
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff] at hx ⊢
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (hx z hz) k).eq
  have hM : {K : Subgroup G | CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal K ∧
      (centralizer (quasithinOmegaOneCenter T : Set G) : Set G) ⊆ (K : Set G)} = {M} := by
    ext K
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hK, hCK⟩
      exact h.centralizer_unique K hK hCK
    · rintro rfl
      exact ⟨h.max_two_local, h.centralizer_le⟩
  obtain ⟨hCN, hNM, -⟩ := QuasithinUnique.maxTwoLocal_centralizer_transfer hZ1 hZ2 hA hM
  intro x hx
  refine hNM (hCN ?_)
  rw [mem_centralizer_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp hx).symm k)).eq

theorem sylow_irreducible_of_qtnq
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L) (hXchar : (X.subgroupOf L).Characteristic)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2)
    (hirrL : IsFrattiniIrreducible X L) :
    IsFrattiniIrreducible X (T ⊓ L) ∧ IsFrattiniIrreducible X T := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ≤ normalizer (X : Set G) := by
    refine le_normalizer.trans ?_
    exact NQSetup.normalizer_le_normalizer_of_characteristic hXL hXchar
  have hpow : ∀ w : X ⧸ CFSG.pCore 2 X, w ^ p = 1 := fun w => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one w
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := fun w => ⟨1, by rw [pow_one, hpow]⟩
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXp⟩
  have hWel := CFSG.isElementaryAbelian_quotient_frattini (R := X ⧸ CFSG.pCore 2 X) (p := p)
  have : IsMulCommutative ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    hWel.toIsMulCommutative
  have hWp : ∀ w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X), w ^ p = 1 :=
    fun w => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hWel.exponent_dvd_p w
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have : Group.IsPerfect L := ⟨by rw [_root_.commutator_def]; exact hLC.2.1⟩
  set β : L →* MulAut ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    (normalizerFrattiniConj X).comp (inclusion hLN) with hβ
  have hβ1 : β ≠ 1 := by
    intro hb
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := (X ⧸ CFSG.pCore 2 X) ⧸
      frattini (X ⧸ CFSG.pCore 2 X)) p (by rw [hW]; exact dvd_pow_self p two_ne_zero)
    rcases hirrL (zpowers w) (by
      intro l hl y hy
      have h1 : normalizerFrattiniConj X l = 1 := by
        have h2 := DFunLike.congr_fun hb ⟨l, hl⟩
        have h3 : inclusion hLN ⟨(l : G), hl⟩ = l := Subtype.ext rfl
        rw [hβ, MonoidHom.comp_apply, h3] at h2
        exact h2
      rw [h1]
      exact hy) with h0 | ht
    · have h1 : w ∈ zpowers w := mem_zpowers w
      rw [h0, mem_bot] at h1
      rw [h1, orderOf_one] at hw
      exact hp.one_lt.ne' hw.symm
    · have h1 := Nat.card_zpowers w
      rw [hw, ht, card_top, hW] at h1
      have := Nat.pow_right_injective hp.two_le (h1.trans (pow_one p).symm)
      omega
  obtain ⟨S, hS⟩ := isSylowOf_inf_l_of_qtnq h
  have hTL : IsFrattiniIrreducible X (T ⊓ L) := by
    intro Y hY
    refine SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hp5 hWp hW β hβ1 S Y ?_
    intro s hs w hw
    have hsTL : ((s : L) : G) ∈ T ⊓ L := by
      rw [← hS]
      exact ⟨s, hs, rfl⟩
    exact hY ⟨s, hLN s.2⟩ hsTL w hw
  exact ⟨hTL, hTL.mono inf_le_left⟩

end CFSG.Quasithin.H13.NQRigid
