module

public import CFSG.Quasithin.H13.NQBlockSourceGlue
public import CFSG.Quasithin.H13.NQBlockNoEscape
public import CFSG.Quasithin.SteinbergBKNearMaximalElementaryRank
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.Quasithin.H13.NQBlockSourceCore

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open Module
open scoped IsMulCommutative commutatorElement

theorem pRank_le_two_of_surjective {p : ℕ} [hp : Fact p.Prime] {Q P : Type*} [Group Q]
    [Group P] [Finite Q] [Finite P] (hQ : IsPGroup p Q) (hexp : ∀ x : Q, x ^ p = 1)
    (hrank : CFSG.pRank p Q ≤ 2) (f : Q →* P) (hf : Function.Surjective f) :
    CFSG.pRank p P ≤ 2 := by
  have hp1 := hp.out.one_lt
  have hQcard : Nat.card Q ≤ p ^ 3 :=
    (CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hQ hexp
      (by rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hrank)).1
  have hPQ : Nat.card P ≤ Nat.card Q := Nat.card_le_card_of_surjective f hf
  apply CFSG.LieType.SteinbergBR.pRank_le_of_card_le hp1
  intro E hE
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup p ↥E).exists_card_eq
  have hEP : Nat.card E ≤ Nat.card P := Subgroup.card_le_card_group E
  rw [hn] at hlt hEP
  have h1 : 2 < n := (Nat.pow_lt_pow_iff_right hp1).1 hlt
  have h2 : n ≤ 3 := (Nat.pow_le_pow_iff_right hp1).1 (hEP.trans (hPQ.trans hQcard))
  obtain rfl : n = 3 := by omega
  have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by omega)
  let e := (MulEquiv.ofBijective f hbij).symm
  have h3 : 3 ≤ CFSG.pRank p Q :=
    CFSG.LieType.SteinbergBR.le_pRank_of_card hp1 (E.map e.toMonoidHom)
      (CFSG.IsElementaryAbelian.map e.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective e.injective, hn])
  omega

@[expose] def NormalSourceWholeActionOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ R : Subgroup G, (R : Set G) = nqOriginalCentralizer T L →
    ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
    ∀ Y : Subgroup G, Y ≤ H → (Y.subgroupOf H).Normal → ¬ Y ≤ M →
      ⁅nqOriginalK T L, Y⁆ ≤ pCoreOf 2 Y →
    ∀ p : ℕ, p.Prime → p ≠ 2 → Monoid.exponent (Y ⧸ CFSG.pCore 2 Y) = p →
      Subgroup.upperCentralSeries (Y ⧸ CFSG.pCore 2 Y) 2 = ⊤ →
      CFSG.pRank p (Y ⧸ CFSG.pCore 2 Y) ≤ 2 →
      IsElementaryAbelian 2 (nqSourceModule Y R) ∧ nqSourceModule Y R ≤ R ∧
      nqOriginalK T L ≤ normalizer (nqSourceModule Y R : Set G) ∧
      Y ≤ normalizer (nqSourceModule Y R : Set G) ∧
      R ≤ normalizer (nqSourceModule Y R : Set G) ∧
      pCoreOf 2 Y ≤ centralizer (nqSourceModule Y R : Set G) ∧
      ⁅nqOriginalK T L, R⁆ ≤ centralizer (nqSourceModule Y R : Set G) ∧
      (∀ r ∈ R, (∀ y ∈ Y, ⁅r, y⁆ ∈ centralizer (nqSourceModule Y R : Set G)) →
        r ∈ centralizer (nqSourceModule Y R : Set G)) ∧
      (p = 3 → (centralizer (nqSourceModule Y R : Set G)).relIndex Y = 3)

theorem solvableSourceRankBudget_of (hWA : NormalSourceWholeActionOdd) :
    SolvableSourceRankBudget := by
  intro G _ _ T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY hodd j hj hm hJM A hA
  classical
  obtain ⟨p, hp, hp2, hexp, hcl, hrk⟩ := hodd
  obtain ⟨hWel, hWR, hKW, hYW, hRW, hOW, hKRW, hRY, h3⟩ :=
    hWA G T L M h R hR H hH hKTH hHM Y hYH hYn hYM hKY p hp hp2 hexp hcl hrk
  have : Fact p.Prime := ⟨hp⟩
  set W := nqSourceModule Y R with hWdef
  set K := nqOriginalK T L with hKdef
  set A' := A.map R.subtype with hA'def
  have : IsElementaryAbelian 2 ↥W := hWel
  have hA'R : A' ≤ R := Subgroup.map_subtype_le A
  have hA'W : A' ≤ normalizer (W : Set G) := hA'R.trans hRW
  obtain ⟨hAel, -⟩ := (CFSG.mem_higherElemThompsonFamily_iff j A).mp hA
  have hA'el : IsElementaryAbelian 2 ↥A' := CFSG.IsElementaryAbelian.map R.subtype
  have : Finite (Additive ↥W) := inferInstanceAs (Finite ↥W)
  have : Finite (Module.End (ZMod 2) (Additive ↥W)) :=
    Finite.of_injective (fun f : Additive ↥W →ₗ[ZMod 2] Additive ↥W =>
      (f : Additive ↥W → Additive ↥W)) DFunLike.coe_injective
  have : Finite (Module.End (ZMod 2) (Additive ↥W))ˣ :=
    Finite.of_injective (fun u : (Module.End (ZMod 2) (Additive ↥W))ˣ =>
      (u : Module.End (ZMod 2) (Additive ↥W))) Units.val_injective
  have hRT : R ≤ T := fun r hr => by
    rw [← SetLike.mem_coe, hR] at hr
    exact hr.1
  have hRH : R ≤ H := hRT.trans (le_sup_right.trans hKTH)
  have hYconj : ∀ g ∈ H, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy =>
    Subgroup.mem_subgroupOf.mp
      (hYn.conj_mem ⟨y, hYH hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨g, hg⟩)
  have hKperf : Group.IsPerfect ↥K :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect _
  have hX : ⁅conjImage W hKW, conjImage W hKW⁆ = conjImage W hKW :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ((conjGL W).comp (Subgroup.inclusion hKW)))
  have hXP := conjImage_comm W hKW hYW fun k hk y hy =>
    hOW (hKY (Subgroup.commutator_mem_commutator hk hy))
  have hXA := conjImage_comm W hKW hA'W fun k hk a ha =>
    hKRW (Subgroup.commutator_mem_commutator hk (hA'R ha))
  have hAP : conjImage W hA'W ≤
      normalizer (conjImage W hYW : Set (Module.End (ZMod 2) (Additive ↥W))ˣ) := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    have haH : a ∈ H := hRH (hA'R ha)
    exact conjGL_mem_normalizer W hYW (a := ⟨a, hA'W ha⟩) (fun y hy => hYconj a haH y hy)
      (fun y hy => by simpa using hYconj a⁻¹ (H.inv_mem haH) y hy)
  have hYexp : ∀ y ∈ Y, y ^ p ∈ pCoreOf 2 Y := by
    intro y hy
    have h1 : (QuotientGroup.mk (⟨y, hy⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) ^ p = 1 := by
      rw [← hexp]
      exact Monoid.pow_exponent_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  have hPexp : ∀ g ∈ conjImage W hYW, g ^ p = 1 := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [← map_pow, MonoidHom.comp_apply]
    exact (conjGL_eq_one_iff W _).mpr (hOW (hYexp y hy))
  have hPp : IsPGroup p ↥(conjImage W hYW) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one]; exact hPexp g g.2)⟩
  have hPrank : CFSG.pRank p ↥(conjImage W hYW) ≤ 2 := by
    have hker : CFSG.pCore 2 ↥Y ≤
        ((conjGL W).comp (Subgroup.inclusion hYW)).rangeRestrict.ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (conjGL_eq_one_iff W _).mpr (hOW ⟨y, hy, rfl⟩)
    have hQ : IsPGroup p (↥Y ⧸ CFSG.pCore 2 ↥Y) := fun x =>
      ⟨1, by rw [pow_one, ← hexp]; exact Monoid.pow_exponent_eq_one x⟩
    exact pRank_le_two_of_surjective hQ
      (fun x => by rw [← hexp]; exact Monoid.pow_exponent_eq_one x) hrk
      (QuotientGroup.lift _ _ hker)
      (QuotientGroup.lift_surjective_of_surjective _ _ (MonoidHom.rangeRestrict_surjective _)
        hker)
  have hA2 : ∀ g ∈ conjImage W hA'W, g ^ 2 = 1 := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩
    rw [← map_pow, MonoidHom.comp_apply]
    apply (conjGL_eq_one_iff W _).mpr
    change a ^ 2 ∈ centralizer (W : Set G)
    rw [CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A') a ha]
    exact Subgroup.one_mem _
  have hAc := conjImage_comm W hA'W hA'W fun a ha b hb => by
    have hab : a * b = b * a := congrArg Subtype.val (hA'el.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hab]
    exact Subgroup.one_mem _
  have hfaith : ∀ g ∈ conjImage W hA'W, (∀ y ∈ conjImage W hYW, g * y = y * g) → g = 1 := by
    rintro _ ⟨⟨a, ha⟩, rfl⟩ hcomm
    rw [MonoidHom.comp_apply]
    apply (conjGL_eq_one_iff W _).mpr
    apply hRY a (hA'R ha)
    intro y hy
    exact (conjGL_mul_comm_iff W ⟨a, hA'W ha⟩ ⟨y, hYW hy⟩).mp
      (hcomm _ (conjGL_mem_conjImage W hYW hy))
  have h3' : p = 3 → IsCyclic ↥(conjImage W hYW) ∧ Nat.card ↥(conjImage W hYW) = 3 := by
    intro hp3
    have hc : Nat.card ↥(conjImage W hYW) = 3 := by
      rw [card_conjImage]
      exact h3 hp3
    exact ⟨isCyclic_of_prime_card hc, hc⟩
  set W' : Subgroup ↥R := W.subgroupOf R with hW'def
  have : W'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr hRW
  have : IsElementaryAbelian 2 ↥W' := CFSG.IsElementaryAbelian.subgroupOf hWR
  obtain ⟨d, e, hd, he, hde, -, -⟩ :=
    Quasithin.SteinbergBK.near_maximal_elementary_whole_module_rank_inequality W' hA
  have hcW' : centralizer (W' : Set ↥R) = (centralizer (W : Set G)).subgroupOf R := by
    ext r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h w hw
      exact congrArg Subtype.val (h ⟨w, hWR hw⟩ (Subgroup.mem_subgroupOf.mpr hw))
    · intro h w hw
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hw)))
  have hcA : centralizer (A : Set ↥R) = (centralizer (A' : Set G)).subgroupOf R := by
    ext r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · rintro h _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val (h a ha)
    · intro h a ha
      exact Subtype.ext (h a ⟨a, ha, rfl⟩)
  have hAA' : A'.subgroupOf R = A := by
    ext a
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨b, hb, hba⟩
      rwa [show a = b from Subtype.ext hba.symm]
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hcardA : Nat.card ↥(conjImage W hA'W) = 2 ^ e := by
    rw [card_conjImage, ← he, Subgroup.inf_relIndex_left, hcW', ← hAA',
      Subgroup.relIndex_subgroupOf hA'R]
  have hrelW : (centralizer (A' : Set G)).relIndex W = 2 ^ d := by
    rw [← hd, Subgroup.inf_relIndex_left, hcA, hW'def, Subgroup.relIndex_subgroupOf hWR]
  have hcD : Nat.card ↥W = 2 ^ finrank (ZMod 2) (Additive ↥W) :=
    (FiniteField.pow_finrank_eq_natCard 2 (Additive ↥W)).symm
  have hcF : Nat.card ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hA'W)) =
      2 ^ finrank (ZMod 2) ↥(CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hA'W)) :=
    (FiniteField.pow_finrank_eq_natCard 2 _).symm
  have h1 := Subgroup.relIndex_mul_card (H := centralizer (A' : Set G)) (K := W)
  rw [hrelW, inf_comm, ← card_fixedSub_conjImage W hA'W, hcF, hcD, ← pow_add] at h1
  have h2 := Nat.pow_right_injective le_rfl h1
  have hFD := Submodule.finrank_le (CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hA'W))
  have hcodim : 2 ^ (finrank (ZMod 2) (Additive ↥W) -
      finrank (ZMod 2) (CFSG.LocalAnalysis.CommutingFactor.fixedSub (conjImage W hA'W))) ≤
      2 ^ j * Nat.card ↥(conjImage W hA'W) := by
    rw [hcardA, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  by_contra hzv
  obtain ⟨hvW, hvX⟩ := commutator_mem_commSpace W hKW hv
  obtain ⟨hzN, hzPA⟩ := conjGL_mem_commutator W hYW hA'W hz
  exact solvable_source_linear_core hX hXP hXA hAP hp hp2 hPp hPexp hPrank hA2 hAc hfaith h3' hj
    hcodim ⟨conjGL W ⟨z, hzN⟩, hzPA, Additive.ofMul ⟨v, hvW⟩, hvX,
      conjGL_apply_ne W hvW hzv⟩

end CFSG.Quasithin.H13.NQBlock
