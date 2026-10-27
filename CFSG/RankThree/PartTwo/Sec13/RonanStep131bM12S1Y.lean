module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
public import CFSG.RankThree.PartTwo.KFacts.KS18M12
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvA
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
public import CFSG.RankThree.PartTwo.Sec13.Item131a

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace M12Inv

variable {G : Type} [Group G] [Finite G]

theorem inf_thetaQuotCentralizer_le' {K : Subgroup G}
    (hZ : Subgroup.center (↥K ⧸ aschbacherSolvableCore 3 ↥K) = ⊥) :
    K ⊓ Sec4.thetaQuotCentralizer K ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  rintro g ⟨hgK, hg⟩
  obtain ⟨-, hgl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hg
  have hc : ((⟨g, hgK⟩ : K) : ↥K ⧸ aschbacherSolvableCore 3 ↥K) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    obtain ⟨t, ht, hte⟩ := hgl l l.2
    have hte' : (t : G) = (l : G)⁻¹ * (g * l * g⁻¹) := hte
    have hmem := (aschbacherSolvableCore_normal 3 K).conj_mem t ht (⟨g, hgK⟩⁻¹)
    convert hmem using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hte', inv_inv]
    group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact ⟨⟨g, hgK⟩, hc, rfl⟩

theorem exists_inv_mul_mem_thetaQuotCentralizer_m12 (hK18 : KFacts.KS18M12) {K : Subgroup G}
    (hM : Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.M12))
    {q : G} (hq : q ∈ Subgroup.normalizer (K : Set G)) {n : ℕ} (hq3 : q ^ 3 ^ n = 1) :
    ∃ y ∈ K, y⁻¹ * q ∈ Sec4.thetaQuotCentralizer K := by
  have h3 : ((Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom) ⟨q, hq⟩ ^ 3 ^ n = 1 := by
    rw [← map_pow]
    have : (⟨q, hq⟩ : Subgroup.normalizer (K : Set G)) ^ 3 ^ n = 1 := Subtype.ext hq3
    rw [this, map_one]
  obtain ⟨-, -, hinn, -⟩ := hK18 _ hM
  obtain ⟨x, hx⟩ := hinn _ ⟨n, h3⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
  have hdN : (k : G)⁻¹ * q ∈ Subgroup.normalizer (K : Set G) := mul_mem (inv_mem hkN) hq
  refine ⟨k, k.2, Subgroup.mem_map.mpr ⟨⟨_, hdN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩⟩
  have he : (⟨(k : G)⁻¹ * q, hdN⟩ : Subgroup.normalizer (K : Set G)) =
      (⟨k, hkN⟩ : Subgroup.normalizer (K : Set G))⁻¹ * ⟨q, hq⟩ := rfl
  have hconj : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨k, hkN⟩) =
      MulAut.conj (k : ↥K ⧸ aschbacherSolvableCore 3 ↥K) := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [Sec4.thetaQuotMulAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
  rw [he, map_mul, map_inv]
  change (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨k, hkN⟩))⁻¹ *
    ((Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom) ⟨q, hq⟩ = 1
  rw [hconj, ← hx, inv_mul_cancel]

end M12Inv

open M12Inv in
theorem s1y_of (hA : InvPartA) (hK18 : KFacts.KS18M12) (h414 : Sec4.Item4_14_local) : S1Y := by
  intro G _ _ A c L E F a b R Y hY hM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hMθ, -, -⟩ := hA G F b Y hY.hD hM
  obtain ⟨-, hZ, -, -⟩ := hK18 (Y ⧸ aschbacherSolvableCore 3 Y) hMθ
  have hSyl : ∀ Qb : Sylow 3 (Y ⧸ aschbacherSolvableCore 3 Y),
      Nat.card (Qb : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) = 27 ∧
        ∀ x ∈ (Qb : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)), x ^ 3 = 1 := by
    intro Qb
    obtain ⟨hHeis, -⟩ := h414 _ hMθ Qb
    refine ⟨hHeis.2.1, fun x hx => ?_⟩
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : (Qb : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)))
    rw [hHeis.2.2] at this
    simpa using congrArg Subtype.val this
  refine ⟨inf_thetaQuotCentralizer_le' hZ, ?_, ?_, ?_⟩
  ·
    intro P hPY hP3
    have hP'3 : IsPGroup 3 (P.subgroupOf Y) :=
      hP3.of_equiv (Subgroup.subgroupOfEquivOfLe hPY).symm
    have hcardP' : Nat.card (P.subgroupOf Y) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv
    have hB3 : IsPGroup 3 ((P.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) :=
      hP'3.map _
    obtain ⟨Qb, hBQ⟩ := hB3.exists_le_sylow
    obtain ⟨h27, hex⟩ := hSyl Qb
    have hinj := injOn_mk_of_isPGroup Nat.prime_three hP'3
    have hcardB : Nat.card ((P.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) =
        Nat.card (P.subgroupOf Y) := card_map_eq_of_injOn _ hinj
    refine ⟨?_, fun x hx => ?_⟩
    · calc Nat.card P = Nat.card (P.subgroupOf Y) := hcardP'.symm
        _ = Nat.card ((P.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) :=
          hcardB.symm
        _ ≤ Nat.card (Qb : Subgroup (Y ⧸ aschbacherSolvableCore 3 Y)) :=
          Subgroup.card_le_of_le hBQ
        _ = 27 := h27
    · have hxP' : (⟨x, hPY hx⟩ : Y) ∈ P.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hx
      have h1 : (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x, hPY hx⟩) ^ 3 = 1 :=
        hex _ (hBQ (Subgroup.mem_map_of_mem _ hxP'))
      have h2 : (⟨x, hPY hx⟩ : Y) ^ 3 = 1 :=
        hinj ((P.subgroupOf Y).pow_mem hxP' 3) (P.subgroupOf Y).one_mem
          (by rw [map_pow, h1, map_one])
      simpa using congrArg Subtype.val h2
  ·
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 Y))
    set Qb : Sylow 3 (Y ⧸ aschbacherSolvableCore 3 Y) :=
      S.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 Y)) with hQbdef
    have hQb : (Qb : Subgroup _) =
        (S : Subgroup Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) :=
      Sylow.coe_mapSurjective _ _
    have hS27 : Nat.card (S : Subgroup Y) = 27 := by
      have := (hSyl Qb).1
      rw [hQb, card_map_eq_of_injOn _ (injOn_mk_of_isPGroup Nat.prime_three S.isPGroup')] at this
      exact this
    refine ⟨(S : Subgroup Y).map Y.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_⟩
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hS27]
  ·
    intro Q hQN hQ3 q hq
    obtain ⟨k, hk⟩ := hQ3 ⟨q, hq⟩
    have hq3 : q ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨y, hy, hyq⟩ := exists_inv_mul_mem_thetaQuotCentralizer_m12 hK18 hMθ (hQN hq) hq3
    have : q = y * (y⁻¹ * q) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hy hyq

theorem s1y_holds
    (h131a : Item131a) : S1Y :=
  s1y_of (invPartA_of h131a sporadicModels131) KFacts.ks18M12
    Sec4.Sporadic.rank3II_4_14_local

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
