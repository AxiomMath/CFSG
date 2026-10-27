module

public import CFSG.Quasithin.Background.RonanF615
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.RankThree.PartTwo.Sec4.Item413Eigen

public section

namespace CFSG.Quasithin.RonanF615

open CFSG.Open

theorem exists_isSection_mulEquiv {X D : Type*} [Group X] [Group D] (φ : X →* D)
    (hφ : Function.Surjective φ) (K : Subgroup D) :
    ∃ (H N : Subgroup X) (_ : (N.subgroupOf H).Normal),
      Nonempty (↥K ⧸ Subgroup.center ↥K ≃* ↥H ⧸ N.subgroupOf H) := by
  obtain ⟨H, N, hN, ⟨e⟩⟩ := exists_section_mulEquiv φ hφ K
  have h : (N.map H.subtype).subgroupOf H = N :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  haveI : ((N.map H.subtype).subgroupOf H).Normal := by rw [h]; exact hN
  exact ⟨H, N.map H.subtype, inferInstance, ⟨e.trans (QuotientGroup.quotientMulEquivOfEq h.symm)⟩⟩

theorem isQuasisimple_of_isSimpleGroup {R : Type*} [Group R] [IsSimpleGroup R]
    (hnab : ∃ a b : R, a * b ≠ b * a) : CFSG.Open.IsQuasisimple R := by
  obtain ⟨a, b, hab⟩ := hnab
  have hcomm : commutator R = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R) with h | h
    · exfalso
      apply hab
      have hc : (⊤ : Subgroup R) ≤ Subgroup.centralizer ((⊤ : Subgroup R) : Set R) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [← commutator_def]; exact h)
      exact (Subgroup.mem_centralizer_iff.mp (hc (Subgroup.mem_top b)) a
        (Subgroup.mem_top a))
    · exact h
  have hcenter : Subgroup.center R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exfalso
      apply hab
      have hb : b ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top b
      exact (Subgroup.mem_center_iff.mp hb a)
  refine ⟨hcomm, ?_⟩
  have e : R ⧸ Subgroup.center R ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact e.isSimpleGroup

theorem genFittingLayer_eq_top {R : Type*} [Group R] [IsSimpleGroup R]
    (hnab : ∃ a b : R, a * b ≠ b * a) : CFSG.Open.genFittingLayer R = ⊤ := by
  have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup R) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv (isQuasisimple_of_isSimpleGroup hnab)
  have hc : CFSG.Open.IsComponentOf (⊤ : Subgroup R) ⊤ := ⟨le_rfl, .refl ⊤, hq⟩
  rw [eq_top_iff, CFSG.Open.genFittingLayer.eq_sSup]
  exact le_sSup hc

theorem evenRank_le_two_of_forall {R : Type*} [Group R] [Finite R]
    (h : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.twoLocalPrimeRank q R ≤ 2) :
    CFSG.Open.evenRank R ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨q, L, hq, hq2, hL, rfl⟩
  refine le_trans ?_ (h q hq hq2)
  exact le_csSup ⟨Nat.card R, by
    rintro _ ⟨K, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt K⟩ ⟨L, hL, rfl⟩

theorem three_ne_zero_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hcard : Nat.card K = (2 ^ n) ^ 2) : (3 : K) ≠ 0 := by
  intro h
  have : Fintype K := Fintype.ofFinite K
  have h3 : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
  haveI : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr h3
  obtain ⟨m, -, hm⟩ := FiniteField.card K 3
  rw [← Nat.card_eq_fintype_card, hcard] at hm
  have h3d : 3 ∣ (2 ^ n) ^ 2 := by
    rw [hm]
    exact dvd_pow_self 3 m.pos.ne'
  have := Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h3d)
  omega

theorem pRank_three_le_two_of_statedSU {n : ℕ} {X : Type} [Group X] [Finite X]
    (h : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n) ^ 2 ∧
      Nonempty (X ≃* ↥(CFSG.Open.StatedSU 3 (2 ^ n) K))) : CFSG.pRank 3 X ≤ 2 := by
  obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := h
  have h3K : (3 : K) ≠ 0 := three_ne_zero_of_card hcard
  rw [CFSG.pRank_congr_of_mulEquiv e 3]
  refine csSup_le' ?_
  rintro r ⟨B, hB, hr⟩
  obtain ⟨hBc, hBe⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 B).mp hB
  set E : Subgroup (GL (Fin 3) K) := B.map (CFSG.Open.StatedSU 3 (2 ^ n) K).subtype with hEdef
  have hfin : Finite E := inferInstance
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩))
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hBe x hx, map_one]
  have hdet : ∀ x ∈ E, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.Open.StatedAPI.det_of_mem_statedSU x.2
  have hbound := CFSG.RankThree.PartTwo.Sec4.card_le_of_det_eq_one h3K (0 : Fin 3) E hcomm hexp
    hdet
  rw [Fintype.card_fin, hEdef,
    Subgroup.card_map_of_injective (CFSG.Open.StatedSU 3 (2 ^ n) K).subtype_injective, hr] at hbound
  have h32 : 3 ^ r ≤ 3 ^ 2 := by simpa using hbound
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h32

theorem not_commutative_of_isQuasisimple {L : Type*} [Group L]
    (h : CFSG.Open.IsQuasisimple L) : ¬ ∀ a b : L, a * b = b * a := by
  intro hc
  have hz : Subgroup.center L = ⊤ :=
    (Subgroup.eq_top_iff' _).mpr fun a => Subgroup.mem_center_iff.mpr fun b => hc b a
  obtain ⟨-, hs⟩ := h
  haveI : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [hz]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_subsingleton (L ⧸ Subgroup.center L)) inferInstance

theorem isComponentOf_subgroupOf {X : Type*} [Group X] {H L : Subgroup X}
    (h : CFSG.Open.IsComponentOf L H) : CFSG.Open.IsComponentOf (L.subgroupOf H) ⊤ :=
  ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib h.2.1.subgroupOf,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩

theorem false_of_clauseB_simple {X : Type} [Group X] [Finite X] {R : Type} [Group R]
    [IsSimpleGroup R] (hnab : ∃ a b : R, a * b ≠ b * a) {H H₁ H₂ : Subgroup X} {n₁ : ℕ}
    (e : R ≃* ↥H ⧸ Subgroup.center ↥H) (hr : CFSG.pRank 3 ↥H = 3) (hsup : H = H₁ ⊔ H₂)
    (hc₁ : CFSG.Open.IsComponentOf H₁ H) (hc₂ : CFSG.Open.IsComponentOf H₂ H)
    (hs₁ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ n₁) ^ 2 ∧
      Nonempty (↥H₁ ≃* ↥(CFSG.Open.StatedSU 3 (2 ^ n₁) K))) :
    False := by
  by_cases hne : H₁ = H₂
  · subst hne
    rw [sup_idem] at hsup
    subst hsup
    have := pRank_three_le_two_of_statedSU hs₁
    omega
  · have hle₁ : H₁ ≤ H := hc₁.1
    have hle₂ : H₂ ≤ H := hc₂.1
    have hA₁ := isComponentOf_subgroupOf hc₁
    have hA₂ := isComponentOf_subgroupOf hc₂
    have hne' : H₁.subgroupOf H ≠ H₂.subgroupOf H := by
      intro h
      apply hne
      have := Subgroup.subgroupOf_inj.mp h
      rwa [inf_of_le_left hle₁, inf_of_le_left hle₂] at this
    have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA₁ hA₂ hne'
    have hsupA : H₁.subgroupOf H ⊔ H₂.subgroupOf H = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hle₁, inf_of_le_left hle₂, ← hsup, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    set π := QuotientGroup.mk' (Subgroup.center ↥H) with hπ
    set B₁ : Subgroup (↥H ⧸ Subgroup.center ↥H) := (H₁.subgroupOf H).map π with hB₁
    set B₂ : Subgroup (↥H ⧸ Subgroup.center ↥H) := (H₂.subgroupOf H).map π with hB₂
    have hBsup : B₁ ⊔ B₂ = ⊤ := by
      rw [hB₁, hB₂, ← Subgroup.map_sup, hsupA,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hle : H₁.subgroupOf H ≤ Subgroup.centralizer ((H₂.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hBc : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hba : b * a = a * b := Subgroup.mem_centralizer_iff.mp (hle ha) b hb
      rw [← map_mul, ← map_mul, hba]
    haveI hQs : IsSimpleGroup (↥H ⧸ Subgroup.center ↥H) := e.symm.isSimpleGroup
    have hnormB : ∀ (B C : Subgroup (↥H ⧸ Subgroup.center ↥H)), B ⊔ C = ⊤ →
        (∀ x ∈ B, ∀ y ∈ C, x * y = y * x) → B.Normal := by
      intro B C hBC hc
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hBC]
      refine sup_le Subgroup.le_normalizer fun y hy => Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hc h hh y hy
    haveI hB₁n : B₁.Normal := hnormB B₁ B₂ hBsup hBc
    haveI hB₂n : B₂.Normal :=
      hnormB B₂ B₁ (by rw [sup_comm]; exact hBsup) (fun x hx y hy => (hBc y hy x hx).symm)
    have hnotbot : ∀ {L : Subgroup X}, CFSG.Open.IsComponentOf L H →
        ¬ ((L.subgroupOf H).map π = ⊥) := by
      intro L hL hbot
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
      refine not_commutative_of_isQuasisimple hL.2.2 fun a b => ?_
      have ha : (⟨(a : X), hL.1 a.2⟩ : ↥H) ∈ Subgroup.center ↥H := hbot a.2
      have h1 := Subgroup.mem_center_iff.mp ha ⟨(b : X), hL.1 b.2⟩
      exact Subtype.ext (congrArg (fun z : ↥H => (z : X)) h1.symm)
    have hB₁top : B₁ = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal B₁).resolve_left (hnotbot hc₁)
    have hB₂top : B₂ = ⊤ :=
      (IsSimpleGroup.eq_bot_or_eq_top_of_normal B₂).resolve_left (hnotbot hc₂)
    have hQc : ∀ a b : ↥H ⧸ Subgroup.center ↥H, a * b = b * a := fun a b =>
      hBc a (by rw [hB₁top]; exact Subgroup.mem_top a) b (by rw [hB₂top]; exact Subgroup.mem_top b)
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact hQc _ _

end CFSG.Quasithin.RonanF615
