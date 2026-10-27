module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingBase
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientKernelCore
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBridge
public import CFSG.RankThree.GroupTheory.SteinbergBMMinimalExtraspecialModule
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne.Lifting36

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Quotient36 CFSG.Assembly
  CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G]

theorem mem_sup_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (h | h)
    · exact ⟨y, h, 1, K.one_mem, by simp⟩
    · exact ⟨1, H.one_mem, y, h, by simp⟩
  · exact ⟨1, H.one_mem, 1, K.one_mem, mul_one 1⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, mul_mem hy₁ hy₂, z₁ * z₂, mul_mem hz₁ hz₂, ?_⟩
    have h1 : z₁ * y₂ = y₂ * z₁ := (hc y₂ hy₂ z₁ hz₁).symm
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [h1]
      _ = y₁ * z₁ * (y₂ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, inv_mem hy, z⁻¹, inv_mem hz, ?_⟩
    have h1 : y * z = z * y := hc y hy z hz
    calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by group
      _ = (y * z)⁻¹ := by rw [h1]

theorem isElementaryAbelian_of_le {p : ℕ} {E F : Subgroup G} (hF : IsElementaryAbelian p F)
    (hEF : E ≤ F) : IsElementaryAbelian p E := CFSG.IsElementaryAbelian.of_le hF hEF

section Commutator

variable {A₀ A R U B : Subgroup G}

theorem commutator_eq_of_le_sup (hA : A ≤ A₀ ⊔ B) (hA₀ : A₀ ≤ A)
    (hBR : B ≤ Subgroup.centralizer (R : Set G)) (hcomm : ∀ x ∈ A₀, ∀ y ∈ B, x * y = y * x)
    (hUR : U ≤ R) (hUA₀ : A₀ ≤ Subgroup.normalizer (U : Set G)) :
    ⁅U, A⁆ = ⁅U, A₀⁆ ∧ A ≤ Subgroup.normalizer (U : Set G) := by
  have hBU : ∀ c ∈ B, ∀ u ∈ U, c * u = u * c := fun c hc u hu =>
    (Subgroup.mem_centralizer_iff.mp (hBR hc) u (hUR hu)).symm
  refine ⟨le_antisymm ?_ (Subgroup.commutator_mono le_rfl hA₀), ?_⟩
  · rw [Subgroup.commutator_le]
    intro u hu x hx
    obtain ⟨a₀, ha₀, c, hc, rfl⟩ := mem_sup_of_commute hcomm (hA hx)
    have h3 : c * u⁻¹ = u⁻¹ * c := ((show Commute c u from hBU c hc u hu).inv_right).eq
    have e : ⁅u, a₀ * c⁆ = ⁅u, a₀⁆ := by
      simp only [commutatorElement_def]
      calc u * (a₀ * c) * u⁻¹ * (a₀ * c)⁻¹ = u * a₀ * (c * u⁻¹) * c⁻¹ * a₀⁻¹ := by group
        _ = u * a₀ * (u⁻¹ * c) * c⁻¹ * a₀⁻¹ := by rw [h3]
        _ = u * a₀ * u⁻¹ * a₀⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator hu ha₀
  · refine hA.trans (sup_le hUA₀ ?_)
    refine le_normalizer_of_conj_mem fun c hc u hu => ?_
    have : c * u * c⁻¹ = u := by rw [hBU c hc u hu]; group
    rw [this]; exact hu

end Commutator

section ChooseA0

variable [Finite G]

theorem exists_A0 {p q : ℕ} {A D R : Subgroup G} (hp : p.Prime) (hp3 : 3 < p) (hq : q.Prime)
    (hq2 : q ≠ 2) (hqp : q ≠ p) (hAel : IsElementaryAbelian p A)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R) (hRA : ⁅R, A⁆ = R)
    (hRne : R ≠ ⊥) (hLD : R ⊔ A ≤ Subgroup.normalizer (D : Set G)) (hDq : IsPGroup q D)
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥) (hRD : ⁅R, D⁆ ≠ ⊥)
    (hidx : (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A = p)
    (hBcard : p ≤ Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G))
    (hmin : ∀ U : Subgroup G, U < R → A ≤ Subgroup.normalizer (U : Set G) → ⁅U, A⁆ = U →
      U ≤ Subgroup.centralizer (D : Set G)) :
    ∃ a b : G, a ∈ A ∧ a ∉ A ⊓ Subgroup.centralizer (R : Set G) ∧
      b ∈ A ⊓ Subgroup.centralizer (R : Set G) ∧ b ≠ 1 ∧
      (⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ ≠ ⊥ → ∃ d ∈ D, ⁅b, d⁆ ≠ 1) ∧
      MinTwoActionSetting p q (Subgroup.zpowers b ⊔ Subgroup.zpowers a) D R := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsElementaryAbelian p A := hAel
  set B : Subgroup G := A ⊓ Subgroup.centralizer (R : Set G) with hB
  have hBA : B ≤ A := inf_le_left
  have hBR : B ≤ Subgroup.centralizer (R : Set G) := inf_le_right
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ B := by
    by_contra h
    push Not at h
    have h1 : B.relIndex A = 1 := Subgroup.relIndex_eq_one.mpr fun x hx => h x hx
    rw [h1] at hidx
    exact hp.one_lt.ne hidx
  obtain ⟨b₁, hb₁B, hb₁1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra h
    push Not at h
    have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 h
    rw [this, Subgroup.card_bot] at hBcard
    have := hp.one_lt
    omega
  obtain ⟨b, hbB, hb1, hbD⟩ : ∃ b ∈ B, b ≠ 1 ∧ (⁅B, D⁆ ≠ ⊥ → ∃ d ∈ D, ⁅b, d⁆ ≠ 1) := by
    by_cases hBD : ⁅B, D⁆ = ⊥
    · exact ⟨b₁, hb₁B, hb₁1, fun h => absurd hBD h⟩
    · obtain ⟨b, hbB, d, hdD, hne⟩ : ∃ b ∈ B, ∃ d ∈ D, ⁅b, d⁆ ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hBD (eq_bot_iff.2 (Subgroup.commutator_le.2 fun b hb d hd => by
          simpa using hcon b hb d hd))
      refine ⟨b, hbB, ?_, fun _ => ⟨d, hdD, hne⟩⟩
      rintro rfl
      exact hne (commutatorElement_one_left d)
  have hzb : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hbB
  have hza : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  have hA₀A : Subgroup.zpowers b ⊔ Subgroup.zpowers a ≤ A := sup_le (hzb.trans hBA) hza
  have hbp : b ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hbB)
  have hap : a ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) a haA
  have hcardb : Nat.card (Subgroup.zpowers b) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hbp hb1]
  obtain ⟨-, hcardA₀⟩ := CFSG.RankThree.PartTwo.sup_zpowers_card (p := p)
    (A := Subgroup.zpowers b) inferInstance (x := a) (fun h => haB (hzb h)) hap
    (fun y hy => hcommA y (hBA (hzb hy)) a haA)
  have hAle : A ≤ Subgroup.zpowers a ⊔ B := by
    set C := Subgroup.zpowers a ⊔ B with hC
    have hCA : C ≤ A := sup_le hza hBA
    have hBC : B ≤ C := le_sup_right
    have hmul : B.relIndex C * C.relIndex A = B.relIndex A :=
      Subgroup.relIndex_mul_relIndex B C A hBC hCA
    rw [hidx] at hmul
    have hdvd : B.relIndex C ∣ p := Dvd.intro _ hmul
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      have : C ≤ B := Subgroup.relIndex_eq_one.mp h1
      exact haB (this (le_sup_left (a := Subgroup.zpowers a) (b := B) (Subgroup.mem_zpowers a)))
    · rw [h1] at hmul
      have : C.relIndex A = 1 := by
        have hp0 : 0 < p := hp.pos
        exact Nat.eq_of_mul_eq_mul_left hp0 (by rw [hmul, mul_one])
      exact Subgroup.relIndex_eq_one.mp this
  have hAle' : A ≤ (Subgroup.zpowers b ⊔ Subgroup.zpowers a) ⊔ B :=
    hAle.trans (sup_le_sup_right (le_sup_right) B)
  have hcommAB : ∀ x ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers a, ∀ y ∈ B, x * y = y * x :=
    fun x hx y hy => hcommA x (hA₀A hx) y (hBA hy)
  refine ⟨a, b, haA, haB, hbB, hb1, hbD, ?_⟩
  refine
    { prime_p := hp
      prime_q := hq
      three_lt_p := hp3
      q_ne_two := hq2
      p_ne_q := fun h => hqp h.symm
      A_elem := isElementaryAbelian_of_le hAel hA₀A
      A_card := by rw [hcardA₀, hcardb]; ring
      D_inv := sup_le (le_sup_left.trans hLD) (hA₀A.trans (le_sup_right.trans hLD))
      D_pgroup := hDq
      D_exp := hDexp
      D_class := hDcl
      R_two := hR2
      R_inv := hA₀A.trans hAR
      R_comm := ?_
      R_ne := hRne
      R_act := hRD
      R_min := ?_ }
  · exact ((commutator_eq_of_le_sup hAle' hA₀A hBR hcommAB le_rfl (hA₀A.trans hAR)).1.symm.trans
      hRA)
  · intro U hU hUA₀ hUc
    obtain ⟨hUeq, hAU⟩ := commutator_eq_of_le_sup hAle' hA₀A hBR hcommAB hU.le hUA₀
    exact hmin U hU hAU (hUeq.trans hUc)

end ChooseA0

section Ranks

theorem isTwoLocal_normalizer_zpowers {R : Subgroup G} (hR : IsPGroup 2 R) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) :
    IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G)) :=
  ⟨Subgroup.zpowers r, by rwa [ne_eq, Subgroup.zpowers_eq_bot],
    hR.to_le (Subgroup.zpowers_le.mpr hr), rfl⟩

theorem centralizer_le_normalizer_zpowers (r : G) :
    Subgroup.centralizer ({r} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers r : Subgroup G) : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer ((Subgroup.zpowers r : Subgroup G) : Set G)

variable [Finite G]

theorem pRank_centralizer_le_localRank {q : ℕ} (hq : q.Prime) (D : Subgroup G) {R : Subgroup G}
    (hR : IsPGroup 2 R) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ localRank q G := by
  rw [← assembly_pRank_eq hq]
  exact (CFSG.SectionRank.pRank_mono hq.one_lt
    (inf_le_right.trans (centralizer_le_normalizer_zpowers r))).trans
    (CFSG.RankThree.Classical.pRank_le_localRank hq.one_lt
      (isTwoLocal_normalizer_zpowers hR hr hr1))

theorem pRank_centralizer_le_three (hrank : evenRank G = 3) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (D : Subgroup G) {R : Subgroup G} (hR : IsPGroup 2 R) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3 :=
  (pRank_centralizer_le_localRank hq D hR hr hr1).trans
    (localRank_le_three_of_evenRank_eq_three hrank hq hq2)

theorem three_le_localRank_of_pRank_eq_three {q : ℕ} (hq : q.Prime) (D : Subgroup G)
    {R : Subgroup G} (hR : IsPGroup 2 R) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1)
    (h3 : CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) : 3 ≤ localRank q G :=
  h3 ▸ pRank_centralizer_le_localRank hq D hR hr hr1

end Ranks

section FrattiniQuotients

theorem relIndex_frattini_eq_card_quotient (D : Subgroup G) :
    (inSubgroup frattini D).relIndex D = Nat.card (↥D ⧸ frattini ↥D) := by
  rw [Subgroup.relIndex]
  have : (inSubgroup frattini D).subgroupOf D = frattini ↥D :=
    Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
  rw [this]
  rfl

theorem commutator_le_center_of_commutator_eq_bot (D : Subgroup G) (h : ⁅⁅D, D⁆, D⁆ = ⊥) :
    commutator ↥D ≤ Subgroup.center ↥D := by
  intro x hx
  have hx' : (x : G) ∈ ⁅D, D⁆ := by
    have : D.subtype x ∈ (commutator ↥D).map D.subtype := Subgroup.mem_map_of_mem _ hx
    rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at this
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  have hc := h hx'
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc g g.2)

variable [Finite G]

theorem three_lt_pRank_of_relIndex {q : ℕ} (hq : q.Prime) {D : Subgroup G} (hDq : IsPGroup q D)
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥) {k : ℕ}
    (hk : (inSubgroup frattini D).relIndex D = q ^ k) (hk4 : 4 < k) : 3 < CFSG.pRank q ↥D := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q ↥D) := ⟨hDq⟩
  by_contra h
  push Not at h
  have hexp : ∀ x : ↥D, x ^ q = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hDexp x x.2)
  have hcl := commutator_le_center_of_commutator_eq_bot D hDcl
  have h34 := (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDq hexp hcl).2.2 h
  have h5 := card_frattini_quotient_le q hexp
  rw [← relIndex_frattini_eq_card_quotient, hk] at h5
  have h6 : q ^ k ≤ q ^ 4 := h5.trans (Nat.pow_le_pow_right hq.pos h34)
  have := (Nat.pow_le_pow_iff_right hq.one_lt).mp h6
  omega

theorem relIndex_frattini_of_isQDShape {q : ℕ} (hq : q.Prime) {D : Subgroup G}
    (hD : IsQDShape q D) : (inSubgroup frattini D).relIndex D = q ^ 4 := by
  rcases hD with ⟨hel, hcard⟩ | ⟨-, hcard, hcomm, -, hfr⟩
  · rw [inSubgroup_frattini_eq_bot hq hel, Subgroup.relIndex_bot_left, hcard]
  · rw [hfr]
    have hle : ⁅D, D⁆ ≤ D := Subgroup.commutator_le_of_le le_rfl le_rfl
    have h := Subgroup.relIndex_mul_card (H := ⁅D, D⁆) (K := D)
    rw [inf_eq_left.mpr hle, hcomm, hcard] at h
    have : (⁅D, D⁆ : Subgroup G).relIndex D * q = q ^ 4 * q := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hq.pos this

end FrattiniQuotients

section Scalar

variable [Finite G]

theorem center_map_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T) :
    (Subgroup.center S).map e.toMonoidHom = Subgroup.center T := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : IsExtraspecialPGroup p S) : IsExtraspecialPGroup p T := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator S).map e.toMonoidHom = commutator T := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hf : (frattini S).map e.toMonoidHom = frattini T :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, center_map_mulEquiv]
  · rw [← hf, hfrat, center_map_mulEquiv]
  · rw [← center_map_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard]


theorem exists_center_eq_zpowers {S : Type*} [Group S] [Finite S] (h : IsExtraspecialPGroup 2 S) :
    ∃ z : S, Subgroup.center S = Subgroup.zpowers z := by
  have hc : Nat.card (Subgroup.center S) = 2 := h.2.2.2
  obtain ⟨z, hzc, hz1⟩ : ∃ z ∈ Subgroup.center S, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subgroup.center S = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hc
    omega
  refine ⟨z, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzc) ?_).symm⟩
  have hdvd : Nat.card (Subgroup.zpowers z) ∣ 2 := hc ▸ Subgroup.card_dvd_of_le
    (Subgroup.zpowers_le.mpr hzc)
  have hne : Nat.card (Subgroup.zpowers z) ≠ 1 := by
    rw [Nat.card_zpowers]
    intro h1
    exact hz1 (orderOf_eq_one_iff.mp h1)
  have : Nat.card (Subgroup.zpowers z) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  omega


theorem scalar_conclusions {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq5 : q ≠ 5)
    {L D R : Subgroup G} (hLD : L ≤ Subgroup.normalizer (D : Set G)) (hDq : IsPGroup q D)
    (hRL : R ≤ L) (hR2 : IsPGroup 2 R) (hRf : R ⊓ Subgroup.centralizer (D : Set G) = ⊥)
    (hRext : IsExtraspecialPGroup 2 ↥R) (hRcard : Nat.card R = 2 ^ (1 + 2 * 2))
    (hDfr : (inSubgroup frattini D).relIndex D = q ^ 4) {b : G} (hbL : b ∈ L)
    (hbR : b ∈ Subgroup.centralizer (R : Set G)) (hb5 : b ^ 5 = 1)
    (hbD : ∃ d ∈ D, ⁅b, d⁆ ≠ 1) :
    q % 5 = 1 ∧ ⁅D, Subgroup.zpowers b⁆ = D := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q ↥D) := ⟨hDq⟩
  have : Subgroup.Normalizes L D := ⟨hLD⟩
  let ρ : Representation (ZMod q) ↥L (Additive (↥D ⧸ frattini ↥D)) :=
    frattiniRep (E := ↥L) (X := ↥D) q
  let ρR : Representation (ZMod q) ↥R (Additive (↥D ⧸ frattini ↥D)) :=
    ρ.comp (Subgroup.inclusion hRL)
  have hsmul : ∀ (g : ↥L) (x : ↥D), ((g • x : ↥D) : G) = (g : G) * (x : G) * (g : G)⁻¹ :=
    fun g x => Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe L D g x
  have hord2 : ∀ r : ↥R, ¬ q ∣ orderOf r := by
    intro r hdvd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR2) r
    have h2 : q ∣ 2 ^ k := hk ▸ hdvd
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
  have hinj : Function.Injective ρR := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hr' : ρ (Subgroup.inclusion hRL r) = 1 := hr
    have htriv : ∀ x : ↥D, ((((Subgroup.inclusion hRL r : ↥L) • x : ↥D)) : ↥D ⧸ frattini ↥D) =
        (x : ↥D ⧸ frattini ↥D) := by
      intro x
      have h1 := frattiniRep_apply_mk (E := ↥L) (X := ↥D) q (Subgroup.inclusion hRL r) x
      have h2 : ρ (Subgroup.inclusion hRL r) (Additive.ofMul (x : ↥D ⧸ frattini ↥D)) =
          Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by rw [hr']; rfl
      exact Additive.ofMul.injective (h1.symm.trans h2)
    have hnot : ¬ q ∣ orderOf (Subgroup.inclusion hRL r) := by
      rw [orderOf_injective (Subgroup.inclusion hRL) (Subgroup.inclusion_injective hRL) r]
      exact hord2 r
    have hfix := smul_eq_of_smul_mk_eq hDq (Subgroup.inclusion hRL r) hnot htriv
    have hmem : (r : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := by
      refine ⟨r.2, ?_⟩
      show (r : G) ∈ Subgroup.centralizer (D : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 := congrArg (fun y : ↥D => (y : G)) (hfix ⟨d, hd⟩)
      simp only [hsmul] at h1
      have h2 : (r : G) * d = d * r := by
        calc (r : G) * d = ((r : G) * d * (r : G)⁻¹) * r := by group
          _ = d * r := by rw [Subgroup.coe_inclusion] at h1; rw [h1]
      exact h2.symm
    rw [hRf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcardV : Nat.card (Additive (↥D ⧸ frattini ↥D)) = q ^ 4 := by
    rw [← hDfr, relIndex_frattini_eq_card_quotient]
    rfl
  have hdim : Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) = 2 ^ 2 := by
    have h1 : Nat.card (Additive (↥D ⧸ frattini ↥D)) =
        q ^ Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
    rw [hcardV] at h1
    have := Nat.pow_right_injective hq.two_le h1
    omega
  have : FiniteDimensional (ZMod q) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  obtain ⟨z, hz⟩ := exists_center_eq_zpowers hRext
  have hK : ringChar (ZMod q) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hq2
  obtain ⟨-, -, hcent, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.minimal_extraspecial_module_scalar_centralizer.{
      0, 0, 0, 0} hRext hRcard hz hK hdim ρR hinj
  let bE : ↥L := ⟨b, hbL⟩
  have hbE5 : bE ^ 5 = 1 := Subtype.ext (by simpa using hb5)
  have hu : ρ.asGroupHom bE ∈ Subgroup.centralizer (Set.range ρR.asGroupHom) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, rfl⟩
    have hcomm : Subgroup.inclusion hRL r * bE = bE * Subgroup.inclusion hRL r := by
      apply Subtype.ext
      have := Subgroup.mem_centralizer_iff.mp hbR (r : G) r.2
      simpa using this
    change ρ.asGroupHom (Subgroup.inclusion hRL r) * ρ.asGroupHom bE =
      ρ.asGroupHom bE * ρ.asGroupHom (Subgroup.inclusion hRL r)
    rw [← map_mul, ← map_mul, hcomm]
  rw [hcent] at hu
  obtain ⟨c, hc⟩ := hu
  have hρb : ∀ v, ρ bE v = (c : ZMod q) • v := by
    intro v
    have h1 : ((ρ.asGroupHom bE : (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ) :
        Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D))) = ρ bE :=
      Representation.asGroupHom_apply ρ bE
    have h2 := congrArg (fun u : (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ =>
      (u : Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))) hc
    simp only [Units.coe_map, h1] at h2
    rw [← h2]
    simp
  have hq5p : Nat.Prime 5 := by norm_num
  have hc1 : (c : ZMod q) ≠ 1 := by
    intro h1
    have htriv : ∀ x : ↥D, ((bE • x : ↥D) : ↥D ⧸ frattini ↥D) = (x : ↥D ⧸ frattini ↥D) := by
      intro x
      have e1 := frattiniRep_apply_mk (E := ↥L) (X := ↥D) q bE x
      have e2 : ρ bE (Additive.ofMul (x : ↥D ⧸ frattini ↥D)) =
          Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by rw [hρb, h1, one_smul]
      exact Additive.ofMul.injective (e1.symm.trans e2)
    have hnot : ¬ q ∣ orderOf bE := by
      intro hdvd
      have h5 : orderOf bE ∣ 5 := orderOf_dvd_of_pow_eq_one hbE5
      exact hq5 ((Nat.prime_dvd_prime_iff_eq hq hq5p).mp (hdvd.trans h5))
    have hfix := smul_eq_of_smul_mk_eq hDq bE hnot htriv
    obtain ⟨d, hd, hne⟩ := hbD
    apply hne
    have h3 := congrArg (fun y : ↥D => (y : G)) (hfix ⟨d, hd⟩)
    simp only [hsmul] at h3
    have h4 : b * d * b⁻¹ = d := h3
    simp only [commutatorElement_def]
    rw [h4]
    group
  have hpow : ∀ (n : ℕ) (v : Additive (↥D ⧸ frattini ↥D)),
      (ρ bE ^ n) v = (c : ZMod q) ^ n • v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, hρb, map_smul, ih, smul_smul, pow_succ]
      ring_nf
  have hcp : (c : ZMod q) ^ 5 = 1 := by
    have hT : ρ bE ^ 5 = 1 := by rw [← map_pow, hbE5, map_one]
    have : Nontrivial (Additive (↥D ⧸ frattini ↥D)) :=
      Module.nontrivial_of_finrank_pos (R := ZMod q) (by rw [hdim]; norm_num)
    obtain ⟨v, hv⟩ := exists_ne (0 : Additive (↥D ⧸ frattini ↥D))
    have h1 := hpow 5 v
    rw [hT, Module.End.one_apply] at h1
    exact smul_left_injective (ZMod q) hv (by simpa using h1.symm)
  have hqmod : q % 5 = 1 := by
    have hc0 : (c : ZMod q) ≠ 0 := c.ne_zero
    have : Fact (Nat.Prime 5) := ⟨hq5p⟩
    have hord : orderOf (c : ZMod q) = 5 := orderOf_eq_prime hcp hc1
    have hdvd : orderOf (c : ZMod q) ∣ q - 1 :=
      orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hc0)
    rw [hord] at hdvd
    obtain ⟨m, hm⟩ := hdvd
    have hq1 : q = 5 * m + 1 := by have := hq.one_lt; omega
    omega
  refine ⟨hqmod, ?_⟩
  have hzbN : Subgroup.zpowers b ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.zpowers_le.mpr (hLD hbL)
  have hle : ⁅D, Subgroup.zpowers b⁆ ≤ D :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hzbN
  refine le_antisymm hle ?_
  set H' : Subgroup ↥D := (⁅D, Subgroup.zpowers b⁆).subgroupOf D with hH'
  have hsup : H' ⊔ frattini ↥D = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hc1' : (c : ZMod q) - 1 ≠ 0 := sub_ne_zero.mpr hc1
    set w : Additive (↥D ⧸ frattini ↥D) :=
      ((c : ZMod q) - 1)⁻¹ • Additive.ofMul (x : ↥D ⧸ frattini ↥D) with hw
    obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have e0 : Additive.ofMul (x₁ : ↥D ⧸ frattini ↥D) = w := by rw [hx₁]; rfl
    have e1 : ρ bE (Additive.ofMul (x₁ : ↥D ⧸ frattini ↥D)) -
        Additive.ofMul (x₁ : ↥D ⧸ frattini ↥D) = Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by
      rw [e0, hρb]
      calc (c : ZMod q) • w - w = ((c : ZMod q) - 1) • w := by rw [sub_smul, one_smul]
        _ = Additive.ofMul (x : ↥D ⧸ frattini ↥D) := by
          rw [hw, smul_smul, mul_inv_cancel₀ hc1', one_smul]
    rw [frattiniRep_apply_mk (E := ↥L) (X := ↥D) q bE x₁] at e1
    have e2 : (((bE • x₁ : ↥D) * x₁⁻¹ : ↥D) : ↥D ⧸ frattini ↥D) = (x : ↥D ⧸ frattini ↥D) := by
      apply Additive.ofMul.injective
      rw [← e1]
      simp [ofMul_mul, ofMul_inv, sub_eq_add_neg]
    have e3 : ((bE • x₁ : ↥D) * x₁⁻¹)⁻¹ * x ∈ frattini ↥D := QuotientGroup.eq.mp e2
    have e4 : (bE • x₁ : ↥D) * x₁⁻¹ ∈ H' := by
      rw [hH', Subgroup.mem_subgroupOf]
      have : (((bE • x₁ : ↥D) * x₁⁻¹ : ↥D) : G) = ⁅b, (x₁ : G)⁆ := by
        simp only [Subgroup.coe_mul, hsmul, commutatorElement_def, Subgroup.coe_inv]
        rfl
      rw [this, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) x₁.2
    have e5 : x = ((bE • x₁ : ↥D) * x₁⁻¹) * (((bE • x₁ : ↥D) * x₁⁻¹)⁻¹ * x) := by group
    rw [e5]
    exact mul_mem (Subgroup.mem_sup_left e4) (Subgroup.mem_sup_right e3)
  have htop : H' = ⊤ := frattini_nongenerating hsup
  intro g hg
  have : (⟨g, hg⟩ : ↥D) ∈ H' := by rw [htop]; exact Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.mp this)



end Scalar

end CFSG.RankThree.PartOne.Lifting36
