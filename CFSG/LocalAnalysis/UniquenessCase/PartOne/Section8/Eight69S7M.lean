module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.PGroup.FrattiniQuotientRankBound
import CFSG.GroupTheory.FrattiniQuotient
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def McLThreeCentralizerOrders : Prop :=
  ∀ x : CFSG.Blueprint.NativeSporadic.McL, orderOf x = 3 →
    Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.McL)) = 29160 ∨
      Nat.card (Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.McL)) = 972

@[expose] def McLThreeFiveMax : Prop :=
  ∀ U : Subgroup CFSG.Blueprint.NativeSporadic.McL, 3 ^ 4 * 5 ^ 3 ∣ Nat.card U → U = ⊤

private theorem s7mcl_zpowers_isPGroup {G : Type} [Group G] [Finite G] {a : G} (ha : a ^ 5 = 1) :
    IsPGroup 5 (Subgroup.zpowers a) := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp (orderOf_dvd_of_pow_eq_one ha) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

private theorem s7mcl_centralizer_le {G : Type} [Group G] [Finite G] {M B : Subgroup G}
    (hM : ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ → IsPGroup 5 X →
      Subgroup.normalizer (X : Set G) ≤ M)
    (hBM : B ≤ M) (hB : CFSG.Open.IsElemAbelian 5 B) {a : G} (haB : a ∈ B) (ha1 : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≤ M := by
  have hz : Subgroup.zpowers a ≤ M := Subgroup.zpowers_le.mpr (hBM haB)
  have hne : Subgroup.zpowers a ≠ ⊥ := fun h => ha1 (Subgroup.zpowers_eq_bot.mp h)
  refine le_trans ?_ (hM _ hz hne (s7mcl_zpowers_isPGroup (hB.2 a haB)))
  rw [← Subgroup.centralizer_closure ({a} : Set G), ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

private theorem s7mcl_le_normalizer_map {G : Type} [Group G] {H : Subgroup G} (K : Subgroup ↥H)
    [K.Normal] : H ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  intro b hb
  have h1 : (⟨b, hb⟩ : ↥H) ∈ Subgroup.normalizer (K : Set ↥H) := by
    rw [Subgroup.normalizer_eq_top K]
    exact Subgroup.mem_top _
  exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ h1)

theorem s7m_core_le {G : Type} [Group G] [Finite G] {M H : Subgroup G}
    (hM : ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ → IsPGroup 5 X →
      Subgroup.normalizer (X : Set G) ≤ M)
    (hrk : 2 ≤ CFSG.Open.pRank 5 (H ⊓ M)) :
    (CFSG.pPrimeCore 5 ↥H).map H.subtype ≤ M := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨B, hBle, hB, hBcard⟩ := CFSG.SectionRank.exists_pRank (p := 5) (by norm_num) (H ⊓ M)
  have hBrk : 5 ^ 2 ≤ Nat.card B := hBcard ▸ Nat.pow_le_pow_right (by norm_num) hrk
  have hBX : B ≤ Subgroup.normalizer
      (((CFSG.pPrimeCore 5 ↥H).map H.subtype : Subgroup G) : Set G) :=
    (hBle.trans inf_le_left).trans (s7mcl_le_normalizer_map _)
  have hX : Nat.Coprime 5 (Nat.card ((CFSG.pPrimeCore 5 ↥H).map H.subtype)) := by
    rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
    (by norm_num) hB hBrk hBX hX
  rw [← hgen]
  exact iSup_le fun a => iSup_le fun haB => iSup_le fun ha1 =>
    inf_le_right.trans (s7mcl_centralizer_le hM (hBle.trans inf_le_right) hB haB ha1)

private theorem s7mim_exists_max {Γ : Type*} [Group Γ] [Finite Γ] {M : Subgroup Γ}
    (h5 : 5 ∣ Nat.card M) :
    ∃ P : Subgroup Γ, P ≤ M ∧ P ≠ ⊥ ∧ IsPGroup 5 P ∧
      ∀ Q : Subgroup Γ, Q ≤ M → IsPGroup 5 Q → P ≤ Q → Q ≤ P := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P₀⟩ : Nonempty (Sylow 5 M) := inferInstance
  refine ⟨(P₀ : Subgroup M).map M.subtype, Subgroup.map_subtype_le _, ?_, P₀.isPGroup'.map _, ?_⟩
  · intro h
    exact P₀.ne_bot_of_dvd_card h5
      ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h)
  · intro Q hQM hQ hPQ q hq
    have h1 : (P₀ : Subgroup M) ≤ Q.subgroupOf M := fun x hx => hPQ ⟨x, hx, rfl⟩
    have h2 : Q.subgroupOf M = P₀ :=
      P₀.is_maximal' (hQ.comap_of_injective M.subtype M.subtype_injective) h1
    have h3 : (⟨q, hQM hq⟩ : M) ∈ Q.subgroupOf M := hq
    rw [h2] at h3
    exact ⟨_, h3, rfl⟩

private theorem s7mim_sylow_le {Γ : Type*} [Group Γ] [Finite Γ] {M : Subgroup Γ}
    (hM : ∀ X : Subgroup Γ, X ≤ M → X ≠ ⊥ → IsPGroup 5 X →
      Subgroup.normalizer (X : Set Γ) ≤ M)
    (h5 : 5 ∣ Nat.card M) :
    ∃ S : Sylow 5 Γ, (S : Subgroup Γ) ≤ M := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P, hPM, hPne, hP5, hPmax⟩ := s7mim_exists_max h5
  obtain ⟨S, hPS⟩ := hP5.exists_le_sylow
  have hSP : (S : Subgroup Γ) ≤ P := by
    by_contra hSP
    have : Group.IsNilpotent ↥S := IsPGroup.isNilpotent S.isPGroup'
    have hlt : P.subgroupOf S < ⊤ :=
      lt_top_iff_ne_top.mpr fun h => hSP (Subgroup.subgroupOf_eq_top.mp h)
    obtain ⟨g, hg, hgP⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hgN : (g : Γ) ∈ Subgroup.normalizer (P : Set Γ) := by
      have := Subgroup.le_normalizer_map (S : Subgroup Γ).subtype (Subgroup.mem_map_of_mem _ hg)
      rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left hPS] at this
    have hgM : (g : Γ) ∈ M := hM P hPM hPne hP5 hgN
    have hQS : P ⊔ Subgroup.zpowers (g : Γ) ≤ S :=
      sup_le hPS (Subgroup.zpowers_le.mpr g.2)
    have hQP := hPmax (P ⊔ Subgroup.zpowers (g : Γ))
      (sup_le hPM (Subgroup.zpowers_le.mpr hgM)) (S.isPGroup'.to_le hQS) le_sup_left
    exact hgP (hQP (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  exact ⟨S, hSP.trans hPM⟩

private theorem s7mim_main {Γ : Type*} [Group Γ] [Finite Γ] {M K : Subgroup Γ} [K.Normal]
    (hKM : K ≤ M)
    (hM : ∀ X : Subgroup Γ, X ≤ M → X ≠ ⊥ → IsPGroup 5 X →
      Subgroup.normalizer (X : Set Γ) ≤ M)
    (hΓM : ¬ (⊤ : Subgroup Γ) ≤ M) (h5 : 5 ∣ Nat.card M)
    {E : Subgroup (Γ ⧸ K)} (hEn : E.Normal)
    (hE5 : ∀ x : Γ ⧸ K, IsPGroup 5 (Subgroup.zpowers x) → x ∈ E) :
    ¬ E ≤ M.map (QuotientGroup.mk' K) ∧
      ∀ k : ℕ, 5 ^ k ∣ Nat.card E → 5 ^ k ∣ Nat.card ↥(E ⊓ M.map (QuotientGroup.mk' K)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨S, hSM⟩ := s7mim_sylow_le hM h5
  have hSE : (S : Subgroup Γ).map (QuotientGroup.mk' K) ≤ E := by
    rintro _ ⟨s, hs, rfl⟩
    refine hE5 _ ((S.isPGroup'.map (QuotientGroup.mk' K)).to_le ?_)
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hs)
  refine ⟨fun hED => hΓM ?_, fun k hk => ?_⟩
  · have hH1M : E.comap (QuotientGroup.mk' K) ≤ M := by
      intro x hx
      obtain ⟨m, hm, hmx⟩ := hED hx
      have hK : m⁻¹ * x ∈ K := QuotientGroup.eq.mp hmx
      simpa using M.mul_mem hm (hKM hK)
    have hSH1 : (S : Subgroup Γ) ≤ E.comap (QuotientGroup.mk' K) := fun s hs => hSE ⟨s, hs, rfl⟩
    have : (E.comap (QuotientGroup.mk' K)).Normal := hEn.comap _
    have hSne : (S : Subgroup Γ) ≠ ⊥ :=
      S.ne_bot_of_dvd_card (h5.trans (Subgroup.card_subgroup_dvd_card M))
    rw [← Sylow.normalizer_sup_eq_top' (N := E.comap (QuotientGroup.mk' K)) S hSH1]
    exact sup_le (hM _ hSM hSne S.isPGroup') hH1M
  · have hdvd : 5 ^ k ∣ Nat.card (Γ ⧸ K) := hk.trans (Subgroup.card_subgroup_dvd_card E)
    exact ((S.mapSurjective (QuotientGroup.mk'_surjective K)).pow_dvd_card_of_pow_dvd_card
      hdvd).trans (Subgroup.card_dvd_of_le (le_inf hSE (Subgroup.map_mono hSM)))

private theorem s7mim_hM_subgroupOf {G : Type} [Group G] {M H : Subgroup G}
    (hM : ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ → IsPGroup 5 X →
      Subgroup.normalizer (X : Set G) ≤ M) :
    ∀ X : Subgroup ↥H, X ≤ M.subgroupOf H → X ≠ ⊥ → IsPGroup 5 X →
      Subgroup.normalizer (X : Set ↥H) ≤ M.subgroupOf H := by
  intro X hXM hX1 hX5 h hh
  have h1 : X.map H.subtype ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hXM hx
  have h2 : X.map H.subtype ≠ ⊥ := fun h =>
    hX1 ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp h)
  exact hM _ h1 h2 (hX5.map _) (Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ hh))

theorem s7m_image {G : Type} [Group G] [Finite G] {M H : Subgroup G}
    (hM : ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ → IsPGroup 5 X →
      Subgroup.normalizer (X : Set G) ≤ M)
    (hHM : ¬ H ≤ M) (hrk : 2 ≤ CFSG.Open.pRank 5 (H ⊓ M))
    (hKM : (CFSG.pPrimeCore 5 ↥H).map H.subtype ≤ M)
    {E : Subgroup (↥H ⧸ CFSG.pPrimeCore 5 ↥H)} (hEn : E.Normal)
    (hE5 : ∀ x : ↥H ⧸ CFSG.pPrimeCore 5 ↥H, IsPGroup 5 (Subgroup.zpowers x) → x ∈ E) :
    ¬ E ≤ (M.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H)) ∧
      ∀ k : ℕ, 5 ^ k ∣ Nat.card E →
        5 ^ k ∣
          Nat.card ↥(E ⊓ (M.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H))) := by
  obtain ⟨x, hx, hx5⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank
    (by norm_num : Nat.Prime 5) (by omega : 1 ≤ CFSG.Open.pRank 5 (H ⊓ M))
  have h5 : 5 ∣ Nat.card (M.subgroupOf H) := by
    have hmem : (⟨x, hx.1⟩ : ↥H) ∈ M.subgroupOf H := hx.2
    have h1 := Subgroup.orderOf_dvd_natCard _ hmem
    rwa [Subgroup.orderOf_mk, hx5] at h1
  refine s7mim_main (fun k hk => ?_) (s7mim_hM_subgroupOf hM) (fun h => hHM ?_) h5 hEn hE5
  · exact hKM (Subgroup.mem_map_of_mem _ hk)
  · exact Subgroup.subgroupOf_eq_top.mp (top_le_iff.mp h)

private theorem s7mpf_commutator_eq {Q : Type} [Group Q] {E : Subgroup Q} [IsSimpleGroup ↥E]
    (hnp : ¬ (Nat.card ↥E).Prime) : ⁅E, E⁆ = E := by
  rw [← Subgroup.isPerfect_iff]
  refine ⟨?_⟩
  rcases (Subgroup.commutator_normal (⊤ : Subgroup ↥E) ⊤).eq_bot_or_eq_top with h | h
  · have : IsMulCommutative ↥E := (commutator_eq_bot_iff _).mp h
    exact absurd (Group.is_simple_iff_prime_card.mp ‹_›) hnp
  · exact h

private theorem s7mpf_map_eq {Q : Type} [Group Q] [Finite Q] {E : Subgroup Q} (hEn : E.Normal)
    [IsSimpleGroup ↥E] (h5 : 5 ∣ Nat.card ↥E)
    (hE5 : ∀ x : Q, IsPGroup 5 (Subgroup.zpowers x) → x ∈ E) (σ : Q ≃* Q) :
    E.map σ.toMonoidHom = E := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : (E.map σ.toMonoidHom).Normal := hEn.map _ σ.surjective
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) 5 h5
  have hy' : orderOf (y : Q) = 5 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyσ : (y : Q) ∈ E.map σ.toMonoidHom := by
    refine ⟨σ.symm y, hE5 _ (IsPGroup.of_card (n := 1) ?_), σ.apply_symm_apply y⟩
    rw [Nat.card_zpowers, MulEquiv.orderOf_eq, hy', pow_one]
  have hle : E ≤ E.map σ.toMonoidHom := by
    rcases (Subgroup.normal_subgroupOf (H := E) (N := E ⊓ E.map σ.toMonoidHom)).eq_bot_or_eq_top
      with h | h
    · have hmem : y ∈ (E ⊓ E.map σ.toMonoidHom).subgroupOf E := ⟨y.2, hyσ⟩
      rw [h, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hy
      omega
    · intro x hx
      have : (⟨x, hx⟩ : ↥E) ∈ (E ⊓ E.map σ.toMonoidHom).subgroupOf E := by
        rw [h]
        exact Subgroup.mem_top _
      exact this.2
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective σ.injective])).symm

private theorem s7mpf_exists_perfect {X : Type} [Group X] [Finite X] {K : Subgroup X}
    [K.Normal] {E : Subgroup (X ⧸ K)} (hEE : ⁅E, E⁆ = E)
    (hX1 : (E.comap (QuotientGroup.mk' K)).Characteristic) :
    ∃ J : Subgroup X, J.Characteristic ∧ ⁅J, J⁆ = J ∧ J.map (QuotientGroup.mk' K) = E := by
  have hne : {J : Subgroup X | J.Characteristic ∧ J.map (QuotientGroup.mk' K) = E}.Nonempty :=
    ⟨E.comap (QuotientGroup.mk' K), hX1,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective K) E⟩
  have : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  obtain ⟨J, ⟨hJc, hJE⟩, hmin⟩ := wellFounded_lt.has_min _ hne
  refine ⟨J, hJc, ?_, hJE⟩
  by_contra hne'
  refine hmin ⁅J, J⁆ ⟨inferInstance, ?_⟩ (lt_of_le_of_ne (Subgroup.commutator_le_right J J) hne')
  rw [Subgroup.map_commutator, hJE, hEE]

theorem s7m_perfect (hSimp : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL)
    (hCard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000)
    {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Characteristic]
    {E : Subgroup (X ⧸ K)} (hEn : E.Normal)
    (hE5 : ∀ x : X ⧸ K, IsPGroup 5 (Subgroup.zpowers x) → x ∈ E) (hE : IsSpor ↥E .McL) :
    ∃ J : Subgroup X, J.Characteristic ∧ ⁅J, J⁆ = J ∧ J.map (QuotientGroup.mk' K) = E := by
  obtain ⟨e⟩ := hE
  have hSimp' : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) := hSimp
  have hCard' : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 := hCard
  have hEs : IsSimpleGroup ↥E := e.isSimpleGroup
  have hEcard : Nat.card ↥E = 898128000 := (Nat.card_congr e.toEquiv).trans hCard'
  have hnp : ¬ (Nat.card ↥E).Prime := by
    rw [hEcard]
    norm_num
  have h5 : 5 ∣ Nat.card ↥E := by
    rw [hEcard]
    norm_num
  have hEc : E.Characteristic := Subgroup.characteristic_iff_map_eq.mpr (s7mpf_map_eq hEn h5 hE5)
  exact s7mpf_exists_perfect (s7mpf_commutator_eq hnp)
    (Subgroup.Characteristic.comap_quotient_mk hEc)

private theorem s7mcr_eq_one {M : Type*} [Monoid M] {a : M} {q n k : ℕ} (hq : q.Prime)
    (hq3 : q ≠ 3) (h3 : a ^ 3 ^ n = 1) (hqa : a ^ q ^ k = 1) : a = 1 := by
  have hcop : Nat.Coprime (3 ^ n) (q ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_three hq).mpr hq3.symm)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
    (orderOf_dvd_of_pow_eq_one hqa))

private theorem s7mcr_class_two {R : Type} [Group R] {D : Subgroup R}
    (hD : ⁅D, (⊤ : Subgroup R)⁆ ≤ D ⊓ Subgroup.centralizer (D : Set R)) :
    ⁅⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆, (⊤ : Subgroup ↥D)⁆ = ⊥ := by
  rw [Subgroup.commutator_top_right_eq_bot_iff_le_center, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_center_iff]
  intro c
  have h1 : ((a * b * a⁻¹ * b⁻¹ : ↥D) : R) ∈ Subgroup.centralizer (D : Set R) :=
    (hD (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top (b : R)))).2
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h1 c c.2)

private theorem s7mcr_comm_pow_mem {W : Type} [Group W] [Finite W] (hW : IsPGroup 3 W) :
    (∀ a b : W, a * b * a⁻¹ * b⁻¹ ∈ frattini W) ∧ ∀ a : W, a ^ 3 ∈ frattini W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hcomm, hpow, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hW
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm.is_comm.comm (a : W ⧸ frattini W) (b : W ⧸ frattini W)]
    group
  · rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hpow _

private theorem s7mcr_aut_eq_one {R : Type} [Group R] [Finite R] {D : Subgroup R}
    [D.Characteristic] (hD3 : IsPGroup 3 ↥D)
    (hfix : IsPGroup 3 (fixingSubgroup (MulAut R) (D : Set R))) {q k : ℕ} (hq : q.Prime)
    (hq3 : q ≠ 3) {α : MulAut R} (hαq : α ^ q ^ k = 1)
    (htriv : ∀ a ∈ D, α a * a⁻¹ ∈ (frattini ↥D).map D.subtype) : α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : MulAut.characteristic D α ∈
      (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥D)).ker := by
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.mem_quotientAutomorphism_kernel]
    intro x
    show (((MulAut.characteristic D α) x : ↥D) : ↥D ⧸ frattini ↥D) = (x : ↥D ⧸ frattini ↥D)
    rw [QuotientGroup.eq]
    have h1 : (α x)⁻¹ * x ∈ (frattini ↥D).map D.subtype := by
      have h2 := Subgroup.Normal.conj_mem inferInstance _ (inv_mem (htriv x x.2)) (x : R)⁻¹
      convert h2 using 1
      group
    have h3 : D.subtype ((MulAut.characteristic D α x)⁻¹ * x) = (α x)⁻¹ * (x : R) := by
      simp [MulAut.characteristic_apply_apply_coe]
    rw [← Subgroup.mem_map_iff_mem D.subtype_injective, h3]
    exact h1
  obtain ⟨n, hn⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hD3).2 ⟨_, hker⟩
  have hαD : MulAut.characteristic D α = 1 :=
    s7mcr_eq_one hq hq3 (congrArg Subtype.val hn) (by rw [← map_pow, hαq, map_one])
  have hfixD : α ∈ fixingSubgroup (MulAut R) (D : Set R) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have := congrArg (fun β : MulAut ↥D => ((β ⟨y, hy⟩ : ↥D) : R)) hαD
    simpa [MulAut.characteristic_apply_apply_coe] using this
  obtain ⟨m, hm⟩ := hfix ⟨α, hfixD⟩
  exact s7mcr_eq_one hq hq3 (congrArg Subtype.val hm) hαq

theorem s7m_crit {R : Type} [Group R] [Finite R] (hR : IsPGroup 3 R)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup R) ≤ 3) :
    ∃ W F : Subgroup R, W.Characteristic ∧ F.Characteristic ∧ F ≤ W ∧
      Nat.card W ≤ 3 ^ 6 * Nat.card F ∧
      (∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ F) ∧ (∀ a ∈ W, a ^ 3 ∈ F) ∧
      ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ α : MulAut R, IsPGroup q (Subgroup.zpowers α) →
        (∀ a ∈ W, α a * a⁻¹ ∈ F) → α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases subsingleton_or_nontrivial R with hsub | hnt
  · refine ⟨⊥, ⊥, inferInstance, inferInstance, le_rfl, by simp, ?_, ?_, ?_⟩
    · intro a ha b hb
      rw [Subgroup.mem_bot] at ha hb
      simp [ha, hb]
    · intro a ha
      rw [Subgroup.mem_bot] at ha
      simp [ha]
    · intro q _ _ α _ _
      exact MulEquiv.ext fun x => Subsingleton.elim _ _
  · obtain ⟨D, hDc, -, hDcomm, hDexp, hDfix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := 3) (by norm_num) hR
    have hD3 : IsPGroup 3 ↥D := hR.to_subgroup D
    have hlem := CFSG.GroupTheory.card_quotient_frattini_le_pow_four hD3
      (fun x => Subtype.ext (hDexp x x.2)) (s7mcr_class_two hDcomm)
      ((CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) D.subtype
        D.subtype_injective).trans hrk)
    obtain ⟨hcommF, hcubeF⟩ := s7mcr_comm_pow_mem hD3
    refine ⟨D, (frattini ↥D).map D.subtype, hDc, inferInstance, Subgroup.map_subtype_le _, ?_,
      fun a ha b hb => Subgroup.mem_map_of_mem D.subtype (hcommF ⟨a, ha⟩ ⟨b, hb⟩),
      fun a ha => Subgroup.mem_map_of_mem D.subtype (hcubeF ⟨a, ha⟩), ?_⟩
    · rw [Subgroup.card_map_of_injective D.subtype_injective,
        Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥D)]
      exact Nat.mul_le_mul_right _ (hlem.trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    · intro q hq hq3 α hα htriv
      obtain ⟨k, hk⟩ := hα ⟨α, Subgroup.mem_zpowers α⟩
      exact s7mcr_aut_eq_one hD3 hDfix hq hq3 (congrArg Subtype.val hk) htriv

private theorem s7mrd_not_dvd_card_mulAut {Q : Type} [Group Q] [Finite Q]
    (hcomm : ∀ a b : Q, a * b = b * a) (hpow : ∀ a : Q, a ^ 3 = 1) {n : ℕ} (hn : n ≤ 6)
    (hcard : Nat.card Q = 3 ^ n) : ¬ 5 ^ 3 ∣ Nat.card (MulAut Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) hcomm hpow hcard
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

private theorem s7mrd_eq_one_of_solvable {J H : Type} [Group J] [Group H]
    [Group.IsPerfect J] (f : J →* H) [Group.IsSolvable f.range] : f = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hsub : Subsingleton f.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable f.range ‹_›
  ext g
  have := hsub.elim (⟨f g, g, rfl⟩ : f.range) 1
  simpa using congrArg Subtype.val this

private theorem s7mrd_hom_trivial {J H : Type} [Group J] [Finite J] [Group H] [Finite H]
    [Group.IsPerfect J] {N : Subgroup J} [N.Normal] [Group.IsSolvable ↥N]
    [IsSimpleGroup (J ⧸ N)] (hcard : 5 ^ 3 ∣ Nat.card (J ⧸ N))
    (hH : ¬ 5 ^ 3 ∣ Nat.card H) (σ : J →* H) : σ = 1 := by
  have hnorm : (σ.ker.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  rcases Subgroup.Normal.eq_bot_or_eq_top (σ.ker.map (QuotientGroup.mk' N)) with h | h
  · exfalso
    have hle : σ.ker ≤ N := by
      have := (Subgroup.map_eq_bot_iff _).mp h
      rwa [QuotientGroup.ker_mk'] at this
    refine hH (hcard.trans ?_)
    have h1 := Subgroup.index_dvd_of_le hle
    rw [Subgroup.index_ker, Subgroup.index_eq_card] at h1
    exact h1.trans (Subgroup.card_subgroup_dvd_card σ.range)
  · have hsurj : Function.Surjective (σ.rangeRestrict.comp N.subtype) := by
      rintro ⟨_, g, rfl⟩
      have hg : QuotientGroup.mk' N g ∈ σ.ker.map (QuotientGroup.mk' N) := h ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg
      have hn : k⁻¹ * g ∈ N := QuotientGroup.eq.mp hkg
      refine ⟨⟨k⁻¹ * g, hn⟩, Subtype.ext ?_⟩
      simp [MonoidHom.mem_ker.mp hk]
    have : Group.IsSolvable σ.range := Group.isSolvable_of_surjective hsurj
    exact s7mrd_eq_one_of_solvable σ

private theorem s7mrd_exists_act {R : Type} [Group R] {W F : Subgroup R} [W.Characteristic]
    [F.Characteristic] :
    ∃ τ : MulAut R →* MulAut (↥W ⧸ F.subgroupOf W), ∀ (α : MulAut R) (a : ↥W),
      τ α (QuotientGroup.mk a) = QuotientGroup.mk (MulAut.characteristic W α a) := by
  have hmem : ∀ (α : MulAut R) (a : ↥W), (MulAut.characteristic W α a : R) ∈ F ↔ (a : R) ∈ F := by
    intro α a
    have h := Subgroup.characteristic_iff_comap_eq.mp ‹F.Characteristic› α
    have := SetLike.ext_iff.mp h (a : R)
    simpa using this
  have hmap : ∀ α : MulAut R, (F.subgroupOf W).map (MulAut.characteristic W α).toMonoidHom =
      F.subgroupOf W := by
    intro α
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (hmem α y).mpr hy
    · intro x hx
      refine ⟨MulAut.characteristic W α⁻¹ x, ?_, ?_⟩
      · exact (hmem α⁻¹ x).mpr hx
      · change MulAut.characteristic W α (MulAut.characteristic W α⁻¹ x) = x
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
  refine ⟨MonoidHom.mk' (fun α => QuotientGroup.congr (F.subgroupOf W) (F.subgroupOf W)
    (MulAut.characteristic W α) (hmap α)) ?_, fun α a => rfl⟩
  intro α β
  ext x
  induction x using QuotientGroup.induction_on with
  | H a => rfl

private theorem s7mrd_not_dvd_quot {R : Type} [Group R] [Finite R] (hR : IsPGroup 3 R)
    {W F : Subgroup R} [F.Normal] (hFW : F ≤ W) (hcard : Nat.card W ≤ 3 ^ 6 * Nat.card F)
    (hcomm : ∀ a ∈ W, ∀ b ∈ W, a * b * a⁻¹ * b⁻¹ ∈ F) (hcube : ∀ a ∈ W, a ^ 3 ∈ F) :
    ¬ 5 ^ 3 ∣ Nat.card (MulAut (↥W ⧸ F.subgroupOf W)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 (↥W ⧸ F.subgroupOf W) := (hR.to_subgroup W).to_quotient _
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hle : Nat.card (↥W ⧸ F.subgroupOf W) ≤ 3 ^ 6 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (F.subgroupOf W)
    have h2 : Nat.card (F.subgroupOf W) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFW).toEquiv
    have hpos : 0 < Nat.card F := Nat.card_pos
    rw [h2] at h1
    rw [h1] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hpos
  have hn6 : n ≤ 6 := by
    rw [hn] at hle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  refine s7mrd_not_dvd_card_mulAut ?_ ?_ hn6 hn
  · intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hcomm (↑b)⁻¹ (inv_mem b.2) (↑a)⁻¹ (inv_mem a.2)
    simpa [mul_assoc] using h
  · intro a
    induction a using QuotientGroup.induction_on with | H a => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hcube a a.2

private theorem s7mrd_isPGroup_range {J R : Type} [Group J] [Group R] [Finite R]
    (ρ : J →* MulAut R)
    (h : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ α : MulAut R, α ∈ ρ.range →
      IsPGroup q (Subgroup.zpowers α) → α = 1) : IsPGroup 3 ρ.range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.Ccomm.isPGroup_of_coprime_eq_one fun a ha => ?_
  by_contra hne
  have hord : orderOf a ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
  have hqp : (orderOf a).minFac.Prime := Nat.minFac_prime hord
  have hqd : (orderOf a).minFac ∣ orderOf a := Nat.minFac_dvd _
  have hq3 : (orderOf a).minFac ≠ 3 := by
    intro h3
    rw [h3] at hqd
    have := Nat.dvd_gcd hqd (dvd_refl 3)
    rw [Nat.Coprime.gcd_eq_one ha] at this
    omega
  have hdvd : orderOf a / (orderOf a).minFac ∣ orderOf a := Nat.div_dvd_of_dvd hqd
  have hpos : orderOf a / (orderOf a).minFac ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (orderOf_pos a) hqd) hqp.pos).ne'
  have hb : orderOf (a ^ (orderOf a / (orderOf a).minFac)) = (orderOf a).minFac := by
    rw [orderOf_pow_of_dvd hpos hdvd, Nat.div_div_self hqd (orderOf_pos a).ne']
  have hbo : orderOf ((a ^ (orderOf a / (orderOf a).minFac) : ρ.range) : MulAut R) =
      (orderOf a).minFac := by
    rw [Subgroup.orderOf_coe, hb]
  have hpg : IsPGroup (orderOf a).minFac
      (Subgroup.zpowers ((a ^ (orderOf a / (orderOf a).minFac) : ρ.range) : MulAut R)) := by
    have : Fact (orderOf a).minFac.Prime := ⟨hqp⟩
    rw [IsPGroup.iff_card, Nat.card_zpowers, hbo]
    exact ⟨1, (pow_one _).symm⟩
  have h1 := h _ hqp hq3 _ (a ^ (orderOf a / (orderOf a).minFac)).2 hpg
  rw [h1, orderOf_one] at hbo
  exact hqp.one_lt.ne hbo

theorem s7m_rad (hSimp : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL)
    (hCard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000)
    {J R : Type} [Group J] [Finite J] [Group R] [Finite R] (hJ : Group.IsPerfect J)
    {N : Subgroup J} [N.Normal] (hNs : Group.IsSolvable ↥N) (hJN : IsSpor (J ⧸ N) .McL)
    (hR : IsPGroup 3 R) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup R) ≤ 3) (ρ : J →* MulAut R) :
    ρ = 1 := by
  obtain ⟨W, F, hWc, hFc, hFW, hcard, hcomm, hcube, hq⟩ := s7m_crit hR hrk
  have := hWc
  have := hFc
  have := hJ
  have := hNs
  obtain ⟨e⟩ := hJN
  have hSimp' : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) := hSimp
  have hCard' : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 := hCard
  have : IsSimpleGroup (J ⧸ N) := e.isSimpleGroup
  have hcardJN : Nat.card (J ⧸ N) = 898128000 := (Nat.card_congr e.toEquiv).trans hCard'
  obtain ⟨τ, hτ⟩ := s7mrd_exists_act (W := W) (F := F)
  have hσ : τ.comp ρ = 1 :=
    s7mrd_hom_trivial (by rw [hcardJN]; norm_num)
      (s7mrd_not_dvd_quot hR hFW hcard hcomm hcube) (τ.comp ρ)
  have hact : ∀ j : J, ∀ a ∈ W, ρ j a * a⁻¹ ∈ F := by
    intro j a ha
    have h1 : τ (ρ j) = 1 := by simpa using DFunLike.congr_fun hσ j
    have h2 := hτ (ρ j) ⟨a, ha⟩
    rw [h1, MulAut.one_apply] at h2
    have h3 := QuotientGroup.eq.mp h2
    rw [Subgroup.mem_subgroupOf] at h3
    exact (inferInstance : F.Normal).mem_comm h3
  have hpg : IsPGroup 3 ρ.range := by
    refine s7mrd_isPGroup_range ρ fun q hqp hq3 α hα hαp => ?_
    obtain ⟨j, rfl⟩ := hα
    exact hq q hqp hq3 (ρ j) hαp (hact j)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent ρ.range := IsPGroup.isNilpotent hpg
  have : Group.IsSolvable ρ.range := inferInstance
  exact s7mrd_eq_one_of_solvable ρ

private theorem s7mly_three {X : Type} [Group X] {N : Subgroup X} [N.Normal] {A B C : Subgroup X}
    (h1 : ⁅⁅B, C⁆, A⁆ ≤ N) (h2 : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  have key : ∀ A B C : Subgroup X, ⁅⁅A, B⁆, C⁆ ≤ N ↔
      ⁅⁅A.map (QuotientGroup.mk' N), B.map (QuotientGroup.mk' N)⁆,
        C.map (QuotientGroup.mk' N)⁆ = ⊥ := by
    intro A B C
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

open scoped commutatorElement in
private theorem s7mly_core {X : Type} [Group X] {N K R J : Subgroup X} [N.Normal] [K.Normal]
    (hRK : ⁅R, K⁆ ≤ R) (hJR : ⁅J, R⁆ ≤ N)
    (hC : ∀ k ∈ K, (∀ r ∈ R, ⁅k, r⁆ ∈ N) → k ∈ R) (hJ : ⁅J, J⁆ = J) : ⁅J, K⁆ ≤ N := by
  have hRJ : ⁅R, J⁆ ≤ N := (Subgroup.commutator_comm R J).le.trans hJR
  have h1 : ⁅⁅J, R⁆, K⁆ ≤ N :=
    (Subgroup.commutator_mono_left hJR).trans (Subgroup.commutator_le_left _ _)
  have h2 : ⁅⁅R, K⁆, J⁆ ≤ N := (Subgroup.commutator_mono_left hRK).trans hRJ
  have h3 : ⁅⁅K, J⁆, R⁆ ≤ N := s7mly_three h1 h2
  have hKJ : ⁅K, J⁆ ≤ R := fun y hy =>
    hC y (Subgroup.commutator_le_left _ _ hy) fun r hr => h3 (Subgroup.commutator_mem_commutator hy hr)
  have h4 : ⁅⁅K, J⁆, J⁆ ≤ N := (Subgroup.commutator_mono_left hKJ).trans hRJ
  have h5 : ⁅⁅J, K⁆, J⁆ ≤ N := by
    rw [Subgroup.commutator_comm J K]
    exact h4
  have h6 : ⁅⁅J, J⁆, K⁆ ≤ N := s7mly_three h5 h4
  rwa [hJ] at h6

private theorem s7mly_exists_quot_act {G : Type} [Group G] (T : Subgroup G) [T.Characteristic] :
    ∃ τ : MulAut G →* MulAut (G ⧸ T), ∀ (α : MulAut G) (g : G),
      τ α (QuotientGroup.mk g) = QuotientGroup.mk (α g) := by
  have hmap : ∀ α : MulAut G, T.map α.toMonoidHom = T := fun α =>
    Subgroup.characteristic_iff_map_eq.mp ‹T.Characteristic› α
  refine ⟨MonoidHom.mk' (fun α => QuotientGroup.congr T T α (hmap α)) ?_, fun α g => rfl⟩
  intro α β
  ext x
  induction x using QuotientGroup.induction_on with
  | H a => rfl

private theorem s7mly_centralizer {K : Type} [Group K] [Finite K] (hK : Group.IsSolvable K)
    (y : K ⧸ CFSG.pPrimeCore 3 K)
    (hy : ∀ r ∈ CFSG.pCore 3 (K ⧸ CFSG.pPrimeCore 3 K), y * r = r * y) :
    y ∈ CFSG.pCore 3 (K ⧸ CFSG.pPrimeCore 3 K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := CFSG.Fitting_eq_pcore (K ⧸ CFSG.pPrimeCore 3 K) 3
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three)
  rw [← hF]
  refine CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance ?_
  rw [hF, Subgroup.mem_centralizer_iff]
  exact fun r hr => (hy r hr).symm

private theorem s7mly_rank {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hK3 : CFSG.Open.pRank 3 K ≤ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.pCore 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K))) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h0 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have h1 := CFSG.SectionRank.pRank_quotient_eq (p := 3) (CFSG.pPrimeCore 3 ↥K) h0
  have h2 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3)
    (CFSG.pCore 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K))
  have h3 := CFSG.SectionRank.pRank_mono (p := 3) Nat.prime_three.one_lt
    (le_top : CFSG.pCore 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≤ ⊤)
  have h4 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) K
  omega

private theorem s7mly_rad_apply (hSimp : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL)
    (hCard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000)
    {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal] (hKs : Group.IsSolvable ↥K)
    (hK3 : CFSG.Open.pRank 3 K ≤ 3) {J : Subgroup X} (hJ : ⁅J, J⁆ = J)
    {E : Subgroup (X ⧸ K)} (hJE : J.map (QuotientGroup.mk' K) = E) (hE : IsSpor ↥E .McL)
    {j : X} (hj : j ∈ J) (k : ↥K)
    (hk : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K) k ∈
      CFSG.pCore 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) :
    (k : X)⁻¹ * (j * k * j⁻¹) ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hKs
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  let φ : ↥J →* ↥E := ((QuotientGroup.mk' K).comp J.subtype).codRestrict E
    fun x => hJE ▸ Subgroup.mem_map_of_mem _ x.2
  have hφ : Function.Surjective φ := by
    rintro ⟨_, hx⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hJE ▸ hx)
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hker : ∀ x : ↥φ.ker, ((x : ↥J) : X) ∈ K := fun x => by
    have h := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    exact (QuotientGroup.eq_one_iff _).mp h
  let f : ↥φ.ker →* ↥K := (J.subtype.comp φ.ker.subtype).codRestrict K hker
  have hf : Function.Injective f := by
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have : Group.IsSolvable ↥φ.ker := Group.isSolvable_of_isSolvable_injective hf
  have hJN : IsSpor (↥J ⧸ φ.ker) .McL := by
    obtain ⟨e⟩ := hE
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans e⟩
  obtain ⟨τ, hτ⟩ := s7mly_exists_quot_act (CFSG.pPrimeCore 3 ↥K)
  let ρ : ↥J →* MulAut ↥(CFSG.pCore 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) :=
    (MulAut.characteristic (CFSG.pCore 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K))).comp
      (τ.comp ((MulAut.conjNormal (H := K)).comp J.subtype))
  have hρ : ρ = 1 := s7m_rad hSimp hCard inferInstance inferInstance hJN CFSG.pCore_isPGroup
    (s7mly_rank hK3) ρ
  have h1 := congrArg Subtype.val (DFunLike.congr_fun (DFunLike.congr_fun hρ ⟨j, hj⟩) ⟨_, hk⟩)
  have h2 : (τ (MulAut.conjNormal (H := K) j)) (QuotientGroup.mk k) = QuotientGroup.mk k := h1
  rw [hτ] at h2
  have h3 := Subgroup.mem_map_of_mem K.subtype (QuotientGroup.eq.mp h2.symm)
  simpa [MulAut.conjNormal_apply] using h3

open scoped commutatorElement in
private theorem s7mly_comm_le {X : Type} [Group X] {K : Subgroup X} (P : Subgroup ↥K) [P.Normal] :
    ⁅P.map K.subtype, K⁆ ≤ P.map K.subtype := by
  rw [Subgroup.commutator_le]
  intro r hr k hk
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
  have h1 : ⁅r', (⟨k, hk⟩ : ↥K)⁆ ∈ P :=
    Subgroup.commutator_le_left _ _ (Subgroup.commutator_mem_commutator hr' (Subgroup.mem_top _))
  exact ⟨_, h1, map_commutatorElement K.subtype r' ⟨k, hk⟩⟩

open scoped commutatorElement in
private theorem s7mly_lift_centralizer {X : Type} [Group X] {K : Subgroup X} (T : Subgroup ↥K)
    [T.Normal] (R : Subgroup (↥K ⧸ T))
    (hR : ∀ y : ↥K ⧸ T, (∀ r ∈ R, y * r = r * y) → y ∈ R) {k : X} (hk : k ∈ K)
    (hc : ∀ r ∈ (R.comap (QuotientGroup.mk' T)).map K.subtype,
      ⁅k, r⁆ ∈ T.map K.subtype) :
    k ∈ (R.comap (QuotientGroup.mk' T)).map K.subtype := by
  refine ⟨⟨k, hk⟩, hR _ fun ρ hρ => ?_, rfl⟩
  obtain ⟨r', rfl⟩ := QuotientGroup.mk'_surjective T ρ
  obtain ⟨x, hx, hx'⟩ := Subgroup.mem_map.mp (hc r' ⟨r', hρ, rfl⟩)
  have hxc : x = ⁅(⟨k, hk⟩ : ↥K), r'⁆ :=
    Subtype.ext (hx'.trans (map_commutatorElement K.subtype ⟨k, hk⟩ r').symm)
  have h2 : QuotientGroup.mk' T ⁅(⟨k, hk⟩ : ↥K), r'⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hxc ▸ hx)
  rw [map_commutatorElement] at h2
  exact commutatorElement_eq_one_iff_mul_comm.mp h2

theorem s7m_layer (hSimp : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL)
    (hCard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000)
    {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal] (hKs : Group.IsSolvable ↥K)
    (hK3 : CFSG.Open.pRank 3 K ≤ 3) {J : Subgroup X} (hJ : ⁅J, J⁆ = J)
    {E : Subgroup (X ⧸ K)} (hJE : J.map (QuotientGroup.mk' K) = E) (hE : IsSpor ↥E .McL) :
    ⁅J, K⁆ ≤ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine s7mly_core (R := ((CFSG.pCore 3 (↥K ⧸ CFSG.pPrimeCore 3 ↥K)).comap
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))).map K.subtype)
    (s7mly_comm_le _) ?_
    (fun k hk hc => s7mly_lift_centralizer _ _ (s7mly_centralizer hKs) hk hc) hJ
  rw [Subgroup.commutator_le]
  intro j hj r hr
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hr
  exact (inferInstance : ((CFSG.pPrimeCore 3 ↥K).map K.subtype).Normal).mem_comm
    (s7mly_rad_apply hSimp hCard hKs hK3 hJ hJE hE hj k hk)

private theorem s7mqs_inner {E : Type} [Group E] [Finite E]
    (hcen : ∀ e : E, (∀ e' : E, e * e' = e' * e) → e = 1) (hOut : Nat.card (Outer E) ≤ 2)
    (τ : MulAut E) (hτ : τ ^ 3 = 1) : ∃ e : E, τ = MulAut.conj e ∧ e ^ 3 = 1 := by
  have hc : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner E)) τ = 1 := by
    set c := (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner E)) τ
      with hcdef
    have h3 : c ^ 3 = 1 := by rw [hcdef, ← map_pow, hτ, map_one]
    have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h2 : orderOf c ∣ Nat.card (Outer E) := orderOf_dvd_natCard c
    have hpos : 0 < Nat.card (Outer E) := Nat.card_pos
    have hg : Nat.gcd 3 (Nat.card (Outer E)) = 1 := by
      generalize Nat.card (Outer E) = n at hOut hpos ⊢
      interval_cases n <;> norm_num
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hg ▸ Nat.dvd_gcd h1 h2))
  obtain ⟨e, he⟩ := (QuotientGroup.eq_one_iff _).mp hc
  refine ⟨e, he.symm, hcen _ fun e' => ?_⟩
  have h1 : MulAut.conj (e ^ 3) = 1 := by rw [map_pow, he, hτ]
  have h2 := congrArg (fun f : MulAut E => f e') h1
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  exact mul_inv_eq_iff_eq_mul.mp h2

private theorem s7mqs_center {P E : Type} [Group P] [Group E] (π : P →* E)
    (hπ : Function.Surjective π) {A : Subgroup P} [A.Normal] (hAB : A ≤ π.ker)
    (hcomm : ∀ b ∈ π.ker, ∀ p : P, p * b * p⁻¹ * b⁻¹ ∈ A)
    (hcen : ∀ e : E, (∀ e' : E, e * e' = e' * e) → e = 1) :
    Subgroup.center (P ⧸ A) = π.ker.map (QuotientGroup.mk' A) := by
  ext q
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective A q
  constructor
  · intro hq
    refine ⟨p, MonoidHom.mem_ker.mpr (hcen _ fun e' => ?_), rfl⟩
    obtain ⟨p', rfl⟩ := hπ e'
    have h1 : ((p' * p : P) : P ⧸ A) = ((p * p' : P) : P ⧸ A) :=
      Subgroup.mem_center_iff.mp hq (p' : P ⧸ A)
    have h2 := MonoidHom.mem_ker.mp (hAB (QuotientGroup.eq.mp h1))
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [← map_mul, ← map_mul]
    exact h2.symm
  · rintro ⟨b, hb, hbq⟩
    rw [← hbq, Subgroup.mem_center_iff]
    intro g
    obtain ⟨p', rfl⟩ := QuotientGroup.mk'_surjective A g
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h := A.inv_mem (hcomm b⁻¹ (inv_mem hb) p'⁻¹)
    have h' : (p' * b)⁻¹ * (b * p') = (p'⁻¹ * b⁻¹ * p'⁻¹⁻¹ * b⁻¹⁻¹)⁻¹ := by group
    rw [h']
    exact h

private theorem s7mqs_mult {P E : Type} [Group P] [Group.IsPerfect P] [Group E] (π : P →* E)
    (hπ : Function.Surjective π) {A : Subgroup P} [A.Normal] (hAB : A ≤ π.ker)
    (hcomm : ∀ b ∈ π.ker, ∀ p : P, p * b * p⁻¹ * b⁻¹ ∈ A)
    (hcen : ∀ e : E, (∀ e' : E, e * e' = e' * e) → e = 1)
    (hMult : ∀ {Q : Type} [Group Q], Group.IsPerfect Q → (Q ⧸ Subgroup.center Q ≃* E) →
      Nat.card (Subgroup.center Q) ∣ 3) :
    Nat.card π.ker ∣ 3 * Nat.card A := by
  have hcenter := s7mqs_center π hπ hAB hcomm hcen
  have hiso : (P ⧸ A) ⧸ Subgroup.center (P ⧸ A) ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      ((QuotientGroup.quotientQuotientEquivQuotient A π.ker hAB).trans
        (QuotientGroup.quotientKerEquivOfSurjective π hπ))
  have h3 := hMult inferInstance hiso
  rw [hcenter] at h3
  have h4 : Nat.card π.ker = Nat.card A * Nat.card (π.ker.map (QuotientGroup.mk' A)) := by
    have h5 := Subgroup.relIndex_mul_relIndex ⊥ A π.ker bot_le hAB
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h5
    have h6 := Subgroup.relIndex_ker (K := π.ker) (QuotientGroup.mk' A)
    rw [QuotientGroup.ker_mk'] at h6
    rw [← h6]
    exact h5.symm
  rw [h4, mul_comm 3]
  exact mul_dvd_mul_left _ h3

open scoped commutatorElement in
private theorem s7mqs_disp {X : Type} [Group X] {N K J : Subgroup X} [N.Normal]
    (hJ : ⁅J, J⁆ = J) (hJK : ⁅J, K⁆ ≤ N) (φ : MulAut X) (hφJ : J.map φ.toMonoidHom = J)
    {x : X} (hx : x ∈ J) (hc : ∀ j ∈ J, (φ j)⁻¹ * (x * j * x⁻¹) ∈ K) :
    ∀ j ∈ J, (φ j)⁻¹ * (x * j * x⁻¹) ∈ N := by
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  have hφ : ∀ g ∈ J, φ g ∈ J := fun g hg => hφJ ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hg
  let c : X → X := fun g => (φ g)⁻¹ * (x * g * x⁻¹)
  have hcJ : ∀ g ∈ J, c g ∈ J := fun g hg =>
    mul_mem (inv_mem (hφ g hg)) (mul_mem (mul_mem hx hg) (inv_mem hx))
  have hid : ∀ a b : X, c (a * b) = (φ b)⁻¹ * c a * φ b * c b := fun a b => by
    simp only [c, map_mul]
    group
  have hψ : ∀ g ∈ J, ∀ u ∈ K, QuotientGroup.mk' N g * QuotientGroup.mk' N u =
      QuotientGroup.mk' N u * QuotientGroup.mk' N g := by
    intro g hg u hu
    have h : QuotientGroup.mk' N ⁅g, u⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hJK (Subgroup.commutator_mem_commutator hg hu))
    rw [map_commutatorElement] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  let d : ↥J →* X ⧸ N :=
    { toFun := fun j => QuotientGroup.mk' N (c j)
      map_one' := by simp [c]
      map_mul' := fun a b => by
        have hu := hψ (φ b) (hφ b b.2) (c a) (hc a a.2)
        rw [Subgroup.coe_mul, hid, map_mul, map_mul, map_mul, map_inv,
          mul_assoc (QuotientGroup.mk' N (φ b))⁻¹, ← hu, ← mul_assoc, inv_mul_cancel, one_mul] }
  have hd : d = 1 := by
    have h1 : (⊤ : Subgroup ↥J) ≤ d.ker := by
      have h2 : ⁅(⊤ : Subgroup ↥J), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top (G := ↥J)
      rw [← h2, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hψ (c a) (hcJ a a.2) (c b) (hc b b.2))
    ext j
    exact MonoidHom.mem_ker.mp (h1 (Subgroup.mem_top j))
  intro j hj
  exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hd ⟨j, hj⟩)

private theorem s7mqs_restrict {G : Type} [Group G] {H : Subgroup G} (f : MulAut G)
    (hf : H.map f.toMonoidHom = H) : ∃ g : MulAut H, ∀ h : H, ((g h : H) : G) = f (h : G) := by
  have hmem : ∀ h ∈ H, f h ∈ H := fun h hh => hf ▸ Subgroup.mem_map_of_mem f.toMonoidHom hh
  have hmem' : ∀ h ∈ H, f.symm h ∈ H := fun h hh => by
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp (hf ▸ hh)
    simpa using hy
  exact ⟨{ toFun := fun h => ⟨f h, hmem h h.2⟩
           invFun := fun h => ⟨f.symm h, hmem' h h.2⟩
           left_inv := fun h => Subtype.ext (f.symm_apply_apply h)
           right_inv := fun h => Subtype.ext (f.apply_symm_apply h)
           map_mul' := fun a b => Subtype.ext (map_mul f (a : G) (b : G)) }, fun h => rfl⟩

private theorem s7mqs_inner_lift {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    {J : Subgroup X} {E : Subgroup (X ⧸ K)} (hJE : J.map (QuotientGroup.mk' K) = E)
    (hcen : ∀ e : ↥E, (∀ e' : ↥E, e * e' = e' * e) → e = 1)
    (hOut : Nat.card (Outer ↥E) ≤ 2) (φ : MulAut X) (hφ3 : φ ^ 3 = 1)
    (hφK : K.map φ.toMonoidHom = K) (hφJ : J.map φ.toMonoidHom = J) :
    ∃ x ∈ J, x ^ 3 ∈ K ∧ ∀ j ∈ J, (φ j)⁻¹ * (x * j * x⁻¹) ∈ K := by
  set τ : MulAut (X ⧸ K) := QuotientGroup.congr K K φ hφK with hτ
  have hτmk : ∀ g : X, τ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) := fun g => rfl
  have hτE : E.map τ.toMonoidHom = E := by
    have hcomp : τ.toMonoidHom.comp (QuotientGroup.mk' K) =
        (QuotientGroup.mk' K).comp φ.toMonoidHom := MonoidHom.ext hτmk
    rw [← hJE, Subgroup.map_map, hcomp, ← Subgroup.map_map, hφJ]
  obtain ⟨g, hg⟩ := s7mqs_restrict τ hτE
  have hφ3' : ∀ j : X, φ (φ (φ j)) = j := fun j => by
    have := congrArg (fun f : MulAut X => f j) hφ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hg3 : g ^ 3 = 1 := by
    ext h
    have h1 : ((g ^ 3) h : ↥E) = g (g (g h)) := by simp [pow_succ, MulAut.mul_apply]
    rw [h1, hg, hg, hg]
    obtain ⟨j, hj⟩ := QuotientGroup.mk_surjective (h : X ⧸ K)
    rw [← hj, hτmk, hτmk, hτmk, hφ3']
    exact hj
  obtain ⟨e, he, he3⟩ := s7mqs_inner hcen hOut g hg3
  have he2 : (e : X ⧸ K) ∈ J.map (QuotientGroup.mk' K) := by
    rw [hJE]
    exact e.2
  obtain ⟨x, hxJ, hxe⟩ := Subgroup.mem_map.mp he2
  refine ⟨x, hxJ, ?_, fun j hj => ?_⟩
  · refine (QuotientGroup.eq_one_iff _).mp ?_
    change QuotientGroup.mk' K (x ^ 3) = 1
    rw [map_pow, hxe, ← Subgroup.coe_pow, he3, Subgroup.coe_one]
  · have hjE : QuotientGroup.mk' K j ∈ E := hJE ▸ Subgroup.mem_map_of_mem _ hj
    have h1 := hg ⟨_, hjE⟩
    rw [he] at h1
    have h2 : ((MulAut.conj e ⟨_, hjE⟩ : ↥E) : X ⧸ K) =
        QuotientGroup.mk' K (x * j * x⁻¹) := by
      rw [MulAut.conj_apply]
      change (e : X ⧸ K) * QuotientGroup.mk' K j * (e : X ⧸ K)⁻¹ = _
      rw [← hxe, map_mul, map_mul, map_inv]
    rw [h2] at h1
    exact QuotientGroup.eq.mp (hτmk j ▸ h1.symm)

private theorem s7mqs_trivial_center {E : Type} [Group E] [IsSimpleGroup E]
    (h : ¬ (Nat.card E).Prime) : ∀ e : E, (∀ e' : E, e * e' = e' * e) → e = 1 := by
  intro e he
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center E) with h1 | h1
  · exact Subgroup.mem_bot.mp (h1 ▸ Subgroup.mem_center_iff.mpr fun g => (he g).symm)
  · exfalso
    have : IsMulCommutative E :=
      ⟨⟨fun a b => ((Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top a)) b).symm⟩⟩
    exact h (Group.is_simple_iff_prime_card.mp ‹_›)

private theorem s7mqs_card_subgroupOf {X : Type} [Group X] (J K : Subgroup X) :
    Nat.card ↥(K.subgroupOf J) = Nat.card ↥(J ⊓ K) := by
  rw [← Subgroup.inf_subgroupOf_left K J]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ⊓ K ≤ J)).toEquiv

open scoped commutatorElement in
private theorem s7mqs_abstract {X : Type} [Group X] [Finite X] {K N J : Subgroup X} [K.Normal]
    [N.Normal] (hNK : N ≤ K) (hJ : ⁅J, J⁆ = J) {E : Subgroup (X ⧸ K)}
    (hJE : J.map (QuotientGroup.mk' K) = E) (hJK : ⁅J, K⁆ ≤ N)
    (hcen : ∀ e : ↥E, (∀ e' : ↥E, e * e' = e' * e) → e = 1) (hOut : Nat.card (Outer ↥E) ≤ 2)
    (hMult : ∀ {Q : Type} [Group Q], Group.IsPerfect Q → (Q ⧸ Subgroup.center Q ≃* ↥E) →
      Nat.card (Subgroup.center Q) ∣ 3)
    (φ : MulAut X) (hφ3 : φ ^ 3 = 1) (hφK : K.map φ.toMonoidHom = K)
    (hφJ : J.map φ.toMonoidHom = J) :
    ∃ x ∈ J, x ^ 3 ∈ K ∧ (∀ j ∈ J, (φ j)⁻¹ * (x * j * x⁻¹) ∈ N) ∧
      Nat.card ↥(J ⊓ K) ∣ 3 * Nat.card ↥(J ⊓ N) := by
  obtain ⟨x, hxJ, hx3, hc⟩ := s7mqs_inner_lift hJE hcen hOut φ hφ3 hφK hφJ
  refine ⟨x, hxJ, hx3, s7mqs_disp hJ hJK φ hφJ hxJ hc, ?_⟩
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hJ
  let π : ↥J →* ↥E := ((QuotientGroup.mk' K).comp J.subtype).codRestrict E
    fun y => hJE ▸ Subgroup.mem_map_of_mem _ y.2
  have hπ : Function.Surjective π := by
    rintro ⟨_, hy⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hJE ▸ hy)
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
  have hker : π.ker = K.subgroupOf J := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun h => (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h),
      fun h => Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)⟩
  have hAB : N.subgroupOf J ≤ π.ker := hker ▸ Subgroup.subgroupOf_mono J hNK
  have hcomm : ∀ b ∈ π.ker, ∀ p : ↥J, p * b * p⁻¹ * b⁻¹ ∈ N.subgroupOf J := by
    intro b hb p
    rw [hker, Subgroup.mem_subgroupOf] at hb
    exact hJK (Subgroup.commutator_mem_commutator p.2 hb)
  have h := s7mqs_mult π hπ hAB hcomm hcen hMult
  rwa [hker, s7mqs_card_subgroupOf, s7mqs_card_subgroupOf] at h

theorem s7m_quasi (hSimp : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL)
    (hCard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000)
    (hOut : Nat.card (Outer CFSG.Blueprint.NativeSporadic.McL) ≤ 2)
    (hMult : ∀ {Q : Type} [Group Q], Group.IsPerfect Q →
      (Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.McL) →
        Nat.card (Subgroup.center Q) ∣ 3)
    {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal] {J : Subgroup X}
    (hJ : ⁅J, J⁆ = J) {E : Subgroup (X ⧸ K)} (hJE : J.map (QuotientGroup.mk' K) = E)
    (hE : IsSpor ↥E .McL) (hJK : ⁅J, K⁆ ≤ (CFSG.pPrimeCore 3 ↥K).map K.subtype)
    (φ : MulAut X) (hφ3 : φ ^ 3 = 1) (hφK : K.map φ.toMonoidHom = K)
    (hφJ : J.map φ.toMonoidHom = J) :
    ∃ x ∈ J, x ^ 3 ∈ K ∧
      (∀ j ∈ J, (φ j)⁻¹ * (x * j * x⁻¹) ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype) ∧
      Nat.card ↥(J ⊓ K) ∣ 3 * Nat.card ↥(J ⊓ (CFSG.pPrimeCore 3 ↥K).map K.subtype) := by
  obtain ⟨e⟩ := hE
  have hSimp' : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) := hSimp
  have hCard' : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 := hCard
  have hOut' : Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .McL)) ≤ 2 := hOut
  have : IsSimpleGroup ↥E := e.isSimpleGroup
  have hcardE : Nat.card ↥E = 898128000 := (Nat.card_congr e.toEquiv).trans hCard'
  have hOutE : Nat.card (Outer ↥E) ≤ 2 :=
    (Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv).le.trans hOut'
  have hMultE : ∀ {Q : Type} [Group Q], Group.IsPerfect Q → (Q ⧸ Subgroup.center Q ≃* ↥E) →
      Nat.card (Subgroup.center Q) ∣ 3 := fun hQ f => hMult hQ (f.trans e)
  exact s7mqs_abstract (N := (CFSG.pPrimeCore 3 ↥K).map K.subtype) (Subgroup.map_subtype_le _) hJ
    hJE hJK (s7mqs_trivial_center (by rw [hcardE]; norm_num)) hOutE hMultE φ hφ3 hφK hφJ

private theorem s7mfx_lift {X : Type} [Group X] [Finite X] {N : Subgroup X} (φ : MulAut X)
    (hφ3 : φ ^ 3 = 1) (hφN : ∀ n ∈ N, φ n ∈ N) (hN3 : ¬ 3 ∣ Nat.card N) {g : X}
    (hg : (φ g)⁻¹ * g ∈ N) : ∃ f : X, φ f = f ∧ g⁻¹ * f ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hφ3' : ∀ y : X, φ (φ (φ y)) = y := fun y => by
    have := congrArg (fun f : MulAut X => f y) hφ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hg' : g⁻¹ * φ g ∈ N := by
    have h := N.inv_mem hg
    rwa [mul_inv_rev, inv_inv] at h
  have hmem : ∀ n : N, g⁻¹ * φ (g * n) ∈ N := fun n => by
    have h : g⁻¹ * φ (g * n) = (g⁻¹ * φ g) * φ n := by rw [map_mul]; group
    rw [h]
    exact N.mul_mem hg' (hφN _ n.2)
  let f : N → N := fun n => ⟨g⁻¹ * φ (g * n), hmem n⟩
  have hinj : Function.Injective f := fun a b h => by
    have h1 : g⁻¹ * φ (g * a) = g⁻¹ * φ (g * b) := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel (φ.injective (mul_left_cancel h1)))
  let σ : Equiv.Perm N := Equiv.ofBijective f ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have hσ : ∀ m : N, g * ((σ m : N) : X) = φ (g * m) := fun m => mul_inv_cancel_left g _
  have hσ3 : σ ^ 3 = 1 := by
    refine Equiv.ext fun n => Subtype.ext ?_
    have e : (σ ^ 3) n = σ (σ (σ n)) := by simp [pow_succ, Equiv.Perm.mul_apply]
    rw [e]
    change ((σ (σ (σ n)) : N) : X) = (n : X)
    refine mul_left_cancel (a := g) ?_
    rw [hσ, hσ, hσ, hφ3']
  have : Fintype N := Fintype.ofFinite N
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (α := N) (p := 3) (n := 1)
    (by rwa [← Nat.card_eq_fintype_card]) (σ := σ) (by simpa using hσ3)
  have h1 : g * (a : X) = φ (g * a) := by rw [← hσ, ha]
  exact ⟨g * a, h1.symm, by rw [inv_mul_cancel_left]; exact a.2⟩

private theorem s7mfx_count {Y : Type} [Group Y] [Finite Y] {P T : Type} [Group P] [Group T]
    (A D : Subgroup Y) (ψ : P →* ↥A) (hψ : Function.Surjective ψ) (c : P →* T)
    (hkc : ψ.ker ≤ c.ker) (hc : Nat.card c.range ∣ 3)
    (hD : ∀ p : P, c p = 1 → ((ψ p : ↥A) : Y) ∈ D) : Nat.card ↥A ∣ 3 * Nat.card ↥D := by
  set c' : ↥A →* T :=
    ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ) ⟨c, hkc⟩
    with hc'def
  have hc' : ∀ p : P, c' (ψ p) = c p := fun p =>
    ψ.liftOfRightInverse_comp_apply (Function.surjInv hψ) (Function.rightInverse_surjInv hψ)
      ⟨c, hkc⟩ p
  have hrange : c'.range ≤ c.range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨p, rfl⟩ := hψ a
    exact ⟨p, (hc' p).symm⟩
  have h2 : c'.ker.map A.subtype ≤ D := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨p, rfl⟩ := hψ a
    exact hD p ((hc' p).symm.trans (MonoidHom.mem_ker.mp ha))
  have h3 : Nat.card c'.ker ∣ Nat.card D := by
    rw [← Subgroup.card_subtype A c'.ker]
    exact Subgroup.card_dvd_of_le h2
  rw [← Subgroup.index_mul_card c'.ker, Subgroup.index_ker]
  exact mul_dvd_mul ((Subgroup.card_dvd_of_le hrange).trans hc) h3

private theorem s7mfx_card_image {X : Type} [Group X] [Finite X] {K N J : Subgroup X} [N.Normal]
    (hNK : N ≤ K) (hZ : Nat.card ↥(J ⊓ K) ∣ 3 * Nat.card ↥(J ⊓ N)) :
    Nat.card ((QuotientGroup.mk' N).comp (J ⊓ K).subtype).range ∣ 3 := by
  set g := (QuotientGroup.mk' N).comp (J ⊓ K).subtype with hg
  have hker : g.ker = N.subgroupOf (J ⊓ K) := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have h1 : Nat.card g.range * Nat.card ↥(J ⊓ N) = Nat.card ↥(J ⊓ K) := by
    have h2 := Subgroup.index_mul_card g.ker
    rw [Subgroup.index_ker, hker, s7mqs_card_subgroupOf, inf_assoc, inf_eq_right.mpr hNK] at h2
    exact h2
  have hpos : 0 < Nat.card ↥(J ⊓ N) := Nat.card_pos
  rw [← h1] at hZ
  exact Nat.dvd_of_mul_dvd_mul_right hpos hZ

open scoped commutatorElement in
private theorem s7mfx_abstract {X : Type} [Group X] [Finite X] {K N J : Subgroup X} [K.Normal]
    [N.Normal] (hNK : N ≤ K) (hJK : ⁅J, K⁆ ≤ N) {E : Subgroup (X ⧸ K)}
    (hJE : J.map (QuotientGroup.mk' K) = E) (φ : MulAut X) {x : X} (hxJ : x ∈ J)
    (hag : ∀ j ∈ J, (φ j)⁻¹ * (x * j * x⁻¹) ∈ N)
    (hlift : ∀ g : X, (φ g)⁻¹ * g ∈ N → ∃ f : X, φ f = f ∧ g⁻¹ * f ∈ N)
    (hZ : Nat.card ↥(J ⊓ K) ∣ 3 * Nat.card ↥(J ⊓ N)) :
    Nat.card ↥(E ⊓ Subgroup.centralizer ({QuotientGroup.mk' K x} : Set (X ⧸ K))) ∣
      3 * Nat.card ↥(E ⊓ (MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id X)).map
        (QuotientGroup.mk' K)) := by
  set C : Subgroup (X ⧸ K) := Subgroup.centralizer ({QuotientGroup.mk' K x} : Set (X ⧸ K))
    with hC
  set Pi : Subgroup X := J ⊓ C.comap (QuotientGroup.mk' K) with hPi
  have hPiJ : ∀ j ∈ Pi, j ∈ J := fun j hj => (Subgroup.mem_inf.mp hj).1
  have hcomm : ∀ j ∈ Pi, QuotientGroup.mk' K x * QuotientGroup.mk' K j =
      QuotientGroup.mk' K j * QuotientGroup.mk' K x := fun j hj =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hj).2) _
      (Set.mem_singleton _)
  have hcK : ∀ j ∈ Pi, j⁻¹ * (x * j * x⁻¹) ∈ K := by
    intro j hj
    have h := hcomm j hj
    refine (QuotientGroup.eq_one_iff _).mp ?_
    change QuotientGroup.mk' K (j⁻¹ * (x * j * x⁻¹)) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel_right, inv_mul_cancel]
  have hcJ : ∀ j ∈ Pi, j⁻¹ * (x * j * x⁻¹) ∈ J := fun j hj =>
    J.mul_mem (J.inv_mem (hPiJ j hj)) (J.mul_mem (J.mul_mem hxJ (hPiJ j hj)) (J.inv_mem hxJ))
  have hψ : ∀ g ∈ J, ∀ u ∈ K, QuotientGroup.mk' N g * QuotientGroup.mk' N u =
      QuotientGroup.mk' N u * QuotientGroup.mk' N g := by
    intro g hg u hu
    have h : QuotientGroup.mk' N ⁅g, u⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hJK (Subgroup.commutator_mem_commutator hg hu))
    rw [map_commutatorElement] at h
    exact commutatorElement_eq_one_iff_mul_comm.mp h
  let c : X → X := fun j => j⁻¹ * (x * j * x⁻¹)
  have hid : ∀ a b : X, c (a * b) = b⁻¹ * c a * b * c b := fun a b => by
    simp only [c]
    group
  let cN : ↥Pi →* X ⧸ N :=
    { toFun := fun j => QuotientGroup.mk' N (c j)
      map_one' := by simp [c]
      map_mul' := fun a b => by
        have hu := hψ (b : X) (hPiJ b b.2) _ (hcK a a.2)
        rw [Subgroup.coe_mul, hid, map_mul, map_mul, map_mul, map_inv,
          mul_assoc (QuotientGroup.mk' N b)⁻¹, ← hu, ← mul_assoc, inv_mul_cancel, one_mul] }
  let ψ : ↥Pi →* ↥(E ⊓ C) :=
    ((QuotientGroup.mk' K).comp Pi.subtype).codRestrict (E ⊓ C) fun j =>
      Subgroup.mem_inf.mpr ⟨hJE ▸ Subgroup.mem_map_of_mem _ (hPiJ j j.2),
        Subgroup.mem_comap.mp (Subgroup.mem_inf.mp j.2).2⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, hyE, hyC⟩
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp (hJE ▸ hyE)
    exact ⟨⟨j, Subgroup.mem_inf.mpr ⟨hj, Subgroup.mem_comap.mpr hyC⟩⟩, rfl⟩
  have hkc : ψ.ker ≤ cN.ker := by
    intro j hj
    have hjK : (j : X) ∈ K :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hj))
    have h1 : x * (j : X) * x⁻¹ * (j : X)⁻¹ ∈ N :=
      hJK (Subgroup.commutator_mem_commutator hxJ hjK)
    have h2 := (inferInstance : N.Normal).conj_mem _ h1 (j : X)⁻¹
    have h3 : (j : X)⁻¹ * (x * j * x⁻¹ * (j : X)⁻¹) * (j : X)⁻¹⁻¹ =
        (j : X)⁻¹ * (x * j * x⁻¹) := by group
    rw [h3] at h2
    exact (QuotientGroup.eq_one_iff _).mpr h2
  have hrange : Nat.card cN.range ∣ 3 := by
    refine (Subgroup.card_dvd_of_le ?_).trans (s7mfx_card_image (J := J) hNK hZ)
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨(j : X)⁻¹ * (x * j * x⁻¹), Subgroup.mem_inf.mpr ⟨hcJ j j.2, hcK j j.2⟩⟩, rfl⟩
  refine s7mfx_count (E ⊓ C) (E ⊓ (MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id X)).map
    (QuotientGroup.mk' K)) ψ hψs cN hkc hrange fun j hj => ?_
  have hc : (j : X)⁻¹ * (x * j * x⁻¹) ∈ N := (QuotientGroup.eq_one_iff _).mp hj
  have hjJ : (j : X) ∈ J := hPiJ j j.2
  have h1 : (φ j)⁻¹ * (j : X) ∈ N := by
    have h2 := N.mul_mem (hag j hjJ) (N.inv_mem hc)
    have h3 : (φ j)⁻¹ * (x * j * x⁻¹) * ((j : X)⁻¹ * (x * j * x⁻¹))⁻¹ = (φ j)⁻¹ * (j : X) := by
      group
    rwa [h3] at h2
  obtain ⟨f, hf, hjf⟩ := hlift j h1
  exact ⟨hJE ▸ Subgroup.mem_map_of_mem _ hjJ, f, hf, (QuotientGroup.eq.mpr (hNK hjf)).symm⟩

theorem s7m_fix {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal] {J : Subgroup X}
    {E : Subgroup (X ⧸ K)} (hJE : J.map (QuotientGroup.mk' K) = E)
    (hJK : ⁅J, K⁆ ≤ (CFSG.pPrimeCore 3 ↥K).map K.subtype)
    (φ : MulAut X) (hφ3 : φ ^ 3 = 1) (hφK : K.map φ.toMonoidHom = K) {x : X} (hxJ : x ∈ J)
    (hag : ∀ j ∈ J, (φ j)⁻¹ * (x * j * x⁻¹) ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype)
    (hZ : Nat.card ↥(J ⊓ K) ∣ 3 * Nat.card ↥(J ⊓ (CFSG.pPrimeCore 3 ↥K).map K.subtype)) :
    Nat.card ↥(E ⊓ Subgroup.centralizer ({QuotientGroup.mk' K x} : Set (X ⧸ K))) ∣
      3 * Nat.card ↥(E ⊓ (MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id X)).map
        (QuotientGroup.mk' K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 : ¬ 3 ∣ Nat.card ((CFSG.pPrimeCore 3 ↥K).map K.subtype) := by
    rw [Subgroup.card_subtype K (CFSG.pPrimeCore 3 ↥K)]
    exact (Nat.prime_three.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card
  have hφN : ∀ n ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype,
      φ n ∈ (CFSG.pPrimeCore 3 ↥K).map K.subtype := by
    obtain ⟨g, hg⟩ := s7mqs_restrict φ hφK
    rintro _ ⟨k, hk, rfl⟩
    have h1 : g k ∈ (CFSG.pPrimeCore 3 ↥K).map g.toMonoidHom := Subgroup.mem_map_of_mem _ hk
    rw [Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pPrimeCore 3 ↥K).Characteristic) g] at h1
    exact ⟨g k, h1, hg k⟩
  exact s7mfx_abstract (N := (CFSG.pPrimeCore 3 ↥K).map K.subtype) (Subgroup.map_subtype_le _) hJK
    hJE φ hxJ hag (fun g hg => s7mfx_lift φ hφ3 hφN hN3 hg) hZ

private theorem s7mct_centralizer_card {Q A : Type} [Group Q] [Group A] {E : Subgroup Q}
    (e : ↥E ≃* A) {y : Q} (hyE : y ∈ E) :
    Nat.card ↥(E ⊓ Subgroup.centralizer ({y} : Set Q)) =
      Nat.card ↥(Subgroup.centralizer ({e ⟨y, hyE⟩} : Set A)) := by
  have h1 : (Subgroup.centralizer ({y} : Set Q)).subgroupOf E =
      Subgroup.centralizer ({(⟨y, hyE⟩ : ↥E)} : Set ↥E) := by
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff,
      Subgroup.coe_mul]
  have h2 : Nat.card ↥(E ⊓ Subgroup.centralizer ({y} : Set Q)) =
      Nat.card ↥((Subgroup.centralizer ({y} : Set Q)).subgroupOf E) := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [h2, h1]
  refine Nat.card_congr (e.toEquiv.subtypeEquiv fun z => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change _ ↔ e z * e ⟨y, hyE⟩ = e ⟨y, hyE⟩ * e z
  rw [← map_mul, ← map_mul]
  exact e.injective.eq_iff.symm

private theorem s7mct_card_subgroupOf {Q : Type} [Group Q] (E D : Subgroup Q) :
    Nat.card ↥(D.subgroupOf E) = Nat.card ↥(E ⊓ D) := by
  rw [← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_comm]

private theorem s7mct_main {Q A : Type} [Group Q] [Group A] {E D : Subgroup Q} (e : ↥E ≃* A)
    (hCard : Nat.card A = 898128000)
    (hCent : ∀ x : A, orderOf x = 3 →
      Nat.card (Subgroup.centralizer ({x} : Set A)) = 29160 ∨
        Nat.card (Subgroup.centralizer ({x} : Set A)) = 972)
    (hMax : ∀ U : Subgroup A, 3 ^ 4 * 5 ^ 3 ∣ Nat.card U → U = ⊤) (hED : ¬ E ≤ D)
    (h5 : ∀ k : ℕ, 5 ^ k ∣ Nat.card E → 5 ^ k ∣ Nat.card ↥(E ⊓ D)) {y : Q} (hyE : y ∈ E)
    (hy3 : y ^ 3 = 1)
    (hdvd : Nat.card ↥(E ⊓ Subgroup.centralizer ({y} : Set Q)) ∣ 3 * Nat.card ↥(E ⊓ D)) :
    False := by
  have hEcard : Nat.card ↥E = 898128000 := (Nat.card_congr e.toEquiv).trans hCard
  have h3 : 3 ^ 5 ∣ Nat.card ↥(E ⊓ Subgroup.centralizer ({y} : Set Q)) := by
    by_cases hy1 : y = 1
    · have : E ⊓ Subgroup.centralizer ({y} : Set Q) = E :=
        inf_eq_left.mpr fun z _ => by simp [Subgroup.mem_centralizer_iff, hy1]
      rw [this, hEcard]
      norm_num
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hord : orderOf (e ⟨y, hyE⟩) = 3 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
        exact orderOf_eq_prime hy3 hy1
      rw [s7mct_centralizer_card e hyE]
      rcases hCent _ hord with h | h <;> rw [h] <;> norm_num
  have h4 : 3 ^ 4 ∣ Nat.card ↥(E ⊓ D) := by
    refine Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) ?_
    have : (3 : ℕ) * 3 ^ 4 = 3 ^ 5 := by norm_num
    rw [this]
    exact h3.trans hdvd
  have h125 : 5 ^ 3 ∣ Nat.card ↥(E ⊓ D) := h5 3 (by rw [hEcard]; norm_num)
  have hdiv : 3 ^ 4 * 5 ^ 3 ∣ Nat.card ↥(E ⊓ D) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h125
  have hU : Nat.card ↥((D.subgroupOf E).map e.toMonoidHom) = Nat.card ↥(E ⊓ D) := by
    rw [Subgroup.card_map_of_injective e.injective, s7mct_card_subgroupOf]
  have hUtop := hMax _ (hU ▸ hdiv)
  have hDtop : D.subgroupOf E = ⊤ :=
    Subgroup.map_injective e.injective
      (hUtop.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)
  exact hED (Subgroup.subgroupOf_eq_top.mp hDtop)

theorem s7m_count (hCard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000)
    (hCent : McLThreeCentralizerOrders) (hMax : McLThreeFiveMax) {Q : Type} [Group Q] [Finite Q]
    {E D : Subgroup Q} (hE : IsSpor ↥E .McL) (hED : ¬ E ≤ D)
    (h5 : ∀ k : ℕ, 5 ^ k ∣ Nat.card E → 5 ^ k ∣ Nat.card ↥(E ⊓ D)) {y : Q} (hyE : y ∈ E)
    (hy3 : y ^ 3 = 1)
    (hdvd : Nat.card ↥(E ⊓ Subgroup.centralizer ({y} : Set Q)) ∣ 3 * Nat.card ↥(E ⊓ D)) :
    False := by
  obtain ⟨e⟩ := hE
  have hCard' : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 := hCard
  have hCent' : ∀ x : CFSG.Blueprint.NativeSporadic.Carrier .McL, orderOf x = 3 →
      Nat.card (Subgroup.centralizer ({x} : Set (CFSG.Blueprint.NativeSporadic.Carrier .McL))) =
          29160 ∨
        Nat.card (Subgroup.centralizer ({x} : Set (CFSG.Blueprint.NativeSporadic.Carrier .McL))) =
          972 := hCent
  have hMax' : ∀ U : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .McL),
      3 ^ 4 * 5 ^ 3 ∣ Nat.card U → U = ⊤ := hMax
  exact s7mct_main e hCard' hCent' hMax' hED h5 hyE hy3 hdvd

private theorem s7m_fixed_mem {G : Type} [Group G] [Finite G] {H Z : Subgroup G} {z : G}
    (hzN : z ∈ Subgroup.normalizer (H : Set G)) (hZz : Subgroup.zpowers z = Z) {h : ↥H}
    (hh : h ∈ MonoidHom.eqLocus (Subgroup.normalizerMonoidHom H ⟨z, hzN⟩).toMonoidHom
      (MonoidHom.id ↥H)) :
    (h : G) ∈ Subgroup.centralizer (Z : Set G) := by
  have hh' : z * (h : G) * z⁻¹ = (h : G) := congrArg Subtype.val hh
  have hc : Commute z (h : G) := by
    calc z * (h : G) = (z * (h : G) * z⁻¹) * z := by group
      _ = (h : G) * z := by rw [hh']
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [← hZz] at hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact (hc.zpow_left k).eq

theorem s7_theoremM (hSimp : IsSimpleGroup CFSG.Blueprint.NativeSporadic.McL)
    (hCard : Nat.card CFSG.Blueprint.NativeSporadic.McL = 898128000)
    (hOut : Nat.card (Outer CFSG.Blueprint.NativeSporadic.McL) ≤ 2)
    (hMult : ∀ {Q : Type} [Group Q], Group.IsPerfect Q →
      (Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.McL) →
        Nat.card (Subgroup.center Q) ∣ 3)
    (hCent : McLThreeCentralizerOrders) (hMax : McLThreeFiveMax)
    {G : Type} [Group G] [Finite G] (M H Z : Subgroup G)
    (hM : ∀ X : Subgroup G, X ≤ M → X ≠ ⊥ → IsPGroup 5 X →
      Subgroup.normalizer (X : Set G) ≤ M)
    (hHM : ¬ H ≤ M) (hrk : 2 ≤ CFSG.Open.pRank 5 (H ⊓ M))
    (E : Subgroup (↥H ⧸ CFSG.pPrimeCore 5 ↥H)) (hEn : E.Normal)
    (hE5 : ∀ x : ↥H ⧸ CFSG.pPrimeCore 5 ↥H, IsPGroup 5 (Subgroup.zpowers x) → x ∈ E)
    (hE : IsSpor ↥E .McL) (h3 : CFSG.Open.pRank 3 M ≤ 3)
    (hodd : Odd (Nat.card (CFSG.pPrimeCore 5 ↥H))) (hZ : Nat.card Z = 3)
    (hZH : Z ≤ Subgroup.normalizer (H : Set G))
    (hCZ : Subgroup.centralizer (Z : Set G) ≤ M) : False := by
  set K : Subgroup ↥H := CFSG.pPrimeCore 5 ↥H with hKdef
  have hKM : K.map H.subtype ≤ M := s7m_core_le hM hrk
  obtain ⟨hED, h5⟩ := s7m_image hM hHM hrk hKM hEn hE5
  have hKs : Group.IsSolvable ↥K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hK3 : CFSG.Open.pRank 3 K ≤ 3 := by
    have h1 := CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three
      H.subtype H.subtype_injective K
    have h2 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hKM
    omega
  obtain ⟨J, hJc, hJ, hJE⟩ := s7m_perfect hSimp hCard hEn hE5 hE
  have hJK := s7m_layer hSimp hCard hKs hK3 hJ hJE hE
  have : Nontrivial ↥Z := Finite.one_lt_card_iff_nontrivial.mp (by rw [hZ]; norm_num)
  obtain ⟨⟨z, hzZ⟩, hz1'⟩ := exists_ne (1 : ↥Z)
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hzZ⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hZz : Subgroup.zpowers z = Z :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ)
      (by rw [Nat.card_zpowers, hzo, hZ])
  have hzN : z ∈ Subgroup.normalizer (H : Set G) := hZH hzZ
  set φ : MulAut ↥H := Subgroup.normalizerMonoidHom H ⟨z, hzN⟩ with hφdef
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (H : Set G))) ^ 3 = 1 := Subtype.ext hz3
    rw [hφdef, ← map_pow, h1, map_one]
  have hφK : K.map φ.toMonoidHom = K :=
    Subgroup.characteristic_iff_map_eq.mp (inferInstance : K.Characteristic) φ
  have hφJ : J.map φ.toMonoidHom = J := Subgroup.characteristic_iff_map_eq.mp hJc φ
  obtain ⟨x, hxJ, hx3, hag, hZJ⟩ :=
    s7m_quasi hSimp hCard hOut hMult hJ hJE hE hJK φ hφ3 hφK hφJ
  have hdvd := s7m_fix hJE hJK φ hφ3 hφK hxJ hag hZJ
  have hfix : (MonoidHom.eqLocus φ.toMonoidHom (MonoidHom.id ↥H)).map (QuotientGroup.mk' K) ≤
      (M.subgroupOf H).map (QuotientGroup.mk' K) := by
    refine Subgroup.map_mono fun h hh => ?_
    rw [Subgroup.mem_subgroupOf]
    exact hCZ (s7m_fixed_mem hzN hZz hh)
  have hyE : QuotientGroup.mk' K x ∈ E := hJE ▸ Subgroup.mem_map_of_mem _ hxJ
  have hy3 : (QuotientGroup.mk' K x) ^ 3 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hx3
  exact s7m_count hCard hCent hMax hE hED h5 hyE hy3
    (hdvd.trans (mul_dvd_mul_left 3 (Subgroup.card_dvd_of_le (inf_le_inf_left E hfix))))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
