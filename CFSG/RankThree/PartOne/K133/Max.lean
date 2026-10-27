module

public import CFSG.RankThree.PartOne.K133.Residue
public import CFSG.RankThree.PartOne.K133.DXFix
import CFSG.RankThree.PartOne.S12.Sec1320
import CFSG.RankThree.PartOne.S10.SectionTenNodesUnconditional
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents
import CFSG.RankThree.PartOne.S12.Sec125Moved

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem eq_zpowers_of_isCyclic [Finite G] {p : ℕ} (hp : p.Prime) {D : Subgroup G} {b : G}
    (hbD : b ∈ D) (hb1 : b ≠ 1) (hpow : ∀ x ∈ D, x ^ p = 1) (hcyc : IsCyclic ↥D) :
    D = Subgroup.zpowers b := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hDg : D = Subgroup.zpowers (g : G) := by
    refine le_antisymm (fun x hx => ?_) (Subgroup.zpowers_le.2 g.2)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨n, congrArg Subtype.val hn⟩
  have hbg : b ∈ Subgroup.zpowers (g : G) := hDg ▸ hbD
  have hg1 : (g : G) ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot] at hbg
    exact hb1 (Subgroup.mem_bot.1 hbg)
  have hgp : (g : G) ^ p = 1 := hpow g g.2
  have hbp : b ^ p = 1 := hpow b hbD
  have hgord : orderOf (g : G) = p := orderOf_eq_prime hgp hg1
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hbD) ?_
  rw [hDg, Nat.card_zpowers, Nat.card_zpowers, hgord, hbord]

theorem exists_two_subgroup_of_even [Finite G] {K : Subgroup G} (hK : Even (Nat.card K)) :
    ∃ S : Subgroup G, S ≤ K ∧ S ≠ ⊥ ∧ IsPGroup 2 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2 (even_iff_two_dvd.1 hK)
  have hxo : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  refine ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.2 x.2, ?_, ?_⟩
  · intro hbot
    have h1 : (x : G) ∈ Subgroup.zpowers (x : G) := Subgroup.mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hxo
    omega
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; norm_num)

theorem card_autFixedInG {p : ℕ} {E : Subgroup G} {t : MulAut E} (hp : p.Prime)
    (hE : IsElementaryAbelian p E) (hcard : Nat.card E = p ^ 4)
    (hrefl : E = autFixedInG E t ⊔ autMovedInG E t ∧ autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧
      Nat.card ↥(autMovedInG E t) = p) : Nat.card ↥(autFixedInG E t) = p ^ 3 := by
  obtain ⟨hsup, hdisj, hM⟩ := hrefl
  have hCE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hME : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hcomm : ∀ x ∈ autFixedInG E t, ∀ y ∈ autMovedInG E t, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hCE hx⟩ ⟨y, hME hy⟩)
  have h1 := card_sup_of_commute_disjoint hcomm hdisj
  rw [← hsup, hcard, hM] at h1
  have hp0 : 0 < p := hp.pos
  have : p ^ 3 * p = Nat.card ↥(autFixedInG E t) * p := by
    rw [← h1]
    ring
  exact (Nat.eq_of_mul_eq_mul_right hp0 this).symm

theorem autFixedInG_mem_admissible [Finite G] {p : ℕ} {E : Subgroup G} {t : MulAut E}
    {K : Subgroup G} (hE : IsElementaryAbelian p E) (hcardC : Nat.card ↥(autFixedInG E t) = p ^ 3)
    (hCK : autFixedInG E t ≤ Subgroup.centralizer (K : Set G)) (hKeven : Even (Nat.card K)) :
    autFixedInG E t ∈ admissibleTriples p E := by
  obtain ⟨S, hSK, hS1, hS2⟩ := exists_two_subgroup_of_even hKeven
  refine ⟨Subgroup.map_subtype_le _, isElementaryAbelian_of_le hE (Subgroup.map_subtype_le _),
    hcardC, S, hS1, hS2, ?_⟩
  have h1 : autFixedInG E t ≤ Subgroup.centralizer (S : Set G) :=
    hCK.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hSK))
  exact h1.trans (Subgroup.centralizer_le_normalizer _)

theorem sectionTenSetup_of_admissible [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) {B : Subgroup G} (hB : B ∈ admissibleTriples p E) :
    SteinbergBM.SectionTenSetup G p B := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -, h10⟩ := h.setup
  obtain ⟨-, hBel, hBcard, S, hS1, hS2, hSB⟩ := hB
  exact ⟨h1, h2, h3, h4, h5, h6, hBel, hBcard, ⟨S, hS1, hS2, hSB⟩, h10⟩

theorem mem_thetaQuotientCentralizer_of_le_centralizer {p : ℕ} {A X : Subgroup G} {b : G}
    (hbA : b ∈ A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hbX : X ≤ Subgroup.centralizer ({b} : Set G)) : b ∈ thetaQuotientCentralizer p A X := by
  rw [mem_thetaQuotientCentralizer_iff]
  refine ⟨hbA, hAX hbA, fun k hk => ?_⟩
  have hke : k * b = b * k := Subgroup.mem_centralizer_singleton_iff.1 (hbX hk)
  have : b * k * b⁻¹ * k⁻¹ = 1 := by rw [← hke]; group
  rw [this]
  exact Subgroup.one_mem _

theorem thetaCompE_trans [Finite G] (hS : SchreierFor InCatalog) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) :
    ∀ X ∈ thetaCompE p E, ∀ Y ∈ thetaCompE p E, ∀ Z ∈ thetaCompE p E,
      sectionTenRel p X Y → sectionTenRel p Y Z → sectionTenRel p X Z := by
  have hp := h.prime
  have hp3 := h.three_lt
  have : IsSimpleGroup G := h.setup.1
  have hUsub : thetaCompE p E ⊆ thetaComponentFamily p E := by
    rintro X ⟨B, hBadm, hXB⟩
    obtain ⟨b, hbB, hb1, hXb⟩ := mem_thetaComponentFamily_iff.1 hXB
    exact mem_thetaComponentFamily_iff.2 ⟨b, hBadm.1 hbB, hb1, hXb⟩
  exact fun X hX Y hY Z hZ hXY hYZ =>
    section_ten_component_supplement_transitivity hS G h.setup.2.1 h.setup.2.2.1
      (sectionTenSetup_evenRank_eq h.setup).le p hp hp3 E h.E_elem X (hUsub hX) Y (hUsub hY)
      Z (hUsub hZ) hXY hYZ

theorem thetaQuotientCentralizer_le_autFixedInG [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    {t : MulAut E} {K X : Subgroup G} (hE : IsElementaryAbelian p E) (hcard : Nat.card E = p ^ 4)
    (hcardC : Nat.card ↥(autFixedInG E t) = p ^ 3) (ht1 : t ≠ 1)
    (hKperf : Group.IsPerfect ↥K) (hCK : autFixedInG E t ≤ Subgroup.centralizer (K : Set G))
    (hlift : ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)), k ∈ K ∧
      E.normalizerMonoidHom ⟨k, hk⟩ = t)
    (hKX : K ≤ X)
    (hKθ : K ≤ Subgroup.centralizer (inSubgroup (aschbacherSolvableCore p) X : Set G)) :
    thetaQuotientCentralizer p E X ≤ autFixedInG E t := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro y hy
  by_contra hyC
  obtain ⟨hyE, -, -⟩ := mem_thetaQuotientCentralizer_iff.1 hy
  have hKy : ⁅K, Subgroup.zpowers y⁆ = ⊥ := by
    have hz : ⁅K, Subgroup.zpowers y⁆ ≤ inSubgroup (aschbacherSolvableCore p) X :=
      (Subgroup.commutator_mono hKX le_rfl).trans (commutator_zpowers_le_theta hy)
    have hθK : inSubgroup (aschbacherSolvableCore p) X ≤ Subgroup.centralizer (K : Set G) :=
      fun n hn k hk => (Subgroup.mem_centralizer_iff.1 (hKθ hk) n hn).symm
    have h1 : ⁅⁅K, Subgroup.zpowers y⁆, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hz.trans hθK)
    have h2 : ⁅⁅Subgroup.zpowers y, K⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (Subgroup.zpowers y) K]
      exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [Subgroup.isPerfect_iff.1 hKperf] at h3
  have hKcent : K ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hKy
  have hy1 : y ≠ 1 := fun h1 => hyC (h1 ▸ Subgroup.one_mem _)
  have hyp : y ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) y hyE
  have hyord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hCE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hcommE : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hcard' := card_sup_zpowers hp hyord (fun x hx => hcommE x (hCE hx) y hyE) hyC
  have hEsup : autFixedInG E t ⊔ Subgroup.zpowers y = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hCE (Subgroup.zpowers_le.2 hyE)) ?_
    rw [hcard, hcard', hcardC]
    exact (by ring : p ^ 4 = p ^ 3 * p).le
  have hKE : ∀ k ∈ K, ∀ x ∈ E, x * k = k * x := by
    intro k hk x hx
    have hCc : autFixedInG E t ≤ Subgroup.centralizer ({k} : Set G) := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hCK hu) k hk).symm
    have hyc : Subgroup.zpowers y ≤ Subgroup.centralizer ({k} : Set G) :=
      Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hKcent hk) y (Subgroup.mem_zpowers y)))
    have hEc : E ≤ Subgroup.centralizer ({k} : Set G) := hEsup ▸ sup_le hCc hyc
    exact Subgroup.mem_centralizer_singleton_iff.1 (hEc hx)
  obtain ⟨k, hk, hkK, hkt⟩ := hlift
  apply ht1
  rw [← hkt]
  refine MulEquiv.ext fun a => Subtype.ext ?_
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
  have hak := hKE k hkK a a.2
  rw [← hak, mul_assoc, mul_inv_cancel, mul_one]

@[expose] def KF133ResMax : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A →
    ∀ t ∈ reflectionSet p E, t ∈ torusImage E L → ∀ K : Subgroup G, IsKt p E t K →
    ∀ b ∈ autFixedInG E t, b ≠ 1 → ∀ J ∈ thetaComponentsAt p b, K ≤ J →
      J ∈ thetaCompStarE p E → thetaQuotientCentralizer p E J = Subgroup.zpowers b →
      c ∉ Subgroup.zpowers b →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 3 ∧ J ∈ sectionTenZero p B

theorem kf133TwoNe_of_resMax (hS : SchreierFor InCatalog)
    (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) (hLift : KFLiftAll) (hRes : KF133ResMax) :
    KF133TwoNe := by
  intro G _ _ p A c L E h hF hF13 hT hEA t ht htL K hK e he he1 I hI hKI
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have heE : e ∈ E := (Subgroup.map_subtype_le _) he
  have hEI : E ≤ Subgroup.normalizer (I : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI
  have hpowE : ∀ x ∈ E, x ^ p = 1 := fun x hx => by
    have := h.E_elem
    exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  obtain ⟨-, r, hr1, hr12, hrow, -, hrA, hr9⟩ := hF.three
  have hr9' : 9 ≤ r := by
    by_contra hlt
    exact hEA (hrA (by omega))
  have hcardE : Nat.card E = p ^ 4 := hr9 hr9'
  obtain ⟨f, -, hKR, -⟩ :=
    hTypes r hr9' hr12 G p A c L E h hF hF13 hT hrow hrA hr9 t ht htL K hK
  have hmod : StatedClassicalModel ↥K .PSL 2 2 f := by
    interval_cases r <;> exact hKR
  have hKq : CFSG.IsQuasisimple ↥K := S15K.isQuasisimple_of_model hmod
  have hKeven : Even (Nat.card K) := Sec1320.even_card_of_psl_two hmod
  obtain ⟨-, -, hnotexc, -, k, hk, hkK0, hkt⟩ :=
    hLift G p A c L E h hF hF13 hT (Or.inl hEA) t ht
  have hKeq : K = kZero p E t := hK.2 hnotexc
  have hlift : ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)), k ∈ K ∧
      E.normalizerMonoidHom ⟨k, hk⟩ = t := ⟨k, hk, hKeq ▸ hkK0, hkt⟩
  have hCcard : Nat.card ↥(autFixedInG E t) = p ^ 3 :=
    card_autFixedInG hp h.E_elem hcardE (hF13.reflection t ht)
  have hCK : autFixedInG E t ≤ Subgroup.centralizer (K : Set G) :=
    autFixedInG_le_centralizer_of_isKt hK
  have hCadm : autFixedInG E t ∈ admissibleTriples p E :=
    autFixedInG_mem_admissible h.E_elem hCcard hCK hKeven
  have ht1 : t ≠ 1 := fun h1 => by
    have := ht.1.1
    rw [h1, orderOf_one] at this
    omega
  have hIF : I ∈ thetaComponentFamily p (autFixedInG E t) :=
    mem_thetaComponentFamily_iff.2 ⟨e, he, he1, hI⟩
  have hIU : I ∈ thetaCompE p E := ⟨_, hCadm, hIF⟩
  have htrans := thetaCompE_trans hS h
  have hEK : E ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact S13K.E_le_normalizer_kZero h.E_elem t
  have hθ : ∀ {e' : G} {X : Subgroup G}, X ∈ thetaComponentsAt p e' →
      inSubgroup (aschbacherSolvableCore p) X ≤
        inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e'} : Set G)) :=
    fun hX => by
      rw [theta_eq_inf_of_mem_thetaComponentsAt hp hX]
      exact inf_le_right
  have hKθ : ∀ {e' : G} {X : Subgroup G}, e' ∈ autFixedInG E t → X ∈ thetaComponentsAt p e' →
      K ≤ Subgroup.centralizer ((inSubgroup (aschbacherSolvableCore p) X ⊓
        Subgroup.centralizer (autFixedInG E t : Set G) : Subgroup G) : Set G) :=
    fun he' hX => (S13K.isKt_centralizes_fixed_theta hp hK he').trans
      (Subgroup.centralizer_le (inf_le_inf_right _ (hθ hX)))
  have hCE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hPp : IsPGroup p ↥(autFixedInG E t) := S13K.isPGroup_of_le_elementaryAbelian h.E_elem hCE
  have hKP : K ≤ Subgroup.centralizer (autFixedInG E t : Set G) := S13K.isKt_le_centralizer_fixed hK
  obtain ⟨J, hJU, hIJ, hJmax⟩ := Sec125.exists_maximal_above (sectionTenRel p) (thetaCompE p E)
    (fun a _ => sectionTenRel_refl p a) htrans hIU
  have hJU' := hJU
  obtain ⟨B', hB'adm, hJB'⟩ := hJU
  obtain ⟨b, hbB', hb1, hJb⟩ := mem_thetaComponentFamily_iff.1 hJB'
  have hbE : b ∈ E := hB'adm.1 hbB'
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hbE hJb
  have hKJ : K ≤ J :=
    S13K.le_of_sectionTenRel_fixed hp hKq.1 hKI hIJ hPp (hCE.trans hEI) (hCE.trans hEJ) hKP
      (hKθ he hI)
  have hbD : b ∈ thetaQuotientCentralizer p E I :=
    mem_thetaQuotientCentralizer_of_rel hbE hEI (mem_thetaComponentsAt_iff.1 hJb).1 hIJ
  have hbC : b ∈ autFixedInG E t :=
    thetaQuotientCentralizer_le_autFixedInG_of_quasisimple hp h.E_elem hcardE hCcard ht1 hKq hEK
      hCK hlift hKI hbD
  have hDJ : thetaQuotientCentralizer p E J ≤ autFixedInG E t :=
    thetaQuotientCentralizer_le_autFixedInG_of_quasisimple hp h.E_elem hcardE hCcard ht1 hKq hEK
      hCK hlift hKJ
  have hJC : J ∈ thetaComponentFamily p (autFixedInG E t) :=
    mem_thetaComponentFamily_iff.2 ⟨b, hbC, hb1, hJb⟩
  have hJmaxC : J ∈ sectionTenStar p (autFixedInG E t) :=
    ⟨hJC, fun K' hK' hJK' => hJmax K' ⟨_, hCadm, hK'⟩ hJK'⟩
  obtain ⟨-, hcyc⟩ := section_ten_maximal_component_quotient_actor_kernel_cyclic hS G p
    (autFixedInG E t) (sectionTenSetup_of_admissible h hCadm) J hJmaxC
  have hDJeq : thetaQuotientCentralizer p (autFixedInG E t) J = thetaQuotientCentralizer p E J := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxC, hxN, hxθ⟩ := mem_thetaQuotientCentralizer_iff.1 hx
      exact mem_thetaQuotientCentralizer_iff.2 ⟨(Subgroup.map_subtype_le _) hxC, hxN, hxθ⟩
    · intro hx
      obtain ⟨-, hxN, hxθ⟩ := mem_thetaQuotientCentralizer_iff.1 hx
      exact mem_thetaQuotientCentralizer_iff.2 ⟨hDJ hx, hxN, hxθ⟩
  have hbDE : b ∈ thetaQuotientCentralizer p E J :=
    mem_thetaQuotientCentralizer_of_le_centralizer hbE hEJ (mem_thetaComponentsAt_iff.1 hJb).1
  have hbDC : b ∈ thetaQuotientCentralizer p (autFixedInG E t) J := by
    rw [hDJeq]
    exact hbDE
  have hDJb : thetaQuotientCentralizer p E J = Subgroup.zpowers b := by
    rw [← hDJeq]
    exact eq_zpowers_of_isCyclic hp hbDC hb1
      (fun x hx => hpowE x ((Subgroup.map_subtype_le _)
        (mem_thetaQuotientCentralizer_iff.1 hx).1)) hcyc
  by_cases hcb : c ∈ Subgroup.zpowers b
  ·
    have hcD : c ∈ thetaQuotientCentralizer p E J := by
      rw [hDJb]
      exact hcb
    have hJL : sectionTenRel p J L :=
      sectionTenRel_of_trivial_action_fix hS h hKq.1 (Sec125.ne_bot_of_isQuasisimple hKq)
        (hF13.kt_le L hF13.inZeroStar t ht htL K hK) hb1 hbE hJb hKJ
        hCE hKP (S13K.isKt_centralizes_fixed_theta hp hK hbC) (commutator_zpowers_le_theta hcD)
    exact ⟨L, hF13.inZeroStar, htrans I hIU J hJU' L hF13.inZeroStar.2.1 hIJ hJL⟩
  · obtain ⟨B, hBE, hBcard, hJB⟩ := hRes G p A c L E h hF hF13 hT hEA t ht htL K hK b hbC hb1 J hJb
      hKJ ⟨hJU', hJmax⟩ hDJb hcb
    have hJB' := hJB
    obtain ⟨-, S, -, hS1, hS2, hSB, -⟩ := hJB'
    have hBadm : B ∈ admissibleTriples p E :=
      ⟨hBE, isElementaryAbelian_of_le h.E_elem hBE, hBcard, S, hS1, hS2, hSB⟩
    exact ⟨J, ⟨⟨B, hBadm, hJB⟩, hJU', hJmax⟩, hIJ⟩

end CFSG.RankThree.PartOne.K133
