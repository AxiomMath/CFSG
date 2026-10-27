module

public import CFSG.Quasithin.Vol2.Ch11SecO6S8
public import CFSG.Quasithin.Vol2.Ch11SecO6S7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD.O6S

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecG.Bar
open CFSG.Quasithin.Vol2.Ch11.O6
open scoped MatrixGroups

theorem actsScalar_one_of_mul_inv_mem {X : Type} [Group X] {r : ℕ} {α : MulAut X}
    (h : ∀ d ∈ CFSG.pCore r X, α d * d⁻¹ ∈ frattiniIn (CFSG.pCore r X)) :
    ActsScalar r α 1 := by
  intro d hd
  obtain ⟨c, hc, hce⟩ := h d hd
  have hnor : (frattini ↥(CFSG.pCore r X)).Normal := inferInstance
  refine ⟨(⟨d, hd⟩ : ↥(CFSG.pCore r X))⁻¹ * c * ⟨d, hd⟩, ?_, ?_⟩
  · have := hnor.conj_mem c hc (⟨d, hd⟩ : ↥(CFSG.pCore r X))⁻¹
    simpa using this
  · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, pow_one]
    rw [show ((c : ↥(CFSG.pCore r X)) : X) = α d * d⁻¹ from hce]
    group

section Act


theorem factCase1PrimeAct_holds : FactCase1PrimeAct := by
  intro G _ _ K L₁ n r hlist h1 hKperf hL₁K hperf ⟨F₄, _, _, hF₄, ⟨eL⟩⟩ hr hnle
  obtain ⟨p, hp, hp5', φK, hφKs, hφKk⟩ := h1
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hp5 : 5 ≤ p := by rcases hp5' with h | h <;> omega
  have hp2 : p ≠ 2 := by omega
  obtain ⟨φ, hφs, hφk, -⟩ := exists_kBar_hom hφKs hφKk
  have hn : n = 2 := by
    rcases hlist with h | ⟨h, -⟩
    · exact (false_of_list2 h hp2 hφs).elim
    · exact h
  subst hn
  have hF₄' : Nat.card F₄ = 4 := by rw [hF₄]; norm_num
  have h60 := index_pCore_eq_sixty hF₄' eL
  have hD : Case1Data (KBar K) := case1Data_of_shape (shape_of_lists hlist hp2 hφs)
  have hOF : CFSG.oddCore (KBar K) = CFSG.fittingSubgroup (KBar K) := oddCore_eq hD
  have hKb : ⁅(⊤ : Subgroup (KBar K)), (⊤ : Subgroup (KBar K))⁆ = ⊤ :=
    commutator_top_eq_top hKperf
  have h2p := two_ne_zero_zmod hp5
  have hcard4 : 4 ≤ Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  have hmemF : ∀ x : KBar K, φ x = 1 → x ∈ CFSG.fittingSubgroup (KBar K) := fun x hx => by
    rw [← hOF, ← hφk]
    exact hx
  have hrF := dvd_card_fitting_of_not_le hnle
  have hr2 : r ≠ 2 := by
    have := hD.struct.2.1 r hr hrF
    omega
  have hna := exists_not_triv r hD hrF (Or.inl hKb)
  obtain ⟨s, hsL, hφs1, -, -⟩ := exists_s hp5 hφk hL₁K hperf h60
  obtain ⟨l₀, hl₀⟩ : s ∈ (l1Map hL₁K).range := by
    rw [range_l1Map]
    exact hsL
  have hsF : s ∉ CFSG.fittingSubgroup (KBar K) := fun h => by
    rw [← hOF, ← hφk, MonoidHom.mem_ker, hφs1] at h
    exact neg_one_ne_one h2p h
  have hs2 : s ^ 2 ∈ CFSG.fittingSubgroup (KBar K) :=
    hmemF _ (by rw [map_pow, hφs1, neg_one_sq])
  have hinv : ActsScalar r (MulAut.conj s) (r - 1) := inverts_of_perfect r hD hKb hrF hsF hs2
  refine ⟨fun y hy hyc => ?_, fun a ha hae hcomm x hx => ?_⟩
  ·
    have hy' : y ∈ ((oTwoPrime K r ⊔ L₁ : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (hL₁K.trans (le_normalizer_oTwoPrime K r))] at hy'
    obtain ⟨u, hu, l, hl, rfl⟩ := hy'
    have huK : u ∈ K := oTwoPrime_le K r hu
    have hyK : u * l ∈ K := K.mul_mem huK (hL₁K hl)
    have hu' : ((⟨u, huK⟩ : ↥K) : KBar K) ∈ CFSG.pCore r (KBar K) :=
      (mem_oTwoPrime_iff ⟨u, huK⟩).mp hu
    have hcen : ∀ d ∈ CFSG.pCore r (KBar K),
        MulAut.conj ((⟨u * l, hyK⟩ : ↥K) : KBar K) d = d := by
      intro d hd
      obtain ⟨⟨x, hxK⟩, rfl⟩ := QuotientGroup.mk_surjective d
      have hxO : x ∈ oTwoPrime K r := (mem_oTwoPrime_iff ⟨x, hxK⟩).mpr hd
      rw [MulAut.conj_apply, mk_commute_of_comm_mem hyK hxK (hyc x hxO), mul_inv_cancel_right]
    have hyk : ((⟨u * l, hyK⟩ : ↥K) : KBar K) ∈ (linConj (X := KBar K) r).ker :=
      (mem_ker_linConj r).mpr ((actsTrivially_iff r _).mpr fun d hd => by
        rw [hcen d hd, pow_one, inv_mul_cancel]
        exact one_mem _)
    have huk : ((⟨u, huK⟩ : ↥K) : KBar K) ∈ (linConj (X := KBar K) r).ker :=
      (mem_ker_linConj r).mpr (fitting_acts_triv r (CFSG.pCore_le_fitting _ r hu'))
    have e : ((⟨l, hL₁K hl⟩ : ↥K) : KBar K) =
        ((⟨u, huK⟩ : ↥K) : KBar K)⁻¹ * ((⟨u * l, hyK⟩ : ↥K) : KBar K) := by
      rw [eq_inv_mul_iff_mul_eq, ← QuotientGroup.mk_mul]
      rfl
    have hlk : ((⟨l, hL₁K hl⟩ : ↥K) : KBar K) ∈ (linConj (X := KBar K) r).ker := by
      rw [e]
      exact mul_mem (inv_mem huk) hyk
    have hker : (linConj (X := KBar K) r).ker ≤ CFSG.fittingSubgroup (KBar K) := by
      intro z hz
      by_contra hzF
      have hne : (linConj (X := KBar K) r).ker.map φ ≠ ⊥ := by
        intro hbot
        apply hzF
        apply hmemF
        have : φ z ∈ (linConj (X := KBar K) r).ker.map φ := Subgroup.mem_map_of_mem φ hz
        rwa [hbot, Subgroup.mem_bot] at this
      obtain ⟨n₀, hn₀, hφn₀⟩ := neg_one_mem_of_normal hcard4 h2p
        ((linConj (X := KBar K) r).normal_ker.map φ hφs) hne
      have hsk : s ∈ (linConj (X := KBar K) r).ker := by
        have hf : n₀⁻¹ * s ∈ CFSG.fittingSubgroup (KBar K) :=
          hmemF _ (by rw [map_mul, map_inv, hφn₀, hφs1, inv_mul_cancel])
        have h' := mul_mem hn₀ ((mem_ker_linConj r).mpr (fitting_acts_triv r hf))
        rwa [mul_inv_cancel_left] at h'
      have h1s : ActsScalar r (MulAut.conj s) 1 :=
        (actsTrivially_iff r s).mp ((mem_ker_linConj r).mp hsk)
      obtain ⟨x, w, hxw⟩ := hna
      apply hxw
      intro d hd
      exact mul_mem (inv_mem (le_frattiniIn_of_one_of_neg hr2 h1s hinv hd))
        (le_frattiniIn_of_one_of_neg hr2 h1s hinv
          ((CFSG.pCore_normal).conj_mem _ hd (x * w * x⁻¹ * w⁻¹)))
    have hl1 : ((⟨l, hL₁K hl⟩ : ↥K) : KBar K) = 1 := by
      have h' : ((⟨l, hL₁K hl⟩ : ↥K) : KBar K) ∈ l1Bar K L₁ ⊓ CFSG.oddCore (KBar K) := by
        refine Subgroup.mem_inf.mpr ⟨l1Map_mem hL₁K ⟨l, hl⟩, ?_⟩
        rw [hOF]
        exact hker hlk
      rwa [l1Bar_inf_oddCore hp5 hφk hL₁K hperf h60, Subgroup.mem_bot] at h'
    have hlO : l ∈ pCoreOf 2 K := (mk_eq_one_iff_mem ⟨l, hL₁K hl⟩).mp hl1
    exact (oTwoPrime K r).mul_mem hu (pCoreOf_le_oTwoPrime K r hlO)
  ·
    obtain ⟨e, hae⟩ := hae
    have hαe : (aut K ⟨a, ha⟩) ^ 2 ^ e = 1 := by
      rw [← map_pow]
      have : (⟨a, ha⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ e = 1 :=
        Subtype.ext (by simpa using hae)
      rw [this, map_one]
    have hfr : ∀ d ∈ CFSG.pCore r (KBar K),
        aut K ⟨a, ha⟩ d * d⁻¹ ∈ frattiniIn (CFSG.pCore r (KBar K)) := by
      intro d hd
      obtain ⟨⟨z, hzK⟩, rfl⟩ := QuotientGroup.mk_surjective d
      have hzO : z ∈ oTwoPrime K r := (mem_oTwoPrime_iff ⟨z, hzK⟩).mpr hd
      have hcO : a * z * a⁻¹ * z⁻¹ ∈ oTwoPrime K r :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_oTwoPrime K r ha)
          z).mp hzO) (inv_mem hzO)
      have hcP : ((⟨a * z * a⁻¹ * z⁻¹, commK_mem ha hzK⟩ : ↥K) : KBar K) ∈
          CFSG.pCore r (KBar K) :=
        (mem_oTwoPrime_iff (⟨a * z * a⁻¹ * z⁻¹, commK_mem ha hzK⟩ : ↥K)).mp hcO
      have hcs : MulAut.conj s ((⟨a * z * a⁻¹ * z⁻¹, commK_mem ha hzK⟩ : ↥K) : KBar K) =
          ((⟨a * z * a⁻¹ * z⁻¹, commK_mem ha hzK⟩ : ↥K) : KBar K) := by
        have h1 := mk_commute_of_comm_mem (commK_mem ha hzK) (hL₁K l₀.2)
          (hcomm z hzO l₀ l₀.2)
        rw [← hl₀, l1Map_apply, MulAut.conj_apply, ← h1, mul_inv_cancel_right]
      rw [← mk_commK ha hzK]
      exact mem_frattiniIn_of_neg_of_fix hr2 hinv hcP hcs
    have hfix := fix_of_actsScalar_one r hr2 hαe (actsScalar_one_of_mul_inv_mem hfr)
    have hxK : x ∈ K := oTwoPrime_le K r hx
    have hxP : ((⟨x, hxK⟩ : ↥K) : KBar K) ∈ CFSG.pCore r (KBar K) :=
      (mem_oTwoPrime_iff ⟨x, hxK⟩).mp hx
    have h2 := mk_commK ha hxK
    rw [hfix _ hxP, mul_inv_cancel] at h2
    exact (mk_eq_one_iff_mem _).mp h2

end Act

end CFSG.Quasithin.Vol2.Ch11.SecD.O6S
