module

public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LieType.Chevalley.TorusCoordinates
public import CFSG.LieType.Chevalley.EvenTrialityTorusCoordinates
public import CFSG.LieType.Chevalley.GraphFixedParameterFields
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank

theorem two_le_pRank_of_injective_prod {A B G : Type*} [Group A] [Group B] [Group G]
    [Finite A] [Finite B] [Finite G] {r : ℕ} (hr : r.Prime) (hA : r ∣ Nat.card A)
    (hB : r ∣ Nat.card B) (φ : A × B →* G) (hφ : Function.Injective φ) :
    2 ≤ CFSG.pRank r G := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' r hA
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hB
  let X := Subgroup.zpowers a
  let Y := Subgroup.zpowers b
  let f : X × Y →* G := φ.comp (MonoidHom.prodMap X.subtype Y.subtype)
  have hf : Function.Injective f := fun p q h => by
    have h' := hφ h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h')) (Subtype.ext (congrArg Prod.snd h'))
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.le_pRank_of_injective hr.one_lt ?_ ?_ ?_ f hf le_top
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.1 hu'
    obtain ⟨n', rfl⟩ := Subgroup.mem_zpowers_iff.1 hv'
    exact Prod.ext (Subtype.ext (Commute.zpow_zpow_self a m m').eq)
      (Subtype.ext (Commute.zpow_zpow_self b n n').eq)
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    have ha' : a ^ r = 1 := ha ▸ pow_orderOf_eq_one a
    have hb' : b ^ r = 1 := hb ▸ pow_orderOf_eq_one b
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change (a ^ m) ^ r = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha', one_zpow]
    · change (b ^ n) ^ r = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb', one_zpow]
  · rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ha, hb, sq]

theorem exists_odd_prime_dvd_two_pow_sub_one {f : ℕ} (hf : 2 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 := by
  have h4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ f - 1) (by omega)
  refine ⟨r, hr, fun h2 => ?_, hrd⟩
  subst h2
  have hev : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hodd : Odd (2 ^ f - 1) := Nat.Even.sub_odd (by omega) hev odd_one
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)

theorem exists_two_le_pRank_of_G2_even {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : UntwistedChevalleyModel S .G2 (2 ^ f)) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted h
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one hf
  obtain ⟨eT, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  have hTle : torusGroup .G2 K ≤ adjointGroup .G2 K := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, u⟩, rfl⟩
    exact torusElt_mem_adjointGroup i u
  let g : Kˣ × Kˣ →* (Fin Tag.G2.rank → Kˣ) :=
    { toFun := fun p i => if (i : ℕ) = 0 then p.1 else p.2
      map_one' := by
        funext i
        simp
      map_mul' := fun p q => by
        funext i
        simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
        split_ifs <;> rfl }
  have hg : Function.Injective g := fun p q hpq => by
    have h0 := congrFun hpq ⟨0, by decide⟩
    have h1 := congrFun hpq ⟨1, by decide⟩
    simp only [g, MonoidHom.coe_mk, OneHom.coe_mk] at h0 h1
    exact Prod.ext (by simpa using h0) (by simpa using h1)
  let φ : Kˣ × Kˣ →* S :=
    e.toMonoidHom.comp ((Subgroup.inclusion hTle).comp (eT.toMonoidHom.comp g))
  have hφ : Function.Injective φ :=
    e.injective.comp ((Subgroup.inclusion_injective hTle).comp (eT.injective.comp hg))
  have hcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrd
  exact ⟨r, hr, hr2, two_le_pRank_of_injective_prod hr hcard hcard φ hφ⟩

theorem exists_two_le_pRank_of_trialityD4_even {S : Type} [Group S] [Finite S] {f : ℕ}
    (hf : 2 ≤ f) (h : TwistedChevalleyModel S .D4 (2 ^ f)) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 2 ≤ CFSG.pRank r S := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted (by omega) h
  have : CharP K 2 := charP_two_of_natCard (by rw [hK, ← pow_mul])
  have h3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    have := Fintype.ofFinite K
    have hord : TwistTag.D4.order = 3 := rfl
    have hc : Fintype.card K = 2 ^ f * (2 ^ f * 2 ^ f) := by
      rw [← Nat.card_eq_fintype_card, hK, hord]
      ring
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul, ← hc, FiniteField.pow_card]
  let σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ3 : σ' ^ 3 = 1 := RingEquiv.ext fun c => h3 c
  obtain ⟨-, ⟨eT, -⟩, -⟩ := even_triality_faithful_torus_coordinates K σ' hσ3
  obtain ⟨-, -, -, -, -, k₀, hk₀, hk₀card, -⟩ :=
    finite_graph_field_parameter_fields .D4 Nat.prime_two (by omega : 1 ≤ f) K hK
  have hkk : trialityFixedField K σ'.toRingHom = k₀ := SetLike.coe_injective (by
    rw [hk₀]
    ext c
    change σ c = c ↔ c ^ 2 ^ f = c
    rw [hσ])
  have hk : Nat.card (trialityFixedField K σ'.toRingHom) = 2 ^ f := by rw [hkk, hk₀card]
  obtain ⟨r, hr, hr2, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one hf
  have hcardk : r ∣ Nat.card (trialityFixedField K σ'.toRingHom)ˣ := by
    rw [Nat.card_units, hk]
    exact hrd
  have hcardK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hrd.trans (by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 _)
  let e' : graphFixedRootGroup .D4 K σ'.toRingHom ≃* S := e
  let φ : Kˣ × (trialityFixedField K σ'.toRingHom)ˣ →* S :=
    e'.toMonoidHom.comp ((Subgroup.inclusion (graphFixedRootTorus_le .D4 K σ'.toRingHom)).comp
      eT.toMonoidHom)
  have hφ : Function.Injective φ :=
    e'.injective.comp ((Subgroup.inclusion_injective
      (graphFixedRootTorus_le .D4 K σ'.toRingHom)).comp eT.injective)
  exact ⟨r, hr, hr2, two_le_pRank_of_injective_prod hr hcardK hcardk φ hφ⟩

theorem odd_rank_one_Chevalley_exceptional_model_is_binary_triality (S : Type) [Group S]
    [Finite S] (hS : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r S ≤ 1) (t : StatedLieTag)
    (p f : ℕ) (h : ChevalleyExceptionalModel S t p f) : t = .trialityD4 ∧ p = 2 ∧ f = 1 := by
  have hS' : ∀ r, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup S) ≤ 1 := fun r hr hr2 => by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hS r hr hr2
  have hex : ∀ r : ℕ, r.Prime → r ≠ 2 → 2 ≤ CFSG.pRank r S → False := fun r hr hr2 h2 => by
    have := hS r hr hr2
    omega
  have h3 := hS' 3 Nat.prime_three (by norm_num)
  obtain ⟨⟨hp, hf, hadm⟩, hm⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp2 : p = 2
  · subst hp2
    cases t
    case G2 =>
      exfalso
      obtain ⟨-, hq⟩ := hadm
      have hf2 : 2 ≤ f := by
        by_contra hlt
        obtain rfl : f = 1 := by omega
        norm_num at hq
      obtain ⟨r, hr, hr2, h2⟩ := exists_two_le_pRank_of_G2_even hf2 hm
      exact hex r hr hr2 h2
    case F4 =>
      have := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two (Or.inl rfl) hm
      omega
    case E6 =>
      have := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two
        (Or.inr (Or.inl rfl)) hm
      omega
    case E7 =>
      have := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two
        (Or.inr (Or.inr (Or.inl rfl))) hm
      omega
    case E8 =>
      have := CFSG.SectionRank.four_le_pRank_three_of_untwistedModel_two
        (Or.inr (Or.inr (Or.inr rfl))) hm
      omega
    case twistedE6 =>
      have := CFSG.SectionRank.four_le_pRank_three_of_twistedE6Model_two hf hm
      omega
    case trialityD4 =>
      refine ⟨rfl, rfl, ?_⟩
      by_contra hf1
      obtain ⟨r, hr, hr2, h2⟩ := exists_two_le_pRank_of_trialityD4_even (by omega) hm
      exact (hex r hr hr2 h2).elim
    all_goals exact (hm : False).elim
  · exfalso
    have hpr := hS' p hp hp2
    cases t
    case G2 =>
      have := CFSG.SectionRank.three_mul_le_pRank_of_G2Model hm
      omega
    case F4 =>
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (Or.inl rfl) hm
      omega
    case E6 =>
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (Or.inr (Or.inl rfl)) hm
      omega
    case E7 =>
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel
        (Or.inr (Or.inr (Or.inl rfl))) hm
      omega
    case E8 =>
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel
        (Or.inr (Or.inr (Or.inr rfl))) hm
      omega
    case twistedE6 =>
      have := CFSG.SectionRank.four_le_pRank_of_twistedE6Model hf hm
      omega
    case trialityD4 =>
      have := CFSG.SectionRank.four_le_pRank_of_trialityD4Model hf hm
      omega
    all_goals exact (hm : False).elim

end CFSG.RankThree.Chevalley
