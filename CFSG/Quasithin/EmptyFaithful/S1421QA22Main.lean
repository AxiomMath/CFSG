module

public import CFSG.Quasithin.EmptyFaithful.S1421QA22Rows
public import CFSG.Quasithin.EmptyFaithful.S1421QA22Ord
public import CFSG.Quasithin.EmptyFaithful.S1421QA22Bender
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112A5
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Split
public import CFSG.Quasithin.EmptyFaithful.S1421QA22Setup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Quasithin.R3c7

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

structure Core3Setup (c : Core3Ctx T M H K1 L M₁) (z : G) : Prop where
  center_eq : Subgroup.center ↥L = CFSG.pCore 2 ↥L
  simple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)
  mem : z ∈ quasithinOmegaOneCenter T
  sq : z ^ 2 = 1
  comm : ⁅L, Subgroup.zpowers z⁆ = L
  cases : Lemma115Cases L z
  quasi : CFSG.IsQuasisimple ↥L

namespace Core3Setup

variable {c : Core3Ctx T M H K1 L M₁} {z : G}

theorem ordClass (s : Core3Setup c z) (hO : Lemma115OrdClass) :
    OrdClass (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  have h := hO ↥L s.quasi (lemma115Type_of_cases s.cases)
  rwa [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq s.center_eq).toEquiv] at h

theorem center_quot_eq_bot (s : Core3Setup c z) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  have := s.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := s.quasi.2.2
    let e := QuotientGroup.quotientMulEquivOfEq s.center_eq
    apply hab
    have h1 := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (e b)) (e a)
    apply e.injective
    simpa using h1

theorem exists_inv (s : Core3Setup c z) (h5 : 5 ∣ Nat.card ↥(modO2Image L K1)) :
    ∃ t : ↥L ⧸ CFSG.pCore 2 ↥L, t ≠ 1 ∧ t * t = 1 ∧ ∀ g ∈ modO2Image L K1, g * t = t * g :=
  c.exists_inv_of_five_dvd s.center_eq s.mem s.sq s.comm s.cases h5

theorem false_of_l3 (s : Core3Setup c z) (hL3 : L3InvCentSolvable) {n : ℕ} (hn : 2 ≤ n)
    (hX : IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsSL3 (2 ^ n) (↥L ⧸ CFSG.pCore 2 ↥L)) : False :=
  c.false_of_l3 hL3 s.center_eq s.mem s.sq s.comm s.cases hn hX

theorem false_of_alt7 (s : Core3Setup c z) (h5 : 5 ∣ Nat.card ↥(modO2Image L K1))
    (hX : IsAlt 7 (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  obtain ⟨e⟩ := hX
  obtain ⟨t, ht1, ht2, hcomm⟩ := s.exists_inv h5
  obtain ⟨g, hgJ, hg⟩ := exists_mem_orderOf_five h5
  have hgt : e t * e g = e g * e t := by
    rw [← map_mul, ← map_mul, (hcomm g hgJ).symm]
  refine Alt7.false_of_alt7_inner ?_ ?_ ?_ hgt
  · intro h
    exact ht1 (e.injective (by rw [h, map_one]))
  · rw [← map_mul, ht2, map_one]
  · rw [MulEquiv.orderOf_eq]
    exact hg

theorem false_of_m22 (s : Core3Setup c z) (hM22 : M22InvFiveFree)
    (h5 : 5 ∣ Nat.card ↥(modO2Image L K1)) (hX : IsSporadic .M22 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    False := by
  obtain ⟨t, ht1, ht2, hcomm⟩ := s.exists_inv h5
  obtain ⟨g, hgJ, hg⟩ := exists_mem_orderOf_five h5
  exact hM22 _ hX t g ht1 ht2 hg (hcomm g hgJ).symm

theorem false_of_m23 (s : Core3Setup c z) (hM23 : M23InvFiveFree)
    (h5 : 5 ∣ Nat.card ↥(modO2Image L K1)) (hX : IsSporadic .M23 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    False := by
  obtain ⟨t, ht1, ht2, hcomm⟩ := s.exists_inv h5
  obtain ⟨g, hgJ, hg⟩ := exists_mem_orderOf_five h5
  exact hM23 _ hX t g ht1 ht2 hg (hcomm g hgJ).symm

theorem false_of_j1 (s : Core3Setup c z) (hO : Lemma115OrdClass)
    (hX : IsSporadic .J1 (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  obtain ⟨e⟩ := hX
  have hc := s.ordClass hO
  have hN : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  rw [hN] at hc
  exact not_ordClass_175560 hc

theorem false_of_l2p (s : Core3Setup c z) (hO : Lemma115OrdClass) {p : ℕ} (hp : p.Prime)
    (h5 : p % 5 = 1 ∨ p % 5 = 4) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (hX : IsPSL 2 p 1 (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  have hc := s.ordClass hO
  obtain ⟨-, -, -, hN⟩ := R3c6.psl2Data hX
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 :=
    Nat.gcd_eq_left (by
      rw [pow_one]
      exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
  rw [hg, pow_one] at hN
  exact hc.false_of_l2p_three hp h5 h8 hN

theorem false_of_l2sq (s : Core3Setup c z) (hO : Lemma115OrdClass)
    (hX : IsPSL 2 5 2 (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  have hc := s.ordClass hO
  obtain ⟨-, -, -, hN⟩ := R3c6.psl2Data hX
  have hg : Nat.gcd 2 (5 ^ 2 - 1) = 2 := by norm_num
  rw [hg] at hN
  have h7800 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 7800 := by norm_num at hN; omega
  rw [h7800] at hc
  exact not_ordClass_7800 hc

omit [Finite G] in
theorem card_quot_center_eq {Y : Type} [Group Y] (h : Subgroup.center Y = ⊥) :
    Nat.card (Y ⧸ Subgroup.center Y) = Nat.card Y :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).toEquiv

omit [Finite G] in
theorem card_quot_sl35 {X : Type} [Group X] (h : IsSL3 5 X) :
    Nat.card (X ⧸ Subgroup.center X) = 372000 := by
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := h
  let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
    eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
  let e₂ : X ⧸ Subgroup.center X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
  rw [Nat.card_congr (e₂.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK]
  decide

omit [Finite G] in
theorem card_psu35 {K : Type} [Field K] (hK : Nat.card K = 5 ^ 2) :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K)) =
      126000 := by
  have hK' : Nat.card K = (5 ^ 1) ^ 2 := by rw [hK]; norm_num
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_five le_rfl hK'
    (n := 3) (by norm_num)
  have e : Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K)) =
      Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (5 ^ 1) K)) := rfl
  rw [e, h]
  decide

omit [Finite G] in
theorem card_quot_su35 {X : Type} [Group X] (h : IsSU3 5 X) :
    Nat.card (X ⧸ Subgroup.center X) = 126000 := by
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hK' : Nat.card K = (5 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hZ : Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 5 K) =
      (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K).subgroupOf
        (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 5) (f := 1)
      hK' le_rfl (by norm_num)).2
  let e₂ : X ⧸ Subgroup.center X ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K) :=
    QuotientGroup.congr _ _ eK (by rw [Subgroup.map_center_eq eK, hZ])
  rw [Nat.card_congr e₂.toEquiv, card_psu35 hK]

theorem false_of_sl3five (s : Core3Setup c z) (hO : Lemma115OrdClass) (b : Bool)
    (hX : IsSLEps3 b 5 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSLEps3 b 5 1 (↥L ⧸ CFSG.pCore 2 ↥L)) :
    False := by
  have hc := s.ordClass hO
  have hZ := s.center_quot_eq_bot
  cases b
  · rcases hX with hX | hX
    · have hq : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 126000 := by
        rw [← card_quot_center_eq hZ]
        exact card_quot_su35 hX
      rw [hq] at hc
      exact not_ordClass_126000 hc
    · obtain ⟨-, -, -, -, hN⟩ := R3c6.psu3Data hX
      simp only [pow_one] at hN
      exact hc.false_of_oddLike (oddLike_of_su3 (by norm_num) le_rfl rfl hN)
  · rcases hX with hX | hX
    · have hq : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 372000 := by
        rw [← card_quot_center_eq hZ]
        exact card_quot_sl35 hX
      rw [hq] at hc
      exact not_ordClass_372000 hc
    · obtain ⟨-, -, -, -, hN⟩ := R3c6.psl3Data hX
      simp only [pow_one] at hN
      exact hc.false_of_oddLike (oddLike_of_sl3 (by norm_num) le_rfl rfl hN)

theorem false_of_isHat (s : Core3Setup c z) {S : Type} [Group S]
    (h : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) S) : False := by
  have h3 := h.2.1
  rw [s.center_quot_eq_bot, Subgroup.card_bot] at h3
  omega

omit [Finite G] in
theorem false_of_simple_sl2 {X : Type} [Group X] [IsSimpleGroup X] (F : Subgroup X) [F.Normal]
    {p : ℕ} [Fact (2 < p)] (e : X ⧸ F ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) : False := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F with h | h
  · have e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)).trans e
    exact H13.not_isSimpleGroup_sl2 (p := p) (e'.isSimpleGroup_congr.mp inferInstance)
  · have : Subsingleton (X ⧸ F) := by
      rw [h]
      exact QuotientGroup.subsingleton_quotient_top
    have := H13.nontrivial_sl2 (p := p)
    have h1 : Subsingleton (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
      e.toEquiv.symm.subsingleton
    exact not_subsingleton _ h1

theorem false_of_case4 (s : Core3Setup c z) (h : A36Case4 (↥L ⧸ CFSG.pCore 2 ↥L)) : False := by
  have := s.simple
  obtain ⟨-, -, ⟨e⟩, -⟩ := h
  have : Fact (2 < 5) := ⟨by norm_num⟩
  exact false_of_simple_sl2 _ e

theorem false_of_natural (s : Core3Setup c z) {p : ℕ} (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (hN : NaturalSL2Action p (↥L ⧸ CFSG.pCore 2 ↥L)
      (CFSG.fittingSubgroup (↥L ⧸ CFSG.pCore 2 ↥L))) : False := by
  have := s.simple
  obtain ⟨-, ψ, hψ, hker, -⟩ := hN
  have : Fact (2 < p) := ⟨by omega⟩
  exact false_of_simple_sl2 _
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ))

end Core3Setup

end S1421

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint in
theorem core3QuasiList_of_inputs
    (hM : Vol2.Ch11.SecB.FactMathieuOrders) (hP : Vol2.Ch11.SecA.FactL2Parabolic)
    (h36 : A36ForSQTK) (h312 : A312ForSQTK) (h37 : A37ForSQTK) (hl : Lemma115_3_List)
    (hO : Lemma115OrdClass) (hL3 : L3InvCentSolvable) (hM22 : M22InvFiveFree)
    (hM23 : M23InvFiveFree) : Core3QuasiList := by
  intro G _ _ T M H K1 L M₁ c hq
  obtain ⟨z, hz, hz1, hz2, hzc, h115, hodd⟩ := c.exists_z
  have hsimpleG : IsSimpleGroup G := c.st.hyp.simple
  have hqtke : QTKECore G := qtkeCore_of_cat c.st.hyp.nonabelian c.st.hyp.qtke
  obtain ⟨-, hLz, -, hcases⟩ := Lemma115_3_List.component_cases hl c.st.hyp.simple
    c.st.hyp.nonabelian hqtke h115 (Id2519.isComponentIn_of_mem_cComp c.mem hq)
  have s : S1421.Core3Setup c z := ⟨c.center_eq_pCore hq hodd, c.isSimpleGroup_quot hq hodd, hz,
    hz2, hLz, hcases, hq⟩
  rcases c.bender_cases hM hP h36 h312 h37 with ⟨n, hn, hK, hconc⟩ | ⟨f, hf, hf3, hF4⟩
  · rcases hconc with h2 | ⟨hn2, h3⟩
    · rcases h2 with hsl | hpsl | hsp | hg2 | hf4 | hd4 | ⟨h3d, hd4'⟩
      · exact (s.false_of_l3 hL3 hn (Or.inr hsl)).elim
      · exact (s.false_of_l3 hL3 hn (Or.inl hpsl)).elim
      · exact Or.inl (Or.inl ⟨n, hn, hsp⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨n, hn, hg2⟩))
      · obtain ⟨-, -, -, -, hodd', h3'⟩ := hf4.1
        exact Or.inl (Or.inr (Or.inr (Or.inr ⟨n, hodd', h3', hf4⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨n, hn, hd4⟩)))
      · rcases Nat.lt_or_ge (n / 3) 2 with h1 | h1
        · have h31 : n / 3 = 1 := by
            obtain ⟨k, hk⟩ := h3d
            omega
          rw [h31] at hd4'
          exact Or.inr (Or.inl hd4')
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨n / 3, h1, hd4'⟩)))
    · subst hn2
      have h5 : 5 ∣ Nat.card ↥(modO2Image L K1) := c.five_dvd_card_modO2Image hK
      rcases h3 with hA7 | hH7 | ⟨p, hp, h5', h8', hpsl⟩ | h25 | ⟨b, hsl⟩ | hm22 | hhm22 | hm23 |
          hj1 | hj2 | hj4 | hhs | hru | hc4 | ⟨p, hp, h5', h8', -, -, hnat⟩
      · exact (s.false_of_alt7 h5 hA7).elim
      · exact (s.false_of_isHat hH7).elim
      · exact (s.false_of_l2p hO hp h5' h8' hpsl).elim
      · exact (s.false_of_l2sq hO h25).elim
      · exact (s.false_of_sl3five hO b hsl).elim
      · exact (s.false_of_m22 hM22 h5 hm22).elim
      · exact (s.false_of_isHat hhm22).elim
      · exact (s.false_of_m23 hM23 h5 hm23).elim
      · exact (s.false_of_j1 hO hj1).elim
      · exact Or.inr (Or.inr ⟨.J2, Or.inl rfl, hj2⟩)
      · exact Or.inr (Or.inr ⟨.J4, Or.inr (Or.inl rfl), hj4⟩)
      · exact Or.inr (Or.inr ⟨.HS, Or.inr (Or.inr (Or.inl rfl)), hhs⟩)
      · exact Or.inr (Or.inr ⟨.Ru, Or.inr (Or.inr (Or.inr rfl)), hru⟩)
      · exact (s.false_of_case4 hc4).elim
      · exact (s.false_of_natural h8' hnat).elim
  · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨f, hf, hf3, hF4⟩)))

end CFSG.Quasithin
