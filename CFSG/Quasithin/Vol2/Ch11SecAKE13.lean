module

public import CFSG.Quasithin.Vol2.Ch11SecAKDc
public import CFSG.Quasithin.Background.A318PF4Frame
public import CFSG.LocalAnalysis.SectionRank.LargeRee.Torus
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.TrialityExactFiniteOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.RankThree.PartOne.KLC.TriTorus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KF.G2Sylow
public import CFSG.RankThree.PartOne.KLC.Assembly
public import CFSG.RankThree.PartOne.S11c.Sec66Exc
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.SectionRank.LargeRee

theorem prime_dvd_two_pow_sub_one {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hd : p ∣ 2 ^ f - 1) :
    p ∣ (2 ^ f) ^ 2 + 2 ^ f + 1 ∨ 5 ≤ p := by
  have h2 : 2 ^ f % 2 = 0 := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [pow_succ, Nat.mul_mod_left]
  have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  generalize 2 ^ f = q at h2 h1 hd ⊢
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  by_cases h3 : p = 3
  · subst h3
    left
    have hq : q % 3 = 1 := by omega
    have : (q ^ 2 + q + 1) % 3 = 0 := by
      rw [Nat.add_mod, Nat.add_mod (q ^ 2), Nat.pow_mod, hq]
    omega
  · right
    have := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h h3
    · exact absurd (h ▸ hp) (by norm_num)
    · exact h


section Ree

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem simpleChar_reeTorusHom (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (u : Kˣ) :
    simpleChar ((reeTorusHom a hK fi_zero_mem_longSet u : reeFixed ReeTag.F4 K a) :
        adjointGroup ReeTag.F4.tag K) (fi 0) = ((u ^ (2 : ℤ) : Kˣ) : K) ∧
      simpleChar ((reeTorusHom a hK fi_one_mem_longSet u : reeFixed ReeTag.F4 K a) :
        adjointGroup ReeTag.F4.tag K) (fi 0) = ((u ^ (-1 : ℤ) : Kˣ) : K) := by
  rw [coe_reeTorusHom, coe_reeTorusHom, simpleChar_reeTorus, simpleChar_reeTorus,
    reeExp_zero_zero, reeExp_one_zero]
  exact ⟨rfl, rfl⟩

theorem two_le_pRank_reeFixed (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ Nat.card K - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (reeFixed ReeTag.F4 K a)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [Nat.card_units]; exact hpd)
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    exact hp.one_lt.ne hζ
  set T₀ := reeTorusHom a hK fi_zero_mem_longSet
  set T₁ := reeTorusHom a hK fi_one_mem_longSet
  have hch := simpleChar_reeTorusHom hK
  refine CFSG.QuasithinUnique.Lin2.OddRank.two_le_pRank_of_gens (x := T₀ ζ) (y := T₁ ζ) ?_ ?_ ?_
    ?_ ?_
  · rw [← map_pow, hζp, map_one]
  · rw [← map_pow, hζp, map_one]
  · exact commute_of_mem_reeTorusPart (reeTorusSub_le_reeTorusPart hK _ ⟨ζ, rfl⟩)
      (reeTorusSub_le_reeTorusPart hK _ ⟨ζ, rfl⟩)
  · intro h
    have h1 : simpleChar ((T₀ ζ : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) (fi 0) =
        simpleChar ((T₀ 1 : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) (fi 0) := by
      rw [h, map_one]
    rw [(hch ζ).1, (hch 1).1, one_zpow] at h1
    have h2 : ζ ^ 2 = 1 := by
      have := Units.ext h1
      rwa [zpow_two, ← pow_two] at this
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hζ] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)
  · intro n h
    have hmem : T₁ ζ ∈ reeTorusSub a hK fi_zero_mem_longSet ⊓ reeTorusSub a hK fi_one_mem_longSet :=
      ⟨⟨ζ ^ n, by rw [map_pow]; exact h⟩, ⟨ζ, rfl⟩⟩
    rw [reeTorusSub_inf hK, Subgroup.mem_bot] at hmem
    have h1 : simpleChar ((T₁ ζ : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) (fi 0) =
        simpleChar ((T₁ 1 : reeFixed ReeTag.F4 K a) : adjointGroup ReeTag.F4.tag K) (fi 0) := by
      rw [hmem, map_one]
    rw [(hch ζ).2, (hch 1).2, one_zpow] at h1
    have := Units.ext h1
    rw [zpow_neg_one, inv_eq_one] at this
    exact hζ1 this

end Ree


theorem two_le_pRank_is2F4 {X : Type} [Group X] [Finite X] {f : ℕ} (h : Is2F4 f X) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ f - 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨a, K, _, _, _, -, hfa, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model h
  subst hfa
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have : Finite (reeFixed ReeTag.F4 K a) := Subtype.finite
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
    (e.trans (CFSG.Quasithin.A318P.reeFixedEquivGamma a).symm)]
  exact two_le_pRank_reeFixed hK hp hp2 (by rw [hK]; exact hpd)


theorem two_le_pRank_is3D4 {X : Type} [Group X] [Finite X] {f : ℕ} (h : Is3D4 2 f X) {p : ℕ}
    (hp : p.Prime) (hpd : p ∣ 2 ^ f - 1 ∨ p ∣ (2 ^ f) ^ 2 + 2 ^ f + 1) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model h
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e,
    ← CFSG.SectionRank.pRank_eq_open_pRank_top]
  have h36 : p ∣ (2 ^ f) ^ 2 + 2 ^ f + 1 →
      2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun hd => by
    refine CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi36 hf hK σ hσ (ε := 1)
      (Or.inl rfl) hp ?_
    have := Int.natCast_dvd_natCast.mpr hd
    push_cast at this
    simpa using this
  rcases hpd with hd | hd
  · rcases prime_dvd_two_pow_sub_one hf hp hd with h3 | hp5
    · exact h36 h3
    · exact CFSG.RankThree.PartOne.KLC.two_le_pRank_triality_phi1
        ⟨hp, hp5, hf, hK, fun c => hσ c, hd⟩
  · exact h36 hd

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
