module

public import CFSG.Quasithin.EmptyFaithful.T1515eC
public import CFSG.Quasithin.Background.A3FactsSporadic
public import CFSG.Sporadic.He
public import CFSG.LieType.Simplicity.TrialityD4
public import CFSG.Quasithin.EmptyFaithful.T1515M11U
public import CFSG.Quasithin.EmptyFaithful.T1515M11D4

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Quasithin.A3Facts CFSG.SectionRank

section Sporadic

theorem a318Exclusion_of_isSporadic1515e {s : TauCeti.SporadicName} {N : ℕ}
    (hfin : Finite (NativeSporadic.Carrier s)) (hs : IsSimpleGroup (NativeSporadic.Carrier s))
    (hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier s)))
    (hN : Nat.card (NativeSporadic.Carrier s) = N) (hL : L3Free1515e N 0)
    {X : Type} [Group X] [Finite X] (h : IsSporadic s X) : A318Exclusion X := by
  obtain ⟨e⟩ := h
  refine A318Exclusion.of_card (N := N) (e.isSimpleGroup) ?_ ?_ hL
  · rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  · rw [Nat.card_congr e.toEquiv, hN]

theorem two_le_pRank_M11_1515e [Finite NativeSporadic.M11] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.M11) := by
  set x := mathieuWord m11GenA m11GenB m11WordX.toList
  set y := mathieuWord m11GenA m11GenB m11WordY.toList
  have hx : x ^ 3 = 1 := by decide +kernel
  have hy : y ^ 3 = 1 := by decide +kernel
  have hxy : x * y = y * x := by decide +kernel
  have hx1 : x ≠ 1 := by decide +kernel
  have hy1 : y ≠ 1 := by decide +kernel
  have hyx : y ≠ x := by decide +kernel
  have hyx2 : y ≠ x ^ 2 := by decide +kernel
  have := Fact.mk Nat.prime_three
  refine two_le_pRank_of_gens hx hy hxy hx1 fun n h => ?_
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h0, pow_zero] at h
    exact hy1 h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h1, pow_one] at h
    exact hyx h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h2] at h
    exact hyx2 h.symm

theorem two_le_pRank_M22_1515e [Finite NativeSporadic.M22] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.M22) := by
  set x := mathieuWord m22GenA m22GenB m22WordX.toList
  set y := mathieuWord m22GenA m22GenB m22WordY.toList
  have hx : x ^ 3 = 1 := by decide +kernel
  have hy : y ^ 3 = 1 := by decide +kernel
  have hxy : x * y = y * x := by decide +kernel
  have hx1 : x ≠ 1 := by decide +kernel
  have hy1 : y ≠ 1 := by decide +kernel
  have hyx : y ≠ x := by decide +kernel
  have hyx2 : y ≠ x ^ 2 := by decide +kernel
  have := Fact.mk Nat.prime_three
  refine two_le_pRank_of_gens hx hy hxy hx1 fun n h => ?_
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h0, pow_zero] at h
    exact hy1 h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h1, pow_one] at h
    exact hyx h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h2] at h
    exact hyx2 h.symm

theorem two_le_pRank_M23_1515e [Finite NativeSporadic.M23] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.M23) := by
  set x := mathieuWord m23GenA m23GenB m23WordX.toList
  set y := mathieuWord m23GenA m23GenB m23WordY.toList
  have hx : x ^ 3 = 1 := by decide +kernel
  have hy : y ^ 3 = 1 := by decide +kernel
  have hxy : x * y = y * x := by decide +kernel
  have hx1 : x ≠ 1 := by decide +kernel
  have hy1 : y ≠ 1 := by decide +kernel
  have hyx : y ≠ x := by decide +kernel
  have hyx2 : y ≠ x ^ 2 := by decide +kernel
  have := Fact.mk Nat.prime_three
  refine two_le_pRank_of_gens hx hy hxy hx1 fun n h => ?_
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h0, pow_zero] at h
    exact hy1 h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h1, pow_one] at h
    exact hyx h.symm
  · rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one, h2] at h
    exact hyx2 h.symm

theorem two_le_pRank_M12_1515e [Finite NativeSporadic.M12] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.M12) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := M12_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact two_le_pRank_of_cubic (by norm_num) hxy hcard

theorem two_le_pRank_M24_1515e [Finite NativeSporadic.M24] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.M24) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := M24_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact two_le_pRank_of_cubic (by norm_num) hxy hcard

theorem two_le_pRank_J2_1515e [Finite NativeSporadic.J2] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.J2) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := J2_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact two_le_pRank_of_cubic (by norm_num) hxy hcard

theorem two_le_pRank_He_1515e [Finite NativeSporadic.He] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup NativeSporadic.He) := by
  obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ := He_sylow3_cubic_witness
  have := Fact.mk Nat.prime_three
  exact two_le_pRank_of_cubic (by norm_num) hxy hcard

theorem a318Exclusion_m11 {X : Type} [Group X] [Finite X]
    (h : IsSporadic .M11 X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m11_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .M11) hfin hs two_le_pRank_M11_1515e
    CFSG.Sporadic.Mathieu.card_M11 l3Free_7920 h

theorem a318Exclusion_m12
    {X : Type} [Group X] [Finite X] (h : IsSporadic .M12 X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m12_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .M12) hfin hs two_le_pRank_M12_1515e
    CFSG.Sporadic.Mathieu.card_M12 l3Free_95040 h

theorem a318Exclusion_m22
    {X : Type} [Group X] [Finite X] (h : IsSporadic .M22 X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m22_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .M22) hfin hs two_le_pRank_M22_1515e
    CFSG.Sporadic.Mathieu.card_M22 l3Free_443520 h

theorem a318Exclusion_m24
    {X : Type} [Group X] [Finite X] (h : IsSporadic .M24 X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m24_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .M24) hfin hs two_le_pRank_M24_1515e
    CFSG.Sporadic.Mathieu.card_M24 l3Free_244823040 h

theorem a318Exclusion_j2
    {X : Type} [Group X] [Finite X] (h : IsSporadic .J2 X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.J2.fam_j2_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .J2) hfin hs two_le_pRank_J2_1515e
    CFSG.Sporadic.J2.card_J2 l3Free_604800 h

theorem a318Exclusion_he
    {X : Type} [Group X] [Finite X] (h : IsSporadic .He X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.He.fam_he_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .He) hfin hs two_le_pRank_He_1515e
    CFSG.Sporadic.He.card_He l3Free_4030387200 h

theorem a318Exclusion_m23
    {X : Type} [Group X] [Finite X] (h : IsSporadic .M23 X) : A318Exclusion X := by
  obtain ⟨hfin, -, hs⟩ := CFSG.Sporadic.Mathieu.fam_m23_simplicity
  have := hfin
  exact a318Exclusion_of_isSporadic1515e (s := .M23) hfin hs two_le_pRank_M23_1515e
    card_nativeM23_1522 l3Free_10200960 h

theorem a318Exclusion_tits
    {X : Type} [Group X] [Finite X] (h : IsTits X) : A318Exclusion X := by
  have hs : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_tits_simplicity X 2 1 h).2
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv X 2 1 h
  have hN : Nat.card X = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  have hr : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    have : Fact (Nat.card (ZMod 2) = 2) := ⟨by simp⟩
    have : CharP (ZMod 2) CFSG.LieType.Ree.ReeTag.F4.prime := inferInstanceAs (CharP (ZMod 2) 2)
    let e' := e.trans (CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := ZMod 2)).symm
    obtain ⟨x, y, -, -, -, hxy, -, -, hcard, -⟩ :=
      Tits_sylow3_cubic_witness (K := ZMod 2) (by simp)
    have := Fact.mk Nat.prime_three
    have h2 := two_le_pRank_of_cubic (by norm_num) hxy hcard
    rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e']
  exact A318Exclusion.of_card hs hr hN l3Free_17971200

theorem a318Exclusion_d42
    (hrank : ∀ (X : Type) [Group X] [Finite X], Is3D4 2 1 X → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    {X : Type} [Group X] [Finite X] (h : Is3D4 2 1 X) : A318Exclusion X :=
  A318Exclusion.of_card (CFSG.LieType.Simplicity.fam_3d4_simplicity X 2 1 h).2 (hrank X h)
    (threeD4TwoOrder1522 X h) l3Free_211341312

theorem a318Exclusion_u33
    (hrank : ∀ (X : Type) [Group X] [Finite X], IsPSU 3 3 1 X → 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    {X : Type} [Group X] [Finite X] (h : IsPSU 3 3 1 X) : A318Exclusion X :=
  A318Exclusion.of_card (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 3 1 h).2 (hrank X h)
    (psuThreeThreeOrder1522 X h) l3Free_6048

theorem knownFacts15122Types_of
    (h34 : L34NotL42Fact1515e)
    (hu33 : ∀ (X : Type) [Group X] [Finite X], IsPSU 3 3 1 X →
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hd4 : ∀ (X : Type) [Group X] [Finite X], Is3D4 2 1 X →
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : KnownFacts15122Types where
  alt7 := a318Exclusion_alt7
  alt6 := a318Exclusion_alt6
  u33 := fun _ _ _ h => a318Exclusion_u33 hu33 h
  l42 := fun _ _ _ h => a318Exclusion_psl42 h34 h
  l52 := fun _ _ _ h => a318Exclusion_psl52 h
  tits := fun _ _ _ h => a318Exclusion_tits h
  d42 := fun _ _ _ h => a318Exclusion_d42 hd4 h
  j2 := fun _ _ _ h => a318Exclusion_j2 h
  he := fun _ _ _ h => a318Exclusion_he h
  m12 := fun _ _ _ h => a318Exclusion_m12 h
  m22 := fun _ _ _ h => a318Exclusion_m22 h
  m23 := fun _ _ _ h => a318Exclusion_m23 h
  m24 := fun _ _ _ h => a318Exclusion_m24 h
  m11 := fun _ _ _ h => a318Exclusion_m11 h

end Sporadic

end CFSG.Quasithin
