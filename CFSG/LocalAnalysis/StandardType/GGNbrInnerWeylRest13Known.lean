module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylComp
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldComp
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6Split
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem largeEvenChevIDImage_inn {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]
    (H : Subgroup (LargeEvenChevGL A K)) (g : LargeEvenCenterQuot H) :
    MulAut.conj g ∈ LargeEvenChevIDImage A K H :=
  Subgroup.subset_closure (Set.mem_union_left _ ⟨g, rfl⟩)

theorem largeEvenLabelAll_inn_chevalley {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ g : R, MulAut.conj g ∈ I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h
  rcases h with rfl | rfl | rfl | rfl
  all_goals
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', fun g => largeEvenChevIDImage_inn _ K _ g⟩

theorem largeEvenLabelAll_inn_twE6 {lab : LargeEvenLabel} (ht : lab.tag = .twE6) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ g : R, MulAut.conj g ∈ I :=
  TwE6Delta.labelAll ht fun K _ _ _ g => largeEvenChevIDImage_inn _ K _ g

theorem largeEvenLabelAll_inn_twA {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twA) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ g : R, MulAut.conj g ∈ I :=
  largeEvenLabelAll_unitary hlab (Or.inl ht) fun d n K _ _ hn hd _ hK g => by
    have h := unitaryFieldData_of_card hn hK
    have hmem := RecipeFieldSU.conj_mem_recIU (d := d) h (by omega) g
    rwa [← SetLike.mem_coe, RecipeFieldSU.coe_recIU h hK (by omega)] at hmem

@[expose] def GGNbrWeylRowKnown (p r : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p r R ∧
    (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGTorusNoLineComp p r R I)

theorem largeEvenLabelAll_innerKLevelComp_of_row {p r : ℕ} {lab : LargeEvenLabel}
    (hPow : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
    (hRow : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r)) :
    LargeEvenLabelAll lab (GGNbrWeylInnerKLevelComp p) :=
  largeEvenLabelAll_weylInnerKLevelComp_of_noLineComp_or hPow
    (hRow.mono fun _ _ _ _ ⟨_, hl, hn⟩ hs hna => ⟨r, Or.inl hl, hn hs hna⟩)

theorem largeEvenLabelAll_fieldKLevelComp_of_row {p r : ℕ} {lab : LargeEvenLabel}
    (hRow : LargeEvenLabelAll lab (GGNbrWeylRowKnown p r))
    (hfld : LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusLiftFix p r R I F ∧ GGTorusNoLineFieldComp p r R I F) :
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp p) :=
  (largeEvenLabelAll_and hRow hfld).mono fun _ _ _ _ ⟨⟨hi, hl, hn⟩, hf⟩ hs hna =>
    ⟨hi, r, hl, (hf hs hna).1, hn hs hna, (hf hs hna).2⟩

theorem five_le_of_prime_ne_two_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := fun h => by
    subst h
    exact absurd hp (by norm_num)
  omega

theorem largeEvenLabelAll_noLineComp_E6 (hKG : GGNbrKGE6ThreeDvd) {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineComp 3 5 R I := by
  obtain ⟨htag, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => hKG K hpq⟩

theorem largeEvenLabelAll_noLineComp_E7 (hKG : GGNbrKGE7SmallAdd) {p : ℕ} (hp : p = 3 ∨ p = 5)
    {lab : LargeEvenLabel} (h : lab.tag = .E7 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineComp p 6 R I := by
  obtain ⟨htag, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => hKG p hp K hpq⟩

theorem largeEvenLabelAll_noLineComp_E8 (hKG : GGNbrKGE8SmallAdd) {p : ℕ} (hp : p = 3 ∨ p = 5)
    {lab : LargeEvenLabel} (h : lab.tag = .E8 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineComp p 7 R I := by
  obtain ⟨htag, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => hKG p hp K hpq⟩

theorem largeEvenLabelAll_noLineComp_F4 (hKG : GGNbrKGF4ThreeAdd) {lab : LargeEvenLabel}
    (h : lab.tag = .F4 ∧ 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineComp 3 3 R I := by
  obtain ⟨htag, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ => hKG K hpq⟩

theorem largeEvenLabelAll_noLineComp_twE6 {p r : ℕ} {lab : LargeEvenLabel}
    (ht : lab.tag = .twE6)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ lab.n) ^ 2 →
      GGTorusNoLineComp p r (TwE6Delta.RecipeR K lab.n) (TwE6Delta.RecipeI K lab.n)) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineComp p r R I :=
  TwE6Delta.labelAll ht fun K _ _ hK _ _ => h K hK

theorem ggNbrInnerWeylOn_triD4Two (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hKG : GGNbrKGFieldTriD4Two) :
    GGNbrInnerWeylOn GGNbrWeylTriD4TwoLabel :=
  ggNbrInnerWeylOn_of_fieldLabelsComp hL hPJ hG fun p lab _ _ hlab ⟨_, ht, hp3, hn⟩ => by
    subst hp3
    exact hKG lab hlab ht hn

section TwARow

theorem largeEvenLabelAll_rowKnown_twA (hKG : GGNbrKGUnitSixThree) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowKnown 3 3) := by
  have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 3 R := by
    have e : ggUnitaryTorusRank 3 (lab.rank + 1) = 3 := by rw [h.2.1]; rfl
    have := largeEvenLabelAll_torusLift_twA hlab h.1 Nat.prime_three h.2.2
    rwa [e] at this
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_twA hlab h.1)
    (largeEvenLabelAll_and hl
      ((hKG lab hlab h.1 h.2.1 h.2.2).mono fun _ _ _ _ hn hs hna =>
        ggTorusNoLineComp_of_le Nat.prime_three.pos (Nat.zero_le 3) (hn hs hna)))).mono
    fun _ _ _ _ h' => h'

end TwARow

section E6Row

theorem largeEvenLabelAll_rowKnown_E6 (hKG : GGNbrKGE6ThreeDvd) {lab : LargeEvenLabel}
    (h : lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) : LargeEvenLabelAll lab (GGNbrWeylRowKnown 3 5) :=
  (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inl h.1))
    (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_E6_three_dvd h)
      (largeEvenLabelAll_noLineComp_E6 hKG h))).mono fun _ _ _ _ h' => h'

section ExcPlusRows

theorem largeEvenLabelAll_rowKnown_E7 (hKG : GGNbrKGE7SmallAdd) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp35 : p = 3 ∨ p = 5) {lab : LargeEvenLabel}
    (h : lab.tag = .E7 ∧ p ∣ 2 ^ lab.n + 1) : LargeEvenLabelAll lab (GGNbrWeylRowKnown p 6) := by
  have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 6 R := by
    have e : ggNbrExcPlusRank lab.tag = 6 := by rw [h.1]; rfl
    have := largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inl h.1, h.2⟩
    rwa [e] at this
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inr (Or.inl h.1)))
    (largeEvenLabelAll_and hl (largeEvenLabelAll_noLineComp_E7 hKG hp35 h))).mono
      fun _ _ _ _ h' => h'

theorem largeEvenLabelAll_rowKnown_E8 (hKG : GGNbrKGE8SmallAdd) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp35 : p = 3 ∨ p = 5) {lab : LargeEvenLabel}
    (h : lab.tag = .E8 ∧ p ∣ 2 ^ lab.n + 1) : LargeEvenLabelAll lab (GGNbrWeylRowKnown p 7) := by
  have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 7 R := by
    have e : ggNbrExcPlusRank lab.tag = 7 := by rw [h.1]; rfl
    have := largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inr (Or.inl h.1), h.2⟩
    rwa [e] at this
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inr (Or.inr (Or.inl h.1))))
    (largeEvenLabelAll_and hl (largeEvenLabelAll_noLineComp_E8 hKG hp35 h))).mono
      fun _ _ _ _ h' => h'

theorem largeEvenLabelAll_rowKnown_F4 (hKG : GGNbrKGF4ThreeAdd) {lab : LargeEvenLabel}
    (h : lab.tag = .F4 ∧ 3 ∣ 2 ^ lab.n + 1) : LargeEvenLabelAll lab (GGNbrWeylRowKnown 3 3) := by
  have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 3 R := by
    have e : ggNbrExcPlusRank lab.tag = 3 := by rw [h.1]; rfl
    have := largeEvenLabelAll_torusLift_excPlus Nat.prime_three (by decide)
      ⟨Or.inr (Or.inr h.1), h.2⟩
    rwa [e] at this
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_chevalley (Or.inr (Or.inr (Or.inr h.1))))
    (largeEvenLabelAll_and hl (largeEvenLabelAll_noLineComp_F4 hKG h))).mono
      fun _ _ _ _ h' => h'

section PowMem

theorem ggNbrInnerWeylOn_e6ThreeDvd (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hKG : GGNbrKGE6ThreeDvd) : GGNbrInnerWeylOn GGNbrWeylE6ThreeDvdLabel :=
  ggNbrInnerWeylOn_of_labelsComp hL hPJ fun p lab hp hp2 hlab ⟨hpow, ht, hp3, hd⟩ => by
    subst hp3
    exact largeEvenLabelAll_innerKLevelComp_of_row
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      (largeEvenLabelAll_rowKnown_E6 hKG ⟨ht, hd⟩)

theorem ggNbrInnerWeylOn_excPlusSmall (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hE7 : GGNbrKGE7SmallAdd) (hE8 : GGNbrKGE8SmallAdd) (hF4 : GGNbrKGF4ThreeAdd) :
    GGNbrInnerWeylOn GGNbrWeylExcPlusSmallPrimeLabel :=
  ggNbrInnerWeylOn_of_labelsComp hL hPJ fun p lab hp hp2 hlab ⟨⟨hpow, _, hd⟩, hsm⟩ => by
    have hPow := largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow
    rcases hsm with ⟨ht | ht, hs⟩ | ⟨ht, hs⟩
    · exact largeEvenLabelAll_innerKLevelComp_of_row hPow
        (largeEvenLabelAll_rowKnown_E7 hE7 hp hp2 hs ⟨ht, hd⟩)
    · exact largeEvenLabelAll_innerKLevelComp_of_row hPow
        (largeEvenLabelAll_rowKnown_E8 hE8 hp hp2 hs ⟨ht, hd⟩)
    · have hp3 : p = 3 := hs
      subst hp3
      exact largeEvenLabelAll_innerKLevelComp_of_row hPow
        (largeEvenLabelAll_rowKnown_F4 hF4 ⟨ht, hd⟩)

theorem ggNbrInnerWeylOn_unitSixThree (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hKG : GGNbrKGUnitSixThree) : GGNbrInnerWeylOn GGNbrWeylUnitSixThreeLabel :=
  ggNbrInnerWeylOn_of_labelsComp hL hPJ fun p lab hp hp2 hlab h => by
    have hp3 : p = 3 := h.2.2.2.1
    subst hp3
    exact largeEvenLabelAll_weylInnerKLevelComp_of_noLineComp_or
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab h.1)
      ((hKG lab hlab h.2.1 h.2.2.1 h.2.2.2.2).mono fun _ _ _ _ hn hs hna =>
        ⟨0, Or.inr rfl, hn hs hna⟩)

section TwE6Rows

theorem largeEvenLabelAll_rowKnown_twE6Dvd (hKG : GGNbrKGTwE6ThreeDvd) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowKnown 3 4) :=
  (largeEvenLabelAll_and (largeEvenLabelAll_inn_twE6 h.1)
    (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_twE6Dvd Nat.prime_three (by decide) hlab h)
      (largeEvenLabelAll_noLineComp_twE6 h.1 fun K _ _ hK => hKG K lab.n hlab.1 hK h.2))).mono
    fun _ _ _ _ h' => h'

theorem largeEvenLabelAll_rowKnown_twE6AddLarge (hKG : GGNbrKGTwE6AddLarge) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) : LargeEvenLabelAll lab (GGNbrWeylRowKnown p 5) := by
  have hl : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p 5 R :=
    (largeEvenLabelAll_torusLift_twE6Add hp hlab h).mono fun _ _ _ _ hl => by
      rwa [TwE6Delta.liftRank_of_ne (by omega)] at hl
  exact (largeEvenLabelAll_and (largeEvenLabelAll_inn_twE6 h.1)
    (largeEvenLabelAll_and hl
      (largeEvenLabelAll_noLineComp_twE6 h.1 fun K _ _ hK =>
        hKG K lab.n p hlab.1 hK hp hp5 h.2))).mono fun _ _ _ _ h' => h'

theorem ggNbrInnerWeylOn_twE6Known (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (h3 : GGNbrKGTwE6ThreeDvd) (h5 : GGNbrKGTwE6AddLarge) :
    GGNbrInnerWeylOn GGNbrWeylTwE6KnownLabel :=
  ggNbrInnerWeylOn_of_labelsComp hL hPJ fun p lab hp hp2 hlab ⟨⟨hpow, ht, hcase⟩, hres⟩ => by
    have hPow := largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow
    rcases hcase with ⟨hp3, hd⟩ | hadd
    · subst hp3
      exact largeEvenLabelAll_innerKLevelComp_of_row hPow
        (largeEvenLabelAll_rowKnown_twE6Dvd h3 hlab ⟨ht, hd⟩)
    · have hp3 : p ≠ 3 := fun h => hres ⟨h, hadd⟩
      exact largeEvenLabelAll_innerKLevelComp_of_row hPow
        (largeEvenLabelAll_rowKnown_twE6AddLarge h5 hp
          (five_le_of_prime_ne_two_three hp hp2 hp3) hlab ⟨ht, hadd⟩)

theorem ggNbrInnerWeylOn_fieldRows (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hKG : GGNbrWeylKGInput) :
    GGNbrInnerWeylOn fun p lab => GGNbrWeylFieldRestLabel p lab ∧ GGNbrWeylFieldRowLabel p lab := by
  obtain ⟨hE6, h3, h5, hE7, hE8, hF4, hU, hf1, hf2, hf3, hf4, hf5, hf6, hf7, -⟩ := hKG
  refine ggNbrInnerWeylOn_of_fieldLabelsComp hL hPJ hG fun p lab hp hp2 hlab ⟨hrest, hrow⟩ => ?_
  have hdvd := ggNbrWeylFieldRowLabel_dvd hrest hrow
  rcases hrow with ⟨ht, hp3, hd⟩ | ⟨ht, ⟨hp3, hd⟩ | ⟨hp5, hd⟩⟩ | ⟨ht | ht, hp35, hd⟩ |
    ⟨ht, hp3, hd⟩ | ⟨ht, hr, hp3, hd⟩
  · subst hp3
    exact largeEvenLabelAll_fieldKLevelComp_of_row (largeEvenLabelAll_rowKnown_E6 hE6 ⟨ht, hd⟩)
      (hf1 3 lab hp hp2 hlab ⟨ht, rfl, hd⟩ hdvd)
  · subst hp3
    exact largeEvenLabelAll_fieldKLevelComp_of_row
      (largeEvenLabelAll_rowKnown_twE6Dvd h3 hlab ⟨ht, hd⟩)
      (hf2 3 lab hp hp2 hlab ⟨ht, rfl, hd⟩ hdvd)
  · exact largeEvenLabelAll_fieldKLevelComp_of_row
      (largeEvenLabelAll_rowKnown_twE6AddLarge h5 hp hp5 hlab ⟨ht, hd⟩)
      (hf3 p lab hp hp2 hlab ⟨ht, hp5, hd⟩ hdvd)
  · exact largeEvenLabelAll_fieldKLevelComp_of_row
      (largeEvenLabelAll_rowKnown_E7 hE7 hp hp2 hp35 ⟨ht, hd⟩)
      (hf4 p lab hp hp2 hlab ⟨ht, hp35, hd⟩ hdvd)
  · exact largeEvenLabelAll_fieldKLevelComp_of_row
      (largeEvenLabelAll_rowKnown_E8 hE8 hp hp2 hp35 ⟨ht, hd⟩)
      (hf5 p lab hp hp2 hlab ⟨ht, hp35, hd⟩ hdvd)
  · subst hp3
    exact largeEvenLabelAll_fieldKLevelComp_of_row (largeEvenLabelAll_rowKnown_F4 hF4 ⟨ht, hd⟩)
      (hf6 3 lab hp hp2 hlab ⟨ht, rfl, hd⟩ hdvd)
  · subst hp3
    exact largeEvenLabelAll_fieldKLevelComp_of_row
      (largeEvenLabelAll_rowKnown_twA hU hlab ⟨ht, hr, hd⟩)
      (hf7 3 lab hp hp2 hlab ⟨ht, hr, rfl, hd⟩ hdvd)

theorem ggNbrInnerWeylOn_rest13_of_known (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hG : GGNbrGraphInput) (hKG : GGNbrWeylKGInput)
    (hOther : GGNbrInnerWeylOn GGNbrWeylFieldOtherLabel)
    (hRes : GGNbrInnerWeylOn GGNbrWeylResidualLabel) :
    GGNbrInnerWeylOn GGNbrWeylRest13Label := by
  have hF := ggNbrInnerWeylOn_fieldRows hL hPJ hG hKG
  obtain ⟨hE6, h3, h5, hE7, hE8, hF4, hU, -, -, -, -, -, -, -, hT⟩ := hKG
  exact ((ggNbrInnerWeylOn_unitSixThree hL hPJ hU).or
    ((ggNbrInnerWeylOn_e6ThreeDvd hL hPJ hE6).or
    ((ggNbrInnerWeylOn_twE6Known hL hPJ h3 h5).or
    ((ggNbrInnerWeylOn_excPlusSmall hL hPJ hE7 hE8 hF4).or
    (hF.or ((ggNbrInnerWeylOn_triD4Two hL hPJ hG hT).or (hOther.or hRes))))))).mono
      fun _ _ hr => ggNbrWeylRest13Label_cover_known hr

end TwE6Rows

end PowMem

end ExcPlusRows

end E6Row

end CFSG.StandardType

end
