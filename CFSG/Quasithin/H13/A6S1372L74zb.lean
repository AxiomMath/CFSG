module

public import CFSG.Quasithin.Background.S1549DL3N
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix

namespace A6L74

theorem eq_four_of_sl2_card {q : ℕ} (h : q * (q ^ 2 - 1) = 60) : q = 4 := by
  have hq : q ≤ 4 := by
    by_contra hq
    push Not at hq
    have h1 : 5 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have h2 : 5 * (5 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right h1 1)
    omega
  interval_cases q <;> omega

theorem sl3_card_ne_60 {q : ℕ} : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ≠ 60 := by
  intro h
  rcases Nat.lt_or_ge q 3 with hq | hq
  · interval_cases q <;> norm_num at h
  · have h1 : 3 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 3 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 3 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    norm_num at h4

theorem sp4_card_ne_60 {q : ℕ} : q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) ≠ 60 := by
  intro h
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q <;> norm_num at h
  · have h1 : 2 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    have h2 : 2 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h3 : 2 ^ 4 - 1 ≤ q ^ 4 - 1 := Nat.sub_le_sub_right h1 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    norm_num at h4

theorem g2_card_ne_60 {q : ℕ} : q ^ 6 * ((q ^ 6 - 1) * (q ^ 2 - 1)) ≠ 60 := by
  intro h
  rcases Nat.lt_or_ge q 2 with hq | hq
  · interval_cases q <;> norm_num at h
  · have h1 : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    have h2 : 2 ^ 6 - 1 ≤ q ^ 6 - 1 := Nat.sub_le_sub_right h1 1
    have h3 : 2 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1
    have h4 := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
    rw [h] at h4
    norm_num at h4

section Exclude

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem b42_cases_60
    (hc : Nat.card ↥K = 60) (h : B42ModulePair K U Z) :
    BinaryNaturalSL K U Z 2 2 ∨ AlternatingNatural K U Z 5 := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · left
    obtain ⟨F, hF1, hF2, hF, π, hπ⟩ := h
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hc] at h1
    have h4 : Nat.card F = 4 := eq_four_of_sl2_card h1.symm
    exact ⟨F, hF1, hF2, by rw [h4]; norm_num, π, hπ⟩
  · exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [hc, card_statedSL_three1527d] at h1
    exact sl3_card_ne_60 h1.symm
  · exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [hc, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp] at h1
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI, Finset.prod_pair (by norm_num)] at h1
    exact sp4_card_ne_60 (q := Nat.card F) (by simpa using h1.symm)
  · exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hcard : Nat.card ↥K = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
      have := FFC.charP_two_of_card_pow hF
      exact (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
    rw [card_quasithinG2_1527d hF, hc] at hcard
    exact g2_card_ne_60 hcard.symm
  · exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hcP := FFC.charP_two_of_card_pow hF
    have hΓ : ⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ≤ CFSG.Open.quasithinG2 F := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      exact (CFSG.Open.quasithinG2 F).mul_mem
        ((CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem ha hb)
          ((CFSG.Open.quasithinG2 F).inv_mem ha)) ((CFSG.Open.quasithinG2 F).inv_mem hb)
    have hcard : Nat.card ↥K = Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
      (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ hΓ) hπ, hπ.1⟩)).symm
    rw [S1549D.card_commutator_quasithinG2_two (by simpa using hF), hc] at hcard
    omega
  · exact Or.inr h
  · exfalso
    obtain ⟨π, hπ⟩ := h
    have hcard : Nat.card ↥K = Nat.card ↥(alternatingGroup (Fin 6)) :=
      (Nat.card_congr (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ).toEquiv).symm
    rw [card_alternatingGroup1527d 6 (by norm_num), hc] at hcard
    norm_num [Nat.factorial] at hcard
  · exfalso
    obtain ⟨π, hπ⟩ := h
    have hcard : Nat.card ↥K = Nat.card ↥(alternatingGroup (Fin 7)) :=
      (Nat.card_congr (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ).toEquiv).symm
    rw [card_alternatingGroup1527d 7 (by norm_num), hc] at hcard
    norm_num [Nat.factorial] at hcard
  · exfalso
    obtain ⟨α, π, hπ⟩ := h
    have hcard : Nat.card ↥K = Nat.card ↥(alternatingGroup (Fin 7)) :=
      (Nat.card_congr (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ).toEquiv).symm
    rw [card_alternatingGroup1527d 7 (by norm_num), hc] at hcard
    norm_num [Nat.factorial] at hcard
  · exfalso
    obtain ⟨F, _, _, Γ₀, hF, -, hhat, -, π, hπ⟩ := h
    have hcard : Nat.card ↥K = Nat.card ↥Γ₀ :=
      (Nat.card_congr (FFC.equivOfRealizes (FFModel.nat_faithful Γ₀) hπ).toEquiv).symm
    have h2 : Nat.card ↥Γ₀ = 1080 :=
      card_of_isHat1527d hhat (by
        rw [card_alternatingGroup1527d 6 (by norm_num)]
        norm_num [Nat.factorial])
    omega
  · exfalso
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [hc, card_statedSL1527d (by omega), Nat.card_zmod] at h1
    revert h1
    decide
  · exfalso
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    have h1 := card_eq_of_nat_realizes1527d hπ
    rw [hc, card_statedSL1527d (by omega), Nat.card_zmod] at h1
    revert h1
    decide
  · exfalso
    obtain ⟨π, hπ⟩ := h
    have hcard : Nat.card ↥K = Nat.card ↥(StatedSL 4 (ZMod 2)) :=
      (Nat.card_congr (FFC.equivOfRealizes (FFC.extSq_faithful (by omega)) hπ).toEquiv).symm
    rw [hc, card_statedSL1527d (by omega), Nat.card_zmod] at hcard
    revert hcard
    decide
  · exfalso
    obtain ⟨π, hπ⟩ := h
    have hcard : Nat.card ↥K = Nat.card ↥(StatedSL 5 (ZMod 2)) :=
      (Nat.card_congr (FFC.equivOfRealizes (FFC.extSq_faithful (by omega)) hπ).toEquiv).symm
    rw [hc, card_statedSL1527d (by omega), Nat.card_zmod] at hcard
    revert hcard
    decide

theorem b42_cases_168
    (hc : Nat.card ↥K = 168) (h : B42ModulePair K U Z) : BinaryNaturalSL K U Z 3 1 := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  · exact (S1549D.not_sl2_168 hc h).elim
  · exact S1549D.binaryNaturalSL_three_one hc h
  · exact (S1549D.not_sp4_168 hc h).elim
  · exact (S1549D.not_g2_168 hc h).elim
  · exact (S1549D.not_g2d_168 hc h).elim
  · exact (S1549D.not_alt_168 (m := 5) (by norm_num) (by norm_num [Nat.factorial]) hc h).elim
  · exact (S1549D.not_alt_168 (m := 6) (by norm_num) (by norm_num [Nat.factorial]) hc h).elim
  · exact (S1549D.not_alt_168 (m := 7) (by norm_num) (by norm_num [Nat.factorial]) hc h).elim
  · exact (S1549D.not_a7Four_168 hc h).elim
  · exact (S1549D.not_tripleA6_168 hc h).elim
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    exact (S1549D.not_sl_two_168 hc (Or.inl rfl) hπ).elim
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    exact (S1549D.not_sl_two_168 hc (Or.inr rfl) hπ).elim
  · exact (S1549D.not_extSq_168 hc (Or.inl rfl) h).elim
  · exact (S1549D.not_extSq_168 hc (Or.inr rfl) h).elim

end Exclude

section Omega

variable {V : Type} [CommGroup V]

theorem false_of_natural_sl3_of_omega {K : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K U Z π) {ω : MulAut V}
    (hωU : ∀ u ∈ U, ω u ∈ U) (hωZ : ∀ z ∈ Z, ω z ∈ Z) (hωZ' : ∀ z ∈ Z, ω⁻¹ z ∈ Z)
    (hωK : ∀ k ∈ K, ω * k = k * ω) (hωf : ∀ u ∈ U, ω u * u⁻¹ ∈ Z → u ∈ Z) : False := by
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  set γ₁ := specialLinearGroupEquivStatedSL 3 (ZMod 2)
    ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩ with hγ₁
  have hact : ∀ x : Fin 3 → ZMod 2, Multiplicative.toAdd
      (natAct (StatedSL 3 (ZMod 2)) γ₁ (Multiplicative.ofAdd x)) =
        (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x := by
    intro x
    rfl
  have hfix : ∀ x : Fin 3 → ZMod 2,
      (!![1, 0, 0; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x = x →
      x = 0 ∨ x = ![1, 0, 0] := by decide
  have hZU : Z ≤ U := hπ.2.1
  obtain ⟨u₀, hu₀⟩ := hfs (Multiplicative.ofAdd ![1, 0, 0])
  have hne : f u₀ ≠ 1 := by
    rw [hu₀]
    intro h
    have := congrArg (fun m : Multiplicative (Fin 3 → ZMod 2) => Multiplicative.toAdd m 0) h
    simp at this
  have hu : ((π γ₁ : ↥K) : MulAut V) (u₀ : V) ∈ U := hπ.2.2.2.1 (π γ₁) u₀ u₀.2
  have hc : ((π γ₁ : ↥K) : MulAut V) (u₀ : V) * (u₀ : V)⁻¹ ∈ Z := by
    have h1 : f ⟨_, hu⟩ = f u₀ := by
      rw [hfe γ₁ u₀ hu, hu₀]
      apply Multiplicative.toAdd.injective
      rw [hact]
      decide
    have h2 : f (⟨_, hu⟩ * u₀⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]
      exact mul_inv_cancel _
    simpa using (hfk _).1 h2
  have hωu : ((π γ₁ : ↥K) : MulAut V) (ω u₀) ∈ U := hπ.2.2.2.1 (π γ₁) _ (hωU _ u₀.2)
  have hcomm : ((π γ₁ : ↥K) : MulAut V) (ω u₀) = ω (((π γ₁ : ↥K) : MulAut V) (u₀ : V)) := by
    have := congrArg (fun φ : MulAut V => φ (u₀ : V)) (hωK _ (π γ₁).2)
    simpa [MulAut.mul_apply] using this.symm
  have hωc : ω (((π γ₁ : ↥K) : MulAut V) (u₀ : V) * (u₀ : V)⁻¹) ∈ U := hZU (hωZ _ hc)
  have hwfix : natAct (StatedSL 3 (ZMod 2)) γ₁ (f ⟨ω u₀, hωU _ u₀.2⟩) = f ⟨ω u₀, hωU _ u₀.2⟩ := by
    rw [← hfe γ₁ _ hωu]
    have e : (⟨((π γ₁ : ↥K) : MulAut V) (ω u₀), hωu⟩ : ↥U) =
        ⟨_, hωc⟩ * ⟨ω u₀, hωU _ u₀.2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hcomm, map_mul, map_inv, inv_mul_cancel_right]
    rw [e, map_mul, (hfk _).2 (hωZ _ hc), one_mul]
  have h2 := hfix (Multiplicative.toAdd (f ⟨ω u₀, hωU _ u₀.2⟩))
    (by rw [← hact, ofAdd_toAdd, hwfix])
  rcases h2 with h2 | h2
  · have h3 : f ⟨ω u₀, hωU _ u₀.2⟩ = 1 := Multiplicative.toAdd.injective (by rw [h2]; rfl)
    have h4 := (hfk _).1 h3
    have h5 : (u₀ : V) ∈ Z := by
      have := hωZ' _ h4
      simpa using this
    exact hne ((hfk u₀).2 h5)
  · have h3 : f ⟨ω u₀, hωU _ u₀.2⟩ = f u₀ := by
      rw [hu₀]
      exact Multiplicative.toAdd.injective h2
    have h4 : f (⟨ω u₀, hωU _ u₀.2⟩ * u₀⁻¹) = 1 := by
      rw [map_mul, map_inv, h3]
      exact mul_inv_cancel _
    exact hne ((hfk u₀).2 (hωf _ u₀.2 (by simpa using (hfk _).1 h4)))

theorem eq_one_of_mem_zpowers_allOnes {x : G6.PermMod 5}
    (hx1 : x ∈ Subgroup.zpowers (G6.allOnes 5)) (hx2 : x ∈ G6.coreMod 5) : x = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx1
  have e : Multiplicative.toAdd (G6.allOnes 5 ^ k) = fun _ => (k : ZMod 2) := by
    funext i
    simp [G6.allOnes, toAdd_zpow, zsmul_eq_mul]
  have hc : ∀ c : ZMod 2, ∑ _i : Fin 5, c = 0 → c = 0 := by decide
  have h := G6.mem_coreMod.mp hx2
  rw [e] at h
  have hk := hc _ h
  apply Multiplicative.toAdd.injective
  rw [e, toAdd_one, hk]
  rfl

theorem altDn5_ker : (FFModel.altDn 5).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  exact Subgroup.mem_bot.mpr (eq_one_of_mem_zpowers_allOnes hx.1 hx.2)

theorem false_of_altDn5_of_omega {K : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(alternatingGroup (Fin 5)) →* ↥K}
    (hπ : (FFModel.altDn 5).RealizesVia K U Z π) {ω : MulAut V}
    (hωU : ∀ u ∈ U, ω u ∈ U) (hωZ : ∀ z ∈ Z, ω z ∈ Z) (hωZ' : ∀ z ∈ Z, ω⁻¹ z ∈ Z)
    (hωK : ∀ k ∈ K, ω * k = k * ω) (hωf : ∀ u ∈ U, ω u * u⁻¹ ∈ Z → u ∈ Z) : False := by
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap altDn5_ker hπ
  have hZU : Z ≤ U := hπ.2.1
  let g : ↥U →* G6.PermMod 5 := (FFModel.altDn 5).sec.subtype.comp f
  have hg1 : ∀ u : ↥U, g u = 1 ↔ (u : V) ∈ Z := fun u => by
    rw [← hfk u]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      show (((f u : ↥(FFModel.altDn 5).sec)) : (FFModel.altDn 5).Amb) = 1
      rw [h]
      rfl
  have hge : ∀ (σ : ↥(alternatingGroup (Fin 5))) (u : ↥U)
      (hu : ((π σ : ↥K) : MulAut V) (u : V) ∈ U),
      g ⟨_, hu⟩ = G6.permAct 5 (σ : Equiv.Perm (Fin 5)) (g u) := fun σ u hu => hfe σ u hu
  have hgsurj : ∀ m : G6.PermMod 5, ∑ i, Multiplicative.toAdd m i = 0 → ∃ u, g u = m := by
    intro m hm
    obtain ⟨u, hu⟩ := hfs ⟨m, G6.mem_coreMod.mpr hm⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  have hgcore : ∀ u : ↥U, ∑ i, Multiplicative.toAdd (g u) i = 0 := fun u =>
    G6.mem_coreMod.mp (f u).2
  have hfix : ∀ x : Fin 5 → ZMod 2,
      (∑ i, x i = 0 ∧
        (∀ i, x ((Equiv.swap 2 3 * Equiv.swap 3 4 : Equiv.Perm (Fin 5))⁻¹ i) = x i) ∧
        ∀ i, x ((Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 5))⁻¹ i) = x i) →
      x = 0 ∨ x = ![1, 1, 0, 0, 0] := by decide +kernel
  have hmem : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
      Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 5) := fun a b c d hab hcd => by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hcd]
    decide
  set σ₁ : ↥(alternatingGroup (Fin 5)) :=
    ⟨Equiv.swap 2 3 * Equiv.swap 3 4, hmem 2 3 3 4 (by decide) (by decide)⟩ with hσ₁
  set σ₂ : ↥(alternatingGroup (Fin 5)) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, hmem 0 1 2 3 (by decide) (by decide)⟩ with hσ₂
  have hv₁ : G6.permAct 5 (Equiv.swap 2 3 * Equiv.swap 3 4)
      (Multiplicative.ofAdd ![1, 1, 0, 0, 0]) = Multiplicative.ofAdd ![1, 1, 0, 0, 0] := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply]
    revert i
    decide
  have hv₂ : G6.permAct 5 (Equiv.swap 0 1 * Equiv.swap 2 3)
      (Multiplicative.ofAdd ![1, 1, 0, 0, 0]) = Multiplicative.ofAdd ![1, 1, 0, 0, 0] := by
    apply Multiplicative.toAdd.injective
    funext i
    rw [G6.permAct_apply]
    revert i
    decide
  obtain ⟨u₀, hu₀⟩ := hgsurj (Multiplicative.ofAdd ![1, 1, 0, 0, 0]) (by decide)
  have hne : g u₀ ≠ 1 := by
    rw [hu₀]
    intro h
    have := congrArg (fun m : G6.PermMod 5 => Multiplicative.toAdd m 0) h
    simp at this
  have hstep : ∀ σ : ↥(alternatingGroup (Fin 5)),
      G6.permAct 5 (σ : Equiv.Perm (Fin 5)) (Multiplicative.ofAdd ![1, 1, 0, 0, 0]) =
        Multiplicative.ofAdd ![1, 1, 0, 0, 0] →
      G6.permAct 5 (σ : Equiv.Perm (Fin 5)) (g ⟨ω u₀, hωU _ u₀.2⟩) = g ⟨ω u₀, hωU _ u₀.2⟩ := by
    intro σ hσ
    have hu : ((π σ : ↥K) : MulAut V) (u₀ : V) ∈ U := hπ.2.2.2.1 (π σ) u₀ u₀.2
    have hc : ((π σ : ↥K) : MulAut V) (u₀ : V) * (u₀ : V)⁻¹ ∈ Z := by
      have h1 : g ⟨_, hu⟩ = g u₀ := by rw [hge σ u₀ hu, hu₀, hσ]
      have h2 : g (⟨_, hu⟩ * u₀⁻¹) = 1 := by
        rw [map_mul, h1, ← map_mul, mul_inv_cancel, map_one]
      simpa using (hg1 _).1 h2
    have hωu : ((π σ : ↥K) : MulAut V) (ω u₀) ∈ U := hπ.2.2.2.1 (π σ) _ (hωU _ u₀.2)
    have hcomm : ((π σ : ↥K) : MulAut V) (ω u₀) = ω (((π σ : ↥K) : MulAut V) (u₀ : V)) := by
      have := congrArg (fun φ : MulAut V => φ (u₀ : V)) (hωK _ (π σ).2)
      simpa [MulAut.mul_apply] using this.symm
    have hωc : ω (((π σ : ↥K) : MulAut V) (u₀ : V) * (u₀ : V)⁻¹) ∈ U := hZU (hωZ _ hc)
    rw [← hge σ _ hωu]
    have e : (⟨((π σ : ↥K) : MulAut V) (ω u₀), hωu⟩ : ↥U) = ⟨_, hωc⟩ * ⟨ω u₀, hωU _ u₀.2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hcomm, map_mul, map_inv, inv_mul_cancel_right]
    rw [e, map_mul, (hg1 _).2 (hωZ _ hc), one_mul]
  have hw1 := hstep σ₁ hv₁
  have hw2 := hstep σ₂ hv₂
  have hwcore := hgcore ⟨ω u₀, hωU _ u₀.2⟩
  have h2 := hfix (Multiplicative.toAdd (g ⟨ω u₀, hωU _ u₀.2⟩))
    ⟨hwcore, fun i => by
      have := congrFun (congrArg Multiplicative.toAdd hw1) i
      rwa [G6.permAct_apply] at this, fun i => by
      have := congrFun (congrArg Multiplicative.toAdd hw2) i
      rwa [G6.permAct_apply] at this⟩
  rcases h2 with h2 | h2
  · have h3 : g ⟨ω u₀, hωU _ u₀.2⟩ = 1 := Multiplicative.toAdd.injective (by rw [h2]; rfl)
    have h4 := (hg1 _).1 h3
    have h5 : (u₀ : V) ∈ Z := by
      have := hωZ' _ h4
      simpa using this
    exact hne ((hg1 u₀).2 h5)
  · have h3 : g ⟨ω u₀, hωU _ u₀.2⟩ = g u₀ := by
      rw [hu₀]
      exact Multiplicative.toAdd.injective h2
    have h4 : g (⟨ω u₀, hωU _ u₀.2⟩ * u₀⁻¹) = 1 := by
      rw [map_mul, h3, ← map_mul, mul_inv_cancel, map_one]
    exact hne ((hg1 u₀).2 (hωf _ u₀.2 (by simpa using (hg1 _).1 h4)))

end Omega

end A6L74

end CFSG.Quasithin.H13.A6
