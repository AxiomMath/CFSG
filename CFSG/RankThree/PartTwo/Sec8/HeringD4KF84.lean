module

public import CFSG.RankThree.PartTwo.Sec8.HeringD4Weyl
public import CFSG.RankThree.PartTwo.Sec8.HeringD4Tools
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofD4
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofD4
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL2U
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityTorus2
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofPairingU3Zs
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U2

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec19

section Certs


namespace CFSG.RankThree.PartTwo.Sec8.HeringD4

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem false_of_classX_of_mem_Bsub (P : D4Par n X σ) {y : C0 σ} (hyB : y ∈ Bsub σ)
    (hy : IsClassX σ y) : False := by
  obtain ⟨hy3, hy1, h, hhA⟩ := hy
  have hσ3 := P.sigma_pow_three
  have hq3 : ¬ 3 ∣ 2 ^ n := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hK4 : 4 ≤ Nat.card X := by
    rw [P.card]
    have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by have := P.one_le; omega) 2
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h2 3
  have hAq := KS11Lie4Proof.isQuasisimple_d4ShortSL2 hσ3 hK4
  have hA1 : KS11Lie4Proof.d4ShortSL2 X σ.toRingHom ≠ ⊥ := by
    intro hbot
    obtain ⟨a, b, hab⟩ := hAq.2.2
    apply hab
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    have ha' : a' = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot a' a'.2)
    have hb' : b' = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp hbot b' b'.2)
    rw [ha', hb']
  have ha3 : (h * y * h⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hy3]
    group
  have ha1 : h * y * h⁻¹ ≠ 1 := fun h' => hy1 (by
    have : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [this, h']
    group)
  exact false_of_conj_B_A (A := KS11Lie4Proof.d4ShortSL2 X σ.toRingHom) hAq.1 hA1
    (fun s hs hsc hs3 => Sec11.Item1118Res3ProofU3Zs.d4ShortSL2_central_eq_one hσ3 hs
      (Subgroup.mem_centralizer_iff.mpr hsc) hs3)
    (fun t ht => Subgroup.mem_centralizer_iff.mp hyB t ht)
    (KS11Lie6Proof.d4ThreeBCent_holds X (2 ^ n) σ P.card P.frob hq3 y hyB hy3 hy1).1
    (KS11Lie6Proof.d4ThreeACent_holds X (2 ^ n) σ P.card P.frob hq3 (h * y * h⁻¹) hhA ha3 ha1)

theorem exists_conj_A0_of_classX (P : D4Par n X σ) (hn : 2 ≤ n) {x : C0 σ}
    (hxG : tauAut σ x = x) (hx : IsClassX σ x) :
    ∃ g : C0 σ, tauAut σ g = g ∧ g * x * g⁻¹ ∈ A0sub σ := by
  have hK : ringChar X = 2 := Item8KFactsProof.ringChar_eq_two_of_card P.card
  have : CharP X 2 := ringChar.of_eq hK
  obtain ⟨w₀, hwS, hwM⟩ := g2_pair_conj_AB' σ P hK
  have hinj := KFacts.trialityG2Incl_injective σ hK
  obtain ⟨u, rfl⟩ : x ∈ (KFacts.trialityG2Incl σ hK).range :=
    (KFacts.mem_range_trialityG2Incl_iff σ hK x).mpr hxG
  have hu3 : u ^ 3 = 1 := hinj (by rw [map_pow, hx.1, map_one])
  have hu1 : u ≠ 1 := fun h => hx.2.1 (by rw [h, map_one])
  have : Finite (fixSubfield σ) := Subtype.finite
  have : CharP (fixSubfield σ) 2 := RingHom.charP (fixSubfield σ).subtype
    (fixSubfield σ).subtype.injective 2
  have hk3 : ringChar (fixSubfield σ) ≠ 3 := by
    rw [ringChar.eq (fixSubfield σ) 2]
    norm_num
  have hk4 : 4 ≤ Nat.card (fixSubfield σ) := P.four_le_card_fix hn
  obtain ⟨c, hc⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds (fixSubfield σ) hk3 hk4 u hu3 hu1
  have hfix : tauAut σ (KFacts.trialityG2Incl σ hK (w₀ * c)) =
      KFacts.trialityG2Incl σ hK (w₀ * c) :=
    (KFacts.mem_range_trialityG2Incl_iff σ hK _).mp ⟨_, rfl⟩
  have key : KFacts.trialityG2Incl σ hK (w₀ * c) * KFacts.trialityG2Incl σ hK u *
      (KFacts.trialityG2Incl σ hK (w₀ * c))⁻¹ =
      KFacts.trialityG2Incl σ hK (w₀ * (c * u * c⁻¹) * w₀⁻¹) := by
    simp only [map_mul, map_inv]
    group
  refine ⟨KFacts.trialityG2Incl σ hK (w₀ * c), hfix, ?_⟩
  rw [key]
  rcases hc with hc | hc
  · exact hwS ⟨_, ⟨_, hc, rfl⟩, rfl⟩
  · exfalso
    have hB : KFacts.trialityG2Incl σ hK (w₀ * (c * u * c⁻¹) * w₀⁻¹) ∈ Bsub σ :=
      hwM ⟨_, ⟨_, hc, rfl⟩, rfl⟩
    rw [← key] at hB
    exact false_of_classX_of_mem_Bsub P hB (IsClassX.conj_mem σ hx _)

theorem residual_fixed_of_two_le (P : D4Par n X σ) (hn : 2 ≤ n) {τ : MulAut (C0 σ)}
    (hτ : Sec4.IsStdGraphFieldConj σ τ) {w : C0 σ} (hwA : w ∈ Asub σ) (hw3 : w ^ 3 = 1)
    (hw1 : w ≠ 1) (hτw : τ w = w) :
    ∀ x ∈ inSubgroup perfectResidual (Subgroup.centralizer ({w} : Set (C0 σ))), τ x = x := by
  obtain ⟨β, hβ⟩ := hτ
  obtain ⟨g₀, hg₀⟩ := KFacts.exists_conj_eq_conj_fieldActor P.one_le P.card P.frob β
  have hτ' : ∀ y, tauAut σ y = y ↔ τ (g₀ * y * g₀⁻¹) = g₀ * y * g₀⁻¹ := by
    intro y
    have hconj : ∀ ε : MulAut (C0 σ),
        (MulAut.conj g₀ * ε * (MulAut.conj g₀)⁻¹) (g₀ * y * g₀⁻¹) = g₀ * ε y * g₀⁻¹ := by
      intro ε
      simp only [MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply]
      group
    rcases hβ with h | h
    · have h' : τ = MulAut.conj g₀ * tauAut σ * (MulAut.conj g₀)⁻¹ := by
        rw [h]
        exact hg₀ σ
      rw [h', hconj]
      constructor
      · intro hy
        rw [hy]
      · intro hy
        exact mul_left_cancel (mul_right_cancel hy)
    · have h' : τ = MulAut.conj g₀ * (tauAut σ)⁻¹ * (MulAut.conj g₀)⁻¹ := by
        rw [h]
        have h1 := hg₀ σ
        calc β * (fieldActor σ σ)⁻¹ * β⁻¹ = (β * fieldActor σ σ * β⁻¹)⁻¹ := by group
          _ = (MulAut.conj g₀ * fieldActor σ σ * (MulAut.conj g₀)⁻¹)⁻¹ := by rw [h1]
          _ = MulAut.conj g₀ * (fieldActor σ σ)⁻¹ * (MulAut.conj g₀)⁻¹ := by group
      rw [h', hconj]
      have hinv : (tauAut σ)⁻¹ y = y ↔ tauAut σ y = y := by
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, eq_comm]
      rw [← hinv]
      constructor
      · intro hy
        rw [hy]
      · intro hy
        exact mul_left_cancel (mul_right_cancel hy)
  set w' := g₀⁻¹ * w * g₀ with hw'
  have hww' : w = g₀ * w' * g₀⁻¹ := by
    rw [hw']
    group
  have hσw' : tauAut σ w' = w' := (hτ' w').mpr (by rw [← hww']; exact hτw)
  have hclass : IsClassX σ w := ⟨hw3, hw1, 1, by simpa using hwA⟩
  have hclass' : IsClassX σ w' := by
    have := IsClassX.conj_mem σ hclass g₀⁻¹
    rwa [inv_inv] at this
  obtain ⟨g, hg, hgA⟩ := exists_conj_A0_of_classX P hn hσw' hclass'
  have hclass₀ : IsClassX σ (g * w' * g⁻¹) := IsClassX.conj_mem σ hclass' g
  have hlayer := Sec4.E27.tau_fixes_layer P hn hclass₀ hgA
  have hlayer' : ∀ d ∈ ⁅Subgroup.centralizer ({w'} : Set (C0 σ)),
      Subgroup.centralizer ({w'} : Set (C0 σ))⁆, tauAut σ d = d :=
    fixed_on_commutator_of_conj (tauAut σ) g w' hg hlayer
  intro x hx
  have hxc : g₀⁻¹ * x * g₀ ∈ ⁅Subgroup.centralizer ({w'} : Set (C0 σ)),
      Subgroup.centralizer ({w'} : Set (C0 σ))⁆ := by
    have h1 := inSubgroup_perfectResidual_le_commutator _ hx
    have h2 : g₀⁻¹ * x * g₀⁻¹⁻¹ ∈ ⁅Subgroup.centralizer ({g₀⁻¹ * w * g₀⁻¹⁻¹} : Set (C0 σ)),
        Subgroup.centralizer ({g₀⁻¹ * w * g₀⁻¹⁻¹} : Set (C0 σ))⁆ := by
      rw [← map_commutator_centralizer_conj]
      exact ⟨x, h1, rfl⟩
    simpa only [inv_inv] using h2
  have h3 := (hτ' _).mp (hlayer' _ hxc)
  have e : g₀ * (g₀⁻¹ * x * g₀) * g₀⁻¹ = x := by group
  rw [e] at h3
  exact h3

theorem residual_eq_bot_two {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ 1) {w : C0 σ} (hwA : w ∈ Asub σ)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) :
    inSubgroup perfectResidual (Subgroup.centralizer ({w} : Set (C0 σ))) = ⊥ := by
  have hKc : ringChar K = 2 := Item8KFactsProof.ringChar_eq_two_of_card hK
  have : CharP K 2 := ringChar.of_eq hKc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨c, R, hcR, hRC, hcomm, U, hU, ⟨e⟩⟩ :=
    Sec21.Item219LieProof.d4_threeA_model_unitary_two (ℓ := 2) (f := 1) Nat.prime_two le_rfl
      (by norm_num) (by norm_num) hK hσ hwA hw3 hw1
  have hUcard := Sec4.E27.card_subgroup_unitarySet (ℓ := 2) (f := 1) le_rfl U hU
  have hRcard : Nat.card R = 2 ^ 3 * 3 ^ 3 := by
    rw [Nat.card_congr e.toEquiv, hUcard]
    norm_num
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hRcard]; norm_num)
  have : Fintype R := Fintype.ofFinite R
  have hRsol : Group.IsSolvable R :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hRcard])
  have hCsol : Group.IsSolvable (Subgroup.centralizer ({c * w * c⁻¹} : Set (C0 σ))) :=
    isSolvable_of_commutator_le _ R (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact hcomm a ha b hb) hRsol
  exact inSubgroup_perfectResidual_eq_bot_of_solvable _ (isSolvable_centralizer_of_conj c w hCsol)

end CFSG.RankThree.PartTwo.Sec8.HeringD4

namespace CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

theorem kF84D4OuterSU3Std_holds : KF84D4OuterSU3Std := by
  intro m K _ _ σ hK hσ τ hτ3 hτin hstd w hwS hw3 hw1 hτw
  left
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK] at h1
      norm_num at h1
    · exact hm
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · intro x hx
    rw [HeringD4.residual_eq_bot_two hK hσ hwS hw3 hw1] at hx
    rw [Subgroup.mem_bot.mp hx, map_one]
  · exact HeringD4.residual_fixed_of_two_le ⟨hm, hK, hσ⟩ hm2 hstd hwS hw3 hw1 hτw

theorem kF84D4OuterSU3_holds : Item8KFacts3.KF84D4OuterSU3 :=
  kF84D4OuterSU3_of kF84D4OuterSU3Std_holds

end CFSG.RankThree.PartTwo.Sec8.Item84KFacts4

end Certs
