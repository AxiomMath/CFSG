module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkConj
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkBstar
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

namespace WitSpBlk

variable {F : Type} [Field F] {n e s r p : ℕ} {A₀ : GL (Fin n ⊕ Fin n) F}
  {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {C : Matrix (Fin e) (Fin e) F}

theorem ne_one_of_spBlockMat (he : 1 ≤ e)
    (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : F, IsUnit (C ^ j - c • 1)) {X : StatedSp n F}
    {k : Fin s → ℕ} (hX : RootPlaneSp.SpBlockMat A₀ ε C X k) {i : Fin s} (hki : ¬ p ∣ k i) :
    X ≠ 1 := by
  intro h1
  have htr : SpNonsplitComp.truncExp p 0 k = k := funext fun j => by
    simp [SpNonsplitComp.truncExp]
  rw [← htr] at hX
  exact hki (SpNonsplitComp.dvd_of_truncExp_eq_one he hcunit hX h1 (i := i) rfl)

end WitSpBlk

open WitSpBlk in
theorem blockWitness_core {G : Type} [Group G] {f n p : ℕ} (hf : 1 ≤ f) (hrk : 2 ≤ n)
    {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)))
    (hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥) (hp : p.Prime) (hp2 : p ≠ 2)
    {B Bs G₀ : Subgroup G} (hBs : GGBstar p B Bs) (hrange : ψ.range = G₀)
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b)
    (hcard : p ^ 4 ≤ Nat.card Bs) (hns : ¬ p ∣ 2 ^ f - 1) (t : StatedLieTag) :
    ∃ d : ℕ, 1 ≤ d ∧ 3 * d ≤ n ∧ ∃ A₀ X₀ : StatedSp n (GaloisField 2 f),
      X₀ ∈ suppGroup (WitSpNs.blockCoords n d 0) ∧
      GGSixBstarWit p Bs G₀ t f (ψ (A₀ * X₀ * A₀⁻¹)) ∧
      GGSixBstarWit p Bs G₀ t f
        (ψ (A₀ * (X₀ * (permSp (GaloisField 2 f) (WitSpNs.blockSwap n d) * X₀ *
          (permSp (GaloisField 2 f) (WitSpNs.blockSwap n d))⁻¹)) * A₀⁻¹)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero n := ⟨by omega⟩
  obtain ⟨e, s, r, C, ε, A₀, hCp, hcunit, hreal, hframe, hN⟩ :=
    spNonsplitFrame_norm hf hrk ψ hker hCψ hp hp2 hBs hdiag hns
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [AutPSp.center_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  have hcongr : ∀ {b : G} {k k' : Fin s → ℕ}, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k →
      (∀ i, k i % p = k' i % p) → NoOffPSLRest.SpFrameRep ψ A₀ ε C b k' := by
    rintro b k k' ⟨X, hX1, hX2⟩ hkk
    exact ⟨X, hX1, by rw [hX2, NoOffPSLRest.nsCore_congr hCp hkk]⟩
  have he0 : e ≠ 0 := by
    intro he0
    have hsub : Bs ≤ ⊥ := fun b hb => by
      obtain ⟨k, X, rfl, hX⟩ := hframe b hb
      have hX1 : X = 1 := by
        apply Subtype.ext
        apply Units.ext
        rw [hX, NoOffPSLRest.nsCore_eq_one_of_e_zero he0, Matrix.submatrix_one_equiv,
          Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        rfl
      rw [hX1, map_one]
      exact Subgroup.one_mem _
    have h1 : Nat.card Bs ≤ 1 := by
      have := Subgroup.card_le_of_le hsub
      rwa [Subgroup.card_bot] at this
    have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) hp.one_lt
    omega
  have he2 : 2 ≤ e := by
    by_contra he
    obtain rfl : e = 1 := by omega
    have hu := hcunit 1 (Nat.Prime.not_dvd_one hp) (C 0 0)
    have h0 : C ^ 1 - C 0 0 • (1 : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) = 0 := by
      ext a b
      rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
      simp
    rw [h0] at hu
    exact not_isUnit_zero hu
  have hinjBs : Function.Injective (fun b : Bs => fun i : Fin s =>
      ((NoOffPSLRest.spExp ψ A₀ ε C b i : ℕ) : ZMod p)) := by
    intro b b' hbb
    have hb := NoOffPSLRest.spExp_spec (hframe b b.2)
    have hb' := NoOffPSLRest.spExp_spec (hframe b' b'.2)
    have hmod : ∀ i, NoOffPSLRest.spExp ψ A₀ ε C b' i % p =
        NoOffPSLRest.spExp ψ A₀ ε C b i % p := by
      intro i
      have := congrFun hbb i
      simp only at this
      rw [ZMod.natCast_eq_natCast_iff'] at this
      exact this.symm
    exact Subtype.ext (hb.eq (hcongr hb' hmod))
  have hBsle : Nat.card Bs ≤ p ^ s := by
    calc Nat.card Bs ≤ Nat.card (Fin s → ZMod p) := Nat.card_le_card_of_injective _ hinjBs
      _ = p ^ s := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin s),
          Fintype.card_fin]
  have hs4 : 4 ≤ s := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard.trans hBsle)
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hnsF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [hcardF]
    exact hns
  have hrealX : ∀ k : Fin s → ℕ, ∃ X : StatedSp n (GaloisField 2 f),
      RootPlaneSp.SpBlockMat A₀ ε C X k := by
    intro k
    obtain ⟨b, -, X, -, hX⟩ := hreal k
    exact ⟨X, hX⟩
  have hmemBs : ∀ {X : StatedSp n (GaloisField 2 f)} {k : Fin s → ℕ},
      RootPlaneSp.SpBlockMat A₀ ε C X k → ψ X ∈ Bs := by
    intro X k hX
    obtain ⟨b', hb', hb'k⟩ := hreal k
    rw [hb'k.eq ⟨X, rfl, hX⟩] at hb'
    exact hb'
  have hC1 : IsUnit (C - 1) := by
    have := hcunit 1 (Nat.Prime.not_dvd_one hp) 1
    rwa [pow_one, one_smul] at this
  set i₀ : Fin s := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin s := ⟨1, by omega⟩ with hi₁
  have h01 : i₀ ≠ i₁ := fun h => by simp [hi₀, hi₁, Fin.ext_iff] at h
  obtain ⟨X, hX⟩ := hrealX (Pi.single i₀ 1)
  obtain ⟨X', hX'⟩ := hrealX (Pi.single i₁ 1)
  obtain ⟨d, hde, A₁, X₀, hX₀, h₁, h₂⟩ := exists_block_conj hC1 hrealX hN h01 hX hX'
  have hcardn : n + n = e * s + r := by
    have := Fintype.card_congr ε
    simpa [Fintype.card_sum, Fintype.card_prod, mul_comm] using this
  have hd3 : 3 * d ≤ n := by
    have := Nat.mul_le_mul_left e hs4
    omega
  have hwit : ∀ {Z : StatedSp n (GaloisField 2 f)} {k : Fin s → ℕ},
      RootPlaneSp.SpBlockMat A₀ ε C Z k → ¬ p ∣ k i₀ →
        (∀ i, i ≠ i₀ → i ≠ i₁ → p ∣ k i) → GGSixBstarWit p Bs G₀ t f (ψ Z) := by
    intro Z k hZ hk0 hk
    have hZ1 : Z ≠ 1 := ne_one_of_spBlockMat (by omega) hcunit hZ hk0
    obtain ⟨L₂, hL₂, hL₂c⟩ := SevSpNs.direct_of_two_supp hp hp2 hnsF he2 hs4 hCp hcunit hrealX
      hψ (fun b hb => hframe b hb) hZ hZ1 h01 hk
    refine ⟨hmemBs hZ, fun h => hZ1 (hψ (h.trans (map_one ψ).symm)), L₂, ?_, Or.inl hL₂c⟩
    rwa [← hrange]
  refine ⟨d, by omega, hd3, A₁, X₀, hX₀, ?_, ?_⟩
  · rw [h₁]
    exact hwit hX (by simpa using hp.not_dvd_one) fun i hi _ => by simp [Pi.single_eq_of_ne hi]
  · have e₁ : A₁ * (X₀ * (permSp (GaloisField 2 f) (WitSpNs.blockSwap n d) * X₀ *
        (permSp (GaloisField 2 f) (WitSpNs.blockSwap n d))⁻¹)) * A₁⁻¹ = X * X' := by
      rw [← h₁, ← h₂]
      group
    rw [e₁]
    refine hwit (SevSpNs.spBlockMat_mul hX hX') ?_ fun i hi hi' => ?_
    · simpa [Pi.single_eq_of_ne h01] using hp.not_dvd_one
    · simp [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi']

section Inputs

theorem ggSpBlockWitnessInputOn_nonsplit_all :
    GGSpBlockWitnessInputOn fun _ f p => ¬ p ∣ 2 ^ f - 1 := by
  intro G _ _ p B Bs x L D J n f ψ hns hctx s1
  have hadm := hctx.2.2.2.1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact s1.1
  have hcard : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
    have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
    have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hctx.prime.pos hr4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  exact blockWitness_core hadm.2.1 hadm.2.2.1 hctx.2.2.2.2.1.2 hCψ hctx.prime hctx.ne_two
    hctx.bstar hctx.range_eq (fun b hb => hctx.2.2.2.2.2.2.1.2 b hb) hcard hns .PSp

theorem ggSpBlockWitnessInputOn_nonsplit_rest :
    GGSpBlockWitnessInputOn fun _ f p => ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1 :=
  fun G _ _ p B Bs x L D J n f ψ hP =>
    ggSpBlockWitnessInputOn_nonsplit_all G p B Bs x L D J n f ψ hP.1

theorem ggSixRootFusionWitnessOn_PSpNonsplit_blk :
    GGSixRootFusionWitnessOn fun t _ f p => t = .PSp ∧ ¬ p ∣ 2 ^ f - 1 :=
  ggSixRootFusionWitnessOn_PSp_of_blockWitness ggSpBlockWitnessInputOn_nonsplit_all
    spBlockFixOrSwapInput_holds

theorem ggSixRootFusionWitClRest2_of_omega
    (hPlus : GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaPlus))
    (hMinus : GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaMinus)) :
    GGSixRootFusionWitClRest2 :=
  ⟨ggSpBlockWitnessInputOn_nonsplit_rest, spBlockFixOrSwapInput_holds, hPlus, hMinus⟩

theorem ggSixRootFusionWitClRest_of_omega
    (hPlus : GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaPlus))
    (hMinus : GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaMinus)) :
    GGSixRootFusionWitClRest :=
  ggSixRootFusionWitClRest_of_rest2 (ggSixRootFusionWitClRest2_of_omega hPlus hMinus)

theorem ggSixRootFusionWitnessInputFor_otherClassical_of_omega
    (hPlus : GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaPlus))
    (hMinus : GGSixRootFusionWitnessOn (fun t _ _ _ => t = .POmegaMinus)) :
    GGSixRootFusionWitnessInputFor GGOtherClassicalTag :=
  ggSixRootFusionWitnessInputFor_otherClassical_of_rest2
    (ggSixRootFusionWitClRest2_of_omega hPlus hMinus)

end Inputs

end CFSG.StandardType
