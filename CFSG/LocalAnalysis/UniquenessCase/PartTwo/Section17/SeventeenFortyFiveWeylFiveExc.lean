module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveNative
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
import CFSG.RankThree.PartOne.K133H.G2Plane
import CFSG.RankThree.PartOne.K133H.F4Weyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalGroups.Orthogonal
  CFSG.TauCetiBridge.BigCell CFSG.TauCetiBridge.Even
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open Subgroup

private theorem weylFivePower_adjointGroup_of_normalForm
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 31) (hNF : InnerFieldNormalForm τ K)
    (hW : ¬ 5 ∣ Nat.card (WeylGroup τ)) : WeylFivePower (adjointGroup τ K) := by
  intro α E _ hexp _ hEinv
  obtain ⟨g, σ, hgσ⟩ := hNF α
  have hα : ∀ x : adjointGroup τ K,
      (α x : ModGL τ K) =
        ((g : ModGL τ K) * rootDiagUnit τ (1 : Fin τ.rank → Kˣ)) *
          Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
          ((g : ModGL τ K) * rootDiagUnit τ (1 : Fin τ.rank → Kˣ))⁻¹ := by
    intro x
    rw [rootDiagUnit_one, mul_one]
    exact hgσ x
  obtain ⟨k, hk⟩ := weylFive_native (τ := τ) hτ hK (G := adjointGroup τ K) le_rfl
    (g : ModGL τ K) g.2 (1 : Fin τ.rank → Kˣ) σ α hα E hexp hEinv
  exact ⟨Nat.card (WeylGroup τ), k, hW, hk⟩

private theorem weylFivePower_adjointGroup_G2_three
    {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hKf : Nat.card K = 3 ^ f) : WeylFivePower (adjointGroup Tag.G2 K) := by
  have hchar : ringChar K = 3 := ringChar_eq_of_card_eq Nat.prime_three hf hKf
  have hcharP : CharP K 3 := by simpa [hchar] using ringChar.charP K
  exact
    letI : CharP K 3 := hcharP
    letI : CharP K ReeTag.G2.prime := hcharP
    by
      have hK31 : ringChar K ≠ 31 := by rw [hchar]; norm_num
      intro α E _ hexp _ hEinv
      have hEinv2 : E.map (α ^ 2).toMonoidHom = E := map_pow_of_map_eq hEinv 2
      obtain ⟨g, k, hαeq⟩ := G2_exists_conj_mul_pow (K := K) hf hKf α
      let σ : K ≃+* K := frobeniusEquiv K 3
      have hσ : ∀ c, σ c = c ^ 3 := fun c => frobeniusEquiv_def K 3 c
      let φ : MulAut ↥(adjointGroup Tag.G2 K) := ReeTag.G2.finiteExceptionalAut K
      let g₀ : ↥(adjointGroup Tag.G2 K) := g
      have hαeq' : α = MulAut.conj g₀ * φ ^ k := hαeq
      let g' : ↥(adjointGroup Tag.G2 K) := g₀ * (φ ^ k) g₀
      have hsq : α ^ 2 = MulAut.conj g' * φ ^ (2 * k) := by
        have hstep := CFSG.LieType.Chevalley.mulAut_mul_conj (φ ^ k) g₀
        rw [hαeq', pow_two]
        calc (MulAut.conj g₀ * φ ^ k) * (MulAut.conj g₀ * φ ^ k) =
              MulAut.conj g₀ * (φ ^ k * MulAut.conj g₀) * φ ^ k := by group
          _ = MulAut.conj g₀ * (MulAut.conj ((φ ^ k) g₀) * φ ^ k) * φ ^ k := by rw [hstep]
          _ = (MulAut.conj g₀ * MulAut.conj ((φ ^ k) g₀)) * (φ ^ k * φ ^ k) := by group
          _ = MulAut.conj g' * φ ^ (2 * k) := by
              rw [← map_mul, show 2 * k = k + k by ring, pow_add]
      have hα2 : ∀ x : adjointGroup Tag.G2 K,
          ((α ^ 2) x : ModGL Tag.G2 K) =
            ((g' : ModGL Tag.G2 K) * rootDiagUnit Tag.G2 (1 : Fin Tag.G2.rank → Kˣ)) *
              Units.map (entrywiseHom (σ ^ k).toRingHom) (x : ModGL Tag.G2 K) *
              ((g' : ModGL Tag.G2 K) *
                rootDiagUnit Tag.G2 (1 : Fin Tag.G2.rank → Kˣ))⁻¹ := by
        intro x
        rw [rootDiagUnit_one, mul_one, hsq]
        exact conj_eq_of_even hσ g' k x
      obtain ⟨k', hk'⟩ := weylFive_native (τ := Tag.G2) (Or.inl rfl) hK31
        (G := adjointGroup Tag.G2 K) le_rfl (g' : ModGL Tag.G2 K) g'.2
        (1 : Fin Tag.G2.rank → Kˣ) (σ ^ k) (α ^ 2) hα2 E hexp hEinv2
      refine ⟨2 * Nat.card (WeylGroup Tag.G2), k', ?_, ?_⟩
      · rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2]
        norm_num
      · intro x hx
        rw [pow_mul]
        exact hk' x hx

theorem weylFivePower_G2
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hp2 : q.p ≠ 2) (hp31 : q.p ≠ 31) :
    WeylFivePower (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group := by
  have hq3 : 3 ≤ q.p ^ q.exponent := by
    rw [← TauCeti.PrimePower.card_def]
    exact (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
      ((TauCeti.LieTypeIndex.valid_iff (.G2 q)).1 hv).1
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, hq3⟩,
      untwistedChevalleyModel_of_bridge chevalleyBridgesAll.g2 (MulEquiv.refl _)⟩
  obtain ⟨K, hfield, hfinite, hcard, ⟨e⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .G2 hm.2
  exact
    letI : Field K := hfield
    letI : Finite K := hfinite
    by
      have hchar : ringChar K = q.p :=
        ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
      have hK31 : ringChar K ≠ 31 := by rw [hchar]; exact hp31
      have hpow : WeylFivePower (adjointGroup Tag.G2 K) := by
        by_cases h3 : q.p = 3
        · have hK3f : Nat.card K = 3 ^ q.exponent := by
            rw [h3] at hcard
            exact hcard
          exact weylFivePower_adjointGroup_G2_three q.exponent_pos hK3f
        · exact weylFivePower_adjointGroup_of_normalForm (Or.inl rfl) hK31
            (innerFieldNormalForm_G2 q.prime_p hp2 h3 q.exponent_pos K hcard) (by
              rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_G2]
              norm_num)
      exact WeylFivePower.of_mulEquiv e.symm hpow

theorem weylFivePower_F4
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    (hp2 : q.p ≠ 2) (hp31 : q.p ≠ 31) :
    WeylFivePower (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group .F4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      untwistedChevalleyModel_of_bridge chevalleyBridgesAll.f4 (MulEquiv.refl _)⟩
  obtain ⟨K, hfield, hfinite, hcard, ⟨e⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .F4 hm.2
  exact
    letI : Field K := hfield
    letI : Finite K := hfinite
    by
      have hchar : ringChar K = q.p :=
        ringChar_eq_of_card_eq q.prime_p q.exponent_pos hcard
      have hK31 : ringChar K ≠ 31 := by rw [hchar]; exact hp31
      have hpow : WeylFivePower (adjointGroup Tag.F4 K) :=
        weylFivePower_adjointGroup_of_normalForm (Or.inr (Or.inr rfl)) hK31
          (innerFieldNormalForm_F4 q.prime_p hp2 q.exponent_pos K hcard) (by
            rw [CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
            norm_num)
      exact WeylFivePower.of_mulEquiv e.symm hpow

theorem weylFivePower_trialityD4
    {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp2 : q.p ≠ 2) (hp31 : q.p ≠ 31) :
    WeylFivePower (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  obtain ⟨K, hfield, hfinite, σ, hK, hσ, -, ⟨eB⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  exact
    letI : Field K := hfield
    letI : Finite K := hfinite
    by
      have hK3 : Nat.card K = q.p ^ (3 * q.exponent) := by
        rw [hK, ← pow_mul, Nat.mul_comm q.exponent 3]
      have hchar : ringChar K = q.p :=
        ringChar_eq_of_card_eq (f := 3 * q.exponent) q.prime_p
          (by have := q.exponent_pos; omega) hK3
      have hK31 : ringChar K ≠ 31 := by rw [hchar]; exact hp31
      have hC0le : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≤ adjointGroup Tag.D4 K :=
        (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom).trans inf_le_left
      have hpow : WeylFivePower ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
        intro α E _ hexp _ hEinv
        obtain ⟨hval, hnf, -⟩ :=
          odd_triality_exact_automorphism_normal_form q.prime_p hp2 q.exponent_pos K hK σ hσ
        obtain ⟨⟨g, δ⟩, hαeq, -⟩ := hnf α
        have hα : ∀ x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
            (α x : ModGL TwistTag.D4.tag K) =
              ((g : ModGL TwistTag.D4.tag K) *
                  rootDiagUnit TwistTag.D4.tag (1 : Fin TwistTag.D4.tag.rank → Kˣ)) *
                Units.map (entrywiseHom δ.toRingHom) (x : ModGL TwistTag.D4.tag K) *
                ((g : ModGL TwistTag.D4.tag K) *
                  rootDiagUnit TwistTag.D4.tag (1 : Fin TwistTag.D4.tag.rank → Kˣ))⁻¹ := by
          intro x
          rw [rootDiagUnit_one, mul_one]
          calc (α x : ModGL TwistTag.D4.tag K)
              = (((MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ) x :
                  ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
                    ModGL TwistTag.D4.tag K) := by rw [hαeq]
            _ = ((g * fieldActor (t := TwistTag.D4) σ δ x * g⁻¹ :
                  ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
                    ModGL TwistTag.D4.tag K) := by rw [MulAut.mul_apply, MulAut.conj_apply]
            _ = (g : ModGL TwistTag.D4.tag K) *
                  ((fieldActor (t := TwistTag.D4) σ δ x :
                    ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
                    ModGL TwistTag.D4.tag K) * (g : ModGL TwistTag.D4.tag K)⁻¹ := by
                simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            _ = (g : ModGL TwistTag.D4.tag K) * Units.map (entrywiseHom δ.toRingHom)
                  (x : ModGL TwistTag.D4.tag K) * (g : ModGL TwistTag.D4.tag K)⁻¹ := by
                rw [hval δ x]
        obtain ⟨k, hk⟩ := weylFive_native (τ := Tag.D4) (Or.inr (Or.inl rfl)) hK31 hC0le
          (g : ModGL TwistTag.D4.tag K) (hC0le g.2) (1 : Fin Tag.D4.rank → Kˣ) δ α hα E hexp
          hEinv
        refine ⟨Nat.card (WeylGroup Tag.D4), k, ?_, hk⟩
        change ¬ 5 ∣ Nat.card (WeylGroup (TwistTag.tag TwistTag.D4))
        exact CFSG.RankThree.PartOne.KGD.not_dvd_card_weylGroup_D4 (p := 5) Nat.prime_five
          (by norm_num)
      exact WeylFivePower.of_mulEquiv eB.symm hpow

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
