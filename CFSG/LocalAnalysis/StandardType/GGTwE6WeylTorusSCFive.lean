module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusAut
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6Tools
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6FiveFix
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section SCFive


theorem twistedE6SCUnique_five {f : ℕ} (hf : 1 ≤ f) (h5 : 5 ∣ 2 ^ f + 1) (K : Type) [Field K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {A A' : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)} (hA : IsElemAbelian 5 A)
    (hA4 : 5 ^ 4 ≤ Nat.card A)
    (hSC : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ), (∀ a ∈ A, c * a = a * c) →
      c ^ 5 = 1 → c ∈ A)
    (hA' : IsElemAbelian 5 A') (hA4' : 5 ^ 4 ≤ Nat.card A')
    (hSC' : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ), (∀ a ∈ A', c * a = a * c) →
      c ^ 5 = 1 → c ∈ A') :
    ∃ c : ↥(graphFixedRootGroup TwistTag.E6 K σ), A' = A.map (MulAut.conj c).toMonoidHom := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : NeZero (5 : ℕ) := ⟨by norm_num⟩
  letI modulePi : Module (ZMod 5) (Fin 6 → ZMod 5) := inferInstance
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (by norm_num))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  obtain ⟨ζK, hζ, g₀, T, ι₀, hζKord, hg₀C, _htwist, hι₀, hbase, hTcomm, hrangeT, htors,
    hjcard, hcent⟩ :=
    exists_langFrame (p := 5) (by norm_num) hf h5 K hK σ hσ L Fr hFr
  obtain ⟨j, hj⟩ := hjcard
  have haut := langFrame_aut (p := 5) (by norm_num) hf K hK σ hσ L hζKord hζ hg₀C ι₀ hι₀
    hbase
  have hXel : IsElemAbelian 5 ι₀.range :=
    @NoOffE8Five.isElemAbelian_range_of_module 5 (Fact.mk Nat.prime_five)
      (Fin 6 → ZMod 5) ↥(graphFixedRootGroup TwistTag.E6 K σ) inferInstance modulePi inferInstance ι₀
  have hXp : ∀ x ∈ ι₀.range, x ^ 5 = 1 := fun x hx => hXel.2 x hx
  have hord : (Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ)).factorization 5 =
      (Nat.card ↥T).factorization 5 + 1 := by
    let σ' : K ≃+* K := RingEquiv.ofBijective σ (Finite.injective_iff_bijective.mp σ.injective)
    have hσ' : ∀ c, σ' c = c ^ (2 ^ f) := hσ
    have hcardH : Nat.card ↥(graphFixedRootGroup TwistTag.E6 K σ) =
        Nat.card ↥(twistedE6RootGroup K σ') := rfl
    rw [hcardH,
      CFSG.HardMathSupport.Timmesfeld.CrossChar.factorization_five_card_twistedE6_of_dvd_add_one
        Nat.prime_two hf K hK σ' hσ' h5]
    have hTF : (Nat.card ↥T).factorization 5 = 6 * (2 ^ f + 1).factorization 5 := by
      have hTne : Nat.card T ≠ 0 := (Nat.card_pos (α := T)).ne'
      have h3ne : 3 ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
      have hfac : (Nat.card T).factorization + (3 ^ j).factorization =
          6 • (2 ^ f + 1).factorization := by
        calc (Nat.card T).factorization + (3 ^ j).factorization
            = (Nat.card T * 3 ^ j).factorization := (Nat.factorization_mul hTne h3ne).symm
          _ = ((2 ^ f + 1) ^ 6).factorization := by rw [hj]
          _ = 6 • (2 ^ f + 1).factorization := Nat.factorization_pow _ _
      have h3fac : (3 ^ j).factorization 5 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (fun hd =>
          absurd (Nat.prime_five.dvd_of_dvd_pow hd) (by norm_num))
      have hfac5 := congrArg (fun g : ℕ →₀ ℕ => g 5) hfac
      rw [Finsupp.add_apply, h3fac, add_zero, Finsupp.smul_apply] at hfac5
      simpa using hfac5
    rw [hTF]
  have hfix : ∀ a ∈ Subgroup.normalizer (ι₀.range : Set ↥(graphFixedRootGroup TwistTag.E6 K σ)),
      a ^ 5 = 1 → (∃ x ∈ ι₀.range, a * x ≠ x * a) →
      Nat.card {x : ι₀.range // a * (x : ↥(graphFixedRootGroup TwistTag.E6 K σ)) =
          (x : ↥(graphFixedRootGroup TwistTag.E6 K σ)) * a} < 5 ^ 3 := by
    intro a ha ha5 hnc
    have hβ5 : (MulAut.conj a : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)) ^ 5 = 1 := by
      rw [← map_pow, ha5, map_one]
    have hstab : ∀ b ∈ ι₀.range, (MulAut.conj a) b ∈ ι₀.range := by
      intro b hb
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp ha b).mp hb
    obtain ⟨w, c, _hc0, hc1, hw⟩ := haut (MulAut.conj a) hstab
    let wE : WeylGroup .E6 := w
    have hwE : ∀ s : Fin Tag.E6.rank → ZMod 5,
        (MulAut.conj a) (ι₀ (Multiplicative.ofAdd s)) =
          ι₀ (Multiplicative.ofAdd (c • TableBExc.torusAct .E6 5 wE s)) := hw
    have hc : c = 1 := hc1 hβ5
    have hwT : ∀ s : Fin Tag.E6.rank → ZMod 5,
        (MulAut.conj a) (ι₀ (Multiplicative.ofAdd s)) =
          ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 wE s)) := by
      intro s
      rw [hwE s, hc, one_smul]
    have hwne : wE ≠ 1 := by
      intro hw1
      obtain ⟨x, hx, hne⟩ := hnc
      obtain ⟨s, rfl⟩ := hx
      let sT : Fin Tag.E6.rank → ZMod 5 := Multiplicative.toAdd s
      have hconj : a * ι₀ (Multiplicative.ofAdd sT) * a⁻¹ =
          ι₀ (Multiplicative.ofAdd sT) := by
        have h := hwT sT
        rw [hw1, TableBExc.torusAct_one (τ := Tag.E6) (p := 5)] at h
        simpa only [MulAut.conj_apply] using h
      apply hne
      have h2 : a * ι₀ (Multiplicative.ofAdd sT) =
          ι₀ (Multiplicative.ofAdd sT) * a := by
        calc a * ι₀ (Multiplicative.ofAdd sT)
            = (a * ι₀ (Multiplicative.ofAdd sT) * a⁻¹) * a := by group
          _ = ι₀ (Multiplicative.ofAdd sT) * a := by rw [hconj]
      exact h2
    have hw5 : wE ^ 5 = 1 := by
      apply NoOffExc.eq_one_of_torusAct (p := 5) (by norm_num)
      intro x
      have hiter : ∀ k : ℕ, ∀ s : Fin Tag.E6.rank → ZMod 5,
          ((MulAut.conj a) ^ k) (ι₀ (Multiplicative.ofAdd s)) =
            ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 (wE ^ k) s)) := by
        intro k
        induction k with
        | zero =>
          intro s
          rw [pow_zero, MulAut.one_apply, pow_zero,
            TableBExc.torusAct_one (τ := Tag.E6) (p := 5)]
        | succ k ih =>
          intro s
          rw [pow_succ, MulAut.mul_apply, hwT s, ih (TableBExc.torusAct .E6 5 wE s),
            ← TableBExc.torusAct_mul, ← pow_succ]
      have h1 : ((MulAut.conj a) ^ 5) (ι₀ (Multiplicative.ofAdd x)) =
          ι₀ (Multiplicative.ofAdd x) := by
        rw [hβ5, MulAut.one_apply]
      rw [hiter 5 x] at h1
      exact Multiplicative.ofAdd.injective (hι₀ h1)
    have hworder : orderOf wE = 5 := orderOf_eq_prime hw5 hwne
    let e : ι₀.range ≃ (Fin Tag.E6.rank → ZMod 5) :=
      (MonoidHom.ofInjective hι₀).toEquiv.symm.trans Multiplicative.toAdd
    have he : ∀ y : ι₀.range,
        ι₀ (Multiplicative.ofAdd (e y)) =
          (y : ↥(graphFixedRootGroup TwistTag.E6 K σ)) := by
      intro y
      change ι₀ (Multiplicative.ofAdd (Multiplicative.toAdd
        ((MonoidHom.ofInjective hι₀).symm y))) = (y : ↥(graphFixedRootGroup TwistTag.E6 K σ))
      rw [ofAdd_toAdd]
      exact MonoidHom.apply_ofInjective_symm hι₀ y
    have hcardFix : Nat.card {x : ι₀.range // a * (x : ↥(graphFixedRootGroup TwistTag.E6 K σ)) =
          (x : ↥(graphFixedRootGroup TwistTag.E6 K σ)) * a} ≤
        Nat.card {s : Fin Tag.E6.rank → ZMod 5 // TableBExc.torusAct .E6 5 wE s = s} := by
      refine Nat.card_le_card_of_injective (fun y => ⟨e y.1, ?_⟩) ?_
      · have hy : (MulAut.conj a) (y.1 : ↥(graphFixedRootGroup TwistTag.E6 K σ)) =
            (y.1 : ↥(graphFixedRootGroup TwistTag.E6 K σ)) := by
          rw [MulAut.conj_apply]
          calc a * (y.1 : ↥(graphFixedRootGroup TwistTag.E6 K σ)) * a⁻¹ =
              ((y.1 : ↥(graphFixedRootGroup TwistTag.E6 K σ)) * a) * a⁻¹ := by rw [← y.2]
            _ = (y.1 : ↥(graphFixedRootGroup TwistTag.E6 K σ)) := by group
        have h2 : ι₀ (Multiplicative.ofAdd (TableBExc.torusAct .E6 5 wE (e y.1))) =
            ι₀ (Multiplicative.ofAdd (e y.1)) := by
          rw [← hwT (e y.1), he y.1, hy]
        exact Multiplicative.ofAdd.injective (hι₀ h2)
      · intro y1 y2 h
        apply Subtype.ext
        exact e.injective (congrArg Subtype.val h)
    calc Nat.card {x : ι₀.range // a * (x : ↥(graphFixedRootGroup TwistTag.E6 K σ)) =
              (x : ↥(graphFixedRootGroup TwistTag.E6 K σ)) * a}
        ≤ Nat.card {s : Fin Tag.E6.rank → ZMod 5 // TableBExc.torusAct .E6 5 wE s = s} := hcardFix
      _ ≤ 5 ^ 2 := card_fix_torusAct_E6_five hworder
      _ < 5 ^ 3 := by norm_num
  have hSCc : ∀ c ∈ Subgroup.centralizer (A : Set ↥(graphFixedRootGroup TwistTag.E6 K σ)),
      c ^ 5 = 1 → c ∈ A :=
    fun c hc hc5 => hSC c (fun a ha => ((Subgroup.mem_centralizer_iff.mp hc) a ha).symm) hc5
  have hSCc' : ∀ c ∈ Subgroup.centralizer (A' : Set ↥(graphFixedRootGroup TwistTag.E6 K σ)),
      c ^ 5 = 1 → c ∈ A' :=
    fun c hc hc5 => hSC' c (fun a ha => ((Subgroup.mem_centralizer_iff.mp hc) a ha).symm) hc5
  obtain ⟨c₁, hc₁⟩ := exists_conj_map_eq_of_SC (p := 5) (T := T) (X := ι₀.range)
    hTcomm hrangeT hXp htors hord hcent hfix hA hA4 hSCc
  obtain ⟨c₂, hc₂⟩ := exists_conj_map_eq_of_SC (p := 5) (T := T) (X := ι₀.range)
    hTcomm hrangeT hXp htors hord hcent hfix hA' hA4' hSCc'
  refine ⟨c₂ * c₁⁻¹, ?_⟩
  calc A' = ι₀.range.map (MulAut.conj c₂).toMonoidHom := hc₂.symm
    _ = (ι₀.range.map (MulAut.conj c₁).toMonoidHom).map
        (MulAut.conj (c₂ * c₁⁻¹)).toMonoidHom := by
        rw [Subgroup.map_map]
        congr 1
        refine MonoidHom.ext fun z => ?_
        simp [MulAut.conj_apply]
        group
    _ = A.map (MulAut.conj (c₂ * c₁⁻¹)).toMonoidHom := by rw [hc₁]

end SCFive

end ExcFrames

end CFSG.StandardType
