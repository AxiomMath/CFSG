module

public import CFSG.LocalAnalysis.StandardType.GGTorusReflFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6PlusRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Sylow
public import CFSG.LocalAnalysis.StandardType.GGTwE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem exists_twE6PlusTorusFrame
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n p : ℕ} [NeZero p] (hp : p.Prime)
    (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    {E : Subgroup (twistedE6RootGroup K σ)} (hE : IsElemAbelian p E)
    (hE3 : p ^ 3 ≤ Nat.card E) (hE5 : p ^ 5 ≤ Nat.card E)
    (hSC : ∀ g : twistedE6RootGroup K σ, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ (F : TwE6Frame K σ n p E) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
      (T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ),
      ExcIsLongest TwistTag.E6.tag F.v ∧ Function.Injective T ∧ T.range = E ∧
      ∀ t : Fin Tag.E6.rank → ZMod p,
        ggKGTwY F (T (Multiplicative.ofAdd t)) =
          rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t) := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, -, hvF⟩ :=
    ExcTwE6Nons.twE6SCTorusInput_nonsplit σ hp hp5 hK hσ hpq E hE hE3 hE5 hSC
  have hv : ExcIsLongest TwistTag.E6.tag F.v := hvF hpq
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ζ, hζp⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) (ℓ := 2) Nat.prime_two hp hp2
  have hζ : ζ ^ p = 1 := hζp.pow_eq_one
  obtain ⟨T, hTinj, hTE, hT⟩ :=
    TwE6PlusRootGen.exists_twE6PlusTorus hK hσ hp5 hpq F hv hζp.eq_orderOf.symm hζ
  exact ⟨F, ζ, hζ, T, hv, hTinj, hTE, hT⟩

private theorem exists_twE6PlusKillingRoot
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1)
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (H : Subgroup (twistedE6RootGroup K σ)) (hE : IsElemAbelian p E) (hHE : H ≤ E)
    (hH5 : p ^ 5 ≤ Nat.card H)
    (hUex : ∃ U : Subgroup (twistedE6RootGroup K σ), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) :
    ∃ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α ∧
      ∀ h ∈ H, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        ggKGTwY F h = rootDiagUnit TwistTag.E6.tag a ∧ rootChar a α = 1 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  obtain ⟨U, hU1, hU2, hUN⟩ := hUex
  have hAcard : Nat.card (H.map (twistedE6RootGroup K σ).subtype) = Nat.card H :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hAI : H.map (twistedE6RootGroup K σ).subtype ≤ twistedE6InndiagGL K σ :=
    (Subgroup.map_subtype_le H).trans le_sup_left
  have hA : IsElemAbelian p (H.map (twistedE6RootGroup K σ).subtype) :=
    (hE.mono hHE).map (twistedE6RootGroup K σ).subtype
  have hAU : TwE6RootKill.TwNormTwo K σ (H.map (twistedE6RootGroup K σ).subtype) := by
    refine ⟨U.map (twistedE6RootGroup K σ).subtype, Subgroup.map_subtype_le U, ?_, hU2.map _, ?_⟩
    · exact (Subgroup.map_eq_bot_iff_of_injective U (Subgroup.subtype_injective _)).not.2 hU1
    · rintro _ ⟨h, hh, rfl⟩ _ ⟨u, hu, rfl⟩
      exact ⟨h * u * h⁻¹, hUN h hh u hu, by simp⟩
  let D : TwLangData K σ (2 ^ n) (H.map (twistedE6RootGroup K σ).subtype) :=
    { v := F.v, Fr := F.Fr, hFr := F.fr_eq, g0 := F.g0, hg0C := F.g0_mem, hg0 := F.lang,
      c := 1, hcI := Subgroup.one_mem _,
      hc := by
        rintro _ ⟨h, hh, rfl⟩
        refine ⟨_, ((F.mem_iff h).1 (hHE hh)).2, ?_⟩
        simp [MulAut.conj_apply, mul_assoc] }
  have hpow : p ^ (if p = 3 then 4 else 5) ≤ p ^ 5 :=
    Nat.pow_le_pow_right hp.pos (by split_ifs <;> omega)
  obtain ⟨α, hα, hkill⟩ := TwE6RootKill.rootKill_of_ennolaKill_weylKill
      (TwE6RootKill.ennolaKill_of_steps TwE6RootKill.leviSplitStep_holds
          TwE6RootKill.ennolaSplitStep_holds) TwE6RootKill.weylKill_holds K σ (2 ^ n) hK hσ (ringChar.eq K 2) p hp
    hpq _ hAI hA (by rw [hAcard]; exact hpow.trans hH5) hAU D
  refine ⟨α, hα, fun h hh => ?_⟩
  obtain ⟨a, ha, hα1⟩ := hkill _ ⟨h, hh, rfl⟩
  exact ⟨a, by rw [ggKGTwY_apply, ha]; simp [D], hα1⟩

private theorem exists_twE6PlusWeylReflection
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (hv : ExcIsLongest TwistTag.E6.tag F.v) (α : Fin TwistTag.E6.tag.rank → ℤ)
    (hα : IsRoot TwistTag.E6.tag α) :
    ∃ r : twistedE6RootGroup K σ,
      ggKGTwY F r =
        canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection α) := by
  obtain ⟨r, -, hrY⟩ := ggKGTwJ_weyl hK hσ F hv hα
  exact ⟨r, hrY⟩

private theorem card_fix_ggKGTwY_conj
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {p : ℕ} [Fact p.Prime]
    {E : Subgroup (twistedE6RootGroup K σ)}
    (T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ)
    (hTinj : Function.Injective T) (hTE : T.range = E)
    (α : Fin TwistTag.E6.tag.rank → ℤ) (hα : IsRoot TwistTag.E6.tag α)
    (r : twistedE6RootGroup K σ)
    (hconj : ∀ t : Fin Tag.E6.rank → ZMod p, r * T (Multiplicative.ofAdd t) * r⁻¹ =
      T (Multiplicative.ofAdd (ExcSplitRootGen.excRefl (τ := Tag.E6) (p := p) α t)))
    (hTmem : ∀ e : twistedE6RootGroup K σ, e ∈ E ↔ ∃ t : Fin Tag.E6.rank → ZMod p,
      T (Multiplicative.ofAdd t) = e)
    (hp2 : p ≠ 2) :
    Nat.card {e : E // r * (e : twistedE6RootGroup K σ) * r⁻¹ = e} * p = Nat.card E := by
  classical
  have hfix : Nat.card {e : E // r * (e : twistedE6RootGroup K σ) * r⁻¹ = e} =
      Nat.card {t : Fin Tag.E6.rank → ZMod p //
        ExcSplitRootGen.excRefl (τ := Tag.E6) (p := p) α t = t} := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun t : {t : Fin Tag.E6.rank → ZMod p //
          ExcSplitRootGen.excRefl (τ := Tag.E6) (p := p) α t = t} =>
        (⟨⟨T (Multiplicative.ofAdd t.1), (hTmem _).2 ⟨_, rfl⟩⟩, by rw [hconj, t.2]⟩ :
          {e : E // r * (e : twistedE6RootGroup K σ) * r⁻¹ = e})) ⟨?_, ?_⟩)).symm
    · intro a b hab
      have := congrArg (fun e : {e : E // r * (e : twistedE6RootGroup K σ) * r⁻¹ = e} =>
        ((e : E) : twistedE6RootGroup K σ)) hab
      exact Subtype.ext (Multiplicative.ofAdd.injective (hTinj this))
    · rintro ⟨⟨e, he⟩, hfe⟩
      obtain ⟨t, rfl⟩ := (hTmem e).1 he
      refine ⟨⟨t, ?_⟩, rfl⟩
      rw [hconj] at hfe
      exact Multiplicative.ofAdd.injective (hTinj hfe)
  have hEcard : Nat.card E = p ^ Tag.E6.rank := by
    rw [← hTE, Nat.card_congr (MonoidHom.ofInjective hTinj).toEquiv.symm]
    simp [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]
  rw [hfix, hEcard]
  exact ExcSplitRootGen.card_fix_excRefl hp2 hα

private theorem ggKGTwY_isReflAt
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} [Fact p.Prime] [NeZero p]
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) (ζ : (AlgebraicClosure K)ˣ) (hζ : ζ ^ p = 1)
    (T : Multiplicative (Fin Tag.E6.rank → ZMod p) →* twistedE6RootGroup K σ)
    (hTinj : Function.Injective T) (hTE : T.range = E)
    (hT : ∀ t : Fin Tag.E6.rank → ZMod p,
      ggKGTwY F (T (Multiplicative.ofAdd t)) =
        rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ t))
    (α : Fin TwistTag.E6.tag.rank → ℤ) (hα : IsRoot TwistTag.E6.tag α)
    (r : twistedE6RootGroup K σ)
    (hrY : ggKGTwY F r =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection α))
    (hp2 : p ≠ 2) : GGKGIsReflAt p E r := by
  classical
  have hα' : IsRoot Tag.E6 α := hα
  have hconj : ∀ t : Fin Tag.E6.rank → ZMod p, r * T (Multiplicative.ofAdd t) * r⁻¹ =
      T (Multiplicative.ofAdd (ExcSplitRootGen.excRefl (τ := Tag.E6) (p := p) α t)) :=
    fun t => TwE6PlusRootGen.conj_twE6PlusTorus F hζ hT hrY t
  have hTmem : ∀ e : twistedE6RootGroup K σ, e ∈ E ↔ ∃ t : Fin Tag.E6.rank → ZMod p,
      T (Multiplicative.ofAdd t) = e := by
    intro e
    rw [← hTE, MonoidHom.mem_range]
    exact ⟨fun ⟨m, hm⟩ => ⟨Multiplicative.toAdd m, hm⟩, fun ⟨t, ht⟩ => ⟨_, ht⟩⟩
  refine ⟨?_, ?_, card_fix_ggKGTwY_conj T hTinj hTE α hα r hconj hTmem hp2⟩
  · refine Subgroup.mem_normalizer_iff.2 fun e => ⟨fun he => ?_, fun he => ?_⟩
    · obtain ⟨t, rfl⟩ := (hTmem e).1 he
      rw [hconj]
      exact (hTmem _).2 ⟨_, rfl⟩
    · obtain ⟨t, ht⟩ := (hTmem _).1 he
      have h1 : T (Multiplicative.ofAdd t) =
          r * T (Multiplicative.ofAdd (ExcSplitRootGen.excRefl (τ := Tag.E6) (p := p) α t)) *
            r⁻¹ := by
        rw [hconj, ExcSplitRootGen.excRefl_excRefl hα']
      have h2 : e = T (Multiplicative.ofAdd
          (ExcSplitRootGen.excRefl (τ := Tag.E6) (p := p) α t)) := by
        have h3 : r * e * r⁻¹ = r * T (Multiplicative.ofAdd
            (ExcSplitRootGen.excRefl (τ := Tag.E6) (p := p) α t)) * r⁻¹ := by
          exact ht.symm.trans h1
        simpa using h3
      exact (hTmem _).2 ⟨_, h2.symm⟩
  · intro e he
    obtain ⟨t, rfl⟩ := (hTmem e).1 he
    rw [hconj, hconj, ExcSplitRootGen.excRefl_excRefl hα']

private theorem ggKGTwY_centralizes_of_rootKill
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) (H : Subgroup (twistedE6RootGroup K σ))
    (α : Fin TwistTag.E6.tag.rank → ℤ) (hα : IsRoot TwistTag.E6.tag α)
    (r : twistedE6RootGroup K σ)
    (hrY : ggKGTwY F r =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection α))
    (hkill : ∀ h ∈ H, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      ggKGTwY F h = rootDiagUnit TwistTag.E6.tag a ∧ rootChar a α = 1) :
    ∀ h ∈ H, r * h = h * r := by
  intro h hh
  obtain ⟨a, hya, hα1⟩ := hkill h hh
  have hfixa : rootDiagUnit TwistTag.E6.tag a =
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection α) *
        rootDiagUnit TwistTag.E6.tag a *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
          (rootReflection α))⁻¹ := by
    refine (rootDiagUnit_eq_conj_canonicalRep_iff a a _).2 fun v => ?_
    rw [rootReflection_smul hα v, sub_eq_add_neg, rootChar_add, ← neg_smul, rootChar_zsmul,
      hα1, one_zpow, mul_one]
  have hY : ggKGTwY F (r * h * r⁻¹) = ggKGTwY F h := by
    rw [map_mul, map_mul, map_inv, hrY, hya, ← hfixa]
  have hY_inj : Function.Injective (ggKGTwY F) := by
    intro x y hxy
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    have h3 : F.g0 * ggKGTwY F x * F.g0⁻¹ = F.g0 * ggKGTwY F y * F.g0⁻¹ := by rw [hxy]
    rw [ggKGTwY_apply, ggKGTwY_apply] at h3
    simpa [mul_assoc] using h3
  have := hY_inj hY
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem ggKGReflFix_twE6Plus
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1) :
    GGKGReflFix p 5 (twistedE6RootGroup K σ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  intro E H hE hSC hHE hH5 hUex
  have hE5 : p ^ 5 ≤ Nat.card E := hH5.trans (Subgroup.card_le_of_le hHE)
  have hE3 : p ^ 3 ≤ Nat.card E := (Nat.pow_le_pow_right hp.pos (by norm_num)).trans hE5
  obtain ⟨F, ζ, hζ, T, hv, hTinj, hTE, hT⟩ :=
    exists_twE6PlusTorusFrame (E := E) σ hp hp5 hK hσ hpq hE hE3 hE5 hSC
  obtain ⟨α, hα, hkill⟩ :=
    exists_twE6PlusKillingRoot hp hK hσ hpq (E := E) F H hE hHE hH5 hUex
  obtain ⟨r, hrY⟩ := exists_twE6PlusWeylReflection hK hσ F hv α hα
  exact ⟨r, ggKGTwY_isReflAt F ζ hζ T hTinj hTE hT α hα r hrY hp2,
    ggKGTwY_centralizes_of_rootKill F H α hα r hrY hkill⟩

end CFSG.StandardType

end
