module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmComp
public import CFSG.LocalAnalysis.StandardType.GGTBJOmModel
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJOmCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusForms
public import CFSG.LocalAnalysis.StandardType.GGTBJSuRow
public import CFSG.LocalAnalysis.StandardType.GGTBRowOFrameAux
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGTBJRowR4Narrow
import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
import CFSG.LocalAnalysis.StandardType.GGTBJOmDTwoCount
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

theorem TBJOmData.blockData_nf [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (hnf : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f₀ : Fin r → Multiplicative (ZMod p)) {J : Subgroup ↥(orthDerived Q)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({Δ.τΩ hA f₀} : Set ↥(orthDerived Q))))
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f} ≤ p ^ r) :
    ∃ (a : ZMod p) (P : Fin r → Prop),
      (∀ i, P i → toAdd (f₀ i) = a ∨ toAdd (f₀ i) = -a) ∧
      (∀ i k : Fin r, i ≠ k → P i → P k → toAdd (f₀ i) = toAdd (f₀ k) →
        ∃ n ∈ J, ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) f)) ∧
      (a ≠ 0 → ∀ i k : Fin r, P i → P k → toAdd (f₀ i) = a → toAdd (f₀ k) = -a →
        ∃ n ∈ J, ∀ f, n * Δ.τΩ hA f * n⁻¹ = Δ.τΩ hA (permAut (Equiv.swap i k) (dinv i k f))) ∧
      (a = 0 → 3 ≤ Nat.card {i : Fin r // P i}) ∧
      (∀ f : Fin r → Multiplicative (ZMod p),
        (∃ m : ZMod p, ∀ i, P i → toAdd (f i) = m * toAdd (f₀ i)) →
          ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f) := by
  classical
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  rcases component_cases hQ Fact.out hp2 (x := Δ.τΩ hA f₀) hx hJ with
    ⟨h, hh, hhX, rfl⟩ | ⟨F, hFq, hFle, hFn, hF4, rfl⟩
  · obtain ⟨a, P, ha, hP, hswap, hmixed, hcent⟩ := Δ.blockG_orthDerived hp2 hQ hA f₀ hh hhX
    exact ⟨a, P, hP, hswap, fun _ => hmixed, fun h0 => absurd h0 ha, hcent⟩
  · have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
    have hFc : CFSG.Assembly.IsComponentOf F (supportedFixedDerived Q (Δ.τ f₀)) :=
      ⟨hFle, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hFle).2 hFn.isSubnormal,
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hFq⟩
    have hcard : Nat.card {f : Fin r → Multiplicative (ZMod p) //
        ∀ j ∈ F.subgroupOf (orthDerived Q), Δ.τΩ hA f * j = j * Δ.τΩ hA f} =
        Nat.card {f : Fin r → Multiplicative (ZMod p) // ∀ j ∈ F, Δ.τ f * j = j * Δ.τ f} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun f =>
        ⟨fun h j hj => congrArg Subtype.val (h ⟨j, hFΩ hj⟩ (Subgroup.mem_subgroupOf.mpr hj)),
          fun h j hj => Subtype.ext (h (j : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hj))⟩)
    have h3 := Δ.three_le_card_zero_of_isComponentOf hp2 hQ hA hnf f₀ hFc
      (by rw [← hcard]; exact hcount)
    obtain ⟨hswapZ, hcentZ, hdim⟩ := Δ.blockZ_nf hp2 hQ hA f₀ h3
    have hFeq : F = supportedFixedDerived Q (Δ.τ f₀) := hF4.resolve_left fun h4 => by
      have h4' : finrank K (fixedSpace (Δ.τ f₀)) ≤ 4 := h4
      omega
    refine ⟨0, fun i => toAdd (f₀ i) = 0, fun i hi => Or.inl hi, fun i k hik hi hk _ => ?_,
      fun h => absurd rfl h, fun _ => h3, ?_⟩
    · obtain ⟨n, hn, hconj⟩ := hswapZ i k hik hi hk
      refine ⟨⟨n, hx.supportedFixedDerived_le_orthDerived hn⟩, ?_, fun f => Subtype.ext (hconj f)⟩
      rw [Subgroup.mem_subgroupOf, hFeq]
      exact hn
    · rintro f ⟨m, hm⟩ j hj
      exact Subtype.ext (hcentZ f (fun i hi => by simpa [hi] using hm i hi) (j : V ≃ₗ[K] V)
        (hFle (Subgroup.mem_subgroupOf.mp hj)))

end OrthTorus

open CFSG CFSG.Assembly TableB OrthExc
open CFSG.RankThree.Classical2 (orthDerived)

theorem ggTBJ_om_torusJNoncomm_nf
    {K : Type} [Field K] [Finite K] [CharP K 2] {m p r : ℕ} {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hm : 3 ≤ m) (hp : p.Prime) (hme : Even m)
    (hpq : p ∣ Nat.card K + 1)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* OrthRest.RMinus K m b c)
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r (OrthRest.RMinus K m b c)
      (Set.range (MulAut.conj : OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)))
      L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ (n₁ n₂ : L') (h₁ : MulAut.conj n₁ ∈ Subgroup.normalizer (A : Set (MulAut L')))
      (h₂ : MulAut.conj n₂ ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      n₁ ∈ J ∧ n₂ ∈ J ∧ GGTorusWeylElt p A n₁ ∧ GGTorusWeylElt p A n₂ ∧
      GGIsReflection p (ggConjAut A h₁) ∧ GGIsReflection p (ggConjAut A h₂) ∧
      ggConjAut A h₁ * ggConjAut A h₂ ≠ ggConjAut A h₂ * ggConjAut A h₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq
  obtain ⟨r', E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hnf⟩ :=
    ggTBJ_om_stdModel_nf hp hp2 hbc hm hme hpq ψ₀ A hA
  exact ggTBJ_om_torus_transport hp hp2 ψ₀ A hA Δ hE σ Θ hψσ hΘ hWeyl
    (fun f₀ J' hJ' hc' => by
      obtain ⟨a, P, hP, hswap, hmixed, h3, hcent⟩ :=
        Δ.blockData_nf hp2 (TableBOrth.nondegenerate_qMinusForm m hbc) hE hnf f₀ hJ' hc'
      exact ggTBJ_om_core_nf hp hp2 (Δ.τΩ hE) f₀ J' a P hP hswap hmixed h3 hcent hc')
    y hy hJ hcount

theorem ggO2Row_recipe_adjoint
    {m n p : ℕ} (hn : 1 ≤ n) (hm : 3 ≤ m) (hme : Even m) (hpn : p ∣ 2 ^ n + 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ (r m' n' : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
        (_ : R ≃* OrthRest.RMinus K m' b c),
        GGTorusLift p r R ∧ Nat.card K = 2 ^ n' ∧ 1 ≤ n' ∧
          (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ 3 ≤ m' ∧ Even m' ∧ p ∣ 2 ^ n' + 1 ∧
          ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0, m, n, K, inferInstance,
    inferInstance, b, c, MulEquiv.refl _,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus hm b c hbc), hK, hn, hbc, hm, hme, hpn,
    fun φ hφ => hφ⟩

theorem ggO2Row_labelAll_adjoint
    {p : ℕ} {lab : LargeEvenLabel} (hq : 1 ≤ lab.n) (h : GGTBRowR5O2 p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (r m n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (b c : K)
        (_ : R ≃* OrthRest.RMinus K m b c),
        GGTorusLift p r R ∧ Nat.card K = 2 ^ n ∧ 1 ≤ n ∧
          (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ 3 ≤ m ∧ Even m ∧ p ∣ 2 ^ n + 1 ∧
          ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, h4, hodd, hpn⟩ := h
  subst htag
  dsimp only at h4 hodd hpn hq
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · refine ggO2Row_recipe_adjoint hq (by omega) ?_ hpn hQ
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j, by omega⟩

theorem ggTBJTorusNoncommAt_of_rowR5O2
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5O2 p lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : GGTBJTorusNoncommAt p Bs L hN := by
  intro y hy hy1 J' hJ' hJl hcount
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGLabQFour p lab ∧ GGTBRowR5O2 p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggO2Row_labelAll_adjoint hlab.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, m, n, K, _, _, b, c, e, hlift, hK, hn, hbc,
    hm, hme, hpn, hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : OrthRest.RMinus K m b c →* MulAut (OrthRest.RMinus K m b c)))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hI φ hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hK
  exact ggTBJ_om_torusJNoncomm_nf hbc hm hp hme (by rw [hK]; exact hpn)
    (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB' y hy hJ' hcount

theorem ggTBJTorusNoncomm_rowR5O2 :
    GGTBJTorusNoncomm fun p lab => GGLabQFour p lab ∧ GGTBRowR5O2 p lab := by
  intro G _ _ p B Bs x L D J hHyp _hq _hok hL hN
  exact ggTBJTorusNoncommAt_of_rowR5O2 hHyp.1 hL hN

theorem ggTBJNaWeylQFourOn_rowR5O2 :
    GGTBJNaWeylQFourOn fun p lab => GGLabQFour p lab ∧ GGTBRowR5O2 p lab :=
  ggTBJNaWeylQFourOn_of_torusNoncomm ggTBJTorusNoncomm_rowR5O2

theorem ggTBJNoncommReflOn_of_rowR5O2
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGLabQFour p lab)
    (h : GGTBJNoncommReflOn fun p lab => S p lab ∧ ¬ GGTBRowR5O2 p lab) :
    GGTBJNoncommReflOn S :=
  ggTBJNoncommReflOn_of_split S GGTBRowR5O2
    ((ggTBJNoncommReflOn_of_naWeyl ggTBJNaWeylQFourOn_rowR5O2).mono
      fun p lab hl => ⟨hS p lab hl.1, hl.2⟩) h

end CFSG.StandardType

end
