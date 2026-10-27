module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusFixed
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlusSide
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBSupported
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBTwisted
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter

public section

namespace CFSG.StandardType.SympMinus

open CFSG CFSG.Assembly CFSG.StandardType.TypeBDatum CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem tbFacts_of_marking {p : ℕ} {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hX : commutator ↥X = ⊤) {R : Type} [Group R] (θ : ↥X ⧸ Subgroup.center ↥X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I) :
    Function.Surjective (ggQuotHom θ) ∧ (ggQuotHom θ).ker ≤ Subgroup.center ↥X ∧
      commutator ↥X = ⊤ ∧ IsElemAbelian p (ggGamma X hBsN).range ∧
      (∀ a ∈ (ggGamma X hBsN).range, ∃ φ ∈ I, ∀ l : ↥X, φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      GGTorusSelfCent p (ggGamma X hBsN).range := by
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 (b : G) b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p (ggGamma X hBsN).range :=
    isElemAbelian_range hBc hBp (ggGamma X hBsN)
  have hAI : ∀ a ∈ (ggGamma X hBsN).range, ∃ φ ∈ I, ∀ l : ↥X,
      φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, hBsI b b.2, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  exact ⟨ggQuotHom_surjective θ, by rw [ker_ggQuotHom], hX, hA, hAI,
    ggTorusSelfCent_ggGamma hBsN hSC⟩


theorem ggTBJ_sympMinus_side_of_frame
    {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [NeZero m] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hm3 : 3 ≤ m) {Bs X J : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hXperf : commutator ↥X = ⊤)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSpGroup K m))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m))))
    {σ : (Fin m → Multiplicative (ZMod p)) →* ↥X}
    {ΘA : (Fin m → Multiplicative (ZMod p)) ≃* ↥(ggGamma X hBsN).range}
    (hΘA : ∀ f, ((ΘA f : ↥(ggGamma X hBsN).range) : MulAut ↥X) = MulAut.conj (σ f))
    (hTop : FrameBs.sectionFrameAut σ ⊤ = TypeBDatum.signedAut m p)
    (hcaseJ : BlockCases σ (J.subgroupOf X)) (hJle : J ≤ X)
    (hcount : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) (hJX : J ≠ X) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hψ, hker, hperf, -, -, -⟩ := tbFacts_of_marking hBs hSC hXperf θ hBsN hBsI
  have hcp : ¬ p ∣ Nat.card (Subgroup.center ↥X) :=
    ggCenterPrime_sp (K := K) (m := m) hp hp2 ↥X (ggQuotHom θ) hψ hker hperf
  have hZ : ∀ z ∈ Subgroup.center ↥X, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    by_contra hne
    apply hcp
    have hord : orderOf (⟨z, hz⟩ : Subgroup.center ↥X) = p := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime hzp hne
    rw [← hord]
    exact orderOf_dvd_natCard _
  obtain ⟨hmem, -⟩ := FrameBs.sectionFrame_model hBs hSC hBsN σ ΘA hΘA
  obtain ⟨Θ, hΘ, hAutH⟩ :=
    FrameBs.ggAutomizer_eq_map_liftBs_sectionFrameAut hBs hSC hBsN hZ σ ΘA hΘA
  have hX : ggAutomizer X Bs = (signedAut m p).map (liftBs Θ) := by
    rw [hAutH X le_rfl, FrameBs.sectionFrameAut_subtype_comp σ le_rfl,
      Subgroup.subgroupOf_self, hTop]
  have hJeq : ggAutomizer J Bs =
      (FrameBs.sectionFrameAut σ (J.subgroupOf X)).map (liftBs Θ) := by
    rw [hAutH J hJle, FrameBs.sectionFrameAut_subtype_comp σ hJle]
  have hcardC := (FrameBs.card_centralizer_frame Θ σ hΘ hmem hJle).2
  have hW0 : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := Nat.card_pos
  have hbound : ∀ n : ℕ, n ≤ Nat.card {f : Fin m → Multiplicative (ZMod p) //
      ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} → n ≤ p ^ 3 := by
    intro n hn
    calc n ≤ _ := hn
      _ = Nat.card {f : Fin m → Multiplicative (ZMod p) //
          ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} * 1 := (mul_one _).symm
      _ ≤ Nat.card {f : Fin m → Multiplicative (ZMod p) //
          ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G)} *
          Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := Nat.mul_le_mul_left _ hW0
      _ = Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := hcardC.symm
      _ ≤ p ^ 3 := hcount
  have hcentJ : ∀ (f : Fin m → Multiplicative (ZMod p)),
      (∀ τ ∈ FrameBs.sectionFrameAut σ (J.subgroupOf X), τ f = f) →
      (∀ j' ∈ J.subgroupOf X, σ f * j' = j' * σ f) →
      ∀ j ∈ J, ((σ f : ↥X) : G) * j = j * ((σ f : ↥X) : G) := by
    intro f _ h j hj
    have := h ⟨j, hJle hj⟩ (Subgroup.mem_subgroupOf.mpr hj)
    simpa using congrArg Subtype.val this
  rcases hcaseJ with ⟨S, hS, hA1, hA2, hA3⟩ | ⟨S, s, hs, hS, hA1, hA2⟩
  · have hSm : S.card ≤ m := by simpa using Finset.card_le_univ S
    have hSlt : S.card < m := by
      by_contra hge
      have htop : J.subgroupOf X = ⊤ := hA3 (le_antisymm hSm (not_lt.mp hge))
      exact hJX (le_antisymm hJle (Subgroup.subgroupOf_eq_top.mp htop))
    have hc3 : m - S.card ≤ 3 := by
      have h2 := hbound _ (card_le_of_forall_mem_eq_one S fun f hf =>
        hcentJ f (fun τ hτ => fixed_of_vanish_signedSupportedAut S hf τ (hA1 ▸ hτ))
          (hA2 f (fun τ hτ => fixed_of_vanish_signedSupportedAut S hf τ (hA1 ▸ hτ))))
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
    have hJeq' : ggAutomizer J Bs = (signedSupportedAut m p S).map (liftBs Θ) := by
      rw [hJeq, hA1]
    have hU := ggTBJTypeB_sideDatum_signedSupported hp2 (by omega) hBs Θ hX hS (by omega) hc3 hJeq'
    by_cases hc1 : m - S.card = 1
    · exact Or.inl (hU.1 hc1)
    · exact Or.inr (hU.2 (by omega))
  · have hSm : S.card ≤ m := by simpa using Finset.card_le_univ S
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    have hc3 : m + 1 - S.card ≤ 3 := by
      have hfix : ∀ (f : Fin m → Multiplicative (ZMod p)) (a : ZMod p),
          (∀ i ∈ S, f i = Multiplicative.ofAdd (s i * a)) →
            ∀ τ ∈ FrameBs.sectionFrameAut σ (J.subgroupOf X), τ f = f := fun f a hf τ hτ =>
        fixed_of_twisted_twistedPermAut S hs (a := a)
          (fun i hi => by rw [hf i hi]; rfl) τ (hA1 ▸ hτ)
      have h2 := hbound _ (card_le_of_forall_mem_eq_smul S hne s hs fun f a hf =>
        hcentJ f (hfix f a hf) (hA2 f (hfix f a hf)))
      have h3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h2
      omega
    have hJeq' : ggAutomizer J Bs = (twistedPermAut m p S s hs).map (liftBs Θ) := by
      rw [hJeq, hA1]
    have hU := ggTBJTypeB_sideDatum_twistedPerm hp2 (by omega) hBs Θ hX hS hc3 hs hJeq'
    by_cases hc1 : m + 1 - S.card = 1
    · exact Or.inl (hU.1 hc1)
    · exact Or.inr (hU.2 (by omega))

theorem ggTBJ_sympMinus_side
    {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [NeZero m] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hm3 : 3 ≤ m) (hq : 4 ≤ Nat.card K ∨ Nat.card K = 2)
    (hpq : p ∣ Nat.card K + 1) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) (hXperf : commutator ↥X = ⊤)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSpGroup K m))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m))))
    {b₀ : G} (hb₀ : b₀ ∈ Bs)
    (hJc : CFSG.Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer ({b₀} : Set G)))
    (hcount : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3) (hJX : J ≠ X) :
    GGResSideDatum p Bs X J ∨ GGResLeviSideDatumLE3 p Bs X J ∨
      SympA6Out X J (ggQuotHom θ) (ggGamma X hBsN ⟨b₀, hb₀⟩) := by
  classical
  have hp : p.Prime := Fact.out
  have hJle : J ≤ X := hJc.1.trans inf_le_left
  obtain ⟨hψ, hker, hperf, hAe, hAI, hsc⟩ := tbFacts_of_marking hBs hSC hXperf θ hBsN hBsI
  obtain ⟨σ, ΘA, hΘA, hTop, hcase⟩ := ggTBJ_sympMinus_frame hp hp2 hq hm3 hpq (ggQuotHom θ)
    hψ hker hperf (ggGamma X hBsN).range hAe hAI hsc
  have hy : ggGamma X hBsN ⟨b₀, hb₀⟩ ∈ (ggGamma X hBsN).range := ⟨⟨b₀, hb₀⟩, rfl⟩
  have hJ' : CFSG.Open.IsComponentOf (J.subgroupOf X)
      (fixSubgroup (ggGamma X hBsN ⟨b₀, hb₀⟩)) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp
      (ggIsComponentOf_ggFixSub_normalizerMonoidHom (hBsN hb₀) hJc)
  rcases hcase _ hy (J.subgroupOf X) hJ' with hB | ⟨hK2, f₀, hyeq, hA6⟩
  · rcases ggTBJ_sympMinus_side_of_frame hp2 hm3 hBs hSC hBsN hXperf θ hBsI hΘA hTop hB hJle
      hcount hJX with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (sympMinusA6_out hp hp2 hJle (ggQuotHom θ) hker hK2 σ f₀ hyeq hA6))


end CFSG.StandardType.SympMinus

end
