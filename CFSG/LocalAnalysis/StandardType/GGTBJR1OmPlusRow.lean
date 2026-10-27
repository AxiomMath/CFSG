module

public import CFSG.LocalAnalysis.StandardType.GGTBJRowR5O2
public import CFSG.LocalAnalysis.StandardType.GGTBRowR1Defs
import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB OrthExc
open CFSG.RankThree.Classical2 (orthDerived)

theorem ggTBJ_omPlus_torusJNoncomm
    {K : Type} [Field K] [Finite K] [CharP K 2] {m p r : ℕ} (hm : 3 ≤ m) (hp : p.Prime)
    (hpq : p ∣ Nat.card K - 1)
    {L' : Type} [Group L'] [Finite L'] (ψ₀ : L' →* OrthRest.RPlus K (m + 1))
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r (OrthRest.RPlus K (m + 1))
      (Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →* MulAut (OrthRest.RPlus K (m + 1))))
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
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := CFSG.SeitzReduction.F4Pilot.two_dvd_natCard_of_charP_two (K := K)
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hp2 : p ≠ 2 := by
    intro hp2
    obtain ⟨d, hd⟩ := hp2 ▸ hpq
    omega
  obtain ⟨r', E, Δ, hE, σ, Θ, hψσ, hΘ, hWeyl, hnf⟩ :=
    ggTBJ_omPlus_stdModel_nf hp hm hpq ψ₀ A hA
  exact ggTBJ_om_torus_transport hp hp2 ψ₀ A hA Δ hE σ Θ hψσ hΘ hWeyl
    (fun f₀ J' hJ' hc' => by
      obtain ⟨a, P, hP, hswap, hmixed, h3, hcent⟩ :=
        Δ.blockData_nf hp2 (TableBOrth.nondegenerate_qPlusForm (m + 1)) hE hnf f₀ hJ' hc'
      exact ggTBJ_om_core_nf hp hp2 (Δ.τΩ hE) f₀ J' a P hP hswap hmixed h3 hcent hc')
    y hy hJ hcount

private theorem ggOmPlusRow_recipe_adjoint
    {m n p : ℕ} (hn : 2 ≤ n) (hm : 3 ≤ m) (hpn : p ∣ 2 ^ n - 1)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeOmegaPlus (m + 1) (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus (m + 1) (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ (r m' n' : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
        (_ : R ≃* OrthRest.RPlus K (m' + 1)),
        GGTorusLift p r R ∧ Nat.card K = 2 ^ n' ∧ 2 ≤ n' ∧ 3 ≤ m' ∧ p ∣ 2 ^ n' - 1 ∧
          ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 0, m, n, K, inferInstance, inferInstance,
    MulEquiv.refl _, TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus (by omega : 4 ≤ m + 1)),
    hK, hn, hm, hpn, fun φ hφ => hφ⟩

theorem ggLabQFour_of_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hn : 1 ≤ lab.n) (h : p ∣ 2 ^ lab.n - 1) : GGLabQFour p lab := by
  unfold GGLabQFour
  by_contra hlt
  have h1 : lab.n = 1 := by omega
  have h' : p ∣ 1 := by simpa [h1] using h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h')

theorem ggOmPlusRow_labelAll_adjoint
    {p : ℕ} {lab : LargeEvenLabel} (hq : GGLabQFour p lab)
    (h : lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (r m n : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : R ≃* OrthRest.RPlus K (m + 1)),
        GGTorusLift p r R ∧ Nat.card K = 2 ^ n ∧ 2 ≤ n ∧ 3 ≤ m ∧ p ∣ 2 ^ n - 1 ∧
          ∀ φ ∈ I, φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, h4, hpn⟩ := h
  subst htag
  unfold GGLabQFour at hq
  dsimp only at h4 hpn hq
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2
  · omega
  · rw [← Nat.sub_add_cancel (by omega : 1 ≤ l)] at hQ ⊢
    exact ggOmPlusRow_recipe_adjoint hq (by omega : 3 ≤ l - 1) hpn hQ

theorem ggTBJTorusNoncommAt_of_rowR1OmPlus
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n - 1) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) : GGTBJTorusNoncommAt p Bs L hN := by
  intro y hy hy1 J' hJ' hJl hcount
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGLabQFour p lab ∧ lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1)
    (fun lab _ hs => nbrC_labelAll_guard (ggOmPlusRow_labelAll_adjoint hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, m, n, K, _, _, e, hlift, hK, hn, hm, hpn,
    hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv
    (I' := Set.range (MulAut.conj : OrthRest.RPlus K (m + 1) →*
      MulAut (OrthRest.RPlus K (m + 1))))
    e (fun φ hφ => by
      obtain ⟨g, rfl⟩ := hI φ hφ
      exact ⟨e g, by ext z; simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have := charP_two_of_card hK
  exact ggTBJ_omPlus_torusJNoncomm hm hp (by rw [hK]; exact hpn)
    (e.toMonoidHom.comp (ggQuotHom θ)) _ hTB' y hy hJ' hcount

end CFSG.StandardType

end
