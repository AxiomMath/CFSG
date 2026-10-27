module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmSmallMain
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmGlue
public import CFSG.RankThree.PartOne.S11d.OrthCaseN
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.StandardType

namespace SevOmSmall

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank Multiplicative SevOm
open scoped MatrixGroups

theorem excluded_of_SL2 {G : Type} [Group G] {t : StatedLieTag} {f : ℕ} {L₁ : Subgroup G}
    {E : Type} [Field E] [Finite E] (hE : Nat.card E = 4) (eL : ↥L₁ ≃* SL(2, E)) :
    GGSixSeventeenExcluded 5 t f L₁ := by
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [Fintype.card_eq_nat_card, hE]
    norm_num)
  exact Or.inr (Or.inl ⟨rfl, Or.inl
    (CFSG.RankThree.PartOne.lieModel_quotient_of_SL2 (hE.trans (by norm_num)) le_rfl eL)⟩)

section Restr

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear NoOffOm

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {p : ℕ} {A : Subgroup (GL (Fin d) K)}

omit [Finite K] [CharP K 2] in
theorem restrClosed_of_genMax (hA : GenMax (polB Q) (matrixDerived Q) p A) :
    RestrClosed Q (A.map (matrixLinearIso (d := d) (K := K)).toMonoidHom) := by
  intro W hWnd hWA c hc
  obtain ⟨c', hc', rfl⟩ := hc
  have hWA' : ∀ a ∈ A, ∀ w ∈ W, glin a w ∈ W := fun a ha w hw => by
    rw [← matrixLinearIso_apply_eq_glin]
    exact hWA _ ⟨a, ha, rfl⟩ w hw
  have hWnd' : SUTB.NondegOn (polB Q) W := fun m hm h0 => hWnd m hm fun n hn => by
    rw [← polB_apply]
    exact h0 n hn
  obtain ⟨g, hgA, hgW, hgperp⟩ := hA.exists_mem_restrict hWnd' hWA' hc'
  refine ⟨matrixLinearIso g, ⟨g, hgA, rfl⟩, fun w hw => ?_, fun v hv => ?_⟩
  · change matrixLinearIso g w = matrixLinearIso c' w
    rw [matrixLinearIso_apply_eq_glin, matrixLinearIso_apply_eq_glin]
    exact hgW w hw
  · change matrixLinearIso g v = v
    rw [matrixLinearIso_apply_eq_glin]
    exact hgperp v (Submodule.mem_orthogonalBilin.mpr fun n hn => by
      rw [polB_apply]
      exact hv n hn)

end Restr

section Model

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthComm CFSG.RankThree.Classical2 NoOffOm

theorem witness_of_matrixModel_small {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {f : ℕ} (hf : 1 ≤ f) {d : ℕ}
    {Q : QuadraticForm (GaloisField 2 f) (Fin d → GaloisField 2 f)}
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 f) (Fin d → GaloisField 2 f),
      Module.finrank (GaloisField 2 f) T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (φ : matrixDerived Q →* G) (hφ : Function.Injective φ) (hrange : φ.range = ggG0 p B x L D J)
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : GGBstar p B Bs) (hBφ : Bs ≤ φ.range)
    (hcard : p ^ 4 ≤ Nat.card Bs) (hsmall : (f = 1 ∧ p = 3) ∨ (f = 2 ∧ p = 5))
    {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) {L₁ : Subgroup G}
    (hL₁ : IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}))
    (hex : ¬ GGSixSeventeenExcluded p t f L₁) (hpL : p ∣ Nat.card L₁) :
    (∃ L₂ : Subgroup G, IsComponentOf L₂ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
      Nat.card (Bs ⊓ Subgroup.centralizer (L₂ : Set G) : Subgroup G) ≤ p ^ 2) ∨
    ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e ∨
      (e ∈ Bs ∧ e ≠ 1 ∧ GGSixSeventeenSixteen p B Bs x L D J t f e) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hKp : (Nat.card (GaloisField 2 f) = 2 ∧ p = 3) ∨
      (Nat.card (GaloisField 2 f) = 4 ∧ p = 5) := by
    rcases hsmall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨by rw [hK]; norm_num, rfl⟩
    · exact Or.inr ⟨by rw [hK]; norm_num, rfl⟩
  have hA := genMax_of_orth hnd hT hp hp2 hBs.2.1 hBs.2.2.2 φ hφ hBφ
  have hR := restrClosed_of_genMax hA
  obtain ⟨r, ⟨F⟩⟩ := exists_frame_of_genMax hA
  set A := ((Bs.comap φ).map (matrixDerived Q).subtype).map
    (matrixLinearIso (d := d) (K := GaloisField 2 f)).toMonoidHom with hAdef
  set Ω := orthDerived Q with hΩ
  set φV : ↥Ω →* G := φ.comp (matrixDerivedEquiv Q).symm.toMonoidHom with hφVdef
  have hφV : Function.Injective φV := hφ.comp (matrixDerivedEquiv Q).symm.injective
  have hφVr : φV.range = φ.range := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨X, rfl⟩
      exact ⟨matrixDerivedEquiv Q X, by simp [hφVdef]⟩
  have : Finite ((Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f] (Fin d → GaloisField 2 f)) :=
    CFSG.RankThree.PartOne.KCOrthComm.finite_linearEquiv
  have hAB : ∀ g : ↥Ω, ((g : ↥Ω) : (Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      (Fin d → GaloisField 2 f)) ∈ A ↔ φV g ∈ Bs := by
    intro g
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, hYg⟩
      have hYg' : (matrixDerivedEquiv Q).symm g = Y := by
        apply (matrixDerivedEquiv Q).injective
        rw [MulEquiv.apply_symm_apply]
        exact Subtype.ext hYg.symm
      show φ ((matrixDerivedEquiv Q).symm g) ∈ Bs
      rw [hYg']
      exact hY
    · intro hg
      exact ⟨((matrixDerivedEquiv Q).symm g).1, ⟨(matrixDerivedEquiv Q).symm g, hg, rfl⟩, by
        have h1 := coe_matrixDerivedEquiv Q ((matrixDerivedEquiv Q).symm g)
        rw [MulEquiv.apply_symm_apply] at h1
        exact h1.symm⟩
  have hAΩ : A ≤ Ω := by
    rintro _ ⟨_, ⟨Y, -, rfl⟩, rfl⟩
    have h1 := (matrixDerivedEquiv Q Y).2
    rwa [coe_matrixDerivedEquiv] at h1
  have hBφV : Bs ≤ φV.range := hφVr ▸ hBφ
  have hmax : ∀ g ∈ Ω, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine (hAB ⟨g, hg⟩).mpr (hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_) ?_)
    · obtain ⟨c, rfl⟩ := hBφV hy
      have h1 := hgc c ((hAB c).mpr hy)
      rw [← map_mul, ← map_mul]
      exact congrArg φV (Subtype.ext h1.symm)
    · rw [← map_pow]
      have h1 : (⟨g, hg⟩ : ↥Ω) ^ p = 1 := Subtype.ext (by simpa using hgp)
      rw [h1, map_one]
  have hr : 4 ≤ r := by
    have hcA : Nat.card A = p ^ r := by
      rw [← F.range, Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv.symm,
        Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have hle : Nat.card Bs ≤ Nat.card A := by
      have hex : ∀ y : Bs, ∃ g : ↥Ω, φV g = y := fun y => hBφV y.2
      choose σ hσ using hex
      refine Nat.card_le_card_of_injective (fun y => ⟨σ y, (hAB _).mpr (by rw [hσ]; exact y.2)⟩)
        fun y y' hyy => ?_
      have h0 := congrArg (fun z : A => (z : (Fin d → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin d → GaloisField 2 f))) hyy
      have h1 : σ y = σ y' := Subtype.ext h0
      exact Subtype.ext (by rw [← hσ y, ← hσ y', h1])
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard.trans (hle.trans hcA.le))
  have hL₁G := hL₁
  obtain ⟨a', rfl⟩ := hBφV hb
  obtain ⟨s₀, hs₀⟩ := F.exists_eq ((hAB a').mpr hb)
  rw [← hrange, ← hφVr] at hL₁
  obtain ⟨hL, hmapL⟩ := isComponentOf_transport hφV a' hL₁
  rw [← hs₀] at hL
  have hpL' : p ∣ Nat.card ((L₁.comap φV).map Ω.subtype) := by
    rw [Subgroup.card_map_of_injective Ω.subtype_injective,
      ← Subgroup.card_map_of_injective hφV, hmapL]
    exact hpL
  have hG₀ : φV.range = ggG0 p B x L D J := hφVr.trans hrange
  rcases exists_witness_orth_small hnd hp hp2 hKp hAΩ F hr hmax hR s₀ hL hpL' with
    ⟨e, heL, heA, he1, L₂, hL₂, hcard₂⟩ | hcardL | ⟨hp5, E, _, _, hE, ⟨eE⟩⟩
  ·
    obtain ⟨y, hy, rfl⟩ := heL
    refine Or.inr ⟨φV y, hy, Or.inl ⟨(hAB y).mp heA, fun h => ?_, Or.inr
      ⟨(L₂.comap Ω.subtype).map φV, ?_, ?_⟩⟩⟩
    · exact he1 (by rw [hφV (h.trans (map_one φV).symm)]; rfl)
    · have h1 := (isComponentOf_transport' hφV y hL₂).1
      rwa [hG₀] at h1
    · exact (card_inf_centralizer_le hφV hBφV hAB (hL₂.1.trans inf_le_left)).trans hcard₂
  ·
    refine Or.inl ⟨L₁, hL₁G, ?_⟩
    have h1 := card_inf_centralizer_le hφV hBφV hAB (Subgroup.map_subtype_le (L₁.comap φV))
    rw [Subgroup.comap_map_eq_self_of_injective Ω.subtype_injective, hmapL] at h1
    exact h1.trans hcardL
  ·
    exfalso
    subst hp5
    let e₁ : ↥L₁ ≃* ↥((L₁.comap φV).map Ω.subtype) :=
      (MulEquiv.subgroupCongr hmapL).symm.trans
        (((L₁.comap φV).equivMapOfInjective φV hφV).symm.trans
          ((L₁.comap φV).equivMapOfInjective Ω.subtype Ω.subtype_injective))
    exact hex (excluded_of_SL2 hE (e₁.trans eE))

end Model

end SevOmSmall

end CFSG.StandardType
