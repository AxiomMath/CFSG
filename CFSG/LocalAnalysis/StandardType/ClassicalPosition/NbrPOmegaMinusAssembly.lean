module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafJOmega
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafJSu
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafJSl
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafNeighbourBlockData
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafKOmega
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafKSu
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafKOmegaSl
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.NbrPOmegaMinusLeafKSl

public section

namespace CFSG.StandardType.ClassicalPosition.NbrLeaf

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.ClassicalPosition

open scoped commutatorElement

local notation "Ix" n:max => (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
local notation "Mx" n:max f:max => Matrix (Ix n) (Ix n) (GaloisField 2 f)
set_option quotPrecheck false in
local notation "UK" n:max f:max => (ggU .POmegaMinus n f).K
set_option quotPrecheck false in
local notation "ρm" n:max f:max => Spin.spinMatrix
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
set_option quotPrecheck false in
local notation "Gm" n:max f:max => LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin
  (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))
local notation "AdS" f:max S:max => Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
local notation "Fadj" n:max f:max e:max => formAdj (RingHom.id (GaloisField 2 f)) (Gm n f) e
local notation "BlkC" n:max f:max S:max ε:max =>
  (glBlockCentralizer (ρm n f) S ε : Subgroup (UK n f))
local notation "rk" f:max e:max =>
  Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e))

@[expose] def DegD (n f : ℕ) (S : Set (GL (Ix n) (GaloisField 2 f))) (ε e : Mx n f) : Prop :=
  (e = ε ∧ blockDegree (AdS f S) e < 2) ∨
    (e = ε ∧ 2 ≤ blockDegree (AdS f S) e ∧ blockDegree (AdS f S) e < 4) ∨
    (e ≠ ε ∧ blockDegree (AdS f S) e < 2)

section Stmts


variable {X : Type} [Group X] [Finite X] (n f : ℕ) (hn : 4 ≤ n) (ψ : UK n f →* X) (p : ℕ)
  (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .POmegaMinus n f ψ p G₀ B₁ D J L x)
include hn hH

private theorem nbrpmmx_base :
    ∃ (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)),
      SetD n f ψ J S J' ∧ FullD n f ψ D S := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let j : spinGroup (Spin.quadMinus n F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) →*
      GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F :=
    Spin.spinMatrix (Spin.quadMinus n F (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
  have hinj : Function.Injective j := nbrpom_spinMatrix_injective n f
  let P : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F → Prop := fun s => s ∈ j.range
  let S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :=
    {s | P s ∧ ∃ d ∈ D, IsGLLift j ψ s d}
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [h1]; exact h15
  have hlift : ∀ d ∈ D, ∃ s : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
      P s ∧ IsGLLift j ψ s d := by
    intro d hd
    have hdB : d ∈ B₁ := h11 hd
    have hb : GGPsiInnerDiag (Spin.Twisted.minusDatum n (minusCoeffs_irr 2 f)) ψ d :=
      h8 d hdB
    obtain ⟨s₀, hs₀⟩ := exists_conj_eq_POmegaMinus n (minusCoeffs_irr 2 f) hn ψ h2 hb
    exact ⟨j s₀, ⟨s₀, rfl⟩, fun u => ⟨s₀ * u * s₀⁻¹, by
      show j (s₀ * u * s₀⁻¹) = j s₀ * j u * (j s₀)⁻¹
      rw [map_mul, map_mul, map_inv], hs₀ u⟩⟩
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift j hinj ψ h2 P hJ hlift
  refine ⟨S, J', ?_, ?_⟩
  · unfold SetD
    refine ⟨fun s hs => hs.1, ?_, ?_, hJ'comp, hJ'map⟩
    · intro s hs s' hs'
      obtain ⟨d, hdD, hsl⟩ := hs.2
      obtain ⟨d', hd'D, hs'l⟩ := hs'.2
      have hdB : d ∈ B₁ := h11 hdD
      have hd'B : d' ∈ B₁ := h11 hd'D
      have hbb' : Commute d d' :=
        congrArg Subtype.val (h9.1.is_comm.comm ⟨d, hdB⟩ ⟨d', hd'B⟩)
      obtain ⟨s₀, hs₀, hsl₀⟩ := nbrpom_lift_to_mem n f ψ hs.1 hsl
      obtain ⟨s₁, hs₁, hsl₁⟩ := nbrpom_lift_to_mem n f ψ hs'.1 hs'l
      have hc := conj_eq_commute_POmegaMinus n (minusCoeffs_irr 2 f) hn ψ h2 hbb' hsl₀ hsl₁
      have hc' : s * s' = s' * s := by
        rw [← hs₀, ← hs₁, ← map_mul, ← map_mul, hc.eq]
      exact hc'
    · intro s hs
      obtain ⟨d, hdD, hsl⟩ := hs.2
      have hdB : d ∈ B₁ := h11 hdD
      have hdpow : d ^ p = 1 := h9.2 d hdB
      have hspowj : s ^ p ∈ j.range := Subgroup.pow_mem _ hs.1 p
      have hslpow : IsGLLift j ψ (s ^ p) 1 := by
        have h := hsl.pow p
        rwa [hdpow] at h
      have huniq : s ^ p = 1 :=
        nbrpom_lift_unique n f hn ψ h2 hspowj (Subgroup.one_mem _) hslpow isGLLift_one
      have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr huniq
      have hpodd : Odd p := h5.odd_of_ne_two h6
      rcases h5.eq_one_or_self_of_dvd (orderOf s) hdvd with h | h
      · rw [h]; exact odd_one
      · rw [h]; exact hpodd
  · unfold FullD
    intro s hsP hsl
    exact ⟨hsP, hsl⟩

section Ctx2a

variable (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) (ε e_J : Mx n f)
  (hB : SetD n f ψ J S J') (hF : FullD n f ψ D S) (hE : EpsD n f S J' ε)
  (heJ : IsPrimIdemIn (AdS f S) e_J)
include S J' ε e_J hB hF hE heJ

private theorem nbrpmmx_J_degree (heJε : e_J * ε = e_J) (hsplit : SplitD n f ε e_J) :
    DegD n f S ε e_J := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  obtain ⟨hSU, hS, hodd, hJ'comp, hJ'map⟩ := hB
  obtain ⟨hε, hJ'ε⟩ := hE
  have hadm : StatedLieAdmissible .POmegaMinus n 2 f :=
    CFSG.Blueprint.LieModel.admissible h3
  have hf : 1 ≤ f := hadm.2.1
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  unfold DegD
  rcases hsplit with heq | ⟨hne, -, -⟩
  · by_cases hd : blockDegree (AdS f S) e_J < 2
    · exact Or.inl ⟨heq, hd⟩
    · by_cases h4' : blockDegree (AdS f S) e_J < 4
      · exact Or.inr (Or.inl ⟨heq, by omega, h4'⟩)
      · refine absurd ?_ h29
        rw [← hJ'map]
        exact ggSixLSevenFieldExtCase_POmegaMinus n (minusCoeffs_irr 2 f) hn f hc ψ h2
          S hSU hS hodd hε hJ'ε heJ heJε (Or.inl ⟨heq, by omega⟩)
  · by_cases hd : blockDegree (AdS f S) e_J < 2
    · exact Or.inr (Or.inr ⟨hne, hd⟩)
    · refine absurd ?_ h29
      rw [← hJ'map]
      exact ggSixLSevenFieldExtCase_POmegaMinus n (minusCoeffs_irr 2 f) hn f hc ψ h2
        S hSU hS hodd hε hJ'ε heJ heJε (Or.inr ⟨hne, by omega⟩)

end Ctx2a

private theorem nbrpmmx_J_split :
    ∃ (S : Set (GL (Ix n) (GaloisField 2 f))) (J' : Subgroup (UK n f)) (ε e_J : Mx n f),
      SetD n f ψ J S J' ∧ FullD n f ψ D S ∧ EpsD n f S J' ε ∧ IsPrimIdemIn (AdS f S) e_J ∧
        e_J * ε = e_J ∧ SplitD n f ε e_J ∧ DegD n f S ε e_J := by
  obtain ⟨S, J', hB, hF⟩ := nbrpmmx_base n f hn ψ p G₀ B₁ D J L x hH
  obtain ⟨hSU, hS, hodd, hJ'comp, hJ'map⟩ := hB
  obtain ⟨ε, e_J, hε, heJ, heJε, hsplit, hJ'ε⟩ := nbrpom_L3 n f hn S hSU hS J' hJ'comp
  have hB : SetD n f ψ J S J' := by
    unfold SetD
    exact ⟨hSU, hS, hodd, hJ'comp, hJ'map⟩
  have hE : EpsD n f S J' ε := by
    unfold EpsD
    exact ⟨hε, hJ'ε⟩
  exact ⟨S, J', ε, e_J, hB, hF, hE, heJ, heJε, hsplit,
    nbrpmmx_J_degree n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ heJε hsplit⟩

end Stmts

theorem nbrpmmx_assembly
    {X : Type} [Group X] [Finite X] (n f : ℕ) (hn : 4 ≤ n)
    (ψ : (ggU .POmegaMinus n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .POmegaMinus n f ψ p G₀ B₁ D J L x) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧
      GGRootPosG0 .POmegaMinus n f p ψ R Rm ∧
      ((∃ (t' : StatedLieTag) (mJ : ℕ) (βJ : Fin (ggU t' mJ f).D.rank → ℤ),
          (t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ mJ ∧
          βJ ∈ (ggU t' mJ f).D.roots ∧ GGLongRoot (ggU t' mJ f).D βJ ∧
          GGRootVia (ggU t' mJ f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            ∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
              (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ mJ < mK ∧
              βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
              GGRootVia (ggU t'' mK f) K R βK) ∨
        (∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ),
          βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧
          GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
              βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧
              GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
            (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
              (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ kJ + 1 ≤ mK ∧
              βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
              GGRootVia (ggU t'' mK f) K R βK)) ∨
        (∃ (m'J : ℕ) (βJ : Fin (ggU .PSU m'J f).D.rank → ℤ),
          βJ ∈ (ggU .PSU m'J f).D.roots ∧
          GGRootVia (ggU .PSU m'J f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            (∃ (m'K : ℕ) (βK : Fin (ggU .PSU m'K f).D.rank → ℤ), m'J < m'K ∧
              βK ∈ (ggU .PSU m'K f).D.roots ∧ GGLongRoot (ggU .PSU m'K f).D βK ∧
              GGRootVia (ggU .PSU m'K f) K R βK) ∨
              (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
                (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ m'J ≤ mK ∧
                βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
                GGRootVia (ggU t'' mK f) K R βK))) := by
  obtain ⟨S, J', ε, e_J, hB, hF, hE, heJ, heJε, hsplit, hdeg⟩ :=
    nbrpmmx_J_split n f hn ψ p G₀ B₁ D J L x hH
  rcases hdeg with homega | hsu | hsl
  · obtain ⟨R, Rm, hRJ, hRmJ, hR0, hJcase⟩ :=
      nbrpmmx_J_omega n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ homega
    rcases hJcase with hO | hSL2
    · obtain ⟨t', mJ, βJ, ht', hmJ, hβJ, hlongJ, hviaJ, hrankJ⟩ := hO
      refine ⟨R, Rm, hRJ, hRmJ, hR0, Or.inl ⟨t', mJ, βJ, ht', hmJ, hβJ, hlongJ, hviaJ, ?_⟩⟩
      intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
      exact nbrpmmx_K_omega n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ e heD K hKG₀
        hKcomp hJK R Rm hRJ hR0 hKne homega t' mJ βJ ht' hmJ hrankJ
    · obtain ⟨kJ, βJ, hkJ, hβJ, hviaJ, hrankJ⟩ := hSL2
      refine ⟨R, Rm, hRJ, hRmJ, hR0, Or.inr (Or.inl ⟨kJ, βJ, hβJ, hviaJ, ?_⟩)⟩
      intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
      exact nbrpmmx_K_omega_sl n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ e heD K hKG₀
        hKcomp hJK R Rm hRJ hR0 hKne homega kJ βJ hrankJ
  · obtain ⟨R, Rm, hRJ, hRmJ, hR0, m'J, βJ, hβJ, hviaJ, hrankJ⟩ :=
      nbrpmmx_J_su n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ hsu
    refine ⟨R, Rm, hRJ, hRmJ, hR0, Or.inr (Or.inr ⟨m'J, βJ, hβJ, hviaJ, ?_⟩)⟩
    intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
    exact nbrpmmx_K_su n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ e heD K hKG₀
      hKcomp hJK R Rm hRJ hR0 hKne hsu m'J βJ hrankJ
  · have hsl' : e_J ≠ ε ∧ Fadj n f e_J ≠ e_J ∧ ε = e_J + Fadj n f e_J ∧
        blockDegree (AdS f S) e_J < 2 := by
      rcases hsplit with hself | ⟨hne, hpair, heq⟩
      · exact absurd hself hsl.1
      · exact ⟨hne, hpair, heq, hsl.2⟩
    obtain ⟨R, Rm, hRJ, hRmJ, hR0, kJ, βJ, hβJ, hviaJ, hrankJ⟩ :=
      nbrpmmx_J_sl n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ hsl'
    refine ⟨R, Rm, hRJ, hRmJ, hR0, Or.inr (Or.inl ⟨kJ, βJ, hβJ, hviaJ, ?_⟩)⟩
    intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
    exact nbrpmmx_K_sl n f hn ψ p G₀ B₁ D J L x hH S J' ε e_J hB hF hE heJ e heD K hKG₀
      hKcomp hJK R Rm hRJ hR0 hKne hsl' kJ βJ hrankJ


end CFSG.StandardType.ClassicalPosition.NbrLeaf

namespace CFSG.StandardType.ClassicalPosition

theorem ggSixPOmegaMinusPosExplicit_holds :
    CFSG.StandardType.LieKnownR2.POmega.GGSixPOmegaPosExplicit .POmegaMinus := by
  unfold CFSG.StandardType.LieKnownR2.POmega.GGSixPOmegaPosExplicit
  intro X hX hXfin n f ψ p G₀ B₁ D J L x hH
  have hn : 4 ≤ n := NbrLeaf.nbrpom_L6 n f ψ p G₀ B₁ D J L x hH
  exact NbrLeaf.nbrpmmx_assembly n f hn ψ p G₀ B₁ D J L x hH

end CFSG.StandardType.ClassicalPosition
