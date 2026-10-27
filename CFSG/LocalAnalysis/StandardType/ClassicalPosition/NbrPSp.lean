module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoRootConversePSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockRankDvd
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepAPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.RootModel
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.LocalAnalysis.UniquenessCase.UC6K323Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Five
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Invol
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Sylow3
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

open scoped commutatorElement

private lemma nbrPSp_lift_to_mem {X : Type} [Group X] (n : ℕ) (F : Type) [Field F]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X) {b : X} {s : GL (Fin n ⊕ Fin n) F}
    (hsP : s ∈ CFSG.Open.StatedSp n F)
    (hs : IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s b) :
    ∃ s₀ : ↥(CFSG.Open.StatedSp n F),
      (s₀ : GL (Fin n ⊕ Fin n) F) = s ∧ ∀ u, b⁻¹ * ψ u * b = ψ (s₀ * u * s₀⁻¹) := by
  refine ⟨⟨s, hsP⟩, rfl, fun u => ?_⟩
  obtain ⟨u', hu'j, hu'ψ⟩ := hs u
  have heq : u' = (⟨s, hsP⟩ : ↥(CFSG.Open.StatedSp n F)) * u *
      (⟨s, hsP⟩ : ↥(CFSG.Open.StatedSp n F))⁻¹ := by
    apply Subgroup.subtype_injective
    rw [hu'j]
    rfl
  rw [hu'ψ, heq]

private lemma nbrPSp_lift_inv {X : Type} [Group X] (n : ℕ) (F : Type) [Field F]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X) {b : X} {s : GL (Fin n ⊕ Fin n) F}
    (hsP : s ∈ CFSG.Open.StatedSp n F)
    (hs : IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s b) :
    IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s⁻¹ b⁻¹ := by
  obtain ⟨s₀, hs₀, hsl₀⟩ := nbrPSp_lift_to_mem n F ψ hsP hs
  intro u
  refine ⟨s₀⁻¹ * u * s₀, ?_, ?_⟩
  · change ((s₀⁻¹ * u * s₀ : ↥(CFSG.Open.StatedSp n F)) : GL (Fin n ⊕ Fin n) F) =
      s⁻¹ * (u : GL (Fin n ⊕ Fin n) F) * s
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hs₀]
  · have h := hsl₀ (s₀⁻¹ * u * s₀)
    have h1 : s₀ * (s₀⁻¹ * u * s₀) * s₀⁻¹ = u := by group
    rw [h1] at h
    rw [inv_inv]
    calc b * ψ u * b⁻¹ = b * (b⁻¹ * ψ (s₀⁻¹ * u * s₀) * b) * b⁻¹ := by rw [h]
      _ = ψ (s₀⁻¹ * u * s₀) := by group

private lemma nbrPSp_lift_zpow {X : Type} [Group X] (n : ℕ) (F : Type) [Field F]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X) {b : X} {s : GL (Fin n ⊕ Fin n) F}
    (hsP : s ∈ CFSG.Open.StatedSp n F)
    (hs : IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s b) (k : ℤ) :
    IsGLLift (CFSG.Open.StatedSp n F).subtype ψ (s ^ k) (b ^ k) := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; simpa using hs.pow m
  · rw [hm]
    rw [show (s : GL (Fin n ⊕ Fin n) F) ^ (-(m : ℤ)) = (s ^ m)⁻¹ by
          rw [zpow_neg, zpow_natCast],
        show b ^ (-(m : ℤ)) = (b ^ m)⁻¹ by rw [zpow_neg, zpow_natCast]]
    exact nbrPSp_lift_inv n F ψ (Subgroup.pow_mem _ hsP m) (hs.pow m)

private lemma nbrPSp_lift_unique {X : Type} [Group X] (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (ψ : ↥(CFSG.Open.StatedSp n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center ↥(CFSG.Open.StatedSp n F)) {b : X}
    {s s' : GL (Fin n ⊕ Fin n) F} (hsP : s ∈ CFSG.Open.StatedSp n F)
    (hs'P : s' ∈ CFSG.Open.StatedSp n F)
    (hs : IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s b)
    (hs' : IsGLLift (CFSG.Open.StatedSp n F).subtype ψ s' b) : s = s' := by
  obtain ⟨s₀, hs₀, hsl₀⟩ := nbrPSp_lift_to_mem n F ψ hsP hs
  obtain ⟨s₁, hs₁, hsl₁⟩ := nbrPSp_lift_to_mem n F ψ hs'P hs'
  have hconj : ∀ u, ψ (s₀ * u * s₀⁻¹) = ψ (s₁ * u * s₁⁻¹) := by
    intro u
    rw [← hsl₀ u, ← hsl₁ u]
  have hEq : s₀ = s₁ := conj_eq_unique_PSp n F ψ hψ hconj
  calc s = (s₀ : GL (Fin n ⊕ Fin n) F) := hs₀.symm
    _ = (s₁ : GL (Fin n ⊕ Fin n) F) := by rw [hEq]
    _ = s' := hs₁

private theorem nbrPSp_center_bot
    (n f : ℕ) :
    Subgroup.center ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) = ⊥ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact (Subgroup.eq_bot_iff_forall _).mpr fun x _ => Subsingleton.elim x 1
  · exact CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two hn

private theorem nbrPSp_injective
    {X : Type} [Group X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K) :
    Function.Injective ψ := by
  have hker : ψ.ker = ⊥ := le_bot_iff.mp (hψ.trans (le_of_eq (nbrPSp_center_bot n f)))
  exact (MonoidHom.ker_eq_bot_iff ψ).mp hker

private theorem nbrPSp_rootLift
    {X : Type} [Group X] (n f p : ℕ) (ψ : (ggU .PSp n f).K →* X) (R Rm : Subgroup X)
    (hR0 : GGRootPosG0 .PSp n f p ψ R Rm) :
    ∃ R' : Subgroup (ggU .PSp n f).K,
      R'.map ψ = R ∧
      ((∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
          R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
            matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
        (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
          a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
          R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
            altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)) := by
  obtain ⟨β, hβ, hcls, u, hRu, -⟩ := hR0
  let R' : Subgroup (ggU .PSp n f).K :=
    ((ggU .PSp n f).D.rootGroup β).map (MulAut.conj u).toMonoidHom
  refine ⟨R', ?_, ?_⟩
  · rw [hRu]
    rfl
  · by_cases hl : GGLongRoot (ggU .PSp n f).D β
    · left
      obtain ⟨v, hv, heq⟩ := exists_matTransvGroup_eq_rootGroup_PSp n f hβ hl u
      exact ⟨v, hv, heq⟩
    · right
      obtain ⟨a₁, a₂, ha₁, ha₂, hli, horth, heq⟩ :=
        exists_altSiegelGroup_eq_rootGroup_PSp n f hβ hl u
      exact ⟨a₁, a₂, ha₁, ha₂, hli, horth, heq⟩

private theorem nbrPSp_blockIdempotents
    (n f : ℕ) (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (K' : Subgroup (ggU .PSp n f).K)
    (hK'comp : IsComponentOf K' ((Subgroup.centralizer S').comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) :
    ∃ ε eK : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f),
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε ∧
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∧
      eK * ε = eK ∧
      (eK = ε ∨ (eK ≠ ε ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          eK ≠ eK ∧
        ε = eK + formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          eK)) ∧
      IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K)⁆ := by
  obtain ⟨ε, hε, hK'ε⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSp n (GaloisField 2 f) S' hS' hK'comp
  obtain ⟨eK, heK, heKε, hsplit⟩ :=
    exists_isPrimIdemIn_of_isPrimAdjIdemIn_PSp n f S' hSU' hS' hε
  exact ⟨ε, eK, hε, heK, heKε, hsplit, hK'ε⟩

private theorem nbrPSp_alt6_of_map {U X : Type} [Group U] [Group X] (ψ : U →* X)
    (hinj : Function.Injective ψ) {K' : Subgroup U} {K : Subgroup X} (h : K'.map ψ = K)
    (e : ↥K' ≃* alternatingGroup (Fin 6)) :
    Nonempty (↥K ≃* alternatingGroup (Fin 6)) := by
  refine ⟨?_⟩
  let σ : ↥K' ≃* ↥K :=
    (Subgroup.equivMapOfInjective K' ψ hinj).trans (MulEquiv.subgroupCongr h)
  exact σ.symm.trans e

private theorem nbrPSp_quasisimple_subgroupOf {G : Type} [Group G] {J K : Subgroup G}
    (hJK : J ≤ K) (hJ : CFSG.Assembly.IsQuasisimple ↥J) :
    CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf K) :=
  CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ

private theorem nbrPSp_normalizes_component
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) :
    D ≤ Subgroup.normalizer (K : Set X) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hKN : IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) :=
    CFSG.Assembly.IsComponentOf.of_le_of_le hKcomp (le_inf hKG₀ hKcomp.1) inf_le_right
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := h15.2.2
  have hDJ : D ≤ Subgroup.centralizer (J : Set X) := by
    intro d' hd'
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (h15.1 hj).2 d' hd').symm
  intro d hd
  have hdB : d ∈ B₁ := h11 hd
  have heB : e ∈ B₁ := h11 heD
  have hde : Commute d e :=
    congrArg Subtype.val (h9.1.is_comm.comm (⟨d, hdB⟩ : ↥B₁) (⟨e, heB⟩ : ↥B₁))
  have hdG₀ : d ∈ Subgroup.normalizer (G₀ : Set X) := h7 hdB
  have hdC : d ∈ Subgroup.normalizer (Subgroup.centralizer ({e} : Set X) : Set X) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hde)
  have hdN : d ∈ Subgroup.normalizer
      ((G₀ ⊓ Subgroup.centralizer ({e} : Set X)) : Set X) :=
    Subgroup.zpowers_le.mp (Subgroup.le_normalizer_inf
      (Subgroup.zpowers_le.mpr hdG₀) (Subgroup.zpowers_le.mpr hdC))
  have hdNmap : (G₀ ⊓ Subgroup.centralizer ({e} : Set X)).map
      (MulAut.conj d).toMonoidHom = G₀ ⊓ Subgroup.centralizer ({e} : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hdN
  have hL₂ : IsComponentOf (K.map (MulAut.conj d).toMonoidHom)
      (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hKN
      (MulAut.conj d).toMonoidHom (MulAut.conj d).injective
    rwa [hdNmap] at h
  have hJmap : J ≤ K.map (MulAut.conj d).toMonoidHom := by
    intro j hj
    refine ⟨j, hJK hj, ?_⟩
    change (MulAut.conj d) j = j
    rw [MulAut.conj_apply]
    have hc := (Subgroup.mem_centralizer_iff.mp (hDJ hd)) j hj
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  have hKeq : K = K.map (MulAut.conj d).toMonoidHom :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJq hKN hL₂ hJK hJmap
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKeq.symm

private theorem nbrPSp_not_centralizes_component
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    ¬ D ≤ Subgroup.centralizer (K : Set X) := by
  intro hD
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hKN : IsComponentOf K (G₀ ⊓ Subgroup.centralizer ({e} : Set X)) :=
    CFSG.Assembly.IsComponentOf.of_le_of_le hKcomp (le_inf hKG₀ hKcomp.1) inf_le_right
  have hKC : K ≤ Subgroup.centralizer (D : Set X) := Subgroup.le_centralizer_iff.mpr hD
  have hKH : K ≤ G₀ ⊓ Subgroup.centralizer (D : Set X) := le_inf hKG₀ hKC
  have hHK : G₀ ⊓ Subgroup.centralizer (D : Set X) ≤
      G₀ ⊓ Subgroup.centralizer ({e} : Set X) := by
    refine le_inf inf_le_left ?_
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2) e heD).symm)
  have hKD : IsComponentOf K (G₀ ⊓ Subgroup.centralizer (D : Set X)) :=
    CFSG.Assembly.IsComponentOf.of_le_of_le hKN hKH hHK
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := h15.2.2
  have hEq : J = K :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJq h15 hKD le_rfl hJK
  exact hKne hEq.symm

private theorem nbrPSp_alt6_inner
    {X : Type} [Group X] {D K J : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hDexp : ∀ d ∈ D, d ^ p = 1)
    (hDN : D ≤ Subgroup.normalizer (K : Set X))
    (hDC : ¬ D ≤ Subgroup.centralizer (K : Set X))
    (hK6 : ↥K ≃* alternatingGroup (Fin 6)) (hDJ : D ≤ Subgroup.centralizer (J : Set X)) :
    ∃ k : ↥K, J.subgroupOf K ≤ Subgroup.centralizer ({k} : Set ↥K) ∧ orderOf k = p := by
  obtain ⟨d, hd, hdC⟩ := Set.not_subset.mp hDC
  have hdN : d ∈ Subgroup.normalizer (K : Set X) := hDN hd
  have hmap : K.map (MulAut.conj d).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hdN
  let θ : MulAut ↥K :=
    (Subgroup.equivMapOfInjective K (MulAut.conj d).toMonoidHom
      (MulAut.conj d).injective).trans (MulEquiv.subgroupCongr hmap)
  have hθ_apply : ∀ x : ↥K, (θ x : X) = d * (x : X) * d⁻¹ := fun x => rfl
  have hpow : ∀ (n : ℕ) (x : ↥K), ((θ ^ n) x : X) = d ^ n * (x : X) * (d ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ']
        change (θ ((θ ^ n) x) : X) = d ^ (n + 1) * (x : X) * (d ^ (n + 1))⁻¹
        rw [hθ_apply, ih]
        group
  have hθ_pow : θ ^ p = 1 := by
    ext x
    rw [hpow p x, hDexp d hd]
    simp
  have hθodd : Odd (orderOf θ) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hθ_pow)
  have hθ_ne : θ ≠ 1 := by
    intro h1
    apply hdC
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hdx : d * x * d⁻¹ = x := by
      have h2 : (θ ⟨x, hx⟩ : X) = x := by
        have := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : ↥K) : X)) h1
        simpa using this
      rwa [hθ_apply] at h2
    calc x * d = (d * x * d⁻¹) * d := by conv_lhs => rw [← hdx]
      _ = d * x := by group
  obtain ⟨k, hk⟩ := CFSG.ASVolI.burnsideA26_a6 hK6 θ hθodd
  have hk_apply : ∀ x : ↥K, (MulAut.conj k) x = θ x := fun x => by rw [hk]
  have hZ : Subgroup.center ↥K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : hK6 z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨w, rfl⟩ := hK6.surjective y
      simpa only [map_mul] using congrArg hK6 (hz w)
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hz'
    exact hK6.injective (by rw [hz', map_one])
  refine ⟨k, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxJ : (x : X) ∈ J := Subgroup.mem_subgroupOf.mp hx
    have h1 : k * (x : X) * k⁻¹ = (x : X) := by
      have h2 : ((MulAut.conj k) x : X) = (θ x : X) := congrArg Subtype.val (hk_apply x)
      rw [MulAut.conj_apply, hθ_apply] at h2
      have hdx : d * (x : X) * d⁻¹ = x := by
        have hc := (Subgroup.mem_centralizer_iff.mp (hDJ hd)) (x : X) hxJ
        rw [← hc]; group
      rwa [hdx] at h2
    apply Subtype.ext
    show (x : X) * k = k * (x : X)
    conv_lhs => rw [← h1]
    simp only [Subgroup.coe_inv]
    group
  · have hkp : k ^ p = 1 := by
      have h1 : (MulAut.conj k) ^ p = 1 := by rw [hk]; exact hθ_pow
      have h2 : MulAut.conj (k ^ p) = 1 := by rwa [← map_pow] at h1
      have hmem : k ^ p ∈ Subgroup.center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro y
        have hy : (MulAut.conj (k ^ p)) y = y := by rw [h2]; rfl
        simp only [MulAut.conj_apply] at hy
        calc y * k ^ p = ((k ^ p) * y * (k ^ p)⁻¹) * k ^ p := by
              conv_rhs => rw [hy]
          _ = k ^ p * y := by group
      rwa [hZ, Subgroup.mem_bot] at hmem
    have hdvd : orderOf k ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hkp
    have hk1 : k ≠ 1 := by
      intro hk1
      apply hθ_ne
      rw [← hk, hk1, map_one]
    rcases hp.eq_one_or_self_of_dvd (orderOf k) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hk1
    · exact h

private theorem nbrPSp_alt6_contradiction
    {K : Type} [Group K] [Finite K] (e : K ≃* alternatingGroup (Fin 6))
    {J : Subgroup K} (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    {k : K} (hk : J ≤ Subgroup.centralizer ({k} : Set K)) (hk1 : k ≠ 1)
    (hodd : Odd (orderOf k)) :
    False := by
  have hle : orderOf k ≤ 5 := by
    have := CFSG.LocalAnalysis.UniquenessCase.UC6.K323A.orderOf_le_five_alt6 (e k)
    rwa [MulEquiv.orderOf_eq] at this
  have hne1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  have hcase : orderOf k = 3 ∨ orderOf k = 5 := by
    have hge : 1 ≤ orderOf k := orderOf_pos k
    interval_cases orderOf k
    · exact absurd rfl hne1
    · exact absurd hodd (by decide)
    · exact Or.inl rfl
    · exact absurd hodd (by decide)
    · exact Or.inr rfl
  have hcard_eq : Nat.card ↥(Subgroup.centralizer ({k} : Set K)) =
      Nat.card ↥(Subgroup.centralizer ({e k} : Set (alternatingGroup (Fin 6)))) := by
    have hmap := CFSG.LocalAnalysis.ComponentInitial.map_centralizer_singleton_mulEquiv e k
    exact Nat.card_congr ((Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({k} : Set K)) e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).toEquiv
  rcases hcase with h3 | h5
  · have h9 : Nat.card ↥(Subgroup.centralizer ({e k} : Set (alternatingGroup (Fin 6)))) = 9 :=
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_orderOf_eq_three
        (x := e k) (by rw [MulEquiv.orderOf_eq]; exact h3)
    have hcardC : Nat.card ↥(Subgroup.centralizer ({k} : Set K)) = 9 := by
      rw [hcard_eq, h9]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hP : IsPGroup 3 ↥(Subgroup.centralizer ({k} : Set K)) := by
      apply IsPGroup.of_card (n := 2)
      rw [hcardC]; norm_num
    haveI := hP.isNilpotent
    exact (CFSG.LocalAnalysis.ComponentInitial.not_le_of_isQuasisimple_of_isSolvable
      hJq IsNilpotent.to_isSolvable) hk
  · have h5c : Nat.card ↥(Subgroup.centralizer ({e k} : Set (alternatingGroup (Fin 6)))) = 5 :=
      CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_orderOf_eq_five (e k)
        (by rw [MulEquiv.orderOf_eq]; exact h5)
    have hcardC : Nat.card ↥(Subgroup.centralizer ({k} : Set K)) = 5 := by
      rw [hcard_eq, h5c]
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hP : IsPGroup 5 ↥(Subgroup.centralizer ({k} : Set K)) := by
      apply IsPGroup.of_card (n := 1)
      rw [hcardC]; norm_num
    haveI := hP.isNilpotent
    exact (CFSG.LocalAnalysis.ComponentInitial.not_le_of_isQuasisimple_of_isSolvable
      hJq IsNilpotent.to_isSolvable) hk

private theorem nbrPSp_notA6
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J)
    (K' : Subgroup (ggU .PSp n f).K)
    (hK'map : K'.map ψ = K) :
    IsEmpty (↥K' ≃* alternatingGroup (Fin 6)) := by
  refine ⟨fun hφ => ?_⟩
  have hDN : D ≤ Subgroup.normalizer (K : Set X) :=
    nbrPSp_normalizes_component n f ψ p G₀ B₁ D J L x hH e heD K hKG₀ hKcomp hJK
  have hDC : ¬ D ≤ Subgroup.centralizer (K : Set X) :=
    nbrPSp_not_centralizes_component n f ψ p G₀ B₁ D J L x hH e heD K hKG₀ hKcomp hJK hKne
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hinj : Function.Injective ψ := nbrPSp_injective n f ψ h2
  obtain ⟨eK⟩ := nbrPSp_alt6_of_map ψ hinj hK'map hφ
  have hDexp : ∀ d ∈ D, d ^ p = 1 := fun d hd => h9.2 d (h11 hd)
  have hDJ : D ≤ Subgroup.centralizer (J : Set X) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (h15.1 hj).2 d hd).symm
  obtain ⟨k, hk, hkord⟩ := nbrPSp_alt6_inner h5 h6 hDexp hDN hDC eK hDJ
  have hJq : CFSG.Assembly.IsQuasisimple ↥(J.subgroupOf K) :=
    nbrPSp_quasisimple_subgroupOf hJK h15.2.2
  exact nbrPSp_alt6_contradiction eK hJq hk
    (fun hk1 => h5.ne_one (by rw [← hkord, hk1, orderOf_one]))
    (by rw [hkord]; exact h5.odd_of_ne_two h6)

private lemma nbrPSp_rank_le_two_of_mulVec_mem {n : ℕ} {F : Type} [Field F] [DecidableEq F]
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (a₁ a₂ : Fin n ⊕ Fin n → F)
    (h : ∀ x, Matrix.mulVec A x ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) :
    Matrix.rank A ≤ 2 := by
  have hrange : A.mulVecLin.range ≤ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) := by
    rintro y ⟨x, rfl⟩
    simpa [Matrix.mulVecLin_apply] using h x
  have h1 : Module.finrank F ↥(A.mulVecLin.range) ≤
      Module.finrank F ↥(Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) :=
    Submodule.finrank_mono hrange
  have h2 : Module.finrank F ↥(Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))) ≤ 2 := by
    have hc := finrank_span_le_card (R := F) ({a₁, a₂} : Set (Fin n ⊕ Fin n → F))
    refine le_trans hc ?_
    rw [show ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)).toFinset
        = ({a₁, a₂} : Finset (Fin n ⊕ Fin n → F)) by simp]
    exact le_trans (Finset.card_insert_le a₁ {a₂}) (by simp)
  rw [Matrix.rank]
  exact le_trans h1 h2

private lemma nbrPSp_vecMulVec_ne_zero {n : ℕ} {F : Type} [Field F]
    {v w : Fin n ⊕ Fin n → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    Matrix.vecMulVec v w ≠ (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
  have hh := congrFun (congrFun h i) j
  simp only [Matrix.vecMulVec_apply, Matrix.zero_apply] at hh
  exact (mul_ne_zero hi hj) hh

private lemma nbrPSp_transvUnit {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (v : Fin n ⊕ Fin n → F) :
    ∃ g : GL (Fin n ⊕ Fin n) F,
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        1 + Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v) := by
  set A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n
        ⊕ Fin n) F) v) with hA
  have hdot : Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      F) v ⬝ᵥ v = 0 := by
    have h := CFSG.ClassicalGroups.Symplectic.spForm_self (m := n) (K := F) v
    rw [CFSG.ClassicalGroups.Symplectic.spForm_apply] at h
    rw [dotProduct_comm]
    exact h
  have hAA : A * A = 0 := by
    rw [hA, Matrix.vecMulVec_mul]
    have hvec : Matrix.vecMul (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
        (Fin n ⊕ Fin n) F) v)
        (Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
            (Fin n ⊕ Fin n) F) v)) =
        (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v
            ⬝ᵥ v) •
          (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
              v) := by
      funext j
      simp only [Matrix.vecMul, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
        dotProduct]
      rw [Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm), Finset.sum_mul]
    rw [hvec, hdot, zero_smul]
    ext i j
    simp
  have hAA2 : A + A = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (A i j)
  have hunit : (1 + A) * (1 + A) = 1 := by
    have h : (1 + A) * (1 + A) = 1 + A + (A + A * A) := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
        Matrix.mul_one]
    rw [h, hAA, add_zero, add_assoc, hAA2, add_zero]
  exact ⟨Units.mk (1 + A) (1 + A) hunit hunit, by rw [Units.val_mk, hA]⟩

private def nbrPSp_HasShortElm
    (n f : ℕ) (R' : Subgroup (CFSG.Open.StatedSp n (GaloisField 2 f))) : Prop :=
  ∃ g ∈ R', g ≠ 1 ∧ Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) ≤ 2

private lemma nbrPSp_matTransv_shortElm
    (n f : ℕ) (R' : Subgroup (ggU .PSp n f).K)
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f) (hv : v ≠ 0)
    (hm : R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) :
    nbrPSp_HasShortElm n f R' := by
  obtain ⟨g₀, hg₀⟩ := nbrPSp_transvUnit (n := n) (F := GaloisField 2 f) v
  have hGv : Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v ≠ 0 := by
    intro h
    refine hv (Matrix.eq_zero_of_mulVec_eq_zero ?_ h)
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hgen : g₀ ∈ matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    rw [hg₀]
    simp
  have hmap : g₀ ∈ R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
    rw [hm]
    exact hgen
  obtain ⟨g, hgR, hgval⟩ := Subgroup.mem_map.mp hmap
  refine ⟨g, hgR, ?_, ?_⟩
  · intro hg1
    have hg0 : g₀ = 1 := by
      rw [← hgval, hg1]
      rfl
    have hmat1 : (g₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = 1 := by
      rw [hg0]
      rfl
    have hz : Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) = 0 := by
      have h' : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) +
          Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) = 1 :=
        hg₀.symm.trans hmat1
      exact add_left_cancel
        (a := (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
        (by simpa using h')
    exact (nbrPSp_vecMulVec_ne_zero hv hGv) hz
  · have hmat : ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1 =
        Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
      have hval : ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
          (g₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
        congrArg (fun u : GL (Fin n ⊕ Fin n) (GaloisField 2 f) =>
          (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) hgval
      rw [hval, hg₀]
      simp
    rw [hmat]
    exact le_trans (Matrix.rank_vecMulVec_le v _) (by norm_num)

private lemma nbrPSp_exists_dot_J_ne_zero {n f : ℕ} {a : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (ha : a ≠ 0) :
    ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f,
      a ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v ≠ 0 := by
  have hsep := (CFSG.ClassicalGroups.Symplectic.spForm_nondegenerate (m := n)
    (K := GaloisField 2 f)).1
  by_contra h
  push_neg at h
  exact ha (hsep a (by
    intro y
    rw [CFSG.ClassicalGroups.Symplectic.spForm_apply]
    exact h y))

private lemma nbrPSp_altSiegel_shortElm
    (n f : ℕ) (R' : Subgroup (ggU .PSp n f).K)
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f) (ha₁ : a₁ ≠ 0)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (horth : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0)
    (hm : R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) :
    nbrPSp_HasShortElm n f R' := by
  classical
  obtain ⟨g₀, hg₀mem, hg₀act⟩ :=
    CFSG.StandardType.LieKnownR2.Short.exists_mem_spAltSiegel_mulVec (n := n)
      (F := GaloisField 2 f) horth (1 : GaloisField 2 f)
  have hg₀gl : (g₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ :=
    Subgroup.mem_comap.mp hg₀mem
  have hmap : (g₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
    rw [hm]
    exact hg₀gl
  obtain ⟨g, hgR, hgval⟩ := Subgroup.mem_map.mp hmap
  obtain ⟨v, hv⟩ := nbrPSp_exists_dot_J_ne_zero (n := n) (f := f) ha₁
  have hv' : (a₂ ⬝ᵥ Matrix.mulVec
        (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) • a₁ +
      (a₁ ⬝ᵥ Matrix.mulVec
        (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) • a₂ ≠ 0 := by
    intro hzero
    exact hv ((LinearIndependent.pair_iff.mp hli)
      (a₂ ⬝ᵥ Matrix.mulVec
        (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v)
      (a₁ ⬝ᵥ Matrix.mulVec
        (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) hzero).2
  refine ⟨g, hgR, ?_, ?_⟩
  · intro hg1
    have hg0 : g₀ = 1 := by
      apply Subtype.ext
      rw [← hgval, hg1]
      rfl
    have hact := hg₀act v
    have hv1 : Matrix.mulVec ((g₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v = v := by
      rw [hg0]
      exact Matrix.one_mulVec v
    rw [hv1] at hact
    simp only [one_mul] at hact
    have hzero : (a₂ ⬝ᵥ Matrix.mulVec
          (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) • a₁ +
        (a₁ ⬝ᵥ Matrix.mulVec
          (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) • a₂ = 0 := by
      calc (a₂ ⬝ᵥ Matrix.mulVec
              (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) • a₁ +
            (a₁ ⬝ᵥ Matrix.mulVec
              (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) • a₂
          = ((v + (a₂ ⬝ᵥ Matrix.mulVec
                (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) • a₁) +
              (a₁ ⬝ᵥ Matrix.mulVec
                (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) v) • a₂) - v :=
            by abel
        _ = v - v := by rw [← hact]
        _ = 0 := sub_self v
    exact hv' hzero
  · have hmem : ∀ x, Matrix.mulVec (((g₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) x ∈
        Submodule.span (GaloisField 2 f)
          ({a₁, a₂} : Set ((Fin n ⊕ Fin n) → GaloisField 2 f)) := by
      intro x
      have hx := hg₀act x
      have heq : Matrix.mulVec (((g₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) x =
          (a₂ ⬝ᵥ Matrix.mulVec
            (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) x) • a₁ +
          (a₁ ⬝ᵥ Matrix.mulVec
            (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) x) • a₂ := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hx]
        simp only [one_mul]
        abel
      rw [heq]
      have h1 : (a₂ ⬝ᵥ Matrix.mulVec
            (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) x) • a₁ ∈
          Submodule.span (GaloisField 2 f)
            ({a₁, a₂} : Set ((Fin n ⊕ Fin n) → GaloisField 2 f)) :=
        Submodule.smul_mem
          (Submodule.span (GaloisField 2 f)
            ({a₁, a₂} : Set ((Fin n ⊕ Fin n) → GaloisField 2 f)))
          (a₂ ⬝ᵥ Matrix.mulVec (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) x)
          (Submodule.subset_span (by simp))
      have h2 : (a₁ ⬝ᵥ Matrix.mulVec
            (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) x) • a₂ ∈
          Submodule.span (GaloisField 2 f)
            ({a₁, a₂} : Set ((Fin n ⊕ Fin n) → GaloisField 2 f)) :=
        Submodule.smul_mem
          (Submodule.span (GaloisField 2 f)
            ({a₁, a₂} : Set ((Fin n ⊕ Fin n) → GaloisField 2 f)))
          (a₁ ⬝ᵥ Matrix.mulVec (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) x)
          (Submodule.subset_span (by simp))
      exact Submodule.add_mem _ h1 h2
    have hrank : Matrix.rank (((g₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) ≤ 2 :=
      nbrPSp_rank_le_two_of_mulVec_mem _ a₁ a₂ hmem
    rw [show ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        ((g₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) from
      congrArg (fun u : GL (Fin n ⊕ Fin n) (GaloisField 2 f) =>
        (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) hgval]
    exact hrank

private lemma nbrPSp_shortElm
    (n f : ℕ) (R' : Subgroup (ggU .PSp n f).K)
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)) :
    nbrPSp_HasShortElm n f R' := by
  rcases hgeo with ⟨v, hv, hm⟩ | ⟨a₁, a₂, ha₁, ha₂, hli, horth, hm⟩
  · exact nbrPSp_matTransv_shortElm n f R' v hv hm
  · exact nbrPSp_altSiegel_shortElm n f R' a₁ a₂ ha₁ hli horth hm

private theorem nbrPSp_blockDegree_selfDual
    (n f : ℕ)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (ggU .PSp n f).K)
    (ε eK : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (hK'ε : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hR'K' : R' ≤ K')
    (hshort : nbrPSp_HasShortElm n f R') (hself : eK = ε) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 4 := by
  obtain ⟨g, hgR, hg1, hgrank⟩ := hshort
  obtain ⟨Gε, hGε⟩ : ∃ Gε : Subgroup (ggU .PSp n f).K,
      Gε = (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K) :=
    ⟨_, rfl⟩
  rw [← hGε] at hK'ε
  have hgGε : g ∈ Gε := by
    have hle : ⁅Gε, Gε⁆ ≤ Gε := by
      refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem Gε (Subgroup.mul_mem Gε (Subgroup.mul_mem Gε ha hb)
        (Subgroup.inv_mem Gε ha)) (Subgroup.inv_mem Gε hb)
    exact hle (hK'ε.1 (hR'K' hgR))
  have hgmem : g ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :=
    hGε ▸ hgGε
  have hgS : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ Subgroup.centralizer S' :=
    (Subgroup.mem_comap.mp hgmem).1
  have hge : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ glFixing (1 - ε) :=
    (Subgroup.mem_comap.mp hgmem).2
  have hgeK : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ glFixing (1 - eK) := by
    rw [hself]
    exact hge
  have hdvd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∣
      Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) :=
    blockDegree_dvd_rank_sub_one_of_glFixing (S := S') hS' hodd' heK hgS hgeK
  have hgne : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ≠ 1 :=
    fun h => hg1 (Subtype.ext h)
  have hAne : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) ≠ 0 := by
    intro h0
    exact hgne (Units.ext (sub_eq_zero.mp h0))
  have hrange_ne : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVecLin.range ≠ ⊥ := by
    intro hbot
    apply hAne
    ext i j
    have hmem : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVec (Pi.single j 1) ∈
        (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVecLin.range :=
      LinearMap.mem_range.mpr ⟨Pi.single j 1, rfl⟩
    rw [hbot] at hmem
    have hz : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVec
          (Pi.single j 1) = 0 := by
      simpa using hmem
    have := congrFun hz i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
  have hrank_pos : 1 ≤ Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) := by
    rw [Matrix.rank, Nat.one_le_iff_ne_zero]
    intro hzero
    exact hrange_ne (Submodule.finrank_eq_zero.mp hzero)
  have hle : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ≤ 2 :=
    le_trans (Nat.le_of_dvd hrank_pos hdvd) hgrank
  omega

private theorem nbrPSp_blockDegree_dualPair
    (n f : ℕ)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' R' : Subgroup (ggU .PSp n f).K)
    (ε eK : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (hK'ε : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hR'K' : R' ≤ K')
    (hshort : nbrPSp_HasShortElm n f R')
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      eK ≠ eK)
    (heq : ε = eK + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      eK) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2 := by
  obtain ⟨g, hgR, hg1, hgrank⟩ := hshort
  obtain ⟨Gε, hGε⟩ : ∃ Gε : Subgroup (ggU .PSp n f).K,
      Gε = (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K) :=
    ⟨_, rfl⟩
  rw [← hGε] at hK'ε
  have hgGε : g ∈ Gε := by
    have hle : ⁅Gε, Gε⁆ ≤ Gε := by
      refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem Gε (Subgroup.mul_mem Gε (Subgroup.mul_mem Gε ha hb)
        (Subgroup.inv_mem Gε ha)) (Subgroup.inv_mem Gε hb)
    exact hle (hK'ε.1 (hR'K' hgR))
  have hgmem : g ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :=
    hGε ▸ hgGε
  have hgS : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ Subgroup.centralizer S' :=
    (Subgroup.mem_comap.mp hgmem).1
  have hge : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ glFixing (1 - ε) :=
    (Subgroup.mem_comap.mp hgmem).2
  let G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    Matrix.fromBlocks 0 1 (-1) 0
  have hGdet : IsUnit G.det := by
    dsimp only [G]
    exact isUnit_iff_ne_zero.mpr (by
      rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) =
          CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
      exact CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero)
  have hGh : Matrix.transpose (G.map (RingHom.id (GaloisField 2 f))) = G := by
    dsimp only [G]
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.LieType.BorelTits.spJ n (GaloisField 2 f) from rfl]
    rw [show ((CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) =
        (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) from rfl]
    exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two
  have hSU : ∀ s ∈ S', Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) * G *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = G := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU' s hs)
    simpa [G] using h
  have hgiso : Matrix.transpose (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) * G *
      ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = G := by
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      g.property
    simpa [G] using h
  have hge' : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      glFixing (1 - (eK + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) eK)) := by
    rw [← heq]
    exact hge
  have hdvd : 2 * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∣
      Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) :=
    two_mul_blockDegree_dvd_rank_sub_one_of_formAdj_ne (RingHom.id (GaloisField 2 f))
      (fun x => rfl) hGdet hGh hSU hS' hodd' heK hadj hgS hgiso hge'
  have hgne : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ≠ 1 :=
    fun h => hg1 (Subtype.ext h)
  have hAne : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) ≠ 0 := by
    intro h0
    exact hgne (Units.ext (sub_eq_zero.mp h0))
  have hrange_ne : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVecLin.range ≠ ⊥ := by
    intro hbot
    apply hAne
    ext i j
    have hmem : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVec (Pi.single j 1) ∈
        (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVecLin.range :=
      LinearMap.mem_range.mpr ⟨Pi.single j 1, rfl⟩
    rw [hbot] at hmem
    have hz : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVec
          (Pi.single j 1) = 0 := by
      simpa using hmem
    have := congrFun hz i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
  have hrank_pos : 1 ≤ Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) := by
    rw [Matrix.rank, Nat.one_le_iff_ne_zero]
    intro hzero
    exact hrange_ne (Submodule.finrank_eq_zero.mp hzero)
  have hle : 2 * blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ≤ 2 :=
    le_trans (Nat.le_of_dvd hrank_pos hdvd) hgrank
  omega

private theorem nbrPSp_blockDegree
    (n f : ℕ) (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (K' : Subgroup (ggU .PSp n f).K) (R' : Subgroup (ggU .PSp n f).K)
    (ε eK : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (heK : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK)
    (hsplit : eK = ε ∨ (eK ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        eK ≠ eK ∧
      ε = eK + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        eK))
    (hK'ε : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hR'K' : R' ≤ K')
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)) :
    (eK = ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2) ∨
      (eK = ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 4) ∨
      (eK ≠ ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2) := by
  have hshort : nbrPSp_HasShortElm n f R' := nbrPSp_shortElm n f R' hgeo
  rcases hsplit with hself | ⟨hne, hadj, heq⟩
  · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) eK < 2
    · exact Or.inl ⟨hself, hd⟩
    · exact Or.inr (Or.inl ⟨hself, by omega,
        nbrPSp_blockDegree_selfDual n f S' hS' hodd' K' R' ε eK heK hK'ε hR'K'
          hshort hself⟩)
  · exact Or.inr (Or.inr ⟨hne,
      nbrPSp_blockDegree_dualPair n f S' hSU' hS' hodd' K' R' ε eK heK hK'ε hR'K'
        hshort hadj heq⟩)

private lemma nbrPSp_blockDegree_pos {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (he : IsPrimIdemIn A e) :
    1 ≤ blockDegree A e := by
  have hmem : e ∈ (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) := by
    refine Submodule.mem_map.mpr ⟨e, he.1, ?_⟩
    simpa [LinearMap.mulRight_apply] using he.2.1.eq
  have hne : (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e) ≠ ⊥ := by
    intro h
    rw [h] at hmem
    exact he.2.2.1 (by simpa using hmem)
  rw [blockDegree, Nat.one_le_iff_ne_zero]
  intro hzero
  exact hne ((Submodule.finrank_eq_zero).mp hzero)

private lemma nbrPSp_rank_pos {n f : ℕ}
    {g : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))} (hg1 : g ≠ 1) :
    1 ≤ Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) := by
  have hgne : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ≠ 1 :=
    fun h => hg1 (Subtype.ext h)
  have hAne : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) ≠ 0 := by
    intro h0
    exact hgne (Units.ext (sub_eq_zero.mp h0))
  have hrange_ne : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVecLin.range ≠ ⊥ := by
    intro hbot
    apply hAne
    ext i j
    have hmem : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVec (Pi.single j 1) ∈
        (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVecLin.range :=
      LinearMap.mem_range.mpr ⟨Pi.single j 1, rfl⟩
    rw [hbot] at hmem
    have hz : (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1).mulVec
          (Pi.single j 1) = 0 := by
      simpa using hmem
    have := congrFun hz i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
  rw [Matrix.rank, Nat.one_le_iff_ne_zero]
  intro hzero
  exact hrange_ne (Submodule.finrank_eq_zero.mp hzero)

private lemma nbrPSp_map_subtype_injective
    {n f : ℕ} {A B : Subgroup (ggU .PSp n f).K}
    (h : A.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      B.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) : A = B := by
  ext x
  constructor
  · intro hx
    have hx' : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x ∈
        A.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [h] at hx'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    rwa [Subtype.ext hyx] at hy
  · intro hx
    have hx' : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype x ∈
        B.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype :=
      Subgroup.mem_map_of_mem _ hx
    rw [← h] at hx'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    rwa [Subtype.ext hyx] at hy

private lemma nbrPSp_mem_glBlockCentralizer
    (n f : ℕ) (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (K' R' : Subgroup (ggU .PSp n f).K)
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hK'ε : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hR'K' : R' ≤ K') {g : (ggU .PSp n f).K} (hgR : g ∈ R') :
    g ∈ (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
      Subgroup (ggU .PSp n f).K) := by
  obtain ⟨Gε, hGε⟩ : ∃ Gε : Subgroup (ggU .PSp n f).K,
      Gε = (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K) := ⟨_, rfl⟩
  rw [← hGε] at hK'ε
  have hgGε : g ∈ Gε := by
    have hle : ⁅Gε, Gε⁆ ≤ Gε := by
      refine Subgroup.commutator_le.mpr (fun a ha b hb => ?_)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem Gε (Subgroup.mul_mem Gε (Subgroup.mul_mem Gε ha hb)
        (Subgroup.inv_mem Gε ha)) (Subgroup.inv_mem Gε hb)
    exact hle (hK'ε.1 (hR'K' hgR))
  exact hGε ▸ hgGε

private lemma nbrPSp_matTransv_rank_le_one
    (n f : ℕ) (R' : Subgroup (CFSG.Open.StatedSp n (GaloisField 2 f)))
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f) (hv : v ≠ 0)
    (hm : R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) :
    ∃ g ∈ R', g ≠ 1 ∧
      Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) ≤ 1 := by
  obtain ⟨g₀, hg₀⟩ := nbrPSp_transvUnit (n := n) (F := GaloisField 2 f) v
  have hGv : Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v ≠ 0 := by
    intro h
    refine hv (Matrix.eq_zero_of_mulVec_eq_zero ?_ h)
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hgen : g₀ ∈ matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
    refine Subgroup.subset_closure ⟨1, ?_⟩
    rw [hg₀]
    simp
  have hmap : g₀ ∈ R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
    rw [hm]
    exact hgen
  obtain ⟨g, hgR, hgval⟩ := Subgroup.mem_map.mp hmap
  refine ⟨g, hgR, ?_, ?_⟩
  · intro hg1
    have hg0 : g₀ = 1 := by
      rw [← hgval, hg1]
      rfl
    have hmat1 : (g₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = 1 := by
      rw [hg0]
      rfl
    have hz : Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) = 0 := by
      have h' : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) +
          Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) = 1 :=
        hg₀.symm.trans hmat1
      exact add_left_cancel
        (a := (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
        (by simpa using h')
    exact (nbrPSp_vecMulVec_ne_zero hv hGv) hz
  · have hmat : ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1 =
        Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
      have hval : ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
          (g₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
        congrArg (fun u : GL (Fin n ⊕ Fin n) (GaloisField 2 f) =>
          (u : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) hgval
      rw [hval, hg₀]
      simp
    rw [hmat]
    exact Matrix.rank_vecMulVec_le v _

private theorem nbrPSpx_base
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x) :
    ∃ (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
      (J' : Subgroup (ggU .PSp n f).K),
      (∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) ∧
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      (∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
        s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
        (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S) ∧
      IsComponentOf J' ((Subgroup.centralizer S).comap
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) ∧
      J'.map ψ = J := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let j : ↥(CFSG.Open.StatedSp n F) →* GL (Fin n ⊕ Fin n) F :=
    (CFSG.Open.StatedSp n F).subtype
  let P : GL (Fin n ⊕ Fin n) F → Prop := fun s => s ∈ CFSG.Open.StatedSp n F
  let S : Set (GL (Fin n ⊕ Fin n) F) := {s | P s ∧ ∃ d ∈ D, IsGLLift j ψ s d}
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [h1]
    exact h15
  have hlift : ∀ d ∈ D, ∃ s : GL (Fin n ⊕ Fin n) F, P s ∧ IsGLLift j ψ s d := by
    intro d hd
    have hdB : d ∈ B₁ := h11 hd
    have hbN : d ∈ Subgroup.normalizer (ψ.range : Set X) := by
      rw [h1]
      exact h7 hdB
    have hb : GGPsiInnerDiag (Symplectic.rootDatum n F) ψ d := h8 d hdB
    obtain ⟨s₀, hs₀⟩ := exists_conj_eq_PSp n F ψ h2 hbN hb
    exact ⟨(s₀ : GL (Fin n ⊕ Fin n) F), s₀.2,
      fun u => ⟨s₀ * u * s₀⁻¹, rfl, hs₀ u⟩⟩
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift j
      (Subgroup.subtype_injective (CFSG.Open.StatedSp n F)) ψ h2 P hJ hlift
  refine ⟨S, J', ?_, ?_, ?_, ?_, hJ'comp, hJ'map⟩
  · intro s hs
    exact hs.1
  · intro s hs s' hs'
    obtain ⟨d, hdD, hsl⟩ := hs.2
    obtain ⟨d', hd'D, hs'l⟩ := hs'.2
    have hdB : d ∈ B₁ := h11 hdD
    have hd'B : d' ∈ B₁ := h11 hd'D
    have hbb' : Commute d d' :=
      congrArg Subtype.val (h9.1.is_comm.comm ⟨d, hdB⟩ ⟨d', hd'B⟩)
    obtain ⟨s₀, hs₀, hsl₀⟩ := sASp_lift_to_mem n F ψ hs.1 hsl
    obtain ⟨s₁, hs₁, hsl₁⟩ := sASp_lift_to_mem n F ψ hs'.1 hs'l
    have hc := conj_eq_commute_PSp n F ψ h2 hbb' hsl₀ hsl₁
    have hc' := congrArg (fun x : ↥(CFSG.Open.StatedSp n F) =>
      (x : GL (Fin n ⊕ Fin n) F)) hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs₀, hs₁] at hc'
    exact hc'
  · intro s hs
    obtain ⟨d, hdD, hsl⟩ := hs.2
    have hdB : d ∈ B₁ := h11 hdD
    have hdpow : d ^ p = 1 := h9.2 d hdB
    have hspowP : s ^ p ∈ CFSG.Open.StatedSp n F := Subgroup.pow_mem _ hs.1 p
    have hslpow : IsGLLift j ψ (s ^ p) 1 := by
      have h := hsl.pow p
      rwa [hdpow] at h
    have huniq : s ^ p = 1 :=
      sASp_lift_unique n F ψ h2 hspowP (Subgroup.one_mem _) hslpow isGLLift_one
    have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr huniq
    have hpodd : Odd p := h5.odd_of_ne_two h6
    rcases h5.eq_one_or_self_of_dvd (orderOf s) hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hpodd
  · intro s hsP hsl
    exact ⟨hsP, hsl⟩

private theorem nbrPSpx_J_degree
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (heJε : e_J * ε = e_J)
    (hsplit : e_J = ε ∨ (e_J ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        e_J ≠ e_J ∧
      ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        e_J))
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆) :
    (e_J = ε ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) ∨
      (e_J = ε ∧
        2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4) ∨
      (e_J ≠ ε ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .PSp n 2 f := CFSG.Blueprint.LieModel.admissible h3
  rcases hadm with ⟨-, hf, -, -⟩
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rcases hsplit with heq | ⟨hne, -, -⟩
  · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2
    · exact Or.inl ⟨heq, hd⟩
    · by_cases h4 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4
      · exact Or.inr (Or.inl ⟨heq, by omega, h4⟩)
      · refine absurd ?_ h29
        rw [← hJ'map]
        exact ggSixLSevenFieldExtCase_PSp n f (GaloisField 2 f) hc ψ h2 S hSU hS hodd hε
          hJ'ε heJ heJε (Or.inl ⟨heq, by omega⟩)
  · by_cases hd : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2
    · exact Or.inr (Or.inr ⟨hne, hd⟩)
    · refine absurd ?_ h29
      rw [← hJ'map]
      exact ggSixLSevenFieldExtCase_PSp n f (GaloisField 2 f) hc ψ h2 S hSU hS hodd hε
        hJ'ε heJ heJε (Or.inr ⟨hne, by omega⟩)

private theorem nbrPSpx_J_split
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x) :
    ∃ (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
      (J' : Subgroup (ggU .PSp n f).K)
      (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)),
      (∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) ∧
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      (∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
        s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
        (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S) ∧
      IsComponentOf J' ((Subgroup.centralizer S).comap
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) ∧
      J'.map ψ = J ∧
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε ∧
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
      e_J * ε = e_J ∧
      (e_J = ε ∨ (e_J ≠ ε ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J ≠ e_J ∧
        ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J)) ∧
      IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆ ∧
      ((e_J = ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) ∨
       (e_J = ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
          blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4) ∨
       (e_J ≠ ε ∧
          blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)) := by
  obtain ⟨S, J', hSU, hS, hodd, hfull, hJ'comp, hJ'map⟩ :=
    nbrPSpx_base n f ψ p G₀ B₁ D J L x hH
  obtain ⟨ε, e_J, hε, heJ, heJε, hsplit, hJ'ε⟩ :=
    nbrPSp_blockIdempotents n f S hSU hS J' hJ'comp
  exact ⟨S, J', ε, e_J, hSU, hS, hodd, hfull, hJ'comp, hJ'map, hε, heJ, heJε, hsplit, hJ'ε,
    nbrPSpx_J_degree n f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hJ'map hε
      heJ heJε hsplit hJ'ε⟩

private lemma nbrPSpx_longRoot_mem_roots
    (m g' : ℕ) (γ : Fin (ggU .PSp m g').D.rank → ℤ)
    (h : GGLongRoot (ggU .PSp m g').D γ) : γ ∈ (ggU .PSp m g').D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := h
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

private lemma nbrPSpx_eq_one_of_range_top {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {a : Matrix ι ι F} (ha : IsIdempotentElem a)
    (htop : LinearMap.range (Matrix.toLin' a) = ⊤) : a = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, hy⟩ : x ∈ LinearMap.range (Matrix.toLin' a) := by rw [htop]; trivial
  rw [Matrix.toLin'_one, LinearMap.id_apply, ← hy, ← Matrix.toLin'_mul_apply, ha.eq]

private lemma nbrPSpx_scalar_lift_commute
    {X : Type} [Group X] {n f : ℕ} (ψ : (ggU .PSp n f).K →* X)
    {s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)} {b : X}
    (hs : IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s b)
    (hsc : ∃ c : GaloisField 2 f,
      (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = c • 1)
    (u : (ggU .PSp n f).K) : b⁻¹ * ψ u * b = ψ u := by
  obtain ⟨u', hu'j, hu'ψ⟩ := hs u
  obtain ⟨c, hc⟩ := hsc
  have hcen : s * (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u =
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u * s := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hu'u : u' = u := by
    apply Subgroup.subtype_injective (CFSG.Open.StatedSp n (GaloisField 2 f))
    rw [hu'j, mul_inv_eq_iff_eq_mul]
    exact hcen
  exact hu'ψ.trans (congrArg ψ hu'u)

private theorem nbrPSpx_J_sp
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hfull : ∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
      (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S)
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hcase : e_J = ε ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .PSp n f p ψ R Rm ∧ 1 ≤ f ∧
      ∃ (mJ : ℕ) (βJ : Fin (ggU .PSp mJ f).D.rank → ℤ), mJ < n ∧
        βJ ∈ (ggU .PSp mJ f).D.roots ∧ GGRootVia (ggU .PSp mJ f) J R βJ ∧
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) = 2 * mJ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .PSp n 2 f := CFSG.Blueprint.LieModel.admissible h3
  rcases hadm with ⟨-, hf, hn2, -⟩
  have hn1 : 1 ≤ n := by omega
  have hA6 : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)) :=
    isEmpty_mulEquiv_alternatingGroup_six_of_map ψ h2 J' (by rw [hJ'map]; exact h28)
  have hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      e_J = e_J := by
    rw [hcase.1]; exact hε.2.2.2.1
  have hJe : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S e_J : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S e_J :
        Subgroup (ggU .PSp n f).K)⁆ := by
    rw [hcase.1]; exact hJ'ε
  obtain ⟨r, ι, β₀, hrank, hlong, hιcent, hιrange, v, w, hvw, hv, hw⟩ :=
    exists_blockModel_selfDual_PSp_explicit n f S hS heJ hadj hcase.2 hJe hA6
  obtain ⟨β, hβroot, hβlong, u, huX, huXneg⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSp n (GaloisField 2 f) hn1 v w hvw
  have heqRoot : (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup β).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSp r f).D.rootGroup β₀).map ι) :=
    nbrPSp_map_subtype_injective (huX.trans hv.symm)
  have heqRootNeg : (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup (-β)).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSp r f).D.rootGroup (-β₀)).map ι) :=
    nbrPSp_map_subtype_injective (huXneg.trans hw.symm)
  have hlt : r < n := by
    have hle : r ≤ n := by
      have h2r : 2 * r ≤ 2 * n := by
        rw [hrank]
        calc Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J))
            ≤ Module.finrank (GaloisField 2 f) (Fin n ⊕ Fin n → GaloisField 2 f) :=
              Submodule.finrank_le _
          _ = 2 * n := by simp [Module.finrank_fintype_fun_eq_card, two_mul]
      omega
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have htop : LinearMap.range (Matrix.toLin' e_J) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [← hrank, h]
        simp [Module.finrank_fintype_fun_eq_card, two_mul]
      have hone : e_J = 1 := nbrPSpx_eq_one_of_range_top heJ.2.1 htop
      have hAfin : Module.finrank (GaloisField 2 f)
          (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f)
            (Units.val '' S))) < 2 := by
        have h := hcase.2
        rw [hone] at h
        have hmap : (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f)
            (Units.val '' S))).map (LinearMap.mulRight (GaloisField 2 f)
              (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) =
            Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) := by
          rw [show LinearMap.mulRight (GaloisField 2 f)
              (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
              LinearMap.id from by ext y; simp [LinearMap.mulRight_apply]]
          exact Submodule.map_id _
        unfold blockDegree at h
        rw [hmap] at h
        exact h
      have h1A : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
          Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) :=
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)).one_mem
      have h1ne : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ≠ 0 := by
        intro h
        have h00 := congrFun (congrFun h (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
        simp at h00
      haveI hnt : Nontrivial (Subalgebra.toSubmodule
          (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))) :=
        ⟨⟨⟨1, h1A⟩, 0, by intro hcon; exact h1ne (congrArg Subtype.val hcon)⟩⟩
      have hpos : 0 < Module.finrank (GaloisField 2 f)
          (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))) :=
        Module.finrank_pos_iff.mpr inferInstance
      have hfin1 : Module.finrank (GaloisField 2 f)
          (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))) = 1 := by
        omega
      have hAspan : Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) =
          Submodule.span (GaloisField 2 f)
            {(1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))} :=
        eq_span_singleton_of_mem_of_finrank_eq_one hfin1 h1A h1ne
      have hscal : ∀ s ∈ S, ∃ c : GaloisField 2 f,
          (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) = c • 1 := by
        intro s hs
        have hsA : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
            Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) :=
          Algebra.subset_adjoin ⟨s, hs, rfl⟩
        rw [hAspan] at hsA
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hsA
        exact ⟨c, hc.symm⟩
      exact h22 fun d hd => by
        have hdB : d ∈ B₁ := h11 hd
        have hdN : d ∈ Subgroup.normalizer (ψ.range : Set X) := by rw [h1]; exact h7 hdB
        have hdID : GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ d := h8 d hdB
        obtain ⟨s₀, hs₀⟩ := exists_conj_eq_PSp n (GaloisField 2 f) ψ h2 hdN hdID
        have hs₀lift : IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ
            (s₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) d :=
          fun u => ⟨s₀ * u * s₀⁻¹, rfl, hs₀ u⟩
        have hs₀S : (s₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ S :=
          hfull (s₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) s₀.2 ⟨d, hd, hs₀lift⟩
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hlG₀ : l ∈ ψ.range := by rw [h1]; exact h19 hl
        obtain ⟨w', rfl⟩ := hlG₀
        have hcomm := nbrPSpx_scalar_lift_commute ψ hs₀lift (hscal _ hs₀S) w'
        calc ψ w' * d = d * (d⁻¹ * ψ w' * d) := by group
          _ = d * ψ w' := by rw [hcomm]
  refine ⟨ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ β u,
    ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ (-β) u, ?_, ?_, ?_, hf, r, β₀,
    hlt, nbrPSpx_longRoot_mem_roots r f β₀ hlong, ?_, hrank.symm⟩
  · have hBle : (((ggU .PSp r f).D.rootGroup β₀).map ι) ≤ ι.range := Subgroup.map_le_range ι _
    calc ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ β u
        = (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup β).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSp r f).D.rootGroup β₀).map ι).map ψ := by rw [heqRoot]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · have hBle : (((ggU .PSp r f).D.rootGroup (-β₀)).map ι) ≤ ι.range := Subgroup.map_le_range ι _
    calc ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ (-β) u
        = (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSp r f).D.rootGroup (-β₀)).map ι).map ψ := by rw [heqRootNeg]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · exact ⟨β, hβroot, Or.inl hβlong, u, rfl, rfl⟩
  · refine ⟨ψ.comp ι, ?_, ?_, 1, ?_⟩
    · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
        _ = Subgroup.map ψ J' := by rw [hιrange]
        _ = J := hJ'map
    · intro y hy
      apply hιcent
      apply h2
      exact MonoidHom.mem_ker.mpr (show ψ (ι y) = 1 from MonoidHom.mem_ker.mp hy)
    · have hconj : Subgroup.map (MulAut.conj (1 : (ggU .PSp r f).K)).toMonoidHom
            ((ggU .PSp r f).D.rootGroup β₀) = (ggU .PSp r f).D.rootGroup β₀ := by
        ext y; simp
      unfold ggRootSub
      rw [hconj, heqRoot]
      exact Subgroup.map_map ((ggU .PSp r f).D.rootGroup β₀) ψ ι

private lemma nbrPSpx_longRoot_mem_roots_PSU
    {m f : ℕ} (γ : Fin (ggU .PSU m f).D.rank → ℤ)
    (h : GGLongRoot (ggU .PSU m f).D γ) : γ ∈ (ggU .PSU m f).D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := h
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

private theorem nbrPSpx_J_su
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hcase : e_J = ε ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .PSp n f p ψ R Rm ∧ 1 ≤ f ∧
      ∃ (m'J : ℕ) (βJ : Fin (ggU .PSU m'J f).D.rank → ℤ), m'J ≤ n ∧
        βJ ∈ (ggU .PSU m'J f).D.roots ∧ GGRootVia (ggU .PSU m'J f) J R βJ ∧
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) = 2 * m'J := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .PSp n 2 f := CFSG.Blueprint.LieModel.admissible h3
  rcases hadm with ⟨-, hf, hn2, -⟩
  have hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      e_J = e_J := by
    rw [hcase.1]; exact hε.2.2.2.1
  have hJe : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S e_J : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S e_J :
        Subgroup (ggU .PSp n f).K)⁆ := by
    rw [hcase.1]; exact hJ'ε
  have hmodel :=
    exists_blockModel_selfDualTwo_PSp_explicit n f S hSU hS hodd heJ hadj hcase.2.1 hcase.2.2 hJe
  rw [max_eq_left hf] at hmodel
  obtain ⟨r, ι, β₀, hrank, hlong, hιcent, hιrange, a₁, a₂, b₁, b₂, h1v, h2v, h0v, hAl, hAl'⟩ :=
    hmodel
  obtain ⟨β, hβroot, h2β, u, huA, huA'⟩ :=
    exists_conj_rootGroup_eq_altSiegelGroup_PSp n (GaloisField 2 f) hn2 a₁ a₂ b₁ b₂ h1v h2v h0v
  have heqRoot : (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup β).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSU r f).D.rootGroup β₀).map ι) :=
    nbrPSp_map_subtype_injective (huA.trans hAl.symm)
  have heqRootNeg : (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup (-β)).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSU r f).D.rootGroup (-β₀)).map ι) :=
    nbrPSp_map_subtype_injective (huA'.trans hAl'.symm)
  have hle : r ≤ n := by
    have h2r : 2 * r ≤ 2 * n := by
      rw [hrank]
      calc Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J))
          ≤ Module.finrank (GaloisField 2 f) (Fin n ⊕ Fin n → GaloisField 2 f) :=
            Submodule.finrank_le _
        _ = 2 * n := by simp [Module.finrank_fintype_fun_eq_card, two_mul]
    omega
  refine ⟨ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ β u,
    ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ (-β) u, ?_, ?_, ?_, hf, r, β₀,
    hle, nbrPSpx_longRoot_mem_roots_PSU β₀ hlong, ?_, hrank.symm⟩
  · have hBle : (((ggU .PSU r f).D.rootGroup β₀).map ι) ≤ ι.range := Subgroup.map_le_range ι _
    calc ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ β u
        = (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup β).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSU r f).D.rootGroup β₀).map ι).map ψ := by rw [heqRoot]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · have hBle : (((ggU .PSU r f).D.rootGroup (-β₀)).map ι) ≤ ι.range := Subgroup.map_le_range ι _
    calc ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ (-β) u
        = (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSU r f).D.rootGroup (-β₀)).map ι).map ψ := by rw [heqRootNeg]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · exact ⟨β, hβroot, Or.inr ⟨Or.inl rfl, h2β⟩, u, rfl, rfl⟩
  · refine ⟨ψ.comp ι, ?_, ?_, 1, ?_⟩
    · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
        _ = Subgroup.map ψ J' := by rw [hιrange]
        _ = J := hJ'map
    · intro y hy
      apply hιcent
      apply h2
      exact MonoidHom.mem_ker.mpr (show ψ (ι y) = 1 from MonoidHom.mem_ker.mp hy)
    · have hconj : Subgroup.map (MulAut.conj (1 : (ggU .PSU r f).K)).toMonoidHom
            ((ggU .PSU r f).D.rootGroup β₀) = (ggU .PSU r f).D.rootGroup β₀ := by
        ext y; simp
      unfold ggRootSub
      rw [hconj, heqRoot]
      exact Subgroup.map_map ((ggU .PSU r f).D.rootGroup β₀) ψ ι

private lemma nbrPSpx_rank_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G M : Matrix ι ι F} (hG : IsUnit G.det) :
    Matrix.rank (formAdj (RingHom.id F) G M) = Matrix.rank M := by
  have hM : M.map (RingHom.id F) = M := by ext i j; rfl
  have hX : (G⁻¹ * Matrix.transpose M).rank = M.rank := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det G⁻¹ (Matrix.transpose M)
      (Matrix.isUnit_nonsing_inv_det G hG), Matrix.rank_transpose]
  unfold formAdj
  rw [hM, Matrix.rank_mul_eq_left_of_isUnit_det G (G⁻¹ * Matrix.transpose M) hG, hX]

private lemma nbrPSpx_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      Commute a b := by
  intro a ha b hb
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rcases hy with ⟨s', hs', rfl⟩
    have h := congrArg (fun u : GL ι F => (u : Matrix ι ι F)) (hS s' hs' s hs).eq
    simpa [Units.val_mul] using h
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have ha' : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  have hgen2 : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h := (Subalgebra.mem_centralizer_iff F).mp ha' (s : Matrix ι ι F) ⟨s, hs, rfl⟩
    exact h.symm
  have hA2 : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := Algebra.adjoin_le hgen2
  have hb' : b ∈ Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := hA2 hb
  exact (Subalgebra.mem_centralizer_iff F).mp hb' a (Set.mem_singleton a)

private lemma nbrPSpx_longRoot_mem_roots_univ {U : Type} [Group U] (D : UniversalRootDatum U)
    (γ : Fin D.rank → ℤ) (h : GGLongRoot D γ) : γ ∈ D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := h
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

private theorem nbrPSpx_J_sl
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hJ'map : J'.map ψ = J)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hcase : e_J ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J ≠ e_J ∧
      ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) :
    ∃ (R Rm : Subgroup X), R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .PSp n f p ψ R Rm ∧ 1 ≤ f ∧
      ∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ), kJ + 1 ≤ n ∧
        βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧
        GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .PSp n 2 f := CFSG.Blueprint.LieModel.admissible h3
  rcases hadm with ⟨-, hf, hn2, -⟩
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hGh : Matrix.transpose ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) (GaloisField 2 f)).map (RingHom.id (GaloisField 2 f))) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.LieType.BorelTits.spJ n (GaloisField 2 f) from rfl]
    rw [show ((CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) = (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f))
        from rfl]
    exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU s hs)
    simpa using h
  let A : Subalgebra (GaloisField 2 f)
      (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
  have hAcomm : ∀ {a b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)},
      a ∈ A → b ∈ A → a * b = b * a := by
    intro a b ha hb
    exact (nbrPSpx_adjoin_comm hS a ha b hb).eq
  have hstarA : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J ∈ A :=
    Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU_iso heJ.1
  have horth : e_J * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J = 0 := by
    by_contra hne0
    have hstar_idem : IsIdempotentElem (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J) := by
      rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG e_J e_J,
        heJ.2.1.eq]
    have hidem : IsIdempotentElem (e_J * formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J) :=
      IsIdempotentElem.mul_of_commute (hAcomm heJ.1 hstarA) heJ.2.1 hstar_idem
    have hee : (e_J * formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J) * e_J =
        e_J * formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J := by
      rw [Matrix.mul_assoc, ← hAcomm heJ.1 hstarA, ← Matrix.mul_assoc, heJ.2.1.eq]
    rcases heJ.2.2.2 (e_J * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J) (Subalgebra.mul_mem A heJ.1 hstarA) hidem hee with h | h
    · exact hne0 h
    · apply hcase.2.1
      calc formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) e_J
          = formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) (e_J * formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) e_J) := by rw [h]
        _ = formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) (formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) e_J) * formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e_J :=
            Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG e_J
              (formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) e_J)
        _ = e_J * formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e_J := by
            rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh e_J]
        _ = e_J := h
  obtain ⟨k, ι, β₀, hrank, hlong, hιcent, hιrange, a₁, a₂, b₁, b₂, h1v, h2v, h0v, hAl, hAl'⟩ :=
    exists_blockModel_dualPair_PSp_explicit n f S hSU hS heJ hcase.2.1 hcase.2.2.2
      (by rw [← hcase.2.2.1]; exact hJ'ε)
  obtain ⟨β, hβroot, h2β, u, huA, huA'⟩ :=
    exists_conj_rootGroup_eq_altSiegelGroup_PSp n (GaloisField 2 f) hn2 a₁ a₂ b₁ b₂ h1v h2v h0v
  have heqRoot : (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup β).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSL (k + 1) f).D.rootGroup β₀).map ι) :=
    nbrPSp_map_subtype_injective (huA.trans hAl.symm)
  have heqRootNeg : (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup (-β)).map
      (MulAut.conj u).toMonoidHom) = (((ggU .PSL (k + 1) f).D.rootGroup (-β₀)).map ι) :=
    nbrPSp_map_subtype_injective (huA'.trans hAl'.symm)
  have hbound : k + 1 ≤ n := by
    have hrank_eq : Matrix.rank (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J) = Matrix.rank e_J :=
      nbrPSpx_rank_formAdj hG
    have hstar_comm : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J * e_J = 0 := by
      rw [hAcomm hstarA heJ.1, horth]
    have hle : LinearMap.range (Matrix.toLin' e_J) ≤ LinearMap.ker (Matrix.toLin'
        (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J)) := by
      rintro v ⟨w, rfl⟩
      rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        hstar_comm, Matrix.zero_mulVec]
    have hmono : Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) ≤
        Module.finrank (GaloisField 2 f) (LinearMap.ker (Matrix.toLin'
          (formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) e_J))) := Submodule.finrank_mono hle
    have hnull := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin'
      (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J))
    have hfinV : Module.finrank (GaloisField 2 f)
        (Fin n ⊕ Fin n → GaloisField 2 f) = 2 * n := by
      simp [Module.finrank_fintype_fun_eq_card, two_mul]
    have hr : Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin'
        (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J))) =
        Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) := by
      rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
      exact hrank_eq
    have h2n : 2 * Module.finrank (GaloisField 2 f)
        (LinearMap.range (Matrix.toLin' e_J)) ≤ 2 * n := by
      rw [two_mul]
      calc Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) +
            Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J))
          = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin'
              (formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) e_J))) +
            Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) := by rw [hr]
        _ ≤ Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin'
              (formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) e_J))) +
            Module.finrank (GaloisField 2 f) (LinearMap.ker (Matrix.toLin'
              (formAdj (RingHom.id (GaloisField 2 f))
                (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                  (GaloisField 2 f)) e_J))) := Nat.add_le_add_left hmono _
        _ = 2 * n := by rw [hnull, hfinV]
    omega
  refine ⟨ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ β u,
    ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ (-β) u, ?_, ?_, ?_, hf, k, β₀,
    hbound, nbrPSpx_longRoot_mem_roots_univ (ggU .PSL (k + 1) f).D β₀ hlong, ?_, hrank.symm⟩
  · have hBle : (((ggU .PSL (k + 1) f).D.rootGroup β₀).map ι) ≤ ι.range :=
      Subgroup.map_le_range ι _
    calc ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ β u
        = (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup β).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSL (k + 1) f).D.rootGroup β₀).map ι).map ψ := by rw [heqRoot]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · have hBle : (((ggU .PSL (k + 1) f).D.rootGroup (-β₀)).map ι) ≤ ι.range :=
      Subgroup.map_le_range ι _
    calc ggRootSub (Symplectic.rootDatum n (GaloisField 2 f)) ψ (-β) u
        = (((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup (-β)).map
            (MulAut.conj u).toMonoidHom).map ψ := rfl
      _ = (((ggU .PSL (k + 1) f).D.rootGroup (-β₀)).map ι).map ψ := by rw [heqRootNeg]
      _ ≤ ι.range.map ψ := Subgroup.map_mono hBle
      _ = J := by rw [hιrange, hJ'map]
  · exact ⟨β, hβroot, Or.inr ⟨Or.inl rfl, h2β⟩, u, rfl, rfl⟩
  · refine ⟨ψ.comp ι, ?_, ?_, 1, ?_⟩
    · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
        _ = Subgroup.map ψ J' := by rw [hιrange]
        _ = J := hJ'map
    · intro y hy
      apply hιcent
      apply h2
      exact MonoidHom.mem_ker.mpr (show ψ (ι y) = 1 from MonoidHom.mem_ker.mp hy)
    · have hconj : Subgroup.map (MulAut.conj (1 : (ggU .PSL (k + 1) f).K)).toMonoidHom
            ((ggU .PSL (k + 1) f).D.rootGroup β₀) = (ggU .PSL (k + 1) f).D.rootGroup β₀ := by
        ext y; simp
      unfold ggRootSub
      rw [hconj, heqRoot]
      exact Subgroup.map_map ((ggU .PSL (k + 1) f).D.rootGroup β₀) ψ ι

private lemma nbrPSpx_mem_sup_central {U : Type} [Group U] {K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) {x : U} : x ∈ K ⊔ Z ↔ ∃ k ∈ K, ∃ z ∈ Z, k * z = x := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  exact Subgroup.mem_sup_of_normal_right

private lemma nbrPSpx_commutatorElement_mul_central_left {U : Type} [Group U]
    {c : U} (hc : c ∈ Subgroup.center U) (g h : U) : ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have e : c * h * c⁻¹ = h := by
    rw [← Subgroup.mem_center_iff.mp hc h, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * c * h * (c⁻¹ * g⁻¹) * h⁻¹ = g * (c * h * c⁻¹) * g⁻¹ * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [e]

private lemma nbrPSpx_commutatorElement_mul_central_right {U : Type} [Group U]
    {c : U} (hc : c ∈ Subgroup.center U) (g h : U) : ⁅g, h * c⁆ = ⁅g, h⁆ := by
  have e : g * c * g⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * (h * c) * g⁻¹ * (c⁻¹ * h⁻¹)
      = (g * h * g⁻¹) * (g * c * g⁻¹) * (c⁻¹ * h⁻¹) := by group
    _ = (g * h * g⁻¹) * c * c⁻¹ * h⁻¹ := by rw [e]; group
    _ = g * h * g⁻¹ * h⁻¹ := by group

private lemma nbrPSpx_commutator_sup_central_le {U : Type} [Group U] {K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ ⁅K, K⁆ := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨k, hk, z, hz, rfl⟩ := (nbrPSpx_mem_sup_central hZ).1 hx
  obtain ⟨k', hk', z', hz', rfl⟩ := (nbrPSpx_mem_sup_central hZ).1 hy
  rw [nbrPSpx_commutatorElement_mul_central_left (hZ hz),
    nbrPSpx_commutatorElement_mul_central_right (hZ hz')]
  exact Subgroup.commutator_mem_commutator hk hk'

private lemma nbrPSpx_perfect_le_of_le_sup_center {U : Type} [Group U] {J K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) (hle : J ≤ K ⊔ Z) (hperf : commutator ↥J = ⊤) : J ≤ K := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  have hmap2 : Subgroup.map (Subgroup.subtype J) (commutator ↥J) = ⁅J, J⁆ := by
    have hc : commutator ↥J = ⁅(⊤ : Subgroup ↥J), ⊤⁆ := rfl
    rw [hc, Subgroup.map_commutator]
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hJle : J ≤ ⁅J, J⁆ := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥J) ∈ commutator ↥J := by rw [hperf]; trivial
    have hxm : x ∈ Subgroup.map (Subgroup.subtype J) (commutator ↥J) :=
      ⟨⟨x, hx⟩, hx', rfl⟩
    rwa [hmap2] at hxm
  have hcommK : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ K := by
    refine (nbrPSpx_commutator_sup_central_le hZ).trans ?_
    simpa using Subgroup.commutator_le_sup K K
  exact hJle.trans ((Subgroup.commutator_mono hle hle).trans hcommK)

private lemma nbrPSpx_commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {T : GL ι F} (hT : T ∈ Subgroup.centralizer S)
    {ε : Matrix ι ι F} (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F) := by
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :
        Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun u : GL ι F => (u : Matrix ι ι F))
      ((Subgroup.mem_centralizer_iff.mp hT) s hs).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA hε) (T : Matrix ι ι F)
    (Set.mem_singleton (T : Matrix ι ι F))

private theorem nbrPSpx_liftComponents
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e}))
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hfull : ∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
      (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S) :
    ∃ S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)),
      S' ⊆ S ∧
      (∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) ∧
      (∀ s ∈ S', ∀ s' ∈ S', Commute s s') ∧
      (∀ s ∈ S', Odd (orderOf s)) ∧
      ∃ K' : Subgroup (ggU .PSp n f).K,
        IsComponentOf K' ((Subgroup.centralizer S').comap
          (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) ∧
        K'.map ψ = K := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  let F := GaloisField 2 f
  let j : ↥(CFSG.Open.StatedSp n F) →* GL (Fin n ⊕ Fin n) F :=
    (CFSG.Open.StatedSp n F).subtype
  have hj : Function.Injective j := Subgroup.subtype_injective _
  let P : GL (Fin n ⊕ Fin n) F → Prop := fun s => s ∈ CFSG.Open.StatedSp n F
  have heB : e ∈ B₁ := h11 heD
  have heN : e ∈ Subgroup.normalizer (ψ.range : Set X) := by rw [h1]; exact h7 heB
  have heID : GGPsiInnerDiag (Symplectic.rootDatum n F) ψ e := h8 e heB
  obtain ⟨se₀, hse₀⟩ := exists_conj_eq_PSp n F ψ h2 heN heID
  let se : GL (Fin n ⊕ Fin n) F := (se₀ : GL (Fin n ⊕ Fin n) F)
  have hseP : se ∈ CFSG.Open.StatedSp n F := se₀.2
  have hseLift : IsGLLift j ψ se e := fun u => ⟨se₀ * u * se₀⁻¹, rfl, hse₀ u⟩
  have hlift : ∀ d ∈ Subgroup.zpowers e, ∃ s : GL (Fin n ⊕ Fin n) F, P s ∧ IsGLLift j ψ s d := by
    intro d hd
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
    refine ⟨se ^ k, Subgroup.zpow_mem _ hseP k, ?_⟩
    rw [← hk]
    exact nbrPSp_lift_zpow n F ψ hseP hseLift k
  have hcent : Subgroup.centralizer (Subgroup.zpowers e : Set X) =
      Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hKcomp' : IsComponentOf K (Subgroup.centralizer (Subgroup.zpowers e : Set X)) := by
    rw [hcent]; exact hKcomp
  have hJ : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer
      (Subgroup.zpowers e : Set X)) := by
    rw [h1]
    exact CFSG.Assembly.IsComponentOf.of_le_of_le hKcomp'
      (le_inf hKG₀ hKcomp'.1) inf_le_right
  obtain ⟨K', hK'comp, hK'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift j hj ψ h2 P hJ hlift
  let S' : Set (GL (Fin n ⊕ Fin n) F) :=
    {s | P s ∧ ∃ d ∈ Subgroup.zpowers e, IsGLLift j ψ s d}
  have hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n F := fun s hs => hs.1
  have hSe : S' ⊆ S := by
    intro s hs
    obtain ⟨d, hd, hsl⟩ := hs.2
    exact hfull s hs.1 ⟨d, Subgroup.zpowers_le.mpr heD hd, hsl⟩
  have hS' : ∀ s ∈ S', ∀ s' ∈ S', Commute s s' := by
    intro s hs s' hs'
    obtain ⟨d, hd, hsl⟩ := hs.2
    obtain ⟨d', hd', hs'l⟩ := hs'.2
    have hdd' : Commute d d' := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd
      obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp hd'
      rw [← hk, ← hk']
      exact (Commute.refl e).zpow_zpow k k'
    obtain ⟨s₀, hs₀, hsl₀⟩ := nbrPSp_lift_to_mem n F ψ hs.1 hsl
    obtain ⟨s₁, hs₁, hsl₁⟩ := nbrPSp_lift_to_mem n F ψ hs'.1 hs'l
    have hc := conj_eq_commute_PSp n F ψ h2 hdd' hsl₀ hsl₁
    have hc' := congrArg (fun x : ↥(CFSG.Open.StatedSp n F) =>
      (x : GL (Fin n ⊕ Fin n) F)) hc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs₀, hs₁] at hc'
    exact hc'
  have hodd' : ∀ s ∈ S', Odd (orderOf s) := by
    intro s hs
    obtain ⟨d, hd, hsl⟩ := hs.2
    have hdB : d ∈ B₁ := Subgroup.zpowers_le.mpr heB hd
    have hdpow : d ^ p = 1 := h9.2 d hdB
    have hspowP : s ^ p ∈ CFSG.Open.StatedSp n F := Subgroup.pow_mem _ hs.1 p
    have hslpow : IsGLLift j ψ (s ^ p) 1 := by
      have h := hsl.pow p
      rwa [hdpow] at h
    have huniq : s ^ p = 1 :=
      nbrPSp_lift_unique n F ψ h2 hspowP (Subgroup.one_mem _) hslpow isGLLift_one
    have hdvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr huniq
    have hpodd : Odd p := h5.odd_of_ne_two h6
    rcases h5.eq_one_or_self_of_dvd (orderOf s) hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hpodd
  exact ⟨S', hSe, hSU', hS', hodd', K', hK'comp, hK'map⟩

private theorem nbrPSpx_neighbourBlockData
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hfull : ∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
      (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) :
    ∃ (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
      (K' : Subgroup (ggU .PSp n f).K)
      (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)),
      S' ⊆ S ∧
      (∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) ∧
      (∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') ∧
      (∀ s ∈ S', Odd (orderOf s)) ∧
      IsComponentOf K' ((Subgroup.centralizer S').comap
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) ∧
      K'.map ψ = K ∧
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε' ∧
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      e' * ε' = e' ∧
      (e' = ε' ∨ (e' ≠ ε' ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' ≠ e' ∧
        ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e')) ∧
      IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
        Subgroup (ggU .PSp n f).K)⁆ ∧
      J' ≤ K' ∧ ε * ε' = ε := by
  have hkerc : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K := hH.2.1
  obtain ⟨S', hSe, hSU', hS', hodd', K', hK'comp, hK'map⟩ :=
    nbrPSpx_liftComponents n f ψ p G₀ B₁ D J L x hH e heD K hKG₀ hKcomp S hfull
  obtain ⟨ε', e', hε', he', he'ε', hsplit', hK'ε'⟩ :=
    nbrPSp_blockIdempotents n f S' hSU' hS' K' hK'comp
  have hJK' : J' ≤ K' := by
    have hmapJK : J'.map ψ ≤ K'.map ψ := by
      calc J'.map ψ = J := hJ'map
        _ ≤ K := hJK
        _ = K'.map ψ := hK'map.symm
    have hleJK : J' ≤ K' ⊔ ψ.ker := Subgroup.map_le_map_iff.mp hmapJK
    have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
    exact nbrPSpx_perfect_le_of_le_sup_center hkerc hleJK hperf
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have htie : ε * ε' = ε := by
    have hAe_le : Algebra.adjoin (GaloisField 2 f) (Units.val '' S') ≤
        Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
      Algebra.adjoin_mono (Set.image_mono hSe)
    have hε'A : ε' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := hAe_le hε'.1
    have hcommA : ∀ a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S),
        ∀ b ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S), a * b = b * a :=
      fun a ha b hb => (nbrPSpx_adjoin_comm hS a ha b hb).eq
    have hmem : ε * ε' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
      Subalgebra.mul_mem _ hε.1 hε'A
    have hidem : IsIdempotentElem (ε * ε') := by
      rw [IsIdempotentElem]
      calc (ε * ε') * (ε * ε') = ε * (ε' * (ε * ε')) := by rw [mul_assoc]
        _ = ε * ((ε' * ε) * ε') := by rw [mul_assoc]
        _ = ε * ((ε * ε') * ε') := by rw [hcommA ε' hε'A ε hε.1]
        _ = ε * (ε * (ε' * ε')) := by rw [mul_assoc]
        _ = ε * (ε * ε') := by rw [hε'.2.1.eq]
        _ = (ε * ε) * ε' := by rw [← mul_assoc]
        _ = ε * ε' := by rw [hε.2.1.eq]
    have hadj : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) (ε * ε') = ε * ε' := by
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG, hε.2.2.2.1, hε'.2.2.2.1]
      exact hcommA ε' hε'A ε hε.1
    have hbelow : (ε * ε') * ε = ε * ε' := by
      rw [mul_assoc, hcommA ε' hε'A ε hε.1, ← mul_assoc, hε.2.1.eq]
    rcases hε.2.2.2.2 (ε * ε') hmem hidem hadj hbelow with h0 | heq
    · exfalso
      have hJ'bot : J' = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have huG : u ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε := by
          have h := (Subgroup.commutator_le_sup _ _) (hJ'ε.1 hu)
          rwa [sup_idem] at h
        have huGe : u ∈ glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
            S' ε' := by
          have h := (Subgroup.commutator_le_sup _ _) (hK'ε'.1 (hJK' hu))
          rwa [sup_idem] at h
        have huG' : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u ∈
            Subgroup.centralizer S ⊓ glFixing (1 - ε) := Subgroup.mem_comap.mp huG
        have huGe' : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u ∈
            Subgroup.centralizer S' ⊓ glFixing (1 - ε') := Subgroup.mem_comap.mp huGe
        have huc : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u ∈ Subgroup.centralizer S :=
          huG'.1
        let U : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
          ((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f))
        have hfixJ : U * (1 - ε) = 1 - ε := huG'.2
        have hfixe : U * (1 - ε') = 1 - ε' := huGe'.2
        have hcomm_u : U * ε = ε * U := nbrPSpx_commute_adjoin huc hε.1
        have h1 : ε * (1 - ε') = ε := by rw [mul_sub, mul_one, h0, sub_zero]
        have hmat_eU : U * ε = ε := by
          calc U * ε = U * (ε * (1 - ε')) := by rw [h1]
            _ = (U * ε) * (1 - ε') := by rw [mul_assoc]
            _ = (ε * U) * (1 - ε') := by rw [hcomm_u]
            _ = ε * (U * (1 - ε')) := by rw [mul_assoc]
            _ = ε * (1 - ε') := by rw [hfixe]
            _ = ε := h1
        have hmat_one : U = 1 := by
          calc U = U * 1 := by rw [mul_one]
            _ = U * (ε + (1 - ε)) := by rw [add_sub_cancel]
            _ = U * ε + U * (1 - ε) := by rw [mul_add]
            _ = ε + (1 - ε) := by rw [hmat_eU, hfixJ]
            _ = 1 := by rw [add_sub_cancel]
        have hu1 : u = 1 := Subtype.ext (Units.ext hmat_one)
        exact Subgroup.mem_bot.mpr hu1
      have hnt : Nontrivial ↥J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJ'comp.2.2
      exact (Subgroup.nontrivial_iff_ne_bot J').mp hnt hJ'bot
    · exact heq
  exact ⟨S', K', ε', e', hSe, hSU', hS', hodd', hK'comp, hK'map, hε', he', he'ε', hsplit',
    hK'ε', hJK', htie⟩

private lemma nbrPSpx_rank_lt_of_mul_eq {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {a b : Matrix ι ι F} (ha : IsIdempotentElem a) (hab : a * b = a) (hba : b * a = a)
    (hne : a ≠ b) :
    Module.finrank F (LinearMap.range (Matrix.toLin' a)) <
      Module.finrank F (LinearMap.range (Matrix.toLin' b)) := by
  have hle : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨Matrix.toLin' a y, by rw [← Matrix.toLin'_mul_apply, hba]⟩
  have hlt : LinearMap.range (Matrix.toLin' a) < LinearMap.range (Matrix.toLin' b) := by
    refine lt_of_le_of_ne hle fun heq => hne ?_
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    have hx : Matrix.toLin' b x ∈ LinearMap.range (Matrix.toLin' a) := by
      rw [heq]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hx
    have h1 : Matrix.toLin' a (Matrix.toLin' b x) = Matrix.toLin' a x := by
      rw [← Matrix.toLin'_mul_apply, hab]
    have h2 : Matrix.toLin' a (Matrix.toLin' a z) = Matrix.toLin' a z := by
      rw [← Matrix.toLin'_mul_apply, ha.eq]
    rw [← h1, ← hz, h2]
  exact Submodule.finrank_lt_finrank_of_lt hlt

private lemma nbrPSpx_selfDual_not_below_dualPair {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (G : Matrix ι ι F) (hG : IsUnit G.det) {A : Subalgebra F (Matrix ι ι F)}
    (hcomm : ∀ a b : Matrix ι ι F, a ∈ A → b ∈ A → a * b = b * a)
    {e_J e' : Matrix ι ι F}
    (heJ : IsPrimIdemIn A e_J) (hadjJ : formAdj (RingHom.id F) G e_J = e_J)
    (he' : e' ∈ A) (he'star : formAdj (RingHom.id F) G e' ∈ A)
    (he'idem : IsIdempotentElem e')
    (hle : e_J * (e' + formAdj (RingHom.id F) G e') = e_J) : False := by
  obtain ⟨heJA, heJidem, heJ0, heJprim⟩ := heJ
  have hmem : e_J * e' ∈ A := A.mul_mem heJA he'
  have hidem : IsIdempotentElem (e_J * e') := by
    rw [IsIdempotentElem]
    calc (e_J * e') * (e_J * e') = e_J * (e' * e_J) * e' := by noncomm_ring
      _ = e_J * (e_J * e') * e' := by rw [hcomm e' e_J he' heJA]
      _ = (e_J * e_J) * (e' * e') := by noncomm_ring
      _ = e_J * e' := by rw [heJidem.eq, he'idem.eq]
  have hmul : (e_J * e') * e_J = e_J * e' := by
    rw [mul_assoc, hcomm e' e_J he' heJA, ← mul_assoc, heJidem.eq]
  rcases heJprim (e_J * e') hmem hidem hmul with h0 | h1
  · have hstar : e_J * formAdj (RingHom.id F) G e' = e_J := by
      have h := hle
      rw [mul_add, h0, zero_add] at h
      exact h
    have hf : formAdj (RingHom.id F) G e' * e_J = 0 := by
      have h := congrArg (formAdj (RingHom.id F) G) h0
      rw [Geo.formAdj_mul (RingHom.id F) hG, hadjJ] at h
      simpa [formAdj] using h
    have hz : e_J * formAdj (RingHom.id F) G e' = 0 :=
      (hcomm e_J (formAdj (RingHom.id F) G e') heJA he'star).trans hf
    rw [hz] at hstar
    exact heJ0 hstar.symm
  · have hstar : e_J * formAdj (RingHom.id F) G e' = e_J := by
      have h := congrArg (formAdj (RingHom.id F) G) h1
      rw [Geo.formAdj_mul (RingHom.id F) hG, hadjJ] at h
      exact (hcomm e_J (formAdj (RingHom.id F) G e') heJA he'star).trans h
    have hsum : e_J + e_J = e_J := by
      have h := hle
      rw [mul_add, h1, hstar] at h
      exact h
    exact heJ0 (add_left_cancel (by rw [add_zero, hsum]))

private lemma nbrPSpx_blockDegree_le_of_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A A' : Subalgebra F (Matrix ι ι F)} (hAA' : A' ≤ A)
    (hcomm : ∀ a b : Matrix ι ι F, a ∈ A → b ∈ A → a * b = b * a)
    {e_J e' : Matrix ι ι F}
    (heJ : IsPrimIdemIn A e_J) (hle : e_J * e' = e_J)
    (hfield : ∀ x ∈ A', x * e' ≠ 0 → ∃ y ∈ A', y * x * e' = e') :
    blockDegree A' e' ≤ blockDegree A e_J := by
  have hker : LinearMap.ker ((LinearMap.mulRight F e_J).comp (Subalgebra.val A').toLinearMap) ≤
      LinearMap.ker ((LinearMap.mulRight F e').comp (Subalgebra.val A').toLinearMap) := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    by_contra hne
    have hne' : (a : Matrix ι ι F) * e' ≠ 0 := by
      simpa [LinearMap.mulRight_apply] using hne
    obtain ⟨b, hb, hb'⟩ := hfield (a : Matrix ι ι F) a.2 hne'
    have haJ : (a : Matrix ι ι F) * e_J = 0 := by
      simpa [LinearMap.mulRight_apply] using ha
    have haA : (a : Matrix ι ι F) ∈ A := hAA' a.2
    have hbA : b ∈ A := hAA' hb
    have hmove : e_J * b * (a : Matrix ι ι F) = b * (a : Matrix ι ι F) * e_J := by
      rw [hcomm e_J b heJ.1 hbA, mul_assoc, hcomm e_J (a : Matrix ι ι F) heJ.1 haA,
        ← mul_assoc]
    have heq0 : e_J = 0 := by
      calc e_J = e_J * e' := hle.symm
        _ = e_J * (b * (a : Matrix ι ι F) * e') := by rw [hb']
        _ = (e_J * b * (a : Matrix ι ι F)) * e' := by noncomm_ring
        _ = (b * (a : Matrix ι ι F) * e_J) * e' := by rw [hmove]
        _ = b * ((a : Matrix ι ι F) * e_J) * e' := by noncomm_ring
        _ = 0 := by rw [haJ, mul_zero, zero_mul]
    exact heJ.2.2.1 heq0
  have hnull' := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.mulRight F e').comp (Subalgebra.val A').toLinearMap)
  have hnull := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.mulRight F e_J).comp (Subalgebra.val A').toLinearMap)
  have hkerle := Submodule.finrank_mono hker
  have hrange_le' : Module.finrank F (LinearMap.range
      ((LinearMap.mulRight F e').comp (Subalgebra.val A').toLinearMap)) ≤
      Module.finrank F (LinearMap.range ((LinearMap.mulRight F e_J).comp
        (Subalgebra.val A').toLinearMap)) := by
    omega
  have hrange_le : LinearMap.range ((LinearMap.mulRight F e_J).comp
      (Subalgebra.val A').toLinearMap) ≤
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e_J) := by
    rintro x ⟨a, rfl⟩
    exact ⟨(a : Matrix ι ι F), hAA' a.2, rfl⟩
  have hfin : Module.finrank F (LinearMap.range ((LinearMap.mulRight F e_J).comp
      (Subalgebra.val A').toLinearMap)) ≤ blockDegree A e_J := by
    rw [blockDegree]
    exact Submodule.finrank_mono hrange_le
  have hval : LinearMap.range (Subalgebra.val A').toLinearMap = Subalgebra.toSubmodule A' := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hrange' : (Subalgebra.toSubmodule A').map (LinearMap.mulRight F e') =
      LinearMap.range ((LinearMap.mulRight F e').comp (Subalgebra.val A').toLinearMap) := by
    rw [LinearMap.range_comp, hval]
  rw [blockDegree, hrange']
  exact hrange_le'.trans hfin

private lemma nbrPSpx_mul_formAdj_eq_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Matrix ι ι F) (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map (RingHom.id F)) = G)
    {A : Subalgebra F (Matrix ι ι F)}
    (hcomm : ∀ a b : Matrix ι ι F, a ∈ A → b ∈ A → a * b = b * a)
    {e : Matrix ι ι F} (he : IsPrimIdemIn A e)
    (hestarA : formAdj (RingHom.id F) G e ∈ A)
    (hfix : formAdj (RingHom.id F) G e ≠ e) :
    e * formAdj (RingHom.id F) G e = 0 := by
  by_contra hne0
  have hstar_idem : IsIdempotentElem (formAdj (RingHom.id F) G e) := by
    rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id F) hG e e, he.2.1.eq]
  have hidem : IsIdempotentElem (e * formAdj (RingHom.id F) G e) :=
    IsIdempotentElem.mul_of_commute (hcomm e (formAdj (RingHom.id F) G e) he.1 hestarA)
      he.2.1 hstar_idem
  have hee : (e * formAdj (RingHom.id F) G e) * e = e * formAdj (RingHom.id F) G e := by
    rw [Matrix.mul_assoc, ← hcomm e (formAdj (RingHom.id F) G e) he.1 hestarA, ← Matrix.mul_assoc,
      he.2.1.eq]
  rcases he.2.2.2 (e * formAdj (RingHom.id F) G e) (Subalgebra.mul_mem _ he.1 hestarA) hidem hee
    with h0 | heq
  · exact hne0 h0
  · apply hfix
    calc formAdj (RingHom.id F) G e =
          formAdj (RingHom.id F) G (e * formAdj (RingHom.id F) G e) := by
          rw [heq]
      _ = formAdj (RingHom.id F) G (formAdj (RingHom.id F) G e) * formAdj (RingHom.id F) G e :=
          Geo.formAdj_mul (RingHom.id F) hG e (formAdj (RingHom.id F) G e)
      _ = e * formAdj (RingHom.id F) G e := by
          rw [Geo.formAdj_formAdj (RingHom.id F) (fun x => rfl) hG hGh e]
      _ = e := heq

private lemma nbrPSpx_rootImage
    {X : Type} [Group X] {n f r : ℕ} (ψ : (ggU .PSp n f).K →* X)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    {K' : Subgroup (ggU .PSp n f).K} {K : Subgroup X} (hK'map : K'.map ψ = K)
    {ι : (ggU .PSp r f).K →* (ggU .PSp n f).K}
    (hιcent : ∀ y, ι y ∈ Subgroup.center (ggU .PSp n f).K →
      y ∈ Subgroup.center (ggU .PSp r f).K)
    (hιrange : ι.range = K')
    {R' : Subgroup (ggU .PSp n f).K} {R : Subgroup X} (hR'map : R'.map ψ = R)
    (hR'K' : R' ≤ K')
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂))
    (hlong : ∀ v₀ : (Fin n ⊕ Fin n) → GaloisField 2 f, v₀ ≠ 0 → matTransvGroup v₀
        (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) v₀) ≤ K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∃ (β : Fin (ggU .PSp r f).D.rank → ℤ) (u : (ggU .PSp r f).K),
        β ∈ (ggU .PSp r f).D.roots ∧ GGLongRoot (ggU .PSp r f).D β ∧
        ((((ggU .PSp r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = matTransvGroup v₀
          (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) v₀))
    (hshort : ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 →
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
          K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∃ (β : Fin (ggU .PSp r f).D.rank → ℤ) (u : (ggU .PSp r f).K),
        β ∈ (ggU .PSp r f).D.roots ∧ GGShortTag .PSp ∧ 2 • β ∉ (ggU .PSp r f).D.roots ∧
        ((((ggU .PSp r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = altSiegelGroup
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) a₁ a₂) :
    ∃ β : Fin (ggU .PSp r f).D.rank → ℤ, β ∈ (ggU .PSp r f).D.roots ∧
      GGRootVia (ggU .PSp r f) K R β := by
  rcases hgeo with ⟨v, hv, hmv⟩ | ⟨a₁, a₂, ha₁, ha₂, hli, horth, hmv⟩
  · have hle : matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) ≤
        K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
      rw [← hmv]
      exact Subgroup.map_mono hR'K'
    obtain ⟨β, u, hβ, -, hβeq⟩ := hlong v hv hle
    refine ⟨β, hβ, ⟨ψ.comp ι, ?_, ?_, u, ?_⟩⟩
    · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
        _ = Subgroup.map ψ K' := by rw [hιrange]
        _ = K := hK'map
    · intro y hy
      apply hιcent
      apply hψ
      rw [MonoidHom.mem_ker]
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
      exact hy
    · have hmodel : (((ggU .PSp r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' :=
        nbrPSp_map_subtype_injective (hβeq.trans hmv.symm)
      rw [ggRootSub, ← hR'map, ← hmodel, Subgroup.map_map]
  · have hle : altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
        K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
      rw [← hmv]
      exact Subgroup.map_mono hR'K'
    obtain ⟨β, u, hβ, -, -, hβeq⟩ := hshort a₁ a₂ ha₁ ha₂ hli horth hle
    refine ⟨β, hβ, ⟨ψ.comp ι, ?_, ?_, u, ?_⟩⟩
    · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
        _ = Subgroup.map ψ K' := by rw [hιrange]
        _ = K := hK'map
    · intro y hy
      apply hιcent
      apply hψ
      rw [MonoidHom.mem_ker]
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
      exact hy
    · have hmodel : (((ggU .PSp r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' :=
        nbrPSp_map_subtype_injective (hβeq.trans hmv.symm)
      rw [ggRootSub, ← hR'map, ← hmodel, Subgroup.map_map]

private theorem nbrPSpx_K_sp_setup
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hfull : ∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
      (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype)) (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (R Rm : Subgroup X) (hR : R ≤ J) (hR0 : GGRootPosG0 .PSp n f p ψ R Rm)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    ∃ (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
      (K' : Subgroup (ggU .PSp n f).K)
      (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (R' : Subgroup (ggU .PSp n f).K),
      S' ⊆ S ∧
      (∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f)) ∧
      (∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') ∧
      (∀ s ∈ S', Odd (orderOf s)) ∧
      IsComponentOf K' ((Subgroup.centralizer S').comap
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) ∧
      K'.map ψ = K ∧
      IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))
        (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε' ∧
      IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      e' * ε' = e' ∧
      (e' = ε' ∨ (e' ≠ ε' ∧ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ e' ∧ ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e')) ∧
      IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆ ∧
      J' ≤ K' ∧ ε * ε' = ε ∧
      IsEmpty (↥K' ≃* alternatingGroup (Fin 6)) ∧
      R'.map ψ = R ∧
      ((∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
          R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
            matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
        (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
          LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
          a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
          R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
            altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)) ∧
      R' ≤ K' ∧
      ((e' = ε' ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2) ∨
        (e' = ε' ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
          blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4) ∨
        (e' ≠ ε' ∧
          blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2)) := by
  obtain ⟨S', K', ε', e', hSe, hSU', hS', hodd', hK'comp, hK'map, hε', he', he'ε', hsplit',
    hK'ε', hJK', htie⟩ := nbrPSpx_neighbourBlockData n f ψ p G₀ B₁ D J L x hH S J' ε hS hfull
        hJ'comp hJ'map hε hJ'ε e heD K hKG₀ hKcomp hJK
  have hA6' : IsEmpty (↥K' ≃* alternatingGroup (Fin 6)) :=
    nbrPSp_notA6 n f ψ p G₀ B₁ D J L x hH e heD K hKG₀ hKcomp hJK hKne K' hK'map
  obtain ⟨R', hR'map, hgeo⟩ := nbrPSp_rootLift n f p ψ R Rm hR0
  have hinj : Function.Injective ψ := nbrPSp_injective n f ψ hH.2.1
  have hR'K' : R' ≤ K' := by
    intro y hy
    have hyR : ψ y ∈ R := by rw [← hR'map]; exact Subgroup.mem_map_of_mem ψ hy
    have hyK : ψ y ∈ K'.map ψ := by rw [hK'map]; exact hJK (hR hyR)
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyK
    rwa [hinj hzy] at hz
  exact ⟨S', K', ε', e', R', hSe, hSU', hS', hodd', hK'comp, hK'map, hε', he', he'ε',
    hsplit', hK'ε', hJK', htie, hA6', hR'map, hgeo, hR'K',
    nbrPSp_blockDegree n f S' hSU' hS' hodd' K' R' ε' e' he' hsplit' hK'ε'
      hR'K' hgeo⟩

private theorem nbrPSpx_K_sp_selfDual
    {X : Type} [Group X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (heJ : IsPrimIdemIn
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hcase : e_J = ε)
    (mJ : ℕ) (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * mJ) (K : Subgroup X) (R : Subgroup X)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (K' : Subgroup (ggU .PSp n f).K)
    (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (R' : Subgroup (ggU .PSp n f).K)
    (hK'map : K'.map ψ = K)
    (hSe : S' ⊆ S) (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε')
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hK'ε' : IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆) (htie : ε * ε' = ε) (hA6' : IsEmpty (↥K' ≃* alternatingGroup
              (Fin 6)))
    (hR'map : R'.map ψ = R)
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂))
    (hR'K' : R' ≤ K') (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (hneJJ : e_J ≠ e')
    (hcaseSp : e' = ε' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2) :
    ∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), mJ < mK ∧
      βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK := by
  obtain ⟨heqSp, hdSp⟩ := hcaseSp
  have hadj' : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' = e' := by
    rw [heqSp]; exact hε'.2.2.2.1
  have hK'e' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S' e' : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' e' :
        Subgroup (ggU .PSp n f).K)⁆ := by
    rw [heqSp]; exact hK'ε'
  obtain ⟨r, ι, hrank', hιcent, hιrange, hlong, hshort⟩ :=
    exists_blockModelClosure_selfDual_PSp_explicit n f S' hS' he' hadj' hdSp hK'e' hA6'
  obtain ⟨βK, hβK, hviaK⟩ :=
    nbrPSpx_rootImage ψ hψ hK'map hιcent hιrange hR'map hR'K' hgeo hlong hshort
  refine ⟨r, βK, ?_, hβK, hviaK⟩
  have he'A : e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have htieJ : e_J * e' = e_J := by
    rw [← hcase, ← heqSp] at htie
    exact htie
  have hba : e' * e_J = e_J :=
    (nbrPSpx_adjoin_comm (S := S) hS e' he'A e_J heJ.1).eq.trans htieJ
  have hrank_lt := nbrPSpx_rank_lt_of_mul_eq heJ.2.1 htieJ hba hneJJ
  have h2r : 2 * mJ < 2 * r := by rw [← hrankJ, hrank']; exact hrank_lt
  omega

private lemma nbrPSpx_mul_e_eq_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (he : IsPrimIdemIn A e)
    (hdeg : blockDegree A e < 2) : ∀ a ∈ A, ∃ c : F, a * e = c • e := by
  let M : Submodule F (Matrix ι ι F) := (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have heM : e ∈ M := ⟨1, by simpa using A.one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hne : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  haveI : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
  have hpos : 0 < Module.finrank F M := Module.finrank_pos_iff.mpr inferInstance
  have hlt : Module.finrank F M < 2 := hdeg
  have hfin : Module.finrank F M = 1 := by omega
  have hspan : M = Submodule.span F {e} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin heM he.2.2.1
  intro a ha
  have hae : a * e ∈ M := ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  rw [hspan] at hae
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hae
  exact ⟨c, hc.symm⟩

private lemma nbrPSpx_glBlockCentralizer_le {n f : ℕ}
    {S S_e : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (heSe : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e)) :
    glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S_e e ≤
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S e := by
  intro u hu
  obtain ⟨huc, hufix⟩ : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u ∈
      Subgroup.centralizer S_e ⊓ glFixing (1 - e) := Subgroup.mem_comap.mp hu
  have hfix : (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) * (1 - e) = 1 - e := hufix
  have hcomm_e : (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) * e = e * (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) := nbrPSpx_commute_adjoin (S := S_e) huc heSe
  refine Subgroup.mem_comap.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, hufix⟩
  intro s hs
  have hsA : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
  obtain ⟨c, hc⟩ := nbrPSpx_mul_e_eq_smul he hdeg _ hsA
  have hse : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e =
      e * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    (nbrPSpx_adjoin_comm hS (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) hsA e he.1).eq
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set G := (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) with hGdef
  set Sm := (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) with hSmdef
  have hG : G = G * e + (1 - e) := by
    have h := hfix
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    calc G = (G - G * e) + G * e := by abel
      _ = (1 - e) + G * e := by rw [h]
      _ = G * e + (1 - e) := by abel
  have hSG : Sm * G = c • (G * e) + (Sm - c • e) := by
    calc Sm * G = Sm * (G * e + (1 - e)) := by rw [← hG]
      _ = Sm * (G * e) + (Sm - Sm * e) := by
        rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
      _ = c • (G * e) + (Sm - c • e) := by
        rw [hc, hcomm_e, ← Matrix.mul_assoc, hc, Matrix.smul_mul]
  have hGS : G * Sm = c • (G * e) + (Sm - c • e) := by
    calc G * Sm = (G * e + (1 - e)) * Sm := by rw [← hG]
      _ = G * (e * Sm) + (Sm - e * Sm) := by
        rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = c • (G * e) + (Sm - c • e) := by rw [← hse, hc, Matrix.mul_smul]
  rw [hSG, hGS]

private theorem nbrPSpx_K_sp_ne
    {X : Type} [Group X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (J' : Subgroup (ggU .PSp n f).K) (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (heJ : IsPrimIdemIn
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hcase : e_J = ε ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    (J K : Subgroup X) (hKne : K ≠ J) (hJ'map : J'.map ψ = J)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (K' : Subgroup (ggU .PSp n f).K)
    (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hK'map : K'.map ψ = K)
    (hSe : S' ⊆ S)
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε')
    (hK'ε' : IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
          Subgroup (ggU .PSp n f).K)⁆)
    (hJK' : J' ≤ K')
    (hcaseSp : e' = ε' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2) :
    e_J ≠ e' := by
  intro heq
  have heqε : ε = ε' := by rw [← hcase.1, heq, ← hcaseSp.1]
  have hK'block : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S' ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K)⁆ := by
    rw [heqε]; exact hK'ε'
  have heSe : ε ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S') := by
    rw [heqε]; exact hε'.1
  have hle : glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε ≤
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε := by
    have hprim : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε := by
      rw [← hcase.1]; exact heJ
    have hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε < 2 := by
      rw [← hcase.1]; exact hcase.2
    exact nbrPSpx_glBlockCentralizer_le (S := S) (S_e := S') hS hprim hdeg heSe
  have hge : glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε ≤
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε := by
    intro u hu
    obtain ⟨huc, hufix⟩ : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u ∈
        Subgroup.centralizer S ⊓ glFixing (1 - ε) := Subgroup.mem_comap.mp hu
    exact Subgroup.mem_comap.mpr ⟨Subgroup.centralizer_le hSe huc, hufix⟩
  have hG_eq : glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε =
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :=
    le_antisymm hge hle
  have hK'blockS : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆ :=
    hG_eq.symm ▸ hK'block
  haveI : Finite (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) := inferInstance
  haveI : Finite (ggU .PSp n f).K := Subtype.finite
  have hJK'' : J' = K' :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ'ε hK'blockS hJK'
  have hKJ : K = J :=
    ((hJ'map.symm.trans (congrArg (Subgroup.map ψ) hJK'')).trans hK'map).symm
  exact hKne hKJ

private lemma nbrPSpx_mul_e'_of_tie {n f : ℕ}
    {ε ε' e_J e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hcase : e_J = ε) (hcaseSU : e' = ε') (htie : ε * ε' = ε) :
    e_J * e' = e_J := by
  rw [← hcase, ← hcaseSU] at htie
  exact htie

private lemma nbrPSpx_blockField_inv {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F}
    {K : Type} [Field K] [Algebra F K] (π : A →ₐ[F] K)
    (hπs : Function.Surjective π) (hπk : ∀ a, π a = 0 ↔ (a : Matrix ι ι F) * e = 0) :
    ∀ x ∈ A, x * e ≠ 0 → ∃ y ∈ A, y * x * e = e := by
  intro x hx hxne
  have hπx : π ⟨x, hx⟩ ≠ 0 := fun h0 => hxne ((hπk ⟨x, hx⟩).mp h0)
  obtain ⟨z, hz⟩ := hπs ((π ⟨x, hx⟩)⁻¹)
  refine ⟨(z : Matrix ι ι F), z.2, ?_⟩
  have hzx : π (z * ⟨x, hx⟩) = 1 := by rw [map_mul, hz, inv_mul_cancel₀ hπx]
  have h1 : π (z * ⟨x, hx⟩ - 1) = 0 := by rw [map_sub, hzx, map_one, sub_self]
  have h2 := (hπk (z * ⟨x, hx⟩ - 1)).mp h1
  have h3 : ((z : Matrix ι ι F) * x - 1) * e = 0 := by simpa using h2
  rw [sub_mul, Matrix.one_mul] at h3
  exact sub_eq_zero.mp h3

private lemma nbrPSpx_field_of_prim {n f : ℕ}
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    {e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e') :
    ∀ x ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S'),
      x * e' ≠ 0 → ∃ y ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S'),
        y * x * e' = e' := by
  obtain ⟨Kf, hKf, hKa, hKfin, π, hπs, hπk, -⟩ := exists_blockField (S := S') hS' hodd' he'
  letI : Field Kf := hKf
  letI : Algebra (GaloisField 2 f) Kf := hKa
  exact nbrPSpx_blockField_inv π hπs hπk

private theorem nbrPSpx_K_sp_notSU (n f : ℕ)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (heJ : IsPrimIdemIn
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hcase : e_J = ε ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSe : S' ⊆ S) (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (htie : ε * ε' = ε)
    (hcaseSU : e' = ε' ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4) : False := by
  have htieJ : e_J * e' = e_J := nbrPSpx_mul_e'_of_tie hcase.1 hcaseSU.1 htie
  have hfield := nbrPSpx_field_of_prim S' hS' hodd' he'
  have hAA' : Algebra.adjoin (GaloisField 2 f) (Units.val '' S') ≤
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hdeg_le := nbrPSpx_blockDegree_le_of_mul
    (A := Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
    (A' := Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) hAA'
    (fun a b ha hb => (nbrPSpx_adjoin_comm hS a ha b hb).eq) heJ htieJ hfield
  omega

private theorem nbrPSpx_K_sp_notSL (n f : ℕ)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (heJ : IsPrimIdemIn
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (hcase : e_J = ε)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSe : S' ⊆ S) (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hsplit' : e' = ε' ∨ (e' ≠ ε' ∧ formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' ≠ e' ∧ ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e'))
    (htie : ε * ε' = ε)
    (hcaseSL : e' ≠ ε' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2) : False := by
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hGh : Matrix.transpose ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) (GaloisField 2 f)).map (RingHom.id (GaloisField 2 f))) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.LieType.BorelTits.spJ n (GaloisField 2 f) from rfl]
    rw [show ((CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) = (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f))
        from rfl]
    exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU s hs)
    simpa using h
  have hSU'_iso : ∀ s ∈ S', Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU' s hs)
    simpa using h
  have heq' : ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' := by
    rcases hsplit' with hself | ⟨-, -, heq'⟩
    · exact absurd hself hcaseSL.1
    · exact heq'
  have hpair' : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' ≠ e' := by
    rcases hsplit' with hself | ⟨-, hpair', -⟩
    · exact absurd hself hcaseSL.1
    · exact hpair'
  have he'A : e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hstarA : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU_iso he'A
  have hstarA' : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S') :=
    Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU'_iso he'.1
  have horth' : e' * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' = 0 :=
    nbrPSpx_mul_formAdj_eq_zero
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      hG hGh (fun a b ha hb => (nbrPSpx_adjoin_comm hS' a ha b hb).eq) he' hstarA' hpair'
  have hadjJ : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J = e_J := by
    rw [hcase]; exact hε.2.2.2.1
  have hle : e_J * (e' + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e') = e_J := by
    rw [← hcase, heq'] at htie
    exact htie
  exact nbrPSpx_selfDual_not_below_dualPair
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    hG (fun a b ha hb => (nbrPSpx_adjoin_comm hS a ha b hb).eq) heJ hadjJ he'A hstarA
    he'.2.1 hle

private theorem nbrPSpx_K_sp
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hfull : ∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
      (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hcase : e_J = ε ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    (mJ : ℕ) (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * mJ)
    (R Rm : Subgroup X) (hR : R ≤ J) (hR0 : GGRootPosG0 .PSp n f p ψ R Rm)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    ∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), mJ < mK ∧
      βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK := by
  obtain ⟨S', K', ε', e', R', hSe, hSU', hS', hodd', hK'comp, hK'map, hε', he', he'ε',
    hsplit', hK'ε', hJK', htie, hA6', hR'map, hgeo, hR'K', hclass⟩ :=
    nbrPSpx_K_sp_setup n f ψ p G₀ B₁ D J L x hH S J' ε hS hfull hJ'comp hJ'map
      hε hJ'ε R Rm hR hR0 e heD K hKG₀ hKcomp hJK hKne
  rcases hclass with hSp | hSu | hSl
  · exact nbrPSpx_K_sp_selfDual n f ψ S ε e_J hS heJ hcase.1 mJ hrankJ K R
      S' K' ε' e' R' hK'map hSe hS' hε' he' hK'ε' htie hA6' hR'map hgeo hR'K' hH.2.1
      (nbrPSpx_K_sp_ne n f ψ S J' ε e_J hS heJ hcase J K hKne hJ'map S' K' ε' e' hK'map hSe hε'
          hK'ε' hJ'ε hJK' hSp) hSp
  · exact (nbrPSpx_K_sp_notSU n f S ε e_J hS heJ hcase S' ε' e' hSe hS' hodd' he' htie
      hSu).elim
  · exact (nbrPSpx_K_sp_notSL n f S ε e_J hSU hS heJ hε hcase.1 S' ε' e' hSe hSU' hS' he'
      hsplit' htie hSl).elim

private theorem nbrPSpx_K_su_selfDual
    {X : Type} [Group X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (heJ : IsPrimIdemIn
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hcase : e_J = ε)
    (m'J : ℕ) (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * m'J)
    (K R : Subgroup X)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (K' : Subgroup (ggU .PSp n f).K)
    (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (R' : Subgroup (ggU .PSp n f).K)
    (hK'map : K'.map ψ = K)
    (hSe : S' ⊆ S) (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε')
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hK'ε' : IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆) (htie : ε * ε' = ε) (hA6' : IsEmpty (↥K' ≃* alternatingGroup
              (Fin 6)))
    (hR'map : R'.map ψ = R)
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂))
    (hR'K' : R' ≤ K') (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (hcaseSp : e' = ε' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2) :
    ∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), m'J ≤ mK ∧
      βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK := by
  have hadj' : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' = e' := by
    rw [hcaseSp.1]; exact hε'.2.2.2.1
  have hK'e' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S' e' : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' e' :
        Subgroup (ggU .PSp n f).K)⁆ := by
    rw [hcaseSp.1]; exact hK'ε'
  obtain ⟨r, ι, hrank', hιcent, hιrange, hlong, hshort⟩ :=
    exists_blockModelClosure_selfDual_PSp_explicit n f S' hS' he' hadj' hcaseSp.2 hK'e' hA6'
  obtain ⟨βK, hβK, hviaK⟩ :=
    nbrPSpx_rootImage ψ hψ hK'map hιcent hιrange hR'map hR'K' hgeo hlong hshort
  refine ⟨r, βK, ?_, hβK, hviaK⟩
  have he'A : e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have htieJ : e_J * e' = e_J := by
    rw [← hcase, ← hcaseSp.1] at htie
    exact htie
  have hba : e' * e_J = e_J :=
    (nbrPSpx_adjoin_comm hS e' he'A e_J heJ.1).eq.trans htieJ
  have hle_range : Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) ≤
      Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e')) := by
    refine Submodule.finrank_mono ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨Matrix.toLin' e_J y, by rw [← Matrix.toLin'_mul_apply, hba]⟩
  have h2 : 2 * m'J ≤ 2 * r := by rw [← hrankJ, hrank']; exact hle_range
  omega

private lemma nbrPSpx_rootImage_PSU
    {X : Type} [Group X] {n f r : ℕ} (ψ : (ggU .PSp n f).K →* X)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    {K' : Subgroup (ggU .PSp n f).K} {K : Subgroup X} (hK'map : K'.map ψ = K)
    {ι : (ggU .PSU r f).K →* (ggU .PSp n f).K}
    (hιcent : ∀ y, ι y ∈ Subgroup.center (ggU .PSp n f).K →
      y ∈ Subgroup.center (ggU .PSU r f).K)
    (hιrange : ι.range = K')
    {R' : Subgroup (ggU .PSp n f).K} {R : Subgroup X} (hR'map : R'.map ψ = R)
    (hR'K' : R' ≤ K')
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (horth : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0)
    (hmv : R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)
    (hlong : ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 →
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
          K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∃ (β : Fin (ggU .PSU r f).D.rank → ℤ) (u : (ggU .PSU r f).K),
        β ∈ (ggU .PSU r f).D.roots ∧ GGLongRoot (ggU .PSU r f).D β ∧
        ((((ggU .PSU r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = altSiegelGroup
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) a₁ a₂) :
    ∃ β : Fin (ggU .PSU r f).D.rank → ℤ, β ∈ (ggU .PSU r f).D.roots ∧
      GGLongRoot (ggU .PSU r f).D β ∧ GGRootVia (ggU .PSU r f) K R β := by
  have hle : altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
      K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
    rw [← hmv]
    exact Subgroup.map_mono hR'K'
  obtain ⟨β, u, hβ, hβlong, hβeq⟩ := hlong a₁ a₂ ha₁ ha₂ hli horth hle
  refine ⟨β, hβ, hβlong, ⟨ψ.comp ι, ?_, ?_, u, ?_⟩⟩
  · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
      _ = Subgroup.map ψ K' := by rw [hιrange]
      _ = K := hK'map
  · intro y hy
    apply hιcent
    apply hψ
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    exact hy
  · have hmodel : (((ggU .PSU r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' :=
      nbrPSp_map_subtype_injective (hβeq.trans hmv.symm)
    rw [ggRootSub, ← hR'map, ← hmodel, Subgroup.map_map]

private lemma nbrPSpx_glBlockCentralizer_le_two {n f : ℕ}
    {S S_e : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (heSe : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e))
    (hAe : ∀ s ∈ S, (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e ∈
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e)) :
    glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S_e e ≤
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S e := by
  intro u hu
  obtain ⟨huc, hufix⟩ : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u ∈
      Subgroup.centralizer S_e ⊓ glFixing (1 - e) := Subgroup.mem_comap.mp hu
  have hfix : (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) * (1 - e) = 1 - e := hufix
  have hcomm_e : (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) * e = e * (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) := nbrPSpx_commute_adjoin (S := S_e) huc heSe
  refine Subgroup.mem_comap.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, hufix⟩
  intro s hs
  have hsA : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have hse : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e =
      e * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    (nbrPSpx_adjoin_comm hS (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) hsA
      e he.1).eq
  have hSme : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e ∈
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e) := hAe s hs
  have hGSm : (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) * ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e) =
      ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e) *
      (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) := nbrPSpx_commute_adjoin (S := S_e) huc hSme
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set G := (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
      GL (Fin n ⊕ Fin n) (GaloisField 2 f)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) with hGdef
  set Sm := (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) with hSmdef
  have hG : G = G * e + (1 - e) := by
    have h := hfix
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    calc G = (G - G * e) + G * e := by abel
      _ = (1 - e) + G * e := by rw [h]
      _ = G * e + (1 - e) := by abel
  have hSG : Sm * G = Sm * (G * e) + (Sm - Sm * e) := by
    calc Sm * G = Sm * (G * e + (1 - e)) := by rw [← hG]
      _ = Sm * (G * e) + Sm * (1 - e) := by rw [Matrix.mul_add]
      _ = Sm * (G * e) + (Sm - Sm * e) := by rw [Matrix.mul_sub, Matrix.mul_one]
  have hGS : G * Sm = (G * e) * Sm + (Sm - Sm * e) := by
    calc G * Sm = (G * e + (1 - e)) * Sm := by rw [← hG]
      _ = (G * e) * Sm + (1 - e) * Sm := by rw [Matrix.add_mul]
      _ = (G * e) * Sm + (Sm - e * Sm) := by rw [Matrix.sub_mul, Matrix.one_mul]
      _ = (G * e) * Sm + (Sm - Sm * e) := by rw [hse]
  have hkey : Sm * (G * e) = (G * e) * Sm := by
    calc Sm * (G * e) = Sm * (e * G) := by rw [hcomm_e]
      _ = (Sm * e) * G := by noncomm_ring
      _ = G * (Sm * e) := hGSm.symm
      _ = G * (e * Sm) := by rw [hse]
      _ = (G * e) * Sm := by noncomm_ring
  rw [hSG, hGS, hkey]

private lemma nbrPSpx_blockDegree_eq_two_of_selfDual {n f : ℕ}
    {S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))}
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e = e)
    (h2 : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (h4 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 2 := by
  have hGdet : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hSG : ∀ s ∈ S, Matrix.transpose ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n)
      (K := GaloisField 2 f)).mp (hSU s hs)
    simpa using h
  have hpar := blockDegree_eq_one_or_even_of_formAdj_eq hGdet hS hodd hSG he hadj
  rcases hpar with h1 | heven
  · omega
  · obtain ⟨k, hk⟩ := heven
    omega

private theorem nbrPSpx_K_su_ne2
    {X : Type} [Group X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (J' : Subgroup (ggU .PSp n f).K) (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hcase : e_J = ε)
    (hdegJ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4)
    (J K : Subgroup X) (hKne : K ≠ J) (hJ'map : J'.map ψ = J)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (K' : Subgroup (ggU .PSp n f).K)
    (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hK'map : K'.map ψ = K)
    (hSe : S' ⊆ S) (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε')
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hK'ε' : IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
          Subgroup (ggU .PSp n f).K)⁆)
    (hJK' : J' ≤ K')
    (hcaseSU : e' = ε' ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4) :
    e_J ≠ e' := by
  intro heq
  have heqε : ε = ε' := by rw [← hcase, heq, ← hcaseSU.1]
  have hsub : Algebra.adjoin (GaloisField 2 f) (Units.val '' S') ≤
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hadj' : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' = e' := by
    rw [hcaseSU.1]
    exact hε'.2.2.2.1
  have hdegA' : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' = 2 :=
    nbrPSpx_blockDegree_eq_two_of_selfDual hSU' hS' hodd' he' hadj' hcaseSU.2.1 hcaseSU.2.2
  have hadjJ : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J = e_J := by
    rw [hcase]
    exact hε.2.2.2.1
  have hmono : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ≤
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e' :=
    Submodule.finrank_mono (Submodule.map_mono hsub)
  have h2 : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J := by
    rw [heq]
    exact le_trans hcaseSU.2.1 hmono
  have hdegJ2 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J = 2 :=
    nbrPSpx_blockDegree_eq_two_of_selfDual hSU hS hodd heJ hadjJ h2 hdegJ
  have hdegA'J : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e_J = 2 := by
    rw [heq]
    exact hdegA'
  have heJA : e_J ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S') := by
    rw [heq]
    exact he'.1
  have hAe : ∀ s ∈ S, (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e_J ∈
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S') := by
    intro s hs
    have hleM : (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' S'))).map (LinearMap.mulRight (GaloisField 2 f) e_J) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f)
          (Units.val '' S))).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      Submodule.map_mono hsub
    have heqm : (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' S'))).map (LinearMap.mulRight (GaloisField 2 f) e_J) =
        (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f)
          (Units.val '' S))).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      Submodule.eq_of_le_of_finrank_eq hleM (by
        show blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e_J =
          blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J
        rw [hdegA'J, hdegJ2])
    have hsM : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e_J ∈
        (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f)
          (Units.val '' S))).map (LinearMap.mulRight (GaloisField 2 f) e_J) :=
      ⟨s, Algebra.subset_adjoin ⟨s, hs, rfl⟩, by rw [LinearMap.mulRight_apply]⟩
    rw [← heqm] at hsM
    obtain ⟨a, ha, hae⟩ := hsM
    rw [LinearMap.mulRight_apply] at hae
    rw [← hae]
    exact Subalgebra.mul_mem _ ha heJA
  have hK'block : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S' ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
        Subgroup (ggU .PSp n f).K)⁆ := by
    rw [heqε]; exact hK'ε'
  have heSe : ε ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S') := by
    rw [heqε]; exact hε'.1
  have hle : glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε ≤
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε := by
    have hprim : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε := by
      rw [← hcase]; exact heJ
    have hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε < 4 := by
      rw [← hcase]; exact hdegJ
    exact nbrPSpx_glBlockCentralizer_le_two (S := S) (S_e := S') hS hprim heSe
      (fun s hs => by rw [← hcase]; exact hAe s hs)
  have hge : glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε ≤
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε := by
    intro u hu
    obtain ⟨huc, hufix⟩ : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u ∈
        Subgroup.centralizer S ⊓ glFixing (1 - ε) := Subgroup.mem_comap.mp hu
    exact Subgroup.mem_comap.mpr ⟨Subgroup.centralizer_le hSe huc, hufix⟩
  have hG_eq : glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε =
      glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :=
    le_antisymm hge hle
  have hK'blockS : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆ :=
    hG_eq.symm ▸ hK'block
  haveI : Finite (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) := inferInstance
  haveI : Finite (ggU .PSp n f).K := Subtype.finite
  have hJK'' : J' = K' :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ'ε hK'blockS hJK'
  have hKJ : K = J :=
    ((hJ'map.symm.trans (congrArg (Subgroup.map ψ) hJK'')).trans hK'map).symm
  exact hKne hKJ

private lemma nbrPSpx_K_suAlt_of_geo
    {n f : ℕ} {R' : Subgroup (ggU .PSp n f).K}
    (hnoTransv : ¬ ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
      R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v))
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)) :
    ∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ := by
  rcases hgeo with h | h
  · exact absurd h hnoTransv
  · exact h

private lemma nbrPSpx_K_suModel
    {n f : ℕ} (hf : 1 ≤ f)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    {e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' = e')
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4)
    {K' : Subgroup (ggU .PSp n f).K}
    (hK'e : IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' e' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' e' :
          Subgroup (ggU .PSp n f).K)⁆) :
    ∃ (r : ℕ) (ι : (ggU .PSU r f).K →* (ggU .PSp n f).K),
      2 * r = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e')) ∧
      (∀ y, ι y ∈ Subgroup.center (ggU .PSp n f).K → y ∈ Subgroup.center (ggU .PSU r f).K) ∧
      ι.range = K' ∧
      (∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
          LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
          a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 →
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
            K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
        ∃ (β : Fin (ggU .PSU r f).D.rank → ℤ) (u : (ggU .PSU r f).K),
          β ∈ (ggU .PSU r f).D.roots ∧ GGLongRoot (ggU .PSU r f).D β ∧
          ((((ggU .PSU r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
            (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = altSiegelGroup
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) a₁ a₂) :=
  by
  have h :=
    exists_blockModelClosure_selfDualTwo_PSp_explicit n f S' hSU' hS' hodd' he' hadj hdeg₁ hdeg₂
      hK'e
  rw [max_eq_left hf] at h
  exact h

private lemma nbrPSpx_siegel_mulVec {n f : ℕ}
    (a₁ a₂ x : (Fin n ⊕ Fin n) → GaloisField 2 f) (c : GaloisField 2 f) :
    Matrix.mulVec (c • (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) +
      Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁))) x =
      c • ((dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) x) • a₁ +
        (dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁) x) • a₂) := by
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  simp

private lemma nbrPSpx_func_factoring {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] (f g : V →ₗ[F] F) (h : LinearMap.ker g ≤ LinearMap.ker f) :
    ∃ c : F, f = c • g := by
  by_cases hg : g = 0
  · subst hg
    have hf : f = 0 := by
      ext x
      have : x ∈ LinearMap.ker f := h (by simp)
      simpa using this
    exact ⟨0, by rw [hf]; simp⟩
  · obtain ⟨x₀, hx₀⟩ : ∃ x, g x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hg (by ext x; exact hc x)
    refine ⟨f x₀ * (g x₀)⁻¹, ?_⟩
    ext x
    have hmem : x - (g x * (g x₀)⁻¹) • x₀ ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
      rw [mul_assoc, inv_mul_cancel₀ hx₀, mul_one, sub_self]
    have hthis := h hmem
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul] at hthis
    rw [sub_eq_zero] at hthis
    rw [hthis, LinearMap.smul_apply, smul_eq_mul]
    ring

private lemma nbrPSpx_indep_func_surj {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] (f g : V →ₗ[F] F) (h : LinearIndependent F ![f, g]) :
    ∀ α β : F, ∃ x, f x = α ∧ g x = β := by
  have hne : ∃ x, g x = 0 ∧ f x ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hker : LinearMap.ker g ≤ LinearMap.ker f := by
      intro x hx
      exact LinearMap.mem_ker.mpr (hc x (LinearMap.mem_ker.mp hx))
    obtain ⟨c, hc'⟩ := nbrPSpx_func_factoring f g hker
    have hzero : (1 : F) • f + (-c) • g = 0 := by
      rw [one_smul, hc']
      rw [show (-c) • g = -(c • g) from neg_smul c g]
      exact add_neg_cancel (c • g)
    exact one_ne_zero ((LinearIndependent.pair_iff.mp h) 1 (-c) hzero).1
  have hne2 : ∃ y, f y = 0 ∧ g y ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hker : LinearMap.ker f ≤ LinearMap.ker g := by
      intro x hx
      exact LinearMap.mem_ker.mpr (hc x (LinearMap.mem_ker.mp hx))
    obtain ⟨c, hc'⟩ := nbrPSpx_func_factoring g f hker
    have hzero : (-c) • f + (1 : F) • g = 0 := by
      rw [add_comm, one_smul, hc']
      rw [show (-c) • f = -(c • f) from neg_smul c f]
      exact add_neg_cancel (c • f)
    exact one_ne_zero ((LinearIndependent.pair_iff.mp h) (-c) 1 hzero).2
  obtain ⟨x, hxg, hxf⟩ := hne
  obtain ⟨y, hyf, hyg⟩ := hne2
  intro α β
  refine ⟨α • ((f x)⁻¹ • x) + β • ((g y)⁻¹ • y), ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, map_smul, map_smul]
    simp [smul_smul, smul_eq_mul, inv_mul_cancel₀ hxf, hyf]
  · rw [map_add, map_smul, map_smul, map_smul, map_smul]
    simp [smul_smul, smul_eq_mul, inv_mul_cancel₀ hyg, hxg]

private lemma nbrPSpx_pair_swap {F : Type*} [Field F] {M : Type*} [AddCommGroup M]
    [Module F M] (a₁ a₂ : M) (hli : LinearIndependent F ![a₁, a₂]) :
    LinearIndependent F ![a₂, a₁] := by
  rw [LinearIndependent.pair_iff] at hli ⊢
  intro s t hst
  have h' : t • a₁ + s • a₂ = 0 := by rw [add_comm]; exact hst
  exact ⟨(hli t s h').2, (hli t s h').1⟩

private lemma nbrPSpx_J_sq {n f : ℕ} :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = 1 := by
  rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
  exact CFSG.StandardType.LayerCores.spJ_mul_self

private lemma nbrPSpx_mulVecLin_J_ker (n f : ℕ) :
    LinearMap.ker (Matrix.mulVecLin (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hx' : Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) (GaloisField 2 f)) x = 0 := hx
  have hJ : Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) (GaloisField 2 f)) (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) x) = x := by
    rw [Matrix.mulVec_mulVec, nbrPSpx_J_sq, Matrix.one_mulVec]
  rw [hx', Matrix.mulVec_zero] at hJ
  exact hJ.symm

private lemma nbrPSpx_J_indep {n f : ℕ}
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂]) :
    LinearIndependent (GaloisField 2 f) ![
      Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) a₂,
      Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) a₁] := by
  have h2 : LinearIndependent (GaloisField 2 f) ![a₂, a₁] := nbrPSpx_pair_swap a₁ a₂ hli
  have h3 := h2.map' (Matrix.mulVecLin (Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) (nbrPSpx_mulVecLin_J_ker n f)
  convert h3 using 1
  funext i
  fin_cases i <;> rfl

private lemma nbrPSpx_dotProductBilin_ker (ι F : Type*) [Fintype ι] [DecidableEq ι] [Field F] :
    LinearMap.ker (dotProductBilin F F :
      (ι → F) →ₗ[F] (ι → F) →ₗ[F] F) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro w hw
  funext j
  by_contra hj
  have h := congrArg (fun l : (ι → F) →ₗ[F] F => l (Pi.single j 1)) hw
  rw [dotProductBilin_apply_apply, LinearMap.zero_apply] at h
  have h' : w j = 0 := by simpa [dotProduct, Pi.single_apply] using h
  exact hj h'

private lemma nbrPSpx_dotJ_indep {n f : ℕ}
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂]) :
    LinearIndependent (GaloisField 2 f) ![
      dotProductBilin (GaloisField 2 f) (GaloisField 2 f) (Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) a₂),
      dotProductBilin (GaloisField 2 f) (GaloisField 2 f) (Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) a₁)] := by
  have h1 := nbrPSpx_J_indep a₁ a₂ hli
  have h2 := h1.map' (dotProductBilin (GaloisField 2 f) (GaloisField 2 f))
    (nbrPSpx_dotProductBilin_ker (Fin n ⊕ Fin n) (GaloisField 2 f))
  convert h2 using 1
  funext i
  fin_cases i <;> rfl
private lemma nbrPSpx_dotJ_exists {n f : ℕ}
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (α β : GaloisField 2 f) :
    ∃ x : (Fin n ⊕ Fin n) → GaloisField 2 f,
      dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) x = α ∧
      dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁) x = β := by
  obtain ⟨x, hx⟩ := nbrPSpx_indep_func_surj _ _ (nbrPSpx_dotJ_indep a₁ a₂ hli) α β
  exact ⟨x, by simpa only [dotProductBilin_apply_apply] using hx⟩
private lemma nbrPSpx_siegel_range {n f : ℕ}
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    {c : GaloisField 2 f} (hc : c ≠ 0) :
    LinearMap.range (Matrix.mulVecLin (c • (Matrix.vecMulVec a₁ (Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) a₂) + Matrix.vecMulVec a₂ (Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) a₁)))) =
      Submodule.span (GaloisField 2 f) {a₁, a₂} := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, nbrPSpx_siegel_mulVec a₁ a₂ x c]
    exact Submodule.smul_mem _ _
      (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))))
  · rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · rw [h]
      obtain ⟨x, hx₂, hx₁⟩ := nbrPSpx_dotJ_exists a₁ a₂ hli c⁻¹ 0
      refine ⟨x, ?_⟩
      rw [Matrix.mulVecLin_apply, nbrPSpx_siegel_mulVec a₁ a₂ x c, hx₂, hx₁, zero_smul,
        add_zero, smul_smul, mul_inv_cancel₀ hc, one_smul]
    · rw [h]
      obtain ⟨x, hx₂, hx₁⟩ := nbrPSpx_dotJ_exists a₁ a₂ hli 0 c⁻¹
      refine ⟨x, ?_⟩
      rw [Matrix.mulVecLin_apply, nbrPSpx_siegel_mulVec a₁ a₂ x c, hx₂, hx₁, zero_smul,
        zero_add, smul_smul, mul_inv_cancel₀ hc, one_smul]

private lemma nbrPSpx_siegel_rank_two {n f : ℕ}
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    {c : GaloisField 2 f} (hc : c ≠ 0) :
    (c • (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) +
      Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁))).rank = 2 := by
  rw [Matrix.rank, nbrPSpx_siegel_range a₁ a₂ hli hc]
  have hsp : Submodule.span (GaloisField 2 f) ({a₁, a₂} : Set (Fin n ⊕ Fin n → GaloisField 2 f)) =
      Submodule.span (GaloisField 2 f) (Set.range ![a₁, a₂]) := by
    congr 1
    ext x
    simp [Fin.exists_fin_two, or_comm, and_comm]
  rw [hsp, finrank_span_eq_card hli]
  simp

private lemma nbrPSpx_rank_smul_le {ι F : Type*} [Fintype ι] [Field F] (c : F)
    (X : Matrix ι ι F) : (c • X).rank ≤ X.rank := by
  rw [Matrix.rank, Matrix.rank]
  refine Submodule.finrank_mono ?_
  rintro y ⟨x, rfl⟩
  exact ⟨c • x, by
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.mulVec_smul]⟩

private lemma nbrPSpx_vecMulVec_mul_self {n f : ℕ}
    (v φ : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    Matrix.vecMulVec v φ * Matrix.vecMulVec v φ =
      (φ ⬝ᵥ v) • Matrix.vecMulVec v φ := by
  rw [Matrix.vecMulVec_mul_vecMulVec]
  simp

private lemma nbrPSpx_transv_mul_formula {n f : ℕ}
    (v φ : (Fin n ⊕ Fin n) → GaloisField 2 f) (c d : GaloisField 2 f) :
    (1 + c • Matrix.vecMulVec v φ) * (1 + d • Matrix.vecMulVec v φ) =
      1 + (c + d + c * d * (φ ⬝ᵥ v)) • Matrix.vecMulVec v φ := by
  set X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    Matrix.vecMulVec v φ with hX
  have hXX : X * X = (φ ⬝ᵥ v) • X := by
    rw [hX]
    exact nbrPSpx_vecMulVec_mul_self v φ
  calc
    (1 + c • X) * (1 + d • X)
        = 1 * (1 + d • X) + (c • X) * (1 + d • X) := Matrix.add_mul _ _ _
    _ = 1 * 1 + 1 * (d • X) + ((c • X) * 1 + (c • X) * (d • X)) := by
          simp only [Matrix.mul_add]
    _ = 1 + d • X + (c • X + (c • X) * (d • X)) := by
          simp only [Matrix.one_mul, Matrix.mul_one]
    _ = 1 + d • X + (c • X + (c * d) • (X * X)) := by
          have h4 : (c • X) * (d • X) = (c * d) • (X * X) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          rw [h4]
    _ = 1 + d • X + (c • X + (c * d * (φ ⬝ᵥ v)) • X) := by
          simp only [hXX, smul_smul]
    _ = 1 + (c + d + c * d * (φ ⬝ᵥ v)) • X := by
          rw [add_smul, add_smul]
          abel

private lemma nbrPSpx_transvGroup_mul {n f : ℕ}
    (v φ : (Fin n ⊕ Fin n) → GaloisField 2 f) (c d : GaloisField 2 f)
    {g h : GL (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hg : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + c • Matrix.vecMulVec v φ)
    (hh : (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + d • Matrix.vecMulVec v φ) :
    ∃ e : GaloisField 2 f,
      ((g * h : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + e • Matrix.vecMulVec v φ := by
  refine ⟨c + d + c * d * (φ ⬝ᵥ v), ?_⟩
  rw [Units.val_mul, hg, hh, nbrPSpx_transv_mul_formula]

private lemma nbrPSpx_matTransvGroup_mem {n f : ℕ}
    (v φ : (Fin n ⊕ Fin n) → GaloisField 2 f)
    {g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)} (hg : g ∈ matTransvGroup v φ) :
    ∃ c : GaloisField 2 f, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      1 + c • Matrix.vecMulVec v φ := by
  classical
  haveI : Finite (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) := inferInstance
  refine Subgroup.closure_induction (k := {g : GL (Fin n ⊕ Fin n) (GaloisField 2 f) |
      ∃ c : GaloisField 2 f, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + c • Matrix.vecMulVec v φ}) ?_ ?_ ?_ ?_ hg
  · intro x hx
    exact hx
  · exact ⟨0, by simp⟩
  · intro x y _ _ hx hy
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact nbrPSpx_transvGroup_mul v φ c d hc hd
  · intro x _ hx
    obtain ⟨c, hc⟩ := hx
    have hpow : ∀ k : ℕ, ∃ e : GaloisField 2 f,
        ((x ^ k : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
          1 + e • Matrix.vecMulVec v φ := by
      intro k
      induction k with
      | zero => exact ⟨0, by simp⟩
      | succ k ih =>
          obtain ⟨e, he⟩ := ih
          obtain ⟨e', he'⟩ := nbrPSpx_transvGroup_mul v φ e c he hc
          exact ⟨e', by rw [pow_succ]; exact he'⟩
    have hord : 0 < orderOf x := orderOf_pos x
    have hmulx : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, tsub_add_cancel_of_le (by omega : 1 ≤ orderOf x), pow_orderOf_eq_one]
    obtain ⟨e, he⟩ := hpow (orderOf x - 1)
    exact ⟨e, by rw [inv_eq_of_mul_eq_one_left hmulx]; exact he⟩

private lemma nbrPSpx_J_dot_self {n f : ℕ} (x : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) x) x = 0 := by
  have h := CFSG.ClassicalGroups.Symplectic.spForm_self (m := n) (K := GaloisField 2 f) x
  rw [CFSG.ClassicalGroups.Symplectic.spForm_apply] at h
  rw [dotProduct_comm]
  exact h

private lemma nbrPSpx_J_dot_swap {n f : ℕ}
    (x y : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) x) y =
      dotProduct x (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) y) := by
  rw [dotProduct_comm]
  have h := (CFSG.ClassicalGroups.Symplectic.spForm_isAlt (m := n)
    (K := GaloisField 2 f)).neg_eq x y
  rw [CharTwo.neg_eq] at h
  calc
    y ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0) x
        = CFSG.ClassicalGroups.Symplectic.spForm n (GaloisField 2 f) y x := by
          rw [CFSG.ClassicalGroups.Symplectic.spForm_apply]
          rfl
    _ = CFSG.ClassicalGroups.Symplectic.spForm n (GaloisField 2 f) x y := h.symm
    _ = x ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0) y := by
          rw [CFSG.ClassicalGroups.Symplectic.spForm_apply]
          rfl

private lemma nbrPSpx_suGen_mem {n f : ℕ}
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (horth : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0) :
    ∃ g : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        1 + (Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) +
          Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁)) ∧
      g ∈ altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ := by
  set X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) +
    Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁) with hX
  have h1 : dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) a₁ = 0 := by
    rw [dotProduct_comm]
    exact horth
  have h2 : dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) a₂ = 0 :=
    nbrPSpx_J_dot_self a₂
  have h3 : dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁) a₁ = 0 :=
    nbrPSpx_J_dot_self a₁
  have h4 : dotProduct (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁) a₂ = 0 := by
    rw [nbrPSpx_J_dot_swap a₁ a₂]
    exact horth
  have hXX : X * X = 0 := by
    rw [hX]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.vecMulVec_mul_vecMulVec, h1, h2, h3, h4,
      zero_smul, Matrix.vecMulVec_zero, add_zero, zero_add]
  have hXX2 : X + X = 0 := by
    ext i j
    exact CharTwo.add_self_eq_zero (X i j)
  have hunit : (1 + X) * (1 + X) = 1 := by
    have h : (1 + X) * (1 + X) = 1 + (X + X) + X * X := by noncomm_ring
    rw [h, hXX2, hXX, add_zero, add_zero]
  refine ⟨Units.mk (1 + X) (1 + X) hunit hunit, ?_, ?_⟩
  · rw [Units.val_mk, hX]
  · rw [altSiegelGroup]
    refine Subgroup.subset_closure ⟨1, ?_⟩
    rw [Units.val_mk, one_smul, hX]

private lemma nbrPSpx_suAlt_ne_transv
    {n f : ℕ}
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f) (v : (Fin n ⊕ Fin n) → GaloisField 2 f)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (horth : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0) :
    altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≠
      matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
  intro heq
  obtain ⟨g, hg, hmem⟩ := nbrPSpx_suGen_mem a₁ a₂ horth
  have hmem' : g ∈ matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
    rw [← heq]; exact hmem
  obtain ⟨c, hc⟩ := nbrPSpx_matTransvGroup_mem v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) hmem'
  have hM : Matrix.vecMulVec a₁ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂) +
      Matrix.vecMulVec a₂ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁) =
      c • Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
    rw [hg] at hc
    exact add_left_cancel hc
  have hrank := nbrPSpx_siegel_rank_two a₁ a₂ hli (c := 1) one_ne_zero
  rw [one_smul, hM] at hrank
  have hle : (c • Matrix.vecMulVec v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)).rank ≤ 1 := by
    exact (nbrPSpx_rank_smul_le c _).trans (Matrix.rank_vecMulVec_le v _)
  omega

private lemma nbrPSpx_suRoot_altSiegel
    {n f : ℕ}
    {S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))} {K' : Subgroup (ggU .PSp n f).K}
    {R' : Subgroup (ggU .PSp n f).K}
    {ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hK'ε' : IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆)
    (hcaseSU : e' = ε' ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4)
    (hR'K' : R' ≤ K')
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)) :
    ∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ := by
  rcases hgeo with ⟨v, hv, hmv⟩ | halt
  · exfalso
    obtain ⟨g, hgR, hg1, hgrank⟩ := nbrPSp_matTransv_rank_le_one n f R' v hv hmv
    have hgmem := nbrPSp_mem_glBlockCentralizer n f S' K' R' ε' hK'ε' hR'K' hgR
    have hgS : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ Subgroup.centralizer S' :=
      (Subgroup.mem_comap.mp hgmem).1
    have hge : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ glFixing (1 - ε') :=
      (Subgroup.mem_comap.mp hgmem).2
    have hge' : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ glFixing (1 - e') := by
      rw [hcaseSU.1]
      exact hge
    have hrank_pos : 0 < Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) := by
      have := nbrPSp_rank_pos hg1
      omega
    have hdvd := blockDegree_dvd_rank_sub_one_of_glFixing (S := S') hS' hodd' he' hgS hge'
    have := le_trans (Nat.le_of_dvd hrank_pos hdvd) hgrank
    omega
  · exact halt

private lemma nbrPSpx_K_su_noTransv
    {n f : ℕ}
    {S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))} {K' : Subgroup (ggU .PSp n f).K}
    {R' : Subgroup (ggU .PSp n f).K}
    {ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hK'ε' : IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆)
    (hcaseSU : e' = ε' ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4)
    (hR'K' : R' ≤ K')
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)) :
    ¬ ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
      R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
  obtain ⟨a₁, a₂, ha₁, ha₂, hli, horth, hmv⟩ :=
    nbrPSpx_suRoot_altSiegel hS' hodd' he' hK'ε' hcaseSU hR'K' hgeo
  intro ⟨v, hv, htransv⟩
  exact nbrPSpx_suAlt_ne_transv a₁ a₂ v hli horth (hmv.symm.trans htransv)

private theorem nbrPSpx_K_su_selfDualTwo
    {X : Type} [Group X] (n f : ℕ) (hf : 1 ≤ f) (ψ : (ggU .PSp n f).K →* X)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (J' : Subgroup (ggU .PSp n f).K) (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hcase : e_J = ε)
    (m'J : ℕ) (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * m'J)
    (J K R : Subgroup X) (hKne : K ≠ J)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (K' : Subgroup (ggU .PSp n f).K)
    (ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (R' : Subgroup (ggU .PSp n f).K)
    (hK'map : K'.map ψ = K) (hJ'map : J'.map ψ = J)
    (hSe : S' ⊆ S) (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε')
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hK'ε' : IsComponentOf K' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆)
    (hJK' : J' ≤ K') (htie : ε * ε' = ε)
    (hR'map : R'.map ψ = R)
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂))
    (hR'K' : R' ≤ K') (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
          Subgroup (ggU .PSp n f).K)⁆)
    (hdegJ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4)
    (hcaseSU : e' = ε' ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4) :
    ∃ (m'K : ℕ) (βK : Fin (ggU .PSU m'K f).D.rank → ℤ), m'J < m'K ∧
      βK ∈ (ggU .PSU m'K f).D.roots ∧ GGLongRoot (ggU .PSU m'K f).D βK ∧
      GGRootVia (ggU .PSU m'K f) K R βK := by
  obtain ⟨a₁, a₂, ha₁, ha₂, hli, horth, hmv⟩ :=
    nbrPSpx_K_suAlt_of_geo
      (nbrPSpx_K_su_noTransv hS' hodd' he' hK'ε' hcaseSU hR'K' hgeo) hgeo
  have hadj' : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' = e' := by
    rw [hcaseSU.1]; exact hε'.2.2.2.1
  have hK'e' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S' e' : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' e' :
        Subgroup (ggU .PSp n f).K)⁆ := by
    rw [hcaseSU.1]; exact hK'ε'
  obtain ⟨r, ι, hrank', hιcent, hιrange, hlong⟩ :=
    nbrPSpx_K_suModel hf S' hSU' hS' hodd' he' hadj' hcaseSU.2.1 hcaseSU.2.2 hK'e'
  obtain ⟨βK, hβK, hβlong, hviaK⟩ :=
    nbrPSpx_rootImage_PSU ψ hψ hK'map hιcent hιrange hR'map hR'K' a₁ a₂ ha₁ ha₂ hli horth hmv
      hlong
  refine ⟨r, βK, ?_, hβK, hβlong, hviaK⟩
  have he'A : e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have htieJ : e_J * e' = e_J := by
    rw [← hcase, ← hcaseSU.1] at htie
    exact htie
  have hba : e' * e_J = e_J :=
    (nbrPSpx_adjoin_comm hS e' he'A e_J heJ.1).eq.trans htieJ
  have hneJJ : e_J ≠ e' :=
    nbrPSpx_K_su_ne2 n f ψ S J' ε e_J hS hSU hodd hε heJ hcase hdegJ J K hKne hJ'map S' K'
      ε' e' hK'map hSe hS' hSU' hodd' hε' he' hK'ε' hJ'ε hJK' hcaseSU
  have hrank_lt := nbrPSpx_rank_lt_of_mul_eq heJ.2.1 htieJ hba hneJJ
  have h2r : 2 * m'J < 2 * r := by rw [← hrankJ, hrank']; exact hrank_lt
  omega

private theorem nbrPSpx_K_su
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hfull : ∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
      (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hcase : e_J = ε ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 4)
    (m'J : ℕ) (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = 2 * m'J)
    (R Rm : Subgroup X) (hR : R ≤ J) (hR0 : GGRootPosG0 .PSp n f p ψ R Rm)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    (∃ (m'K : ℕ) (βK : Fin (ggU .PSU m'K f).D.rank → ℤ), m'J < m'K ∧
      βK ∈ (ggU .PSU m'K f).D.roots ∧ GGLongRoot (ggU .PSU m'K f).D βK ∧
      GGRootVia (ggU .PSU m'K f) K R βK) ∨
    (∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), m'J ≤ mK ∧
      βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK) := by
  obtain ⟨S', K', ε', e', R', hSe, hSU', hS', hodd', hK'comp, hK'map, hε', he', he'ε',
    hsplit', hK'ε', hJK', htie, hA6', hR'map, hgeo, hR'K', hclass⟩ :=
    nbrPSpx_K_sp_setup n f ψ p G₀ B₁ D J L x hH S J' ε hS hfull hJ'comp hJ'map
      hε hJ'ε R Rm hR hR0 e heD K hKG₀ hKcomp hJK hKne
  rcases hclass with hSp | hSu | hSl
  · exact Or.inr (nbrPSpx_K_su_selfDual n f ψ S ε e_J hS heJ hcase.1 m'J hrankJ K R S' K' ε' e' R'
      hK'map hSe hS' hε' he' hK'ε' htie hA6' hR'map hgeo hR'K'
      hH.2.1 hSp)
  · exact Or.inl (nbrPSpx_K_su_selfDualTwo n f (CFSG.Blueprint.LieModel.admissible hH.2.2.1).2.1
      ψ S J' ε e_J hSU hS hodd hε heJ hcase.1 m'J
      hrankJ J K R hKne S' K' ε' e' R' hK'map hJ'map hSe hSU' hS' hodd' hε' he' hK'ε' hJK'
      htie hR'map hgeo hR'K' hH.2.1 hJ'ε hcase.2.2 hSu)
  · exact (nbrPSpx_K_sp_notSL n f S ε e_J hSU hS heJ hε hcase.1 S' ε' e' hSe hSU' hS' he'
      hsplit' htie hSl).elim

private lemma nbrPSpx_rootImage_PSL
    {X : Type} [Group X] {n f r : ℕ} (ψ : (ggU .PSp n f).K →* X)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    {K' : Subgroup (ggU .PSp n f).K} {K : Subgroup X} (hK'map : K'.map ψ = K)
    {ι : (ggU .PSL r f).K →* (ggU .PSp n f).K}
    (hιcent : ∀ y, ι y ∈ Subgroup.center (ggU .PSp n f).K →
      y ∈ Subgroup.center (ggU .PSL r f).K)
    (hιrange : ι.range = K')
    {R' : Subgroup (ggU .PSp n f).K} {R : Subgroup X} (hR'map : R'.map ψ = R)
    (hR'K' : R' ≤ K')
    (a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (horth : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0)
    (hmv : R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)
    (hlong : ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 →
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
          K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∃ (β : Fin (ggU .PSL r f).D.rank → ℤ) (u : (ggU .PSL r f).K),
        β ∈ (ggU .PSL r f).D.roots ∧ GGLongRoot (ggU .PSL r f).D β ∧
        ((((ggU .PSL r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = altSiegelGroup
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) a₁ a₂) :
    ∃ β : Fin (ggU .PSL r f).D.rank → ℤ, β ∈ (ggU .PSL r f).D.roots ∧
      GGLongRoot (ggU .PSL r f).D β ∧ GGRootVia (ggU .PSL r f) K R β := by
  have hle : altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
      K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
    rw [← hmv]
    exact Subgroup.map_mono hR'K'
  obtain ⟨β, u, hβ, hβlong, hβeq⟩ := hlong a₁ a₂ ha₁ ha₂ hli horth hle
  refine ⟨β, hβ, hβlong, ⟨ψ.comp ι, ?_, ?_, u, ?_⟩⟩
  · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
      _ = Subgroup.map ψ K' := by rw [hιrange]
      _ = K := hK'map
  · intro y hy
    apply hιcent
    apply hψ
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    exact hy
  · have hmodel : (((ggU .PSL r f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι = R' :=
      nbrPSp_map_subtype_injective (hβeq.trans hmv.symm)
    rw [ggRootSub, ← hR'map, ← hmodel, Subgroup.map_map]

private lemma nbrPSpx_dualPair_orth {n f : ℕ}
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J ≠ e_J) :
    e_J * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J = 0 := by
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hGh : Matrix.transpose ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n)
      (Fin n ⊕ Fin n) (GaloisField 2 f)).map (RingHom.id (GaloisField 2 f))) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.LieType.BorelTits.spJ n (GaloisField 2 f) from rfl]
    rw [show ((CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) = (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f))
        from rfl]
    exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU s hs)
    simpa using h
  let A : Subalgebra (GaloisField 2 f)
      (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
  have hAcomm : ∀ {a b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)},
      a ∈ A → b ∈ A → a * b = b * a := by
    intro a b ha hb
    exact (nbrPSpx_adjoin_comm hS a ha b hb).eq
  have hstarA : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J ∈ A :=
    Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU_iso heJ.1
  by_contra hne0
  have hstar_idem : IsIdempotentElem (formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J) := by
    rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG e_J e_J,
      heJ.2.1.eq]
  have hidem : IsIdempotentElem (e_J * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J) :=
    IsIdempotentElem.mul_of_commute (hAcomm heJ.1 hstarA) heJ.2.1 hstar_idem
  have hee : (e_J * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J) * e_J =
      e_J * formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J := by
    rw [Matrix.mul_assoc, ← hAcomm heJ.1 hstarA, ← Matrix.mul_assoc, heJ.2.1.eq]
  rcases heJ.2.2.2 (e_J * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J) (Subalgebra.mul_mem A heJ.1 hstarA) hidem hee with h | h
  · exact hne0 h
  · apply hpair
    calc formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J
        = formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) (e_J * formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e_J) := by rw [h]
      _ = formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) (formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e_J) * formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) e_J :=
          Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG e_J
            (formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e_J)
      _ = e_J * formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) e_J := by
          rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh e_J]
      _ = e_J := h

private lemma nbrPSpx_finrank_range_add_of_orth {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Field F] {a b : Matrix ι ι F} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b = 0) (hba : b * a = 0) :
    Module.finrank F (LinearMap.range (Matrix.toLin' (a + b))) =
      Module.finrank F (LinearMap.range (Matrix.toLin' a)) +
        Module.finrank F (LinearMap.range (Matrix.toLin' b)) := by
  have hp : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' (a + b)) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨Matrix.toLin' a y, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.add_mul, Matrix.add_mulVec, Matrix.mulVec_mulVec,
      ha.eq, hba, Matrix.zero_mulVec, add_zero]
  have hq : LinearMap.range (Matrix.toLin' b) ≤ LinearMap.range (Matrix.toLin' (a + b)) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨Matrix.toLin' b y, ?_⟩
    simp only [Matrix.toLin'_apply, Matrix.add_mul, Matrix.add_mulVec, Matrix.mulVec_mulVec,
      hb.eq, hab, Matrix.zero_mulVec, zero_add]
  have hsup : LinearMap.range (Matrix.toLin' (a + b)) =
      LinearMap.range (Matrix.toLin' a) ⊔ LinearMap.range (Matrix.toLin' b) := by
    refine le_antisymm ?_ (sup_le hp hq)
    rintro _ ⟨y, rfl⟩
    change Matrix.mulVec (a + b) y ∈
      LinearMap.range (Matrix.toLin' a) ⊔ LinearMap.range (Matrix.toLin' b)
    rw [Matrix.add_mulVec]
    exact Submodule.add_mem_sup ⟨y, by rw [Matrix.toLin'_apply]⟩
      ⟨y, by rw [Matrix.toLin'_apply]⟩
  have hdisj : LinearMap.range (Matrix.toLin' a) ⊓ LinearMap.range (Matrix.toLin' b) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨z, rfl⟩, w, hw⟩
    have h1 : Matrix.mulVec a (Matrix.mulVec a z) = 0 := by
      rw [← Matrix.toLin'_apply a z, ← hw, Matrix.toLin'_apply b w, Matrix.mulVec_mulVec,
        hab, Matrix.zero_mulVec]
    have h2 : Matrix.mulVec a (Matrix.mulVec a z) = Matrix.mulVec a z := by
      rw [Matrix.mulVec_mulVec, ha.eq]
    rw [h2] at h1
    exact h1
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (Matrix.toLin' a))
    (LinearMap.range (Matrix.toLin' b))
  rw [hdisj, ← hsup] at hfin
  simp only [finrank_bot, add_zero] at hfin
  omega
private lemma nbrPSpx_sl_rank_eps
    {n f : ℕ}
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hpairJ : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J ≠ e_J)
    (heqJ : ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J)
    (kJ : ℕ) (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1) :
    Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' ε)) = 2 * (kJ + 1) := by
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU s hs)
    simpa using h
  have hAcomm : ∀ a b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f),
      a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →
      b ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) → a * b = b * a :=
    fun a b ha hb => (nbrPSpx_adjoin_comm hS a ha b hb).eq
  have hstarA : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU_iso heJ.1
  have horth : e_J * formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J = 0 := nbrPSpx_dualPair_orth S hSU hS heJ hpairJ
  have hba : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J * e_J = 0 := by
    rw [hAcomm _ _ hstarA heJ.1, horth]
  have hstaridem : IsIdempotentElem (formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e_J) := by
    rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG e_J e_J,
      heJ.2.1.eq]
  rw [heqJ]
  rw [nbrPSpx_finrank_range_add_of_orth heJ.2.1 hstaridem horth hba]
  rw [show Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1
    from hrankJ]
  rw [show Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin'
      (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J))) = kJ + 1 from by
    rw [show Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin'
        (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J))) = Matrix.rank (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J) from rfl]
    rw [nbrPSpx_rank_formAdj hG, show Matrix.rank e_J = kJ + 1 from hrankJ]]
  ring

private lemma nbrPSpx_sl_sp
    {X : Type} [Group X] {n f : ℕ}
    (ψ : (ggU .PSp n f).K →* X) (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (hSe : S' ⊆ S)
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    {K' : Subgroup (ggU .PSp n f).K} {K : Subgroup X} (hK'map : K'.map ψ = K)
    {ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hε' : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) ε')
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hK'ε' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆)
    (hSp : e' = ε' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2)
    {R' : Subgroup (ggU .PSp n f).K} {R : Subgroup X} (hR'map : R'.map ψ = R)
    (hR'K' : R' ≤ K')
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂))
    (hA6' : IsEmpty (↥K' ≃* alternatingGroup (Fin 6)))
    (htie : ε * ε' = ε) (kJ : ℕ)
    (hrank_eps : Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' ε)) =
      2 * (kJ + 1)) :
    ∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), kJ + 1 ≤ mK ∧
      βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK := by
  have hadj' : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' = e' := by
    rw [hSp.1]
    exact hε'.2.2.2.1
  have hK'e' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
      S' e' : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' e' :
        Subgroup (ggU .PSp n f).K)⁆ := by
    rw [hSp.1]
    exact hK'ε'
  obtain ⟨r, ι, hrank', hιcent, hιrange, hlong, hshort⟩ :=
    exists_blockModelClosure_selfDual_PSp_explicit n f S' hS' he' hadj' hSp.2 hK'e' hA6'
  obtain ⟨βK, hβK, hviaK⟩ :=
    nbrPSpx_rootImage ψ hψ hK'map hιcent hιrange hR'map hR'K' hgeo hlong hshort
  refine ⟨r, βK, ?_, hβK, hviaK⟩
  have he'A : e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have htieJ : ε * e' = ε := by rw [hSp.1]; exact htie
  have hcommE' : e' * ε = ε :=
    (nbrPSpx_adjoin_comm hS e' he'A ε hε.1).eq.trans htieJ
  have hleE : Matrix.rank ε ≤ Matrix.rank e' := by
    refine Submodule.finrank_mono ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨Matrix.toLin' ε y, by
      show Matrix.mulVec e' (Matrix.mulVec ε y) = Matrix.mulVec ε y
      rw [Matrix.mulVec_mulVec, hcommE']⟩
  have hrank'' : Matrix.rank e' = 2 * r := by
    rw [show Matrix.rank e' = Module.finrank (GaloisField 2 f)
        (LinearMap.range (Matrix.toLin' e')) from rfl]
    exact hrank'.symm
  have hrank_eps' : Matrix.rank ε = 2 * (kJ + 1) := by
    rw [show Matrix.rank ε = Module.finrank (GaloisField 2 f)
        (LinearMap.range (Matrix.toLin' ε)) from rfl]
    exact hrank_eps
  omega

private lemma nbrPSpx_sl_su
    {n f : ℕ}
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (hSe : S' ⊆ S)
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    {ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (heJε : e_J * ε = e_J)
    (hcase : e_J ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J ≠ e_J ∧
      ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    {ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hSu : e' = ε' ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 4)
    (htie : ε * ε' = ε) : False := by
  have hle' : e_J * e' = e_J := by
    rw [hSu.1]
    calc e_J * ε' = (e_J * ε) * ε' := by rw [heJε]
      _ = e_J * (ε * ε') := by rw [Matrix.mul_assoc]
      _ = e_J * ε := by rw [htie]
      _ = e_J := heJε
  have hfield := nbrPSpx_field_of_prim S' hS' hodd' he'
  have hAA' : Algebra.adjoin (GaloisField 2 f) (Units.val '' S') ≤
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hcomm : ∀ a b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f),
      a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →
      b ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) → a * b = b * a :=
    fun a b ha hb => (nbrPSpx_adjoin_comm hS a ha b hb).eq
  have hdeg := nbrPSpx_blockDegree_le_of_mul hAA' hcomm heJ hle' hfield
  have hdegJ_lt : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2 :=
    hcase.2.2.2
  omega

private lemma nbrPSpx_sl_sl_model
    {n f : ℕ}
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    {K' : Subgroup (ggU .PSp n f).K}
    {ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hsplit' : e' = ε' ∨ (e' ≠ ε' ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ e' ∧
      ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e'))
    (hSl : e' ≠ ε' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2)
    (hK'ε' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆) :
    ∃ (k : ℕ) (ι : (ggU .PSL (k + 1) f).K →* (ggU .PSp n f).K),
      k + 1 = Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e')) ∧
      (∀ y, ι y ∈ Subgroup.center (ggU .PSp n f).K →
        y ∈ Subgroup.center (ggU .PSL (k + 1) f).K) ∧ ι.range = K' ∧
      (∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 →
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
          K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
        ∃ (β : Fin (ggU .PSL (k + 1) f).D.rank → ℤ) (u : (ggU .PSL (k + 1) f).K),
          β ∈ (ggU .PSL (k + 1) f).D.roots ∧ GGLongRoot (ggU .PSL (k + 1) f).D β ∧
          ((((ggU .PSL (k + 1) f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
            (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = altSiegelGroup
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) a₁ a₂)
 := by
  have hpair' : formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' ≠ e' := (hsplit'.resolve_left hSl.1).2.1
  have heq' : ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) e' := (hsplit'.resolve_left hSl.1).2.2
  have hK'e' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' (e' + formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
          S' (e' + formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') : Subgroup (ggU .PSp n f).K)⁆ := by
    rw [← heq']
    exact hK'ε'
  exact exists_blockModelClosure_dualPair_PSp_explicit n f S' hSU' hS' he' hpair' hSl.2 hK'e'

private lemma nbrPSpx_dualPair_ne
    {X : Type} [Group X] {n f : ℕ}
    (ψ : (ggU .PSp n f).K →* X)
    (S S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (hSe : S' ⊆ S)
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {K' : Subgroup (ggU .PSp n f).K} {K : Subgroup X} (hK'map : K'.map ψ = K)
    (J : Subgroup X) {J' : Subgroup (ggU .PSp n f).K} (hJ'map : J'.map ψ = J)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype))
    (hK'comp : IsComponentOf K' ((Subgroup.centralizer S').comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype))
    (hJ'K' : J' ≤ K') (hKne : K ≠ J)
    {ε e_J e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (hK'ε : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε :
          Subgroup (ggU .PSp n f).K)⁆)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hdegJ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    (hdual' : e' ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ e' ∧
      ε = e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e')
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e') :
    e_J ≠ e' := by
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU s hs)
    simpa using h
  have hSU'_iso : ∀ s ∈ S', Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU' s hs)
    simpa using h
  intro heq
  have heJ' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e' := by
    rw [← heq]; exact heJ
  have hdegJ' : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e' < 2 := by
    rw [← heq]; exact hdegJ
  have hK'H : K' ≤ (Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype := by
    intro u hu
    have huG : (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u ∈
        Subgroup.centralizer S' ⊓ glFixing (1 - ε) :=
      Subgroup.mem_comap.mp (le_trans hK'ε.1 (Subgroup.commutator_le_self _) hu)
    obtain ⟨hcent_e, hfix⟩ := huG
    refine Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_iff.mpr ?_)
    intro s hs
    have hse : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
        Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
    obtain ⟨c_s, hc_s⟩ := nbrPSpx_mul_e_eq_smul heJ' hdegJ' _ hse
    have hsE : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e' =
        e' * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
      (nbrPSpx_adjoin_comm (S := S) hS _ hse _ heJ'.1).eq
    have hformAdj_mem_S : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ∈
        Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
      Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU_iso heJ'.1
    have hsF : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' =
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
      (nbrPSpx_adjoin_comm (S := S) hS _ hse _ hformAdj_mem_S).eq
    have hε_mem_S : ε ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := by
      rw [hdual'.2.2]; exact add_mem heJ'.1 hformAdj_mem_S
    have hs_eps : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * ε =
        ε * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
      (nbrPSpx_adjoin_comm (S := S) hS _ hse _ hε_mem_S).eq
    have hs1e : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * (1 - ε) =
        (1 - ε) * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hs_eps]
    have huE : (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e' =
        e' * (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
      nbrPSpx_commute_adjoin (S := S') hcent_e he'.1
    have hformAdj_mem_se : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S') :=
      Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU'_iso he'.1
    have huF : (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' =
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' *
        (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
      nbrPSpx_commute_adjoin (S := S') hcent_e hformAdj_mem_se
    have hisom : Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) := hSU_iso s hs
    have hss : (((s⁻¹ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hc_ne : c_s ≠ 0 := by
      intro h0
      have h1 : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e' = 0 := by
        rw [hc_s, h0, zero_smul]
      have h2 := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) =>
        (((s⁻¹ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) * M) h1
      rw [Matrix.mul_zero, ← Matrix.mul_assoc, hss, Matrix.one_mul] at h2
      exact heJ'.2.2.1 h2
    have h2 : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' =
        c_s • ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) e') := by
      have h := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) =>
        M * (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
        (show formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f))
            ((s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) * e') =
          formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) (c_s • e') from by rw [hc_s])
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG,
        Geo.formAdj_eq_inv_of_isometry (RingHom.id (GaloisField 2 f)) hG s hisom,
        Geo.formAdj_smul, Matrix.mul_assoc, hss, Matrix.mul_one, Matrix.smul_mul, ← hsF] at h
      exact h
    have hd_s : (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' =
        c_s⁻¹ • formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' := by
      have h3 := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) =>
        c_s⁻¹ • M) h2
      rw [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at h3
      exact h3.symm
    have hkill1 : ((((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) -
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) * e' = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hc_s, Matrix.mul_smul, huE,
        ← Matrix.mul_assoc, hc_s, Matrix.smul_mul, sub_self]
    have hkill2 : ((((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) -
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) *
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hd_s, Matrix.mul_smul, huF,
        ← Matrix.mul_assoc, hd_s, Matrix.smul_mul, sub_self]
    have hkill3 : ((((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) -
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) * (1 - ε) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, hs1e, ← Matrix.mul_assoc, hfix,
        hs1e, sub_self]
    have hsum : e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' + (1 - ε) = 1 := by
      rw [hdual'.2.2]; abel
    have hzero : ((((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
        GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) -
        (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))) = 0 := by
      calc ((((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
          GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) -
          (s : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
          (((CFSG.Open.StatedSp n (GaloisField 2 f)).subtype u :
            GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)))
          = _ * 1 := by rw [Matrix.mul_one]
        _ = _ * (e' + formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e' + (1 - ε)) := by rw [hsum]
        _ = _ * e' + _ * formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e' + _ * (1 - ε) := by rw [Matrix.mul_add, Matrix.mul_add]
        _ = 0 := by rw [hkill1, hkill2, hkill3]; abel
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact (sub_eq_zero.mp hzero).symm
  have hSe' : (Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ≤
      (Subgroup.centralizer S').comap (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype :=
    Subgroup.comap_mono (Subgroup.centralizer_le hSe)
  haveI : Finite (ggU .PSp n f).K := Subtype.finite
  have hK'compS : IsComponentOf K' ((Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) :=
    IsComponentOf.of_le_of_le hK'comp hK'H hSe'
  have hJK' : J' = K' :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hJ'comp hK'compS hJ'K'
  exact hKne (by rw [← hK'map, ← hJ'map, hJK'])

private lemma nbrPSpx_sl_sl_lt {n f : ℕ}
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (hSe : S' ⊆ S)
    {e_J e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (heJe' : e_J * e' = e_J) (hne : e_J ≠ e')
    (kJ : ℕ) (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1)
    (k : ℕ) (hrank' : k + 1 = Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e'))) :
    kJ < k := by
  have he'A : e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) he'.1
  have hba : e' * e_J = e_J :=
    (nbrPSpx_adjoin_comm hS e' he'A e_J heJ.1).eq.trans heJe'
  have hlt := nbrPSpx_rank_lt_of_mul_eq heJ.2.1 heJe' hba hne
  rw [hrankJ, ← hrank'] at hlt
  omega

private lemma nbrPSpx_sl_sl_root
    {X : Type} [Group X] {n f : ℕ}
    (ψ : (ggU .PSp n f).K →* X) (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    {K' : Subgroup (ggU .PSp n f).K} {K : Subgroup X} (hK'map : K'.map ψ = K)
    {ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hsplit' : e' = ε' ∨ (e' ≠ ε' ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ e' ∧
      ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e'))
    (hSl : e' ≠ ε' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2)
    (hK'ε' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆)
    {R' : Subgroup (ggU .PSp n f).K} {R : Subgroup X} (hR'map : R'.map ψ = R)
    (hR'K' : R' ≤ K')
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂))
    (k : ℕ)
    (ι : (ggU .PSL (k + 1) f).K →* (ggU .PSp n f).K)
    (hιcent : ∀ y, ι y ∈ Subgroup.center (ggU .PSp n f).K →
      y ∈ Subgroup.center (ggU .PSL (k + 1) f).K)
    (hιrange : ι.range = K')
    (hclosure : ∀ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 → a₂ ≠ 0 →
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] →
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 →
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ ≤
        K'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype →
      ∃ (β : Fin (ggU .PSL (k + 1) f).D.rank → ℤ) (u : (ggU .PSL (k + 1) f).K),
        β ∈ (ggU .PSL (k + 1) f).D.roots ∧ GGLongRoot (ggU .PSL (k + 1) f).D β ∧
        ((((ggU .PSL (k + 1) f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype = altSiegelGroup
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) a₁ a₂)
:
    ∃ (βK : Fin (ggU .PSL (k + 1) f).D.rank → ℤ),
      βK ∈ (ggU .PSL (k + 1) f).D.roots ∧ GGRootVia (ggU .PSL (k + 1) f) K R βK
 := by
  rcases hgeo with ⟨v, hv, hmv⟩ | ⟨a₁, a₂, ha₁, ha₂, hli, horth, hmv⟩
  · exfalso
    obtain ⟨g, hgR, hg1, hgrank⟩ := nbrPSp_matTransv_rank_le_one n f R' v hv hmv
    have hgmem := nbrPSp_mem_glBlockCentralizer n f S' K' R' ε' hK'ε' hR'K' hgR
    have hgS : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ Subgroup.centralizer S' :=
      (Subgroup.mem_comap.mp hgmem).1
    have hge : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈ glFixing (1 - ε') :=
      (Subgroup.mem_comap.mp hgmem).2
    have hpair' : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ e' := (hsplit'.resolve_left hSl.1).2.1
    have heq' : ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' := (hsplit'.resolve_left hSl.1).2.2
    have hge' : (g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ∈
        glFixing (1 - (e' + formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e')) := by
      rw [← heq']
      exact hge
    have hGdet : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).det := by
      rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
      exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
    have hGh : Matrix.transpose ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) := by
      rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) = CFSG.LieType.BorelTits.spJ n (GaloisField 2 f) from rfl]
      rw [show ((CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) =
          (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)) from rfl]
      exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two
    have hSU_iso : ∀ s ∈ S', Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) *
        ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) := by
      intro s hs
      have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
        (hSU' s hs)
      simpa using h
    have hgiso : Matrix.transpose (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) *
        ((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) := by
      have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
        g.property
      simpa using h
    have hdvd := two_mul_blockDegree_dvd_rank_sub_one_of_formAdj_ne
      (RingHom.id (GaloisField 2 f)) (fun x => rfl) hGdet hGh hSU_iso hS' hodd' he' hpair' hgS
      hgiso hge'
    have hrank_pos : 0 < Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) := by
      have := nbrPSp_rank_pos hg1
      omega
    have hbdpos : 1 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' :=
      nbrPSp_blockDegree_pos he'
    have htwo : 2 ≤ Matrix.rank (((g : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) - 1) :=
      le_trans (by omega) (Nat.le_of_dvd hrank_pos hdvd)
    omega
  · obtain ⟨βK, hβK, -, hviaK⟩ :=
      nbrPSpx_rootImage_PSL ψ hψ hK'map hιcent hιrange hR'map hR'K' a₁ a₂ ha₁ ha₂ hli horth
        hmv hclosure
    exact ⟨βK, hβK, hviaK⟩

private lemma nbrPSpx_sl_sl
    {X : Type} [Group X] {n f : ℕ}
    (ψ : (ggU .PSp n f).K →* X) (hψ : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (hSe : S' ⊆ S)
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'') (hodd' : ∀ s ∈ S', Odd (orderOf s))
    {K' : Subgroup (ggU .PSp n f).K} {K : Subgroup X} (hK'map : K'.map ψ = K)
    {ε' e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e')
    (hsplit' : e' = ε' ∨ (e' ≠ ε' ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ e' ∧
      ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e'))
    (hSl : e' ≠ ε' ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e' < 2)
    (hK'ε' : IsComponentOf K'
      ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S' ε' : Subgroup (ggU .PSp n f).K),
        (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S' ε' :
          Subgroup (ggU .PSp n f).K)⁆)
    {R' : Subgroup (ggU .PSp n f).K} {R : Subgroup X} (hR'map : R'.map ψ = R)
    (hR'K' : R' ≤ K')
    (hgeo : (∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) ∨
      (∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
        LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
        R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂)) (kJ : ℕ)
    (hrankJ : Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1)
    (heJe' : e_J * e' = e_J) (hne : e_J ≠ e')
    :
    ∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
      βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧
      GGRootVia (ggU .PSL (kK + 1) f) K R βK := by
  obtain ⟨k, ι, hrank', hιcent, hιrange, hclosure⟩ :=
    nbrPSpx_sl_sl_model S' hSU' hS' he'
      hsplit' hSl hK'ε'
  have hbound : kJ < k :=
    nbrPSpx_sl_sl_lt S hS S' hSe heJ he' heJe' hne kJ hrankJ k hrank'
  obtain ⟨βK, hβK, hviaK⟩ :=
    nbrPSpx_sl_sl_root ψ hψ S' hSU' hS' hodd' hK'map he'
      hsplit' hSl hK'ε' hR'map hR'K' hgeo k ι hιcent hιrange
      hclosure
  exact ⟨k, βK, hbound, hβK, hviaK⟩

private lemma nbrPSpx_blockDegree_formAdj {n f : ℕ}
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))
        (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e) =
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e := by
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hSU_iso : ∀ s ∈ S, Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU s hs)
    simpa using h
  have hGh : Matrix.transpose ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.LieType.BorelTits.spJ n (GaloisField 2 f) from rfl]
    rw [show ((CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) = (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f))
        from rfl]
    exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two
  let A : Subalgebra (GaloisField 2 f)
      (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) :=
    Algebra.adjoin (GaloisField 2 f) (Units.val '' S)
  let ψe : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) ≃ₗ[GaloisField 2 f]
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    { toFun := formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))
      invFun := formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))
      left_inv := fun a => Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG
        hGh a
      right_inv := fun a => Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG
        hGh a
      map_add' := fun a b => Geo.formAdj_add (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) a b
      map_smul' := fun c a => by
        rw [Geo.formAdj_smul (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) c a] }
  have hcomm : ∀ a b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f),
      a ∈ A → b ∈ A → a * b = b * a := fun a b ha hb => (nbrPSpx_adjoin_comm hS a ha b hb).eq
  have hmem : ∀ a, a ∈ A → formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) a ∈ A :=
    fun a ha => Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU_iso ha
  have hS2 : (Subalgebra.toSubmodule A).map
      (LinearMap.mulRight (GaloisField 2 f) (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e)) =
      ((Subalgebra.toSubmodule A).map (LinearMap.mulRight (GaloisField 2 f) e)).map
        ψe.toLinearMap := by
    ext M
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) a * e,
        ⟨formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) a, hmem a ha, rfl⟩, ?_⟩
      show formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f))
          (formAdj (RingHom.id (GaloisField 2 f))
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
              (GaloisField 2 f)) a * e) =
        a * formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG,
        Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh a]
      exact hcomm (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e) a (hmem e he.1) ha
    · rintro ⟨N, ⟨a, ha, rfl⟩, hN⟩
      refine ⟨formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) a, hmem a ha, ?_⟩
      rw [← hN]
      show formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) a * formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e =
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) (a * e)
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG]
      exact hcomm (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) a) (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e) (hmem a ha) (hmem e he.1)
  unfold blockDegree
  rw [hS2, LinearEquiv.finrank_map_eq ψe]

private lemma nbrPSpx_isPrimIdemIn_formAdj
    {n f : ℕ} (S' : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (hSU' : ∀ s ∈ S', s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS' : ∀ s ∈ S', ∀ s'' ∈ S', Commute s s'')
    {e' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (he' : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S')) e') :
    IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S'))
      (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e') := by
  have hG : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
      (GaloisField 2 f)).det := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
    exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
  have hSU'_iso : ∀ s ∈ S', Matrix.transpose (((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) *
      ((s : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    intro s hs
    have h := (CFSG.Open.StatedAPI.mem_statedSp_iff (n := n) (K := GaloisField 2 f)).mp
      (hSU' s hs)
    simpa using h
  have hGh : Matrix.transpose ((Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) := by
    rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f)) = CFSG.LieType.BorelTits.spJ n (GaloisField 2 f) from rfl]
    rw [show ((CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)).map
        (RingHom.id (GaloisField 2 f))) = (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f))
        from rfl]
    exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two
  have hA'comm : ∀ {a b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)},
      a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S') →
      b ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S') → a * b = b * a :=
    fun ha hb => (nbrPSpx_adjoin_comm hS' _ ha _ hb).eq
  refine ⟨Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU'_iso he'.1, ?_, ?_, ?_⟩
  · rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG e' e',
      he'.2.1.eq]
  · intro h0
    have h := congrArg (formAdj (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 f))) h0
    rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh e',
      show formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) 0 = 0 by simp [formAdj]] at h
    exact he'.2.2.1 h
  · intro x hx hxidem hxe
    have hx' : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) x ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S') :=
      Geo.formAdj_mem_adjoin (RingHom.id (GaloisField 2 f)) hG hSU'_iso hx
    have hx'idem : IsIdempotentElem (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) x) := by
      rw [IsIdempotentElem, ← Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG x x, hxidem.eq]
    have hx'e : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) x * e' =
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) x := by
      have h := congrArg (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))) hxe
      rw [Geo.formAdj_mul (RingHom.id (GaloisField 2 f)) hG x
        (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e'),
        Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh e'] at h
      rw [hA'comm hx' he'.1]
      exact h
    rcases he'.2.2.2 (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) x) hx' hx'idem hx'e with h | h
    · left
      have h2 := congrArg (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))) h
      rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh x,
        show formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) 0 = 0 by simp [formAdj]] at h2
      exact h2
    · right
      have h2 := congrArg (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))) h
      rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hG hGh x] at h2
      exact h2

private theorem nbrPSpx_K_sl
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f))) (J' : Subgroup (ggU .PSp n f).K)
    (ε e_J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 f))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hfull : ∀ s : GL (Fin n ⊕ Fin n) (GaloisField 2 f),
      s ∈ CFSG.Open.StatedSp n (GaloisField 2 f) →
      (∃ d ∈ D, IsGLLift (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype ψ s d) → s ∈ S)
    (hJ'comp : IsComponentOf J' ((Subgroup.centralizer S).comap
      (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype))
    (hJ'map : J'.map ψ = J)
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (heJε : e_J * ε = e_J)
    (hJ'ε : IsComponentOf J' ⁅(glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype
        S ε : Subgroup (ggU .PSp n f).K),
      (glBlockCentralizer (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype S ε :
        Subgroup (ggU .PSp n f).K)⁆)
    (hcase : e_J ≠ ε ∧
      formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J ≠ e_J ∧
      ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e_J ∧
      blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2)
    (kJ : ℕ) (hrankJ : Module.finrank (GaloisField 2 f)
      (LinearMap.range (Matrix.toLin' e_J)) = kJ + 1)
    (R Rm : Subgroup X) (hR : R ≤ J) (hR0 : GGRootPosG0 .PSp n f p ψ R Rm)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG₀ : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K) (hKne : K ≠ J) :
    (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
      βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧
      GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
    (∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), kJ + 1 ≤ mK ∧
      βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK) := by
  obtain ⟨S', K', ε', e', R', hSe, hSU', hS', hodd', hK'comp, hK'map, hε', he', he'ε',
    hsplit', hK'ε', hJK', htie, hA6', hR'map, hgeo, hR'K', hclass⟩ :=
    nbrPSpx_K_sp_setup n f ψ p G₀ B₁ D J L x hH S J' ε hS hfull hJ'comp hJ'map
      hε hJ'ε R Rm hR hR0 e heD K hKG₀ hKcomp hJK hKne
  have hrank_eps :=
    nbrPSpx_sl_rank_eps S hSU hS heJ hcase.2.1 hcase.2.2.1 kJ hrankJ
  rcases hclass with hSp | hSu | hSl
  · exact Or.inr (nbrPSpx_sl_sp ψ hH.2.1 S hS hε S' hSe hS' hK'map hε' he' hK'ε' hSp
      hR'map hR'K' hgeo hA6' htie kJ hrank_eps)
  · exact (nbrPSpx_sl_su S hS S' hSe hS' hodd' heJ heJε hcase he' hSu
      htie).elim
  · have hGdet : IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).det := by
      rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) = CFSG.ClassicalGroups.Symplectic.spJ n (GaloisField 2 f) from rfl]
      exact isUnit_iff_ne_zero.mpr CFSG.ClassicalGroups.Symplectic.spJ_det_ne_zero
    have hGh : Matrix.transpose ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) =
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) := by
      rw [show (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) = CFSG.LieType.BorelTits.spJ n (GaloisField 2 f) from rfl]
      rw [show ((CFSG.LieType.BorelTits.spJ n (GaloisField 2 f)).map
          (RingHom.id (GaloisField 2 f))) = (CFSG.LieType.BorelTits.spJ n (GaloisField 2 f))
          from rfl]
      exact CFSG.StandardType.LieKnownR2.Short.spJ_transpose_char_two
    have he'star : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S'))
        (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') :=
      nbrPSpx_isPrimIdemIn_formAdj S' hSU' hS' he'
    have hε'_adj : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) ε' = ε' := hε'.2.2.2.1
    have heq' : ε' = e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' := (hsplit'.resolve_left hSl.1).2.2
    have hpair' : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ e' := (hsplit'.resolve_left hSl.1).2.1
    have hstar_ne_eps : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ ε' := by
      intro h
      apply hSl.1
      have hh := congrArg (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f))) h
      rw [hε'_adj, Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hGdet
        hGh e'] at hh
      exact hh
    have hstar_ne_self : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') ≠ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' := by
      rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hGdet hGh e']
      exact fun h => hpair' h.symm
    have hstar_pair : ε' = formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') := by
      rw [Geo.formAdj_formAdj (RingHom.id (GaloisField 2 f)) (fun x => rfl) hGdet hGh e']
      exact heq'.trans (add_comm _ _)
    have hdual'' : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ ε' ∧ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') ≠ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ∧ ε' = formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') := ⟨hstar_ne_eps, hstar_ne_self, hstar_pair⟩
    have hsplit'star : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' = ε' ∨ (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ ε' ∧ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') ≠ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ∧ ε' = formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' + formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) (formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e')) := Or.inr ⟨hstar_ne_eps, hstar_ne_self, hstar_pair⟩
    have hSlstar : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' ≠ ε' ∧ blockDegree (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' S')) (formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e') < 2 :=
      ⟨hstar_ne_eps, by rw [nbrPSpx_blockDegree_formAdj S' hSU' hS' he']; exact hSl.2⟩
    have hne : e_J ≠ e' :=
      nbrPSpx_dualPair_ne ψ S S' hSe hSU hSU' hS hK'map J hJ'map hJ'comp hK'comp hJK' hKne
        hK'ε' heJ hcase.2.2.2 (hsplit'.resolve_left hSl.1) he'
    have hneStar : e_J ≠ formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' :=
      nbrPSpx_dualPair_ne ψ S S' hSe hSU hSU' hS hK'map J hJ'map hJ'comp hK'comp hJK' hKne
        hK'ε' heJ hcase.2.2.2 ⟨hstar_ne_eps, hstar_ne_self, hstar_pair⟩ he'star
    have hcommS : ∀ a b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f),
        a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) →
        b ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) → a * b = b * a :=
      fun a b ha hb => (nbrPSpx_adjoin_comm hS a ha b hb).eq
    have he'S : e' ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
      Algebra.adjoin_mono (Set.image_mono hSe) he'.1
    have heJε' : e_J * ε' = e_J := by
      calc e_J * ε' = (e_J * ε) * ε' := by rw [heJε]
        _ = e_J * (ε * ε') := by rw [Matrix.mul_assoc]
        _ = e_J * ε := by rw [htie]
        _ = e_J := heJε
    have hsumJ : e_J * e' + e_J * formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e' = e_J := by
      rw [← Matrix.mul_add, ← heq', heJε']
    have heJ_e' : e_J * e' = 0 ∨ e_J * e' = e_J := by
      apply heJ.2.2.2
      · exact Subalgebra.mul_mem _ heJ.1 he'S
      · rw [IsIdempotentElem]
        calc (e_J * e') * (e_J * e') = e_J * (e' * (e_J * e')) := by rw [mul_assoc]
          _ = e_J * ((e' * e_J) * e') := by rw [mul_assoc]
          _ = e_J * ((e_J * e') * e') := by rw [hcommS e' e_J he'S heJ.1]
          _ = e_J * (e_J * (e' * e')) := by rw [mul_assoc]
          _ = e_J * (e_J * e') := by rw [he'.2.1.eq]
          _ = (e_J * e_J) * e' := by rw [mul_assoc]
          _ = e_J * e' := by rw [heJ.2.1.eq]
      · rw [mul_assoc, hcommS e' e_J he'S heJ.1, ← mul_assoc, heJ.2.1.eq]
    rcases heJ_e' with h0 | hE
    · have hE' : e_J * formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e' = e_J := by
        have h := hsumJ
        rw [h0, zero_add] at h
        exact h
      exact Or.inl (nbrPSpx_sl_sl (e' := formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e') ψ hH.2.1 S hS heJ S' hSe hSU' hS' hodd' hK'map he'star
                hsplit'star hSlstar hK'ε' hR'map hR'K' hgeo kJ hrankJ hE'
        hneStar)
    · exact Or.inl (nbrPSpx_sl_sl ψ hH.2.1 S hS heJ S' hSe hSU' hS' hodd' hK'map he' hsplit' hSl
        hK'ε' hR'map hR'K' hgeo kJ hrankJ hE hne)

theorem ggSixPSpPosExplicit_holds
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSp n f ψ p G₀ B₁ D J L x) :
    ∃ (R Rm : Subgroup X),
      R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .PSp n f p ψ R Rm ∧ 1 ≤ f ∧
      ((∃ (mJ : ℕ) (βJ : Fin (ggU .PSp mJ f).D.rank → ℤ), mJ < n ∧
          βJ ∈ (ggU .PSp mJ f).D.roots ∧ GGRootVia (ggU .PSp mJ f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            ∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), mJ < mK ∧
              βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK) ∨
        (∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ), kJ + 1 ≤ n ∧
          βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
              βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
            (∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), kJ + 1 ≤ mK ∧
              βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK)) ∨
        (∃ (m'J : ℕ) (βJ : Fin (ggU .PSU m'J f).D.rank → ℤ), m'J ≤ n ∧
          βJ ∈ (ggU .PSU m'J f).D.roots ∧ GGRootVia (ggU .PSU m'J f) J R βJ ∧
          ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
            CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
            Odd (Nat.card (Subgroup.center ↥K)) →
            (∃ (m'K : ℕ) (βK : Fin (ggU .PSU m'K f).D.rank → ℤ), m'J < m'K ∧
              βK ∈ (ggU .PSU m'K f).D.roots ∧ GGLongRoot (ggU .PSU m'K f).D βK ∧
              GGRootVia (ggU .PSU m'K f) K R βK) ∨
            (∃ (mK : ℕ) (βK : Fin (ggU .PSp mK f).D.rank → ℤ), m'J ≤ mK ∧
              βK ∈ (ggU .PSp mK f).D.roots ∧ GGRootVia (ggU .PSp mK f) K R βK))) := by
  obtain ⟨S, J', ε, e_J, hSU, hS, hodd, hfull, hJ'comp, hJ'map, hε, heJ, heJε, hsplit,
    hJ'ε, hcase⟩ := nbrPSpx_J_split n f ψ p G₀ B₁ D J L x hH
  rcases hcase with hsp | hsu | hsl
  · obtain ⟨R, Rm, hRJ, hRmJ, hR0, hf, mJ, βJ, hmJ, hβJ, hviaJ, hrankJ⟩ :=
      nbrPSpx_J_sp n f ψ p G₀ B₁ D J L x hH S J' ε e_J hS hfull hJ'map
        hε heJ hJ'ε hsp
    refine ⟨R, Rm, hRJ, hRmJ, hR0, hf, Or.inl ⟨mJ, βJ, hmJ, hβJ, hviaJ, ?_⟩⟩
    intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
    exact nbrPSpx_K_sp n f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hfull hJ'comp
      hJ'map hε heJ hJ'ε hsp mJ hrankJ R Rm hRJ hR0 e heD K hKG₀ hKcomp hJK hKne
  · obtain ⟨R, Rm, hRJ, hRmJ, hR0, hf, m'J, βJ, hmJ, hβJ, hviaJ, hrankJ⟩ :=
      nbrPSpx_J_su n f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hJ'map
        hε heJ hJ'ε hsu
    refine ⟨R, Rm, hRJ, hRmJ, hR0, hf, Or.inr (Or.inr ⟨m'J, βJ, hmJ, hβJ, hviaJ, ?_⟩)⟩
    intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
    exact nbrPSpx_K_su n f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hodd hfull hJ'comp
      hJ'map hε heJ hJ'ε hsu m'J hrankJ R Rm hRJ hR0 e heD K hKG₀ hKcomp hJK hKne
  · have hsl' : e_J ≠ ε ∧
        formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J ≠ e_J ∧
        ε = e_J + formAdj (RingHom.id (GaloisField 2 f))
          (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
            (GaloisField 2 f)) e_J ∧
        blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2 := by
      rcases hsplit with hself | ⟨hne, hpair, heq⟩
      · exact absurd hself hsl.1
      · exact ⟨hne, hpair, heq, hsl.2⟩
    obtain ⟨R, Rm, hRJ, hRmJ, hR0, hf, kJ, βJ, hmJ, hβJ, hviaJ, hrankJ⟩ :=
      nbrPSpx_J_sl n f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hJ'map heJ hJ'ε hsl'
    refine ⟨R, Rm, hRJ, hRmJ, hR0, hf, Or.inr (Or.inl ⟨kJ, βJ, hmJ, hβJ, hviaJ, ?_⟩)⟩
    intro e heD he1 K hKG₀ hKcomp hJK hKne hZodd
    exact nbrPSpx_K_sl n f ψ p G₀ B₁ D J L x hH S J' ε e_J hSU hS hfull hJ'comp
      hJ'map hε heJ heJε hJ'ε hsl' kJ hrankJ R Rm hRJ hR0 e heD K hKG₀ hKcomp hJK hKne

end CFSG.StandardType.ClassicalPosition
