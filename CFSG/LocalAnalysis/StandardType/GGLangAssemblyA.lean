module

public import CFSG.LocalAnalysis.StandardType.GGLangDictOrbits
public import CFSG.LocalAnalysis.StandardType.GGLangDictTransport
public import CFSG.LocalAnalysis.StandardType.GGLangAlgebraic
public import CFSG.LocalAnalysis.StandardType.GGLangDetects
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
public import CFSG.LocalAnalysis.StandardType.GGLatEigenOrbit
public import CFSG.LocalAnalysis.StandardType.GGLangReidx
public import CFSG.LocalAnalysis.StandardType.GGLangDictCentralizer
public import CFSG.LocalAnalysis.StandardType.GGLangTorusMem
public import CFSG.LocalAnalysis.StandardType.GGLangTorusOrbit
public import CFSG.LocalAnalysis.StandardType.GGLangLatEigenTorus

public section

namespace CFSG.StandardType

section AssemblyA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem asmA_smat
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) :
    ∃ k : ℤ, 0 < k ∧ (fun i j : Fin B.τ.rank =>
        S (Fin.cast B.rank_eq.symm i) (Fin.cast B.rank_eq.symm j))
      = k • B.τ.symmetrizedCartan := by
  obtain ⟨k, hk, hg⟩ := B.gram_eq
  refine ⟨k, hk, ?_⟩
  ext i j
  have hsingle : latGram S (Pi.single (Fin.cast B.rank_eq.symm i) (1 : ℤ))
      (Pi.single (Fin.cast B.rank_eq.symm j) (1 : ℤ)) =
      S (Fin.cast B.rank_eq.symm i) (Fin.cast B.rank_eq.symm j) := by
    simp [latGram, Pi.single_apply]
  have hre : ∀ c : Fin (ggU (absTag t) 6 f).D.rank,
      ggLangReidx B.rank_eq (Pi.single c (1 : ℤ)) =
        (Pi.single (Fin.cast B.rank_eq c) (1 : ℤ) : Fin B.τ.rank → ℤ) := by
    intro c
    funext m
    simp only [ggLangReidx, Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro hm
      rw [← hm]
      simp
    · intro hm
      rw [hm]
      simp
  rw [Matrix.smul_apply, ← hsingle, hg, hre, hre]
  simp [iform, Pi.single_apply]

private theorem asmA_latEigenCoroot_reidx
    {R N p : ℕ} (h : R = N) (S : Matrix (Fin R) (Fin R) ℤ) (π : Equiv.Perm (Fin R))
    (O' : Set (Fin N → ℤ)) (g : Fin R → ZMod p) :
    g ∈ latEigenCoroot p S π (ggLangReidx h ⁻¹' O') →
      (fun j => g (Fin.cast h.symm j)) ∈
        latEigenCoroot p (fun i j => S (Fin.cast h.symm i) (Fin.cast h.symm j))
          (ggLangPerm h π) O' := by
  subst h
  intro hg
  change g ∈ latEigenCoroot p S π O' at hg
  change (fun j => g j) ∈ latEigenCoroot p S π O'
  exact hg

theorem ggClauseA_of_langData
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    (hp : p.Prime) (hp2 : p ≠ 2)
    (B : GGLangData L t n f p Bs S π coord)
    (hZ : LangRat.LangRatCentralizerDetectsP) :
    GGClauseA t n f p (ggPsiU t n f) Bs S π coord := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro b hb L hL
  obtain ⟨i, hq, rfl⟩ :=
    ggLang_exists_rationalComponent_of_isComponentOf B hp hp2 hb hL
  let T : Set (Fin B.τ.rank → ℤ) := rationalRoots B.setup.ρ (rootCharHom (B.a b)) i
  let O : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ) := ggLangReidx B.rank_eq ⁻¹' T
  have hζ : B.ζ ^ p = 1 := by
    have h := pow_orderOf_eq_one B.ζ
    rwa [B.ζ_order] at h
  have hpε : (p : ℤ) ∣ ((B.setup.D.q : ℕ) : ℤ) - B.ε := by
    rw [B.q_eq]
    exact_mod_cast B.p_dvd
  have hAlg : B.setup.IsAlgebraic := langSetup_isAlgebraic_of_zmod_two B.setup B.q_eq
  have hπ' : ∀ j k, B.τ.cartan (ggLangPerm B.rank_eq π j) (ggLangPerm B.rank_eq π k) =
      B.τ.cartan j k := ggLang_cartan_perm B
  have hρ : ∀ γ, IsRoot B.τ γ →
      B.setup.ρ γ = B.ε • latPerm (ggLangPerm B.rank_eq π) γ :=
    fun γ hγ => ggLang_rho_eq_perm B hγ
  set Smat : Matrix (Fin B.τ.rank) (Fin B.τ.rank) ℤ :=
    fun i j => S (Fin.cast B.rank_eq.symm i) (Fin.cast B.rank_eq.symm j) with hSmatdef
  obtain ⟨k, hk, hSmat0⟩ := asmA_smat B
  rw [← hSmatdef] at hSmat0
  have hSperm : ∀ i j,
      Smat (ggLangPerm B.rank_eq π i) (ggLangPerm B.rank_eq π j) = Smat i j := by
    intro i j
    change S (Fin.cast B.rank_eq.symm (ggLangPerm B.rank_eq π i))
        (Fin.cast B.rank_eq.symm (ggLangPerm B.rank_eq π j)) =
      S (Fin.cast B.rank_eq.symm i) (Fin.cast B.rank_eq.symm j)
    have h1 : Fin.cast B.rank_eq.symm (ggLangPerm B.rank_eq π i) =
        π (Fin.cast B.rank_eq.symm i) := by
      rw [ggLangPerm_apply]
      simp
    have h2 : Fin.cast B.rank_eq.symm (ggLangPerm B.rank_eq π j) =
        π (Fin.cast B.rank_eq.symm j) := by
      rw [ggLangPerm_apply]
      simp
    rw [h1, h2]
    exact ggLang_gram_perm B _ _
  have hgen : ∀ α ∈ T,
      rootDiagUnit B.τ (fun j => B.ζ ^ latOrbitSumZ Smat (ggLangPerm B.rank_eq π) α j) ∈
        rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i := by
    intro α hαT
    have hα : IsRoot B.τ α := LangRat.isRoot_of_mem_rationalRoots B.setup i hαT
    have hcorα : latCorootZ Smat α = fun m => corootPair α (Pi.single m 1) := by
      rw [hSmat0]
      exact latCorootZ_smul_symmetrizedCartan_of_ne B.τ hk.ne' hα
    by_cases hfix : latPerm (ggLangPerm B.rank_eq π) α = α
    · have hsum : latOrbitSumZ Smat (ggLangPerm B.rank_eq π) α = latCorootZ Smat α := by
        funext j
        simp [latOrbitSumZ, hfix]
      rw [hsum, hcorα]
      have hρα : B.setup.ρ α = B.ε • α := by
        have h := hρ α hα
        rwa [hfix] at h
      have hραOr : B.setup.ρ α = α ∨ B.setup.ρ α = -α := by
        rcases B.ε_cases with hε | hε
        · left
          rw [hρα, hε, one_smul]
        · right
          rw [hρα, hε, neg_one_smul]
      have hT : rootDiagUnit B.τ (fun j => B.ζ ^ corootPair α (Pi.single j 1)) ∈
          B.setup.D.torus :=
        LangRat.langCorootFactor_mem_torus B.setup B.tag_five B.ε_cases hpε hζ hα hρα
      exact LangRat.langCorootFactor B.setup B.tag_five B.q_eq hAlg hp hp2 i hαT hραOr hζ hT
    · have hπαroot : IsRoot B.τ (latPerm (ggLangPerm B.rank_eq π) α) := by
        have h := hρ α hα
        rcases B.ε_cases with hε | hε
        · rw [hε, one_smul] at h
          rw [← h]
          exact (B.setup.frob.isRoot_iff α).2 hα
        · rw [hε, neg_one_smul] at h
          have h2 : latPerm (ggLangPerm B.rank_eq π) α = -(B.setup.ρ α) :=
            (neg_eq_iff_eq_neg).mp h.symm
          rw [h2]
          exact IsRoot.neg ((B.setup.frob.isRoot_iff α).2 hα)
      have hcorπα : latCorootZ Smat (latPerm (ggLangPerm B.rank_eq π) α) =
          fun m => corootPair (latPerm (ggLangPerm B.rank_eq π) α) (Pi.single m 1) := by
        rw [hSmat0]
        exact latCorootZ_smul_symmetrizedCartan_of_ne B.τ hk.ne' hπαroot
      have hsum : latOrbitSumZ Smat (ggLangPerm B.rank_eq π) α =
          fun j => corootPair α (Pi.single j 1) +
            corootPair (latPerm (ggLangPerm B.rank_eq π) α) (Pi.single j 1) := by
        funext j
        simp only [latOrbitSumZ, if_neg hfix, Pi.add_apply, hcorα, hcorπα]
      have hfun : (fun j => B.ζ ^ latOrbitSumZ Smat (ggLangPerm B.rank_eq π) α j) =
          (fun j => B.ζ ^ corootPair α (Pi.single j 1) *
            B.ζ ^ corootPair (latPerm (ggLangPerm B.rank_eq π) α) (Pi.single j 1)) := by
        funext j
        rw [congrFun hsum j]
        exact zpow_add B.ζ _ _
      rw [hfun]
      have hT : rootDiagUnit B.τ (fun j => B.ζ ^ corootPair α (Pi.single j 1) *
          B.ζ ^ corootPair (latPerm (ggLangPerm B.rank_eq π) α) (Pi.single j 1)) ∈
          B.setup.D.torus :=
        LangRat.langCorootPairFactor_mem_torus B.setup B.tag_five (ggLangPerm B.rank_eq π) hπ'
          B.ε_cases hρ hpε hζ hα hfix
      exact LangRat.langCorootPairFactor B.setup B.tag_five B.q_eq hAlg hp hp2
        (ggLangPerm B.rank_eq π) hπ' B.ε_cases hρ i hαT hfix hζ hζ hT
  have hR : rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i ≤ B.setup.Γ :=
    (Subgroup.commutator_le_self _).trans inf_le_right
  refine ⟨O, (isCompOrbit_iff_rationalRoots B hp b O).2 ⟨i, rfl⟩, ?_, ?_⟩
  · intro b'
    exact ggLang_mem_centralizer_rationalComponent_iff B hp hp2 hZ i hq b'
  · intro b' hb'
    have hg := asmA_latEigenCoroot_reidx B.rank_eq S π T (Multiplicative.toAdd (coord b')) hb'
    have hmem := LangRat.rootDiagUnit_latEigenCoroot_mem_rationalComponent B.setup
      (ggLangPerm B.rank_eq π) T hζ hp2 hSperm i hgen hg
    have haeq : B.a b' =
        fun j => B.ζ ^ (Multiplicative.toAdd (coord b') (Fin.cast B.rank_eq.symm j)).val := by
      funext j
      exact B.a_coord b' j
    refine ggPsi_mem_of_rootDiagUnit_mem B hR b' ?_
    simpa [haeq] using hmem

end AssemblyA

end CFSG.StandardType
