module

public import CFSG.LocalAnalysis.StandardType.GGLangDictOrbits
public import CFSG.LocalAnalysis.StandardType.GGLangDictTransport
public import CFSG.LocalAnalysis.StandardType.GGLangAlgebraic
public import CFSG.LocalAnalysis.StandardType.GGLangDetects
public import CFSG.LocalAnalysis.StandardType.GGLangPSLTwo
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
public import CFSG.LocalAnalysis.StandardType.GGLangReidx
public import CFSG.LocalAnalysis.StandardType.GGLangDictCentralizer
public import CFSG.LocalAnalysis.StandardType.GGLangNormalizer
public import CFSG.LocalAnalysis.StandardType.GGLangLatSolv

public section

namespace CFSG.StandardType

section AssemblyComp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem asmComp_not_isSolvable_of_isQuasisimple {C : Type*} [Group C]
    (hQ : CFSG.IsQuasisimple C) : ¬ Group.IsSolvable C := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  haveI : IsSimpleGroup (C ⧸ Subgroup.center C) := hsimple
  have : Nontrivial C := (QuotientGroup.mk_surjective (s := Subgroup.center C)).nontrivial
  exact Group.IsPerfect.not_isSolvable C

private theorem asmComp_a_eq_corootPair
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (B : GGLangData L t n f p Bs S π coord) (hp : p.Prime)
    {α : Fin (ggU (absTag t) 6 f).D.rank → ℤ}
    (b' : Bs)
    (hb' : Multiplicative.toAdd (coord b') = corootCoord p S α) :
    B.a b' = fun j => B.ζ ^ corootPair (ggLangReidx B.rank_eq α) (Pi.single j 1) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ : B.ζ ^ p = 1 := by
    have h := pow_orderOf_eq_one B.ζ
    rwa [B.ζ_order] at h
  have hval : ∀ n : ℤ, B.ζ ^ ((n : ZMod p).val) = B.ζ ^ n := by
    intro n
    rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, ZMod.val_intCast]
    exact (Int.mod_modEq n (p : ℤ)).of_dvd (by exact_mod_cast orderOf_dvd_of_pow_eq_one hζ)
  obtain ⟨k, hk, hg⟩ := B.gram_eq
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
  have hcc : ∀ j : Fin B.τ.rank,
      corootCoord p S α (Fin.cast B.rank_eq.symm j) =
        ((2 * iform (ggLangReidx B.rank_eq α) (Pi.single j 1) /
          iform (ggLangReidx B.rank_eq α) (ggLangReidx B.rank_eq α) : ℤ) : ZMod p) := by
    intro j
    have hjc : Fin.cast B.rank_eq (Fin.cast B.rank_eq.symm j) = j := Fin.ext rfl
    simp only [corootCoord]
    rw [hg (Pi.single (Fin.cast B.rank_eq.symm j) 1) α,
      hg α α, hre, hjc]
    rw [show 2 * (k * iform (Pi.single j 1) (ggLangReidx B.rank_eq α)) =
      k * (2 * iform (Pi.single j 1) (ggLangReidx B.rank_eq α)) by ring]
    rw [Int.mul_ediv_mul_of_pos _ _ hk]
    rw [iform_comm (Pi.single j 1) (ggLangReidx B.rank_eq α)]
  funext j
  rw [B.a_coord, hb', hcc, hval]
  rfl

theorem ggClauseComp_of_langData
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    [Algebra (ZMod 2) L] [Algebra.IsAlgebraic (ZMod 2) L]
    (hp : p.Prime) (hp2 : p ≠ 2)
    (B : GGLangData L t n f p Bs S π coord)
    (hZ : LangRat.LangRatCentralizerDetectsP) :
    GGClauseComp t n f p (ggPsiU t n f) Bs S π coord := by
  classical
  have hτG2 : B.τ ≠ .G2 := by
    rcases B.tag_five with h | h | h | h <;> rw [h] <;> decide
  have hpL : (p : L) ≠ 0 := ggLang_natCast_ne_zero B hp hp2
  have hπ' : ∀ j k : Fin B.τ.rank,
      B.τ.cartan (ggLangPerm B.rank_eq π j) (ggLangPerm B.rank_eq π k) = B.τ.cartan j k :=
    ggLang_cartan_perm B
  have hρ : ∀ γ : Fin B.τ.rank → ℤ, IsRoot B.τ γ →
      B.setup.ρ γ = B.ε • latPerm (ggLangPerm B.rank_eq π) γ :=
    fun γ hγ => ggLang_rho_eq_perm B hγ
  have hpε : (p : ℤ) ∣ ((B.setup.D.q : ℕ) : ℤ) - B.ε := by
    rw [B.q_eq]
    push_cast
    exact B.p_dvd
  have hζ : B.ζ ^ p = 1 := by
    have h := pow_orderOf_eq_one B.ζ
    rwa [B.ζ_order] at h
  have hap : ∀ b : Bs, ∀ j : Fin B.τ.rank, B.a b j ^ p = 1 :=
    fun b j => ggLang_a_pow_eq_one B b j
  have hAlg : B.setup.IsAlgebraic := langSetup_isAlgebraic_of_zmod_two B.setup B.q_eq
  unfold GGClauseComp
  constructor
  ·
    intro b hb O hO hnot
    obtain ⟨i, rfl⟩ := (isCompOrbit_iff_rationalRoots B hp b O).1 hO
    rw [ggLang_latSolv_preimage B.rank_eq (f = 1) π
      (rationalRoots B.setup.ρ (rootCharHom (B.a b)) i)] at hnot
    have hnot' : ¬ LangRat.LangSmallSolv B.setup.D.q B.setup.ρ
        (rootCharHom (B.a b)) i := by
      intro hs
      exact hnot (LangRat.latSolv_of_langSmallSolv B.setup B.q_eq hp hpL
        (ggLangPerm B.rank_eq π) B.ε B.ε_cases hpε hρ (B.a_torus b) (hap b) i hs)
    have hq : CFSG.IsQuasisimple
        ↥(rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i) :=
      LangRat.isQuasisimple_rationalComponent_of_not_langSmallSolv B.setup hτG2 hp hpL
        (B.a_torus b) (hap b) (rootDiagUnit_ne_one_of_ne_one B hb) i hnot'
    refine ⟨((rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i).comap B.ι).map
      (ggPsiBar t n f), ?_, ?_⟩
    · exact ggLang_isComponentOf_rationalComponent B i hq
    · intro b'
      exact ggLang_mem_centralizer_rationalComponent_iff B hp hp2 hZ i hq b'
  ·
    intro b hb L hL
    obtain ⟨i, hq, rfl⟩ := ggLang_exists_rationalComponent_of_isComponentOf B hp hp2 hb hL
    have hRb : rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i ≤ B.setup.Γ :=
      (Subgroup.commutator_le_self
        (rationalSpan B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i)).trans inf_le_right
    refine ⟨ggLangReidx B.rank_eq ⁻¹'
        rationalRoots B.setup.ρ (rootCharHom (B.a b)) i,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (isCompOrbit_iff_rationalRoots B hp b _).2 ⟨i, rfl⟩
    · intro hs
      rw [ggLang_latSolv_preimage B.rank_eq (f = 1) π
        (rationalRoots B.setup.ρ (rootCharHom (B.a b)) i)] at hs
      have hsolv : Group.IsSolvable
          ↥(rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i) :=
        LangRat.isSolvable_rationalComponent_of_latSolv B.setup B.q_eq hp hpL
          (ggLangPerm B.rank_eq π) B.ε B.ε_cases hpε hρ (B.a_torus b) (hap b) i hs
      exact asmComp_not_isSolvable_of_isQuasisimple hq hsolv
    · intro b'
      exact ggLang_mem_centralizer_rationalComponent_iff B hp hp2 hZ i hq b'
    · intro x hx
      exact ggPsi_mem_normalizer_of_conj B ⟨x, hx⟩
        (LangRat.conj_rationalComponent_eq B.setup (B.a b) (B.a ⟨x, hx⟩)
          (B.a_torus ⟨x, hx⟩) i)
    ·
      intro α hα hfix b' hb'
      set α' : Fin B.τ.rank → ℤ := ggLangReidx B.rank_eq α with hα'def
      have hα' : α' ∈ rationalRoots B.setup.ρ (rootCharHom (B.a b)) i := by
        rw [hα'def]
        exact hα
      have hroot : IsRoot B.τ α' := LangRat.isRoot_of_mem_rationalRoots B.setup i hα'
      have hfix' : latPerm (ggLangPerm B.rank_eq π) α' = α' := by
        rw [hα'def, ← ggLang_reidx_latPerm B.rank_eq π α, hfix]
      have hρα : B.setup.ρ α' = α' ∨ B.setup.ρ α' = -α' := by
        have h := hρ α' hroot
        rw [hfix'] at h
        rcases B.ε_cases with hε | hε
        · left
          rw [h, hε, one_smul]
        · right
          rw [h, hε]
          simp
      have hcoord : B.a b' =
          fun j => B.ζ ^ corootPair α' (Pi.single j 1) :=
        asmComp_a_eq_corootPair B hp b' hb'
      have hT : rootDiagUnit B.τ (fun j => B.ζ ^ corootPair α' (Pi.single j 1)) ∈
          B.setup.D.torus := by
        rw [← hcoord]
        exact B.a_torus b'
      have hmem : rootDiagUnit B.τ (fun j => B.ζ ^ corootPair α' (Pi.single j 1)) ∈
          rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i :=
        LangRat.langCorootFactor B.setup B.tag_five B.q_eq hAlg hp hp2 i hα' hρα hζ hT
      exact ggPsi_mem_of_rootDiagUnit_mem B hRb b' (by simpa [← hcoord] using hmem)
    ·
      by_cases hEq : rationalRoots B.setup.ρ (rootCharHom (B.a b)) i =
          componentRoots (rootCharHom (B.a b)) i
      · left
        rw [hEq]
        exact ggLang_isSingleComp_componentRoots B hp b i
      · right
        obtain ⟨k, hmodel⟩ := LangRat.langPSLOfLengthTwo B.τ L B.p₀ p f B.setup
          B.tag_five hp hp2 hpL B.q_eq (ggLangPerm B.rank_eq π) hπ' B.ε B.ε_cases hρ
          (B.a b) (B.a_torus b) (hap b) (rootDiagUnit_ne_one_of_ne_one B hb) i hq hEq
        obtain ⟨e⟩ := ggPsiImage_mulEquiv B hRb
        exact ⟨k, CFSG.Blueprint.LieModel.of_mulEquiv
          (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hmodel⟩

end AssemblyComp

end CFSG.StandardType
