module

public import CFSG.LocalAnalysis.StandardType.GGLangDictOrbits
public import CFSG.LocalAnalysis.StandardType.GGLangDictTransport
public import CFSG.LocalAnalysis.StandardType.GGLangFamily
public import CFSG.LocalAnalysis.StandardType.GGLangReidx
public import CFSG.LocalAnalysis.StandardType.GGLangDictCentralizer

public section

namespace CFSG.StandardType

section AssemblyAU

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem asmAU_isRoot_of_mem_familyOrbit
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀)
    {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (i : KernelComponent (Pi.monoidHom fun u : ι => rootCharHom (a u)))
    {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ {γ : Fin τ.rank → ℤ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ),
      δ ∈ componentRoots (Pi.monoidHom fun u : ι => rootCharHom (a u)) i ∧
        γ = (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ}) :
    IsRoot τ γ := by
  obtain ⟨k, δ, hδ, rfl⟩ := hγ
  induction k with
  | zero => exact hδ.1.1
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (S.frob.isRoot_iff _).2 ih

theorem ggClauseAU_of_langData
    {L : Type} [Field L] [IsAlgClosed L] {t : StatedLieTag} {n f p : ℕ}
    {Bs : Subgroup (GGAutU t n f)}
    {S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag t) 6 f).D.rank → ZMod p)}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (B : GGLangData L t n f p Bs S π coord) :
    GGClauseAU t n f p (ggPsiU t n f) Bs S π coord := by
  intro U hU _ K hK
  let Us : Set Bs := {u | (u : GGAutU t n f) ∈ U}
  have hUsval : (Subtype.val '' Us : Set (GGAutU t n f)) = (U : Set (GGAutU t n f)) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      exact ⟨⟨x, hU hx⟩, hx, rfl⟩
  have hK' : CFSG.Assembly.IsComponentOf K ((ggPsiU t n f).range ⊓
      Subgroup.centralizer (Subtype.val '' Us : Set (GGAutU t n f))) := by
    rw [hUsval]
    exact hK
  obtain ⟨R, hR, hEq⟩ := (isComponentOf_psi_range_centralizer_family_iff B Us K).1 hK'
  have hRΓ : R ≤ B.setup.Γ := hR.1.trans inf_le_left
  have hpL : (p : L) ≠ 0 := ggLang_natCast_ne_zero B hp hp2
  obtain ⟨i, hRi⟩ := LangRat.langFamilyComponentsInRootSpan B.τ L B.p₀ p B.setup B.tag_five hp hp2
    hpL (↥Us) (fun u : Us => B.a u.1) (fun u => B.a_torus u.1)
    (fun u j => ggLang_a_pow_eq_one B u.1 j) R hR
  let Tfam : Set (Fin B.τ.rank → ℤ) := {γ : Fin B.τ.rank → ℤ | ∃ (k : ℕ) (δ : Fin B.τ.rank → ℤ),
      δ ∈ componentRoots (Pi.monoidHom fun u : Us => rootCharHom (B.a u.1)) i ∧
        γ = (B.setup.ρ : (Fin B.τ.rank → ℤ) → (Fin B.τ.rank → ℤ))^[k] δ}
  have hRrootSpan : R ≤ rootSpan B.τ L Tfam := hRi
  let O : Set (Fin (ggU (absTag t) 6 f).D.rank → ℤ) := ggLangReidx B.rank_eq ⁻¹' Tfam
  refine ⟨O, ?_, ?_⟩
  · exact (isCompOrbit_iff_rationalRoots_family B hp Us O).2 ⟨i, rfl⟩
  · intro b' hb'
    have hsub : Tfam ⊆ rootCharKernel (B.a b') := by
      intro γ hγ
      refine ⟨asmAU_isRoot_of_mem_familyOrbit B.setup (fun u : Us => B.a u.1) i hγ, ?_⟩
      obtain ⟨k, δ, hδ, rfl⟩ := hγ
      have hsymm : ggLangReidx B.rank_eq (ggLangReidx B.rank_eq.symm ((B.setup.ρ)^[k] δ))
          = (B.setup.ρ)^[k] δ :=
        (ggLangReidxEquiv B.rank_eq).apply_symm_apply ((B.setup.ρ)^[k] δ)
      have hαmem : ggLangReidx B.rank_eq.symm ((B.setup.ρ)^[k] δ) ∈ O := by
        refine ⟨k, δ, hδ, hsymm⟩
      have hzero := hb' _ hαmem
      have h1 := (latChar_eq_zero_iff_rootChar_eq_one B hp b'
        (ggLangReidx B.rank_eq.symm ((B.setup.ρ)^[k] δ))).1 hzero
      rwa [hsymm] at h1
    have hRcent : R ≤ Subgroup.centralizer {rootDiagUnit B.τ (B.a b')} :=
      hRrootSpan.trans (rootSpan_le_centralizer (B.a b') hsub)
    have hmem := (ggPsi_mem_centralizer_iff B hRΓ b').2 hRcent
    rw [hEq]
    exact hmem

end AssemblyAU

end CFSG.StandardType
