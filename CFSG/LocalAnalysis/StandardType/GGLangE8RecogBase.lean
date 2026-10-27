module

public import CFSG.LocalAnalysis.StandardType.GGTBJMaxRankRow
public import CFSG.LocalAnalysis.StandardType.GGLangE8Prime
public import CFSG.LocalAnalysis.StandardType.GGLangDictCentralizer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms

public section

namespace CFSG.StandardType

section Recognition

open CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable abbrev recogaR
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (b : Bs)
    (i : KernelComponent (rootCharHom (B.a b))) : Subgroup (ModGL B.τ L) :=
  rationalComponent B.setup.ρ B.setup.Γ (rootCharHom (B.a b)) i

theorem recoga_tau_eq_E8
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    : B.τ = .E8 := by
  have h8 : (ggU (absTag .E8) 6 f).D.rank = 8 := rfl
  have hr : B.τ.rank = 8 := B.rank_eq ▸ h8
  rcases B.tag_five with h | h | h | h
  · rw [h] at hr; exact absurd hr (by decide)
  · rw [h] at hr; exact absurd hr (by decide)
  · rw [h] at hr; exact absurd hr (by decide)
  · exact h

theorem recoga_charP
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (_hf : 1 ≤ f) : CharP L 2 :=
  CFSG.StandardType.LangRat.charP_two_of_langSetup_q_eq_two_pow B.setup (f := f) B.q_eq

theorem recoga_rho_smul
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (hτ : B.τ = .E8) {γ : Fin B.τ.rank → ℤ} (hγ : IsRoot B.τ γ) :
    B.setup.ρ γ = B.ε • γ := by
  have hπ : π = 1 := by
    have key : ∀ (τ : Tag) (_ : τ = .E8) (h : (ggU (absTag .E8) 6 f).D.rank = τ.rank),
        (∀ j k, τ.cartan (Fin.cast h (π j)) (Fin.cast h (π k)) =
          τ.cartan (Fin.cast h j) (Fin.cast h k)) → π = 1 := by
      intro τ hτ' h hh
      subst hτ'
      exact perm_eq_one_of_cartan_E8 π fun i j => hh i j
    exact key B.τ hτ B.rank_eq B.pi_diag
  have e1 : ggLangReidx B.rank_eq (ggLangReidx B.rank_eq.symm γ) = γ := by
    funext j
    simp [ggLangReidx]
  have hv : ggLangReidx B.rank_eq.symm γ ∈ (ggU (absTag .E8) 6 f).D.roots := by
    rw [B.roots_iff, e1]
    exact hγ
  have h := B.rho_eq _ hv
  rw [e1] at h
  have e2 : ∀ v : Fin (ggU (absTag .E8) 6 f).D.rank → ℤ, latPerm π v = v := by
    intro v
    rw [hπ]
    funext j
    rfl
  rw [h, e2, e1]

theorem recoga_orbitLength_eq_one
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (hτ : B.τ = .E8) (b : Bs)
    (i : KernelComponent (rootCharHom (B.a b))) :
    componentOrbitLength B.setup.ρ (componentRoots (rootCharHom (B.a b)) i) = 1 := by
  have hΨ : IsRootComponent (componentRoots (rootCharHom (B.a b)) i) :=
    isRootComponent_componentRoots (χ := rootCharHom (B.a b)) i
  have himg : (B.setup.ρ : (Fin B.τ.rank → ℤ) → _)^[1] ''
      componentRoots (rootCharHom (B.a b)) i = componentRoots (rootCharHom (B.a b)) i := by
    rw [Function.iterate_one]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [recoga_rho_smul B hτ (hΨ.isRoot y hy)]
      rcases B.ε_cases with h | h
      · rw [h, one_smul]; exact hy
      · rw [h, neg_one_smul]; exact hΨ.neg_mem y hy
    · intro hx
      have hy : B.ε • x ∈ componentRoots (rootCharHom (B.a b)) i := by
        rcases B.ε_cases with h | h
        · rw [h, one_smul]; exact hx
        · rw [h, neg_one_smul]; exact hΨ.neg_mem x hx
      refine ⟨B.ε • x, hy, ?_⟩
      rw [recoga_rho_smul B hτ (hΨ.isRoot _ hy), smul_smul]
      rcases B.ε_cases with h | h <;> simp [h]
  have hmem : 1 ∈ {s : ℕ | 0 < s ∧ (B.setup.ρ : (Fin B.τ.rank → ℤ) → _)^[s] ''
      componentRoots (rootCharHom (B.a b)) i = componentRoots (rootCharHom (B.a b)) i} :=
    ⟨Nat.one_pos, himg⟩
  unfold componentOrbitLength
  exact le_antisymm (Nat.sInf_le hmem) (Nat.sInf_mem ⟨1, hmem⟩).1

theorem recoga_rootDiagUnit_pow
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (b : Bs) : rootDiagUnit B.τ (B.a b) ^ p = 1 :=
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall
    fun j => ggLang_a_pow_eq_one B b j

theorem recoga_rootDiagUnit_ne_one
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (_hp : p.Prime) {b : Bs} (hb : b ≠ 1) : rootDiagUnit B.τ (B.a b) ≠ 1 :=
  rootDiagUnit_ne_one_of_ne_one B hb

theorem recoga_natCast_ne_zero
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (_hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) : (p : L) ≠ 0 :=
  ggLang_natCast_ne_zero B hp hp2

end Recognition

end CFSG.StandardType

end
