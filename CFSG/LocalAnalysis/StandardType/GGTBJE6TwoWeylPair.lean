module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6TwoBase
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair

public section

namespace CFSG.StandardType.E6Two

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Lattice

open Matrix
open scoped MatrixGroups commutatorElement


theorem pairWeyl_mem_rationalComponent
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {k' : Type} [Field k'] [Finite k'] [Algebra k' L] [IsAlgClosure k' L]
    {n : ℕ} (hn : 1 ≤ n) (hq : S.D.q = 2 ^ n)
    (hρ : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = -permLattice TwistTag.E6.perm γ)
    {a : Fin Tag.E6.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ rationalRoots S.ρ (rootCharHom a) i)
    (hne : permLattice TwistTag.E6.perm β ≠ β) :
    rootSL2 Tag.E6 L β WSL * rootSL2 Tag.E6 L (permLattice TwistTag.E6.perm β) WSL ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  classical
  have hβr : IsRoot Tag.E6 β := LangRat.isRoot_of_mem_rationalRoots S i hβ
  have hρβr : IsRoot Tag.E6 (permLattice TwistTag.E6.perm β) :=
    hβr.permLattice (TwistTag.cartan_perm TwistTag.E6)
  obtain ⟨hρρ, h0, hsum, hdiff⟩ := LangRat.rho_orthogonal_of_latPerm_ne S
    (Or.inr (Or.inl rfl)) TwistTag.E6.perm (TwistTag.cartan_perm TwistTag.E6) (Or.inr rfl)
    (fun γ hγ => by
      rw [hρ γ hγ, neg_one_smul]
      congr 1) hβr hne
  have hcomm : ∀ Y Z : SL(2, L),
      Commute (rootSL2 Tag.E6 L β Y) (rootSL2 Tag.E6 L (S.ρ β) Z) := fun Y Z =>
    exceptional_Lang_strongly_orthogonal_root_rank_one_commutation Tag.E6 L hβr
      ((S.frob.isRoot_iff β).2 hβr) h0 hsum hdiff _
      (MonoidHom.mem_range.2 ⟨Y, rfl⟩) _ (MonoidHom.mem_range.2 ⟨Z, rfl⟩)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : SL(2, L) × SL(2, L) →* ModGL Tag.E6 L,
      ∀ Y Z, Ψ (Y, Z) = rootSL2 Tag.E6 L β Y * rootSL2 Tag.E6 L (S.ρ β) Z :=
    ⟨MonoidHom.noncommCoprod (rootSL2 Tag.E6 L β) (rootSL2 Tag.E6 L (S.ρ β)) hcomm,
      fun Y Z => rfl⟩
  let Fr : L →+* L := iterateFrobenius L 2 n
  have hFr : ∀ c, Fr c = c ^ S.D.q := fun c => by
    rw [hq]
    show iterateFrobenius L 2 n c = c ^ 2 ^ n
    rw [iterateFrobenius_def]
  let Fr2 : L →+* L := Fr.comp Fr
  have hFr2 : ∀ c, Fr2 c = c ^ (2 : ℕ) ^ (2 * n) := by
    intro c
    change Fr (Fr c) = c ^ 2 ^ (2 * n)
    rw [hFr, hFr, hq]
    show (c ^ 2 ^ n) ^ 2 ^ n = c ^ 2 ^ (2 * n)
    rw [← pow_mul, show 2 * n = n + n by ring, pow_add]
  let F' : SL(2, L) →* SL(2, L) :=
    (CFSG.RankThree.Classical2.conjSLn (1 : GL (Fin 2) L)).comp
      (Matrix.SpecialLinearGroup.map Fr2)
  let X := F'.eqLocus (MonoidHom.id _)
  have hconjF : ∀ z : SL(2, L), F' z = Matrix.SpecialLinearGroup.map Fr2 z := fun z => by
    change CFSG.RankThree.Classical2.conjSLn (1 : GL (Fin 2) L)
      (Matrix.SpecialLinearGroup.map Fr2 z) = Matrix.SpecialLinearGroup.map Fr2 z
    rw [CFSG.RankThree.Classical2.conjSLn_one]
  have h42n : 4 ≤ 2 ^ (2 * n) :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨-, hQ⟩ := CFSG.RankThree.Classical2.isQuasisimple_eqLocus_conjSLn_frobenius_split
    (k' := k') (Ω := L) (ℓ := 2) (f := 2 * n) (n := 2) Nat.prime_two (by omega) le_rfl
    (Or.inr h42n) Fr2 hFr2 (1 : GL (Fin 2) L)
  let ψ : X →* ModGL Tag.E6 L := Ψ.comp
    ((X.subtype).prod ((Matrix.SpecialLinearGroup.map Fr).comp X.subtype))
  have hψapply : ∀ y : X, ψ y = rootSL2 Tag.E6 L β (y : SL(2, L)) *
      rootSL2 Tag.E6 L (S.ρ β)
        (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))) := fun y => by
    change Ψ ((y : SL(2, L)), Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))) = _
    rw [hΨ]
  have hmapfix2 : ∀ y : X,
      Matrix.SpecialLinearGroup.map Fr2 (y : SL(2, L)) = (y : SL(2, L)) := by
    intro y
    have hy := y.2
    change F' (y : SL(2, L)) = (y : SL(2, L)) at hy
    rwa [hconjF] at hy
  have hmapFrFr : ∀ y : SL(2, L), Matrix.SpecialLinearGroup.map Fr2 y =
      Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr y) := by
    intro y
    ext i j
    rfl
  have hmapfixFr : ∀ y : X,
      Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))) =
        (y : SL(2, L)) := fun y => (hmapFrFr (y : SL(2, L))).symm.trans (hmapfix2 y)
  have hψS : ∀ y, ψ y ∈ rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) := by
    intro y
    rw [hψapply]
    exact mul_mem (LangRat.rootSL2_mem_rootSpan_of_mem_rationalRoots S i hβ _)
      (LangRat.rootSL2_mem_rootSpan_of_mem_rationalRoots S i
        (show S.ρ β ∈ rationalRoots S.ρ (rootCharHom a) i from by
          obtain ⟨k, δ, hδ, hk⟩ := hβ
          exact ⟨k + 1, δ, hδ, by rw [hk, Function.iterate_succ_apply']⟩) _)
  have hψA : ∀ y, ψ y ∈ adjointGroup Tag.E6 L :=
    fun y => rootSpan_le_adjointGroup L _ (hψS y)
  have hψF : ∀ y, S.D.step (ψ y) = ψ ((MonoidHom.id X) y) := by
    intro y
    have h1 : ψ ((MonoidHom.id X) y) = rootSL2 Tag.E6 L β (y : SL(2, L)) *
        rootSL2 Tag.E6 L (S.ρ β)
          (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))) := by
      rw [MonoidHom.id_apply]; exact hψapply y
    rw [hψapply y, h1]
    rw [map_mul, step_rootSL2_of_charTwo S hβr Fr hFr (y : SL(2, L)),
      step_rootSL2_of_charTwo S ((S.frob.isRoot_iff β).2 hβr) Fr hFr
        (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L))), hρρ, hmapfixFr y]
    exact (hcomm (y : SL(2, L)) (Matrix.SpecialLinearGroup.map Fr (y : SL(2, L)))).eq.symm
  haveI hperf : Group.IsPerfect X := hQ.1
  have hKperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have hres := map_fix_le_rationalComponent S i ψ hψS hψA (MonoidHom.id X) hψF ⊤
    (fun _ _ => rfl) hKperf
  have hWfix : Matrix.SpecialLinearGroup.map Fr WSL = WSL := by
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      coe_WSL]
    fin_cases i <;> fin_cases j <;> simp
  have hWX : (WSL : SL(2, L)) ∈ X := by
    change F' WSL = WSL
    rw [hconjF, hmapFrFr, hWfix, hWfix]
  have hmem := hres ⟨WSL, hWX⟩ (Subgroup.mem_top _)
  rw [hψapply, hWfix] at hmem
  have hconv : rootSL2 Tag.E6 L (S.ρ β) WSL =
      rootSL2 Tag.E6 L (permLattice TwistTag.E6.perm β) WSL := by
    rw [hρ β hβr]
    exact rootSL2_neg_WSL_of_charTwo hρβr
  rw [hconv] at hmem
  exact hmem

end CFSG.StandardType.E6Two

end
