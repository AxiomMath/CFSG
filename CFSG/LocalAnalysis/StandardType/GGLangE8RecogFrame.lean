module

public import CFSG.LocalAnalysis.StandardType.GGLangE8RecogBase
public import CFSG.LocalAnalysis.StandardType.GGK0LQRecA

public section

namespace CFSG.StandardType

section Recognition

open CFSG.Assembly
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.Open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem recogf_main
    {τ : Tag} (hτ : τ = .E8) {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hρ : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → S.ρ γ = ε • γ)
    (i : KernelComponent (rootCharHom a))
    (hm1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hrank8 : compRank (componentRoots (rootCharHom a) i) = 8)
    (hn72 : (componentRoots (rootCharHom a) i).ncard = 72) :
    ∃ Bm : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ,
      Bm.transpose * Tag.E8.cartan * Bm = CartanMatrix.A 8 ∧
      (∀ j, rootChar (fun i : Fin Tag.E8.rank => a (Fin.cast (by rw [hτ]) i))
        (fun i => Bm i j) = 1) ∧
      (twistKind S.ρ (rootCharHom a) i = .inner → ε = 1) ∧
      (twistKind S.ρ (rootCharHom a) i = .suN → ε = -1) := by
  subst hτ
  classical
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1) := by rw [hrank8, hn72]
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_frame_of_typeA_tag_T_of_prime
      CFSG.HardMathSupport.Timmesfeld.CrossChar.g2LongA2Frame_proved S hp hpL hTp i
      (by omega) hncard
  have hfr := CFSG.LocalAnalysis.GLTheoremA.kd147c_frameRoots_ncard hψ hκ hnorm
  have hν9 : ν = 9 := by
    have h72 : ν * (ν - 1) = 72 := by rw [← hfr, ← hΨ, hn72]
    have hle : ν ≤ 9 := by
      by_contra h
      push Not at h
      have : 10 * 9 ≤ ν * (ν - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases ν <;> omega
  subst hν9
  have hκ1 : κ = 1 := by
    have h := hnorm 0 1 (by decide)
    have h2 := CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two
      (Or.inr (Or.inr (Or.inr rfl))) (hψ.isRoot 0 1 (by decide))
    omega
  subst hκ1
  have hrho1 : ∀ x y : Fin 9, x ≠ y →
      (S.ρ : (Fin Tag.E8.rank → ℤ) → _) (σ x y) = ε • σ x y :=
    fun x y hxy => hρ _ (hψ.isRoot x y hxy)
  have h8 : Tag.E8.rank = 8 := rfl
  have hlt : ∀ j : Fin Tag.E8.rank, j.val < 8 := fun j => by have := j.isLt; omega
  let u : Fin Tag.E8.rank → Fin 9 := fun j => ⟨j.val, by have := hlt j; omega⟩
  let v : Fin Tag.E8.rank → Fin 9 := fun j => ⟨j.val + 1, by have := hlt j; omega⟩
  have hA0 : ∀ j k : Fin 8, CFSG.HardMathSupport.Timmesfeld.CrossChar.framePairForm
      j.castSucc j.succ k.castSucc k.succ = CartanMatrix.A 8 j k := by
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [CFSG.HardMathSupport.Timmesfeld.CrossChar.framePairForm, CartanMatrix.A, Fin.ext_iff]
  have hA : ∀ j k : Fin Tag.E8.rank, CFSG.HardMathSupport.Timmesfeld.CrossChar.framePairForm
      (u j) (v j) (u k) (v k) = CartanMatrix.A 8 j k := fun j k => hA0 j k
  let α : Fin Tag.E8.rank → (Fin Tag.E8.rank → ℤ) := fun j => σ (u j) (v j)
  refine ⟨Matrix.of fun i j => α j i, ?_, ?_, ?_, ?_⟩
  · ext j k
    have hsym := CFSG.LieType.Chevalley.symmetrizedCartan_eq_of_E (τ := Tag.E8)
      (Or.inr (Or.inr rfl))
    have h2 : (Matrix.transpose (Matrix.of fun i j => α j i) * Tag.E8.cartan *
        (Matrix.of fun i j => α j i)) j k = iform (α j) (α k) := by
      rw [← dotProduct_mulVec_eq_iform, hsym]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
        Finset.sum_mul, Finset.mul_sum, mul_assoc, Matrix.of_apply]
      exact Finset.sum_comm
    rw [h2]
    show iform (σ (u j) (v j)) (σ (u k) (v k)) = _
    rw [hψ.iform_eq hnorm, one_mul]
    exact hA j k
  · intro j
    have hne : u j ≠ v j := by
      intro h
      have := congrArg Fin.val h
      simp [u, v] at this
    have hmem : α j ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨u j, v j, hne, rfl⟩
    obtain ⟨hk, -⟩ := hmem
    have hk' : α j ∈ {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧ rootChar a β = 1} := by
      rwa [← kernelRoots_rootCharHom]
    exact hk'.2
  · intro hk
    have hinner : twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) :=
      twistInner_of_twistKind_eq_innerT S
        CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hk
    rw [hm1] at hinner
    have hmaps : ∀ x y : Fin 9, x ≠ y →
        (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[1] (σ x y) ∈
          CFSG.HardMathSupport.Timmesfeld.CrossChar.frameRoots σ := by
      intro x y hxy
      rw [Function.iterate_one, hrho1 x y hxy]
      rcases hε with h | h
      · rw [h, one_smul]; exact ⟨x, y, hxy, rfl⟩
      · rw [h, neg_one_smul, ← hψ.neg x y]; exact ⟨y, x, hxy.symm, rfl⟩
    have hneg1 : ∀ γ : Fin Tag.E8.rank → ℤ,
        (S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[1] (-γ) = -(S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[1] γ := by
      intro γ
      rw [Function.iterate_one]
      exact S.frob.neg_eq γ
    rcases hψ.aut_cases hν hκ hnorm _ hmaps hneg1
        (fun γ δ => iform_rho_iterate S 1 γ δ) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · rcases hε with h | h
      · exact h
      · exfalso
        have key : ∀ x y : Fin 9, x ≠ y → σ (π x) (π y) = σ y x := by
          intro x y hxy
          have := hπ x y hxy
          rw [Function.iterate_one, hrho1 x y hxy, h, neg_one_smul, ← hψ.neg x y] at this
          exact this.symm
        have e1 := hψ.eq_of_eq hκ hnorm (π.injective.ne (by decide : (0 : Fin 9) ≠ 1))
          (by decide : (1 : Fin 9) ≠ 0) (key 0 1 (by decide))
        have e2 := hψ.eq_of_eq hκ hnorm (π.injective.ne (by decide : (0 : Fin 9) ≠ 2))
          (by decide : (2 : Fin 9) ≠ 0) (key 0 2 (by decide))
        exact absurd (e1.1.symm.trans e2.1) (by decide)
    · exact absurd (hΨ ▸ hinner)
        (CFSG.StandardType.TablePThreeKG.not_twistInner_of_unitaryFrame hν hψ hκ hnorm _ π hπ)
  · intro hk
    obtain ⟨π, hπ⟩ := CFSG.HardMathSupport.Dickson.Sec6.ssexc_suN_perm S hT i hk hν hψ hκ hnorm hΨ
    rcases hε with h | h
    · exfalso
      have key : ∀ x y : Fin 9, x ≠ y → σ (π y) (π x) = σ x y := by
        intro x y hxy
        have := hπ x y hxy
        rw [hm1, Function.iterate_one, hrho1 x y hxy, h, one_smul] at this
        exact this.symm
      have e1 := hψ.eq_of_eq hκ hnorm (π.injective.ne (by decide : (1 : Fin 9) ≠ 0))
        (by decide : (0 : Fin 9) ≠ 1) (key 0 1 (by decide))
      have e2 := hψ.eq_of_eq hκ hnorm (π.injective.ne (by decide : (2 : Fin 9) ≠ 0))
        (by decide : (0 : Fin 9) ≠ 2) (key 0 2 (by decide))
      exact absurd (e1.2.symm.trans e2.2) (by decide)
    · exact h

theorem recoga_A8_frame
    {L : Type} [Field L] [IsAlgClosed L] {n' f p : ℕ} {Bs : Subgroup (GGAutU .E8 n' f)}
    {S : Matrix (Fin (ggU (absTag .E8) 6 f).D.rank) (Fin (ggU (absTag .E8) 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU (absTag .E8) 6 f).D.rank)}
    {coord : Bs →* Multiplicative (Fin (ggU (absTag .E8) 6 f).D.rank → ZMod p)}
    (B : GGLangData L .E8 n' f p Bs S π coord)
    (hτ : B.τ = .E8) (hp : p.Prime) (hp2 : p ≠ 2)
    {b : Bs} (hb : b ≠ 1) (i : KernelComponent (rootCharHom (B.a b)))
    (hrank8 : compRank (componentRoots (rootCharHom (B.a b)) i) = 8)
    (hn72 : (componentRoots (rootCharHom (B.a b)) i).ncard = 72) :
    ∃ Bm : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ,
      Bm.transpose * Tag.E8.cartan * Bm = CartanMatrix.A 8 ∧
      (∀ j, rootChar (fun i : Fin Tag.E8.rank => B.a b (Fin.cast (by rw [hτ]) i))
        (fun i => Bm i j) = 1) ∧
      (twistKind B.setup.ρ (rootCharHom (B.a b)) i = .inner → B.ε = 1) ∧
      (twistKind B.setup.ρ (rootCharHom (B.a b)) i = .suN → B.ε = -1) :=
  recogf_main hτ B.setup hp (ggLang_natCast_ne_zero B hp hp2) (B.a_torus b)
    (recoga_rootDiagUnit_pow B b) B.ε_cases (fun γ hγ => recoga_rho_smul B hτ hγ) i
    (recoga_orbitLength_eq_one B hτ b i) hrank8 hn72

end Recognition

end CFSG.StandardType

end
