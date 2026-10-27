module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLCat
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoRoots
import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoF4Class

public section

namespace CFSG.StandardType.LangRat

open CFSG CFSG.Assembly
open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

private theorem rationalRoots_ne_of_iterate_image_ne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i i' : KernelComponent (rootCharHom a))
    (hno : ∀ k : ℕ, (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] ''
      componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i') :
    rationalRoots S.ρ (rootCharHom a) i ≠ rationalRoots S.ρ (rootCharHom a) i' := by
  intro heq
  obtain ⟨x, hx⟩ := Quotient.exists_rep i'
  have hxmem : (x : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i' := ⟨x.2, hx⟩
  have hxrat' : (x : Fin τ.rank → ℤ) ∈ rationalRoots S.ρ (rootCharHom a) i' :=
    ⟨0, x.1, hxmem, rfl⟩
  have hxrat : (x : Fin τ.rank → ℤ) ∈ rationalRoots S.ρ (rootCharHom a) i := by
    rw [heq]
    exact hxrat'
  obtain ⟨k, y, hy, hky⟩ := hxrat
  obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k
  have hmemj : (x : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) j := by
    rw [hj]
    exact ⟨y, hy, hky.symm⟩
  have hji : j = i' := eq_of_mem_componentRoots hmemj hxmem
  exact hno k (by rw [← hj, hji])

theorem rationalComponent_ne_of_forall_iterate_ne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i i' : KernelComponent (rootCharHom a))
    (hno : ∀ k : ℕ, (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] ''
      componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i')
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≠ rationalComponent S.ρ S.Γ (rootCharHom a) i' := by
  have hker :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rho_mem_kernelRoots_of_mem_torus S hT
  have hform : ∀ γ δ : Fin τ.rank → ℤ,
      CFSG.LieType.Steinberg.Adjoint.iform (S.ρ γ) (S.ρ δ) =
        CFSG.LieType.Steinberg.Adjoint.iform γ δ := fun γ δ => S.frob.iform_eq γ δ
  have hratne : rationalRoots S.ρ (rootCharHom a) i ≠ rationalRoots S.ρ (rootCharHom a) i' :=
    rationalRoots_ne_of_iterate_image_ne S hT i i' hno
  have hcomm :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.commute_rootSpan_rationalRoots
      (τ := τ) (L := L) hker hform hratne
  intro heq
  have hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :=
    (commutator_le_self_of_subgroup _).trans inf_le_left
  have hle' : rationalComponent S.ρ S.Γ (rootCharHom a) i' ≤
      rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i') :=
    (commutator_le_self_of_subgroup _).trans inf_le_left
  have habel : ∀ x y : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      x * y = y * x := by
    intro x y
    have hx : (x : ModGL τ L) ∈
        rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) :=
      hle x.2
    have hy : (y : ModGL τ L) ∈
        rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i') :=
      hle' (by rw [← heq]; exact y.2)
    exact Subtype.ext (hcomm (x : ModGL τ L) hx (y : ModGL τ L) hy).eq
  obtain ⟨u, v, huv⟩ := hQS.2.2
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) u
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) v
  rw [← hx, ← hy] at huv
  exact huv (by rw [← map_mul, ← map_mul, habel x y])

section F4A2A2

open CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

private theorem langF4_a2a2_two_comp_aux
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hak : ∀ j, a j = ω ^ k j) (hk : KernelA2A2 k)
    (hq : 4 ≤ S.D.q) (i : KernelComponent (rootCharHom a)) :
    ∃ j : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) j) ∧
        rationalComponent S.ρ S.Γ (rootCharHom a) j ≠
          rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  obtain ⟨x, hx⟩ := Quotient.exists_rep i
  have hi_eq : componentRoots (rootCharHom a) i =
      {γ : V4 | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 (x : V4) (x : V4)} := by
    rw [← hx]
    exact componentRoots_eq_sameLength hω3 hω1 hak hk (γ₀ := (x : V4)) x.2
  have hxcases : ipF4 (x : V4) (x : V4) = 2 ∨ ipF4 (x : V4) (x : V4) = 4 := by
    have h := iform_self_cases noG2_F4 x.2.1
    rwa [iform_F4] at h
  have hfinL : {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 ∧ ipF4 γ γ = 4}.Finite :=
    (finite_setOf_isRoot Tag.F4).subset (fun γ hγ => hγ.1)
  have hfinS : {γ : V4 | IsRoot Tag.F4 γ ∧ kdot k γ % 3 = 0 ∧ ipF4 γ γ = 2}.Finite :=
    (finite_setOf_isRoot Tag.F4).subset (fun γ hγ => hγ.1)
  have hexists : ∃ γ' : V4, IsRoot Tag.F4 γ' ∧ kdot k γ' % 3 = 0 ∧
      ipF4 γ' γ' ≠ ipF4 (x : V4) (x : V4) := by
    rcases hxcases with hx2 | hx4
    · obtain ⟨γ', hγ'⟩ := (Set.ncard_pos hfinL).1 (by rw [hk.card_long]; norm_num)
      exact ⟨γ', hγ'.1, hγ'.2.1, by rw [hγ'.2.2, hx2]; norm_num⟩
    · obtain ⟨γ', hγ'⟩ := (Set.ncard_pos hfinS).1 (by rw [hk.card_short]; norm_num)
      exact ⟨γ', hγ'.1, hγ'.2.1, by rw [hγ'.2.2, hx4]; norm_num⟩
  obtain ⟨γ', hγ'r, hγ'k, hlen_ne⟩ := hexists
  have hγ'ker : γ' ∈ kernelRoots (rootCharHom a) := by
    rw [kernelRoots_rootCharHom]
    exact ⟨hγ'r, (rootChar_eq_one_iff hω3 hω1 hak γ').2 hγ'k⟩
  let j : KernelComponent (rootCharHom a) := ⟦⟨γ', hγ'ker⟩⟧
  have hpres_all : ∀ m : ℕ,
      ipF4 ((S.ρ : V4 → V4)^[m] γ') ((S.ρ : V4 → V4)^[m] γ') = ipF4 γ' γ' := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      have h := S.frob.iform_eq ((S.ρ : V4 → V4)^[m] γ') ((S.ρ : V4 → V4)^[m] γ')
      rw [iform_F4, iform_F4] at h
      rw [h, ih]
  have hno : ∀ m : ℕ,
      (S.ρ : V4 → V4)^[m] '' componentRoots (rootCharHom a) j ≠
        componentRoots (rootCharHom a) i := by
    intro m heq
    have hmem : (S.ρ : V4 → V4)^[m] γ' ∈ componentRoots (rootCharHom a) i := by
      rw [← heq]
      exact ⟨γ', ⟨hγ'ker, rfl⟩, rfl⟩
    have hlen_i : ipF4 ((S.ρ : V4 → V4)^[m] γ') ((S.ρ : V4 → V4)^[m] γ') =
        ipF4 (x : V4) (x : V4) := by
      have : (S.ρ : V4 → V4)^[m] γ' ∈
          {γ : V4 | γ ∈ kernelRoots (rootCharHom a) ∧
            ipF4 γ γ = ipF4 (x : V4) (x : V4)} := by
        rwa [← hi_eq]
      exact this.2
    exact hlen_ne ((hpres_all m).symm.trans hlen_i)
  have hs : 0 < componentOrbitLength S.ρ (componentRoots (rootCharHom a) j) :=
    (outer_componentOrbitLength_spec S hT j).1
  have hpow4 : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) j) :=
    calc (4 : ℕ) ≤ S.D.q := hq
      _ = S.D.q ^ 1 := (pow_one _).symm
      _ ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) j) :=
        pow_le_pow_right₀ (by omega) (by omega)
  have hnot : ¬ LangSmallSolv S.D.q S.ρ (rootCharHom a) j := by
    rintro (⟨hle, -⟩ | ⟨heq, -, -⟩)
    · have : (4 : ℕ) ≤ 3 := le_trans hpow4 hle
      norm_num at this
    · have : (4 : ℕ) ≤ 2 := by
        rw [heq] at hpow4
        exact hpow4
      norm_num at this
  have hpL : (3 : L) ≠ 0 := by
    intro h
    have hdvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h
    norm_num at hdvd
  have hQSj : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) j) :=
    isQuasisimple_rationalComponent_of_not_langSmallSolv (τ := Tag.F4) (p := 3) S (by decide)
      Nat.prime_three hpL hT hap h1 j hnot
  exact ⟨j, hQSj, rationalComponent_ne_of_forall_iterate_ne S hT j i hno hQSj⟩

end F4A2A2

theorem langF4_a2a2_two_comp
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀)
    {a : Fin Tag.F4.rank → Lˣ} (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hak : ∀ j, a j = ω ^ k j)
    (hk : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.KernelA2A2 k)
    (hq : 4 ≤ S.D.q) (i : KernelComponent (rootCharHom a)) :
    ∃ j : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) j) ∧
        rationalComponent S.ρ S.Γ (rootCharHom a) j ≠ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  exact langF4_a2a2_two_comp_aux S hT hap h1 hω3 hω1 hak hk hq i

end CFSG.StandardType.LangRat

end
