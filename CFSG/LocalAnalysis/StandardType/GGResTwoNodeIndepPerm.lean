module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l6aP_ggIntCartan_A (n : ℕ) :
    GGIntCartan (CoxeterMatrix.A n) (CartanMatrix.A n) := by
  refine ⟨fun i => by simp [CartanMatrix.A], fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [CoxeterMatrix.A, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem l6aP_perm_embed_aux {p m : ℕ} [Fact p.Prime] (hN : 5 ≤ m + 1)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {h : Fin m → V} (hinj : Function.Injective h)
    {α : Fin m → Module.Dual (ZMod p) V} {x : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A m i j : ZMod p))
    (hx : ∀ i, α i x = 0)
    (r : Fin m → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i) :
    ∃ ρ : Equiv.Perm (Fin (m + 1)) →* (V ≃ₗ[ZMod p] V),
      (∀ i, ρ (Equiv.swap (ggDepALeft (m + 1) i) (ggDepARight (m + 1) i)) = r i) ∧
        (∀ σ, ρ σ ∈ Subgroup.closure (Set.range r)) ∧ (∀ σ, ρ σ x = x) ∧
        ∀ σ, (∀ i, ρ σ (h i) = h i) → σ = 1 := by
  have hm2 : 2 ≤ m := by omega
  let M : CoxeterMatrix (Fin m) :=
    CFSG.LieType.RootSystem.coxeterMatrix (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)
  have hα : ∀ i : Fin m, α i (h i) = 2 := by
    intro i
    rw [hpair i i]
    simp [CartanMatrix.A]
  have hP : ∀ i j : Fin m, α i (h j) = (CartanMatrix.A m i j : ZMod p) := hpair
  have hCartan : GGIntCartan M (CartanMatrix.A m) := by
    dsimp only [M]
    rw [coxeterMatrix_isFiniteType_A_eq m]
    exact l6aP_ggIntCartan_A m
  have hLift : M.IsLiftable (fun i : Fin m => Module.reflection (hα i)) :=
    isLiftable_reflection_of_intCartan hCartan h α hα hP
  let lift : M.Group →* (V ≃ₗ[ZMod p] V) :=
    M.toCoxeterSystem.lift ⟨fun i : Fin m => Module.reflection (hα i), hLift⟩
  let ρ : Equiv.Perm (Fin (m + 1)) →* (V ≃ₗ[ZMod p] V) :=
    lift.comp (typeAWeylEquiv m).toMonoidHom
  have hrefl : ∀ i : Fin m, Module.reflection (hα i) = r i := by
    intro i
    ext v
    rw [Module.reflection_apply, hr i v]
  have hsimple : ∀ i : Fin m, lift (M.toCoxeterSystem.simple i) = r i := by
    intro i
    rw [← hrefl i]
    exact CoxeterSystem.lift_apply_simple M.toCoxeterSystem hLift i
  have hswapLR : ∀ i : Fin m,
      Equiv.swap (ggDepALeft (m + 1) i) (ggDepARight (m + 1) i) =
        Equiv.swap i.castSucc i.succ := by
    intro i
    rw [show ggDepALeft (m + 1) i = i.castSucc from Fin.ext rfl,
      show ggDepARight (m + 1) i = i.succ from Fin.ext rfl]
  have hρsimple : ∀ i : Fin m, ρ (Equiv.swap i.castSucc i.succ) = r i := by
    intro i
    change lift ((typeAWeylEquiv m) (Equiv.swap i.castSucc i.succ)) = r i
    rw [typeAWeylEquiv_swap]
    change lift (M.toCoxeterSystem.simple i) = r i
    rw [hsimple i]
  have hliftx : ∀ w : M.Group, lift w x = x := by
    intro w
    refine M.toCoxeterSystem.simple_induction_left (p := fun w => lift w x = x) w ?_ ?_
    · rw [map_one]; rfl
    · intro w i ih
      rw [map_mul, LinearEquiv.mul_apply, ih, hsimple i, hr i x, hx i, zero_smul, sub_zero]
  have hρmem : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ρ σ ∈ Subgroup.closure (Set.range r) := by
    intro σ
    have hσ : σ ∈
        Subgroup.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ m)]
      exact Subgroup.mem_top σ
    refine Subgroup.closure_induction
      (k := Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)
      (p := fun σ _ => ρ σ ∈ Subgroup.closure (Set.range r)) ?_ ?_ ?_ ?_ hσ
    · rintro g ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, (hρsimple i).symm⟩
    · rw [map_one]; exact Subgroup.one_mem _
    · intro a b ha hb iha ihb
      rw [map_mul]; exact Subgroup.mul_mem _ iha ihb
    · intro a ha iha
      rw [map_inv]; exact Subgroup.inv_mem _ iha
  let H : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  have hsub : ∀ i : Fin m, h i ∈ H := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hRpres : ∀ g ∈ Subgroup.closure (Set.range r),
      (∀ v ∈ H, g v ∈ H) ∧ (∀ v ∈ H, g⁻¹ v ∈ H) := by
    intro g hg
    refine Subgroup.closure_induction (k := Set.range r)
      (p := fun g _ => (∀ v ∈ H, g v ∈ H) ∧ (∀ v ∈ H, g⁻¹ v ∈ H)) ?_ ?_ ?_ ?_ hg
    · rintro g ⟨i, rfl⟩
      have h1 : ∀ v ∈ H, r i v ∈ H := by
        intro v hv
        rw [hr i v]
        exact H.sub_mem hv (H.smul_mem _ (hsub i))
      have hinv : (r i)⁻¹ = r i := by rw [← hrefl i, Module.reflection_inv, hrefl i]
      exact ⟨h1, fun v hv => by rw [hinv]; exact h1 v hv⟩
    · exact ⟨fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩
    · rintro a b ha hb ⟨h1a, h1b⟩ ⟨h2a, h2b⟩
      refine ⟨?_, ?_⟩
      · intro v hv
        rw [LinearEquiv.mul_apply]
        exact h1a (b v) (h2a v hv)
      · intro v hv
        rw [mul_inv_rev, LinearEquiv.mul_apply]
        exact h2b (a⁻¹ v) (h1b v hv)
    · rintro a ha ⟨h1a, h1b⟩
      exact ⟨h1b, fun v hv => by simpa using h1a v hv⟩
  have hKmem_H : ∀ n : Equiv.Perm (Fin (m + 1)),
      (∀ i, ρ n (h i) = h i) → ∀ v ∈ H, ρ n v = v := by
    intro n hn v hv
    refine Submodule.span_induction (p := fun v _ => ρ n v = v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨i, rfl⟩
      exact hn i
    · rw [map_zero]
    · intro x y hx hy ihx ihy
      rw [map_add, ihx, ihy]
    · intro c x hx ihx
      rw [map_smul, ihx]
  let K : Subgroup (Equiv.Perm (Fin (m + 1))) :=
    { carrier := {σ | ∀ i, ρ σ (h i) = h i}
      one_mem' := by intro i; rw [map_one]; rfl
      mul_mem' := by
        intro a b ha hb i
        rw [map_mul, LinearEquiv.mul_apply, hb i, ha i]
      inv_mem' := by
        intro a ha i
        rw [map_inv]
        have h2 : (ρ a)⁻¹ ((ρ a) (h i)) = h i := by
          rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
        rw [ha i] at h2
        exact h2 }
  haveI hKnormal : K.Normal := ⟨fun n hn σ => by
    intro i
    rw [map_mul, map_mul, map_inv]
    have h1 : (ρ σ)⁻¹ (h i) ∈ H := (hRpres (ρ σ) (hρmem σ)).2 (h i) (hsub i)
    have h2 : ρ n ((ρ σ)⁻¹ (h i)) = (ρ σ)⁻¹ (h i) := hKmem_H n hn _ h1
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h2]
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl⟩
  have hKbot : K = ⊥ := by
    by_contra hne
    have hnt : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
    have hcard : 5 ≤ Nat.card (Fin (m + 1)) := by rw [Nat.card_fin]; omega
    have hAle : alternatingGroup (Fin (m + 1)) ≤ K :=
      Equiv.Perm.alternatingGroup_le_of_normal hcard hnt
    let a : Fin m := ⟨0, by omega⟩
    let b : Fin m := ⟨1, by omega⟩
    let c : Equiv.Perm (Fin (m + 1)) :=
      Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ
    have hcA : c ∈ alternatingGroup (Fin (m + 1)) := by
      change Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ ∈
        alternatingGroup (Fin (m + 1))
      exact Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        ⟨a.castSucc, a.succ, a.castSucc_lt_succ.ne, rfl⟩
        ⟨b.castSucc, b.succ, b.castSucc_lt_succ.ne, rfl⟩
    have hcK : c ∈ K := hAle hcA
    have hcK' : ∀ i, ρ c (h i) = h i := hcK
    have hc_fix : ρ c (h a) = h a := hcK' a
    have haa : α a (h a) = 2 := hα a
    have hba : α b (h a) = -1 := by
      rw [hpair b a]
      have h1 : ¬ (b = a) := by
        intro hb
        have hval := congrArg Fin.val hb
        dsimp only [a, b] at hval
        omega
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg h1]
      norm_num
    have hab : α a (h b) = -1 := by
      rw [hpair a b]
      have h1 : ¬ (a = b) := by
        intro hb
        have hval := congrArg Fin.val hb
        dsimp only [a, b] at hval
        omega
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg h1]
      norm_num
    have hrb : r b (h a) = h a + h b := by
      rw [hr b (h a), hba]
      module
    have hcval : ρ c (h a) = h b := by
      change ρ (Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ) (h a) = h b
      rw [map_mul, LinearEquiv.mul_apply, hρsimple a, hρsimple b, hrb, map_add,
        hr a (h a), hr a (h b), haa, hab]
      module
    have hne_h : h a ≠ h b := by
      intro hh
      have hab' : a = b := hinj hh
      have hval := congrArg Fin.val hab'
      dsimp only [a, b] at hval
      omega
    exact hne_h (hc_fix.symm.trans hcval)
  refine ⟨ρ, ?_, hρmem, ?_, ?_⟩
  · intro i
    rw [hswapLR i, hρsimple i]
  · intro σ
    exact hliftx ((typeAWeylEquiv m) σ)
  · intro σ hσ
    have hσK : σ ∈ K := hσ
    rw [hKbot] at hσK
    exact Subgroup.mem_bot.mp hσK

theorem ggIndep_perm_embed {p N : ℕ} [Fact p.Prime] (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGIndepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i) :
    ∃ ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V),
      (∀ i, ρ (Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = r i) ∧
        (∀ σ, ρ σ ∈ Subgroup.closure (Set.range r)) ∧ (∀ σ, ρ σ x = x) ∧
        ∀ σ, (∀ i, ρ σ (h i) = h i) → σ = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact l6aP_perm_embed_aux hN F.indep.injective F.pair F.x_ker r hr

end CFSG.StandardType

end
