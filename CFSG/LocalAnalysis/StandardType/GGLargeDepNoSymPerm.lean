module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l04fD5_ggIntCartan_A (n : ℕ) : GGIntCartan (CoxeterMatrix.A n) (CartanMatrix.A n) := by
  refine ⟨fun i => by simp [CartanMatrix.A], fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [CoxeterMatrix.A, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega
lemma l04fD5_swap_mul_apply {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {h : Fin m → V} {α : Fin m → Module.Dual (ZMod p) V}
    (r : Fin m → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A m i j : ZMod p))
    {i j : Fin m} (hij : (i : ℕ) + 1 = (j : ℕ)) : r i (r j (h i)) = h j := by
  have hji : α j (h i) = -1 := by
    rw [hpair j i]
    have hne : ¬ (j = i) := by
      intro hh
      have hval := congrArg Fin.val hh
      omega
    have hadj : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) := Or.inr hij
    simp only [CartanMatrix.A, Matrix.of_apply]
    rw [if_neg hne, if_pos hadj]
    norm_num
  have hij' : α i (h j) = -1 := by
    rw [hpair i j]
    have hne : ¬ (i = j) := by
      intro hh
      have hval := congrArg Fin.val hh
      omega
    have hadj : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) := Or.inl hij
    simp only [CartanMatrix.A, Matrix.of_apply]
    rw [if_neg hne, if_pos hadj]
    norm_num
  have hii : α i (h i) = 2 := by
    rw [hpair i i]
    simp [CartanMatrix.A]
  have hrj : r j (h i) = h i + h j := by
    rw [hr j (h i), hji]
    module
  have hri : r i (h i + h j) = h j := by
    rw [map_add, hr i (h i), hr i (h j), hii, hij']
    module
  rw [hrj, hri]
theorem l04fD5_perm_embed {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 5 ≤ m + 1)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {h : Fin m → V}
    {α : Fin m → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A m i j : ZMod p))
    (r : Fin m → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i) : ∃ ρ : Equiv.Perm (Fin (m + 1)) →* (V ≃ₗ[ZMod p] V), (∀ i, ρ (Equiv.swap i.castSucc i.succ) = r i) ∧ (∀ σ, ρ σ ∈ Subgroup.closure (Set.range r)) ∧ Function.Injective ρ := by
  have hm2 : 2 ≤ m := by omega
  let M : CoxeterMatrix (Fin m) := CFSG.LieType.RootSystem.coxeterMatrix (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A m)
  have hα : ∀ i : Fin m, α i (h i) = 2 := by
    intro i
    rw [hpair i i]
    simp [CartanMatrix.A]
  have hP : ∀ i j : Fin m, α i (h j) = (CartanMatrix.A m i j : ZMod p) := hpair
  have hCartan : GGIntCartan M (CartanMatrix.A m) := by
    dsimp only [M]
    rw [coxeterMatrix_isFiniteType_A_eq m]
    exact l04fD5_ggIntCartan_A m
  have hLift : M.IsLiftable (fun i : Fin m => Module.reflection (hα i)) := isLiftable_reflection_of_intCartan hCartan h α hα hP
  let lift : M.Group →* (V ≃ₗ[ZMod p] V) := M.toCoxeterSystem.lift ⟨fun i : Fin m => Module.reflection (hα i), hLift⟩
  let ρ : Equiv.Perm (Fin (m + 1)) →* (V ≃ₗ[ZMod p] V) := lift.comp (typeAWeylEquiv m).toMonoidHom
  have hrefl : ∀ i : Fin m, Module.reflection (hα i) = r i := by
    intro i
    ext v
    rw [Module.reflection_apply, hr i v]
  have hsimple : ∀ i : Fin m, lift (M.toCoxeterSystem.simple i) = r i := by
    intro i
    rw [← hrefl i]
    exact CoxeterSystem.lift_apply_simple M.toCoxeterSystem hLift i
  have hρsimple : ∀ i : Fin m, ρ (Equiv.swap i.castSucc i.succ) = r i := by
    intro i
    change lift ((typeAWeylEquiv m) (Equiv.swap i.castSucc i.succ)) = r i
    rw [typeAWeylEquiv_swap]
    change lift (M.toCoxeterSystem.simple i) = r i
    rw [hsimple i]
  have hρmem : ∀ σ : Equiv.Perm (Fin (m + 1)), ρ σ ∈ Subgroup.closure (Set.range r) := by
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
  have hRpres : ∀ g ∈ Subgroup.closure (Set.range r), (∀ v ∈ H, g v ∈ H) ∧ (∀ v ∈ H, g⁻¹ v ∈ H) := by
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
  have hKmem_H : ∀ n : Equiv.Perm (Fin (m + 1)), (∀ i, ρ n (h i) = h i) → ∀ v ∈ H, ρ n v = v := by
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
        have h2 : (ρ a)⁻¹ ((ρ a) (h i)) = h i := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
        rw [ha i] at h2
        exact h2 }
  have hKnormal : K.Normal := ⟨fun n hn σ => by
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
    have hAle : alternatingGroup (Fin (m + 1)) ≤ K := Equiv.Perm.alternatingGroup_le_of_normal hcard hnt
    let a : Fin m := ⟨0, by omega⟩
    let b : Fin m := ⟨1, by omega⟩
    let d : Fin m := ⟨2, by omega⟩
    have hab1 : (a : ℕ) + 1 = (b : ℕ) := by simp [a, b]
    have hbd1 : (b : ℕ) + 1 = (d : ℕ) := by simp [b, d]
    have hc0A : Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ ∈
        alternatingGroup (Fin (m + 1)) := Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        ⟨a.castSucc, a.succ, a.castSucc_lt_succ.ne, rfl⟩
        ⟨b.castSucc, b.succ, b.castSucc_lt_succ.ne, rfl⟩
    have hc0K : Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ ∈ K := hAle hc0A
    have hc0K' : ∀ i, ρ (Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ) (h i) = h i := hc0K
    have hc0val : ρ (Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ) (h a) = h b := by
      rw [map_mul, LinearEquiv.mul_apply, hρsimple a, hρsimple b]
      exact l04fD5_swap_mul_apply (i := a) (j := b) r hr hpair hab1
    have heq_ab : h a = h b := (hc0K' a).symm.trans hc0val
    have hc1A : Equiv.swap b.castSucc b.succ * Equiv.swap d.castSucc d.succ ∈
        alternatingGroup (Fin (m + 1)) := Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        ⟨b.castSucc, b.succ, b.castSucc_lt_succ.ne, rfl⟩
        ⟨d.castSucc, d.succ, d.castSucc_lt_succ.ne, rfl⟩
    have hc1K : Equiv.swap b.castSucc b.succ * Equiv.swap d.castSucc d.succ ∈ K := hAle hc1A
    have hc1K' : ∀ i, ρ (Equiv.swap b.castSucc b.succ * Equiv.swap d.castSucc d.succ) (h i) = h i := hc1K
    have hc1val : ρ (Equiv.swap b.castSucc b.succ * Equiv.swap d.castSucc d.succ) (h b) = h d := by
      rw [map_mul, LinearEquiv.mul_apply, hρsimple b, hρsimple d]
      exact l04fD5_swap_mul_apply (i := b) (j := d) r hr hpair hbd1
    have heq_bd : h b = h d := (hc1K' b).symm.trans hc1val
    have heq_ad : h a = h d := heq_ab.trans heq_bd
    have hcontra : (2 : ZMod p) = 0 := by
      have hc := congrArg (fun v => α a v) heq_ad
      rw [hα a] at hc
      have h0 : α a (h d) = 0 := by
        rw [hpair a d]
        have hne : ¬ (a = d) := by
          intro hh
          have hval := congrArg Fin.val hh
          dsimp only [a, d] at hval
          omega
        have hnot : ¬ ((a : ℕ) + 1 = (d : ℕ) ∨ (d : ℕ) + 1 = (a : ℕ)) := by
          intro hh
          rcases hh with hh | hh <;> (dsimp only [a, d] at hh; omega)
        simp only [CartanMatrix.A, Matrix.of_apply]
        rw [if_neg hne, if_neg hnot]
        norm_num
      rw [h0] at hc
      exact hc
    exact (ZMod.prime_ne_zero p 2 hp2) hcontra
  refine ⟨ρ, hρsimple, hρmem, ?_⟩
  intro σ τ hστ
  have hmemK : σ * τ⁻¹ ∈ K := by
    intro i
    rw [map_mul, hστ, MonoidHom.map_inv, mul_inv_cancel]
    rfl
  rw [hKbot] at hmemK
  have h1 : σ * τ⁻¹ = 1 := by simpa using hmemK
  exact mul_inv_eq_one.mp h1
theorem l04fD5_P_card {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 5 ≤ m + 1)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {h : Fin m → V}
    {α : Fin m → Module.Dual (ZMod p) V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A m i j : ZMod p))
    (r : Fin m → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i) : Nat.card ↥(Subgroup.closure (Set.range r)) = (m + 1).factorial := by
  obtain ⟨ρ, hρr, hρmem, hρinj⟩ := l04fD5_perm_embed hp2 hm hpair r hr
  have hrange : ρ.range = Subgroup.closure (Set.range r) := by
    apply le_antisymm
    · rintro _ ⟨σ, rfl⟩
      exact hρmem σ
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨Equiv.swap i.castSucc i.succ, hρr i⟩
  rw [← hrange]
  calc Nat.card ↥ρ.range = Nat.card (Equiv.Perm (Fin (m + 1))) := Nat.card_congr (Equiv.ofInjective ρ hρinj).symm
    _ = (m + 1).factorial := by rw [Nat.card_perm, Nat.card_fin]

end CFSG.StandardType

end
