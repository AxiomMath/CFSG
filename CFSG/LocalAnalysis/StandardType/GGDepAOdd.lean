module

public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGDepAPerm
public import CFSG.LocalAnalysis.StandardType.GGDepAArith
public import CFSG.LocalAnalysis.StandardType.GGDepACaseI
public import CFSG.LocalAnalysis.StandardType.GGDepACaseII
public import CFSG.LocalAnalysis.StandardType.GGDepARefl
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nOA_ggIntCartan_A (n : ℕ) :
    GGIntCartan (CoxeterMatrix.A n) (CartanMatrix.A n) := by
  refine ⟨fun i => by simp [CartanMatrix.A], fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [CoxeterMatrix.A, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma l05nOA_swap_mul_apply {p m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {h : Fin m → V} {α : Fin m → Module.Dual (ZMod p) V}
    (r : Fin m → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A m i j : ZMod p))
    {i j : Fin m} (hij : (i : ℕ) + 1 = (j : ℕ)) :
    r i (r j (h i)) = h j := by
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

private theorem l05nOA_perm_embed_aux {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ m + 1)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {h : Fin m → V}
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
    exact l05nOA_ggIntCartan_A m
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
    let d : Fin m := ⟨2, by omega⟩
    have hab1 : (a : ℕ) + 1 = (b : ℕ) := by simp [a, b]
    have hbd1 : (b : ℕ) + 1 = (d : ℕ) := by simp [b, d]
    have hc0A : Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ ∈
        alternatingGroup (Fin (m + 1)) :=
      Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        ⟨a.castSucc, a.succ, a.castSucc_lt_succ.ne, rfl⟩
        ⟨b.castSucc, b.succ, b.castSucc_lt_succ.ne, rfl⟩
    have hc0K : Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ ∈ K := hAle hc0A
    have hc0K' : ∀ i, ρ (Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ) (h i) =
        h i := hc0K
    have hc0val : ρ (Equiv.swap a.castSucc a.succ * Equiv.swap b.castSucc b.succ) (h a) = h b := by
      rw [map_mul, LinearEquiv.mul_apply, hρsimple a, hρsimple b]
      exact l05nOA_swap_mul_apply (i := a) (j := b) r hr hpair hab1
    have heq_ab : h a = h b := (hc0K' a).symm.trans hc0val
    have hc1A : Equiv.swap b.castSucc b.succ * Equiv.swap d.castSucc d.succ ∈
        alternatingGroup (Fin (m + 1)) :=
      Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
        ⟨b.castSucc, b.succ, b.castSucc_lt_succ.ne, rfl⟩
        ⟨d.castSucc, d.succ, d.castSucc_lt_succ.ne, rfl⟩
    have hc1K : Equiv.swap b.castSucc b.succ * Equiv.swap d.castSucc d.succ ∈ K := hAle hc1A
    have hc1K' : ∀ i, ρ (Equiv.swap b.castSucc b.succ * Equiv.swap d.castSucc d.succ) (h i) =
        h i := hc1K
    have hc1val : ρ (Equiv.swap b.castSucc b.succ * Equiv.swap d.castSucc d.succ) (h b) = h d := by
      rw [map_mul, LinearEquiv.mul_apply, hρsimple b, hρsimple d]
      exact l05nOA_swap_mul_apply (i := b) (j := d) r hr hpair hbd1
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
  refine ⟨ρ, ?_, hρmem, ?_, ?_⟩
  · intro i
    rw [hswapLR i, hρsimple i]
  · intro σ
    exact hliftx ((typeAWeylEquiv m) σ)
  · intro σ hσ
    have hσK : σ ∈ K := hσ
    rw [hKbot] at hσK
    exact Subgroup.mem_bot.mp hσK

theorem ggDepAOdd_perm_embed {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i) :
    ∃ ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V),
      (∀ i, ρ (Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = r i) ∧
        (∀ σ, ρ σ ∈ Subgroup.closure (Set.range r)) ∧ (∀ σ, ρ σ x = x) ∧
        ∀ σ, (∀ i, ρ σ (h i) = h i) → σ = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact l05nOA_perm_embed_aux hp2 hN F.pair F.x_ker r hr

private lemma l05nOB_refl_invol {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (r : V ≃ₗ[ZMod p] V) {h : V} {α : Module.Dual (ZMod p) V}
    (hr : ∀ v, r v = v - α v • h) (hα : α h = 2) : r * r = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, hr (r v), hr v]
  have hαv : α (v - α v • h) = -α v := by
    rw [map_sub, map_smul, hα, smul_eq_mul]
    ring
  rw [hαv, neg_smul]
  abel

private lemma l05nOB_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b : α) :
    e.permCongr (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  ext x
  rw [Equiv.permCongr_apply, ← Equiv.symm_trans_swap_trans a b e]
  rfl

private lemma l05nOB_adjacent_closure_top (N : ℕ) (h1 : 1 ≤ N) :
    Subgroup.closure (Set.range fun i : Fin (N - 1) =>
      Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = ⊤ := by
  have hfin : (N - 1) + 1 = N := Nat.sub_add_cancel h1
  let e : Fin ((N - 1) + 1) ≃ Fin N := finCongr hfin
  have hvalL : ∀ i : Fin (N - 1), e i.castSucc = ggDepALeft N i := by
    intro i
    apply Fin.ext
    rw [finCongr_apply, Fin.val_cast, Fin.val_castSucc]
    rfl
  have hvalR : ∀ i : Fin (N - 1), e i.succ = ggDepARight N i := by
    intro i
    apply Fin.ext
    rw [finCongr_apply, Fin.val_cast, Fin.val_succ]
    rfl
  have hmap : ∀ i : Fin (N - 1),
      e.permCongrHom (Equiv.swap i.castSucc i.succ) =
        Equiv.swap (ggDepALeft N i) (ggDepARight N i) := by
    intro i
    rw [Equiv.permCongrHom_coe, l05nOB_permCongr_swap e i.castSucc i.succ, hvalL i, hvalR i]
  have hset : Set.range (fun i : Fin (N - 1) =>
        Equiv.swap (ggDepALeft N i) (ggDepARight N i)) =
      e.permCongrHom '' Set.range (fun i : Fin (N - 1) =>
        Equiv.swap i.castSucc i.succ) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Equiv.swap i.castSucc i.succ, ⟨i, rfl⟩, hmap i⟩
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hmap i).symm⟩
  have htop0 : Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
      Equiv.swap i.castSucc i.succ)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Submonoid.closure_le.2 (fun y hy => Subgroup.subset_closure hy)
      (by rw [Equiv.Perm.mclosure_swap_castSucc_succ (N - 1)]; trivial)
  calc Subgroup.closure (Set.range fun i : Fin (N - 1) =>
        Equiv.swap (ggDepALeft N i) (ggDepARight N i))
      = Subgroup.closure (e.permCongrHom '' Set.range (fun i : Fin (N - 1) =>
          Equiv.swap i.castSucc i.succ)) := by rw [hset]
    _ = Subgroup.map e.permCongrHom (Subgroup.closure (Set.range (fun i : Fin (N - 1) =>
          Equiv.swap i.castSucc i.succ))) := by
        rw [MonoidHom.map_closure]
        rfl
    _ = Subgroup.map e.permCongrHom ⊤ := by rw [htop0]
    _ = ⊤ := by
        rw [Subgroup.map_top, MonoidHom.range_eq_top]
        exact e.permCongrHom.surjective

private lemma l05nOB_rho_mem_closure {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i, ρ (Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = r i)
    (h1 : 1 ≤ N) (σ : Equiv.Perm (Fin N)) :
    ρ σ ∈ Subgroup.closure (Set.range r) := by
  have hσ : σ ∈ Subgroup.closure (Set.range fun i : Fin (N - 1) =>
      Equiv.swap (ggDepALeft N i) (ggDepARight N i)) := by
    rw [l05nOB_adjacent_closure_top N h1]
    trivial
  refine Subgroup.closure_induction
    (p := fun x _ => ρ x ∈ Subgroup.closure (Set.range r))
    (fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      rw [hρ i]
      exact Subgroup.subset_closure ⟨i, rfl⟩)
    (by rw [map_one]; exact Subgroup.one_mem _)
    (fun x y hx hy ihx ihy => by rw [map_mul]; exact Subgroup.mul_mem _ ihx ihy)
    (fun x hx ih => by rw [map_inv]; exact Subgroup.inv_mem _ ih) hσ

private lemma l05nOB_closure_preserves {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (hii : ∀ i, α i (h i) = 2) :
    ∀ g ∈ Subgroup.closure (Set.range r),
      (∀ v ∈ Submodule.span (ZMod p) (Set.range h), g v ∈ Submodule.span (ZMod p) (Set.range h)) ∧
      (∀ v ∈ Submodule.span (ZMod p) (Set.range h),
        g⁻¹ v ∈ Submodule.span (ZMod p) (Set.range h)) := by
  intro g hg
  refine Subgroup.closure_induction (p := fun x _ =>
    (∀ v ∈ Submodule.span (ZMod p) (Set.range h), x v ∈ Submodule.span (ZMod p) (Set.range h)) ∧
    (∀ v ∈ Submodule.span (ZMod p) (Set.range h),
      x⁻¹ v ∈ Submodule.span (ZMod p) (Set.range h))) ?_ ?_ ?_ ?_ hg
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    have hinv : (r i)⁻¹ = r i := by
      rw [inv_eq_iff_mul_eq_one]
      exact l05nOB_refl_invol (r i) (hr i) (hii i)
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [hr i v]
      exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · intro v hv
      rw [hinv, hr i v]
      exact Submodule.sub_mem _ hv (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · refine ⟨?_, ?_⟩
    · intro v hv; simpa using hv
    · intro v hv; simpa using hv
  · intro x y hx hy ihx ihy
    refine ⟨?_, ?_⟩
    · intro v hv
      exact ihx.1 (y v) (ihy.1 v hv)
    · intro v hv
      rw [mul_inv_rev]
      exact ihy.2 (x⁻¹ v) (ihx.2 v hv)
  · intro x hx ih
    refine ⟨?_, ?_⟩
    · exact ih.2
    · intro v hv
      rw [inv_inv]
      exact ih.1 v hv

theorem ggDepAOdd_perm_swap_refl {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i, ρ (Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = r i) {a b : Fin N}
    (hab : a ≠ b) :
    ∃ (t : V) (β : Module.Dual (ZMod p) V), t ∈ Submodule.span (ZMod p) (Set.range h) ∧
      β t = 2 ∧ ∀ v, ρ (Equiv.swap a b) v = v - β v • t := by
  let i0 : Fin (N - 1) := ⟨0, by omega⟩
  have hL0R0 : ggDepALeft N i0 ≠ ggDepARight N i0 := by
    rw [ne_eq, Fin.ext_iff]
    simp [ggDepALeft, ggDepARight, i0]
  have hii : ∀ i, α i (h i) = 2 := by
    intro i
    rw [F.pair i i]
    have hdiag := congrFun (CartanMatrix.A_diag (N - 1)) i
    rw [Matrix.diag_apply] at hdiag
    rw [hdiag]
    norm_num
  have hpres := l05nOB_closure_preserves (p := p) (N := N) (h := h) (α := α) r hr hii
  obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (w := ggDepALeft N i0)
    (x := ggDepARight N i0) (y := a) (z := b) hL0R0 hab)
  refine ⟨ρ c (h i0), (α i0).comp ((ρ c)⁻¹).toLinearMap, ?_, ?_, ?_⟩
  · exact (hpres (ρ c) (l05nOB_rho_mem_closure r ρ hρ (by omega) c)).1 (h i0)
      (Submodule.subset_span ⟨i0, rfl⟩)
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact hii i0
  · intro v
    rw [← hc]
    simp only [map_mul, map_inv, hρ i0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr i0, map_sub, map_smul,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

private lemma l05nOB_lin_aux (j : ℕ) : j + 12 ≤ 3 ^ (j + 8) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    have h1 : j + 1 + 12 = (j + 12) + 1 := by omega
    rw [h1]
    calc
      (j + 12) + 1 ≤ 3 * (j + 12) := by omega
      _ ≤ 3 * 3 ^ (j + 8) := Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (j + 1 + 8) := by
            rw [show j + 1 + 8 = (j + 8) + 1 by omega, pow_succ]
            ring

private lemma l05nOB_lin (k : ℕ) (hk : 8 ≤ k) : k + 4 ≤ 3 ^ k := by
  have h := l05nOB_lin_aux (k - 8)
  have e1 : k - 8 + 12 = k + 4 := by omega
  have e2 : k - 8 + 8 = k := by omega
  rwa [e1, e2] at h

private lemma l05nOB_exp (m : ℕ) (hm : 3 ≤ m) :
    (m - 1) * (m - 2) / 2 = (m - 2) * (m - 3) / 2 + (m - 2) := by
  have h1 : (m - 1).choose 2 = (m - 1) * (m - 2) / 2 := by
    rw [Nat.choose_two_right, show m - 1 - 1 = m - 2 by omega]
  have h2 : (m - 2).choose 2 = (m - 2) * (m - 3) / 2 := by
    rw [Nat.choose_two_right, show m - 2 - 1 = m - 3 by omega]
  have hkey : (m - 1).choose 2 = (m - 2).choose 2 + (m - 2) := by
    have h := Nat.choose_succ_succ (m - 2) 1
    have e : m - 2 + 1 = m - 1 := by omega
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd] at h
    rw [e, Nat.choose_one_right] at h
    rw [h]
    exact Nat.add_comm _ _
  rw [← h1, ← h2, hkey]

theorem ggDepAOdd_order_ineq {p N : ℕ} (hp : 3 ≤ p) (hN : 11 ≤ N) :
    8 * (p ^ N * (6 * (p - 1) * Nat.factorial N)) < p ^ ((N - 2) * (N - 3) / 2) := by
  have hp0 : 0 < p := by omega
  refine Nat.le_induction (m := 11)
    (P := fun n _ => 8 * (p ^ n * (6 * (p - 1) * Nat.factorial n)) <
      p ^ ((n - 2) * (n - 3) / 2)) ?base ?step N hN
  · have hExp : (11 - 2) * (11 - 3) / 2 = 36 := by norm_num
    rw [hExp]
    have hX : 8 * (6 * (p - 1) * Nat.factorial 11) < p ^ 25 := by
      have hf : 48 * Nat.factorial 11 < 3 ^ 24 := by norm_num
      have hp1 : p - 1 < p := by omega
      calc
        8 * (6 * (p - 1) * Nat.factorial 11) = 48 * (p - 1) * Nat.factorial 11 := by
              ring
        _ < 48 * p * Nat.factorial 11 := by
              apply Nat.mul_lt_mul_of_pos_right
              · exact Nat.mul_lt_mul_of_pos_left hp1 (by norm_num)
              · norm_num
        _ = (48 * Nat.factorial 11) * p := by ring
        _ < 3 ^ 24 * p := Nat.mul_lt_mul_of_pos_right hf hp0
        _ ≤ p ^ 24 * p := Nat.mul_le_mul_right p (Nat.pow_le_pow_left hp 24)
        _ = p ^ 25 := by rw [← pow_succ]
    calc
      8 * (p ^ 11 * (6 * (p - 1) * Nat.factorial 11))
          = p ^ 11 * (8 * (6 * (p - 1) * Nat.factorial 11)) := by ring
      _ < p ^ 11 * p ^ 25 := Nat.mul_lt_mul_of_pos_left hX (pow_pos hp0 11)
      _ = p ^ 36 := by rw [← pow_add]
  · intro m hm ih
    have hexp : (m - 1) * (m - 2) / 2 = (m - 2) * (m - 3) / 2 + (m - 2) :=
      l05nOB_exp m (by omega)
    have hbound : p * (m + 1) ≤ p ^ (m - 2) := by
      have hk8 : 8 ≤ m - 3 := by omega
      have hlin : m + 1 ≤ p ^ (m - 3) := by
        have h := l05nOB_lin (m - 3) hk8
        have e : m - 3 + 4 = m + 1 := by omega
        rw [e] at h
        exact le_trans h (Nat.pow_le_pow_left hp (m - 3))
      calc
        p * (m + 1) ≤ p * p ^ (m - 3) := Nat.mul_le_mul_left p hlin
        _ = p ^ (m - 2) := by
              rw [mul_comm, ← pow_succ]
              congr 1
              omega
    have hident : 8 * (p ^ (m + 1) * (6 * (p - 1) * Nat.factorial (m + 1)))
        = (p * (m + 1)) * (8 * (p ^ m * (6 * (p - 1) * Nat.factorial m))) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    calc
      8 * (p ^ (m + 1) * (6 * (p - 1) * Nat.factorial (m + 1)))
          = (p * (m + 1)) * (8 * (p ^ m * (6 * (p - 1) * Nat.factorial m))) := hident
      _ < (p * (m + 1)) * p ^ ((m - 2) * (m - 3) / 2) :=
            Nat.mul_lt_mul_of_pos_left ih (Nat.mul_pos hp0 (by omega))
      _ ≤ p ^ (m - 2) * p ^ ((m - 2) * (m - 3) / 2) :=
            Nat.mul_le_mul_right _ hbound
      _ = p ^ ((m - 2) + (m - 2) * (m - 3) / 2) := by rw [← pow_add]
      _ = p ^ (((m + 1) - 2) * ((m + 1) - 3) / 2) := by
            congr 1
            have h1 : (m + 1) - 2 = m - 1 := by omega
            have h2 : (m + 1) - 3 = m - 2 := by omega
            rw [h1, h2, hexp]
            ring

theorem ggDepAOdd_caseI_data {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hjoin : ∃ c, αa (h c) ≠ 0)
    (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (hnH : ha ∉ Submodule.span (ZMod p) (Set.range h)) (U : Submodule (ZMod p) V)
    (hU : U = Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) ({ha} : Set V)) :
    ∃ (AU : Subgroup (↥U ≃ₗ[ZMod p] ↥U)) (ψ : Equiv.Perm (Fin N) →* ↥AU),
      Module.finrank (ZMod p) ↥U = N - 1 ∧ ZS.AbsIrred p AU ∧
        AU = Subgroup.closure {t | t ∈ AU ∧ GGLinRefl t} ∧
        Nat.card ↥AU ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) ∧ Function.Injective ψ ∧
        ∀ q : ↥U ≃ₗ[ZMod p] ↥U, q ∈ AU ↔
          ∃ a ∈ Subgroup.closure (Set.range r ∪ {ra}), ∀ w : ↥U, a (w : V) = ((q w : ↥U) : V) := by
  classical
  subst hU
  haveI : NeZero (N - 1) := ⟨by omega⟩
  let H : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h)
  let U : Submodule (ZMod p) V := H ⊔ Submodule.span (ZMod p) ({ha} : Set V)
  have hhU : ∀ i, h i ∈ U := fun i =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
  have haU : ha ∈ U := Submodule.mem_sup_right (Submodule.mem_span_singleton_self ha)
  have hdimU : Module.finrank (ZMod p) ↥U = N - 1 := by
    have hrel := ggDepA_relation F
    have hdimH : Module.finrank (ZMod p) ↥H = N - 2 := hrel.2.2
    have hinf : H ⊓ Submodule.span (ZMod p) ({ha} : Set V) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨hvH, hvS⟩ := hv
      rw [Submodule.mem_span_singleton] at hvS
      obtain ⟨c, hc⟩ := hvS
      by_cases hc0 : c = 0
      · rw [hc0, zero_smul] at hc
        exact hc.symm
      · exfalso
        apply hnH
        have hha : ha = c⁻¹ • (c • ha) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hc] at hha
        rw [hha]
        exact H.smul_mem c⁻¹ hvH
    have hspan1 : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({ha} : Set V)) = 1 := by
      rw [finrank_span_singleton]
      intro hha0
      exact hnH (by rw [hha0]; exact H.zero_mem)
    have h := Submodule.finrank_sup_add_finrank_inf_eq H
      (Submodule.span (ZMod p) ({ha} : Set V))
    rw [hinf, finrank_bot, add_zero, hdimH, hspan1] at h
    change Module.finrank (ZMod p) ↥(H ⊔ Submodule.span (ZMod p) ({ha} : Set V)) = N - 1
    omega
  let S : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hS : ∀ s ∈ S, ∀ u ∈ U, s u ∈ U := by
    intro s hs u hu
    rcases hs with ⟨i, rfl⟩ | rfl
    · rw [hr i u]
      exact U.sub_mem hu (U.smul_mem (α i u) (hhU i))
    · rw [hra u]
      exact U.sub_mem hu (U.smul_mem (αa u) haU)
  obtain ⟨res, he_apply, hcard_res, hrange_res⟩ := ggDepA_restrict U S hS
  have hraS : ra ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
  have hrS : ∀ i, r i ∈ Subgroup.closure S := fun i =>
    Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  let gU : Option (Fin (N - 1)) → (↥U ≃ₗ[ZMod p] ↥U) := fun o =>
    match o with
    | none => res ⟨ra, hraS⟩
    | some i => res ⟨r i, hrS i⟩
  have hAU_closure : res.range = Subgroup.closure (Set.range gU) := by
    have hset : Set.range gU = {t | ∃ (s : V ≃ₗ[ZMod p] V) (hs : s ∈ S),
        t = res ⟨s, Subgroup.subset_closure hs⟩} := by
      ext t; constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => exact ⟨ra, Or.inr rfl, rfl⟩
        | some i => exact ⟨r i, Or.inl ⟨i, rfl⟩, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        rcases hs with ⟨i, rfl⟩ | rfl
        · exact ⟨some i, rfl⟩
        · exact ⟨none, rfl⟩
    rw [hrange_res, hset]
  let sU : Option (Fin (N - 1)) → V := fun o =>
    match o with
    | none => ha
    | some i => h i
  have hsU : ∀ o, sU o ∈ U := by
    intro o; cases o with
    | none => exact haU
    | some i => exact hhU i
  let hU : Option (Fin (N - 1)) → ↥U := fun o => ⟨sU o, hsU o⟩
  let αU : Option (Fin (N - 1)) → Module.Dual (ZMod p) ↥U := fun o =>
    match o with
    | none => αa.comp U.subtype
    | some i => (α i).comp U.subtype
  have hspan_range : Submodule.span (ZMod p) (Set.range sU) = U := by
    have hrange : Set.range sU = Set.range h ∪ ({ha} : Set V) := by
      ext v; constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => exact Or.inr rfl
        | some i => exact Or.inl ⟨i, rfl⟩
      · rintro (⟨i, rfl⟩ | rfl)
        · exact ⟨some i, rfl⟩
        · exact ⟨none, rfl⟩
    rw [hrange, Submodule.span_union]
  have hspanU : Submodule.span (ZMod p) (Set.range hU) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff U hsU).mpr hspan_range
  have hαdiag : ∀ i, α i (h i) = 2 := by
    intro i
    rw [F.pair i i]
    have hdiag : CartanMatrix.A (N - 1) i i = 2 := by
      simp [CartanMatrix.A, Matrix.of_apply]
    rw [hdiag]
    norm_num
  have hαU : ∀ o, αU o (hU o) = 2 := by
    intro o; cases o with
    | none => exact hαa
    | some i => exact hαdiag i
  have hgUapply : ∀ o u, gU o u = u - αU o u • hU o := by
    intro o u
    cases o with
    | none =>
      apply Subtype.ext
      show (((res ⟨ra, hraS⟩) u : ↥U) : V) = ((u - αU none u • hU none : ↥U) : V)
      rw [he_apply]
      show ra (u : V) = ((u - αU none u • hU none : ↥U) : V)
      rw [hra]
      simp only [Submodule.coe_sub, Submodule.coe_smul, αU, hU, sU, LinearMap.comp_apply,
        Submodule.subtype_apply]
    | some i =>
      apply Subtype.ext
      show (((res ⟨r i, hrS i⟩) u : ↥U) : V) = ((u - αU (some i) u • hU (some i) : ↥U) : V)
      rw [he_apply]
      show r i (u : V) = ((u - αU (some i) u • hU (some i) : ↥U) : V)
      rw [hr]
      simp only [Submodule.coe_sub, Submodule.coe_smul, αU, hU, sU, LinearMap.comp_apply,
        Submodule.subtype_apply]
  have hkerU : ∀ w : ↥U, (∀ o, αU o w = 0) → w = 0 := by
    intro w hw0
    have hfix := F.fix (w : V) (fun i => hw0 (some i))
    rw [Submodule.mem_span_singleton] at hfix
    obtain ⟨c, hc⟩ := hfix
    have hcz : c = 0 := by
      have h0 : c * αa x = 0 := by
        have h1 : αa (w : V) = 0 := hw0 none
        rw [← hc, map_smul, smul_eq_mul] at h1
        exact h1
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hw
    apply Subtype.ext
    rw [← hc, hcz, zero_smul]
    rfl
  let R : Option (Fin (N - 1)) → Option (Fin (N - 1)) → Prop :=
    fun a b => αU a (hU b) ≠ 0 ∧ αU b (hU a) ≠ 0
  have hneg1 : (-1 : ZMod p) ≠ 0 := by
    rw [neg_ne_zero]; exact one_ne_zero
  have hA_succ : ∀ i j : Fin (N - 1), i.val + 1 = j.val →
      (CartanMatrix.A (N - 1) i j : ZMod p) = -1 := by
    intro i j hij
    have hne : i ≠ j := by intro hh; have := congrArg Fin.val hh; omega
    have hAi : CartanMatrix.A (N - 1) i j = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hne, if_pos (Or.inl hij)]
    rw [hAi]; norm_num
  have hA_succ' : ∀ i j : Fin (N - 1), i.val + 1 = j.val →
      (CartanMatrix.A (N - 1) j i : ZMod p) = -1 := by
    intro i j hij
    have hne : j ≠ i := by intro hh; have := congrArg Fin.val hh; omega
    have hAi : CartanMatrix.A (N - 1) j i = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hne, if_pos (Or.inr hij)]
    rw [hAi]; norm_num
  have hedge : ∀ i j : Fin (N - 1), i.val + 1 = j.val → R (some i) (some j) := by
    intro i j hij
    refine ⟨?_, ?_⟩
    · show α i (h j) ≠ 0
      rw [F.pair i j, hA_succ i j hij]
      exact hneg1
    · show α j (h i) ≠ 0
      rw [F.pair j i, hA_succ' i j hij]
      exact hneg1
  have hchain : ∀ j : Fin (N - 1),
      Relation.ReflTransGen R (some (0 : Fin (N - 1))) (some j) := by
    intro j
    refine Fin.strong_induction_on
      (motive := fun j => Relation.ReflTransGen R (some 0) (some j)) ?_ j
    intro j ih
    by_cases hj : j = 0
    · subst hj; exact Relation.ReflTransGen.refl
    · have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun hh => hj (Fin.ext hh))
      let j' : Fin (N - 1) := ⟨j.val - 1, by omega⟩
      have hlt : j' < j := by
        show j.val - 1 < j.val
        omega
      have hval : j'.val + 1 = j.val := by
        show j.val - 1 + 1 = j.val
        omega
      exact (ih j' hlt).tail (hedge j' j hval)
  obtain ⟨c, hc⟩ := hjoin
  have hRc_none : R (some c) none := by
    refine ⟨?_, ?_⟩
    · show α c ha ≠ 0
      intro h0
      exact hc (ggDepA_pair_zero_symm hp2 (Subgroup.closure S) hnt
        (hrS c) hraS (hr c) hra (hαdiag c) hαa h0)
    · show αa (h c) ≠ 0
      exact hc
  haveI : Std.Symm R := ⟨fun a b hh => ⟨hh.2, hh.1⟩⟩
  have hsymm : ∀ {a b : Option (Fin (N - 1))},
      Relation.ReflTransGen R a b → Relation.ReflTransGen R b a :=
    fun h => Std.Symm.symm _ _ h
  have hnone_c : Relation.ReflTransGen R none (some c) :=
    Relation.ReflTransGen.single ⟨hRc_none.2, hRc_none.1⟩
  have hconnU : ∀ o o' : Option (Fin (N - 1)), Relation.ReflTransGen R o o' := by
    intro o o'
    cases o with
    | none =>
      cases o' with
      | none => exact Relation.ReflTransGen.refl
      | some j => exact hnone_c.trans ((hsymm (hchain c)).trans (hchain j))
    | some i =>
      cases o' with
      | none =>
        exact hsymm (hnone_c.trans ((hsymm (hchain c)).trans (hchain i)))
      | some j =>
        exact (hsymm (hnone_c.trans ((hsymm (hchain c)).trans (hchain i)))).trans
          (hnone_c.trans ((hsymm (hchain c)).trans (hchain j)))
  have hirr : ZS.AbsIrred p res.range :=
    ggRC_absIrred_of_connected hp2 gU hU αU hgUapply hαU hspanU hkerU hconnU res.range hAU_closure
  have hreflU : ∀ o : Option (Fin (N - 1)), GGLinRefl (gU o) := by
    intro o
    rw [ggDepA_linRefl_iff hp2]
    exact ⟨hU o, αU o, hαU o, fun v => hgUapply o v⟩
  have hgen : res.range =
      Subgroup.closure {t : ↥U ≃ₗ[ZMod p] ↥U | t ∈ res.range ∧ GGLinRefl t} := by
    rw [hAU_closure]
    apply le_antisymm
    · apply Subgroup.closure_mono
      intro x hx
      obtain ⟨o, rfl⟩ := hx
      exact ⟨Subgroup.subset_closure (Set.mem_range_self o), hreflU o⟩
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
  have hcardAU : Nat.card ↥res.range ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) :=
    le_trans hcard_res hcard
  obtain ⟨ρ, hρr, hρA, hρx, hρf⟩ := ggDepAOdd_perm_embed hp2 hN F r hr
  let ρ' : Equiv.Perm (Fin N) →* ↥(Subgroup.closure S) :=
    { toFun := fun σ => ⟨ρ σ, Subgroup.closure_mono Set.subset_union_left (hρA σ)⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun a b => Subtype.ext (map_mul ρ a b) }
  let ψ : Equiv.Perm (Fin N) →* ↥(res.range) := res.rangeRestrict.comp ρ'
  have hψinj : Function.Injective ψ := by
    intro σ τ hστ
    have hfix : ∀ i, ρ (τ⁻¹ * σ) (h i) = h i := by
      intro i
      have hval : (res (ρ' σ) : ↥U ≃ₗ[ZMod p] ↥U) = res (ρ' τ) := by
        have hh := congrArg Subtype.val hστ
        simpa [ψ, MonoidHom.comp_apply] using hh
      have h1 : (((res (ρ' σ)) (hU (some i)) : ↥U) : V) =
          (((res (ρ' τ)) (hU (some i)) : ↥U) : V) :=
        congrArg (fun (e : ↥U ≃ₗ[ZMod p] ↥U) => ((e (hU (some i)) : ↥U) : V)) hval
      have h3 : ρ σ (h i) = ρ τ (h i) := by
        rw [he_apply, he_apply] at h1
        change ρ σ (h i) = ρ τ (h i) at h1
        exact h1
      calc ρ (τ⁻¹ * σ) (h i)
          = ((ρ τ)⁻¹ * ρ σ) (h i) := by rw [map_mul, map_inv]
        _ = (ρ τ)⁻¹ (ρ σ (h i)) := by rw [LinearEquiv.mul_apply]
        _ = (ρ τ)⁻¹ (ρ τ (h i)) := by rw [h3]
        _ = h i := by simp
    have hone : τ⁻¹ * σ = 1 := hρf (τ⁻¹ * σ) hfix
    exact (inv_mul_eq_one.mp hone).symm
  have hmem : ∀ q : ↥U ≃ₗ[ZMod p] ↥U, q ∈ res.range ↔
      ∃ a ∈ Subgroup.closure S, ∀ w : ↥U, a (w : V) = ((q w : ↥U) : V) := by
    intro q
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, fun w => (he_apply a w).symm⟩
    · rintro ⟨a, ha, haq⟩
      refine MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, ?_⟩
      ext w
      exact (he_apply ⟨a, ha⟩ w).trans (haq w)
  exact ⟨res.range, ψ, hdimU, hirr, hgen, hcardAU, hψinj, hmem⟩

private theorem l05nOC_exclude (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 11 ≤ N) (hpN : p ∣ N) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (hdim : Module.finrank (ZMod p) U = N - 1)
    (AU : Subgroup (U ≃ₗ[ZMod p] U)) (hirr : ZS.AbsIrred p AU)
    (hgen : AU = Subgroup.closure {t | t ∈ AU ∧ GGLinRefl t})
    (hcard : Nat.card ↥AU ≤ p ^ N * (6 * (p - 1) * Nat.factorial N))
    (ψ : Equiv.Perm (Fin N) →* ↥AU) (hψ : Function.Injective ψ) : False := by
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  obtain himp | hclass | ⟨hndvd, _e1, _he1⟩ | ⟨hdvd, _e2, _he2⟩ :=
    hKG p hp2 U (N - 1) hdim (by omega) AU hirr hgen
  ·
    obtain ⟨b, hmon⟩ :=
      ggRC_monomial_of_imprimitive (p := p) (n := N - 1) hdim AU hirr hgen himp
    obtain ⟨π, _hπ, _hπker, hπcomm, _hπp⟩ := ggRC_monomial_hom b AU hmon
    let π' : Equiv.Perm (Fin N) →* Equiv.Perm (Fin (N - 1)) := π.comp ψ
    have hπ'comm : IsMulCommutative π'.ker := by
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      apply hψ
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hπcomm
        ⟨ψ (a : Equiv.Perm (Fin N)), a.2⟩
        ⟨ψ (b : Equiv.Perm (Fin N)), b.2⟩)
    exact ggRC_perm_not_monomial (N := N) (m := N - 1) (by omega) (by omega) π' hπ'comm
  ·
    have hle : (N - 2) * (N - 3) / 2 ≤ (N - 1) * (N - 1 - 1) / 2 := by
      apply Nat.div_le_div_right
      have h1 : N - 1 - 1 = N - 2 := by omega
      rw [h1]
      calc (N - 2) * (N - 3) ≤ (N - 2) * (N - 1) :=
            Nat.mul_le_mul_left (N - 2) (by omega)
        _ = (N - 1) * (N - 2) := Nat.mul_comm (N - 2) (N - 1)
    have hpow : p ^ ((N - 2) * (N - 3) / 2) ≤ p ^ ((N - 1) * (N - 1 - 1) / 2) :=
      Nat.pow_le_pow_right (by omega) hle
    have hchain : p ^ ((N - 2) * (N - 3) / 2) ≤
        8 * (p ^ N * (6 * (p - 1) * Nat.factorial N)) :=
      hpow.trans (hclass.trans (Nat.mul_le_mul_left 8 hcard))
    exact absurd (lt_of_le_of_lt hchain (ggDepAOdd_order_ineq hp3 hN)) (lt_irrefl _)
  ·
    have hN1 : N - 1 + 1 = N := by omega
    exact hndvd (hN1.symm ▸ hpN)
  ·
    have hN2 : N - 1 + 2 = N + 1 := by omega
    have hdvd' : p ∣ N + 1 := hN2 ▸ hdvd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hpN).mp hdvd'
    have hp1 : ¬ p ∣ 1 := by
      intro h
      have := Nat.le_of_dvd (by norm_num : 0 < 1) h
      omega
    exact hp1 h1

theorem ggDepAOdd_caseI_false (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hN : 11 ≤ N) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hjoin : ∃ c, αa (h c) ≠ 0)
    (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (hnH : ha ∉ Submodule.span (ZMod p) (Set.range h)) : False := by
  let U : Submodule (ZMod p) V :=
    Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) ({ha} : Set V)
  obtain ⟨AU, ψ, hdim, hirr, hgen, hcardU, hψ, -⟩ :=
    ggDepAOdd_caseI_data hp2 (by omega) F r hr ra ha αa hra hαa hjoin hw hnt hcard hnH U rfl
  haveI : Module.Finite (ZMod p) ↥U :=
    Module.Finite.of_injective (Submodule.subtype U) U.subtype_injective
  exact l05nOC_exclude hKG hp2 hN F.dvd hdim AU hirr hgen hcardU ψ hψ

private theorem l05nOD_cartan_adj (n : ℕ) {i j : Fin n}
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) (hne : i ≠ j) :
    CartanMatrix.A n i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hne, if_pos h]

private theorem l05nOD_cartan_self (n : ℕ) (i : Fin n) : CartanMatrix.A n i i = 2 := by
  simp [CartanMatrix.A]

theorem ggDepAOdd_caseII_data {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (H : Submodule (ZMod p) V) (hHdef : H = Submodule.span (ZMod p) (Set.range h))
    (hH : ha ∈ H) (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V))
    (hρA : ∀ σ, ρ σ ∈ Subgroup.closure (Set.range r))
    (hρfaith : ∀ σ, (∀ i, ρ σ (h i) = h i) → σ = 1) :
    ∃ (AH : Subgroup (↥H ≃ₗ[ZMod p] ↥H)) (ψ : Equiv.Perm (Fin N) →* ↥AH)
      (γ : ↥H ≃ₗ[ZMod p] ↥H),
      Module.finrank (ZMod p) ↥H = N - 2 ∧ ZS.AbsIrred p AH ∧
        AH = Subgroup.closure {t | t ∈ AH ∧ GGLinRefl t} ∧
        Nat.card ↥AH ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) ∧ Function.Injective ψ ∧
        (∀ (σ : Equiv.Perm (Fin N)) (v : ↥H), ((((ψ σ : ↥AH) : ↥H ≃ₗ[ZMod p] ↥H) v : ↥H) : V) =
          ρ σ (v : V)) ∧
        γ ∈ AH ∧ (∀ v : ↥H, ((γ v : ↥H) : V) = ra (v : V)) ∧
        ∀ q : ↥H ≃ₗ[ZMod p] ↥H, q ∈ AH ↔
          ∃ a ∈ Subgroup.closure (Set.range r ∪ {ra}), ∀ w : ↥H, a (w : V) = ((q w : ↥H) : V) := by
  obtain ⟨-, hx_span, hdimSpan⟩ := ggDepA_relation F
  have hmemH : ∀ i, h i ∈ H := fun i => by
    rw [hHdef]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hxH : x ∉ H := by
    rw [hHdef]
    exact hx_span
  have hdimH : Module.finrank (ZMod p) ↥H = N - 2 := by
    rw [hHdef]
    exact hdimSpan
  let S : Set (V ≃ₗ[ZMod p] V) := Set.range r ∪ {ra}
  have hS : ∀ s ∈ S, ∀ u ∈ H, s u ∈ H := by
    intro s hs u hu
    rcases hs with ⟨i, rfl⟩ | rfl
    · rw [hr i u]
      exact H.sub_mem hu (H.smul_mem (α i u) (hmemH i))
    · rw [hra u]
      exact H.sub_mem hu (H.smul_mem (αa u) hH)
  obtain ⟨res, hres_apply, hres_card, hres_range⟩ := ggDepA_restrict H S hS
  let A : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure S
  let AH : Subgroup (↥H ≃ₗ[ZMod p] ↥H) := MonoidHom.range res
  have hcardAH : Nat.card ↥AH ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) :=
    le_trans hres_card hcard
  let hU : Option (Fin (N - 1)) → ↥H :=
    fun o => o.elim ⟨ha, hH⟩ (fun i => ⟨h i, hmemH i⟩)
  let αU : Option (Fin (N - 1)) → Module.Dual (ZMod p) ↥H :=
    fun o => o.elim (αa.comp H.subtype) (fun i => (α i).comp H.subtype)
  let gH : Option (Fin (N - 1)) → (↥H ≃ₗ[ZMod p] ↥H) :=
    fun o => o.elim (res ⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩)
      (fun i => res ⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩)
  have hgH_mem_AH : ∀ o : Option (Fin (N - 1)), gH o ∈ AH := by
    intro o
    cases o with
    | none =>
      exact MonoidHom.mem_range.mpr
        ⟨⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩, rfl⟩
    | some i =>
      exact MonoidHom.mem_range.mpr
        ⟨⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩, rfl⟩
  have hclosA : AH = Subgroup.closure (Set.range gH) := by
    apply le_antisymm
    · change MonoidHom.range res ≤ Subgroup.closure (Set.range gH)
      rw [hres_range, Subgroup.closure_le]
      intro t ht
      obtain ⟨s, hs, rfl⟩ := ht
      rcases hs with ⟨i, rfl⟩ | rfl
      · exact Subgroup.subset_closure ⟨some i, congrArg res (Subtype.ext rfl)⟩
      · exact Subgroup.subset_closure ⟨none, congrArg res (Subtype.ext rfl)⟩
    · rw [Subgroup.closure_le]
      intro t ht
      obtain ⟨o, rfl⟩ := ht
      exact hgH_mem_AH o
  have hαU : ∀ o : Option (Fin (N - 1)), αU o (hU o) = 2 := by
    intro o
    cases o with
    | none =>
      simpa only [αU, hU, Option.elim_none, LinearMap.comp_apply, Submodule.subtype_apply]
        using hαa
    | some i =>
      have hA : ((CartanMatrix.A (N - 1) i i : ℤ) : ZMod p) = 2 := by
        rw [l05nOD_cartan_self (N - 1) i]
        simp
      simpa only [αU, hU, Option.elim_some, LinearMap.comp_apply, Submodule.subtype_apply,
        F.pair i i, hA]
  have hg : ∀ (o : Option (Fin (N - 1))) (w : ↥H), gH o w = w - αU o w • hU o := by
    intro o w
    cases o with
    | none =>
      apply Subtype.ext
      change ((res ⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩ w : ↥H) : V) =
        ((w - αU none w • hU none : ↥H) : V)
      rw [hres_apply]
      show ra (w : V) = ((w - αU none w • hU none : ↥H) : V)
      rw [hra (w : V)]
      simp only [Submodule.coe_sub, Submodule.coe_smul, αU, hU, Option.elim_none,
        LinearMap.comp_apply, Submodule.subtype_apply]
    | some i =>
      apply Subtype.ext
      change ((res ⟨r i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩ w : ↥H) : V) =
        ((w - αU (some i) w • hU (some i) : ↥H) : V)
      rw [hres_apply]
      show r i (w : V) = ((w - αU (some i) w • hU (some i) : ↥H) : V)
      rw [hr i (w : V)]
      simp only [Submodule.coe_sub, Submodule.coe_smul, αU, hU, Option.elim_some,
        LinearMap.comp_apply, Submodule.subtype_apply]
  have hreflU : ∀ o : Option (Fin (N - 1)), GGLinRefl (gH o) :=
    fun o => (ggDepA_linRefl_iff hp2 (gH o)).mpr ⟨hU o, αU o, hαU o, hg o⟩
  have hsome_span :
      Submodule.span (ZMod p) (Set.range (fun i => (⟨h i, hmemH i⟩ : ↥H))) = ⊤ := by
    have heq : H.subtype '' Set.range (fun i => (⟨h i, hmemH i⟩ : ↥H)) = Set.range h := by
      ext v
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨h i, hmemH i⟩, ⟨i, rfl⟩, rfl⟩
    have hmap : Submodule.map H.subtype
        (Submodule.span (ZMod p) (Set.range (fun i => (⟨h i, hmemH i⟩ : ↥H)))) =
        Submodule.map H.subtype (⊤ : Submodule (ZMod p) ↥H) := by
      rw [← Submodule.span_image (f := H.subtype)]
      rw [heq, hHdef, Submodule.map_top, Submodule.range_subtype]
    exact Submodule.map_injective_of_injective Subtype.val_injective hmap
  have hspanU : Submodule.span (ZMod p) (Set.range hU) = ⊤ := by
    apply le_antisymm le_top
    rw [← hsome_span]
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨some i, rfl⟩
  have hkerU : ∀ w : ↥H, (∀ o, αU o w = 0) → w = 0 := by
    intro w hw
    have hwSpan : (w : V) ∈ Submodule.span (ZMod p) ({x} : Set V) := by
      apply F.fix
      intro i
      have h1 := hw (some i)
      simpa only [αU, Option.elim_some, LinearMap.comp_apply, Submodule.subtype_apply] using h1
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwSpan
    by_cases hc0 : c = 0
    · apply Subtype.ext
      show (w : V) = (0 : V)
      rw [← hc, hc0, zero_smul]
    · exfalso
      apply hxH
      have hmem : c⁻¹ • (w : V) ∈ H := H.smul_mem _ w.2
      have heq : c⁻¹ • (w : V) = x := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rwa [heq] at hmem
  have haSpan : ha ∈ Submodule.span (ZMod p) (Set.range h) := by
    simpa [hHdef] using hH
  obtain ⟨bcoef, hbcoef⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp haSpan
  have htwo : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hsum_ne : ∑ i : Fin (N - 1), bcoef i * αa (h i) ≠ 0 := by
    have hsum : ∑ i : Fin (N - 1), bcoef i * αa (h i) = αa ha := by
      rw [← hbcoef, map_sum]
      simp only [map_smul, smul_eq_mul]
    rw [hsum, hαa]
    exact htwo
  obtain ⟨c, -, hcmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hαac : αa (h c) ≠ 0 := fun h0 => hcmul (by rw [h0, mul_zero])
  have hpair_self : ∀ i : Fin (N - 1), α i (h i) = 2 := by
    intro i
    have hA : ((CartanMatrix.A (N - 1) i i : ℤ) : ZMod p) = 2 := by
      rw [l05nOD_cartan_self (N - 1) i]
      simp
    rw [F.pair i i, hA]
  have hcne : α c ha ≠ 0 := by
    intro h0
    exact hαac (ggDepA_pair_zero_symm hp2 A hnt
      (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
      (Subgroup.subset_closure (Or.inr rfl))
      (hr c) hra (hpair_self c) hαa h0)
  let E : Option (Fin (N - 1)) → Option (Fin (N - 1)) → Prop :=
    fun a b => αU a (hU b) ≠ 0 ∧ αU b (hU a) ≠ 0
  have hsymmE : ∀ a b, E a b → E b a := fun a b h => h.symm
  have hpair_adj : ∀ (k : ℕ) (hk : k < N - 1) (hk1 : k + 1 < N - 1),
      E (some ⟨k, hk⟩) (some ⟨k + 1, hk1⟩) := by
    intro k hk hk1
    have hne : (⟨k, hk⟩ : Fin (N - 1)) ≠ ⟨k + 1, hk1⟩ := by
      intro h
      have h1 : k = k + 1 := by simpa using congrArg Fin.val h
      omega
    have hA1 : ((CartanMatrix.A (N - 1) (⟨k, hk⟩ : Fin (N - 1)) ⟨k + 1, hk1⟩ : ℤ) :
        ZMod p) = -1 := by
      rw [l05nOD_cartan_adj (N - 1) (Or.inl rfl) hne]
      simp
    have hA2 : ((CartanMatrix.A (N - 1) (⟨k + 1, hk1⟩ : Fin (N - 1)) ⟨k, hk⟩ : ℤ) :
        ZMod p) = -1 := by
      rw [l05nOD_cartan_adj (N - 1) (Or.inr rfl) hne.symm]
      simp
    constructor
    · change α ⟨k, hk⟩ (h ⟨k + 1, hk1⟩) ≠ 0
      rw [F.pair (⟨k, hk⟩) (⟨k + 1, hk1⟩), hA1]
      exact neg_ne_zero.mpr one_ne_zero
    · change α ⟨k + 1, hk1⟩ (h ⟨k, hk⟩) ≠ 0
      rw [F.pair (⟨k + 1, hk1⟩) (⟨k, hk⟩), hA2]
      exact neg_ne_zero.mpr one_ne_zero
  have hpair_dn : ∀ (k : ℕ) (hk : k < N - 1) (hk1 : k + 1 < N - 1),
      E (some ⟨k + 1, hk1⟩) (some ⟨k, hk⟩) :=
    fun k hk hk1 => hsymmE _ _ (hpair_adj k hk hk1)
  have hbase_lt : 0 < N - 1 := by omega
  let base : Fin (N - 1) := ⟨0, hbase_lt⟩
  have hup : ∀ (k : ℕ) (hk : k < N - 1),
      Relation.ReflTransGen E (some base) (some ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hbase : (⟨0, hk⟩ : Fin (N - 1)) = base := Fin.ext rfl
      rw [hbase]
    | succ k ih =>
      intro hk
      have hk' : k < N - 1 := by omega
      exact (ih hk').tail (hpair_adj k hk' hk)
  have hdn : ∀ (k : ℕ) (hk : k < N - 1),
      Relation.ReflTransGen E (some ⟨k, hk⟩) (some base) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have hbase : (⟨0, hk⟩ : Fin (N - 1)) = base := Fin.ext rfl
      rw [hbase]
    | succ k ih =>
      intro hk
      have hk' : k < N - 1 := by omega
      exact (Relation.ReflTransGen.single (hpair_dn k hk' hk)).trans (ih hk')
  have hconn_none : E none (some c) := by
    constructor
    · change αa (h c) ≠ 0
      exact hαac
    · change α c ha ≠ 0
      exact hcne
  have hnone_start : Relation.ReflTransGen E none (some base) :=
    (Relation.ReflTransGen.single hconn_none).trans (hdn c.val c.isLt)
  have hfrom_none : ∀ o : Option (Fin (N - 1)), Relation.ReflTransGen E none o := by
    intro o
    cases o with
    | none => exact Relation.ReflTransGen.refl
    | some b => exact hnone_start.trans (hup b.val b.isLt)
  have hsome0_none : Relation.ReflTransGen E (some base) none :=
    (hup c.val c.isLt).tail (hsymmE none (some c) hconn_none)
  have hto_none : ∀ o : Option (Fin (N - 1)), Relation.ReflTransGen E o none := by
    intro o
    cases o with
    | none => exact Relation.ReflTransGen.refl
    | some b => exact (hdn b.val b.isLt).trans hsome0_none
  have hconn : ∀ o o' : Option (Fin (N - 1)), Relation.ReflTransGen E o o' :=
    fun o o' => (hto_none o).trans (hfrom_none o')
  have hirr : ZS.AbsIrred p AH :=
    ggRC_absIrred_of_connected hp2 gH hU αU hg hαU hspanU hkerU hconn AH hclosA
  have hgen : AH = Subgroup.closure {t | t ∈ AH ∧ GGLinRefl t} := by
    apply le_antisymm
    · have hsub : Set.range gH ⊆ {t | t ∈ AH ∧ GGLinRefl t} := by
        intro x hx
        obtain ⟨o, rfl⟩ := hx
        exact ⟨hgH_mem_AH o, hreflU o⟩
      have hle := Subgroup.closure_mono hsub
      rwa [← hclosA] at hle
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
  have hρA' : ∀ σ : Equiv.Perm (Fin N), ρ σ ∈ A := fun σ =>
    Subgroup.closure_mono Set.subset_union_left (hρA σ)
  let ρA : Equiv.Perm (Fin N) →* A :=
    { toFun := fun σ => ⟨ρ σ, hρA' σ⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun σ τ => Subtype.ext (map_mul ρ σ τ) }
  let ψ : Equiv.Perm (Fin N) →* ↥AH :=
    { toFun := fun σ => ⟨res (ρA σ), MonoidHom.mem_range.mpr ⟨ρA σ, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        show res (ρA 1) = (1 : ↥H ≃ₗ[ZMod p] ↥H)
        rw [map_one, map_one]
      map_mul' := fun σ τ => by
        apply Subtype.ext
        show res (ρA (σ * τ)) = res (ρA σ) * res (ρA τ)
        rw [map_mul ρA σ τ, map_mul res (ρA σ) (ρA τ)] }
  have hψval : ∀ (σ : Equiv.Perm (Fin N)) (v : ↥H),
      ((((ψ σ : ↥AH) : ↥H ≃ₗ[ZMod p] ↥H) v : ↥H) : V) = ρ σ (v : V) := by
    intro σ v
    show ((res (ρA σ) v : ↥H) : V) = ρ σ (v : V)
    rw [hres_apply]
    rfl
  have hψ_inj : Function.Injective ψ := by
    intro σ τ hστ
    have hker : σ * τ⁻¹ = 1 := by
      apply hρfaith
      intro i
      have h1 : ψ (σ * τ⁻¹) = 1 := by
        rw [map_mul, hστ, map_inv]
        exact mul_inv_cancel (ψ τ)
      have hv := hψval (σ * τ⁻¹) (hU (some i))
      rw [h1] at hv
      simpa [hU] using hv.symm
    exact mul_inv_eq_one.mp hker
  let γ : ↥H ≃ₗ[ZMod p] ↥H := res ⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩
  have hγmem : γ ∈ AH :=
    MonoidHom.mem_range.mpr ⟨⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩, rfl⟩
  have hγapply : ∀ v : ↥H, ((γ v : ↥H) : V) = ra (v : V) := by
    intro v
    exact hres_apply ⟨ra, Subgroup.subset_closure (Or.inr rfl)⟩ v
  have hmem : ∀ q : ↥H ≃ₗ[ZMod p] ↥H, q ∈ AH ↔
      ∃ a ∈ Subgroup.closure S, ∀ w : ↥H, a (w : V) = ((q w : ↥H) : V) := by
    intro q
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, fun w => (hres_apply a w).symm⟩
    · rintro ⟨a, ha, haq⟩
      refine MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, ?_⟩
      ext w
      exact (hres_apply ⟨a, ha⟩ w).trans (haq w)
  exact ⟨AH, ψ, γ, hdimH, hirr, hgen, hcardAH, hψ_inj, hψval, hγmem, hγapply, hmem⟩

private theorem l05nOD_classify (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 11 ≤ N) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (hdim : Module.finrank (ZMod p) U = N - 2)
    (AU : Subgroup (U ≃ₗ[ZMod p] U)) (hirr : ZS.AbsIrred p AU)
    (hgen : AU = Subgroup.closure {t | t ∈ AU ∧ GGLinRefl t})
    (hcard : Nat.card ↥AU ≤ p ^ N * (6 * (p - 1) * Nat.factorial N))
    (ψ : Equiv.Perm (Fin N) →* ↥AU) (hψ : Function.Injective ψ)
    (hsw : ∀ a b : Fin N, a ≠ b → GGLinRefl ((ψ (Equiv.swap a b) : ↥AU) : U ≃ₗ[ZMod p] U)) :
    ∀ t ∈ AU, GGLinRefl t → ∃ σ : Equiv.Perm (Fin N), σ.IsSwap ∧
      ((ψ σ : ↥AU) : U ≃ₗ[ZMod p] U) = t := by
  intro t htAU htRefl
  have hp3 : 3 ≤ p := by
    have h2le : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h2lt : 2 < p := lt_of_le_of_ne h2le (Ne.symm hp2)
    omega
  obtain himp | hclass | ⟨_hndvd, e1, _he1⟩ | ⟨_hdvd, e2, _he2⟩ :=
    hKG p hp2 U (N - 2) hdim (by omega) AU hirr hgen
  ·
    exfalso
    obtain ⟨bU, hmon⟩ := ggRC_monomial_of_imprimitive hdim AU hirr hgen himp
    obtain ⟨π, _hπ, _hπker, hπcomm, _hπp⟩ := ggRC_monomial_hom bU AU hmon
    have hπ'comm : IsMulCommutative (π.comp ψ).ker := by
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      apply hψ
      show ψ ((a : Equiv.Perm (Fin N)) * (b : Equiv.Perm (Fin N))) =
        ψ ((b : Equiv.Perm (Fin N)) * (a : Equiv.Perm (Fin N)))
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hπcomm
        ⟨ψ (a : Equiv.Perm (Fin N)), MonoidHom.mem_ker.mpr a.2⟩
        ⟨ψ (b : Equiv.Perm (Fin N)), MonoidHom.mem_ker.mpr b.2⟩)
    exact ggRC_perm_not_monomial (N := N) (m := N - 2) (by omega) (by omega)
      (π.comp ψ) hπ'comm
  ·
    exfalso
    have h1 : 8 * Nat.card AU < p ^ ((N - 2) * (N - 3) / 2) :=
      lt_of_le_of_lt (Nat.mul_le_mul_left 8 hcard) (ggDepAOdd_order_ineq hp3 hN)
    have h2 : p ^ ((N - 2) * (N - 3) / 2) ≤ 8 * Nat.card AU := by
      have hh := hclass
      rwa [show N - 2 - 1 = N - 3 by omega] at hh
    exact absurd h1 (not_lt.mpr h2)
  ·
    exfalso
    let ψ1 : Equiv.Perm (Fin N) →* Equiv.Perm (Fin (N - 2 + 1)) := e1.toMonoidHom.comp ψ
    have hψ1inj : Function.Injective ψ1 := e1.injective.comp hψ
    have hle : Nat.card (Equiv.Perm (Fin N)) ≤
        Nat.card (Equiv.Perm (Fin (N - 2 + 1))) :=
      Nat.card_le_card_of_injective ψ1 hψ1inj
    have hleN : Nat.card (Equiv.Perm (Fin N)) = Nat.factorial N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have hleM : Nat.card (Equiv.Perm (Fin (N - 2 + 1))) = Nat.factorial (N - 1) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin,
        show N - 2 + 1 = N - 1 by omega]
    have hle' : Nat.factorial N ≤ Nat.factorial (N - 1) := by
      rw [hleN, hleM] at hle
      exact hle
    have hlt : Nat.factorial (N - 1) < Nat.factorial N :=
      Nat.factorial_lt_of_lt (by omega) (by omega)
    exact absurd hle' (not_le.mpr hlt)
  ·
    have hN2 : N - 2 + 2 = N := by omega
    let ψ' : Equiv.Perm (Fin N) →* Equiv.Perm (Fin (N - 2 + 2)) := e2.toMonoidHom.comp ψ
    have hψ'inj : Function.Injective ψ' := e2.injective.comp hψ
    have hcardPermN : Nat.card (Equiv.Perm (Fin N)) = Nat.factorial N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have hcardPermN2 : Nat.card (Equiv.Perm (Fin (N - 2 + 2))) = Nat.factorial N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, hN2]
    have hcardψ' : Nat.card (Equiv.Perm (Fin N)) =
        Nat.card (Equiv.Perm (Fin (N - 2 + 2))) := by
      rw [hcardPermN, hcardPermN2]
    have hbijψ' : Function.Bijective ψ' :=
      (Nat.bijective_iff_injective_and_card ψ').mpr ⟨hψ'inj, hcardψ'⟩
    obtain ⟨τ, hτ⟩ := hbijψ'.surjective (e2 ⟨t, htAU⟩)
    have hψτ : ψ τ = ⟨t, htAU⟩ := e2.injective hτ
    let T : Equiv.Perm (Fin N) →* (U ≃ₗ[ZMod p] U) := AU.subtype.comp ψ
    have hTinj : Function.Injective T := by
      intro a b hab
      exact hψ (Subtype.ext hab)
    have hswLin : ∀ x y : Fin N, x ≠ y → IsLinRefl (T (Equiv.swap x y)) := by
      intro x y hxy
      exact (ggDepA_linRefl_iff hp2 (T (Equiv.swap x y))).mp (hsw x y hxy)
    have hTτ : T τ = t := by
      change ((ψ τ : ↥AU) : U ≃ₗ[ZMod p] U) = t
      rw [hψτ]
    have hLin : IsLinRefl (T τ) := by
      rw [hTτ]
      exact (ggDepA_linRefl_iff hp2 t).mp htRefl
    exact ⟨τ, isSwap_of_isLinRefl hp2 T hTinj hswLin hLin, hTτ⟩

private theorem l05nOD_end {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hH : ha ∈ Submodule.span (ZMod p) (Set.range h))
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i, ρ (Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = r i)
    (hρA : ∀ σ, ρ σ ∈ Subgroup.closure (Set.range r)) (hρx : ∀ σ, ρ σ x = x) {a b : Fin N}
    (hab : a ≠ b)
    (hrestr : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), ra v = ρ (Equiv.swap a b) v) :
    False := by
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  obtain ⟨t, β, htH, hβt, hβ⟩ := ggDepAOdd_perm_swap_refl hp2 hN F r hr ρ hρ hab
  have ht0 : t ≠ 0 := by
    intro h0
    have hz : β (0 : V) = (2 : ZMod p) := by simpa [h0] using hβt
    rw [map_zero] at hz
    exact h2 hz.symm
  have ha0 : ha ≠ 0 := by
    intro h0
    have hz : αa (0 : V) = (2 : ZMod p) := by simpa [h0] using hαa
    rw [map_zero] at hz
    exact h2 hz.symm
  have h2ha : (2 : ZMod p) • ha = β ha • t := by
    have e1 : ra ha = ha - (2 : ZMod p) • ha := by rw [hra ha, hαa]
    have e2 : ra ha = ha - β ha • t := by rw [hrestr ha hH, hβ]
    have e : ha - (2 : ZMod p) • ha = ha - β ha • t := by rw [← e1, e2]
    simpa using e
  set c : ZMod p := β ha / 2 with hcdef
  have hha : ha = c • t := by
    calc ha = (1 : ZMod p) • ha := (one_smul _ _).symm
      _ = ((2 : ZMod p)⁻¹ * 2) • ha := by rw [inv_mul_cancel₀ h2]
      _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • ha) := by rw [smul_smul]
      _ = (2 : ZMod p)⁻¹ • (β ha • t) := by rw [h2ha]
      _ = ((2 : ZMod p)⁻¹ * β ha) • t := by rw [smul_smul]
      _ = c • t := by rw [hcdef, div_eq_mul_inv, mul_comm]
  set αa' : Module.Dual (ZMod p) V := c • αa with hαa'def
  have hβeq : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), β v = c * αa v := by
    intro v hv
    have e1 : ra v = v - αa v • ha := hra v
    have e2 : ra v = v - β v • t := by rw [hrestr v hv, hβ]
    have e : v - αa v • ha = v - β v • t := by rw [← e1, e2]
    have e' : αa v • ha = β v • t := by simpa using e
    rw [hha, smul_smul] at e'
    have e5 : αa v * c = β v := (smul_left_injective (ZMod p) ht0) e'
    rw [← e5, mul_comm]
  have hαa't : αa' t = 2 := by
    have hbt : β t = c * αa t := hβeq t htH
    have hcα : c * αa t = 2 := by rw [← hbt, hβt]
    rw [hαa'def, LinearMap.smul_apply, smul_eq_mul]
    exact hcα
  have hra' : ∀ v, ra v = v - αa' v • t := by
    intro v
    calc ra v = v - αa v • ha := hra v
      _ = v - αa v • (c • t) := by rw [hha]
      _ = v - (αa v * c) • t := by rw [smul_smul]
      _ = v - αa' v • t := by
            rw [hαa'def, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  let d : V → ZMod p := fun v => β v - αa' v
  set g : V ≃ₗ[ZMod p] V := ra * ρ (Equiv.swap a b) with hgdef
  have hdt : d t = 0 := by
    dsimp only [d]
    rw [hβt, hαa't, sub_self]
  have hg : ∀ w, g w = w + d w • t := by
    intro w
    have hlin : αa' (w - β w • t) = αa' w - (β w * 2) := by
      rw [map_sub, map_smul, hαa't]
      rfl
    calc g w = ra (ρ (Equiv.swap a b) w) := by rw [hgdef, LinearEquiv.mul_apply]
      _ = ra (w - β w • t) := by rw [hβ w]
      _ = (w - β w • t) - αa' (w - β w • t) • t := hra' _
      _ = w + d w • t := by
            rw [hlin]
            dsimp only [d]
            module
  have hgid : ∀ w, g (g w - w) = g w - w := by
    intro w
    have hgw : g w - w = d w • t := by
      rw [hg w]
      module
    rw [hgw, hg]
    have hz : d (d w • t) = 0 := by
      dsimp only [d]
      rw [map_smul, map_smul, hβt, hαa't]
      simp [smul_eq_mul]
    rw [hz, zero_smul, add_zero]
  have hle : ggLinMove g ≤ Submodule.span (ZMod p) ({t} : Set V) := by
    intro z hz
    rw [ggLinMove, LinearMap.mem_range] at hz
    obtain ⟨w, hw⟩ := hz
    have hzw : z = d w • t := by
      rw [← hw, LinearMap.sub_apply, LinearMap.id_apply]
      have hgw : g w - w = d w • t := by
        rw [hg w]
        module
      exact hgw
    rw [hzw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton t))
  have hfrle : Module.finrank (ZMod p) (ggLinMove g) ≤ 1 := by
    haveI hsp : Module.Finite (ZMod p) (Submodule.span (ZMod p) ({t} : Set V)) :=
      Module.Finite.span_singleton (ZMod p) t
    have h1 : Module.finrank (ZMod p) (ggLinMove g) ≤
        Module.finrank (ZMod p) (Submodule.span (ZMod p) ({t} : Set V)) :=
      Submodule.finrank_mono hle
    have h2' : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({t} : Set V)) = 1 :=
      finrank_span_singleton ht0
    omega
  have hgA : g ∈ Subgroup.closure (Set.range r ∪ {ra}) := by
    have hraA : ra ∈ Subgroup.closure (Set.range r ∪ {ra}) :=
      Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton ra))
    have hρA' : ρ (Equiv.swap a b) ∈ Subgroup.closure (Set.range r ∪ {ra}) :=
      Subgroup.closure_mono (Set.subset_union_left) (hρA (Equiv.swap a b))
    rw [hgdef]
    exact Subgroup.mul_mem _ hraA hρA'
  have hfrne : Module.finrank (ZMod p) (ggLinMove g) ≠ 1 := by
    intro h1
    exact hnt g hgA ⟨h1, hgid⟩
  have hfr0 : Module.finrank (ZMod p) (ggLinMove g) = 0 := by omega
  haveI hfing : Module.Finite (ZMod p) (ggLinMove g) := by
    haveI hsp : Module.Finite (ZMod p) (Submodule.span (ZMod p) ({t} : Set V)) :=
      Module.Finite.span_singleton (ZMod p) t
    exact Submodule.finiteDimensional_of_le hle
  have hbot : ggLinMove g = ⊥ := (Submodule.finrank_eq_zero (S := ggLinMove g)).mp hfr0
  have hg1 : g = 1 := by
    ext w
    have hmem : (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)) w ∈ ggLinMove g := by
      rw [ggLinMove]
      exact ⟨w, rfl⟩
    rw [hbot] at hmem
    have hz : (g.toLinearMap - (LinearMap.id : V →ₗ[ZMod p] V)) w = 0 :=
      (Submodule.mem_bot (ZMod p)).mp hmem
    rw [LinearMap.sub_apply, LinearMap.id_apply] at hz
    have := sub_eq_zero.mp hz
    simpa using this
  have hrax : ra x = x := by
    have hgx : g x = x := by rw [hg1]; rfl
    rw [hgdef, LinearEquiv.mul_apply, hρx (Equiv.swap a b)] at hgx
    exact hgx
  have hz : αa x • ha = 0 := by
    have hx : x - αa x • ha = x := by rw [← hra x, hrax]
    exact sub_eq_self.mp hx
  rcases smul_eq_zero.mp hz with hsc | hv
  · exact hw hsc
  · exact ha0 hv

theorem ggDepAOdd_caseII_false (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hN : 11 ≤ N) {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V}
    (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (ra : V ≃ₗ[ZMod p] V) (ha : V) (αa : Module.Dual (ZMod p) V)
    (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N))
    (hH : ha ∈ Submodule.span (ZMod p) (Set.range h)) : False := by
  obtain ⟨ρ, hρ, hρA, hρx, hρfaith⟩ := ggDepAOdd_perm_embed hp2 (by omega) F r hr
  obtain ⟨AH, ψ, γ, hdim, hirr, hgen, hcardAH, hinj, hpsi, hγmem, hγval, -⟩ :=
    ggDepAOdd_caseII_data hp2 (by omega) F r hr ra ha αa hra hαa hw hnt hcard
      (Submodule.span (ZMod p) (Set.range h)) rfl hH ρ hρA hρfaith
  have hsw : ∀ a b : Fin N, a ≠ b →
      GGLinRefl ((ψ (Equiv.swap a b) : ↥AH) :
        ↥(Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p]
          ↥(Submodule.span (ZMod p) (Set.range h))) := by
    intro a b hab
    obtain ⟨t, β, htH, hβt, hβ⟩ := ggDepAOdd_perm_swap_refl hp2 (by omega) F r hr ρ hρ hab
    rw [ggDepA_linRefl_iff hp2]
    refine ⟨⟨t, htH⟩, β.comp (Submodule.span (ZMod p) (Set.range h)).subtype, ?_, ?_⟩
    · simpa using hβt
    · intro v
      apply Subtype.ext
      rw [hpsi, hβ]
      rfl
  have hγrefl : GGLinRefl γ := by
    rw [ggDepA_linRefl_iff hp2]
    refine ⟨⟨ha, hH⟩, αa.comp (Submodule.span (ZMod p) (Set.range h)).subtype, ?_, ?_⟩
    · simpa using hαa
    · intro v
      apply Subtype.ext
      rw [hγval, hra]
      rfl
  obtain ⟨σ, hσswap, hσeq⟩ :=
    l05nOD_classify hKG hp2 hN hdim AH hirr hgen hcardAH ψ hinj hsw γ hγmem hγrefl
  obtain ⟨a, b, hab, hσab⟩ := hσswap
  rw [hσab] at hσeq
  have hrestr : ∀ v ∈ Submodule.span (ZMod p) (Set.range h), ra v = ρ (Equiv.swap a b) v := by
    intro v hv
    let v' : ↥(Submodule.span (ZMod p) (Set.range h)) := ⟨v, hv⟩
    have h1 : ((((ψ (Equiv.swap a b) : ↥AH) :
        ↥(Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p]
          ↥(Submodule.span (ZMod p) (Set.range h))) v' :
          ↥(Submodule.span (ZMod p) (Set.range h))) : V) = ρ (Equiv.swap a b) v :=
      hpsi (Equiv.swap a b) v'
    have h2 : ((((ψ (Equiv.swap a b) : ↥AH) :
        ↥(Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p]
          ↥(Submodule.span (ZMod p) (Set.range h))) v' :
          ↥(Submodule.span (ZMod p) (Set.range h))) : V) = ra v := by
      rw [hσeq]
      simpa using hγval v'
    exact h2.symm.trans h1
  exact l05nOD_end hp2 (by omega) F r hr ra ha αa hra hαa hw hH hnt ρ hρ hρA hρx hab hrestr

end CFSG.StandardType
