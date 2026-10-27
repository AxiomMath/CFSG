module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggDepALeft (N : ℕ) (i : Fin (N - 1)) : Fin N := ⟨i.val, by have := i.isLt; omega⟩

@[expose] def ggDepARight (N : ℕ) (i : Fin (N - 1)) : Fin N :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

private lemma l05nDP2_rc_ra {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (rc ra : V ≃ₗ[ZMod p] V) {hc ha : V}
    {αc αa : Module.Dual (ZMod p) V} (hc' : ∀ v, rc v = v - αc v • hc)
    (ha' : ∀ v, ra v = v - αa v • ha) (h0 : αc ha = 0) (v : V) :
    rc (ra v) = v - αa v • ha - αc v • hc := by
  have hha : rc (αa v • ha) = αa v • ha := by
    rw [hc' (αa v • ha), map_smul, h0, smul_zero, zero_smul, sub_zero]
  calc rc (ra v) = rc (v - αa v • ha) := by rw [ha' v]
    _ = rc v - rc (αa v • ha) := by rw [map_sub]
    _ = (v - αc v • hc) - αa v • ha := by rw [hc' v, hha]
    _ = v - αa v • ha - αc v • hc := by abel

private lemma l05nDP2_alpha_c {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (rc ra : V ≃ₗ[ZMod p] V) {hc ha : V}
    {αc αa : Module.Dual (ZMod p) V} (hc' : ∀ v, rc v = v - αc v • hc)
    (ha' : ∀ v, ra v = v - αa v • ha) (h0 : αc ha = 0) (hαc : αc hc = 2) (v : V) :
    αc (rc (ra v)) = -αc v := by
  rw [l05nDP2_rc_ra rc ra hc' ha' h0 v]
  simp only [map_sub, map_smul, h0, hαc, smul_zero, zero_smul, smul_eq_mul]
  ring

private lemma l05nDP2_alpha_a {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (rc ra : V ≃ₗ[ZMod p] V) {hc ha : V}
    {αc αa : Module.Dual (ZMod p) V} (hc' : ∀ v, rc v = v - αc v • hc)
    (ha' : ∀ v, ra v = v - αa v • ha) (h0 : αc ha = 0) (hαa : αa ha = 2) (v : V) :
    αa (rc (ra v)) = -αa v - αa hc * αc v := by
  rw [l05nDP2_rc_ra rc ra hc' ha' h0 v]
  simp only [map_sub, map_smul, h0, hαa, smul_zero, zero_smul, smul_eq_mul]
  ring

private lemma l05nDP2_sq_form {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (rc ra : V ≃ₗ[ZMod p] V) {hc ha : V}
    {αc αa : Module.Dual (ZMod p) V} (hc' : ∀ v, rc v = v - αc v • hc)
    (ha' : ∀ v, ra v = v - αa v • ha) (hαc : αc hc = 2) (hαa : αa ha = 2)
    (h0 : αc ha = 0) (v : V) :
    ((rc * ra) ^ 2) v = v + (αa hc * αc v) • ha := by
  have hG : ((rc * ra) ^ 2) v = rc (ra (rc (ra v))) := by
    simp only [pow_two, LinearEquiv.mul_apply]
  rw [hG, l05nDP2_rc_ra rc ra hc' ha' h0 (rc (ra v)),
    l05nDP2_alpha_a rc ra hc' ha' h0 hαa v, l05nDP2_alpha_c rc ra hc' ha' h0 hαc v,
    l05nDP2_rc_ra rc ra hc' ha' h0 v]
  module

theorem ggDepA_pair_zero_symm {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hnt : ∀ g ∈ A, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    {rc ra : V ≃ₗ[ZMod p] V} (hrc : rc ∈ A) (hra : ra ∈ A) {hc ha : V}
    {αc αa : Module.Dual (ZMod p) V} (hc' : ∀ v, rc v = v - αc v • hc)
    (ha' : ∀ v, ra v = v - αa v • ha) (hαc : αc hc = 2) (hαa : αa ha = 2)
    (h0 : αc ha = 0) : αa hc = 0 := by
  by_contra hne
  have hp2z : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have ha_ne : ha ≠ 0 := by
    intro h
    exact hp2z (by rw [← hαa, h, map_zero])
  let G : V ≃ₗ[ZMod p] V := (rc * ra) ^ 2
  have hGform : ∀ v, G v = v + (αa hc * αc v) • ha :=
    fun v => l05nDP2_sq_form rc ra hc' ha' hαc hαa h0 v
  have hmem : G ∈ A := by
    show (rc * ra) ^ 2 ∈ A
    exact Subgroup.pow_mem A (Subgroup.mul_mem A hrc hra) 2
  have hfix : ∀ w, G (G w - w) = G w - w := by
    intro w
    have hw : G w - w = (αa hc * αc w) • ha := by
      rw [hGform w]; abel
    rw [hw, hGform ((αa hc * αc w) • ha)]
    simp only [map_smul, h0, smul_zero, mul_zero, zero_smul, add_zero]
  have hGmove : ggLinMove G = Submodule.span (ZMod p) {ha} := by
    refine le_antisymm (fun x hx => ?_) ?_
    · simp only [ggLinMove, LinearMap.mem_range] at hx
      obtain ⟨v, hv⟩ := hx
      rw [Submodule.mem_span_singleton]
      refine ⟨αa hc * αc v, ?_⟩
      rw [← hv, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, hGform v]
      abel
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      simp only [ggLinMove, LinearMap.mem_range]
      refine ⟨((2 : ZMod p) * αa hc)⁻¹ • hc, ?_⟩
      have hscal : αa hc * αc (((2 : ZMod p) * αa hc)⁻¹ • hc) = 1 := by
        rw [map_smul, hαc, smul_eq_mul]
        field_simp
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_toLinearMap, hGform, hscal]
      module
  have hfin : Module.finrank (ZMod p) (ggLinMove G) = 1 := by
    rw [hGmove]
    exact finrank_span_singleton ha_ne
  exact hnt G hmem ⟨hfin, hfix⟩

private theorem l05nDP1_ggIntCartan_A (n : ℕ) :
    GGIntCartan (CoxeterMatrix.A n) (CartanMatrix.A n) := by
  refine ⟨fun i => by simp [CartanMatrix.A], fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  simp only [CoxeterMatrix.A, CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem l05nDP1_perm_embed_aux {p m : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hN : 5 ≤ m + 1)
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
    exact l05nDP1_ggIntCartan_A m
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
      have hc := congrArg (fun v => α a v) hh
      rw [haa, hab] at hc
      have h3 : (3 : ZMod p) = 0 := by
        have h2 : (2 : ZMod p) + 1 = 0 := by rw [hc]; ring
        rw [show (3 : ZMod p) = (2 : ZMod p) + 1 by norm_num]
        exact h2
      have hp3 : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
      have hle := Nat.le_of_dvd (by norm_num : 0 < 3) hp3
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

theorem ggDepA_perm_embed {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hN : 5 ≤ N) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {h : Fin (N - 1) → V}
    {α : Fin (N - 1) → Module.Dual (ZMod p) V} {x : V} (F : GGDepAFrame p N h α x)
    (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (hr : ∀ i v, r i v = v - α i v • h i) :
    ∃ ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V),
      (∀ i, ρ (Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = r i) ∧
        (∀ σ, ρ σ ∈ Subgroup.closure (Set.range r)) ∧ (∀ σ, ρ σ x = x) ∧
        ∀ σ, (∀ i, ρ σ (h i) = h i) → σ = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  exact l05nDP1_perm_embed_aux hp hN F.pair F.x_ker r hr

private lemma l05nDP2_refl_invol {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (r : V ≃ₗ[ZMod p] V) {h : V} {α : Module.Dual (ZMod p) V}
    (hr : ∀ v, r v = v - α v • h) (hα : α h = 2) : r * r = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, hr (r v), hr v]
  have hαv : α (v - α v • h) = -α v := by
    rw [map_sub, map_smul, hα, smul_eq_mul]
    ring
  rw [hαv, neg_smul]
  abel

private lemma l05nDP2_permCongr_swap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a b : α) :
    e.permCongr (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  ext x
  rw [Equiv.permCongr_apply, ← Equiv.symm_trans_swap_trans a b e]
  rfl

private lemma l05nDP2_adjacent_closure_top (N : ℕ) (h1 : 1 ≤ N) :
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
    rw [Equiv.permCongrHom_coe, l05nDP2_permCongr_swap e i.castSucc i.succ, hvalL i, hvalR i]
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

private lemma l05nDP2_rho_mem_closure {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (ρ : Equiv.Perm (Fin N) →* (V ≃ₗ[ZMod p] V))
    (hρ : ∀ i, ρ (Equiv.swap (ggDepALeft N i) (ggDepARight N i)) = r i)
    (h1 : 1 ≤ N) (σ : Equiv.Perm (Fin N)) :
    ρ σ ∈ Subgroup.closure (Set.range r) := by
  have hσ : σ ∈ Subgroup.closure (Set.range fun i : Fin (N - 1) =>
      Equiv.swap (ggDepALeft N i) (ggDepARight N i)) := by
    rw [l05nDP2_adjacent_closure_top N h1]
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

private lemma l05nDP2_closure_preserves {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
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
      exact l05nDP2_refl_invol (r i) (hr i) (hii i)
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

theorem ggDepA_perm_swap_refl {p N : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (hN : 5 ≤ N) {V : Type}
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
  have hpres := l05nDP2_closure_preserves (p := p) (N := N) (h := h) (α := α) r hr hii
  obtain ⟨c, hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap (w := ggDepALeft N i0)
    (x := ggDepARight N i0) (y := a) (z := b) hL0R0 hab)
  refine ⟨ρ c (h i0), (α i0).comp ((ρ c)⁻¹).toLinearMap, ?_, ?_, ?_⟩
  · exact (hpres (ρ c) (l05nDP2_rho_mem_closure r ρ hρ (by omega) c)).1 (h i0)
      (Submodule.subset_span ⟨i0, rfl⟩)
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact hii i0
  · intro v
    rw [← hc]
    simp only [map_mul, map_inv, hρ i0, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hr i0, map_sub, map_smul,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

end CFSG.StandardType
