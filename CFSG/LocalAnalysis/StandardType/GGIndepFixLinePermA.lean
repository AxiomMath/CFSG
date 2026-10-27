module

public import CFSG.LocalAnalysis.StandardType.GGIndepFixLineStep2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def l6kp_sumLM (p M : ℕ) : (Fin M → ZMod p) →ₗ[ZMod p] ZMod p :=
  ∑ i : Fin M, LinearMap.proj i

noncomputable def l6kp_H0 (p M : ℕ) : Submodule (ZMod p) (Fin M → ZMod p) :=
  LinearMap.ker (l6kp_sumLM p M)

private lemma l6kp_mem_H0 {p M : ℕ} {v : Fin M → ZMod p} :
    v ∈ l6kp_H0 p M ↔ ∑ i, v i = 0 := by
  simp [l6kp_H0, l6kp_sumLM, LinearMap.mem_ker, Finset.sum_apply, LinearMap.proj_apply]

private lemma l6kp_sum_perm {p M : ℕ} (v : Fin M → ZMod p) (σ : Equiv.Perm (Fin M)) :
    (∑ i, v (σ.symm i)) = ∑ i, v i :=
  Equiv.sum_comp σ.symm v

private noncomputable def l6kp_prefLM (p N : ℕ) :
    (Fin (N - 1 + 1) → ZMod p) →ₗ[ZMod p] (Fin (N - 1) → ZMod p) where
  toFun := fun v j => ∑ k : Fin (N - 1 + 1), if k ≤ j.castSucc then v k else 0
  map_add' := by
    intro v w
    funext j
    have hterm : ∀ k : Fin (N - 1 + 1),
        (if k ≤ j.castSucc then v k + w k else 0)
          = (if k ≤ j.castSucc then v k else 0)
            + (if k ≤ j.castSucc then w k else 0) := by
      intro k
      by_cases h : k ≤ j.castSucc <;> simp [h]
    simp only [Pi.add_apply, hterm, Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    funext j
    have hterm : ∀ k : Fin (N - 1 + 1),
        (if k ≤ j.castSucc then c • v k else 0)
          = c • (if k ≤ j.castSucc then v k else 0) := by
      intro k
      by_cases h : k ≤ j.castSucc <;> simp [h]
    simp only [Pi.smul_apply, RingHom.id_apply, hterm, Finset.smul_sum]

noncomputable def l6kp_w {p N : ℕ} (i : Fin (N - 1)) : Fin (N - 1 + 1) → ZMod p :=
  fun k => (if i.castSucc = k then (1 : ZMod p) else 0) - (if i.succ = k then (1 : ZMod p) else 0)

private lemma l6kp_prefLM_w {p N : ℕ} (i : Fin (N - 1)) :
    l6kp_prefLM p N (l6kp_w (p := p) i) = fun k => if i = k then (1 : ZMod p) else 0 := by
  funext j
  simp only [l6kp_prefLM, LinearMap.coe_mk, AddHom.coe_mk, l6kp_w]
  have hterm : ∀ k : Fin (N - 1 + 1),
      (if k ≤ j.castSucc then
        ((if i.castSucc = k then (1 : ZMod p) else 0) - (if i.succ = k then (1 : ZMod p) else 0))
        else 0)
      = (if i.castSucc = k then (if k ≤ j.castSucc then (1 : ZMod p) else 0) else 0)
        - (if i.succ = k then (if k ≤ j.castSucc then (1 : ZMod p) else 0) else 0) := by
    intro k
    by_cases hk : k ≤ j.castSucc
    · by_cases h1 : i.castSucc = k
      · subst h1; simp [hk]
      · by_cases h2 : i.succ = k
        · subst h2; simp [hk, h1]
        · simp [hk, h1, h2]
    · by_cases h1 : i.castSucc = k
      · subst h1; simp [hk]
      · by_cases h2 : i.succ = k
        · subst h2; simp [hk]
        · simp [hk, h1, h2]
  simp only [hterm, Finset.sum_sub_distrib]
  have h1 : (∑ k : Fin (N - 1 + 1),
      (if i.castSucc = k then (if k ≤ j.castSucc then (1 : ZMod p) else 0) else 0))
      = if i.castSucc ≤ j.castSucc then 1 else 0 := by
    rw [Finset.sum_ite_eq]
    simp
  have h2 : (∑ k : Fin (N - 1 + 1),
      (if i.succ = k then (if k ≤ j.castSucc then (1 : ZMod p) else 0) else 0))
      = if i.succ ≤ j.castSucc then 1 else 0 := by
    rw [Finset.sum_ite_eq]
    simp
  rw [h1, h2]
  by_cases hij : i = j
  · subst hij
    simp
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hval with h | h
    · have hle : i.castSucc ≤ j.castSucc := by
        show (i.castSucc : ℕ) ≤ (j.castSucc : ℕ); simp only [Fin.val_castSucc]; omega
      have hle2 : i.succ ≤ j.castSucc := by
        show (i.succ : ℕ) ≤ (j.castSucc : ℕ); simp only [Fin.val_succ, Fin.val_castSucc]; omega
      simp [hle, hle2, hij]
    · have hle : ¬ (i.castSucc ≤ j.castSucc) := by
        show ¬ ((i.castSucc : ℕ) ≤ (j.castSucc : ℕ)); simp only [Fin.val_castSucc]; omega
      have hle2 : ¬ (i.succ ≤ j.castSucc) := by
        show ¬ ((i.succ : ℕ) ≤ (j.castSucc : ℕ)); simp only [Fin.val_succ, Fin.val_castSucc]; omega
      simp [hle, hle2, hij]

lemma l6kp_w_mem {p N : ℕ} (i : Fin (N - 1)) :
    l6kp_w (p := p) (N := N) i ∈ l6kp_H0 p (N - 1 + 1) := by
  rw [l6kp_mem_H0]
  simp only [l6kp_w]
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ k : Fin (N - 1 + 1), (if i.castSucc = k then (1 : ZMod p) else 0)) = 1 := by
    rw [Finset.sum_ite_eq]; simp
  have h2 : (∑ k : Fin (N - 1 + 1), (if i.succ = k then (1 : ZMod p) else 0)) = 1 := by
    rw [Finset.sum_ite_eq]; simp
  rw [h1, h2]; simp

private noncomputable def l6kp_linCombV {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin (N - 1) → V) :
    (Fin (N - 1) → ZMod p) →ₗ[ZMod p] V :=
  ∑ j : Fin (N - 1), (LinearMap.toSpanSingleton (ZMod p) V (h j)).comp (LinearMap.proj j)

private noncomputable def l6kp_PhiV {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin (N - 1) → V) :
    (Fin (N - 1 + 1) → ZMod p) →ₗ[ZMod p] V :=
  (l6kp_linCombV (p := p) (N := N) h).comp (l6kp_prefLM p N)

private lemma l6kp_PhiV_apply {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin (N - 1) → V) (v : Fin (N - 1 + 1) → ZMod p) :
    l6kp_PhiV (p := p) (N := N) h v = ∑ j, (l6kp_prefLM p N v) j • h j := by
  simp [l6kp_PhiV, l6kp_linCombV, LinearMap.comp_apply, Finset.sum_apply, LinearMap.proj_apply,
    LinearMap.toSpanSingleton_apply]

private lemma l6kp_PhiV_w {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} (i : Fin (N - 1)) :
    l6kp_PhiV (p := p) (N := N) h (l6kp_w (p := p) i) = h i := by
  rw [l6kp_PhiV_apply, l6kp_prefLM_w]
  have hterm : ∀ x : Fin (N - 1),
      (if i = x then (1 : ZMod p) else 0) • h x = if i = x then h x else 0 := by
    intro x
    by_cases h : i = x <;> simp [h]
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma l6kp_PhiV_mem {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin (N - 1) → V) (v : Fin (N - 1 + 1) → ZMod p) :
    l6kp_PhiV (p := p) (N := N) h v ∈ Submodule.span (ZMod p) (Set.range h) := by
  rw [l6kp_PhiV_apply]
  exact Submodule.sum_mem _ (fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))

private noncomputable def l6kp_PhiH {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin (N - 1) → V) :
    (l6kp_H0 p (N - 1 + 1)) →ₗ[ZMod p] V :=
  (l6kp_PhiV (p := p) (N := N) h).comp (l6kp_H0 p (N - 1 + 1)).subtype

private lemma l6kp_PhiH_w {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} (i : Fin (N - 1)) :
    l6kp_PhiH (p := p) (N := N) h ⟨l6kp_w (p := p) i, l6kp_w_mem (p := p) (N := N) i⟩ = h i :=
  l6kp_PhiV_w (p := p) (N := N) i

private lemma l6kp_PhiH_mem {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin (N - 1) → V) (v : l6kp_H0 p (N - 1 + 1)) :
    l6kp_PhiH (p := p) (N := N) h v ∈ Submodule.span (ZMod p) (Set.range h) :=
  l6kp_PhiV_mem (p := p) (N := N) h v.1

private noncomputable def l6kp_PhiR {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Fin (N - 1) → V) :
    (l6kp_H0 p (N - 1 + 1)) →ₗ[ZMod p] (Submodule.span (ZMod p) (Set.range h)) :=
  (l6kp_PhiH (p := p) (N := N) h).codRestrict _
    (fun v => l6kp_PhiH_mem (p := p) (N := N) h v)

lemma l6kp_finrank_R {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) = N - 1 := by
  have := finrank_span_eq_card (R := ZMod p) S.indep
  simpa using this

private lemma l6kp_finrank_H0 {p M : ℕ} [Fact p.Prime] (hM : 1 ≤ M) :
    Module.finrank (ZMod p) (l6kp_H0 p M) = M - 1 := by
  have hsurj : LinearMap.range (l6kp_sumLM p M) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨fun k => if (⟨0, hM⟩ : Fin M) = k then c else 0, ?_⟩
    simp [l6kp_sumLM, Finset.sum_apply, Finset.sum_ite_eq]
  have hdim : Module.finrank (ZMod p) (Fin M → ZMod p) = M := by
    simp [Module.finrank_fintype_fun_eq_card]
  have h := LinearMap.finrank_range_add_finrank_ker (l6kp_sumLM p M)
  rw [hsurj, finrank_top, Module.finrank_self, hdim] at h
  have hb : Module.finrank (ZMod p) (LinearMap.ker (l6kp_sumLM p M)) = M - 1 := by
    calc Module.finrank (ZMod p) (LinearMap.ker (l6kp_sumLM p M))
        = (1 + Module.finrank (ZMod p) (LinearMap.ker (l6kp_sumLM p M))) - 1 := by
          rw [Nat.add_sub_cancel_left]
      _ = M - 1 := by rw [h]
  change Module.finrank (ZMod p) (LinearMap.ker (l6kp_sumLM p M)) = M - 1
  exact hb

private lemma l6kp_finrank_H0' {p N : ℕ} [Fact p.Prime] (hN : 1 ≤ N) :
    Module.finrank (ZMod p) (l6kp_H0 p (N - 1 + 1)) = N - 1 := by
  have h := l6kp_finrank_H0 (p := p) (M := N - 1 + 1) (by omega)
  have e : N - 1 + 1 - 1 = N - 1 := by omega
  rwa [e] at h

private lemma l6kp_PhiR_surj {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Function.Surjective (l6kp_PhiR (p := p) (N := N) h) := by
  intro z
  have hz : (z : V) ∈ LinearMap.range (l6kp_PhiH (p := p) (N := N) h) := by
    have hle : Submodule.span (ZMod p) (Set.range h) ≤
        LinearMap.range (l6kp_PhiH (p := p) (N := N) h) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨l6kp_w (p := p) i, l6kp_w_mem (p := p) (N := N) i⟩,
        l6kp_PhiH_w (p := p) (N := N) i⟩
    exact hle z.2
  obtain ⟨v, hv⟩ := hz
  exact ⟨v, Subtype.ext hv⟩

private lemma l6kp_PhiR_inj {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    Function.Injective (l6kp_PhiR (p := p) (N := N) h) := by
  have hker : Module.finrank (ZMod p) (LinearMap.ker (l6kp_PhiR (p := p) (N := N) h)) = 0 := by
    have hfr := LinearMap.finrank_range_add_finrank_ker (l6kp_PhiR (p := p) (N := N) h)
    have htop : LinearMap.range (l6kp_PhiR (p := p) (N := N) h) = ⊤ :=
      LinearMap.range_eq_top.mpr (l6kp_PhiR_surj S)
    rw [htop, finrank_top, l6kp_finrank_R S, l6kp_finrank_H0' (show 1 ≤ N by have := S.five_le; omega)] at hfr
    have h2 : (N - 1) + Module.finrank (ZMod p)
        (LinearMap.ker (l6kp_PhiR (p := p) (N := N) h)) = (N - 1) + 0 := by
      simpa using hfr
    simpa using Nat.add_left_cancel h2
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp hker

noncomputable def l6kp_E {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) :
    (Submodule.span (ZMod p) (Set.range h)) ≃ₗ[ZMod p] (l6kp_H0 p (N - 1 + 1)) :=
  (LinearEquiv.ofBijective (l6kp_PhiR (p := p) (N := N) h)
    ⟨l6kp_PhiR_inj S, l6kp_PhiR_surj S⟩).symm

lemma l6kp_E_h {p N : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)} {ι : Type} {s : ι → (V ≃ₗ[ZMod p] V)} {x : V}
    (S : GGFixLineHyp p N h α r s x) (j : Fin (N - 1)) :
    l6kp_E S ⟨h j, Submodule.subset_span (Set.mem_range_self j)⟩ =
      ⟨l6kp_w (p := p) j, l6kp_w_mem (p := p) (N := N) j⟩ := by
  have hw : l6kp_PhiR (p := p) (N := N) h
      ⟨l6kp_w (p := p) j, l6kp_w_mem (p := p) (N := N) j⟩ =
      ⟨h j, Submodule.subset_span (Set.mem_range_self j)⟩ :=
    Subtype.ext (l6kp_PhiH_w (p := p) (N := N) j)
  change (LinearEquiv.ofBijective (l6kp_PhiR (p := p) (N := N) h)
    ⟨l6kp_PhiR_inj S, l6kp_PhiR_surj S⟩).symm _ = _
  rw [← hw]
  exact LinearEquiv.symm_apply_apply _ _

noncomputable def l6kp_shat {p M : ℕ} (σ : Equiv.Perm (Fin M)) :
    (Fin M → ZMod p) ≃ₗ[ZMod p] (Fin M → ZMod p) where
  toFun := fun v i => v (σ.symm i)
  invFun := fun v i => v (σ i)
  left_inv := by
    intro v; funext i; simp
  right_inv := by
    intro v; funext i; simp
  map_add' := by
    intro v w; funext i; simp
  map_smul' := by
    intro c v; funext i; simp

lemma l6kp_shat_mem {p N : ℕ} (σ : Equiv.Perm (Fin (N - 1 + 1)))
    {v : Fin (N - 1 + 1) → ZMod p} (hv : v ∈ l6kp_H0 p (N - 1 + 1)) :
    l6kp_shat σ v ∈ l6kp_H0 p (N - 1 + 1) := by
  rw [l6kp_mem_H0] at hv ⊢
  exact (l6kp_sum_perm v σ).trans hv

@[expose] noncomputable def l6kp_rho {p N : ℕ} (σ : Equiv.Perm (Fin (N - 1 + 1))) :
    (l6kp_H0 p (N - 1 + 1)) ≃ₗ[ZMod p] (l6kp_H0 p (N - 1 + 1)) where
  toFun v := ⟨l6kp_shat σ v.1, l6kp_shat_mem σ v.2⟩
  invFun v := ⟨l6kp_shat σ.symm v.1, l6kp_shat_mem σ.symm v.2⟩
  left_inv v := by ext i; simp [l6kp_shat]
  right_inv v := by ext i; simp [l6kp_shat]
  map_add' v w := by ext i; simp [l6kp_shat]
  map_smul' c v := by ext i; simp [l6kp_shat]

@[expose] noncomputable def l6kp_rhoHom {p N : ℕ} :
    Equiv.Perm (Fin (N - 1 + 1)) →*
      (l6kp_H0 p (N - 1 + 1) ≃ₗ[ZMod p] l6kp_H0 p (N - 1 + 1)) where
  toFun := l6kp_rho
  map_one' := by ext v i; rfl
  map_mul' σ τ := by
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    funext i
    change v.1 ((σ * τ).symm i) = (l6kp_shat τ v.1) (σ.symm i)
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]
    rfl

private lemma l6kp_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := by
    have hh := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
    simpa using hh
  have hp2 : p = 2 := by
    have h := (Nat.prime_two.dvd_iff_eq (Fact.out : p.Prime).ne_one).mp hdvd
    omega
  exact hp hp2

private lemma l6kp_neg_one_ne_one {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by
    have hh : (-1 + 1 : ZMod p) = 1 + 1 := congrArg (fun x => x + 1) h
    rw [neg_add_cancel] at hh
    rw [show (1 : ZMod p) + 1 = 2 by norm_num] at hh
    exact hh.symm
  exact l6kp_two_ne_zero hp h2

private lemma l6kp_rho_eq_one {p N : ℕ} [Fact p.Prime] (hN : 2 ≤ N) (hp : p ≠ 2)
    {σ : Equiv.Perm (Fin (N - 1 + 1))}
    (hσ : l6kp_rhoHom (p := p) (N := N) σ = 1) : σ = 1 := by
  apply Equiv.Perm.ext
  intro i
  show σ i = i
  let z : Fin (N - 1 + 1) := ⟨0, by omega⟩
  let o : Fin (N - 1 + 1) := ⟨1, by omega⟩
  let b : Fin (N - 1 + 1) := if z = i then o else z
  have hb : b ≠ i := by
    dsimp only [b]
    by_cases h : z = i
    · rw [if_pos h]
      intro hc
      have hv : (o : ℕ) = (z : ℕ) := by rw [hc, ← h]
      simp [o, z] at hv
    · rw [if_neg h]
      exact h
  let v : Fin (N - 1 + 1) → ZMod p :=
    fun k => (if i = k then (1 : ZMod p) else 0) - (if b = k then (1 : ZMod p) else 0)
  have hv : v ∈ l6kp_H0 p (N - 1 + 1) := by
    rw [l6kp_mem_H0]
    simp only [v]
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ k : Fin (N - 1 + 1), (if i = k then (1 : ZMod p) else 0)) = 1 := by
      rw [Finset.sum_ite_eq]; simp
    have h2 : (∑ k : Fin (N - 1 + 1), (if b = k then (1 : ZMod p) else 0)) = 1 := by
      rw [Finset.sum_ite_eq]; simp
    rw [h1, h2]; simp
  have h1 : l6kp_rho σ ⟨v, hv⟩ = ⟨v, hv⟩ := by
    change l6kp_rhoHom (p := p) (N := N) σ ⟨v, hv⟩ = ⟨v, hv⟩
    rw [hσ]
    rfl
  have h2 : l6kp_shat σ v = v := congrArg Subtype.val h1
  have h3 := congr_fun h2 (σ i)
  have h4 : v (σ.symm (σ i)) = v (σ i) := h3
  have h5 : v (σ.symm (σ i)) = v i := by rw [Equiv.symm_apply_apply]
  have h6 : v (σ i) = v i := h4.symm.trans h5
  have hvi : v i = 1 := by
    simp [v, hb]
  by_contra hne
  have h7 : v (σ i) = 1 := by rw [h6, hvi]
  have h8 : v (σ i) = (if i = σ i then (1 : ZMod p) else 0)
      - (if b = σ i then (1 : ZMod p) else 0) := rfl
  rw [h8] at h7
  have hnei : σ i ≠ i := hne
  have h9 : (if i = σ i then (1 : ZMod p) else 0) = 0 := by
    rw [if_neg (fun h => hnei h.symm)]
  rw [h9, zero_sub] at h7
  by_cases hbi : b = σ i
  · rw [if_pos hbi] at h7
    exact l6kp_neg_one_ne_one hp h7
  · rw [if_neg hbi] at h7
    have h0 : (0 : ZMod p) = 1 := by simpa using h7
    exact zero_ne_one h0

lemma l6kp_rho_inj {p N : ℕ} [Fact p.Prime] (hN : 2 ≤ N) (hp : p ≠ 2) :
    Function.Injective (l6kp_rhoHom (p := p) (N := N)) := by
  intro σ τ hστ
  have hmul : l6kp_rhoHom (p := p) (N := N) (σ * τ⁻¹) = 1 := by
    rw [map_mul, MonoidHom.map_inv, hστ, mul_inv_cancel]
  exact mul_inv_eq_one.mp (l6kp_rho_eq_one (p := p) (N := N) hN hp hmul)

lemma l6kp_cartanA {p N : ℕ} (i j : Fin (N - 1)) :
    (CartanMatrix.A (N - 1) i j : ZMod p) =
      if i = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0 := by
  have hd : CartanMatrix.A (N - 1) i j =
      if i = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0 := by
    rw [CartanMatrix.A]
    simp only [Matrix.of_apply]
  rw [hd]
  by_cases h1 : i = j
  · rw [if_pos h1, if_pos h1]; norm_num
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · rw [if_pos h2, if_pos h2]; norm_num
    · rw [if_neg h2, if_neg h2]; norm_num

private lemma l6kp_shat_single {p M : ℕ} (σ : Equiv.Perm (Fin M)) (l : Fin M) :
    l6kp_shat (p := p) σ (fun k => if l = k then (1 : ZMod p) else 0)
      = fun k => if σ l = k then (1 : ZMod p) else 0 := by
  funext k
  show (if l = σ.symm k then (1 : ZMod p) else 0) = (if σ l = k then (1 : ZMod p) else 0)
  by_cases h : σ l = k
  · have h2 : l = σ.symm k := by
      rw [← h]
      exact (Equiv.symm_apply_apply σ l).symm
    rw [if_pos h, if_pos h2]
  · have h2 : ¬ (l = σ.symm k) := by
      intro hh
      apply h
      rw [hh]
      exact Equiv.apply_symm_apply σ k
    rw [if_neg h, if_neg h2]

lemma l6kp_shat_w {p N : ℕ} (i j : Fin (N - 1)) :
    l6kp_shat (p := p) (Equiv.swap i.castSucc i.succ) (l6kp_w (p := p) j)
      = l6kp_w (p := p) j
        - (CartanMatrix.A (N - 1) i j : ZMod p) • l6kp_w (p := p) i := by
  have hwj : l6kp_w (p := p) j
      = (fun k => if j.castSucc = k then (1 : ZMod p) else 0)
        - (fun k => if j.succ = k then (1 : ZMod p) else 0) := rfl
  have hwi : l6kp_w (p := p) i
      = (fun k => if i.castSucc = k then (1 : ZMod p) else 0)
        - (fun k => if i.succ = k then (1 : ZMod p) else 0) := rfl
  rw [hwj, hwi]
  simp only [map_sub, l6kp_shat_single]
  have hA := l6kp_cartanA (p := p) (N := N) i j
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hji : j = i
  · subst hji
    rw [hA, if_pos rfl, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  · rw [hA, if_neg (Ne.symm hji)]
    have hja' : j.castSucc ≠ i.castSucc := by
      intro h
      exact hji (Fin.ext (by simpa using congrArg Fin.val h))
    have hss : j.succ ≠ i.succ := by
      intro h
      apply hji
      apply Fin.ext
      have := congrArg Fin.val h
      simpa [Fin.val_succ] using this
    by_cases h2 : j.succ = i.castSucc
    · have hjb : j.castSucc ≠ i.succ := by
        intro h
        have hv1 : (j.castSucc : ℕ) = (i.succ : ℕ) := by rw [h]
        have hv2 : (j.succ : ℕ) = (i.castSucc : ℕ) := by rw [h2]
        simp only [Fin.val_castSucc, Fin.val_succ] at hv1 hv2
        omega
      have h2v : (j : ℕ) + 1 = i := by
        have := congrArg Fin.val h2
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      rw [if_pos (Or.inr h2v)]
      rw [h2, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hja' hjb]
      ring
    · by_cases h3 : j.castSucc = i.succ
      · have h3v : (i : ℕ) + 1 = j := by
          have := congrArg Fin.val h3
          simp only [Fin.val_castSucc, Fin.val_succ] at this
          omega
        rw [if_pos (Or.inl h3v)]
        rw [h3, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne h2 hss]
        ring
      · have hAv : ¬ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by
          rintro (h | h)
          · exact h3 (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
          · exact h2 (Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
        rw [if_neg hAv]
        rw [Equiv.swap_apply_of_ne_of_ne hja' h3, Equiv.swap_apply_of_ne_of_ne h2 hss]
        ring

end CFSG.StandardType

end
