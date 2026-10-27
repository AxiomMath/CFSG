module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreSwaps

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggQ2s08bf4_coxeterB_apply (n : ℕ) (u v : Fin n) :
    CoxeterMatrix.B n u v =
      if u = v then 1
      else if ((u = n - 1 ∧ v = n - 2) ∨ (v = n - 1 ∧ u = n - 2)) then 4
      else if ((u.val + 1 = v.val) ∨ (v.val + 1 = u.val)) then 3 else 2 := by
  show (if u = v then 1
      else if (u = n - 1 ∧ v = n - 2 ∨ v = n - 1 ∧ u = n - 2) then 4
      else if (v.val + 1 = u.val ∨ u.val + 1 = v.val) then 3 else 2) =
    (if u = v then 1
      else if ((u = n - 1 ∧ v = n - 2) ∨ (v = n - 1 ∧ u = n - 2)) then 4
      else if (u.val + 1 = v.val ∨ v.val + 1 = u.val) then 3 else 2)
  by_cases huv : u = v
  · rw [if_pos huv, if_pos huv]
  · rw [if_neg huv, if_neg huv]
    by_cases h4 : (u = n - 1 ∧ v = n - 2 ∨ v = n - 1 ∧ u = n - 2)
    · rw [if_pos h4, if_pos h4]
    · rw [if_neg h4, if_neg h4]
      by_cases h : (v.val + 1 = u.val ∨ u.val + 1 = v.val)
      · rw [if_pos h, if_pos (h.elim Or.inr Or.inl)]
      · rw [if_neg h, if_neg (fun hh => h (hh.elim Or.inr Or.inl))]

private lemma ggQ2s08bf4_coxeterB_double (r : ℕ) (hr : 2 ≤ r) :
    CoxeterMatrix.B r ⟨r - 1, by omega⟩ ⟨r - 2, by omega⟩ = 4 := by
  rw [ggQ2s08bf4_coxeterB_apply]
  have huv : (⟨r - 1, by omega⟩ : Fin r) ≠ ⟨r - 2, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  rw [if_neg huv]
  have hdb : ((⟨r - 1, by omega⟩ : Fin r).val = r - 1 ∧
        (⟨r - 2, by omega⟩ : Fin r).val = r - 2) ∨
      ((⟨r - 2, by omega⟩ : Fin r).val = r - 1 ∧
        (⟨r - 1, by omega⟩ : Fin r).val = r - 2) := by
    left; exact ⟨rfl, rfl⟩
  rw [if_pos hdb]

private lemma ggQ2s08bf4_coxeterD_adj1 (r : ℕ) (hr : 9 ≤ r) :
    ggCoxeterMatrixD r ⟨r - 3, by omega⟩ ⟨r - 4, by omega⟩ = 3 := by
  rw [ggCoxeterMatrixD_apply]
  have hne : (⟨r - 3, by omega⟩ : Fin r) ≠ ⟨r - 4, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  rw [if_neg hne]
  have hD : CartanMatrix.D r ⟨r - 3, by omega⟩ ⟨r - 4, by omega⟩ ≠ 0 := by
    have h1 : CartanMatrix.D r ⟨r - 3, by omega⟩ ⟨r - 4, by omega⟩ = -1 := by
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rw [h1]; norm_num
  rw [if_neg hD]

private lemma ggQ2s08bf4_coxeterD_adj2 (r : ℕ) (hr : 9 ≤ r) :
    ggCoxeterMatrixD r ⟨r - 3, by omega⟩ ⟨r - 2, by omega⟩ = 3 := by
  rw [ggCoxeterMatrixD_apply]
  have hne : (⟨r - 3, by omega⟩ : Fin r) ≠ ⟨r - 2, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  rw [if_neg hne]
  have hD : CartanMatrix.D r ⟨r - 3, by omega⟩ ⟨r - 2, by omega⟩ ≠ 0 := by
    have h1 : CartanMatrix.D r ⟨r - 3, by omega⟩ ⟨r - 2, by omega⟩ = -1 := by
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rw [h1]; norm_num
  rw [if_neg hD]

private lemma ggQ2s08bf4_coxeterD_adj3 (r : ℕ) (hr : 9 ≤ r) :
    ggCoxeterMatrixD r ⟨r - 3, by omega⟩ ⟨r - 1, by omega⟩ = 3 := by
  rw [ggCoxeterMatrixD_apply]
  have hne : (⟨r - 3, by omega⟩ : Fin r) ≠ ⟨r - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  rw [if_neg hne]
  have hD : CartanMatrix.D r ⟨r - 3, by omega⟩ ⟨r - 1, by omega⟩ ≠ 0 := by
    have h1 : CartanMatrix.D r ⟨r - 3, by omega⟩ ⟨r - 1, by omega⟩ = -1 := by
      simp only [CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
      split_ifs <;> omega
    rw [h1]; norm_num
  rw [if_neg hD]

private lemma ggQ2s08bf4_coxeterD_nonadj12 (r : ℕ) (hr : 9 ≤ r) :
    ggCoxeterMatrixD r ⟨r - 4, by omega⟩ ⟨r - 2, by omega⟩ = 2 := by
  simp only [ggCoxeterMatrixD_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggQ2s08bf4_coxeterD_nonadj13 (r : ℕ) (hr : 9 ≤ r) :
    ggCoxeterMatrixD r ⟨r - 4, by omega⟩ ⟨r - 1, by omega⟩ = 2 := by
  simp only [ggCoxeterMatrixD_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private lemma ggQ2s08bf4_coxeterD_nonadj23 (r : ℕ) (hr : 9 ≤ r) :
    ggCoxeterMatrixD r ⟨r - 2, by omega⟩ ⟨r - 1, by omega⟩ = 2 := by
  simp only [ggCoxeterMatrixD_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

private theorem ggQ2s08bf4_swap_of_perm_refl {N : ℕ} {f0 : Fin N → Vn N}
    (hli : LinearIndependent (ZMod 3) f0)
    (hspan : Submodule.span (ZMod 3) (Set.range f0) = ⊤)
    (g : Vn N ≃ₗ[ZMod 3] Vn N) (hg2 : g * g = 1)
    (hgr : Module.finrank (ZMod 3) (ggLinMove g) = 1)
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ j, g (f0 j) = f0 (σ j)) :
    σ.IsSwap := by
  let b : Module.Basis (Fin N) (ZMod 3) (Vn N) := Module.Basis.mk hli hspan.ge
  have hb : ∀ i, b i = f0 i := fun i => Module.Basis.mk_apply hli hspan.ge i
  have hb' : ∀ i, f0 i = b i := fun i => (hb i).symm
  have hf0inj : Function.Injective f0 := fun i j h =>
    b.injective (by rwa [hb' i, hb' j] at h)
  have hσ2 : σ * σ = 1 := by
    apply Equiv.ext; intro j
    apply hf0inj
    have h := congrArg (fun T : Vn N ≃ₗ[ZMod 3] Vn N => T (f0 j)) hg2
    rw [LinearEquiv.mul_apply, hσ j, hσ (σ j)] at h
    simpa using h
  have hσ2c : ∀ c, σ (σ c) = c := by
    intro c
    have h := congrArg (fun τ : Equiv.Perm (Fin N) => τ c) hσ2
    simpa [Equiv.Perm.mul_apply] using h
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hσ' : ∀ j, g (f0 j) = f0 j := fun j => by simp [hσ j, h1]
    have hmaps : (g : Vn N →ₗ[ZMod 3] Vn N) = 1 :=
      Module.Basis.ext b (fun j => by rw [hb j]; simpa using hσ' j)
    have hg1 : g = 1 := by
      apply LinearEquiv.ext; intro v
      exact congrArg (fun f : Vn N →ₗ[ZMod 3] Vn N => f v) hmaps
    have hbot : ggLinMove g = ⊥ := by
      rw [ggLinMove, hg1]; simp
    rw [hbot] at hgr
    exact absurd hgr (by simp)
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext h)
  set bp : Fin N := σ a with hbp
  have hab : a ≠ bp := fun h => ha (h.trans hbp).symm
  have hσb : σ bp = a := by
    have h := hσ2c a
    rwa [hbp]
  have hw_ne : f0 bp - f0 a ≠ 0 := by
    intro h0
    exact hab (hf0inj (sub_eq_zero.mp h0)).symm
  have hw_mem : f0 bp - f0 a ∈ ggLinMove g := by
    change f0 bp - f0 a ∈ LinearMap.range (g.toLinearMap - LinearMap.id)
    refine ⟨f0 a, ?_⟩
    change g (f0 a) - f0 a = f0 bp - f0 a
    rw [hσ a, ← hbp]
  have hw_span : Submodule.span (ZMod 3) ({f0 bp - f0 a} : Set (Vn N)) = ggLinMove g := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hw_mem
    · rw [finrank_span_singleton hw_ne, hgr]
  have hkey : ∀ c, σ c ≠ c → c = a ∨ c = bp := by
    intro c hc
    have hx_mem : f0 (σ c) - f0 c ∈ ggLinMove g := by
      change f0 (σ c) - f0 c ∈ LinearMap.range (g.toLinearMap - LinearMap.id)
      refine ⟨f0 c, ?_⟩
      change g (f0 c) - f0 c = f0 (σ c) - f0 c
      rw [hσ c]
    rw [← hw_span, Submodule.mem_span_singleton] at hx_mem
    obtain ⟨lam, hlam⟩ := hx_mem
    have hrepr : lam • (Finsupp.single bp (1 : ZMod 3) - Finsupp.single a (1 : ZMod 3)) =
        Finsupp.single (σ c) (1 : ZMod 3) - Finsupp.single c (1 : ZMod 3) := by
      have := congrArg b.repr hlam
      simpa [map_smul, map_sub, Module.Basis.repr_self, hb'] using this
    have h1 : σ c = a ∨ σ c = bp := by
      by_contra h
      push Not at h
      obtain ⟨hca, hcb⟩ := h
      have heval := congrArg (fun y : Fin N →₀ ZMod 3 => y (σ c)) hrepr
      rw [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne hcb, Finsupp.single_eq_of_ne hca,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne hc] at heval
      have h01 : (0 : ZMod 3) = 1 := by simpa using heval
      exact (by norm_num : (0 : ZMod 3) ≠ 1) h01
    rcases h1 with h1 | h1
    · right
      rw [← hσ2c c, h1, ← hbp]
    · left
      rw [← hσ2c c, h1, hσb]
  refine ⟨a, bp, hab, ?_⟩
  apply Equiv.ext; intro c
  by_cases hca : c = a
  · rw [hca, ← hbp, Equiv.swap_apply_left]
  · by_cases hcb : c = bp
    · rw [hcb, hσb, Equiv.swap_apply_right]
    · have hfix : σ c = c := by
        by_contra hne
        rcases hkey c hne with h | h
        · exact hca h
        · exact hcb h
      rw [hfix, Equiv.swap_apply_of_ne_of_ne hca hcb]

private lemma ggQ2s08bf4_perm_pow_apply {N : ℕ} {f0 : Fin N → Vn N}
    {g : Vn N ≃ₗ[ZMod 3] Vn N} {σ : Equiv.Perm (Fin N)}
    (hσ : ∀ k, g (f0 k) = f0 (σ k)) (n : ℕ) :
    ∀ k, (g ^ n) (f0 k) = f0 ((σ ^ n) k) := by
  induction n with
  | zero => intro k; simp
  | succ n ih =>
      intro k
      simp only [pow_succ, LinearEquiv.mul_apply, Equiv.Perm.mul_apply, hσ, ih]

private lemma ggQ2s08bf4_perm_pow_eq_one {N : ℕ} {f0 : Fin N → Vn N}
    (hf0inj : Function.Injective f0) {g : Vn N ≃ₗ[ZMod 3] Vn N}
    {σ : Equiv.Perm (Fin N)} (hσ : ∀ k, g (f0 k) = f0 (σ k))
    {n : ℕ} (h : g ^ n = 1) : σ ^ n = 1 := by
  apply Equiv.ext; intro k
  apply hf0inj
  have h1 : (g ^ n) (f0 k) = f0 k := by rw [h]; rfl
  rw [← ggQ2s08bf4_perm_pow_apply hσ n k]
  exact h1

private lemma ggQ2s08bf4_perm_mul_apply {N : ℕ} {f0 : Fin N → Vn N}
    {g h : Vn N ≃ₗ[ZMod 3] Vn N} {σ τ : Equiv.Perm (Fin N)}
    (hσ : ∀ k, g (f0 k) = f0 (σ k)) (hτ : ∀ k, h (f0 k) = f0 (τ k)) :
    ∀ k, (g * h) (f0 k) = f0 ((σ * τ) k) := by
  intro k
  simp only [LinearEquiv.mul_apply, hτ k, hσ (τ k), Equiv.Perm.mul_apply]

private lemma ggQ2s08bf4_perm_comm_of_lin_comm {N : ℕ} {f0 : Fin N → Vn N}
    (hf0inj : Function.Injective f0) {g h : Vn N ≃ₗ[ZMod 3] Vn N}
    {σ τ : Equiv.Perm (Fin N)}
    (hσ : ∀ k, g (f0 k) = f0 (σ k)) (hτ : ∀ k, h (f0 k) = f0 (τ k))
    (hcomm : g * h = h * g) : σ * τ = τ * σ := by
  apply Equiv.ext; intro k
  apply hf0inj
  simp only [← ggQ2s08bf4_perm_mul_apply hσ hτ k,
    ← ggQ2s08bf4_perm_mul_apply hτ hσ k, hcomm]

private lemma ggQ2s08bf4_lin_comm_of_perm_comm {N : ℕ} {f0 : Fin N → Vn N}
    (hli : LinearIndependent (ZMod 3) f0)
    (hspan : Submodule.span (ZMod 3) (Set.range f0) = ⊤)
    {g h : Vn N ≃ₗ[ZMod 3] Vn N} {σ τ : Equiv.Perm (Fin N)}
    (hσ : ∀ k, g (f0 k) = f0 (σ k)) (hτ : ∀ k, h (f0 k) = f0 (τ k))
    (hcomm : σ * τ = τ * σ) : g * h = h * g := by
  let b : Module.Basis (Fin N) (ZMod 3) (Vn N) := Module.Basis.mk hli hspan.ge
  have hb : ∀ i, b i = f0 i := fun i => Module.Basis.mk_apply hli hspan.ge i
  apply LinearEquiv.ext; intro v
  have hmaps : ((g * h : Vn N ≃ₗ[ZMod 3] Vn N) : Vn N →ₗ[ZMod 3] Vn N) =
      ((h * g : Vn N ≃ₗ[ZMod 3] Vn N) : Vn N →ₗ[ZMod 3] Vn N) := by
    apply Module.Basis.ext b; intro k
    rw [hb k]
    change (g * h) (f0 k) = (h * g) (f0 k)
    rw [ggQ2s08bf4_perm_mul_apply hσ hτ k,
      ggQ2s08bf4_perm_mul_apply hτ hσ k, hcomm]
  exact congrArg (fun f : Vn N →ₗ[ZMod 3] Vn N => f v) hmaps

private lemma ggQ2s08bf4_lin_eq_of_perm_eq {N : ℕ} {f0 : Fin N → Vn N}
    (hli : LinearIndependent (ZMod 3) f0)
    (hspan : Submodule.span (ZMod 3) (Set.range f0) = ⊤)
    {g h : Vn N ≃ₗ[ZMod 3] Vn N} {σ τ : Equiv.Perm (Fin N)}
    (hσ : ∀ k, g (f0 k) = f0 (σ k)) (hτ : ∀ k, h (f0 k) = f0 (τ k))
    (heq : σ = τ) : g = h := by
  let b : Module.Basis (Fin N) (ZMod 3) (Vn N) := Module.Basis.mk hli hspan.ge
  have hb : ∀ i, b i = f0 i := fun i => Module.Basis.mk_apply hli hspan.ge i
  apply LinearEquiv.ext; intro v
  have hmaps : (g : Vn N →ₗ[ZMod 3] Vn N) = (h : Vn N →ₗ[ZMod 3] Vn N) := by
    apply Module.Basis.ext b; intro k
    rw [hb k]
    change g (f0 k) = h (f0 k)
    rw [hσ k, heq, hτ k]
  exact congrArg (fun f : Vn N →ₗ[ZMod 3] Vn N => f v) hmaps

private lemma ggQ2s08bf4_perm_ne_of_lin_ne {N : ℕ} {f0 : Fin N → Vn N}
    (hli : LinearIndependent (ZMod 3) f0)
    (hspan : Submodule.span (ZMod 3) (Set.range f0) = ⊤)
    {g h : Vn N ≃ₗ[ZMod 3] Vn N} {σ τ : Equiv.Perm (Fin N)}
    (hσ : ∀ k, g (f0 k) = f0 (σ k)) (hτ : ∀ k, h (f0 k) = f0 (τ k))
    (hgh : g ≠ h) : σ ≠ τ :=
  fun hστ => hgh (ggQ2s08bf4_lin_eq_of_perm_eq hli hspan hσ hτ hστ)

theorem ggQ2s08_big_roFrame_of_facts [Finite G] (M : GGQ2LDatum 3 Bs L x)
    {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab) (hMW : GGQ2LabelWeyl lab M.coxeter)
    (κ : M.V ≃ₗ[ZMod 3] Vn (lab.rank + 1)) (e : Fin lab.rank ≃ M.Λ)
    (s : Fin lab.rank → (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)))
    (Mx : CoxeterMatrix (Fin lab.rank))
    (hMx : ∀ i j, Mx i j = M.coxeter (e i) (e j))
    (hs : ∀ i v, κ (ggLin (p := 3) M.model (M.simple (e i)) (κ.symm v)) = s i v)
    (hsrefl : ∀ i, GGLinRefl (s i)) (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ Mx i j = 1)
    (hncomm : ∀ i j, i ≠ j → Mx i j ≠ 2 → s i * s j ≠ s j * s i)
    {R : Subgroup (Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1))}
    {r : Vn (lab.rank + 1) ≃ₗ[ZMod 3] Vn (lab.rank + 1)}
    (hRO : GGQ2S08CoreRO (N := lab.rank + 1) R (Subgroup.closure (Set.range s)) r (κ M.xV)) :
    lab.tag = .twA ∧ Even (lab.rank + 1) ∧
      ∃ f : Fin (lab.rank + 1) → M.V, GGQ2S08ROFrame M f ∧
        (∀ a, a ∈ R ↔ GGQ2S08Mono (fun i => κ (f i)) a) ∧
        (∀ a, a ∈ GGQ2S08M0 R (Subgroup.closure (Set.range s)) r (κ M.xV) ↔ GGQ2S08MonoEven
          (fun i => κ (f i)) a) := by
  classical
  simp only [GGQ2S08CoreRO] at hRO
  obtain ⟨hEven, f0, hli, hspan, hsum, hperm, hRmono, hM0mono⟩ := hRO
  have hb' : ∀ i, f0 i = (Module.Basis.mk hli hspan.ge : Module.Basis (Fin (lab.rank + 1))
      (ZMod 3) (Vn (lab.rank + 1))) i :=
    fun i => (Module.Basis.mk_apply hli hspan.ge i).symm
  have hf0inj : Function.Injective f0 := fun i j h =>
    (Module.Basis.mk hli hspan.ge).injective (by rwa [hb' i, hb' j] at h)
  have hsW : ∀ i, s i ∈ Subgroup.closure (Set.range s) :=
    fun i => Subgroup.subset_closure ⟨i, rfl⟩
  choose σ hσ using fun i => hperm (s i) (hsW i)
  have hσswap : ∀ i, (σ i).IsSwap := fun i =>
    ggQ2s08bf4_swap_of_perm_refl hli hspan (s i) (hsrefl i).1 (hsrefl i).2 (σ i) (hσ i)
  have hσne : ∀ {u v : Fin lab.rank}, u ≠ v → σ u ≠ σ v := by
    intro u v huv
    exact ggQ2s08bf4_perm_ne_of_lin_ne hli hspan (hσ u) (hσ v) (hdist u v huv)
  obtain ⟨-, htags, hrank⟩ := hlab
  have hcontra4 : ∀ u v : Fin lab.rank, u ≠ v → Mx u v = 4 → False := by
    intro u v huv hMx4
    have h4 : (s u * s v) ^ 4 = 1 := by
      have := hrel u v huv
      rwa [hMx4] at this
    have h4σ : (σ u * σ v) ^ 4 = 1 :=
      ggQ2s08bf4_perm_pow_eq_one hf0inj (ggQ2s08bf4_perm_mul_apply (hσ u) (hσ v)) h4
    have hcommσ : σ u * σ v = σ v * σ u :=
      ggQ2s08core_no_four (hσswap u) (hσswap v) (hσne huv) h4σ
    have hcomm : s u * s v = s v * s u :=
      ggQ2s08bf4_lin_comm_of_perm_comm hli hspan (hσ u) (hσ v) hcommσ
    exact hncomm u v huv (by rw [hMx4]; norm_num) hcomm
  have hcontraBreindex : (∃ e' : Fin lab.rank ≃ M.Λ,
      M.coxeter = (CoxeterMatrix.B lab.rank).reindex e') → False := by
    rintro ⟨e', he'⟩
    let p : Fin lab.rank := ⟨lab.rank - 1, by omega⟩
    let q : Fin lab.rank := ⟨lab.rank - 2, by omega⟩
    have hpq : p ≠ q := by
      intro h
      have := congrArg Fin.val h
      simp only [p, q] at this
      omega
    let u : Fin lab.rank := e.symm (e' p)
    let v : Fin lab.rank := e.symm (e' q)
    have huv : u ≠ v := by
      show e.symm (e' p) ≠ e.symm (e' q)
      intro h
      exact hpq (e'.injective (e.symm.injective h))
    have hMx4 : Mx u v = 4 := by
      rw [hMx u v, he', CoxeterMatrix.reindex_apply]
      have hp : e'.symm (e u) = p := by simp [u]
      have hq : e'.symm (e v) = q := by simp [v]
      rw [hp, hq]
      simpa [p, q] using ggQ2s08bf4_coxeterB_double lab.rank (by omega)
    exact hcontra4 u v huv hMx4
  have hcontraDreindex : (∃ e' : Fin lab.rank ≃ M.Λ,
      M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e') → False := by
    rintro ⟨e', he'⟩
    let i0 : Fin lab.rank := e.symm (e' ⟨lab.rank - 3, by omega⟩)
    let j1 : Fin lab.rank := e.symm (e' ⟨lab.rank - 4, by omega⟩)
    let j2 : Fin lab.rank := e.symm (e' ⟨lab.rank - 2, by omega⟩)
    let j3 : Fin lab.rank := e.symm (e' ⟨lab.rank - 1, by omega⟩)
    have hDij : ∀ (u v : Fin lab.rank) (a b : Fin lab.rank),
        e'.symm (e u) = a → e'.symm (e v) = b →
        Mx u v = ggCoxeterMatrixD lab.rank a b := by
      intro u v a b ha hb
      rw [hMx u v, he', CoxeterMatrix.reindex_apply, ha, hb]
    have h01 : Mx i0 j1 = 3 := by
      rw [hDij i0 j1 ⟨lab.rank - 3, by omega⟩ ⟨lab.rank - 4, by omega⟩
        (by simp [i0]) (by simp [j1])]
      simpa using ggQ2s08bf4_coxeterD_adj1 lab.rank hrank
    have h02 : Mx i0 j2 = 3 := by
      rw [hDij i0 j2 ⟨lab.rank - 3, by omega⟩ ⟨lab.rank - 2, by omega⟩
        (by simp [i0]) (by simp [j2])]
      simpa using ggQ2s08bf4_coxeterD_adj2 lab.rank hrank
    have h03 : Mx i0 j3 = 3 := by
      rw [hDij i0 j3 ⟨lab.rank - 3, by omega⟩ ⟨lab.rank - 1, by omega⟩
        (by simp [i0]) (by simp [j3])]
      simpa using ggQ2s08bf4_coxeterD_adj3 lab.rank hrank
    have h12 : Mx j1 j2 = 2 := by
      rw [hDij j1 j2 ⟨lab.rank - 4, by omega⟩ ⟨lab.rank - 2, by omega⟩
        (by simp [j1]) (by simp [j2])]
      simpa using ggQ2s08bf4_coxeterD_nonadj12 lab.rank hrank
    have h13 : Mx j1 j3 = 2 := by
      rw [hDij j1 j3 ⟨lab.rank - 4, by omega⟩ ⟨lab.rank - 1, by omega⟩
        (by simp [j1]) (by simp [j3])]
      simpa using ggQ2s08bf4_coxeterD_nonadj13 lab.rank hrank
    have h23 : Mx j2 j3 = 2 := by
      rw [hDij j2 j3 ⟨lab.rank - 2, by omega⟩ ⟨lab.rank - 1, by omega⟩
        (by simp [j2]) (by simp [j3])]
      simpa using ggQ2s08bf4_coxeterD_nonadj23 lab.rank hrank
    have hne_phi : ∀ {u v : Fin lab.rank}, u ≠ v → e.symm (e' u) ≠ e.symm (e' v) :=
      fun huv h => huv (e'.injective (e.symm.injective h))
    have hne01 : i0 ≠ j1 := hne_phi (by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
    have hne02 : i0 ≠ j2 := hne_phi (by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
    have hne03 : i0 ≠ j3 := hne_phi (by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
    have hne12 : j1 ≠ j2 := hne_phi (by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
    have hne13 : j1 ≠ j3 := hne_phi (by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
    have hne23 : j2 ≠ j3 := hne_phi (by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
    have hrel3 : ∀ {u v : Fin lab.rank}, u ≠ v → Mx u v = 3 → (σ u * σ v) ^ 3 = 1 := by
      intro u v huv huv3
      have h := hrel u v huv
      rw [huv3] at h
      exact ggQ2s08bf4_perm_pow_eq_one hf0inj
        (ggQ2s08bf4_perm_mul_apply (hσ u) (hσ v)) h
    have hcomm2 : ∀ {u v : Fin lab.rank}, u ≠ v → Mx u v = 2 → σ u * σ v = σ v * σ u := by
      intro u v huv huv2
      have h2 : (s u * s v) ^ 2 = 1 := by
        have h := hrel u v huv
        rwa [huv2] at h
      have hlin : s u * s v = s v * s u := by
        have hu := (hsrefl u).1
        have hv := (hsrefl v).1
        have h1 : (s u * s v) * (s u * s v) = 1 := by simpa [pow_two] using h2
        have h2' : (s u * s v)⁻¹ = s u * s v := _root_.inv_eq_of_mul_eq_one_right h1
        have hu' : (s u)⁻¹ = s u := _root_.inv_eq_of_mul_eq_one_right hu
        have hv' : (s v)⁻¹ = s v := _root_.inv_eq_of_mul_eq_one_right hv
        rw [← h2', _root_.mul_inv_rev, hu', hv']
      exact ggQ2s08bf4_perm_comm_of_lin_comm hf0inj (hσ u) (hσ v) hlin
    exact ggQ2s08core_no_fork (hσswap i0) (hσswap j1) (hσswap j2) (hσswap j3)
      (hσne hne01) (hσne hne02) (hσne hne03) (hσne hne12) (hσne hne13) (hσne hne23)
      (hrel3 hne01 h01) (hrel3 hne02 h02) (hrel3 hne03 h03)
      (hcomm2 hne12 h12) (hcomm2 hne13 h13) (hcomm2 hne23 h23)
  have htag : lab.tag = .twA := by
    rcases htags with h | h | h | h | h
    · exact h
    · exfalso
      obtain ⟨e', he'⟩ : ∃ e' : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.B lab.rank).reindex e' := by
        simpa [GGQ2LabelWeyl, h] using hMW
      exact hcontraBreindex ⟨e', he'⟩
    · exfalso
      obtain ⟨e', he'⟩ : ∃ e' : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.B lab.rank).reindex e' := by
        simpa [GGQ2LabelWeyl, h] using hMW
      exact hcontraBreindex ⟨e', he'⟩
    · exfalso
      obtain ⟨e', he'⟩ : ∃ e' : Fin lab.rank ≃ M.Λ,
          M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e' := by
        simpa [GGQ2LabelWeyl, h] using hMW
      exact hcontraDreindex ⟨e', he'⟩
    · exfalso
      obtain ⟨e', he'⟩ : ∃ e' : Fin lab.rank ≃ M.Λ,
          M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e' := by
        simpa [GGQ2LabelWeyl, h] using hMW
      exact hcontraDreindex ⟨e', he'⟩
  have hWmap : (ggAutomizer L Bs).map (ggQ2CellLin M κ) = Subgroup.closure (Set.range s) :=
    ggQ2Cell_map_automizer_L M κ e s hs
  refine ⟨htag, hEven, fun i => κ.symm (f0 i), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hli.map' κ.symm.toLinearMap (LinearMap.ker_eq_bot.mpr κ.symm.injective)
    · have hrange : Set.range (fun i => κ.symm (f0 i)) = κ.symm '' Set.range f0 :=
        Set.range_comp κ.symm f0
      have hset : κ.symm '' Set.range f0 = κ.symm.toLinearMap '' Set.range f0 := rfl
      rw [hrange, hset, ← Submodule.map_span κ.symm.toLinearMap (Set.range f0), hspan]
      simp
    · apply κ.injective
      rw [map_sum, hsum]
      simp
    · intro a ha
      have haW : ggQ2CellLin M κ a ∈ Subgroup.closure (Set.range s) := by
        rw [← hWmap]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      obtain ⟨τ, hτ⟩ := hperm (ggQ2CellLin M κ a) haW
      refine ⟨τ, fun i => ?_⟩
      have h1 := hτ i
      simp only [ggQ2CellLin_apply] at h1
      apply κ.injective
      rw [h1, LinearEquiv.apply_symm_apply]
  · intro a
    have hκf : (fun i => κ (κ.symm (f0 i))) = f0 := by funext i; simp
    rw [hκf]; exact hRmono a
  · intro a
    have hκf : (fun i => κ (κ.symm (f0 i))) = f0 := by funext i; simp
    rw [hκf]; exact hM0mono a

end CFSG.StandardType

end
