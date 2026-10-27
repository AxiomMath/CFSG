module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTenEn

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ASVolI.ChIJK Equiv

variable {Γ : Type} [Group Γ] {n : ℕ} {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

structure SwapDisjoint (ε : Γ →* Perm (Fin n)) (ρ : Representation (ZMod 2) Γ M) : Prop where
  ker_trivial : ∀ g : Γ, ε g = 1 → ρ g = 1
  disjoint : ∀ g h : Γ, (ε g).IsSwap → (ε h).IsSwap → ε g ≠ ε h →
    LinearMap.range (ρ g - 1) ⊓ LinearMap.range (ρ h - 1) = ⊥

variable {ε : Γ →* Perm (Fin n)} {ρ : Representation (ZMod 2) Γ M}

private lemma seven_ten_alg_add_self_eq_zero {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (x : A) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_smul]

private lemma seven_ten_alg_neg_eq_self {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (x : A) : -x = x := by
  have h : x + x = 0 := seven_ten_alg_add_self_eq_zero x
  calc -x = -x + 0 := (add_zero _).symm
    _ = -x + (x + x) := by rw [h]
    _ = (-x + x) + x := by abel
    _ = x := by rw [neg_add_cancel, zero_add]

private lemma seven_ten_alg_sub_eq_add {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (x y : A) : x - y = x + y := by
  rw [sub_eq_add_neg, seven_ten_alg_neg_eq_self y]

private lemma seven_ten_alg_rho_eq_of_eps_eq (hS : SwapDisjoint ε ρ) {x y : Γ}
    (h : ε x = ε y) : ρ x = ρ y := by
  have hk : ε (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, h]
    simp
  have hxy : x = y * (y⁻¹ * x) := by group
  calc ρ x = ρ (y * (y⁻¹ * x)) := congrArg ρ hxy
    _ = ρ y * ρ (y⁻¹ * x) := map_mul ρ y (y⁻¹ * x)
    _ = ρ y * 1 := by rw [hS.ker_trivial (y⁻¹ * x) hk]
    _ = ρ y := mul_one _

theorem SwapDisjoint.rho_mul_comm (hS : SwapDisjoint ε ρ) {g h : Γ}
    (hc : Commute (ε g) (ε h)) : ρ g * ρ h = ρ h * ρ g := by
  set k : Γ := (h * g)⁻¹ * (g * h) with hk
  have hεk : ε k = 1 := by
    rw [hk, map_mul, map_inv, map_mul, map_mul, hc.eq]
    simp
  have hgh : g * h = (h * g) * k := by
    rw [hk]; group
  calc ρ g * ρ h = ρ (g * h) := (map_mul ρ g h).symm
    _ = ρ ((h * g) * k) := by rw [hgh]
    _ = ρ (h * g) * ρ k := map_mul ρ (h * g) k
    _ = ρ (h * g) * 1 := by rw [hS.ker_trivial k hεk]
    _ = ρ (h * g) := mul_one _
    _ = ρ h * ρ g := map_mul ρ h g

theorem SwapDisjoint.sub_one_mul_sub_one_eq_zero (hS : SwapDisjoint ε ρ) {g h : Γ}
    (hg : (ε g).IsSwap) (hh : (ε h).IsSwap) (hc : Commute (ε g) (ε h)) (hne : ε g ≠ ε h) :
    (ρ g - 1) * (ρ h - 1) = 0 := by
  have hcomm : (ρ g - 1) * (ρ h - 1) = (ρ h - 1) * (ρ g - 1) := by
    have hmul := hS.rho_mul_comm hc
    calc (ρ g - 1) * (ρ h - 1) = ρ g * ρ h - ρ h - ρ g + 1 := by noncomm_ring
      _ = ρ h * ρ g - ρ h - ρ g + 1 := by rw [hmul]
      _ = (ρ h - 1) * (ρ g - 1) := by noncomm_ring
  refine LinearMap.ext fun m => ?_
  have hmemg : ((ρ g - 1) * (ρ h - 1)) m ∈ LinearMap.range (ρ g - 1) :=
    ⟨(ρ h - 1) m, by rw [Module.End.mul_apply]⟩
  have hmemh : ((ρ g - 1) * (ρ h - 1)) m ∈ LinearMap.range (ρ h - 1) := by
    rw [hcomm]
    exact ⟨(ρ g - 1) m, by rw [Module.End.mul_apply]⟩
  have hmem : ((ρ g - 1) * (ρ h - 1)) m ∈
      LinearMap.range (ρ g - 1) ⊓ LinearMap.range (ρ h - 1) :=
    Submodule.mem_inf.mpr ⟨hmemg, hmemh⟩
  rw [hS.disjoint g h hg hh hne] at hmem
  simpa using hmem

theorem SwapDisjoint.apply_eq_self_of_mem_range (hS : SwapDisjoint ε ρ) {g : Γ}
    (hg : (ε g).IsSwap) {w : M} (hw : w ∈ LinearMap.range (ρ g - 1)) : ρ g w = w := by
  obtain ⟨m, rfl⟩ := hw
  have hgg : ε (g * g) = 1 := by
    obtain ⟨x, y, hxy, hgxy⟩ := hg
    rw [map_mul, hgxy, Equiv.swap_mul_self]
  have hsq : (ρ g - 1) * (ρ g - 1) = 0 := by
    have hexp : (ρ g - 1) * (ρ g - 1) = ρ g * ρ g + 1 := by
      calc (ρ g - 1) * (ρ g - 1) = ρ g * ρ g - (ρ g + ρ g) + 1 := by noncomm_ring
        _ = ρ g * ρ g + 1 := by
              rw [seven_ten_alg_add_self_eq_zero (ρ g)]
              abel
    rw [hexp, ← map_mul ρ g g, hS.ker_trivial (g * g) hgg]
    exact seven_ten_alg_add_self_eq_zero (1 : M →ₗ[ZMod 2] M)
  have hzero : ρ g ((ρ g - 1) m) - ((ρ g - 1) m) = 0 := by
    have := congrArg (fun f : M →ₗ[ZMod 2] M => f m) hsq
    simpa [Module.End.mul_apply] using this
  exact sub_eq_zero.mp hzero

theorem SwapDisjoint.apply_eq_of_fixes (hS : SwapDisjoint ε ρ) (hε : Function.Surjective ε)
    {s g : Γ} {a b : Fin n} (hab : a ≠ b) (hs : ε s = swap a b) (ha : ε g a = a)
    (hb : ε g b = b) {w : M} (hw : w ∈ LinearMap.range (ρ s - 1)) : ρ g w = w := by
  obtain ⟨m, rfl⟩ := hw
  let P : Perm (Fin n) → Prop :=
    fun σ => ∀ g' : Γ, ε g' = σ → ρ g' ((ρ s - 1) m) = (ρ s - 1) m
  have hPg : P (ε g) := by
    refine Subgroup.closure_induction (p := fun σ _ => P σ) ?_ ?_ ?_ ?_
      (mem_closure_isSwap_fixing_two ha hb)
    · intro τ hτ g' hg'
      obtain ⟨hτswap, hτa, hτb⟩ := hτ
      obtain ⟨k, l, hkl, hτkl⟩ := hτswap
      have hs_swap : (ε s).IsSwap := by rw [hs]; exact ⟨a, b, hab, rfl⟩
      have hτ_swap : (ε g').IsSwap := by rw [hg', hτkl]; exact ⟨k, l, hkl, rfl⟩
      have hta : swap k l a = a := by rw [← hτkl]; exact hτa
      have htb : swap k l b = b := by rw [← hτkl]; exact hτb
      have hka : k ≠ a := by
        intro hka
        rw [hka, Equiv.swap_apply_left] at hta
        exact hkl (hka.trans hta.symm)
      have hkb : k ≠ b := by
        intro hkb
        rw [hkb, Equiv.swap_apply_left] at htb
        exact hkl (hkb.trans htb.symm)
      have hla : l ≠ a := by
        intro hla
        rw [hla, Equiv.swap_apply_right] at hta
        exact hkl (hta.trans hla.symm)
      have hlb : l ≠ b := by
        intro hlb
        rw [hlb, Equiv.swap_apply_right] at htb
        exact hkl (htb.trans hlb.symm)
      have hnodup : [k, l, a, b].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
          List.nodup_nil, and_true, not_or]
        exact ⟨⟨hkl, hka, hkb⟩, ⟨hla, hlb⟩, hab⟩
      have hcomm : Commute (ε g') (ε s) := by
        rw [hg', hτkl, hs]
        exact (Equiv.Perm.disjoint_swap_swap hnodup).commute
      have hne : ε g' ≠ ε s := by
        rw [hg', hτkl, hs]
        intro heq
        have h1 := congrArg (fun f : Perm (Fin n) => f a) heq
        rw [hta, Equiv.swap_apply_left] at h1
        exact hab h1
      have hop := hS.sub_one_mul_sub_one_eq_zero hτ_swap hs_swap hcomm hne
      have hzero : (ρ g' - 1) ((ρ s - 1) m) = 0 := by
        have := congrArg (fun f : M →ₗ[ZMod 2] M => f m) hop
        simpa [Module.End.mul_apply] using this
      exact sub_eq_zero.mp hzero
    · intro g' hg'
      rw [hS.ker_trivial g' hg']
      rfl
    · intro σ₁ σ₂ _ _ h1 h2 g' hg'
      obtain ⟨g₁, hg₁⟩ := hε σ₁
      obtain ⟨g₂, hg₂⟩ := hε σ₂
      set k : Γ := (g₁ * g₂)⁻¹ * g' with hk
      have hεk : ε k = 1 := by
        rw [hk, map_mul, map_inv, map_mul, hg₁, hg₂, hg']
        simp
      have hgh : g' = (g₁ * g₂) * k := by
        rw [hk]; group
      calc ρ g' ((ρ s - 1) m) = ρ ((g₁ * g₂) * k) ((ρ s - 1) m) := by rw [hgh]
        _ = (ρ (g₁ * g₂) * ρ k) ((ρ s - 1) m) := by rw [map_mul]
        _ = (ρ (g₁ * g₂) * 1) ((ρ s - 1) m) := by rw [hS.ker_trivial k hεk]
        _ = ρ (g₁ * g₂) ((ρ s - 1) m) := by rw [mul_one]
        _ = ρ g₁ (ρ g₂ ((ρ s - 1) m)) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ g₁ ((ρ s - 1) m) := by rw [h2 g₂ hg₂]
        _ = (ρ s - 1) m := h1 g₁ hg₁
    · intro σ _ h1 g' hg'
      obtain ⟨g₁, hg₁⟩ := hε σ
      have hg'g₁ : ε (g' * g₁) = 1 := by
        rw [map_mul, hg', hg₁, inv_mul_cancel]
      have hgg : ρ g' * ρ g₁ = 1 := by
        rw [← map_mul, hS.ker_trivial (g' * g₁) hg'g₁]
      calc ρ g' ((ρ s - 1) m) = ρ g' (ρ g₁ ((ρ s - 1) m)) := by rw [h1 g₁ hg₁]
        _ = (ρ g' * ρ g₁) ((ρ s - 1) m) := (Module.End.mul_apply _ _ _).symm
        _ = (1 : M →ₗ[ZMod 2] M) ((ρ s - 1) m) := by rw [hgg]
        _ = (ρ s - 1) m := rfl
  exact hPg g rfl

theorem SwapDisjoint.sum_threeCycle_eq_zero (hS : SwapDisjoint ε ρ) {s c : Γ} {a b d : Fin n}
    (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d) (hs : ε s = swap a b)
    (hc : ε c = swap a b * swap b d) {w : M} (hw : w ∈ LinearMap.range (ρ s - 1)) :
    w + ρ c w + ρ c (ρ c w) = 0 := by
  obtain ⟨m, rfl⟩ := hw
  let c₀ : Perm (Fin n) := swap a b * swap b d
  have hc0 : ε c = c₀ := hc
  have hc0a : c₀ a = b := by
    show swap a b (swap b d a) = b
    rw [Equiv.swap_apply_of_ne_of_ne hab had, Equiv.swap_apply_left]
  have hc0b : c₀ b = d := by
    show swap a b (swap b d b) = d
    rw [Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
  have hc0d : c₀ d = a := by
    show swap a b (swap b d d) = a
    rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
  have hc0_3 : c₀ * c₀ * c₀ = 1 := by
    have hc0x : ∀ x : Fin n, x ≠ a → x ≠ b → x ≠ d → c₀ x = x := by
      intro x hxa hxb hxd
      show swap a b (swap b d x) = x
      rw [Equiv.swap_apply_of_ne_of_ne hxb hxd, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    ext x
    by_cases hxa : x = a
    · subst hxa; simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]; simp [hc0a, hc0b, hc0d]
    by_cases hxb : x = b
    · subst hxb; simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]; simp [hc0a, hc0b, hc0d]
    by_cases hxd : x = d
    · subst hxd; simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]; simp [hc0a, hc0b, hc0d]
    · have hx0 : c₀ x = x := hc0x x hxa hxb hxd
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      simp [hx0]
  have hτc0 : swap a b * c₀ = c₀ * c₀ * swap a b := by
    have hc0x : ∀ x : Fin n, x ≠ a → x ≠ b → x ≠ d → c₀ x = x := by
      intro x hxa hxb hxd
      show swap a b (swap b d x) = x
      rw [Equiv.swap_apply_of_ne_of_ne hxb hxd, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    ext x
    by_cases hxa : x = a
    · subst hxa
      simp only [Equiv.Perm.mul_apply]
      simp [hc0a, hc0b, hc0d]
    by_cases hxb : x = b
    · subst hxb
      simp only [Equiv.Perm.mul_apply]
      simp [hc0a, hc0b, hc0d, Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
    by_cases hxd : x = d
    · subst hxd
      simp only [Equiv.Perm.mul_apply]
      simp [hc0a, hc0b, hc0d, Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
    · have hx0 : c₀ x = x := hc0x x hxa hxb hxd
      have hxt : swap a b x = x := Equiv.swap_apply_of_ne_of_ne hxa hxb
      simp only [Equiv.Perm.mul_apply]
      simp [hx0, hxt]
  have hτc02 : swap a b * c₀ * c₀ = c₀ * swap a b := by
    have hc0x : ∀ x : Fin n, x ≠ a → x ≠ b → x ≠ d → c₀ x = x := by
      intro x hxa hxb hxd
      show swap a b (swap b d x) = x
      rw [Equiv.swap_apply_of_ne_of_ne hxb hxd, Equiv.swap_apply_of_ne_of_ne hxa hxb]
    ext x
    by_cases hxa : x = a
    · subst hxa
      simp only [Equiv.Perm.mul_apply]
      simp [hc0a, hc0b, hc0d, Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
    by_cases hxb : x = b
    · subst hxb
      simp only [Equiv.Perm.mul_apply]
      simp [hc0a, hc0b, hc0d, Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
    by_cases hxd : x = d
    · subst hxd
      simp only [Equiv.Perm.mul_apply]
      simp [hc0a, hc0b, hc0d, Equiv.swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
    · have hx0 : c₀ x = x := hc0x x hxa hxb hxd
      have hxt : swap a b x = x := Equiv.swap_apply_of_ne_of_ne hxa hxb
      simp only [Equiv.Perm.mul_apply]
      simp [hx0, hxt]
  have hc0_τ : c₀ * swap a b * c₀⁻¹ = swap b d := by
    rw [← Equiv.swap_apply_apply c₀ a b, hc0a, hc0b]
  have hperm : ε (s * c) = ε ((c * c) * s) := by
    rw [map_mul, map_mul, map_mul, hs, hc0]
    exact hτc0
  have hperm2 : ε (s * (c * c)) = ε (c * s) := by
    rw [map_mul, map_mul, map_mul, hs, hc0]
    simpa only [mul_assoc] using hτc02
  let e : M →ₗ[ZMod 2] M := 1 + ρ c + ρ c * ρ c
  have hc3 : ρ c * ρ c * ρ c = 1 := by
    have hc3' : ρ c * ρ c * ρ c = ρ (c * c * c) := by rw [← map_mul, ← map_mul]
    rw [hc3']
    exact hS.ker_trivial (c * c * c) (by rw [map_mul, map_mul, hc0, hc0_3])
  have hce : ρ c * e = e := by
    change ρ c * (1 + ρ c + ρ c * ρ c) = 1 + ρ c + ρ c * ρ c
    calc ρ c * (1 + ρ c + ρ c * ρ c)
        = ρ c + ρ c * ρ c + ρ c * ρ c * ρ c := by noncomm_ring
      _ = ρ c + ρ c * ρ c + 1 := by rw [hc3]
      _ = 1 + ρ c + ρ c * ρ c := by abel
  have hsc : ρ s * ρ c = ρ c * ρ c * ρ s := by
    calc ρ s * ρ c = ρ (s * c) := (map_mul ρ s c).symm
      _ = ρ ((c * c) * s) := seven_ten_alg_rho_eq_of_eps_eq hS hperm
      _ = ρ (c * c) * ρ s := map_mul ρ (c * c) s
      _ = (ρ c * ρ c) * ρ s := by rw [map_mul]
      _ = ρ c * ρ c * ρ s := rfl
  have hscc : ρ s * (ρ c * ρ c) = ρ c * ρ s := by
    calc ρ s * (ρ c * ρ c) = ρ s * ρ (c * c) := by rw [map_mul]
      _ = ρ (s * (c * c)) := (map_mul ρ s (c * c)).symm
      _ = ρ (c * s) := seven_ten_alg_rho_eq_of_eps_eq hS hperm2
      _ = ρ c * ρ s := map_mul ρ c s
  have hse : ρ s * e = e * ρ s := by
    change ρ s * (1 + ρ c + ρ c * ρ c) = (1 + ρ c + ρ c * ρ c) * ρ s
    calc ρ s * (1 + ρ c + ρ c * ρ c)
        = ρ s + ρ s * ρ c + ρ s * (ρ c * ρ c) := by noncomm_ring
      _ = ρ s + ρ c * ρ c * ρ s + ρ c * ρ s := by rw [hsc, hscc]
      _ = (1 + ρ c + ρ c * ρ c) * ρ s := by noncomm_ring
  have hce_m : ∀ x : M, ρ c (e x) = e x := fun x => by
    have := congrArg (fun f : M →ₗ[ZMod 2] M => f x) hce
    simpa [Module.End.mul_apply] using this
  have hse_m : ∀ x : M, ρ s (e x) = e (ρ s x) := fun x => by
    have := congrArg (fun f : M →ₗ[ZMod 2] M => f x) hse
    simpa [Module.End.mul_apply] using this
  have ht : ε (c * s * c⁻¹) = swap b d := by
    rw [map_mul, map_mul, map_inv, hs, hc0]
    exact hc0_τ
  have ht_swap : (ε (c * s * c⁻¹)).IsSwap := by
    rw [ht]; exact ⟨b, d, hbd, rfl⟩
  have hs_swap : (ε s).IsSwap := by rw [hs]; exact ⟨a, b, hab, rfl⟩
  have hne : ε s ≠ ε (c * s * c⁻¹) := by
    rw [hs, ht]
    intro heq
    have h1 := congrArg (fun f : Perm (Fin n) => f a) heq
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab had] at h1
    exact hab h1.symm
  have hfix : ∀ m : M, (ρ s - 1) (e m) = 0 := by
    intro m
    set m' : M := e m
    have hcm : ρ c m' = m' := hce_m m
    have hsm : ρ s m' = e (ρ s m) := hse_m m
    have hcs : ρ c (ρ s m') = ρ s m' := by
      rw [hsm]
      exact hce_m (ρ s m)
    have hcinv : ρ (c⁻¹) m' = m' := by
      have hm : ρ (c⁻¹) * ρ c = 1 := by
        rw [← map_mul ρ (c⁻¹) c, inv_mul_cancel, map_one]
      calc ρ (c⁻¹) m' = ρ (c⁻¹) (ρ c m') := by rw [hcm]
        _ = (ρ (c⁻¹) * ρ c) m' := (Module.End.mul_apply _ _ _).symm
        _ = (1 : M →ₗ[ZMod 2] M) m' := by rw [hm]
        _ = m' := Module.End.one_apply m'
    have htm : ρ (c * s * c⁻¹) m' = ρ s m' := by
      calc ρ (c * s * c⁻¹) m' = (ρ c * ρ s * ρ (c⁻¹)) m' := by
              rw [map_mul, map_mul]
        _ = ρ c (ρ s (ρ (c⁻¹) m')) := by
              simp only [Module.End.mul_apply]
        _ = ρ c (ρ s m') := by rw [hcinv]
        _ = ρ s m' := hcs
    have hmem : (ρ s - 1) m' ∈
        LinearMap.range (ρ s - 1) ⊓ LinearMap.range (ρ (c * s * c⁻¹) - 1) := by
      refine Submodule.mem_inf.mpr ⟨⟨m', rfl⟩, ⟨m', ?_⟩⟩
      show (ρ (c * s * c⁻¹) - 1) m' = (ρ s - 1) m'
      rw [LinearMap.sub_apply, LinearMap.sub_apply, htm]
    rw [hS.disjoint s (c * s * c⁻¹) hs_swap ht_swap hne] at hmem
    simpa using hmem
  have he_sub : e * (ρ s - 1) = (ρ s - 1) * e := by
    have h1 : e * ρ s = ρ s * e := hse.symm
    calc e * (ρ s - 1) = e * ρ s - e * 1 := by rw [mul_sub]
      _ = ρ s * e - e := by rw [h1, mul_one]
      _ = (ρ s - 1) * e := by rw [sub_mul, one_mul]
  have heX : e ((ρ s - 1) m) = 0 := by
    calc e ((ρ s - 1) m) = (e * (ρ s - 1)) m := (Module.End.mul_apply e (ρ s - 1) m).symm
      _ = ((ρ s - 1) * e) m := by rw [he_sub]
      _ = (ρ s - 1) (e m) := Module.End.mul_apply (ρ s - 1) e m
      _ = 0 := hfix m
  have heXexpand : e ((ρ s - 1) m) =
      (ρ s - 1) m + ρ c ((ρ s - 1) m) + ρ c (ρ c ((ρ s - 1) m)) := by
    change (1 + ρ c + ρ c * ρ c) ((ρ s - 1) m) =
      (ρ s - 1) m + ρ c ((ρ s - 1) m) + ρ c (ρ c ((ρ s - 1) m))
    simp only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply]
  rw [← heXexpand, heX]

private noncomputable def seven_ten_alg_W2 {Γ : Type} [Group Γ] {n : ℕ} {M : Type}
    [AddCommGroup M] [Module (ZMod 2) M] (ε : Γ →* Perm (Fin n))
    (ρ : Representation (ZMod 2) Γ M) (hε : Function.Surjective ε) {a b : Fin n}
    (hab : a ≠ b) (w : M) (i j : Fin n) : M :=
  if hij : i = j then 0
  else
    ρ (Classical.choose (hε (Classical.choose (exists_perm_apply_two hab hij)))) w

theorem SwapDisjoint.exists_equivariant_evenWeight (hS : SwapDisjoint ε ρ) (hn : 3 ≤ n)
    (hε : Function.Surjective ε) {s : Γ} {a b : Fin n} (hab : a ≠ b) (hs : ε s = swap a b)
    {w : M} (hw : w ∈ LinearMap.range (ρ s - 1)) :
    ∃ f : evenWeight n →ₗ[ZMod 2] M,
      (∀ (g : Γ) (x : evenWeight n), f (evenWeightRep n (ε g) x) = ρ g (f x)) ∧
        f (evenPair n a b) = w := by
  let W₂ : Fin n → Fin n → M := seven_ten_alg_W2 ε ρ hε hab w
  have W₂_eq : ∀ (h : Γ) (i j : Fin n), ε h a = i → ε h b = j → i ≠ j →
      W₂ i j = ρ h w := by
    intro h i j hi hj hij
    change seven_ten_alg_W2 ε ρ hε hab w i j = ρ h w
    rw [seven_ten_alg_W2, dif_neg hij]
    let σ : Perm (Fin n) := Classical.choose (exists_perm_apply_two hab hij)
    let g₀ : Γ := Classical.choose (hε σ)
    change ρ g₀ w = ρ h w
    have hσa : σ a = i := (Classical.choose_spec (exists_perm_apply_two hab hij)).1
    have hσb : σ b = j := (Classical.choose_spec (exists_perm_apply_two hab hij)).2
    have hg₀ : ε g₀ = σ := Classical.choose_spec (hε σ)
    have hka : ε (g₀⁻¹ * h) a = a := by
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
      rw [hg₀, hi, ← hσa]
      simpa using Equiv.symm_apply_apply σ a
    have hkb : ε (g₀⁻¹ * h) b = b := by
      simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
      rw [hg₀, hj, ← hσb]
      simpa using Equiv.symm_apply_apply σ b
    have hkw : ρ (g₀⁻¹ * h) w = w := hS.apply_eq_of_fixes hε hab hs hka hkb hw
    calc ρ g₀ w = ρ g₀ (ρ (g₀⁻¹ * h) w) := by rw [hkw]
      _ = (ρ g₀ * ρ (g₀⁻¹ * h)) w := rfl
      _ = ρ (g₀ * (g₀⁻¹ * h)) w := by simp only [map_mul]
      _ = ρ h w := by rw [show g₀ * (g₀⁻¹ * h) = h by group]
  have W₂_ab : W₂ a b = w := by
    rw [W₂_eq 1 a b (by simp) (by simp) hab, map_one, Module.End.one_apply]
  have W₂_aa : ∀ i : Fin n, W₂ i i = 0 := by
    intro i
    change seven_ten_alg_W2 ε ρ hε hab w i i = 0
    rw [seven_ten_alg_W2, dif_pos rfl]
  have W₂_symm : ∀ i j : Fin n, W₂ j i = W₂ i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · let σ : Perm (Fin n) := Classical.choose (exists_perm_apply_two hab hij)
      let h : Γ := Classical.choose (hε σ)
      have hσa : σ a = i := (Classical.choose_spec (exists_perm_apply_two hab hij)).1
      have hσb : σ b = j := (Classical.choose_spec (exists_perm_apply_two hab hij)).2
      have hh : ε h = σ := Classical.choose_spec (hε σ)
      have hha : ε h a = i := by rw [hh, hσa]
      have hhb : ε h b = j := by rw [hh, hσb]
      have hji : j ≠ i := fun hji => hij hji.symm
      have hWij : W₂ i j = ρ h w := W₂_eq h i j hha hhb hij
      have hWji : W₂ j i = ρ (h * s) w := by
        refine W₂_eq (h * s) j i ?_ ?_ hji
        · show ε (h * s) a = j
          rw [map_mul, hh, hs]
          simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hσb]
        · show ε (h * s) b = i
          rw [map_mul, hh, hs]
          simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hσa]
      rw [hWji, hWij]
      calc ρ (h * s) w = (ρ h * ρ s) w := by rw [map_mul]
        _ = ρ h (ρ s w) := rfl
        _ = ρ h w := by
              rw [hS.apply_eq_self_of_mem_range (g := s)
                (by rw [hs]; exact ⟨a, b, hab, rfl⟩) hw]
  have W₂_equiv : ∀ (g : Γ) (i j : Fin n),
      ρ g (W₂ i j) = W₂ (ε g i) (ε g j) := by
    intro g i j
    by_cases hij : i = j
    · rw [hij]
      rw [W₂_aa j, map_zero, W₂_aa (ε g j)]
    · let σ : Perm (Fin n) := Classical.choose (exists_perm_apply_two hab hij)
      let h : Γ := Classical.choose (hε σ)
      have hσa : σ a = i := (Classical.choose_spec (exists_perm_apply_two hab hij)).1
      have hσb : σ b = j := (Classical.choose_spec (exists_perm_apply_two hab hij)).2
      have hh : ε h = σ := Classical.choose_spec (hε σ)
      have hha : ε h a = i := by rw [hh, hσa]
      have hhb : ε h b = j := by rw [hh, hσb]
      have hWij : W₂ i j = ρ h w := W₂_eq h i j hha hhb hij
      have hne : ε g i ≠ ε g j := fun hcon => hij ((ε g).injective hcon)
      have hWh : W₂ (ε g i) (ε g j) = ρ (g * h) w := by
        refine W₂_eq (g * h) (ε g i) (ε g j) ?_ ?_ hne
        · show ε (g * h) a = ε g i
          rw [map_mul]
          simp only [Equiv.Perm.mul_apply, hha]
        · show ε (g * h) b = ε g j
          rw [map_mul]
          simp only [Equiv.Perm.mul_apply, hhb]
      rw [hWij, hWh, map_mul]
      rfl
  obtain ⟨d, hda, hdb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  have hbd : b ≠ d := hdb.symm
  have had : a ≠ d := hda.symm
  obtain ⟨c, hc⟩ := hε (swap a b * swap b d)
  have hca : ε c a = b := by
    rw [hc, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab had, Equiv.swap_apply_left]
  have hcb : ε c b = d := by
    rw [hc, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hda hdb]
  have hcd : ε c d = a := by
    rw [hc, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
  have hWbd : W₂ b d = ρ c w := W₂_eq c b d hca hcb hbd
  have hWc2a : ε (c * c) a = d := by
    simp only [map_mul, Equiv.Perm.mul_apply, hca, hcb]
  have hWc2b : ε (c * c) b = a := by
    simp only [map_mul, Equiv.Perm.mul_apply, hcb, hcd]
  have hWad : W₂ a d = ρ (c * c) w := by
    rw [← W₂_symm a d]
    exact W₂_eq (c * c) d a hWc2a hWc2b (Ne.symm had)
  have hbase : W₂ a b + W₂ b d + W₂ a d = 0 := by
    have hsum := hS.sum_threeCycle_eq_zero hab hbd had hs hc hw
    rw [W₂_ab, hWbd, hWad, map_mul]
    simpa only [Module.End.mul_apply] using hsum
  have W₂_triple : ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
      W₂ i j + W₂ j k + W₂ i k = 0 := by
    intro i j k hij hjk hik
    obtain ⟨σ, hσa, hσb, hσd⟩ := exists_perm_apply_three hab had hbd hij hik hjk
    obtain ⟨g, hg⟩ := hε σ
    have htrans := congrArg (fun x : M => ρ g x) hbase
    simp only [map_add, map_zero] at htrans
    rw [W₂_equiv g a b, W₂_equiv g b d, W₂_equiv g a d] at htrans
    rw [hg, hσa, hσb, hσd] at htrans
    exact htrans
  have W₂_pair : ∀ i j : Fin n, W₂ a i + W₂ a j = W₂ i j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
      rw [seven_ten_alg_add_self_eq_zero (W₂ a j), W₂_aa j]
    by_cases hia : i = a
    · rw [hia]
      rw [W₂_aa a, zero_add]
    by_cases hja : j = a
    · rw [hja]
      rw [W₂_aa a, add_zero, W₂_symm i a]
    · have hai : a ≠ i := fun h => hia h.symm
      have haj : a ≠ j := fun h => hja h.symm
      have htriple := W₂_triple a i j hai hij haj
      have hzero : W₂ a i + W₂ a j + W₂ i j = 0 := by
        rw [show W₂ a i + W₂ a j + W₂ i j = W₂ a i + W₂ i j + W₂ a j by abel]
        exact htriple
      rw [← sub_eq_zero, seven_ten_alg_sub_eq_add]
      exact hzero
  let θ : (Fin n → ZMod 2) →ₗ[ZMod 2] M :=
    Fintype.linearCombination (ZMod 2) (fun i => W₂ a i)
  let f : evenWeight n →ₗ[ZMod 2] M := θ.comp (evenWeight n).subtype
  have f_pair : ∀ i j : Fin n, f (evenPair n i j) = W₂ i j := by
    intro i j
    change θ (((evenPair n i j : evenWeight n)) : Fin n → ZMod 2) = W₂ i j
    rw [show (((evenPair n i j : evenWeight n)) : Fin n → ZMod 2) =
        Pi.single i 1 + Pi.single j 1 from rfl]
    rw [map_add, Fintype.linearCombination_apply_single,
      Fintype.linearCombination_apply_single]
    simp only [one_smul]
    exact W₂_pair i j
  have hspan : Submodule.span (ZMod 2)
      (Set.range fun p : Fin n × Fin n => evenPair n p.1 p.2) = ⊤ :=
    span_evenPair_eq_top (by omega)
  refine ⟨f, ?_, ?_⟩
  · intro g
    let F : evenWeight n →ₗ[ZMod 2] M := f.comp (evenWeightRep n (ε g))
    let G : evenWeight n →ₗ[ZMod 2] M := (ρ g).comp f
    have hFG : F = G := by
      apply LinearMap.ext_on hspan
      rintro _ ⟨p, rfl⟩
      obtain ⟨i, j⟩ := p
      show f (evenWeightRep n (ε g) (evenPair n i j)) = ρ g (f (evenPair n i j))
      rw [evenWeightRep_evenPair, f_pair, f_pair, W₂_equiv]
    intro x
    exact LinearMap.congr_fun hFG x
  · rw [f_pair a b, W₂_ab]

end CFSG.LocalAnalysis.WeakClosure81
