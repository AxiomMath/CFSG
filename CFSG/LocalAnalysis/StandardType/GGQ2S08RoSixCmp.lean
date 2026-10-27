module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixRefl
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoSixPath

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly E6QTwo


section Comb

variable {A : Type} [CommGroup A] [Finite A]

private theorem cmp_pow_three (hA : Nat.card A = 3) (a : A) : a ^ 3 = 1 := by
  rw [← hA]
  exact pow_card_eq_one'

private theorem cmp_exists_ne_one (hA : Nat.card A = 3) : ∃ ζ : A, ζ ≠ 1 := by
  by_contra h
  push Not at h
  have : Subsingleton A := ⟨fun a b => by rw [h a, h b]⟩
  rw [Nat.card_unique] at hA
  omega

private theorem cmp_eq_one_of_pow (hA : Nat.card A = 3) {r : A} {n : ℕ} (hn : ¬ 3 ∣ n)
    (hr : r ^ n = 1) : r = 1 := by
  have h1 : orderOf r ∣ n := orderOf_dvd_of_pow_eq_one hr
  have h2 : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one (cmp_pow_three hA r)
  have h3 : orderOf r ∣ Nat.gcd n 3 := Nat.dvd_gcd h1 h2
  have hg : Nat.gcd n 3 = 1 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn).symm
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

private theorem cmp_pow_eq_one_of_dvd (hA : Nat.card A = 3) {n : ℕ} (hn : 3 ∣ n) (a : A) :
    a ^ n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [pow_mul, cmp_pow_three hA, one_pow]

theorem ggQ2s08r6_swap_of_refl_mod (hA : Nat.card A = 3) {τ : Equiv.Perm (Fin 6)} (hτ : τ ≠ 1)
    {s : Fin 6 → A}
    (hrefl : ∀ σ : Fin 6 → A, ∃ (n : ℕ) (μ : A), ∀ i, σ (τ.symm i) = μ * (σ i * s i ^ n)) :
    τ.IsSwap := by
  classical
  obtain ⟨ζ, hζ⟩ := cmp_exists_ne_one hA
  obtain ⟨c, hc⟩ : ∃ c, τ c ≠ c := by
    by_contra h
    push Not at h
    exact hτ (Equiv.ext h)
  have key : ∀ c', τ c' ≠ c' → c' = c ∨ c' = τ c := by
    intro c' hc'
    by_contra hne
    push Not at hne
    obtain ⟨i₁, h1, h2, h3, h4⟩ : ∃ i : Fin 6, i ≠ c ∧ i ≠ τ c ∧ i ≠ c' ∧ i ≠ τ c' := by
      have : ∀ a b a' b' : Fin 6, ∃ i : Fin 6, i ≠ a ∧ i ≠ b ∧ i ≠ a' ∧ i ≠ b' := by decide
      exact this _ _ _ _
    have hsymm : ∀ {a b : Fin 6}, b ≠ τ a → τ.symm b ≠ a := fun hab h => hab (by
      rw [← h, Equiv.apply_symm_apply])
    obtain ⟨n₁, μ₁, e₁⟩ := hrefl (Pi.mulSingle c ζ)
    obtain ⟨n₂, μ₂, e₂⟩ := hrefl (Pi.mulSingle c' ζ)
    have q1 := e₁ i₁
    have q2 := e₁ c'
    have q3 := e₁ c
    have q4 := e₂ i₁
    have q5 := e₂ c'
    rw [Pi.mulSingle_eq_of_ne (hsymm h2), Pi.mulSingle_eq_of_ne h1, one_mul] at q1
    rw [Pi.mulSingle_eq_of_ne (hsymm hne.2), Pi.mulSingle_eq_of_ne hne.1, one_mul] at q2
    rw [Pi.mulSingle_eq_of_ne (hsymm (Ne.symm hc)), Pi.mulSingle_eq_same] at q3
    rw [Pi.mulSingle_eq_of_ne (hsymm h4), Pi.mulSingle_eq_of_ne h3, one_mul] at q4
    rw [Pi.mulSingle_eq_of_ne (hsymm (Ne.symm hc')), Pi.mulSingle_eq_same] at q5
    have hn₁ : ¬ 3 ∣ n₁ := by
      intro hd
      rw [cmp_pow_eq_one_of_dvd hA hd, mul_one] at q1 q3
      rw [← q1, one_mul] at q3
      exact hζ q3.symm
    have hr : (s c' * (s i₁)⁻¹) ^ n₁ = 1 := by
      rw [mul_pow, inv_pow, mul_inv_eq_one]
      exact mul_left_cancel (q2.symm.trans q1)
    have hcc : s c' = s i₁ := mul_inv_eq_one.mp (cmp_eq_one_of_pow hA hn₁ hr)
    rw [hcc] at q5
    have : ζ * s i₁ ^ n₂ = 1 * s i₁ ^ n₂ := by
      rw [one_mul]
      exact mul_left_cancel (q5.symm.trans q4)
    exact hζ (mul_right_cancel this)
  set d := τ c with hd
  have hdd : τ d ≠ d := fun h => hc (τ.injective (by rw [h]))
  have hτd : τ d = c := by
    rcases key (τ d) (fun h => hdd (τ.injective h)) with h | h
    · exact h
    · exact absurd h hdd
  refine ⟨c, d, Ne.symm hc, Equiv.ext fun y => ?_⟩
  by_cases hyc : y = c
  · rw [hyc, Equiv.swap_apply_left]
  · by_cases hyd : y = d
    · rw [hyd, Equiv.swap_apply_right, hτd]
    · rw [Equiv.swap_apply_of_ne_of_ne hyc hyd]
      by_contra hy
      rcases key y hy with h | h
      · exact hyc h
      · exact hyd h


theorem ggQ2s08r6_perm_eq_of_forall (hA : Nat.card A = 3) {τ τ' : Equiv.Perm (Fin 6)}
    (h : ∀ σ : Fin 6 → A, ∃ μ : A, ∀ i, σ (τ.symm i) = μ * σ (τ'.symm i)) : τ = τ' := by
  classical
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k, τ.symm k ≠ τ'.symm k := by
    by_contra h'
    push Not at h'
    exact hne (Equiv.symm_bijective.injective (Equiv.ext h'))
  obtain ⟨ζ, hζ⟩ := cmp_exists_ne_one hA
  obtain ⟨μ, hμ⟩ := h (Pi.mulSingle (τ.symm k) ζ)
  obtain ⟨k', hk'1, hk'2⟩ : ∃ k' : Fin 6, k' ≠ k ∧ k' ≠ τ' (τ.symm k) := by
    have : ∀ a b : Fin 6, ∃ k' : Fin 6, k' ≠ a ∧ k' ≠ b := by decide
    exact this _ _
  have q1 := hμ k
  have q2 := hμ k'
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hk), mul_one] at q1
  have hne1 : τ.symm k' ≠ τ.symm k := fun h => hk'1 (τ.symm.injective h)
  have hne2 : τ'.symm k' ≠ τ.symm k := fun h => hk'2 (by rw [← h, Equiv.apply_symm_apply])
  rw [Pi.mulSingle_eq_of_ne hne1, Pi.mulSingle_eq_of_ne hne2, mul_one] at q2
  exact hζ (q1.trans q2.symm)

theorem ggQ2s08r6_eq_of_swap_fix (hA : Nat.card A = 3) {c d : Fin 6} (hcd : c ≠ d)
    {σ : Fin 6 → A} {μ : A} (h : ∀ i, σ ((Equiv.swap c d).symm i) = μ * σ i) : σ c = σ d := by
  have h1 := h c
  have h2 := h d
  rw [Equiv.symm_swap, Equiv.swap_apply_left] at h1
  rw [Equiv.symm_swap, Equiv.swap_apply_right] at h2
  have hμ2 : μ * μ = 1 := by
    have : σ c = (μ * μ) * σ c := by rw [mul_assoc, ← h1, ← h2]
    exact (mul_eq_right.mp this.symm)
  have hμ : μ = 1 := by
    have h3 := cmp_pow_three hA μ
    rw [pow_succ, pow_two, hμ2, one_mul] at h3
    exact h3
  rw [h1, hμ, one_mul]

end Comb

namespace GGQ2S08RoSix

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

@[expose] noncomputable def vdiag (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (v : M.V) :
    Fin 6 → c.Kˣ :=
  c.diag (Additive.toMul (M.model.symm v))

theorem vdiag_add (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (v w : M.V) :
    c.vdiag M (v + w) = c.vdiag M v * c.vdiag M w := by
  rw [vdiag, vdiag, vdiag, map_add, toMul_add, c.diag_mul]

theorem vdiag_zero (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) : c.vdiag M 0 = 1 := by
  rw [vdiag, map_zero, toMul_zero, c.diag_one]

theorem vdiag_neg (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (v : M.V) :
    c.vdiag M (-v) = (c.vdiag M v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← vdiag_add, neg_add_cancel, vdiag_zero]

theorem vdiag_sub (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (v w : M.V) :
    c.vdiag M (v - w) = c.vdiag M v * (c.vdiag M w)⁻¹ := by
  rw [sub_eq_add_neg, vdiag_add, vdiag_neg]

theorem vdiag_nsmul (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (n : ℕ) (v : M.V) :
    c.vdiag M (n • v) = c.vdiag M v ^ n := by
  induction n with
  | zero => rw [zero_smul, vdiag_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, vdiag_add, ih, pow_succ]

theorem vdiag_smul (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (a : ZMod 3) (v : M.V) :
    c.vdiag M (a • v) = c.vdiag M v ^ a.val := by
  rw [← vdiag_nsmul]
  congr 1
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul]

theorem vdiag_zero_apply (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (v : M.V) :
    c.vdiag M v (0 : Fin 6) = 1 :=
  c.diag_zero _

theorem vdiag_eq_one_iff (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (v : M.V) :
    c.vdiag M v = 1 ↔ v ∈ Submodule.span (ZMod 3) {M.xV} := by
  rw [vdiag, c.diag_eq_one_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨(n : ZMod 3), ?_⟩
    have hb : Additive.toMul (M.model.symm v) = (⟨x, M.hx⟩ : ↥Bs) ^ n :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
    have hv : M.model.symm v = n • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) := by
      rw [← ofMul_toMul (M.model.symm v), hb, ofMul_zpow]
    rw [← M.model.apply_symm_apply v, hv, map_zsmul, GGQ2LDatum.xV]
    exact (Int.cast_smul_eq_zsmul (ZMod 3) n _)
  · rintro ⟨a, ha⟩
    refine ⟨(a.val : ℤ), ?_⟩
    have ha' : v = a.val • M.xV := by
      rw [← ha]
      conv_lhs => rw [← ZMod.natCast_zmod_val a]
      rw [Nat.cast_smul_eq_nsmul]
    have hv : M.model.symm v = a.val • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) := by
      rw [ha', map_nsmul, GGQ2LDatum.xV, AddEquiv.symm_apply_apply]
    show x ^ ((a.val : ℕ) : ℤ) = _
    rw [hv, toMul_nsmul, toMul_ofMul, zpow_natCast, Subgroup.coe_pow]


theorem exists_vdiag_eq (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (σ : Fin 6 → c.Kˣ)
    (h0 : σ (0 : Fin 6) = 1) : ∃ v : M.V, c.vdiag M v = σ := by
  obtain ⟨b, hb⟩ := c.exists_diag_eq σ h0
  refine ⟨M.model (Additive.ofMul b), ?_⟩
  rw [vdiag, AddEquiv.symm_apply_apply, toMul_ofMul, hb]

theorem exists_smul_vdiag (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x)
    (σ : Fin 6 → c.Kˣ) : ∃ (v : M.V) (μ : c.Kˣ), ∀ i, σ i = μ * c.vdiag M v i := by
  obtain ⟨v, hv⟩ := c.exists_vdiag_eq M (fun i => (σ (0 : Fin 6))⁻¹ * σ i) (by simp)
  refine ⟨v, σ (0 : Fin 6), fun i => ?_⟩
  rw [hv, mul_inv_cancel_left]

theorem sub_mem_of_vdiag (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) {v w : M.V}
    {μ : c.Kˣ} (h : ∀ i, c.vdiag M v i = μ * c.vdiag M w i) :
    v - w ∈ Submodule.span (ZMod 3) {M.xV} := by
  have hμ : μ = 1 := by
    have h0 := h (0 : Fin 6)
    rw [vdiag_zero_apply, vdiag_zero_apply, mul_one] at h0
    exact h0.symm
  rw [← vdiag_eq_one_iff, vdiag_sub, mul_inv_eq_one]
  funext i
  rw [h i, hμ, one_mul]

theorem exists_perm_of_mem_automizer (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x)
    {a : MulAut ↥Bs} (ha : a ∈ ggAutomizer L Bs) :
    ∃ τ : Equiv.Perm (Fin 6), ∀ v : M.V, ∃ μ : c.Kˣ, ∀ i,
      c.vdiag M (ggLin (p := 3) M.model a v) i = μ * c.vdiag M v (τ.symm i) := by
  obtain ⟨n, hnL, hnN, hna⟩ := mem_ggAutomizer_iff.mp ha
  obtain ⟨τ, hτ⟩ := c.exists_perm_of_mem_normalizer hnL hnN
  refine ⟨τ, fun v => ?_⟩
  set b : ↥Bs := Additive.toMul (M.model.symm v) with hbdef
  have hb : n * (b : G) * n⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hnN (b : G)).mp b.2
  obtain ⟨μ, hμ⟩ := hτ b hb
  refine ⟨μ, fun i => ?_⟩
  have hv : v = M.model (Additive.ofMul b) := by rw [hbdef, ofMul_toMul, AddEquiv.apply_symm_apply]
  have hab : a b = ⟨n * (b : G) * n⁻¹, hb⟩ := Subtype.ext (hna b)
  rw [hv, ggLin_apply_ofMul, vdiag, AddEquiv.symm_apply_apply, toMul_ofMul, hab, hμ i, vdiag,
    AddEquiv.symm_apply_apply, toMul_ofMul]

theorem vdiag_rel_comp (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x)
    {A A' : M.V → M.V} {τ τ' : Equiv.Perm (Fin 6)}
    (h : ∀ v, ∃ μ : c.Kˣ, ∀ i, c.vdiag M (A v) i = μ * c.vdiag M v (τ.symm i))
    (h' : ∀ v, ∃ μ : c.Kˣ, ∀ i, c.vdiag M (A' v) i = μ * c.vdiag M v (τ'.symm i)) :
    ∀ v, ∃ μ : c.Kˣ, ∀ i, c.vdiag M (A (A' v)) i = μ * c.vdiag M v ((τ * τ').symm i) := by
  intro v
  obtain ⟨μ, hμ⟩ := h (A' v)
  obtain ⟨μ', hμ'⟩ := h' v
  refine ⟨μ * μ', fun i => ?_⟩
  rw [hμ i, hμ' (τ.symm i), Equiv.Perm.mul_def, Equiv.symm_trans_apply, mul_assoc]


theorem card_units (c : GGQ2S08RoSix Bs L x) : Nat.card c.Kˣ = 3 := by
  rw [Nat.card_units, c.hK]

theorem exists_tpath (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA)
    {e : Fin 5 ≃ M.Λ} (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) :
    ∃ b : Fin 6 ≃ Fin 6, ∀ (k : Fin 5) (v : M.V), ∃ μ : c.Kˣ, ∀ i,
      c.vdiag M (ggQ2s08r6S M (e k) v) i =
        μ * c.vdiag M v ((Equiv.swap (b k.castSucc) (b k.succ)).symm i) := by
  classical
  have hmem : ∀ k : Fin 5, M.simple (e k) ∈ ggAutomizer L Bs := fun k => by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨e k, rfl⟩
  choose τ hτ using fun k => c.exists_perm_of_mem_automizer M (hmem k)
  have hrel : ∀ (k : Fin 5) (v : M.V), ∃ μ : c.Kˣ, ∀ i,
      c.vdiag M (ggQ2s08r6S M (e k) v) i = μ * c.vdiag M v ((τ k).symm i) := hτ
  have hswap : ∀ k, (τ k).IsSwap := by
    intro k
    refine ggQ2s08r6_swap_of_refl_mod c.card_units (s := c.vdiag M (M.coroot (e k))) ?_ ?_
    · intro h1
      obtain ⟨v, hv⟩ := ggQ2s08r6_S_ne_one_mod M hShape (e k)
      obtain ⟨μ, hμ⟩ := hrel k v
      apply hv
      refine c.sub_mem_of_vdiag M (μ := μ) fun i => ?_
      rw [hμ i, h1]
      rfl
    · intro σ
      obtain ⟨v, μ₀, hσ⟩ := c.exists_smul_vdiag M σ
      obtain ⟨μ, hμ⟩ := hrel k v
      have hS : ggQ2s08r6S M (e k) v = v - M.root (e k) v • M.coroot (e k) :=
        M.simple_apply (e k) v
      refine ⟨2 * (M.root (e k) v).val, μ⁻¹, fun i => ?_⟩
      have h1 := hμ i
      rw [hS, vdiag_sub, vdiag_smul, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply] at h1
      have hinv : ∀ t : c.Kˣ, ∀ m : ℕ, (t ^ m)⁻¹ = t ^ (2 * m) := by
        intro t m
        rw [inv_eq_iff_mul_eq_one, ← pow_add, show m + 2 * m = 3 * m by ring, pow_mul, c.cube,
          one_pow]
      rw [hinv] at h1
      have h2 : c.vdiag M v ((τ k).symm i) = μ⁻¹ * (c.vdiag M v i *
          c.vdiag M (M.coroot (e k)) i ^ (2 * (M.root (e k) v).val)) := by
        rw [h1]
        group
      rw [hσ, hσ, h2, mul_assoc μ₀]
      exact mul_left_comm _ _ _
  have hrel2 : ∀ k l : Fin 5, ∀ v, ∃ μ : c.Kˣ, ∀ i,
      c.vdiag M (ggQ2s08r6S M (e k) (ggQ2s08r6S M (e l) v)) i =
        μ * c.vdiag M v ((τ k * τ l).symm i) :=
    fun k l => c.vdiag_rel_comp M (hrel k) (hrel l)
  have hadj : ∀ k l : Fin 5, (k : ℕ) + 1 = l → τ k * τ l ≠ τ l * τ k := by
    intro k l hkl hc
    obtain ⟨v, hv⟩ := ggQ2s08r6_S_noncomm_mod M hShape he hkl
    obtain ⟨μ, hμ⟩ := hrel2 k l v
    obtain ⟨μ', hμ'⟩ := hrel2 l k v
    apply hv
    refine c.sub_mem_of_vdiag M (μ := μ * μ'⁻¹) fun i => ?_
    rw [hμ i, hμ' i, hc]
    group
  have hfar : ∀ k l : Fin 5, k ≠ l → (k : ℕ) + 1 ≠ l → (l : ℕ) + 1 ≠ k →
      τ k * τ l = τ l * τ k ∧ τ k ≠ τ l := by
    intro k l hkl h1 h2
    refine ⟨?_, ?_⟩
    · refine ggQ2s08r6_perm_eq_of_forall c.card_units fun σ => ?_
      obtain ⟨v, μ₀, hσ⟩ := c.exists_smul_vdiag M σ
      obtain ⟨μ, hμ⟩ := hrel2 k l v
      obtain ⟨μ', hμ'⟩ := hrel2 l k v
      refine ⟨μ⁻¹ * μ', fun i => ?_⟩
      have hc := ggQ2s08r6_S_comm M he hkl h1 h2 v
      have e1 := hμ i
      have e2 := hμ' i
      rw [hc] at e1
      rw [hσ, hσ]
      have : c.vdiag M v ((τ k * τ l).symm i) = μ⁻¹ * μ' * c.vdiag M v ((τ l * τ k).symm i) := by
        rw [mul_assoc, ← e2, e1]
        group
      rw [this]
      exact mul_left_comm _ _ _
    · intro heq
      obtain ⟨v, hv⟩ := ggQ2s08r6_S_ne_mod M hShape he hkl
      obtain ⟨μ, hμ⟩ := hrel k v
      obtain ⟨μ', hμ'⟩ := hrel l v
      apply hv
      refine c.sub_mem_of_vdiag M (μ := μ * μ'⁻¹) fun i => ?_
      rw [hμ i, hμ' i, heq]
      group
  obtain ⟨b, hb⟩ := ggQ2s08r6_path hswap hadj hfar
  refine ⟨b, fun k v => ?_⟩
  rw [← hb k]
  exact hrel k v


theorem _root_.CFSG.StandardType.ggQ2s08r6_frame_not_mem {M : GGQ2LDatum 3 Bs L x}
    {f : Fin 6 → M.V} (hf : GGQ2S08ROFrame M f) (j : Fin 6) :
    f j ∉ Submodule.span (ZMod 3) {M.xV} := by
  classical
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  rw [hf.2.2.1] at ha
  have hlin := Fintype.linearIndependent_iff.mp hf.1
  have hsum : ∑ i, (a - if i = j then 1 else 0) • f i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.smul_sum, ha, sub_self]
  have h1 := hlin _ hsum j
  obtain ⟨i, hij⟩ : ∃ i : Fin 6, i ≠ j := ⟨j + 1, by
    intro h'
    have := congrArg (fun z : Fin 6 => (z : ℕ)) h'
    simp only [Fin.val_add] at this
    omega⟩
  have h2 := hlin _ hsum i
  rw [if_pos rfl, sub_eq_zero] at h1
  rw [if_neg hij, sub_zero] at h2
  rw [h2] at h1
  exact zero_ne_one h1

private theorem cmp_swap_conj (π : Equiv.Perm (Fin 6)) (u v m : Fin 6) :
    Equiv.swap (π u) (π v) (π m) = π (Equiv.swap u v m) := by
  rw [Equiv.swap_apply_apply]
  simp

theorem frame_cmp (c : GGQ2S08RoSix Bs L x) (M : GGQ2LDatum 3 Bs L x) (hShape : M.ShapeA)
    {e : Fin 5 ≃ M.Λ} (he : M.coxeter = (CoxeterMatrix.A 5).reindex e) (f : Fin 6 → M.V)
    (hf : GGQ2S08ROFrame M f) :
    ∃ w : Fin 6 ≃ Fin 6, ∀ j : Fin 6,
      (∀ i i', i ≠ w j → i' ≠ w j → c.vdiag M (f j) i = c.vdiag M (f j) i') ∧
      ∀ i, i ≠ w j → c.vdiag M (f j) i ≠ c.vdiag M (f j) (w j) := by
  classical
  obtain ⟨σ, hσf, hσswap, hσadj, hσfar⟩ := ggQ2s08r6_fswap M hShape he f hf
  obtain ⟨a, ha⟩ := ggQ2s08r6_path hσswap hσadj hσfar
  obtain ⟨b, hb⟩ := c.exists_tpath M hShape he
  set g : Fin 6 → Fin 6 → c.Kˣ := fun m p => c.vdiag M (f (a m)) (b p) with hg
  have hstep : ∀ (k : Fin 5) (m : Fin 6), ∃ μ : c.Kˣ, ∀ p,
      g (Equiv.swap k.castSucc k.succ m) p = μ * g m (Equiv.swap k.castSucc k.succ p) := by
    intro k m
    obtain ⟨μ, hμ⟩ := hb k (f (a m))
    refine ⟨μ, fun p => ?_⟩
    have hSf : ggQ2s08r6S M (e k) (f (a m)) = f (a (Equiv.swap k.castSucc k.succ m)) := by
      rw [hσf, ha k, cmp_swap_conj]
    have h1 := hμ (b p)
    rw [hSf, Equiv.symm_swap, cmp_swap_conj] at h1
    exact h1
  have hfix0 : ∀ k : Fin 5, k ≠ 0 → g 0 k.castSucc = g 0 k.succ := by
    intro k hk
    obtain ⟨μ, hμ⟩ := hstep k 0
    have h0 : Equiv.swap k.castSucc k.succ (0 : Fin 6) = 0 := by
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · intro h
        apply hk
        have h' := congrArg Fin.val h
        simp only [Fin.coe_castSucc, Fin.val_zero] at h'
        exact Fin.ext (by simp only [Fin.val_zero]; omega)
      · intro h
        have := congrArg (fun z : Fin 6 => (z : ℕ)) h
        simp at this
    refine ggQ2s08r6_eq_of_swap_fix c.card_units (Fin.castSucc_lt_succ : k.castSucc < k.succ).ne
      (σ := g 0) (μ := μ⁻¹) fun p => ?_
    have h1 := hμ p
    rw [h0] at h1
    rw [Equiv.symm_swap, h1, inv_mul_cancel_left]
  have e1 := hfix0 1 (by decide)
  have e2 := hfix0 2 (by decide)
  have e3 := hfix0 3 (by decide)
  have e4 := hfix0 4 (by decide)
  have hbase : ∀ p : Fin 6, p ≠ 0 → g 0 p = g 0 1 := by
    intro p hp
    fin_cases p
    · exact absurd rfl hp
    · rfl
    · exact e1.symm
    · exact (e1.trans e2).symm
    · exact (e1.trans (e2.trans e3)).symm
    · exact (e1.trans (e2.trans (e3.trans e4))).symm
  have hne : g 0 0 ≠ g 0 1 := by
    intro heq
    have hall : ∀ i, c.vdiag M (f (a 0)) i = 1 := by
      have hc : ∀ p, g 0 p = g 0 0 := fun p => by
        by_cases hp : p = 0
        · rw [hp]
        · rw [hbase p hp, heq]
      have h00 : g 0 (b.symm 0) = 1 := by
        simp only [hg, Equiv.apply_symm_apply]
        exact c.vdiag_zero_apply M _
      intro i
      have := hc (b.symm i)
      rw [← hc (b.symm 0), h00] at this
      simpa [hg] using this
    exact ggQ2s08r6_frame_not_mem hf (a 0) ((c.vdiag_eq_one_iff M _).mp (funext hall))
  have hind : ∀ (m : ℕ) (hm : m < 6), ∃ μ : c.Kˣ, ∀ p,
      g ⟨m, hm⟩ p = μ * (if p = ⟨m, hm⟩ then g 0 0 else g 0 1) := by
    intro m
    induction m with
    | zero =>
      intro hm
      refine ⟨1, fun p => ?_⟩
      rw [one_mul]
      by_cases hp : p = ⟨0, hm⟩
      · rw [if_pos hp, hp]
        rfl
      · rw [if_neg hp]
        exact hbase p (fun h => hp (h.trans (Fin.ext rfl)))
    | succ m ih =>
      intro hm
      obtain ⟨μ, hμ⟩ := ih (by omega)
      set k : Fin 5 := ⟨m, by omega⟩ with hk
      have hkc : k.castSucc = ⟨m, by omega⟩ := rfl
      have hks : k.succ = ⟨m + 1, hm⟩ := rfl
      obtain ⟨μ', hμ'⟩ := hstep k ⟨m, by omega⟩
      refine ⟨μ' * μ, fun p => ?_⟩
      have h1 := hμ' p
      rw [hkc, hks, Equiv.swap_apply_left] at h1
      rw [h1, hμ, mul_assoc]
      congr 2
      have hiff : Equiv.swap (⟨m, by omega⟩ : Fin 6) ⟨m + 1, hm⟩ p = ⟨m, by omega⟩ ↔
          p = ⟨m + 1, hm⟩ := Equiv.swap_apply_eq_iff.trans (by rw [Equiv.swap_apply_left])
      by_cases hp : p = ⟨m + 1, hm⟩
      · rw [if_pos (hiff.mpr hp), if_pos hp]
      · rw [if_neg (fun h => hp (hiff.mp h)), if_neg hp]
  refine ⟨a.symm.trans b, fun j => ?_⟩
  obtain ⟨μ, hμ⟩ := hind (a.symm j) (a.symm j).2
  have hval : ∀ p, c.vdiag M (f j) (b p) =
      μ * (if p = a.symm j then g 0 0 else g 0 1) := by
    intro p
    have h := hμ p
    simp only [hg, Fin.eta, Equiv.apply_symm_apply] at h
    exact h
  have hoff : ∀ i, i ≠ (a.symm.trans b) j → c.vdiag M (f j) i = μ * g 0 1 := by
    intro i hi
    have hp : b.symm i ≠ a.symm j := fun h => hi (by
      rw [Equiv.trans_apply, ← h, Equiv.apply_symm_apply])
    have := hval (b.symm i)
    rw [Equiv.apply_symm_apply, if_neg hp] at this
    exact this
  refine ⟨fun i i' hi hi' => by rw [hoff i hi, hoff i' hi'], fun i hi => ?_⟩
  rw [hoff i hi, Equiv.trans_apply, hval, if_pos rfl]
  exact fun h => hne (mul_left_cancel h).symm

end GGQ2S08RoSix

end CFSG.StandardType

end
