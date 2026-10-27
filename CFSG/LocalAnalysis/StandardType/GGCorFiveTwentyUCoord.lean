module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestPerm

public section

namespace CFSG.StandardType

namespace UCoord

open Multiplicative SpCoord

variable {d p : ℕ}

variable (d p) in
@[expose] def sumZero : Subgroup (Fin d → Multiplicative (ZMod p)) where
  carrier := {f | ∑ i, toAdd (f i) = 0}
  mul_mem' {f g} hf hg := by
    change ∑ i, toAdd (f i) = 0 at hf
    change ∑ i, toAdd (g i) = 0 at hg
    change ∑ i, toAdd ((f * g) i) = 0
    simp only [Pi.mul_apply, toAdd_mul, Finset.sum_add_distrib]
    rw [hf, hg, add_zero]
  one_mem' := by
    change ∑ i, toAdd ((1 : Fin d → Multiplicative (ZMod p)) i) = 0
    simp
  inv_mem' {f} hf := by
    change ∑ i, toAdd (f i) = 0 at hf
    change ∑ i, toAdd (f⁻¹ i) = 0
    simp only [Pi.inv_apply, toAdd_inv, Finset.sum_neg_distrib]
    rw [hf, neg_zero]

theorem mem_sumZero {f : Fin d → Multiplicative (ZMod p)} :
    f ∈ sumZero d p ↔ ∑ i, toAdd (f i) = 0 :=
  Iff.rfl

@[expose] def crd (f : ↥(sumZero d p)) (k : Fin d) : ZMod p :=
  toAdd ((f : Fin d → Multiplicative (ZMod p)) k)

theorem ext_crd {f g : ↥(sumZero d p)} (h : ∀ k, crd f k = crd g k) : f = g :=
  Subtype.ext (funext fun k => toAdd.injective (h k))

theorem crd_mul (f g : ↥(sumZero d p)) (k : Fin d) : crd (f * g) k = crd f k + crd g k :=
  rfl

theorem crd_inv (f : ↥(sumZero d p)) (k : Fin d) : crd f⁻¹ k = -crd f k :=
  rfl

theorem crd_one (k : Fin d) : crd (1 : ↥(sumZero d p)) k = 0 :=
  rfl

theorem crd_pow (f : ↥(sumZero d p)) (n : ℕ) (k : Fin d) :
    crd (f ^ n) k = (n : ZMod p) * crd f k := by
  rw [← nsmul_eq_mul]
  rfl

theorem sum_crd (f : ↥(sumZero d p)) : ∑ k, crd f k = 0 :=
  f.2

theorem pow_p_eq_one (f : ↥(sumZero d p)) : f ^ p = 1 :=
  ext_crd fun k => by rw [crd_pow, crd_one, ZMod.natCast_self, zero_mul]

theorem permAut_mem_sumZero (σ : Equiv.Perm (Fin d)) {f : Fin d → Multiplicative (ZMod p)}
    (hf : f ∈ sumZero d p) : permAut σ f ∈ sumZero d p := by
  show ∑ i, toAdd (f (σ⁻¹ i)) = 0
  exact (Equiv.sum_comp σ⁻¹ (fun i => toAdd (f i))).trans hf

@[expose] def permAutV (σ : Equiv.Perm (Fin d)) : MulAut ↥(sumZero d p) where
  toFun f := ⟨permAut σ f, permAut_mem_sumZero σ f.2⟩
  invFun f := ⟨permAut σ⁻¹ f, permAut_mem_sumZero σ⁻¹ f.2⟩
  left_inv f := ext_crd fun k => by
    show toAdd ((f : Fin d → Multiplicative (ZMod p)) (σ⁻¹ (σ⁻¹⁻¹ k))) = _
    rw [inv_inv, Equiv.Perm.inv_eq_iff_eq.mpr rfl]
    rfl
  right_inv f := ext_crd fun k => by
    show toAdd ((f : Fin d → Multiplicative (ZMod p)) (σ⁻¹⁻¹ (σ⁻¹ k))) = _
    rw [inv_inv, Equiv.Perm.eq_inv_iff_eq.mp rfl]
    rfl
  map_mul' f g := Subtype.ext (map_mul (permAut σ) (f : Fin d → Multiplicative (ZMod p))
    (g : Fin d → Multiplicative (ZMod p)))

theorem crd_permAutV (σ : Equiv.Perm (Fin d)) (f : ↥(sumZero d p)) (k : Fin d) :
    crd (permAutV σ f) k = crd f (σ⁻¹ k) :=
  rfl

theorem permAutV_mul (σ τ : Equiv.Perm (Fin d)) :
    (permAutV (σ * τ) : MulAut ↥(sumZero d p)) = permAutV σ * permAutV τ := by
  refine MulEquiv.ext fun f => ext_crd fun k => ?_
  rw [MulAut.mul_apply, crd_permAutV, crd_permAutV, crd_permAutV, mul_inv_rev,
    Equiv.Perm.mul_apply]

theorem permAutV_one : (permAutV 1 : MulAut ↥(sumZero d p)) = 1 :=
  MulEquiv.ext fun f => ext_crd fun k => by
    rw [crd_permAutV, inv_one, Equiv.Perm.one_apply]
    rfl

variable (d p) in
@[expose] def permAutVHom : Equiv.Perm (Fin d) →* MulAut ↥(sumZero d p) :=
  MonoidHom.mk' permAutV permAutV_mul

theorem permAutVHom_apply (σ : Equiv.Perm (Fin d)) :
    permAutVHom d p σ = permAutV σ :=
  rfl

@[expose] def rootV (i j : Fin d) : ↥(sumZero d p) :=
  ⟨fun k => ofAdd ((if k = i then 1 else 0) - (if k = j then 1 else 0)), by
    rw [mem_sumZero]
    simp [Finset.sum_sub_distrib]⟩

theorem crd_rootV (i j k : Fin d) :
    crd (rootV i j : ↥(sumZero d p)) k = (if k = i then 1 else 0) - (if k = j then 1 else 0) :=
  rfl

theorem permAutV_rootV (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    (permAutV σ (rootV i j) : ↥(sumZero d p)) = rootV (σ i) (σ j) :=
  ext_crd fun k => by
    simp only [crd_permAutV, crd_rootV, Equiv.Perm.inv_eq_iff_eq]

theorem crd_rootV_left {i j : Fin d} (hij : i ≠ j) : crd (rootV i j : ↥(sumZero d p)) i = 1 := by
  rw [crd_rootV, ite_eq_left rfl, ite_eq_right hij, sub_zero]

theorem crd_rootV_right {i j : Fin d} (hij : i ≠ j) :
    crd (rootV i j : ↥(sumZero d p)) j = -1 := by
  rw [crd_rootV, ite_eq_right (Ne.symm hij), ite_eq_left rfl, zero_sub]

theorem crd_rootV_other {i j k : Fin d} (hki : k ≠ i) (hkj : k ≠ j) :
    crd (rootV i j : ↥(sumZero d p)) k = 0 := by
  rw [crd_rootV, ite_eq_right hki, ite_eq_right hkj, sub_zero]

theorem mul_inv_permAutV_swap [NeZero p] {i j : Fin d} (hij : i ≠ j) (f : ↥(sumZero d p)) :
    f * (permAutV (Equiv.swap i j) f)⁻¹ = rootV i j ^ (crd f i - crd f j).val := by
  refine ext_crd fun k => ?_
  rw [crd_mul, crd_inv, crd_permAutV, crd_pow, ZMod.natCast_zmod_val, Equiv.swap_inv]
  by_cases hki : k = i
  · rw [hki, Equiv.swap_apply_left, crd_rootV_left hij, mul_one, ← sub_eq_add_neg]
  · by_cases hkj : k = j
    · rw [hkj, Equiv.swap_apply_right, crd_rootV_right hij, mul_neg_one, neg_sub,
        ← sub_eq_add_neg]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, crd_rootV_other hki hkj, mul_zero, add_neg_cancel]

theorem permAutV_swap_pow (hp : p.Prime) (hp2 : p ≠ 2) (i j : Fin d) :
    (permAutV (Equiv.swap i j) : MulAut ↥(sumZero d p)) ^ (p - 1) = 1 :=
  pow_sub_one_eq_one_of_sq hp hp2 (by rw [sq, ← permAutV_mul, Equiv.swap_mul_self, permAutV_one])

theorem isPseudoReflection_permAutV_swap (hp : p.Prime) (hp2 : p ≠ 2) {i j : Fin d}
    (hij : i ≠ j) :
    GGIsPseudoReflection p (permAutV (Equiv.swap i j) : MulAut ↥(sumZero d p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨permAutV_swap_pow hp hp2 i j, ?_⟩
  refine card_fix_mul_of_le_zpowers hp (fun a b => mul_comm a b) _ (a₁ := rootV i j)
    (pow_p_eq_one _) (fun a => ⟨_, mul_inv_permAutV_swap hij a⟩) ?_
  intro h
  have h1 := congrArg (fun f => crd f i) h
  simp only [crd_mul, crd_inv, crd_permAutV, crd_one, Equiv.swap_inv, Equiv.swap_apply_left,
    crd_rootV_left hij, crd_rootV_right hij, neg_neg] at h1
  exact coord_two_ne_zero hp hp2 (by rw [← h1, one_add_one_eq_two])

theorem mem_closure_permAutV {H : Subgroup (MulAut ↥(sumZero d p))}
    (hH : ∀ i j : Fin d, i ≠ j → permAutV (Equiv.swap i j) ∈ H) (σ : Equiv.Perm (Fin d)) :
    permAutV σ ∈ H := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    rw [permAutV_one]
    exact one_mem _
  | swap_mul π x y hxy ih =>
    rw [permAutV_mul]
    exact mul_mem (hH x y hxy) ih

theorem permAutV_injective (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (permAutV : Equiv.Perm (Fin d) → MulAut ↥(sumZero d p)) := by
  have hker : ∀ σ : Equiv.Perm (Fin d), (permAutV σ : MulAut ↥(sumZero d p)) = 1 → σ = 1 := by
    intro σ h1
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
      by_contra h
      push Not at h
      exact hne (Equiv.ext h)
    have h2 := congrArg (fun φ : MulAut ↥(sumZero d p) => crd (φ (rootV i (σ i))) (σ i)) h1
    simp only [MulAut.one_apply, crd_permAutV] at h2
    rw [Equiv.Perm.inv_eq_iff_eq.mpr rfl, crd_rootV_left (Ne.symm hi),
      crd_rootV_right (Ne.symm hi)] at h2
    exact coord_two_ne_zero hp hp2 (by
      rw [← one_add_one_eq_two]
      calc (1 : ZMod p) + 1 = 1 - -1 := by rw [sub_neg_eq_add]
        _ = 0 := by rw [← h2, sub_self])
  intro σ τ h
  have h1 : (permAutV (σ * τ⁻¹) : MulAut ↥(sumZero d p)) = 1 := by
    rw [permAutV_mul, h, ← permAutV_mul, mul_inv_cancel, permAutV_one]
  exact mul_inv_eq_one.mp (hker _ h1)

theorem fix_or_fix_pow_mul_inv {H : Type*} [Group H] [Finite H] (hp : p.Prime)
    (hc : ∀ a b : H, a * b = b * a) (u : MulAut H)
    (hfix : Nat.card {a : H // u a = a} * p = Nat.card H) (a₁ a₂ : H) :
    u a₁ = a₁ ∨ ∃ e : ℕ, u (a₁ ^ e * a₂⁻¹) = a₁ ^ e * a₂⁻¹ := by
  have := Fact.mk hp
  let δ : H →* H :=
    { toFun := fun a => a * (u a)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv_rev]
        calc a * b * ((u b)⁻¹ * (u a)⁻¹) = a * (b * (u b)⁻¹ * (u a)⁻¹) := by group
          _ = a * ((u a)⁻¹ * (b * (u b)⁻¹)) := by rw [hc _ (u a)⁻¹]
          _ = a * (u a)⁻¹ * (b * (u b)⁻¹) := by group }
  have hδ1 : ∀ a, δ a = 1 ↔ u a = a := fun a => by
    show a * (u a)⁻¹ = 1 ↔ u a = a
    rw [mul_inv_eq_one, eq_comm]
  have hker : Nat.card δ.ker = Nat.card {a : H // u a = a} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun a => by rw [MonoidHom.mem_ker, hδ1])
  have hrange : Nat.card δ.range = p := by
    have h1 := δ.ker.card_mul_index
    rw [Subgroup.index_ker, hker, ← hfix] at h1
    have hpos : 0 < Nat.card {a : H // u a = a} := by
      rw [← hker]
      exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  by_cases ha₁ : δ a₁ = 1
  · exact Or.inl ((hδ1 _).mp ha₁)
  right
  have hpow : δ a₁ ^ p = 1 := by
    have h1 := pow_card_eq_one' (G := δ.range) (x := ⟨δ a₁, ⟨_, rfl⟩⟩)
    rw [hrange] at h1
    simpa using congrArg Subtype.val h1
  have hz : Subgroup.zpowers (δ a₁) = δ.range := by
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le (H := δ.range)).mpr ⟨_, rfl⟩)
    rw [Nat.card_zpowers, orderOf_eq_prime hpow ha₁, hrange]
  have h2 : δ a₂ ∈ Submonoid.powers (δ a₁) :=
    mem_powers_iff_mem_zpowers.mpr (by rw [hz]; exact ⟨_, rfl⟩)
  obtain ⟨e, he⟩ := h2
  have he' : δ a₁ ^ e = δ a₂ := he
  refine ⟨e, ?_⟩
  have h3 : δ (a₁ ^ e * a₂⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, he', mul_inv_cancel]
  exact (hδ1 _).mp h3

theorem crd_apply_eq_of_fix {σ : Equiv.Perm (Fin d)} {f : ↥(sumZero d p)}
    (h : permAutV σ f = f) (k : Fin d) : crd f (σ k) = crd f k := by
  have h1 := congrArg (fun g => crd g (σ k)) h
  simp only [crd_permAutV] at h1
  rw [Equiv.Perm.inv_eq_iff_eq.mpr rfl] at h1
  exact h1.symm

theorem isSwap_of_isPseudoReflection (hp : p.Prime) (hp2 : p ≠ 2) (hd : 4 ≤ d)
    {σ : Equiv.Perm (Fin d)} (h : GGIsPseudoReflection p (permAutV σ : MulAut ↥(sumZero d p))) :
    σ.IsSwap := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hrank := fix_or_fix_pow_mul_inv hp (fun a b => mul_comm a b) (permAutV σ) h.2
  have h1ne : (1 : ZMod p) ≠ -1 := fun h1 => coord_two_ne_zero hp hp2 (by
    rw [← one_add_one_eq_two]
    nth_rewrite 2 [h1]
    exact add_neg_cancel 1)
  by_contra hns
  have hne1 : σ ≠ 1 := by
    rintro rfl
    have h1 := h.2
    rw [permAutV_one] at h1
    have h2 : Nat.card {f : ↥(sumZero d p) // (1 : MulAut ↥(sumZero d p)) f = f} =
        Nat.card ↥(sumZero d p) := Nat.card_congr (Equiv.subtypeUnivEquiv fun f => rfl)
    rw [h2] at h1
    have hpos : 0 < Nat.card ↥(sumZero d p) := Nat.card_pos
    have := hp.two_le
    nlinarith
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra h'
    push Not at h'
    exact hne1 (Equiv.ext h')
  have hg₁ : permAutV σ (rootV i (σ i) : ↥(sumZero d p)) ≠ rootV i (σ i) := by
    intro hf
    have h2 := crd_apply_eq_of_fix hf i
    rw [crd_rootV_left (Ne.symm hi), crd_rootV_right (Ne.symm hi)] at h2
    exact h1ne h2.symm
  by_cases hj : σ (σ i) = i
  ·
    obtain ⟨m, hmi, hmj, hm⟩ : ∃ m, m ≠ i ∧ m ≠ σ i ∧ σ m ≠ m := by
      by_contra h'
      push Not at h'
      apply hns
      refine ⟨i, σ i, Ne.symm hi, Equiv.ext fun x => ?_⟩
      by_cases hxi : x = i
      · rw [hxi, Equiv.swap_apply_left]
      by_cases hxj : x = σ i
      · rw [hxj, hj, Equiv.swap_apply_right]
      · rw [h' x hxi hxj, Equiv.swap_apply_of_ne_of_ne hxi hxj]
    have hn_i : σ m ≠ i := fun h => hmj (σ.injective (h.trans hj.symm))
    have hn_j : σ m ≠ σ i := fun h => hmi (σ.injective h)
    rcases hrank (rootV i (σ i)) (rootV m (σ m)) with hf | ⟨e, he⟩
    · exact hg₁ hf
    · have h2 := crd_apply_eq_of_fix he m
      simp only [crd_mul, crd_pow, crd_inv, crd_rootV_other hn_i hn_j, crd_rootV_other hmi hmj,
        crd_rootV_right (Ne.symm hm), crd_rootV_left (Ne.symm hm), mul_zero, zero_add,
        neg_neg] at h2
      exact h1ne h2
  ·
    have hk_j : σ (σ i) ≠ σ i := fun h => hi (σ.injective h)
    obtain ⟨l, hli, hlj, hlk⟩ := TypeA.exists_fin_avoid_three hd i (σ i) (σ (σ i))
    rcases hrank (rootV i (σ i)) (rootV (σ i) l) with hf | ⟨e, he⟩
    · exact hg₁ hf
    · have h_i := crd_apply_eq_of_fix he i
      have h_j := crd_apply_eq_of_fix he (σ i)
      simp only [crd_mul, crd_pow, crd_inv, crd_rootV_left (Ne.symm hi),
        crd_rootV_right (Ne.symm hi), crd_rootV_left (Ne.symm hlj),
        crd_rootV_other (Ne.symm hi) (Ne.symm hli), crd_rootV_other hj hk_j,
        crd_rootV_other hk_j (Ne.symm hlk), mul_one, mul_neg_one, mul_zero, neg_zero,
        add_zero] at h_i h_j
      have he0 : (e : ZMod p) = 0 := (h_j.trans h_i).symm
      rw [he0, neg_zero, zero_add] at h_j
      exact coord_zero_ne_one hp (neg_eq_zero.mp h_j.symm).symm

theorem exists_eq_conj_of_normalizes (hp : p.Prime) (hp2 : p ≠ 2) (hd : 4 ≤ d)
    {φ : MulAut ↥(sumZero d p)}
    (hφ : ∀ σ : Equiv.Perm (Fin d), ∃ τ, φ * permAutV σ * φ⁻¹ = permAutV τ) :
    ∃ π : Equiv.Perm (Fin d), ∀ σ, φ * permAutV σ * φ⁻¹ = permAutV (π * σ * π⁻¹) := by
  choose α hα using hφ
  have hinj := permAutV_injective (d := d) hp hp2
  have hαmul : ∀ σ τ, α (σ * τ) = α σ * α τ := by
    intro σ τ
    apply hinj
    rw [← hα (σ * τ), permAutV_mul, permAutV_mul, ← hα σ, ← hα τ]
    group
  let αh : Equiv.Perm (Fin d) →* Equiv.Perm (Fin d) := MonoidHom.mk' α hαmul
  have hαinj : Function.Injective αh := by
    intro σ τ h
    apply hinj
    have h1 : φ * permAutV σ * φ⁻¹ = φ * permAutV τ * φ⁻¹ := by
      rw [hα, hα]
      exact congrArg permAutV h
    exact mul_left_cancel (mul_right_cancel h1)
  have hαswap : ∀ σ : Equiv.Perm (Fin d), σ.IsSwap → (αh σ).IsSwap := by
    rintro σ ⟨i, j, hij, rfl⟩
    have h1 := (isPseudoReflection_permAutV_swap hp hp2 hij).conj φ
    rw [hα] at h1
    exact isSwap_of_isPseudoReflection hp hp2 hd h1
  obtain ⟨π₀, hπ₀⟩ := exists_eq_conj_of_isSwap (by omega) αh hαinj hαswap
  exact ⟨π₀, fun σ => by rw [hα, ← hπ₀ σ]; rfl⟩

theorem exists_perm_apply_apply {a b i j : Fin d} (hab : a ≠ b) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin d), σ a = i ∧ σ b = j := by
  refine ⟨Equiv.swap (Equiv.swap a i b) j * Equiv.swap a i, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => hab ?_) hij
    have h2 : Equiv.swap a i b = Equiv.swap a i a := by rw [Equiv.swap_apply_left]; exact h.symm
    exact ((Equiv.swap a i).injective h2).symm
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem exists_pow_of_commute_permAutV (hp : p.Prime) (hp2 : p ≠ 2) (hd : 2 ≤ d)
    (hpd : ¬ p ∣ d) (F : ↥(sumZero d p) →* ↥(sumZero d p))
    (hF : ∀ (σ : Equiv.Perm (Fin d)) (f : ↥(sumZero d p)), F (permAutV σ f) = permAutV σ (F f)) :
    ∃ c : ℕ, ∀ f, F f = f ^ c := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i₀, i₁, h01⟩ : ∃ i₀ i₁ : Fin d, i₀ ≠ i₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  set v := F (rootV i₀ i₁) with hv
  have hsw : permAutV (Equiv.swap i₀ i₁) v = v⁻¹ := by
    rw [hv, ← hF, permAutV_rootV, Equiv.swap_apply_left, Equiv.swap_apply_right, ← map_inv]
    congr 1
    exact ext_crd fun k => by rw [crd_inv, crd_rootV, crd_rootV, neg_sub]
  have hv0 : ∀ k, k ≠ i₀ → k ≠ i₁ → crd v k = 0 := by
    intro k hk0 hk1
    have h1 := congrArg (fun g => crd g k) hsw
    simp only [crd_permAutV, crd_inv, Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne hk0 hk1] at h1
    exact coord_eq_zero_of_eq_neg hp hp2 h1
  have hv1 : crd v i₁ = -crd v i₀ := by
    have h1 := congrArg (fun g => crd g i₀) hsw
    simp only [crd_permAutV, crd_inv, Equiv.swap_inv, Equiv.swap_apply_left] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (c : ZMod p) = crd v i₀ := ⟨(crd v i₀).val, ZMod.natCast_zmod_val _⟩
  have hvc : v = rootV i₀ i₁ ^ c := by
    refine ext_crd fun k => ?_
    rw [crd_pow, hc]
    by_cases hk0 : k = i₀
    · rw [hk0, crd_rootV_left h01, mul_one]
    · by_cases hk1 : k = i₁
      · rw [hk1, crd_rootV_right h01, hv1, mul_neg_one]
      · rw [hv0 k hk0 hk1, crd_rootV_other hk0 hk1, mul_zero]
  have hroot : ∀ i j : Fin d, i ≠ j → F (rootV i j) = rootV i j ^ c := by
    intro i j hij
    obtain ⟨σ, hσi, hσj⟩ := exists_perm_apply_apply h01 hij
    rw [← hσi, ← hσj, ← permAutV_rootV, hF, ← hv, hvc, map_pow]
  refine ⟨c, fun f => ?_⟩
  have hconst : ∀ i j : Fin d, crd (F f) i - (c : ZMod p) * crd f i =
      crd (F f) j - (c : ZMod p) * crd f j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have h1 := congrArg F (mul_inv_permAutV_swap hij f)
    rw [map_mul, map_inv, hF, map_pow, hroot i j hij, ← pow_mul] at h1
    have h2 := congrArg (fun g => crd g i) h1
    simp only [crd_mul, crd_inv, crd_permAutV, crd_pow, Equiv.swap_inv, Equiv.swap_apply_left,
      crd_rootV_left hij, mul_one] at h2
    rw [Nat.cast_mul, ZMod.natCast_zmod_val (crd f i - crd f j), ← sub_eq_add_neg, mul_sub] at h2
    exact sub_eq_sub_iff_sub_eq_sub.mp h2
  have hsum : ∑ k, (crd (F f) k - (c : ZMod p) * crd f k) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_crd, sum_crd, mul_zero, sub_zero]
  have hzero : crd (F f) i₀ - (c : ZMod p) * crd f i₀ = 0 := by
    rw [Finset.sum_eq_card_nsmul (fun k _ => hconst k i₀), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    have hd0 : (d : ZMod p) ≠ 0 := by
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      exact hpd h0
    exact (coord_mul_eq_zero hp hsum).resolve_left hd0
  refine ext_crd fun k => ?_
  rw [crd_pow]
  exact sub_eq_zero.mp ((hconst k i₀).trans hzero)

end UCoord

end CFSG.StandardType

end
