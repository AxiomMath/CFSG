module

public import CFSG.Quasithin.Background.G64PermAut
public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin Equiv Equiv.Perm

variable {V : Type*} [CommGroup V]

omit [CommGroup V] in
theorem exists_ne_one_of_card_two {M : Type*} [Group M] {A : Subgroup M}
    (h : Nat.card A = 2) : ∃ w ∈ A, w ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : A = ⊥ := eq_bot_iff.2 fun y hy => hcon y hy
  rw [this, Subgroup.card_bot] at h
  omega

@[expose] noncomputable def swapAut {H : Subgroup (MulAut V)} {n : ℕ} (θ : ↥H ≃* Perm (Fin n))
    (i j : Fin n) : MulAut V :=
  ((θ.symm (swap i j) : ↥H) : MulAut V)

theorem swapAut_comm {H : Subgroup (MulAut V)} {n : ℕ} (θ : ↥H ≃* Perm (Fin n)) (i j : Fin n) :
    swapAut θ i j = swapAut θ j i := by
  rw [swapAut, swapAut, swap_comm]

theorem conj_swapAut {H : Subgroup (MulAut V)} {n : ℕ} (θ : ↥H ≃* Perm (Fin n))
    (σ : Perm (Fin n)) (i j : Fin n) :
    ((θ.symm σ : ↥H) : MulAut V) * swapAut θ i j * ((θ.symm σ : ↥H) : MulAut V)⁻¹ =
      swapAut θ (σ i) (σ j) := by
  rw [swapAut, swapAut, swap_apply_apply, map_mul, map_mul, map_inv]
  rfl

section Centres

variable (hV2 : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)} {n : ℕ} (θ : ↥H ≃* Perm (Fin n))
  (htr : ∀ i j : Fin n, i ≠ j → Nat.card (commV (Subgroup.zpowers (swapAut θ i j))) = 2)

include hV2 htr in
theorem center_relation {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) {uij ujk uik : V}
    (hu₁ : uij ∈ commV (Subgroup.zpowers (swapAut θ i j))) (hu₁' : uij ≠ 1)
    (hu₂ : ujk ∈ commV (Subgroup.zpowers (swapAut θ j k))) (hu₂' : ujk ≠ 1)
    (hu₃ : uik ∈ commV (Subgroup.zpowers (swapAut θ i k))) (hu₃' : uik ≠ 1) :
    uik = uij * ujk := by
  set x := swapAut θ i j with hx
  set y := swapAut θ j k with hy
  set z := swapAut θ i k with hz
  have hzxy : z = x * y * x⁻¹ := by
    have := conj_swapAut θ (swap i j) j k
    rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hik) (Ne.symm hjk)] at this
    rw [hz, ← this]
    rfl
  have hxu : x ujk = uik := by
    have hmem : x ujk ∈ commV (Subgroup.zpowers z) := by
      rw [hzxy, G6.commV_zpowers_conj]
      exact ⟨ujk, hu₂, rfl⟩
    have hne : x ujk ≠ 1 := fun e => hu₂' (x.injective (e.trans (map_one x).symm))
    rcases eq_one_or_eq_of_card_two (htr i k hik) hu₃ hu₃' hmem with h1 | h1
    · exact absurd h1 hne
    · exact h1
  rcases eq_one_or_eq_of_card_two (htr i j hij) hu₁ hu₁'
      (G6.mem_commV_of_mem (Subgroup.mem_zpowers x) ujk) with h1 | h1
  ·
    exfalso
    have hxu' : x ujk = ujk := mul_inv_eq_one.1 h1
    have hcz : commV (Subgroup.zpowers z) = commV (Subgroup.zpowers y) := by
      rw [hzxy, G6.commV_zpowers_conj]
      apply le_antisymm
      · rintro _ ⟨w, hw, rfl⟩
        rcases eq_one_or_eq_of_card_two (htr j k hjk) hu₂ hu₂' hw with h2 | h2
        · rw [h2, map_one]
          exact Subgroup.one_mem _
        · rw [h2]
          exact (show x ujk ∈ commV (Subgroup.zpowers y) by rw [hxu']; exact hu₂)
      · intro w hw
        refine ⟨w, hw, ?_⟩
        rcases eq_one_or_eq_of_card_two (htr j k hjk) hu₂ hu₂' hw with h2 | h2
        · rw [h2, map_one]
        · rw [h2]
          exact hxu'
    have hrank : ∀ v, (y * z) v * v⁻¹ = 1 ∨ (y * z) v * v⁻¹ = ujk := by
      intro v
      have h3 : (y * z) v * v⁻¹ = (y (z v) * (z v)⁻¹) * (z v * v⁻¹) := by
        rw [MulAut.mul_apply]
        group
      have h4 := eq_one_or_eq_of_card_two (htr j k hjk) hu₂ hu₂'
        (G6.mem_commV_of_mem (Subgroup.mem_zpowers y) (z v))
      have h5 : z v * v⁻¹ ∈ commV (Subgroup.zpowers y) := by
        rw [← hcz]
        exact G6.mem_commV_of_mem (Subgroup.mem_zpowers z) v
      have h6 := eq_one_or_eq_of_card_two (htr j k hjk) hu₂ hu₂' h5
      rw [h3]
      rcases h4 with h4 | h4 <;> rcases h6 with h6 | h6 <;> rw [h4, h6]
      · left; rw [one_mul]
      · right; rw [one_mul]
      · right; rw [mul_one]
      · left; rw [← sq, hV2]
    have hsq := sq_eq_one_of_rankOne hV2 hrank
    have hsq' : (swap j k * swap i k) ^ 2 = 1 := by
      have : (θ.symm (swap j k * swap i k)) ^ 2 = 1 := by
        apply Subtype.ext
        rw [map_mul, SubgroupClass.coe_pow, Subgroup.coe_mul]
        exact hsq
      have := congrArg θ this
      rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
    have := congrArg (fun σ : Perm (Fin n) => σ i) hsq'
    simp only [sq, Perm.mul_apply, Perm.one_apply, swap_apply_left, swap_apply_right] at this
    rw [swap_apply_of_ne_of_ne (Ne.symm hij) hjk, swap_apply_left] at this
    exact hik this.symm
  · rw [← hxu]
    have : x ujk = uij * ujk := by
      rw [← h1]
      group
    rw [this]

include hV2 htr in
theorem exists_center (hn : 1 ≤ n) :
    ∃ c : Fin n → V, ∀ i j : Fin n, i ≠ j →
      c i * c j ∈ commV (Subgroup.zpowers (swapAut θ i j)) ∧ c i * c j ≠ 1 := by
  classical
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  choose u hu hu1 using fun (p : Fin n × Fin n) (hp : p.1 ≠ p.2) =>
    exists_ne_one_of_card_two (htr p.1 p.2 hp)
  set c : Fin n → V := fun l => if hl : i₀ = l then 1 else u (i₀, l) hl with hc
  refine ⟨c, fun i j hij => ?_⟩
  by_cases hi : i₀ = i
  · subst hi
    have hcj : c j = u (i₀, j) hij := by simp [hc, hij]
    have hci : c i₀ = 1 := by simp [hc]
    rw [hci, hcj, one_mul]
    exact ⟨hu (i₀, j) hij, hu1 (i₀, j) hij⟩
  by_cases hj : i₀ = j
  · subst hj
    have hci : c i = u (i₀, i) hi := by simp [hc, hi]
    have hcj : c i₀ = 1 := by simp [hc]
    rw [hci, hcj, mul_one, swapAut_comm]
    exact ⟨hu (i₀, i) hi, hu1 (i₀, i) hi⟩
  have hci : c i = u (i₀, i) hi := by simp [hc, hi]
  have hcj : c j = u (i₀, j) hj := by simp [hc, hj]
  rw [hci, hcj]
  have hu' : u (i₀, i) hi ∈ commV (Subgroup.zpowers (swapAut θ i i₀)) := by
    rw [swapAut_comm]
    exact hu (i₀, i) hi
  have := center_relation hV2 θ htr (Ne.symm hi) hj hij hu' (hu1 (i₀, i) hi) (hu (i₀, j) hj)
    (hu1 (i₀, j) hj) (hu (i, j) hij) (hu1 (i, j) hij)
  rw [← this]
  exact ⟨hu (i, j) hij, hu1 (i, j) hij⟩

end Centres

theorem pow_mod_two (hV2 : ∀ v : V, v ^ 2 = 1) (g : V) (m : ℕ) : g ^ (m % 2) = g ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 2, pow_add, pow_mul, hV2, one_pow, one_mul]

@[expose] noncomputable def prodHom (hV2 : ∀ v : V, v ^ 2 = 1) {n : ℕ} (c : Fin n → V) :
    G6.PermMod n →* V where
  toFun x := ∏ l, c l ^ (Multiplicative.toAdd x l).val
  map_one' := by simp
  map_mul' x y := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, pow_mod_two hV2, pow_add]

theorem prodHom_apply (hV2 : ∀ v : V, v ^ 2 = 1) {n : ℕ} (c : Fin n → V) (x : G6.PermMod n) :
    prodHom hV2 c x = ∏ l, c l ^ (Multiplicative.toAdd x l).val :=
  rfl

theorem prodHom_pairVec (hV2 : ∀ v : V, v ^ 2 = 1) {n : ℕ} (c : Fin n → V) {i j : Fin n}
    (hij : i ≠ j) : prodHom hV2 c (pairVec i j) = c i * c j := by
  classical
  rw [prodHom_apply]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  rw [Finset.prod_eq_mul i j hij]
  · simp [pairVec, hij, Ne.symm hij, h1]
  · intro l _ hl
    simp [pairVec, hl.1, hl.2]
  · simp
  · simp

theorem even_sum_val_of_mem_coreMod {n : ℕ} {x : G6.PermMod n} (hx : x ∈ G6.coreMod n) :
    2 ∣ ∑ l, (Multiplicative.toAdd x l).val := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  simp only [ZMod.natCast_val, ZMod.cast_id', id]
  exact G6.mem_coreMod.1 hx

theorem prodHom_permAct (hV2 : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)} {n : ℕ}
    (θ : ↥H ≃* Perm (Fin n)) {c : Fin n → V}
    (hc : ∀ i j : Fin n, i ≠ j →
      c i * c j ∈ commV (Subgroup.zpowers (swapAut θ i j)) ∧ c i * c j ≠ 1)
    (htr : ∀ i j : Fin n, i ≠ j → Nat.card (commV (Subgroup.zpowers (swapAut θ i j))) = 2)
    (σ : Perm (Fin n)) {x : G6.PermMod n} (hx : x ∈ G6.coreMod n) :
    prodHom hV2 c (G6.permAct n σ x) = ((θ.symm σ : ↥H) : MulAut V) (prodHom hV2 c x) := by
  classical
  set h : MulAut V := ((θ.symm σ : ↥H) : MulAut V) with hh
  have hpair : ∀ a b : Fin n, h (c a * c b) = c (σ a) * c (σ b) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [← sq, hV2, map_one, ← sq, hV2]
    · have hσ : σ a ≠ σ b := fun e => hab (σ.injective e)
      have hmem : h (c a * c b) ∈ commV (Subgroup.zpowers (swapAut θ (σ a) (σ b))) := by
        rw [← conj_swapAut θ σ a b, G6.commV_zpowers_conj]
        exact ⟨_, (hc a b hab).1, rfl⟩
      have hne : h (c a * c b) ≠ 1 := fun e => (hc a b hab).2 (h.injective (e.trans
        (map_one h).symm))
      rcases eq_one_or_eq_of_card_two (htr _ _ hσ) (hc _ _ hσ).1 (hc _ _ hσ).2 hmem with h1 | h1
      · exact absurd h1 hne
      · exact h1
  set d : Fin n → V := fun a => h (c a) * c (σ a) with hd
  have hdconst : ∀ a b, d a = d b := by
    intro a b
    have h1 := hpair a b
    rw [map_mul] at h1
    have : d a * d b = 1 := by
      rw [hd]
      calc h (c a) * c (σ a) * (h (c b) * c (σ b)) = (h (c a) * h (c b)) * (c (σ a) * c (σ b)) :=
            mul_mul_mul_comm _ _ _ _
        _ = 1 := by rw [h1, ← sq, hV2]
    calc d a = d a * (d b * d b) := by rw [← sq, hV2, mul_one]
      _ = (d a * d b) * d b := (mul_assoc _ _ _).symm
      _ = d b := by rw [this, one_mul]
  have hhc : ∀ a, h (c a) = d a * c (σ a) := by
    intro a
    rw [hd]
    calc h (c a) = h (c a) * (c (σ a) * c (σ a)) := by rw [← sq, hV2, mul_one]
      _ = h (c a) * c (σ a) * c (σ a) := (mul_assoc _ _ _).symm
  rw [prodHom_apply, prodHom_apply, map_prod]
  simp only [map_pow, hhc, mul_pow, Finset.prod_mul_distrib]
  have hdx : ∏ l, d l ^ (Multiplicative.toAdd x l).val = 1 := by
    rcases isEmpty_or_nonempty (Fin n) with hne | ⟨⟨i₀⟩⟩
    · simp
    · simp only [hdconst _ i₀, Finset.prod_pow_eq_pow_sum]
      obtain ⟨m, hm⟩ := even_sum_val_of_mem_coreMod hx
      rw [hm, pow_mul, hV2, one_pow]
  rw [hdx, one_mul]
  rw [← Equiv.prod_comp σ (fun l => c l ^ (Multiplicative.toAdd (G6.permAct n σ x) l).val)]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [G6.permAct_apply]
  simp

theorem card_swapAut_of_isSwap {H : Subgroup (MulAut V)} {n : ℕ} (θ : ↥H ≃* Perm (Fin n))
    {a : MulAut V} (ha : a ∈ H) (hsw : (θ ⟨a, ha⟩).IsSwap)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    ∀ i j : Fin n, i ≠ j → Nat.card (commV (Subgroup.zpowers (swapAut θ i j))) = 2 := by
  intro i j hij
  obtain ⟨x, y, hxy, hxy'⟩ := hsw
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_swap hxy hij)
  have : swapAut θ i j = ((θ.symm g : ↥H) : MulAut V) * a * ((θ.symm g : ↥H) : MulAut V)⁻¹ := by
    rw [swapAut, ← hg, ← hxy', map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rfl
  rw [this, G6.card_commV_zpowers_conj, htr]

theorem le_closure_swapAut {H : Subgroup (MulAut V)} {n : ℕ} (θ : ↥H ≃* Perm (Fin n)) :
    H ≤ Subgroup.closure {x : MulAut V | ∃ i j : Fin n, i ≠ j ∧ x = swapAut θ i j} := by
  intro x hx
  have h1 : θ ⟨x, hx⟩ ∈ Subgroup.closure {σ : Perm (Fin n) | σ.IsSwap} := by
    rw [closure_isSwap]
    trivial
  have h2 := Subgroup.mem_map_of_mem (H.subtype.comp θ.symm.toMonoidHom) h1
  rw [MonoidHom.map_closure] at h2
  have h3 : (H.subtype.comp θ.symm.toMonoidHom) (θ ⟨x, hx⟩) = x := by simp
  rw [h3] at h2
  refine (Subgroup.closure_mono ?_) h2
  rintro _ ⟨σ, ⟨i, j, hij, rfl⟩, rfl⟩
  exact ⟨i, j, hij, rfl⟩

theorem realizesVia_permModel_bot {H : Subgroup (MulAut V)} {n : ℕ} {π : Perm (Fin n) →* ↥H}
    (hπ : Function.Surjective π) (E : ↥(G6.coreMod n) ≃* V)
    (hE : ∀ (σ : Perm (Fin n)) (x : ↥(G6.coreMod n)),
      E ⟨G6.permAct n σ x, G6.permAct_mem_coreMod σ x.2⟩ = ((π σ : ↥H) : MulAut V) (E x)) :
    (permModel n ⊥).RealizesVia H ⊤ ⊥ π := by
  have hq : Function.Injective (QuotientGroup.mk' ((⊥ : Subgroup (G6.PermMod n)).subgroupOf
      (G6.coreMod n))) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_bot] at hx
    exact Subtype.ext hx
  refine ⟨hπ, bot_le, bot_le, fun _ _ _ => trivial, fun h z hz => ?_,
    fun σ m hm => G6.permAct_mem_coreMod σ hm, ?_, ?_⟩
  · rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro (σ : Perm (Fin n)) (m : G6.PermMod n) hm
    have hm' : m = 1 := Subgroup.mem_bot.1 hm
    show G6.permAct n σ m ∈ (⊥ : Subgroup (G6.PermMod n))
    rw [hm', map_one]
    exact Subgroup.one_mem _
  · refine ⟨(QuotientGroup.mk' _).comp (E.symm.toMonoidHom.comp (⊤ : Subgroup V).subtype),
      ?_, fun u => ?_, ?_⟩
    · intro q
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ q
      refine ⟨⟨E m, trivial⟩, ?_⟩
      exact congrArg QuotientGroup.mk (E.symm_apply_apply m)
    · rw [Subgroup.mem_bot]
      show QuotientGroup.mk (E.symm (u : V)) = (1 : ↥(G6.coreMod n) ⧸
        (⊥ : Subgroup (G6.PermMod n)).subgroupOf (G6.coreMod n)) ↔ (u : V) = 1
      constructor
      · intro h1
        have h2 : E.symm (u : V) = 1 := hq (h1.trans (map_one _).symm)
        simpa using h2
      · intro h1
        rw [h1, map_one]
        rfl
    · intro (σ : Perm (Fin n)) u m hu hm hum
      have hm' : E.symm (u : V) = m := hq hum
      show QuotientGroup.mk (E.symm (((π σ : ↥H) : MulAut V) (u : V))) =
        QuotientGroup.mk (⟨G6.permAct n σ m.1, hm⟩ : ↥(G6.coreMod n))
      congr 1
      rw [MulEquiv.symm_apply_eq]
      have h2 := hE σ (E.symm (u : V))
      rw [MulEquiv.apply_symm_apply] at h2
      rw [← h2]
      congr 2
      rw [hm']

theorem symmetricCore_of_card [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    {n : ℕ} (hn : 3 ≤ n) (θ : ↥H ≃* Perm (Fin n))
    (htr : ∀ i j : Fin n, i ≠ j → Nat.card (commV (Subgroup.zpowers (swapAut θ i j))) = 2)
    (hVH : commV H = ⊤) (hcard : Nat.card V = 2 ^ (n - 1)) : SymmetricCore H ⊤ ⊥ n := by
  classical
  obtain ⟨c, hc⟩ := exists_center hV2 θ htr (by omega)
  set φ : ↥(G6.coreMod n) →* V := (prodHom hV2 c).comp (G6.coreMod n).subtype with hφ
  have hsurj : Function.Surjective φ := by
    intro v
    have hv : v ∈ commV H := by rw [hVH]; trivial
    have hle : commV H ≤ φ.range := by
      refine (G6.commV_mono (le_closure_swapAut θ)).trans (G6.commV_closure_le ?_)
      rintro _ ⟨i, j, hij, rfl⟩ w
      have hw := G6.mem_commV_of_mem (Subgroup.mem_zpowers (swapAut θ i j)) w
      rcases eq_one_or_eq_of_card_two (htr i j hij) (hc i j hij).1 (hc i j hij).2 hw with h1 | h1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [h1]
        refine ⟨⟨pairVec i j, pairVec_mem_coreMod i j⟩, ?_⟩
        rw [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype]
        exact prodHom_pairVec hV2 c hij
    obtain ⟨x, hx⟩ := hle hv
    exact ⟨x, hx⟩
  have hbij : Function.Bijective φ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [Explicit.card_coreMod (by omega), hcard]
  set E : ↥(G6.coreMod n) ≃* V := MulEquiv.ofBijective φ hbij with hE
  refine ⟨θ.symm.toMonoidHom, realizesVia_permModel_bot θ.symm.surjective E fun σ x => ?_⟩
  show prodHom hV2 c (G6.permAct n σ x) = ((θ.symm σ : ↥H) : MulAut V) (prodHom hV2 c x)
  exact prodHom_permAct hV2 θ hc htr σ x.2

end CFSG.Quasithin.G64
