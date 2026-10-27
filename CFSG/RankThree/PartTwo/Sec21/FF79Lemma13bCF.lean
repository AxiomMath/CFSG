module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma13bSyl

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L13bCF

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.L13b

variable {G : Type} [Group G]

structure Crd (B : Subgroup G) (ω : Fin 3 → G) where
  co : Fin 3 → G → ZMod 3
  co_mul : ∀ i, ∀ x ∈ B, ∀ y ∈ B, co i (x * y) = co i x + co i y
  co_ω : ∀ i j, co i (ω j) = if i = j then 1 else 0
  co_inj : ∀ x ∈ B, ∀ y ∈ B, (∀ i, co i x = co i y) → x = y

theorem exists_crd [Finite G] {B : Subgroup G} {ω : Fin 3 → G} (hB : IsElemAb 3 3 B)
    (hω : ∀ i, ω i ∈ B) (hcl : B = Subgroup.closure (Set.range ω)) : Nonempty (Crd B ω) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsElementaryAbelian 3 ↥B := hB.1
  letI : CommGroup ↥B := IsMulCommutative.instCommGroup
  letI : Module (ZMod 3) (Additive ↥B) := IsElementaryAbelian.isVectorSpace 3
  haveI : Finite (Additive ↥B) := inferInstanceAs (Finite ↥B)
  haveI : Module.Finite (ZMod 3) (Additive ↥B) := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 3) (Additive ↥B) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive ↥B)
    have h1 : Nat.card (Additive ↥B) = 3 ^ 3 := hB.2
    rw [h1, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  let v : Fin 3 → Additive ↥B := fun i => Additive.ofMul ⟨ω i, hω i⟩
  have hspan : ⊤ ≤ Submodule.span (ZMod 3) (Set.range v) := by
    intro u hu
    clear hu
    obtain ⟨⟨x, hxB⟩, rfl⟩ : ∃ y : ↥B, Additive.ofMul y = u := ⟨Additive.toMul u, by simp⟩
    have hx : x ∈ Subgroup.closure (Set.range ω) := hcl ▸ hxB
    revert hxB
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro h
      exact Submodule.subset_span ⟨i, rfl⟩
    | one => intro h; exact Submodule.zero_mem _
    | mul x y hx hy ihx ihy =>
      intro h
      have hx' : x ∈ B := hcl ▸ hx
      have hy' : y ∈ B := hcl ▸ hy
      have : Additive.ofMul (⟨x * y, h⟩ : ↥B) =
          Additive.ofMul (⟨x, hx'⟩ : ↥B) + Additive.ofMul (⟨y, hy'⟩ : ↥B) := rfl
      rw [this]
      exact Submodule.add_mem _ (ihx hx') (ihy hy')
    | inv x hx ih =>
      intro h
      have hx' : x ∈ B := hcl ▸ hx
      have : Additive.ofMul (⟨x⁻¹, h⟩ : ↥B) = - Additive.ofMul (⟨x, hx'⟩ : ↥B) := rfl
      rw [this]
      exact Submodule.neg_mem _ (ih hx')
  have hli : LinearIndependent (ZMod 3) v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by rw [hrank]; simp)
  let bs : Module.Basis (Fin 3) (ZMod 3) (Additive ↥B) := Module.Basis.mk hli hspan
  classical
  refine ⟨⟨fun i x => if h : x ∈ B then bs.repr (Additive.ofMul ⟨x, h⟩) i else 0,
    fun i x hx y hy => ?_, fun i j => ?_, fun x hx y hy h => ?_⟩⟩
  · have hxy : x * y ∈ B := B.mul_mem hx hy
    simp only [hx, hy, hxy, dite_true]
    have : Additive.ofMul (⟨x * y, hxy⟩ : ↥B) =
        Additive.ofMul (⟨x, hx⟩ : ↥B) + Additive.ofMul (⟨y, hy⟩ : ↥B) := rfl
    rw [this, map_add]
    rfl
  · simp only [hω j, dite_true]
    have : Additive.ofMul (⟨ω j, hω j⟩ : ↥B) = bs j := by simp [bs, v]
    rw [this, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  · have h' : bs.repr (Additive.ofMul ⟨x, hx⟩) = bs.repr (Additive.ofMul ⟨y, hy⟩) := by
      ext i
      simpa [hx, hy] using h i
    have := bs.repr.injective h'
    have := Additive.ofMul.injective this
    exact congrArg Subtype.val this

variable {B : Subgroup G} {ω : Fin 3 → G}

theorem Crd.co_one (c : Crd B ω) (i : Fin 3) : c.co i 1 = 0 := by
  have h := c.co_mul i 1 B.one_mem 1 B.one_mem
  rw [mul_one] at h
  linear_combination -h

theorem Crd.co_inv (c : Crd B ω) (i : Fin 3) {x : G} (hx : x ∈ B) :
    c.co i x⁻¹ = - c.co i x := by
  have h := c.co_mul i x⁻¹ (B.inv_mem hx) x hx
  rw [inv_mul_cancel, c.co_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

@[expose] def Rel (ω : Fin 3 → G) (n : G) (i j : Fin 3) : Prop :=
  n * ω i * n⁻¹ = ω j ∨ n * ω i * n⁻¹ = (ω j)⁻¹

theorem rel_one (ω : Fin 3 → G) (i : Fin 3) : Rel ω 1 i i := Or.inl (by simp)

theorem rel_mul {m n : G} {i j k : Fin 3} (hm : Rel ω m i j) (hn : Rel ω n j k) :
    Rel ω (n * m) i k := by
  have h : n * m * ω i * (n * m)⁻¹ = n * (m * ω i * m⁻¹) * n⁻¹ := by group
  have e : n * (ω j)⁻¹ * n⁻¹ = (n * ω j * n⁻¹)⁻¹ := by group
  unfold Rel at *
  rw [h]
  rcases hm with hm | hm <;> rw [hm]
  · exact hn
  · rw [e]
    rcases hn with hn | hn <;> rw [hn]
    · exact Or.inr rfl
    · exact Or.inl (inv_inv _)

theorem rel_unique (c : Crd B ω) (hω : ∀ i, ω i ∈ B) {n : G} {i j k : Fin 3}
    (h1 : Rel ω n i j) (h2 : Rel ω n i k) : j = k := by
  by_contra hjk
  have key : ω j = ω k ∨ ω j = (ω k)⁻¹ := by
    unfold Rel at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (h1.symm.trans h2)
    · exact Or.inr (h1.symm.trans h2)
    · exact Or.inr (inv_eq_iff_eq_inv.mp (h1.symm.trans h2))
    · left; exact inv_injective (h1.symm.trans h2)
  have h0 : c.co j (ω j) = 1 := by simp [c.co_ω]
  have h1 : c.co j (ω k) = 0 := by simp [c.co_ω, hjk]
  rcases key with h | h
  · rw [h, h1] at h0; exact zero_ne_one h0
  · rw [h, c.co_inv j (hω k), h1] at h0; exact absurd h0 (by decide)

theorem conj_mem' {n x : G} (hn : n ∈ Nor B) (hx : x ∈ B) : n * x * n⁻¹ ∈ B :=
  ((Subgroup.mem_set_normalizer_iff.mp hn) x).mp hx

structure Mono (B : Subgroup G) (ω : Fin 3 → G) where
  crd : Crd B ω
  mem : ∀ i, ω i ∈ B
  cl : B = Subgroup.closure (Set.range ω)
  mono : ∀ n ∈ Nor B, ∀ i, ∃ j, Rel ω n i j
  card : Nat.card B = 27
  comm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x

noncomputable def rhoFun (M : Mono B ω) (n : Nor B) : Equiv.Perm (Fin 3) where
  toFun i := Classical.choose (M.mono n.1 n.2 i)
  invFun j := Classical.choose (M.mono (n⁻¹ : Nor B).1 (n⁻¹ : Nor B).2 j)
  left_inv i := by
    have h1 := Classical.choose_spec (M.mono n.1 n.2 i)
    have h2 := Classical.choose_spec (M.mono (n⁻¹ : Nor B).1 (n⁻¹ : Nor B).2
      (Classical.choose (M.mono n.1 n.2 i)))
    have h3 := rel_mul h1 h2
    have h4 : (n⁻¹ : Nor B).1 * n.1 = 1 := congrArg Subtype.val (inv_mul_cancel n)
    rw [h4] at h3
    exact rel_unique M.crd M.mem h3 (rel_one ω i)
  right_inv j := by
    have h1 := Classical.choose_spec (M.mono (n⁻¹ : Nor B).1 (n⁻¹ : Nor B).2 j)
    have h2 := Classical.choose_spec (M.mono n.1 n.2
      (Classical.choose (M.mono (n⁻¹ : Nor B).1 (n⁻¹ : Nor B).2 j)))
    have h3 := rel_mul h1 h2
    have h4 : n.1 * (n⁻¹ : Nor B).1 = 1 := congrArg Subtype.val (mul_inv_cancel n)
    rw [h4] at h3
    exact rel_unique M.crd M.mem h3 (rel_one ω j)

theorem rhoFun_spec (M : Mono B ω) (n : Nor B) (i : Fin 3) : Rel ω n.1 i (rhoFun M n i) :=
  Classical.choose_spec (M.mono n.1 n.2 i)

noncomputable def rho (M : Mono B ω) : Nor B →* Equiv.Perm (Fin 3) :=
  MonoidHom.mk' (rhoFun M) (fun m n => by
    refine Equiv.ext fun i => ?_
    have h1 := rel_mul (rhoFun_spec M n i) (rhoFun_spec M m (rhoFun M n i))
    exact rel_unique M.crd M.mem (rhoFun_spec M (m * n) i) h1)

theorem rho_spec (M : Mono B ω) (n : Nor B) (i : Fin 3) : Rel ω n.1 i (rho M n i) :=
  rhoFun_spec M n i


theorem eq_of_sylowOf [Finite G] {H P Q : Subgroup G} (hP : IsSylowOf 3 P H) (hPQ : P ≤ Q)
    (hQH : Q ≤ H) (hQ : IsPGroup 3 Q) : P = Q := by
  obtain ⟨k, -, hk⟩ := exists_conj_le_sylowOf hP hQH hQ
  have hle : Q.map (MulAut.conj k).toMonoidHom ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
  have hcard : Nat.card Q ≤ Nat.card P := by
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj k).injective] at this
  exact Subgroup.eq_of_le_of_card_ge hPQ hcard

theorem isPGroup_zpowers {n : G} {k : ℕ} (hk : n ^ (3 ^ k) = 1) :
    IsPGroup 3 (Subgroup.zpowers n) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])

theorem sq_fix {n : G} {i : Fin 3} (h : Rel ω n i i) : n * n * ω i * (n * n)⁻¹ = ω i := by
  have e : n * n * ω i * (n * n)⁻¹ = n * (n * ω i * n⁻¹) * n⁻¹ := by group
  rcases h with h | h
  · rw [e, h, h]
  · have e2 : n * (ω i)⁻¹ * n⁻¹ = (n * ω i * n⁻¹)⁻¹ := by group
    rw [e, h, e2, h, inv_inv]

theorem cen_of_rho_one (M : Mono B ω) {n : Nor B} (h1 : rho M n = 1) {k : ℕ}
    (hk : n.1 ^ (3 ^ k) = 1) : n.1 ∈ CenS B := by
  have hrel : ∀ i, Rel ω n.1 i i := fun i => by
    have := rho_spec M n i
    rwa [h1] at this
  have hsq : B ≤ Cen (n.1 * n.1) := by
    refine (le_of_eq M.cl).trans ((Subgroup.closure_le _).mpr ?_)
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := sq_fix (hrel i)
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hsq' : n.1 * n.1 ∈ CenS B := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := (Subgroup.mem_centralizer_iff.mp (hsq hh)) _ rfl
    exact this.symm
  obtain ⟨t, ht⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have hn : n.1 = (n.1 * n.1) ^ (t + 1) := by
    rw [← sq, ← pow_mul, show 2 * (t + 1) = 3 ^ k + 1 by omega, pow_succ, hk, one_mul]
  rw [hn]
  exact Subgroup.pow_mem _ hsq' _

theorem mem_of_cen [Finite G] {b : G} (hb : b ∈ B) (hB : IsSylowOf 3 B (Cen b))
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {n : G} (hn : n ∈ CenS B) {k : ℕ}
    (hk : n ^ (3 ^ k) = 1) : n ∈ B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnN : n ∈ Nor B := by
    refine mem_nor_of_forall (fun y hy => ?_)
    have := (Subgroup.mem_centralizer_iff.mp hn) y hy
    rwa [← this, mul_inv_cancel_right]
  have hnb : n ∈ Cen b := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (Subgroup.mem_centralizer_iff.mp hn) h hb
  have hBle : B ≤ Cen b := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm h hb z hz
  have hTp : IsPGroup 3 (Subgroup.zpowers n ⊔ B : Subgroup G) :=
    (isPGroup_zpowers hk).to_sup_of_normal_right' hB.2.1 (Subgroup.zpowers_le.mpr hnN)
  have hTle : Subgroup.zpowers n ⊔ B ≤ Cen b := sup_le (Subgroup.zpowers_le.mpr hnb) hBle
  have heq := eq_of_sylowOf hB le_sup_right hTle hTp
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers n)


theorem perm_pow_three (σ : Equiv.Perm (Fin 3)) {k : ℕ} (h : σ ^ (3 ^ k) = 1) : σ ^ 3 = 1 := by
  have h6 : ∀ τ : Equiv.Perm (Fin 3), τ ^ 6 = 1 := by decide
  cases k with
  | zero =>
    rw [pow_zero, pow_one] at h
    rw [h, one_pow]
  | succ j =>
    have h1 : (σ ^ 3) ^ (3 ^ j) = 1 := by rw [← pow_mul, ← pow_succ']; exact h
    have h2 : (σ ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact h6 σ
    have h3 := (pow_gcd_eq_one (a := σ ^ 3) (m := 3 ^ j) (n := 2)).mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left j (by norm_num)), pow_one] at h3

theorem perm_comm : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 → τ * σ = σ * τ →
    τ = 1 ∨ τ = σ ∨ τ = σ * σ := by decide

theorem perm_cover : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 →
    ∀ i, i = 0 ∨ i = σ 0 ∨ i = σ (σ 0) := by decide

theorem co_conj (M : Mono B ω) {n : G} (hn : n ∈ Nor B) (σ : Equiv.Perm (Fin 3))
    (s : Fin 3 → ZMod 3)
    (hs : ∀ k, (n * ω k * n⁻¹ = ω (σ k) ∧ s k = 1) ∨
      (n * ω k * n⁻¹ = (ω (σ k))⁻¹ ∧ s k = -1)) :
    ∀ x ∈ B, ∀ k, M.crd.co (σ k) (n * x * n⁻¹) = s k * M.crd.co k x := by
  intro x hx
  have hx' : x ∈ Subgroup.closure (Set.range ω) := M.cl ▸ hx
  revert hx
  induction hx' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    intro _ k
    rcases hs m with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, M.crd.co_ω, M.crd.co_ω]
      by_cases hkm : k = m
      · subst hkm; simp [h2]
      · simp [hkm, σ.injective.eq_iff]
    · rw [h1, M.crd.co_inv _ (M.mem _), M.crd.co_ω, M.crd.co_ω]
      by_cases hkm : k = m
      · subst hkm; simp [h2]
      · simp [hkm, σ.injective.eq_iff] <;> rfl
  | one =>
    intro _ k
    simp [M.crd.co_one]
  | mul x y hx hy ihx ihy =>
    intro hxy k
    have hx' : x ∈ B := M.cl ▸ hx
    have hy' : y ∈ B := M.cl ▸ hy
    have e : n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
    rw [e, M.crd.co_mul _ _ (conj_mem' hn hx') _ (conj_mem' hn hy'), ihx hx' k, ihy hy' k,
      M.crd.co_mul _ _ hx' _ hy', mul_add]
  | inv x hx ih =>
    intro hxi k
    have hx' : x ∈ B := M.cl ▸ hx
    have e : n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ := by group
    rw [e, M.crd.co_inv _ (conj_mem' hn hx'), ih hx' k, M.crd.co_inv _ hx']
    exact (by decide : ∀ a b : ZMod 3, -(a * b) = a * -b) _ _

theorem card_inf_le (M : Mono B ω) {A : Subgroup G} {a : G} (haA : a ∈ A) (haN : a ∈ Nor B)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h1 : rho M ⟨a, haN⟩ ≠ 1)
    (h3 : rho M ⟨a, haN⟩ ^ 3 = 1) : Nat.card ↥(A ⊓ B) ≤ 3 := by
  set σ := rho M ⟨a, haN⟩ with hσ
  have hsign : ∀ k, ∃ s : ZMod 3, (a * ω k * a⁻¹ = ω (σ k) ∧ s = 1) ∨
      (a * ω k * a⁻¹ = (ω (σ k))⁻¹ ∧ s = -1) := fun k => by
    rcases rho_spec M ⟨a, haN⟩ k with h | h
    · exact ⟨1, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨-1, Or.inr ⟨h, rfl⟩⟩
  choose s hs using hsign
  have key := co_conj M haN σ s hs
  have hfix : ∀ x : ↥(A ⊓ B), ∀ k, M.crd.co (σ k) x.1 = s k * M.crd.co k x.1 := by
    intro x k
    have hc : a * x.1 * a⁻¹ = x.1 := by rw [hAc a haA x.1 x.2.1, mul_inv_cancel_right]
    have := key x.1 x.2.2 k
    rwa [hc] at this
  have hinj : Function.Injective (fun x : ↥(A ⊓ B) => M.crd.co 0 x.1) := by
    intro x y hxy
    simp only at hxy
    have e1 : M.crd.co (σ 0) x.1 = M.crd.co (σ 0) y.1 := by rw [hfix, hfix, hxy]
    have e2 : M.crd.co (σ (σ 0)) x.1 = M.crd.co (σ (σ 0)) y.1 := by
      rw [hfix x (σ 0), hfix y (σ 0), e1]
    refine Subtype.ext (M.crd.co_inj x.1 x.2.2 y.1 y.2.2 fun i => ?_)
    rcases perm_cover σ h3 h1 i with rfl | rfl | rfl
    · exact hxy
    · exact e1
    · exact e2
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_zmod] at this

theorem cfAbelian_eq [Finite G] (M : Mono B ω) {b : G} (hb : b ∈ B) (hB : IsSylowOf 3 B (Cen b))
    {A : Subgroup G} (hAN : A ≤ Nor B) (hAp : IsPGroup 3 A)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hcard : 27 ≤ Nat.card A) : A = B := by
  by_cases hAB : A ≤ B
  · exact Subgroup.eq_of_le_of_card_ge hAB (by rw [M.card]; exact hcard)
  exfalso
  obtain ⟨a, haA, haB⟩ := SetLike.not_le_iff_exists.mp hAB
  let φ : A →* Equiv.Perm (Fin 3) := (rho M).comp (Subgroup.inclusion hAN)
  have hpow : ∀ x : A, ∃ k : ℕ, (x : G) ^ (3 ^ k) = 1 := fun x => by
    obtain ⟨k, hk⟩ := hAp x
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hker : ∀ x : A, φ x = 1 → (x : G) ∈ B := by
    intro x hx
    obtain ⟨k, hk⟩ := hpow x
    exact mem_of_cen hb hB M.comm (cen_of_rho_one M (n := Subgroup.inclusion hAN x) hx hk) hk
  have hσ1 : φ ⟨a, haA⟩ ≠ 1 := fun h => haB (hker _ h)
  have hσ3 : φ ⟨a, haA⟩ ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hAp ⟨a, haA⟩
    refine perm_pow_three _ (k := k) ?_
    rw [← map_pow, hk, map_one]
  have hcomm : ∀ x : A, φ x * φ ⟨a, haA⟩ = φ ⟨a, haA⟩ * φ x := fun x => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc x x.2 a haA)
  have hrange : φ.range ≤ Subgroup.zpowers (φ ⟨a, haA⟩) := by
    rintro _ ⟨x, rfl⟩
    rcases perm_comm _ (φ x) hσ3 hσ1 (hcomm x) with h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  have hr : Nat.card φ.range ≤ 3 := by
    refine (Subgroup.card_le_of_le hrange).trans ?_
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hσ3)
  have hk : Nat.card φ.ker ≤ 3 := by
    let f : φ.ker → ↥(A ⊓ B) := fun x => ⟨x.1.1, x.1.2, hker x.1 x.2⟩
    have hf : Function.Injective f := fun x y h => by
      have h' : ((f x).1 : G) = (f y).1 := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    exact (Nat.card_le_card_of_injective f hf).trans
      (card_inf_le M haA (hAN haA) hAc hσ1 hσ3)
  have := Subgroup.card_ker_mul_card_range φ
  nlinarith [Nat.zero_le (Nat.card φ.ker), Nat.zero_le (Nat.card φ.range)]

end CFSG.RankThree.PartTwo.Sec21.FF79.L13bCF
