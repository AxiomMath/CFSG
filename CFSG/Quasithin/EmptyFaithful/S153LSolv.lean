module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin

namespace S153L

section Helpers

variable {Γ : Type*} [Group Γ]

open scoped Pointwise

private lemma solv_sq_ne_one {e : Γ} (he : orderOf e = 3) : e * e ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one (show e ^ 2 = 1 by rw [pow_two]; exact h)
  rw [he] at this
  norm_num at this

private lemma solv_ne_inv {e : Γ} (he : orderOf e = 3) : e ≠ e⁻¹ := fun h =>
  solv_sq_ne_one he ((congrArg (e * ·) h).trans (mul_inv_cancel e))

private lemma solv_cube {e : Γ} (he : orderOf e = 3) : e ^ 3 = 1 :=
  he ▸ pow_orderOf_eq_one e

private lemma solv_cube_of_mem {e y : Γ} (he : orderOf e = 3) (hy : y ∈ Subgroup.zpowers e) :
    y ^ 3 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (he ▸ orderOf_dvd_of_mem_zpowers hy)

private lemma solv_zpow3 {e y : Γ} (he : orderOf e = 3) (hy : y ∈ Subgroup.zpowers e) :
    y = 1 ∨ y = e ∨ y = e⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hmod : e ^ (k % 3) = e ^ k := by simpa [he] using zpow_mod_orderOf e k
  rw [← hmod]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · left; simp
  · right; left; simp
  · right; right
    apply eq_inv_of_mul_eq_one_left
    rw [← zpow_add_one]
    exact_mod_cast solv_cube he

private lemma solv_orderOf_conj (g x : Γ) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc] : SemiconjBy g x (g * x * g⁻¹))).symm

private lemma solv_two {R : Subgroup Γ} (hR : IsPGroup 2 R) {x : Γ} (hx : x ∈ R) (h3 : x ^ 3 = 1) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h3)
      (Nat.Coprime.pow_right k (by norm_num))
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hk'))

private lemma solv_idx {S : Subgroup Γ} (hS : Nat.card S = 6) {e : Γ} (heS : e ∈ S)
    (he : orderOf e = 3) {x y : Γ} (hx : x ∈ S) (hy : y ∈ S) :
    x * y ∈ Subgroup.zpowers e ↔ (x ∈ Subgroup.zpowers e ↔ y ∈ Subgroup.zpowers e) := by
  have hle : Subgroup.zpowers e ≤ S := Subgroup.zpowers_le.mpr heS
  have hidx : ((Subgroup.zpowers e).subgroupOf S).index = 2 := by
    have h1 := Subgroup.card_mul_index ((Subgroup.zpowers e).subgroupOf S)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, he, hS] at h1
    omega
  simpa [Subgroup.mem_subgroupOf] using
    Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)

private lemma solv_not_le_zpowers {S : Subgroup Γ} (hna : ∃ a b : S, a * b ≠ b * a) (x : Γ) :
    ¬ S ≤ Subgroup.zpowers x := by
  intro h
  obtain ⟨a, b, hab⟩ := hna
  apply hab
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (h a.2)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (h b.2)
  apply Subtype.ext
  simp only [Subgroup.coe_mul, ← hm, ← hn]
  exact zpow_mul_comm x m n

section S3

variable {S : Subgroup Γ} (hS : Nat.card S = 6) (hna : ∃ a b : S, a * b ≠ b * a)
  {e : Γ} (heS : e ∈ S) (he : orderOf e = 3)
include hS hna heS he

private lemma solv_inv {x : Γ} (hx : x ∈ S) (hxe : x ∉ Subgroup.zpowers e) :
    x * x = 1 ∧ x * e * x⁻¹ = e⁻¹ := by
  have hsq : ∀ z ∈ S, z ∉ Subgroup.zpowers e → z * z = 1 := by
    intro z hz hze
    have hzz : z * z ∈ Subgroup.zpowers e := (solv_idx hS heS he hz hz).mpr Iff.rfl
    by_contra hne
    have hez : e ∈ Subgroup.zpowers z := by
      have hm : z * z ∈ Subgroup.zpowers z :=
        Subgroup.mul_mem _ (Subgroup.mem_zpowers z) (Subgroup.mem_zpowers z)
      rcases solv_zpow3 he hzz with h | h | h
      · exact absurd h hne
      · exact h ▸ hm
      · simpa [h] using Subgroup.inv_mem _ hm
    apply solv_not_le_zpowers hna z
    intro y hy
    by_cases hye : y ∈ Subgroup.zpowers e
    · exact Subgroup.zpowers_le.mpr hez hye
    · have h1 : z⁻¹ * y ∈ Subgroup.zpowers e :=
        (solv_idx hS heS he (S.inv_mem hz) hy).mpr
          (iff_of_false (fun h' => hze (by simpa using Subgroup.inv_mem _ h')) hye)
      simpa using Subgroup.mul_mem _ (Subgroup.mem_zpowers z) (Subgroup.zpowers_le.mpr hez h1)
  have h2 := hsq x hx hxe
  refine ⟨h2, ?_⟩
  have hxe' : x * e ∉ Subgroup.zpowers e := fun h =>
    hxe (((solv_idx hS heS he hx heS).mp h).mpr (Subgroup.mem_zpowers e))
  have h1 := hsq (x * e) (S.mul_mem hx heS) hxe'
  rw [← (eq_inv_of_mul_eq_one_left h2)]
  exact eq_inv_of_mul_eq_one_left (by simpa [mul_assoc] using h1)

private lemma solv_inv_zpow {x : Γ} (hx : x ∈ S) (hxe : x ∉ Subgroup.zpowers e) {y : Γ}
    (hy : y ∈ Subgroup.zpowers e) : x * y * x⁻¹ = y⁻¹ := by
  have h := (solv_inv hS hna heS he hx hxe).2
  rcases solv_zpow3 he hy with rfl | rfl | rfl
  · simp
  · exact h
  · rw [show x * e⁻¹ * x⁻¹ = (x * e * x⁻¹)⁻¹ by group, h]

private lemma solv_ord3 {x : Γ} (hx : x ∈ S) (hx3 : orderOf x = 3) : x = e ∨ x = e⁻¹ := by
  have hxe : x ∈ Subgroup.zpowers e := by
    by_contra h
    exact solv_sq_ne_one hx3 (solv_inv hS hna heS he hx h).1
  rcases solv_zpow3 he hxe with rfl | h | h
  · simp at hx3
  · exact Or.inl h
  · exact Or.inr h

private lemma solv_conj {x : Γ} (hx : x ∈ S) : x * e * x⁻¹ = e ∨ x * e * x⁻¹ = e⁻¹ := by
  by_cases hxe : x ∈ Subgroup.zpowers e
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxe
    left
    group
  · exact Or.inr (solv_inv hS hna heS he hx hxe).2

private lemma solv_mem_of_comm {x : Γ} (hx : x ∈ S) (hxc : x * e * x⁻¹ = e) :
    x ∈ Subgroup.zpowers e := by
  by_contra h
  have := (solv_inv hS hna heS he hx h).2
  rw [hxc] at this
  exact solv_ne_inv he this

private lemma solv_mem_of_cube {x : Γ} (hx : x ∈ S) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.zpowers e := by
  by_contra h
  have h2 := (solv_inv hS hna heS he hx h).1
  have h1 : x = 1 := by
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [hx3, h2]; group
  exact h (h1 ▸ Subgroup.one_mem _)

omit hS heS he in
private lemma solv_exists_out : ∃ t ∈ S, t ∉ Subgroup.zpowers e :=
  IsConcreteLE.not_le_iff_exists.mp (solv_not_le_zpowers hna e)

omit heS he in
private lemma solv_A : ∀ u ∈ S, ∀ v ∈ S, orderOf u = 3 → orderOf v = 3 → v = u ∨ v = u⁻¹ :=
  fun _ hu _ hv hu3 hv3 => solv_ord3 hS hna hu hu3 hv hv3

end S3

private lemma solv_fix {G₁ G₂ : Subgroup Γ} (h12 : G₁ ⊓ G₂ = ⊥)
    (hA₁ : ∀ u ∈ G₁, ∀ v ∈ G₁, orderOf u = 3 → orderOf v = 3 → v = u ∨ v = u⁻¹)
    (hA₂ : ∀ u ∈ G₂, ∀ v ∈ G₂, orderOf u = 3 → orderOf v = 3 → v = u ∨ v = u⁻¹)
    (Q : Γ → Prop) (hQ : ∀ x, Q x → x ∈ G₁ ∨ x ∈ G₂) (hQo : ∀ x, Q x → orderOf x = 3)
    {g : Γ} (hg : g ^ 3 = 1) (hQg : ∀ x, Q x → Q (g * x * g⁻¹))
    {e : Γ} (he : e ∈ G₁) (hQe : Q e) : g * e * g⁻¹ = e := by
  have hinv : ∀ u : Γ, g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := fun u => by group
  have he3 := hQo e hQe
  have hboth : e ∉ G₂ := fun h2 => by
    have : e ∈ G₁ ⊓ G₂ := ⟨he, h2⟩
    rw [h12, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at he3
    exact absurd he3 (by norm_num)
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ = g * e * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, x₂ = g * x₁ * g⁻¹ := ⟨_, rfl⟩
  have hq₁ : Q x₁ := hx₁ ▸ hQg e hQe
  have hq₂ : Q x₂ := hx₂ ▸ hQg x₁ hq₁
  have h3 : g * x₂ * g⁻¹ = e := by
    rw [hx₂, hx₁]
    calc g * (g * (g * e * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * e * (g * g * g)⁻¹ := by group
      _ = e := by rw [← pow_three', hg]; group
  rcases hQ x₁ hq₁ with h₁ | h₁
  · rcases hA₁ e he x₁ h₁ he3 (hQo x₁ hq₁) with h | h
    · exact hx₁ ▸ h
    · exfalso
      have h₂ : x₂ = e := by rw [hx₂, h, hinv, ← hx₁, h, inv_inv]
      rw [h₂, ← hx₁, h] at h3
      exact solv_ne_inv he3 h3.symm
  · exfalso
    rcases hQ x₂ hq₂ with h₂ | h₂
    · rcases hA₁ e he x₂ h₂ he3 (hQo x₂ hq₂) with h | h
      · rw [h, ← hx₁] at h3
        exact hboth (h3 ▸ h₁)
      · rw [h, hinv, ← hx₁] at h3
        exact hboth (h3 ▸ Subgroup.inv_mem _ h₁)
    · rcases hA₂ x₁ h₁ x₂ h₂ (hQo x₁ hq₁) (hQo x₂ hq₂) with h | h
      · rw [h, ← hx₂] at h3
        exact hboth (h3 ▸ h₂)
      · rw [h, hinv, ← hx₂] at h3
        exact hboth (h3 ▸ Subgroup.inv_mem _ h₂)

section Product

variable {G₁ G₂ : Subgroup Γ} (hc : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
include hc

private lemma solv_decomp {x : Γ} (hx : x ∈ G₁ ⊔ G₂) : ∃ a ∈ G₁, ∃ b ∈ G₂, x = a * b := by
  have hle : G₁ ≤ Subgroup.normalizer (G₂ : Set Γ) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rwa [hc a ha h hh, mul_inv_cancel_right]
    · intro hh
      have hk := hc a⁻¹ (G₁.inv_mem ha) _ hh
      have : h = a * h * a⁻¹ := by
        calc h = a⁻¹ * (a * h * a⁻¹) * a := by group
          _ = a * h * a⁻¹ * a⁻¹ * a := by rw [hk]
          _ = a * h * a⁻¹ := by group
      rw [this]
      exact hh
  have hx' : x ∈ (G₁ : Set Γ) * (G₂ : Set Γ) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right G₁ G₂ hle]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨a, ha, b, hb, rfl⟩

variable {J : Subgroup Γ} (hsup : G₁ ⊔ G₂ = J) (h1c : Nat.card G₁ = 6)
  (h1na : ∃ a b : G₁, a * b ≠ b * a) {e₁ : Γ} (he₁ : e₁ ∈ G₁) (he₁o : orderOf e₁ = 3)
include hsup h1c h1na he₁ he₁o

private lemma solv_P : ∀ j ∈ J, j * e₁ * j⁻¹ = e₁ ∨ j * e₁ * j⁻¹ = e₁⁻¹ := by
  intro j hj
  rw [← hsup] at hj
  obtain ⟨a, ha, b, hb, rfl⟩ := solv_decomp hc hj
  have hbe : b * e₁ = e₁ * b := (hc e₁ he₁ b hb).symm
  have : a * b * e₁ * (a * b)⁻¹ = a * e₁ * a⁻¹ := by
    calc a * b * e₁ * (a * b)⁻¹ = a * (b * e₁) * b⁻¹ * a⁻¹ := by group
      _ = a * (e₁ * b) * b⁻¹ * a⁻¹ := by rw [hbe]
      _ = a * e₁ * a⁻¹ := by group
  rw [this]
  exact solv_conj h1c h1na he₁ he₁o ha

private lemma solv_type (h12 : G₁ ⊓ G₂ = ⊥) {x : Γ} (hxJ : x ∈ J) (hx3 : x ^ 3 = 1)
    (hP : ∀ j ∈ J, j * x * j⁻¹ = x ∨ j * x * j⁻¹ = x⁻¹) : x ∈ G₁ ∨ x ∈ G₂ := by
  rw [← hsup] at hxJ
  obtain ⟨a, ha, b, hb, rfl⟩ := solv_decomp hc hxJ
  have hab : Commute a b := hc a ha b hb
  have h33 : a ^ 3 * b ^ 3 = 1 := by rw [← hab.mul_pow]; exact hx3
  have ha3 : a ^ 3 = 1 := by
    have hmem : a ^ 3 ∈ G₁ ⊓ G₂ := ⟨G₁.pow_mem ha 3, by
      rw [eq_inv_of_mul_eq_one_left h33]; exact G₂.inv_mem (G₂.pow_mem hb 3)⟩
    rwa [h12, Subgroup.mem_bot] at hmem
  have hb3 : b ^ 3 = 1 := by rwa [ha3, one_mul] at h33
  have haE : a ∈ Subgroup.zpowers e₁ := solv_mem_of_cube h1c h1na he₁ he₁o ha ha3
  obtain ⟨t, htG, htE⟩ := solv_exists_out h1na (e := e₁)
  have hta : t * a * t⁻¹ = a⁻¹ := solv_inv_zpow h1c h1na he₁ he₁o htG htE haE
  have htb : t * b * t⁻¹ = b := by rw [hc t htG b hb, mul_inv_cancel_right]
  have hconj : t * (a * b) * t⁻¹ = a⁻¹ * b := by
    calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      _ = a⁻¹ * b := by rw [hta, htb]
  have hone : ∀ y : Γ, y ^ 3 = 1 → y⁻¹ = y → y = 1 := fun y hy3 hyi => by
    have hyy : y * y = 1 := by
      calc y * y = y * y⁻¹ := by rw [hyi]
        _ = 1 := mul_inv_cancel y
    calc y = y ^ 3 * (y * y)⁻¹ := by group
      _ = 1 := by rw [hy3, hyy]; group
  rcases hP t (hsup ▸ Subgroup.mem_sup_left htG) with h | h
  · right
    rw [hconj] at h
    rw [hone a ha3 (mul_right_cancel h), one_mul]
    exact hb
  · left
    rw [hconj, mul_inv_rev, ← hab.inv_inv.eq] at h
    rw [hone b hb3 (mul_left_cancel h).symm, mul_one]
    exact ha

end Product

end Helpers

theorem solv_absurd {Γ : Type*} [Group Γ] [Finite Γ] (H J M Y T B : Subgroup Γ)
    (hJH : J ≤ H) (hJn : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J)
    (hYM : Y ≤ M) (hMH : M ≤ H)
    (hBJ : B ≤ J) (hBne : B ≠ ⊥)
    (hBR : ∃ R : Subgroup Γ, IsPGroup 2 R ∧ B ≤ R ∧ ∀ x ∈ Y ⊔ T, ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hθ : ∀ x ∈ M, orderOf x = 3 → x ∈ Y)
    (hYgen : Y = Subgroup.closure {y | y ∈ Y ∧ orderOf y = 3})
    (hKL : ∀ X : Subgroup Γ, X ≤ H → (∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) → X ≤ M)
    (hshape : (Nat.card J = 6 ∧ ∃ a b : J, a * b ≠ b * a) ∨
      ∃ G₁ G₂ : Subgroup Γ, G₁ ⊔ G₂ = J ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧
        (Nat.card G₁ = 6 ∧ ∃ a b : G₁, a * b ≠ b * a) ∧
        (Nat.card G₂ = 6 ∧ ∃ a b : G₂, a * b ≠ b * a)) :
    False := by
  obtain ⟨R, hR2, hBR, hRn⟩ := hBR
  have hfin : ∀ e b : Γ, e ∈ J → orderOf e = 3 → b ∈ B → b * e * b⁻¹ = e⁻¹ →
      (∀ g ∈ H, orderOf g = 3 → g * e * g⁻¹ = e) → False := by
    intro e b heJ he3 hbB hinv hfix
    have hYc : Y ≤ Subgroup.centralizer {e} := by
      refine hYgen.le.trans ((Subgroup.closure_le _).mpr ?_)
      rintro y ⟨hyY, hy3⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (mul_inv_eq_iff_eq_mul.mp (hfix y (hMH (hYM hyY)) hy3)).symm
    have hXM : Subgroup.zpowers e ≤ M := by
      refine hKL _ (Subgroup.zpowers_le.mpr (hJH heJ)) fun x hx y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Commute.zpow_left (Subgroup.mem_centralizer_iff.mp (hYc hy) e rfl) k
    have heY : e ∈ Y := hθ e (hXM (Subgroup.mem_zpowers e)) he3
    have hbR : b ∈ R := hBR hbB
    have hmem : e * b * e⁻¹ * b⁻¹ ∈ R :=
      R.mul_mem (hRn e (Subgroup.mem_sup_left heY) b hbR) (R.inv_mem hbR)
    have hee : e * b * e⁻¹ * b⁻¹ = e * e := by
      calc e * b * e⁻¹ * b⁻¹ = e * (b * e * b⁻¹)⁻¹ := by group
        _ = e * e := by rw [hinv, inv_inv]
    rw [hee] at hmem
    refine solv_sq_ne_one he3 (solv_two hR2 hmem ?_)
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, solv_cube he3, one_pow]
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbR : b ∈ R := hBR hbB
  have hbJ : b ∈ J := hBJ hbB
  rcases hshape with ⟨hJ6, hJna⟩ | ⟨G₁, G₂, hsup, hinf, hc, ⟨h1c, h1na⟩, ⟨h2c, h2na⟩⟩
  ·
    obtain ⟨⟨e, heJ⟩, he3⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 (by rw [hJ6]; norm_num)
    rw [Subgroup.orderOf_mk] at he3
    have hbE : b ∉ Subgroup.zpowers e := fun h =>
      hb1' (solv_two hR2 hbR (solv_cube_of_mem he3 h))
    refine hfin e b heJ he3 hbB (solv_inv hJ6 hJna heJ he3 hbJ hbE).2 fun g hg hg3 => ?_
    refine solv_fix (G₁ := J) (G₂ := ⊥) (inf_bot_eq J) (solv_A hJ6 hJna) ?_
      (fun x => x ∈ J ∧ orderOf x = 3) (fun x hx => Or.inl hx.1) (fun x hx => hx.2)
      (solv_cube hg3) (fun x hx => ⟨hJn g hg x hx.1, (solv_orderOf_conj g x).trans hx.2⟩)
      heJ ⟨heJ, he3⟩
    intro u hu
    rw [Subgroup.mem_bot] at hu
    subst hu
    intro _ _ h
    simp at h
  ·
    obtain ⟨⟨e₁, he₁⟩, he₁3⟩ := exists_prime_orderOf_dvd_card' (G := G₁) 3 (by rw [h1c]; norm_num)
    obtain ⟨⟨e₂, he₂⟩, he₂3⟩ := exists_prime_orderOf_dvd_card' (G := G₂) 3 (by rw [h2c]; norm_num)
    rw [Subgroup.orderOf_mk] at he₁3 he₂3
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hsup' : G₂ ⊔ G₁ = J := by rw [sup_comm]; exact hsup
    have hinf' : G₂ ⊓ G₁ = ⊥ := by rw [inf_comm]; exact hinf
    have hP₁ := solv_P hc hsup h1c h1na he₁ he₁3
    have hP₂ := solv_P hc' hsup' h2c h2na he₂ he₂3
    have hQg : ∀ g ∈ H, ∀ x : Γ,
        (x ∈ J ∧ orderOf x = 3 ∧ ∀ j ∈ J, j * x * j⁻¹ = x ∨ j * x * j⁻¹ = x⁻¹) →
        (g * x * g⁻¹ ∈ J ∧ orderOf (g * x * g⁻¹) = 3 ∧ ∀ j ∈ J,
          j * (g * x * g⁻¹) * j⁻¹ = g * x * g⁻¹ ∨ j * (g * x * g⁻¹) * j⁻¹ = (g * x * g⁻¹)⁻¹) := by
      rintro g hg x ⟨hxJ, hx3, hxP⟩
      refine ⟨hJn g hg x hxJ, (solv_orderOf_conj g x).trans hx3, fun j hj => ?_⟩
      have hj' : g⁻¹ * j * g ∈ J := by simpa using hJn g⁻¹ (H.inv_mem hg) j hj
      have key : j * (g * x * g⁻¹) * j⁻¹ =
          g * ((g⁻¹ * j * g) * x * (g⁻¹ * j * g)⁻¹) * g⁻¹ := by group
      rcases hxP _ hj' with h | h
      · left
        rw [key, h]
      · right
        rw [key, h]
        group
    have hfix₁ : ∀ g ∈ H, orderOf g = 3 → g * e₁ * g⁻¹ = e₁ := fun g hg hg3 =>
      solv_fix hinf (solv_A h1c h1na) (solv_A h2c h2na) _
        (fun x hx => solv_type hc hsup h1c h1na he₁ he₁3 hinf hx.1 (solv_cube hx.2.1) hx.2.2)
        (fun x hx => hx.2.1) (solv_cube hg3) (hQg g hg) he₁
        ⟨hsup ▸ Subgroup.mem_sup_left he₁, he₁3, hP₁⟩
    have hfix₂ : ∀ g ∈ H, orderOf g = 3 → g * e₂ * g⁻¹ = e₂ := fun g hg hg3 =>
      solv_fix hinf' (solv_A h2c h2na) (solv_A h1c h1na) _
        (fun x hx => solv_type hc' hsup' h2c h2na he₂ he₂3 hinf' hx.1 (solv_cube hx.2.1) hx.2.2)
        (fun x hx => hx.2.1) (solv_cube hg3) (hQg g hg) he₂
        ⟨hsup' ▸ Subgroup.mem_sup_left he₂, he₂3, hP₂⟩
    rcases hP₁ b hbJ with h1 | h1
    · rcases hP₂ b hbJ with h2 | h2
      ·
        rw [← hsup] at hbJ
        obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := solv_decomp hc hbJ
        have k₁ : b₁ * b₂ * e₁ * (b₁ * b₂)⁻¹ = b₁ * e₁ * b₁⁻¹ := by
          have hbe : b₂ * e₁ = e₁ * b₂ := (hc e₁ he₁ b₂ hb₂).symm
          calc b₁ * b₂ * e₁ * (b₁ * b₂)⁻¹ = b₁ * (b₂ * e₁) * b₂⁻¹ * b₁⁻¹ := by group
            _ = b₁ * (e₁ * b₂) * b₂⁻¹ * b₁⁻¹ := by rw [hbe]
            _ = b₁ * e₁ * b₁⁻¹ := by group
        have k₂ : b₁ * b₂ * e₂ * (b₁ * b₂)⁻¹ = b₂ * e₂ * b₂⁻¹ := by
          have hbe : b₁ * e₂ = e₂ * b₁ := hc b₁ hb₁ e₂ he₂
          rw [hc b₁ hb₁ b₂ hb₂]
          calc b₂ * b₁ * e₂ * (b₂ * b₁)⁻¹ = b₂ * (b₁ * e₂) * b₁⁻¹ * b₂⁻¹ := by group
            _ = b₂ * (e₂ * b₁) * b₁⁻¹ * b₂⁻¹ := by rw [hbe]
            _ = b₂ * e₂ * b₂⁻¹ := by group
        have hb₁3 := solv_cube_of_mem he₁3 (solv_mem_of_comm h1c h1na he₁ he₁3 hb₁ (k₁ ▸ h1))
        have hb₂3 := solv_cube_of_mem he₂3 (solv_mem_of_comm h2c h2na he₂ he₂3 hb₂ (k₂ ▸ h2))
        have hbb : Commute b₁ b₂ := hc b₁ hb₁ b₂ hb₂
        refine hb1' (solv_two hR2 hbR ?_)
        rw [hbb.mul_pow, hb₁3, hb₂3, one_mul]
      · exact hfin e₂ b (hsup' ▸ Subgroup.mem_sup_left he₂) he₂3 hbB h2 hfix₂
    · exact hfin e₁ b (hsup ▸ Subgroup.mem_sup_left he₁) he₁3 hbB h1 hfix₁

end S153L

end CFSG.Quasithin
