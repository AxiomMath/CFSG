module

public import CFSG.Quasithin.H13.A5X1367h
public import CFSG.Quasithin.EmptyFaithful.SzN17Fac
public import CFSG.Quasithin.H13.A5X1367b

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique CFSG.Quasithin

theorem eq_of_card_three_of_card_six {X : Type} [Group X] [Finite X] (hX : Nat.card X = 6)
    {Q Q' : Subgroup X} (hQ : Nat.card ↥Q = 3) (hQ' : Nat.card ↥Q' = 3) : Q = Q' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card X).factorization 3 = 1 := by
    rw [hX, show (6 : ℕ) = 2 * 3 by rfl, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcQ : Nat.card ↥Q = 3 ^ (Nat.card X).factorization 3 := by rw [hfac, pow_one, hQ]
  have hcQ' : Nat.card ↥Q' = 3 ^ (Nat.card X).factorization 3 := by rw [hfac, pow_one, hQ']
  set P := Sylow.ofCard Q hcQ with hP
  set P' := Sylow.ofCard Q' hcQ' with hP'
  have hidx : (P : Subgroup X).index = 2 := by
    rw [hP, Sylow.coe_ofCard]
    have := Subgroup.card_mul_index Q
    rw [hQ, hX] at this
    omega
  have h1 := card_sylow_modEq_one 3 X
  have h2 := Sylow.card_dvd_index P
  rw [hidx] at h2
  have hc1 : Nat.card (Sylow 3 X) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) h2
    have hpos : 0 < Nat.card (Sylow 3 X) := Nat.card_pos
    interval_cases h : Nat.card (Sylow 3 X)
    · rfl
    · exact absurd h1 (by decide)
  have : Subsingleton (Sylow 3 X) := (Nat.card_eq_one_iff_unique.mp hc1).1
  have hPP : P = P' := Subsingleton.elim P P'
  have e1 : (P : Subgroup X) = Q := Sylow.coe_ofCard Q hcQ
  have e2 : (P' : Subgroup X) = Q' := Sylow.coe_ofCard Q' hcQ'
  rw [← e1, ← e2, hPP]

theorem eq_of_card_three_of_le {Γ : Type} [Group Γ] [Finite Γ] {G Q Q' : Subgroup Γ}
    (hG : Nat.card ↥G = 6) (hQG : Q ≤ G) (hQ'G : Q' ≤ G) (hQ : Nat.card ↥Q = 3)
    (hQ' : Nat.card ↥Q' = 3) : Q = Q' := by
  have h := eq_of_card_three_of_card_six hG (Q := Q.subgroupOf G) (Q' := Q'.subgroupOf G)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQG).toEquiv, hQ])
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ'G).toEquiv, hQ'])
  have := congrArg (Subgroup.map G.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hQG, Subgroup.map_subgroupOf_eq_of_le hQ'G] at this

theorem eq_or_eq_inv_of_mem_zpowers {Γ : Type} [Group Γ] {y x : Γ} (hy : orderOf y = 3)
    (hx : x ∈ Subgroup.zpowers y) (hx1 : x ≠ 1) : x = y ∨ x = y⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, hy] at hx1 ⊢
  have hk3 : k % (3 : ℕ) = 0 ∨ k % (3 : ℕ) = 1 ∨ k % (3 : ℕ) = 2 := by omega
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  rcases hk3 with h | h | h <;> rw [h] at hx1 ⊢
  · simp at hx1
  · left; simp
  · right
    have : y ^ (2 : ℤ) = y⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one]
      exact_mod_cast hy3
    exact this

theorem orderOf_conj' {Γ : Type} [Group Γ] (g y : Γ) : orderOf (g * y * g⁻¹) = orderOf y := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  simpa [MulAut.conj_apply] using this

theorem card_zpowers_three {Γ : Type} [Group Γ] {x : Γ} (hx : orderOf x = 3) :
    Nat.card ↥(Subgroup.zpowers x) = 3 := by
  rw [Nat.card_zpowers, hx]

theorem two_trivial_of_comm {U : Type} [Group U] {E : Subgroup U} (hE : Nat.card ↥E = 4)
    (hE2 : ∀ e ∈ E, e * e = 1) {α β : MulAut U} (hαE : ∀ e ∈ E, α e ∈ E)
    (hβE : ∀ e ∈ E, β e ∈ E) (hα : orderOf α = 3) (hβ : ∃ k : ℕ, β ^ 2 ^ k = 1)
    (hα1 : ∃ e ∈ E, α e ≠ e) (hαβ : α * β = β * α) : ∀ e ∈ E, β e = e := by
  by_contra hcon
  push Not at hcon
  have hαodd : Odd (orderOf α) := by rw [hα]; decide
  obtain ⟨hconj, hcube⟩ := four_aut hE hE2 hαE hβE hαodd hβ hα1 hcon
  obtain ⟨e₀, he₀, hαe₀⟩ := hα1
  apply hαe₀
  have h1 : ∀ e ∈ E, α e = α⁻¹ e := by
    intro e he
    have h := hconj e he
    have hab : α (β e) = β (α e) := by
      have := congrArg (fun f : MulAut U => f e) hαβ
      simpa [MulAut.mul_apply] using this
    have h2 : β⁻¹ (α (β e)) = α e := by
      rw [hab, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [← h2, h]
  have h2 := hcube e₀ he₀
  rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply] at h2
  have h3 : α (α e₀) = e₀ := by
    have := h1 e₀ he₀
    rw [this, ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  rw [h3] at h2
  exact h2

section DS3

variable {U : Type} [CommGroup U] [Finite U]

structure DS3 (J G₁ G₂ : Subgroup (MulAut U)) (W₁ W₂ : Subgroup U) (y₁ y₂ : MulAut U) :
    Prop where
  sup : G₁ ⊔ G₂ = J
  inf : G₁ ⊓ G₂ = ⊥
  comm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a
  card₁ : Nat.card ↥G₁ = 6
  card₂ : Nat.card ↥G₂ = 6
  nc₁ : ∃ a b : ↥G₁, a * b ≠ b * a
  nc₂ : ∃ a b : ↥G₂, a * b ≠ b * a
  Wsup : W₁ ⊔ W₂ = ⊤
  Winf : W₁ ⊓ W₂ = fixV J
  inv₁ : ∀ g ∈ J, ∀ w ∈ W₁, g w ∈ W₁
  inv₂ : ∀ g ∈ J, ∀ w ∈ W₂, g w ∈ W₂
  W₁eq : W₁ = commV G₁ ⊔ fixV J
  W₂eq : W₂ = commV G₂ ⊔ fixV J
  W₁card : Nat.card ↥W₁ = 4 * Nat.card ↥(fixV J)
  W₂card : Nat.card ↥W₂ = 4 * Nat.card ↥(fixV J)
  y₁mem : y₁ ∈ G₁
  y₂mem : y₂ ∈ G₂
  y₁ord : orderOf y₁ = 3
  y₂ord : orderOf y₂ = 3

namespace DS3

variable {J G₁ G₂ : Subgroup (MulAut U)} {W₁ W₂ : Subgroup U} {y₁ y₂ : MulAut U}

omit [Finite U] in
theorem symm (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) : DS3 J G₂ G₁ W₂ W₁ y₂ y₁ where
  sup := by rw [sup_comm]; exact h.sup
  inf := by rw [inf_comm]; exact h.inf
  comm := fun a ha b hb => (h.comm b hb a ha).symm
  card₁ := h.card₂
  card₂ := h.card₁
  nc₁ := h.nc₂
  nc₂ := h.nc₁
  Wsup := by rw [sup_comm]; exact h.Wsup
  Winf := by rw [inf_comm]; exact h.Winf
  inv₁ := h.inv₂
  inv₂ := h.inv₁
  W₁eq := h.W₂eq
  W₂eq := h.W₁eq
  W₁card := h.W₂card
  W₂card := h.W₁card
  y₁mem := h.y₂mem
  y₂mem := h.y₁mem
  y₁ord := h.y₂ord
  y₂ord := h.y₁ord

theorem struct₁ (hU2 : ∀ u : U, u * u = 1) (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) :
    (threePhi y₁).range ≤ W₁ ∧ Nat.card ↥(threePhi y₁).range = 4 ∧ (threePhi y₁).ker = W₂ :=
  ds3_structure hU2 h.sup h.comm h.Wsup h.Winf h.inv₁ h.inv₂ h.W₁eq h.W₂eq h.W₁card h.y₁mem
    h.y₁ord

omit [Finite U] in
theorem G₁_le (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) : G₁ ≤ J := h.sup ▸ le_sup_left

omit [Finite U] in
theorem G₂_le (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) : G₂ ≤ J := h.sup ▸ le_sup_right

theorem zpowers_normal₁ (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) :
    ∀ g ∈ J, g * y₁ * g⁻¹ ∈ Subgroup.zpowers y₁ := by
  intro g hg
  rw [← h.sup] at hg
  obtain ⟨a, ha, b, hb, rfl⟩ := S153L.comp_exists_mul h.comm hg
  have hby : b * y₁ * b⁻¹ = y₁ := by
    rw [mul_inv_eq_iff_eq_mul, h.comm y₁ h.y₁mem b hb]
  have e : a * b * y₁ * (a * b)⁻¹ = a * y₁ * a⁻¹ := by
    calc a * b * y₁ * (a * b)⁻¹ = a * (b * y₁ * b⁻¹) * a⁻¹ := by group
      _ = a * y₁ * a⁻¹ := by rw [hby]
  rw [e]
  have hx : a * y₁ * a⁻¹ ∈ G₁ := G₁.mul_mem (G₁.mul_mem ha h.y₁mem) (G₁.inv_mem ha)
  have hxo : orderOf (a * y₁ * a⁻¹) = 3 := by rw [orderOf_conj', h.y₁ord]
  have hQ := eq_of_card_three_of_le h.card₁
    ((Subgroup.zpowers_le).mpr hx) ((Subgroup.zpowers_le).mpr h.y₁mem)
    (card_zpowers_three hxo) (card_zpowers_three h.y₁ord)
  rw [← hQ]
  exact Subgroup.mem_zpowers _

theorem conj_cases (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) {g : MulAut U}
    (hg : g ∈ Subgroup.normalizer (J : Set (MulAut U))) :
    (g * y₁ * g⁻¹ = y₁ ∨ g * y₁ * g⁻¹ = y₁⁻¹) ∨ (g * y₁ * g⁻¹ = y₂ ∨ g * y₁ * g⁻¹ = y₂⁻¹) := by
  set x := g * y₁ * g⁻¹ with hxdef
  have hxJ : x ∈ J := (Subgroup.mem_normalizer_iff.mp hg y₁).mp (h.G₁_le h.y₁mem)
  have hxo : orderOf x = 3 := by rw [hxdef, orderOf_conj', h.y₁ord]
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hxo; omega
  have hQn : ∀ k ∈ J, ∀ q ∈ Subgroup.zpowers x, k * q * k⁻¹ ∈ Subgroup.zpowers x := by
    intro k hk q hq
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    rw [← conj_zpow]
    refine Subgroup.zpow_mem _ ?_ n
    have hk' : g⁻¹ * k * g ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
      simpa using this
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (h.zpowers_normal₁ _ hk')
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have e : k * x * k⁻¹ = g * ((g⁻¹ * k * g) * y₁ * (g⁻¹ * k * g)⁻¹) * g⁻¹ := by
      rw [hxdef]; group
    rw [e, ← hm, hxdef, conj_zpow]
  have hQ3 : SzN17.IsNormalThree (G₁ ⊔ G₂) (Subgroup.zpowers x) :=
    ⟨by rw [h.sup]; exact (Subgroup.zpowers_le).mpr hxJ, fun k hk q hq => hQn k (h.sup ▸ hk) q hq,
      card_zpowers_three hxo⟩
  rcases SzN17.normalThree_le_factor h.comm h.inf (SzN17.centerTrivial_of_card_six h.card₁ h.nc₁)
      hQ3 with h1 | h2
  · left
    have hQ := eq_of_card_three_of_le h.card₁ h1 ((Subgroup.zpowers_le).mpr h.y₁mem)
      (card_zpowers_three hxo) (card_zpowers_three h.y₁ord)
    exact eq_or_eq_inv_of_mem_zpowers h.y₁ord (hQ ▸ Subgroup.mem_zpowers x) hx1
  · right
    have hQ := eq_of_card_three_of_le h.card₂ h2 ((Subgroup.zpowers_le).mpr h.y₂mem)
      (card_zpowers_three hxo) (card_zpowers_three h.y₂ord)
    exact eq_or_eq_inv_of_mem_zpowers h.y₂ord (hQ ▸ Subgroup.mem_zpowers x) hx1

theorem trivial_W₂ (hU2 : ∀ u : U, u * u = 1) (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) {s : MulAut U}
    (hs : s ∈ G₁) (hs2 : ∃ k : ℕ, s ^ 2 ^ k = 1) : ∀ w ∈ W₂, s w = w := by
  obtain ⟨hEW, hcard, hker⟩ := h.symm.struct₁ hU2
  have hy3 : y₂ ^ 3 = 1 := by rw [← h.y₂ord]; exact pow_orderOf_eq_one y₂
  have hsy : y₂ * s = s * y₂ := (h.comm s hs y₂ h.y₂mem).symm
  have hsJ : s ∈ J := h.G₁_le hs
  have hsE : ∀ e ∈ (threePhi y₂).range, s e ∈ (threePhi y₂).range := by
    intro e he
    refine three_range_apply hU2 (Or.inl ?_) he
    rw [← hsy, mul_inv_cancel_right]
  have hyE : ∀ e ∈ (threePhi y₂).range, y₂ e ∈ (threePhi y₂).range :=
    fun e he => three_range_apply_self he
  have hy1 : ∃ e ∈ (threePhi y₂).range, y₂ e ≠ e := by
    have h4 : (threePhi y₂).range ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hcard
      omega
    obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h4
    refine ⟨e, he, fun hfix => he1 ?_⟩
    exact Subtype.ext (three_range_fix hU2 hy3 he hfix)
  have hsE1 : ∀ e ∈ (threePhi y₂).range, s e = e :=
    two_trivial_of_comm hcard (fun e _ => hU2 e) hyE hsE h.y₂ord hs2 hy1 hsy
  intro w hw
  obtain ⟨h1, h2⟩ := three_decomp hU2 hy3 w
  have hc : w * y₂ w * y₂ (y₂ w) ∈ fixV J := by
    rw [← h.Winf]
    refine ⟨?_, ?_⟩
    · rw [← hker]; exact h2
    · exact W₂.mul_mem (W₂.mul_mem hw (h.inv₂ y₂ (h.G₂_le h.y₂mem) w hw))
        (h.inv₂ y₂ (h.G₂_le h.y₂mem) _ (h.inv₂ y₂ (h.G₂_le h.y₂mem) w hw))
  rw [← h1, map_mul, hsE1 _ ⟨y₂ w, rfl⟩, hc s hsJ]

omit [Finite U] in
theorem y₁_ne_one (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) : y₁ ≠ 1 := fun h1 => by
  have h3 := h.y₁ord
  rw [h1, orderOf_one] at h3
  omega

omit [Finite U] in
theorem y₁_ne_y₂ (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) : y₁ ≠ y₂ ∧ y₁ ≠ y₂⁻¹ := by
  have hG : ∀ x ∈ G₂, x = y₁ → False := fun x hx hxy => by
    have hm : y₁ ∈ G₁ ⊓ G₂ := ⟨h.y₁mem, hxy ▸ hx⟩
    rw [h.inf, Subgroup.mem_bot] at hm
    exact h.y₁_ne_one hm
  exact ⟨fun e => hG y₂ h.y₂mem e.symm, fun e => hG y₂⁻¹ (G₂.inv_mem h.y₂mem) e.symm⟩

theorem swap_consistent (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) {g : MulAut U}
    (hg : g ∈ Subgroup.normalizer (J : Set (MulAut U)))
    (h1 : g * y₁ * g⁻¹ = y₂ ∨ g * y₁ * g⁻¹ = y₂⁻¹) :
    g * y₂ * g⁻¹ = y₁ ∨ g * y₂ * g⁻¹ = y₁⁻¹ := by
  rcases h.symm.conj_cases hg with h2 | h2
  · exfalso
    obtain ⟨hne1, hne2⟩ := h.y₁_ne_y₂
    have hinj : ∀ a b : MulAut U, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b hab => by
      have := congrArg (fun x => g⁻¹ * x * g) hab
      simpa [mul_assoc] using this
    have hinv : ∀ a : MulAut U, g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := fun a => by group
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact hne1 (hinj _ _ (h1.trans h2.symm))
    · exact hne2 (hinj _ _ (by rw [h1, hinv, h2, inv_inv]))
    · exact hne2 (hinj _ _ (by rw [h1, hinv, h2]))
    · exact hne1 (hinj _ _ (h1.trans h2.symm))
  · exact h2

@[expose] def FixY (y₁ g : MulAut U) : Prop := g * y₁ * g⁻¹ = y₁ ∨ g * y₁ * g⁻¹ = y₁⁻¹

omit [Finite U] in
theorem fixY_mul {a b : MulAut U} (ha : FixY y₁ a) (hb : FixY y₁ b) : FixY y₁ (a * b) := by
  have e : a * b * y₁ * (a * b)⁻¹ = a * (b * y₁ * b⁻¹) * a⁻¹ := by group
  have hinv : a * y₁⁻¹ * a⁻¹ = (a * y₁ * a⁻¹)⁻¹ := by group
  unfold FixY at ha hb ⊢
  rw [e]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [hb]
  · exact Or.inl ha
  · rw [hinv, ha]; exact Or.inr rfl
  · exact Or.inr ha
  · rw [hinv, ha, inv_inv]; exact Or.inl rfl

omit [Finite U] in
theorem fixY_pow {g : MulAut U} (hg : FixY y₁ g) (n : ℕ) : FixY y₁ (g ^ n) := by
  induction n with
  | zero => simp [FixY]
  | succ n ih => rw [pow_succ]; exact fixY_mul ih hg

omit [Finite U] in
theorem fixY_inv {g : MulAut U} (hg : FixY y₁ g) : FixY y₁ g⁻¹ := by
  unfold FixY at hg ⊢
  rw [inv_inv]
  rcases hg with h | h
  · left
    calc g⁻¹ * y₁ * g = g⁻¹ * (g * y₁ * g⁻¹) * g := by rw [h]
      _ = y₁ := by group
  · right
    calc g⁻¹ * y₁ * g = g⁻¹ * (y₁⁻¹)⁻¹ * g := by rw [inv_inv]
      _ = g⁻¹ * (g * y₁ * g⁻¹)⁻¹ * g := by rw [h]
      _ = y₁⁻¹ := by group

theorem fixY_sq (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) {g : MulAut U}
    (hg : g ∈ Subgroup.normalizer (J : Set (MulAut U))) : FixY y₁ (g * g) := by
  rcases h.conj_cases hg with h1 | h1
  · exact fixY_mul h1 h1
  · have h2 := h.swap_consistent hg h1
    have e : g * g * y₁ * (g * g)⁻¹ = g * (g * y₁ * g⁻¹) * g⁻¹ := by group
    have hinv : g * y₂⁻¹ * g⁻¹ = (g * y₂ * g⁻¹)⁻¹ := by group
    unfold FixY
    rw [e]
    rcases h1 with h1 | h1 <;> rw [h1]
    · exact h2
    · rw [hinv]
      rcases h2 with h2 | h2 <;> rw [h2]
      · exact Or.inr rfl
      · rw [inv_inv]; exact Or.inl rfl

theorem fixY_of_odd (h : DS3 J G₁ G₂ W₁ W₂ y₁ y₂) {g : MulAut U}
    (hg : g ∈ Subgroup.normalizer (J : Set (MulAut U))) (hodd : Odd (orderOf g)) :
    FixY y₁ g := by
  obtain ⟨j, hj⟩ := hodd
  have hsq := fixY_pow (h.fixY_sq hg) (j + 1)
  have e : (g * g) ^ (j + 1) = g := by
    rw [← pow_two, ← pow_mul, show 2 * (j + 1) = orderOf g + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rwa [e] at hsq

end DS3

end DS3

end CFSG.Quasithin.H13.A5
