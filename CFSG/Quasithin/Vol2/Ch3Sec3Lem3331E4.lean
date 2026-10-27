module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3331S

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Par32 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

namespace Lem3331E4


section Lift

variable {H : Type*} [Group H]

theorem val_add_mod4 : ∀ i j : ZMod 4, (i + j).val % 4 = (i.val + j.val) % 4 := by decide

theorem val_sub_mod4 : ∀ i j : ZMod 4, (j - i).val % 4 = (3 * i.val + j.val) % 4 := by decide

theorem val_add_mod2 : ∀ i j : ZMod 2, (i + j).val % 2 = (i.val + j.val) % 2 := by decide

theorem pow_congr_mod {a : H} {n : ℕ} (ha : a ^ n = 1) {k m : ℕ} (h : k % n = m % n) :
    a ^ k = a ^ m := by
  rw [pow_eq_pow_mod k ha, pow_eq_pow_mod m ha, h]

theorem pow_mul_eq {a b : H} (ha : a ^ 4 = 1) (hb : b * b = 1) (hab : b * a * b = a⁻¹) (n : ℕ) :
    a ^ n * b = b * a ^ (3 * n) := by
  have h1 : a * b = b * a ^ 3 := by
    have e : a⁻¹ = a ^ 3 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact ha
    calc a * b = (b * b) * a * b := by rw [hb, one_mul]
      _ = b * (b * a * b) := by group
      _ = b * a ^ 3 := by rw [hab, e]
  induction n with
  | zero => simp
  | succ n ih =>
    calc a ^ (n + 1) * b = a ^ n * (a * b) := by rw [pow_succ, mul_assoc]
      _ = (a ^ n * b) * a ^ 3 := by rw [h1, mul_assoc]
      _ = b * a ^ (3 * n) * a ^ 3 := by rw [ih]
      _ = b * a ^ (3 * (n + 1)) := by rw [mul_assoc, ← pow_add]; ring_nf

@[expose] def d8Lift (a b : H) (ha : a ^ 4 = 1) (hb : b * b = 1) (hab : b * a * b = a⁻¹) :
    DihedralGroup 4 →* H where
  toFun x := match x with
    | .r i => a ^ i.val
    | .sr i => b * a ^ i.val
  map_one' := by
    show a ^ (0 : ZMod 4).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    rintro (i | i) (j | j)
    · show a ^ (i + j).val = a ^ i.val * a ^ j.val
      rw [← pow_add]
      exact pow_congr_mod ha (val_add_mod4 i j)
    · show b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
      rw [← mul_assoc, pow_mul_eq ha hb hab, mul_assoc, ← pow_add]
      exact congrArg (b * ·) (pow_congr_mod ha (val_sub_mod4 i j))
    · show b * a ^ (i + j).val = b * a ^ i.val * a ^ j.val
      rw [mul_assoc, ← pow_add]
      exact congrArg (b * ·) (pow_congr_mod ha (val_add_mod4 i j))
    · show a ^ (j - i).val = b * a ^ i.val * (b * a ^ j.val)
      rw [mul_assoc, ← mul_assoc (a ^ i.val), pow_mul_eq ha hb hab, ← mul_assoc, ← mul_assoc,
        hb, one_mul, ← pow_add]
      exact pow_congr_mod ha (val_sub_mod4 i j)

@[expose] def z2Lift (e : H) (he : e * e = 1) : Multiplicative (ZMod 2) →* H where
  toFun x := e ^ (Multiplicative.toAdd x).val
  map_one' := by
    show e ^ (0 : ZMod 2).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' x y := by
    show e ^ (Multiplicative.toAdd x + Multiplicative.toAdd y).val =
      e ^ (Multiplicative.toAdd x).val * e ^ (Multiplicative.toAdd y).val
    rw [← pow_add]
    exact pow_congr_mod (n := 2) (by rw [sq]; exact he) (val_add_mod2 _ _)

end Lift

section Recog

variable {G : Type} [Group G]

theorem eq_one_or_of_mem_zpowers {z x : G} (hz : z * z = 1) (hx : x ∈ Subgroup.zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem card_zpowers_le_two {z : G} (hz : z * z = 1) : Nat.card (Subgroup.zpowers z) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact hz)

theorem card_sup_le_mul [Finite G] {H K : Subgroup G} (hK : K ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card ↥(H ⊔ K) ≤ Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun x =>
    ⟨(x.1 : G) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hK).mp hy
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod] at this

theorem eq_one_of_mul_eq_one {z z' e₁ e₂ F₁ F₂ E₁ E₂ : G} (hz : z ≠ 1)
    (hz' : z' ∉ Subgroup.zpowers z) (he₁ : e₁ ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers z')
    (he₂ : e₂ ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers z' ⊔ Subgroup.zpowers e₁)
    (hF₁ : F₁ = 1 ∨ F₁ = z) (hF₂ : F₂ = 1 ∨ F₂ = z') (hE₁ : E₁ = 1 ∨ E₁ = e₁)
    (hE₂ : E₂ = 1 ∨ E₂ = e₂) (h : F₁ * (F₂ * (E₁ * E₂)) = 1) :
    F₁ = 1 ∧ F₂ = 1 ∧ E₁ = 1 ∧ E₂ = 1 := by
  set Z₁ := Subgroup.zpowers z
  set Z₂ := Z₁ ⊔ Subgroup.zpowers z'
  set Z₃ := Z₂ ⊔ Subgroup.zpowers e₁
  have hF₁Z : F₁ ∈ Z₁ := by
    rcases hF₁ with rfl | rfl
    · exact Z₁.one_mem
    · exact Subgroup.mem_zpowers _
  have hF₂Z : F₂ ∈ Subgroup.zpowers z' := by
    rcases hF₂ with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hE₁Z : E₁ ∈ Subgroup.zpowers e₁ := by
    rcases hE₁ with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  have hE₂ : E₂ = 1 := by
    rcases hE₂ with h2 | h2
    · exact h2
    · exfalso
      apply he₂
      rw [h2] at h
      have e : e₂ = (F₁ * F₂ * E₁)⁻¹ :=
        eq_inv_of_mul_eq_one_right (by simpa only [mul_assoc] using h)
      rw [e]
      exact Z₃.inv_mem (Z₃.mul_mem (Z₃.mul_mem
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hF₁Z))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hF₂Z))) (Subgroup.mem_sup_right hE₁Z))
  subst hE₂
  rw [mul_one] at h
  have hE₁ : E₁ = 1 := by
    rcases hE₁ with h2 | h2
    · exact h2
    · exfalso
      apply he₁
      rw [h2] at h
      have e : e₁ = (F₁ * F₂)⁻¹ :=
        eq_inv_of_mul_eq_one_right (by simpa only [mul_assoc] using h)
      rw [e]
      exact Z₂.inv_mem (Z₂.mul_mem (Subgroup.mem_sup_left hF₁Z) (Subgroup.mem_sup_right hF₂Z))
  subst hE₁
  rw [mul_one] at h
  have hF₂ : F₂ = 1 := by
    rcases hF₂ with h2 | h2
    · exact h2
    · exfalso
      apply hz'
      rw [h2] at h
      have e : z' = F₁⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [e]
      exact Z₁.inv_mem hF₁Z
  subst hF₂
  rw [mul_one] at h
  exact ⟨h, rfl, rfl, rfl⟩

@[expose] def IsCen (x : D8D8E4) : Prop :=
  (x.1 = 1 ∨ x.1 = DihedralGroup.r 2) ∧ (x.2.1 = 1 ∨ x.2.1 = DihedralGroup.r 2)

instance : DecidablePred IsCen := fun x => by unfold IsCen; infer_instance

theorem cen_witness : ∀ x : D8D8E4, x = 1 ∨ IsCen x ∨
    ∃ g ∈ ([(DihedralGroup.r 1, 1, 1), (DihedralGroup.sr 0, 1, 1), (1, DihedralGroup.r 1, 1),
      (1, DihedralGroup.sr 0, 1)] : List D8D8E4), ⁅x, g⁆ ≠ 1 ∧ IsCen ⁅x, g⁆ := by
  decide +kernel

theorem commute_d8Lift {H : Type*} [Group H] {a b x : H} (ha : a ^ 4 = 1) (hb : b * b = 1)
    (hab : b * a * b = a⁻¹) (h₁ : Commute a x) (h₂ : Commute b x) (m : DihedralGroup 4) :
    Commute (d8Lift a b ha hb hab m) x := by
  rcases m with i | i
  · exact h₁.pow_left _
  · exact h₂.mul_left (h₁.pow_left _)

theorem nonempty_mulEquiv [Finite G] {S : Subgroup G} {ρ₁ σ₁ ρ₂ σ₂ e₁ e₂ : G}
    (hρ₁S : ρ₁ ∈ S) (hσ₁S : σ₁ ∈ S) (hρ₂S : ρ₂ ∈ S) (hσ₂S : σ₂ ∈ S) (he₁S : e₁ ∈ S)
    (he₂S : e₂ ∈ S)
    (hρ₁ : ρ₁ ^ 4 = 1) (hσ₁ : σ₁ * σ₁ = 1) (hc₁ : σ₁ * ρ₁ * σ₁ = ρ₁⁻¹)
    (hρ₂ : ρ₂ ^ 4 = 1) (hσ₂ : σ₂ * σ₂ = 1) (hc₂ : σ₂ * ρ₂ * σ₂ = ρ₂⁻¹)
    (he₁ : e₁ * e₁ = 1) (he₂ : e₂ * e₂ = 1) (he₁₂ : Commute e₁ e₂)
    (hρ₁ρ₂ : Commute ρ₁ ρ₂) (hρ₁σ₂ : Commute ρ₁ σ₂) (hσ₁ρ₂ : Commute σ₁ ρ₂)
    (hσ₁σ₂ : Commute σ₁ σ₂) (hρ₁e₁ : Commute ρ₁ e₁) (hρ₁e₂ : Commute ρ₁ e₂)
    (hσ₁e₁ : Commute σ₁ e₁) (hσ₁e₂ : Commute σ₁ e₂) (hρ₂e₁ : Commute ρ₂ e₁)
    (hρ₂e₂ : Commute ρ₂ e₂) (hσ₂e₁ : Commute σ₂ e₁) (hσ₂e₂ : Commute σ₂ e₂)
    (hz : ρ₁ ^ 2 ≠ 1) (hz' : ρ₂ ^ 2 ∉ Subgroup.zpowers (ρ₁ ^ 2))
    (hi₁ : e₁ ∉ Subgroup.zpowers (ρ₁ ^ 2) ⊔ Subgroup.zpowers (ρ₂ ^ 2))
    (hi₂ : e₂ ∉ Subgroup.zpowers (ρ₁ ^ 2) ⊔ Subgroup.zpowers (ρ₂ ^ 2) ⊔ Subgroup.zpowers e₁)
    (hcard : Nat.card S ≤ 256) : Nonempty (↥S ≃* D8D8E4) := by
  set f₁ := d8Lift ρ₁ σ₁ hρ₁ hσ₁ hc₁ with hf₁
  set f₂ := d8Lift ρ₂ σ₂ hρ₂ hσ₂ hc₂ with hf₂
  set g₁ := z2Lift e₁ he₁ with hg₁
  set g₂ := z2Lift e₂ he₂ with hg₂
  have hg₁g₂ : ∀ m n, Commute (g₁ m) (g₂ n) := fun m n => (he₁₂.pow_left _).pow_right _
  set fE := g₁.noncommCoprod g₂ hg₁g₂ with hfE
  have hf₂E : ∀ m n, Commute (f₂ m) (fE n) := by
    intro m n
    show Commute (f₂ m) (g₁ n.1 * g₂ n.2)
    exact (commute_d8Lift hρ₂ hσ₂ hc₂ (hρ₂e₁.pow_right _) (hσ₂e₁.pow_right _) m).mul_right
      (commute_d8Lift hρ₂ hσ₂ hc₂ (hρ₂e₂.pow_right _) (hσ₂e₂.pow_right _) m)
  set f₂₃ := f₂.noncommCoprod fE hf₂E with hf₂₃
  have hf₁₂₃ : ∀ m n, Commute (f₁ m) (f₂₃ n) := by
    intro m n
    show Commute (f₁ m) (f₂ n.1 * (g₁ n.2.1 * g₂ n.2.2))
    have h1 : Commute ρ₁ (f₂ n.1) :=
      (commute_d8Lift hρ₂ hσ₂ hc₂ hρ₁ρ₂.symm hρ₁σ₂.symm n.1).symm
    have h2 : Commute σ₁ (f₂ n.1) :=
      (commute_d8Lift hρ₂ hσ₂ hc₂ hσ₁ρ₂.symm hσ₁σ₂.symm n.1).symm
    exact (commute_d8Lift hρ₁ hσ₁ hc₁ h1 h2 m).mul_right
      ((commute_d8Lift hρ₁ hσ₁ hc₁ (hρ₁e₁.pow_right _) (hσ₁e₁.pow_right _) m).mul_right
        (commute_d8Lift hρ₁ hσ₁ hc₁ (hρ₁e₂.pow_right _) (hσ₁e₂.pow_right _) m))
  set φ := f₁.noncommCoprod f₂₃ hf₁₂₃ with hφ
  have hφapp : ∀ x : D8D8E4, φ x = f₁ x.1 * (f₂ x.2.1 * (g₁ x.2.2.1 * g₂ x.2.2.2)) :=
    fun x => rfl
  have hd8S : ∀ {a b : G} (ha : a ^ 4 = 1) (hb : b * b = 1) (hab : b * a * b = a⁻¹), a ∈ S →
      b ∈ S → ∀ m, d8Lift a b ha hb hab m ∈ S := by
    intro a b ha hb hab haS hbS m
    rcases m with i | i
    · exact S.pow_mem haS _
    · exact S.mul_mem hbS (S.pow_mem haS _)
  have hmem : ∀ x, φ x ∈ S := by
    intro x
    rw [hφapp]
    exact S.mul_mem (hd8S hρ₁ hσ₁ hc₁ hρ₁S hσ₁S _) (S.mul_mem (hd8S hρ₂ hσ₂ hc₂ hρ₂S hσ₂S _)
      (S.mul_mem (S.pow_mem he₁S _) (S.pow_mem he₂S _)))
  have hz2 : ∀ {e : G} (m : Multiplicative (ZMod 2)),
      e ^ (Multiplicative.toAdd m).val = 1 ∨ e ^ (Multiplicative.toAdd m).val = e := by
    intro e m
    have h2 : (Multiplicative.toAdd m).val < 2 := ZMod.val_lt _
    interval_cases (Multiplicative.toAdd m).val
    · left
      exact pow_zero e
    · right
      exact pow_one e
  have he₁1 : e₁ ≠ 1 := fun h1 => hi₁ (h1 ▸ Subgroup.one_mem _)
  have he₂1 : e₂ ≠ 1 := fun h1 => hi₂ (h1 ▸ Subgroup.one_mem _)
  have hz'1 : ρ₂ ^ 2 ≠ 1 := fun h1 => hz' (h1 ▸ Subgroup.one_mem _)
  have hr2 : ∀ {a b : G} (ha : a ^ 4 = 1) (hb : b * b = 1) (hab : b * a * b = a⁻¹),
      d8Lift a b ha hb hab (DihedralGroup.r 2) = a ^ 2 := fun _ _ _ => rfl
  have hcen : ∀ c : D8D8E4, IsCen c → φ c = 1 → c = 1 := by
    rintro ⟨c₁, c₂, a, b⟩ ⟨h1, h2⟩ hc
    dsimp only at h1 h2
    have hF₁ : f₁ c₁ = 1 ∨ f₁ c₁ = ρ₁ ^ 2 := by
      rcases h1 with h1 | h1 <;> rw [h1]
      · exact Or.inl (map_one _)
      · exact Or.inr (hr2 _ _ _)
    have hF₂ : f₂ c₂ = 1 ∨ f₂ c₂ = ρ₂ ^ 2 := by
      rcases h2 with h2 | h2 <;> rw [h2]
      · exact Or.inl (map_one _)
      · exact Or.inr (hr2 _ _ _)
    rw [hφapp] at hc
    obtain ⟨k₁, k₂, k₃, k₄⟩ :=
      eq_one_of_mul_eq_one hz hz' hi₁ hi₂ hF₁ hF₂ (hz2 a) (hz2 b) hc
    have hc₁ : c₁ = 1 := by
      rcases h1 with h1 | h1
      · exact h1
      · exfalso
        rw [h1, hr2] at k₁
        exact hz k₁
    have hc₂ : c₂ = 1 := by
      rcases h2 with h2 | h2
      · exact h2
      · exfalso
        rw [h2, hr2] at k₂
        exact hz'1 k₂
    have hval : ∀ {e : G}, e ≠ 1 → ∀ m : Multiplicative (ZMod 2),
        e ^ (Multiplicative.toAdd m).val = 1 → m = 1 := by
      intro e he m hm
      have h2 : (Multiplicative.toAdd m).val < 2 := ZMod.val_lt _
      have h0 : (Multiplicative.toAdd m).val = 0 := by
        by_contra h0
        have h1 : (Multiplicative.toAdd m).val = 1 := by omega
        rw [h1, pow_one] at hm
        exact he hm
      exact Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).mp h0)
    have ha : a = 1 := hval he₁1 a k₃
    have hb : b = 1 := hval he₂1 b k₄
    rw [hc₁, hc₂, ha, hb]
    rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rcases cen_witness x with h | h | ⟨g, -, hg1, hg⟩
    · exact h
    · exact hcen x h hx
    · exfalso
      apply hg1
      apply hcen _ hg
      rw [map_commutatorElement, hx, commutatorElement_one_left]
  let φS : D8D8E4 →* ↥S := φ.codRestrict S hmem
  have hinjS : Function.Injective φS := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  have h256 : Nat.card D8D8E4 = 256 := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_prod, DihedralGroup.card, Fintype.card_multiplicative, ZMod.card]
  have hbij : Function.Bijective φS := (Nat.bijective_iff_injective_and_card φS).mpr
    ⟨hinjS, le_antisymm (Nat.card_le_card_of_injective φS hinjS) (h256 ▸ hcard)⟩
  exact ⟨(MulEquiv.ofBijective φS hbij).symm⟩

end Recog


section Tools

variable {G : Type} [Group G]

theorem zpowers_le_normalizer_of_commute {a b : G} (h : Commute a b) :
    Subgroup.zpowers b ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  have hb : b ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (h.zpow_left n).eq
  exact Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hb)

theorem zpowers_le_normalizer_sup {z z' e : G} (h₁ : Commute e z) (h₂ : Commute e z') :
    Subgroup.zpowers e ≤
      Subgroup.normalizer ((Subgroup.zpowers z ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) := by
  have hle : Subgroup.zpowers z ⊔ Subgroup.zpowers z' ≤ Subgroup.centralizer ({e} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h₁.eq.symm))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h₂.eq.symm))
  have he : e ∈ Subgroup.centralizer
      ((Subgroup.zpowers z ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun w hw => Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  exact Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ he)

theorem exists_e [Finite G] {W : Subgroup G} {z z' : G} (hW : 16 ≤ Nat.card W)
    (hzz : z * z = 1) (hz'z' : z' * z' = 1) (hzz' : Commute z z')
    (hWz : ∀ w ∈ W, Commute w z) (hWz' : ∀ w ∈ W, Commute w z')
    (hWe : ∀ w ∈ W, w * w = 1) :
    ∃ e₁ ∈ W, ∃ e₂ ∈ W, e₁ ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers z' ∧
      e₂ ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers z' ⊔ Subgroup.zpowers e₁ := by
  have hZ₂ : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers z') ≤ 4 := by
    have h1 := card_sup_le_mul (zpowers_le_normalizer_of_commute hzz')
    have h2 := card_zpowers_le_two hzz
    have h3 := card_zpowers_le_two hz'z'
    nlinarith
  obtain ⟨e₁, he₁W, he₁Z⟩ : ∃ e ∈ W, e ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers z' := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun x hx => hcon x hx :
      W ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers z')
    omega
  have hZ₃ : Nat.card ↥(Subgroup.zpowers z ⊔ Subgroup.zpowers z' ⊔ Subgroup.zpowers e₁) ≤ 8 := by
    have h1 := card_sup_le_mul (zpowers_le_normalizer_sup (hWz e₁ he₁W) (hWz' e₁ he₁W))
    have h2 := card_zpowers_le_two (hWe e₁ he₁W)
    nlinarith
  obtain ⟨e₂, he₂W, he₂Z⟩ : ∃ e ∈ W,
      e ∉ Subgroup.zpowers z ⊔ Subgroup.zpowers z' ⊔ Subgroup.zpowers e₁ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun x hx => hcon x hx :
      W ≤ Subgroup.zpowers z ⊔ Subgroup.zpowers z' ⊔ Subgroup.zpowers e₁)
    omega
  exact ⟨e₁, he₁W, e₂, he₂W, he₁Z, he₂Z⟩

theorem card_ge_32 [Finite G] {U V Zl : Subgroup G} (hUV : U ≤ V)
    (hU : Nat.card U = 16 * Nat.card Zl) (hZl : Zl = ⊥ → ∃ z ∈ V, z ∉ U) :
    32 ≤ Nat.card V := by
  by_cases hZ : Zl = ⊥
  · obtain ⟨z, hzV, hzU⟩ := hZl hZ
    rw [hZ, Subgroup.card_bot, mul_one] at hU
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hUV
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [mul_one] at hk
      exact hzU (by rw [Subgroup.eq_of_le_of_card_ge hUV hk.le]; exact hzV)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact (Nat.card_pos (α := V)).ne' hk
    rw [hk, hU]
    have : 2 ≤ k := by omega
    omega
  · have h2 : 1 < Nat.card Zl := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
    have h3 : Nat.card U ≤ Nat.card V := Subgroup.card_le_of_le hUV
    omega

theorem card_sup_le_64 [Finite G] {U C Zl : Subgroup G} {z : G}
    (hCU : C ≤ Subgroup.normalizer (U : Set G)) (hU : Nat.card U = 16 * Nat.card Zl)
    (hC : Nat.card C = 4) (hZlU : Zl ≤ U) (hZl : ∀ y ∈ Zl, y = 1 ∨ y = z) (hzC : z ∈ C)
    (hz1 : z ≠ 1) (hzz : z * z = 1) : Nat.card ↥(U ⊔ C) ≤ 64 := by
  by_cases hZ : Zl = ⊥
  · rw [hZ, Subgroup.card_bot, mul_one] at hU
    have := card_sup_le_mul hCU
    rw [hU, hC] at this
    omega
  obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
  have hzZl : z ∈ Zl := by
    rcases hZl y y.2 with h1 | h1
    · exact absurd (Subtype.ext h1) hy1
    · exact h1 ▸ y.2
  have hZl2 : Nat.card Zl = 2 := by
    have hle : Zl ≤ Subgroup.zpowers z := fun x hx => by
      rcases hZl x hx with h1 | h1
      · rw [h1]
        exact Subgroup.one_mem _
      · rw [h1]
        exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_zpowers_le_two hzz
    have h3 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
    omega
  rw [hZl2] at hU
  have hzU : z ∈ U := hZlU hzZl
  have hzpU : Subgroup.zpowers z ≤ U := Subgroup.zpowers_le.mpr hzU
  have horder : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hidx : ((Subgroup.zpowers z).subgroupOf C).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers z) (K := C)
    rw [inf_of_le_left (Subgroup.zpowers_le.mpr hzC), horder, hC] at h1
    show (Subgroup.zpowers z).relIndex C = 2
    omega
  have hle := Lem3331S.card_le_two_mul (A := U) (Z := U ⊔ C) (fun x hx y hy hxU hyU => by
    obtain ⟨u₁, hu₁, k₁, hk₁, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCU).mp hx
    obtain ⟨u₂, hu₂, k₂, hk₂, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hCU).mp hy
    have hk₁U : k₁ ∉ Subgroup.zpowers z := fun h1 => hxU (U.mul_mem hu₁ (hzpU h1))
    have hk₂U : k₂ ∉ Subgroup.zpowers z := fun h1 => hyU (U.mul_mem hu₂ (hzpU h1))
    have hk : k₁⁻¹ * k₂ ∈ Subgroup.zpowers z := by
      have h3 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨k₁, hk₁⟩ : ↥C)⁻¹)
        (b := ⟨k₂, hk₂⟩)).mpr (iff_of_false (fun h' => hk₁U (by
          have := Subgroup.mem_subgroupOf.mp h'
          simpa using this)) (fun h' => hk₂U (Subgroup.mem_subgroupOf.mp h')))
      exact Subgroup.mem_subgroupOf.mp h3
    have e : (u₁ * k₁)⁻¹ * (u₂ * k₂) = (k₁⁻¹ * (u₁⁻¹ * u₂) * k₁⁻¹⁻¹) * (k₁⁻¹ * k₂) := by group
    rw [e]
    refine U.mul_mem ?_ (hzpU hk)
    exact (Subgroup.mem_normalizer_iff.mp (hCU (C.inv_mem hk₁)) _).mp
      (U.mul_mem (U.inv_mem hu₁) hu₂))
  rw [hU] at hle
  omega

theorem card_blockU_eq {L : Subgroup G} (β : ↥(blockU L) →* Multiplicative A6Coc.Vec4)
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ L).subgroupOf (blockU L)) :
    Nat.card ↥(blockU L) = 16 * Nat.card ↥(blockZ L) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun x hx => hx.1 :
      blockZ L ≤ blockU L)).toEquiv] at h1
  rw [h1]
  congr 1
  rw [Nat.card_eq_fintype_card]
  rfl

theorem inv_mul_mem_of_relIndex_two {Q V Vd S : Subgroup G} {d : G} (hVQ : V ≤ Q) (hQS : Q ≤ S)
    (hVZ : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v) (hVd : ∀ w ∈ Vd, d * w * d⁻¹ ∈ V)
    (hdS : d ∈ Subgroup.normalizer (S : Set G)) (hidx : Q.relIndex S = 2) :
    ∀ x ∈ V, ∀ y ∈ V, x ∉ V ⊓ Subgroup.centralizer (Vd : Set G) →
      y ∉ V ⊓ Subgroup.centralizer (Vd : Set G) →
        x⁻¹ * y ∈ V ⊓ Subgroup.centralizer (Vd : Set G) := by
  have key : ∀ g, d * g * d⁻¹ ∈ Q → g ∈ Subgroup.centralizer (Vd : Set G) := by
    intro g hgQ
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := hVZ _ (hVd w hw) _ hgQ
    have e : d * (w * g) * d⁻¹ = d * (g * w) * d⁻¹ := by
      calc d * (w * g) * d⁻¹ = (d * w * d⁻¹) * (d * g * d⁻¹) := by group
        _ = (d * g * d⁻¹) * (d * w * d⁻¹) := h1
        _ = d * (g * w) * d⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  intro x hx y hy hxW hyW
  have hdx : d * x * d⁻¹ ∉ Q := fun h => hxW ⟨hx, key x h⟩
  have hdy : d * y * d⁻¹ ∉ Q := fun h => hyW ⟨hy, key y h⟩
  have hdxS : d * x * d⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hdS x).mp (hQS (hVQ hx))
  have hdyS : d * y * d⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hdS y).mp (hQS (hVQ hy))
  have h2 : (Q.subgroupOf S).index = 2 := hidx
  have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨d * x * d⁻¹, hdxS⟩ : ↥S)⁻¹)
    (b := ⟨d * y * d⁻¹, hdyS⟩)).mpr (iff_of_false (fun h' => hdx (by
      have h5 : (d * x * d⁻¹)⁻¹ ∈ Q := Subgroup.mem_subgroupOf.mp h'
      have h6 := Q.inv_mem h5
      rwa [inv_inv] at h6)) (fun h' => hdy (Subgroup.mem_subgroupOf.mp h')))
  have h4 : (d * x * d⁻¹)⁻¹ * (d * y * d⁻¹) ∈ Q := Subgroup.mem_subgroupOf.mp h3
  have e : (d * x * d⁻¹)⁻¹ * (d * y * d⁻¹) = d * (x⁻¹ * y) * d⁻¹ := by group
  rw [e] at h4
  exact ⟨V.mul_mem (V.inv_mem hx) hy, key _ h4⟩

theorem exists_rho₁ {Q C Vd : Subgroup G} [Finite G] {u z : G} (huQ : u ∈ Q)
    (huVd : u ∈ Subgroup.centralizer (Vd : Set G)) (huN : u ∈ Subgroup.normalizer (C : Set G))
    (hu2 : u ^ 2 ∈ C) (hCQ : C ≤ Q) (hCVd : C ≤ Subgroup.centralizer (Vd : Set G))
    (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a) (hCe : ∀ x ∈ C, x ^ 2 = 1)
    (hzC : z ∈ C) (hzu : z * u = u * z)
    (hCu : ∀ y ∈ C, y * u = u * y → y = 1 ∨ y = z) (hC4 : Nat.card C = 4) :
    ∃ c ∈ C, c ∉ Subgroup.zpowers z ∧ ∃ ρ₁ ∈ Q, ρ₁ ∈ Subgroup.centralizer (Vd : Set G) ∧
      ρ₁ ^ 2 = z ∧ c * ρ₁ * c = ρ₁⁻¹ := by
  have hzz : z * z = 1 := by rw [← sq]; exact hCe z hzC
  obtain ⟨c, hcC, hcz⟩ : ∃ c ∈ C, c ∉ Subgroup.zpowers z := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card C ≤ Nat.card (Subgroup.zpowers z) :=
      Subgroup.card_le_of_le (fun x hx => hcon x hx)
    have h2 := card_zpowers_le_two hzz
    omega
  have hcc : c * c = 1 := by rw [← sq]; exact hCe c hcC
  have hc1 : c ≠ 1 := fun h1 => hcz (h1 ▸ Subgroup.one_mem _)
  have hcz' : c ≠ z := fun h1 => hcz (h1 ▸ Subgroup.mem_zpowers _)
  have hucC : u * c * u⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp huN c).mp hcC
  have hu2C : u ^ 2 * c = c * u ^ 2 := hCab _ hu2 _ hcC
  have huc : u * c * u⁻¹ = c * z := by
    set y := c * (u * c * u⁻¹) with hy
    have hyC : y ∈ C := C.mul_mem hcC hucC
    have hyu : y * u = u * y := by
      have e1 : u * y * u⁻¹ = (u * c * u⁻¹) * (u ^ 2 * c * (u ^ 2)⁻¹) := by
        rw [hy]
        group
      have e2 : u ^ 2 * c * (u ^ 2)⁻¹ = c := by
        rw [hu2C]
        group
      rw [e2, hCab _ hucC _ hcC] at e1
      calc y * u = (u * y * u⁻¹) * u := by rw [e1]
        _ = u * y := by group
    rcases hCu y hyC hyu with h1 | h1
    · exfalso
      have h2 : u * c * u⁻¹ = c := by
        calc u * c * u⁻¹ = (c * c) * (u * c * u⁻¹) := by rw [hcc, one_mul]
          _ = c * y := by rw [hy]; group
          _ = c := by rw [h1, mul_one]
      have h3 : c * u = u * c := by
        calc c * u = (u * c * u⁻¹) * u := by rw [h2]
          _ = u * c := by group
      rcases hCu c hcC h3 with h4 | h4
      · exact hc1 h4
      · exact hcz' h4
    · calc u * c * u⁻¹ = (c * c) * (u * c * u⁻¹) := by rw [hcc, one_mul]
        _ = c * y := by rw [hy]; group
        _ = c * z := by rw [h1]
  have hu2' : u ^ 2 = 1 ∨ u ^ 2 = z := hCu _ hu2 (by group)
  refine ⟨c, hcC, hcz, ?_⟩
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  rcases hu2' with hu2' | hu2'
  ·
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hu2')
    refine ⟨c * u, Q.mul_mem (hCQ hcC) huQ, Subgroup.mul_mem _ (hCVd hcC) huVd, ?_, ?_⟩
    · calc (c * u) ^ 2 = c * (u * c * u⁻¹) * u ^ 2 := by rw [sq, sq]; group
        _ = z := by rw [huc, hu2', mul_one, ← mul_assoc, hcc, one_mul]
    · calc c * (c * u) * c = (c * c) * u * c := by group
        _ = u⁻¹ * c⁻¹ := by rw [hcc, one_mul, hui, hci]
        _ = (c * u)⁻¹ := by group
  ·
    refine ⟨u, huQ, huVd, hu2', ?_⟩
    have huc' : u * c = c * z * u := by
      calc u * c = (u * c * u⁻¹) * u := by group
        _ = c * z * u := by rw [huc]
    have hui : u⁻¹ = z * u := by
      rw [inv_eq_iff_mul_eq_one]
      calc u * (z * u) = (u * z) * u := by group
        _ = (z * u) * u := by rw [hzu]
        _ = z * u ^ 2 := by rw [sq, mul_assoc]
        _ = 1 := by rw [hu2', hzz]
    calc c * u * c = c * (u * c) := by group
      _ = c * (c * z * u) := by rw [huc']
      _ = (c * c) * z * u := by group
      _ = z * u := by rw [hcc, one_mul]
      _ = u⁻¹ := hui.symm

end Tools

theorem move_check : ∀ σ ∈ S6Syl.elemsS, σ ≠ 1 → ∃ x : A6Coc.Vec4,
    x + A6Coc.act σ x ≠ 0 := by
  decide +kernel

section Main

variable {G : Type} [Group G]

theorem exists_u [Finite G]
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hA6 : IsAltBlockType L 6) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {d : G}
    (hF : frattini ↥(qL L T) ≠ ⊥) (hFTC : frattini ↥(tC L T) = ⊥)
    (hVdC : CFSG.conjugate (vPlus L T) d ≤ Subgroup.centralizer (tC L T : Set G))
    (hQdec : qL L T = vPlus L T ⊔
      (qL L T ⊓ Subgroup.centralizer (CFSG.conjugate (vPlus L T) d : Set G)))
    (hTdec : T = T ⊓ L ⊔ qL L T ⊔ CFSG.conjugate (vPlus L T) d) :
    ∃ u ∈ qL L T, u ∈ Subgroup.centralizer (CFSG.conjugate (vPlus L T) d : Set G) ∧
      u ^ 2 ∈ tC L T ∧ ∀ y ∈ tC L T, y * u = u * y →
        y ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := qL L T with hQdef
  set V := vPlus L T with hVdef
  set C := tC L T with hCdef
  set Vd := CFSG.conjugate V d with hVddef
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hCT : C ≤ T := inf_le_left
  have hCe : IsElemAbelian 2 C := isElemAbelian_of_frattini_eq_bot (hT2.to_le hCT) hFTC
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => by
    have := hCe.1
    exact setLike_mul_comm ha hb
  have hCQ : C ≤ Q := h.tC_le_qL h38 h39 hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : V ≤ Q := hred.1.trans inf_le_left
  have hVZ : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v := fun v hv q hq =>
    (Subgroup.mem_centralizer_iff.mp ((hred.1.trans inf_le_right) hv) q hq).symm
  have hVe := hred.2.1
  have hΦ : (frattini ↥Q).map Q.subtype ≤ C := h.frattini_qL_le_tC h38 h39 hA6.1 hTL
  have hsq : ∀ x ∈ Q, x ^ 2 ∈ C := fun x hx => Lem3331.sq_mem_of_frattini_le hQ2 hΦ hx
  have hCN : T ≤ Subgroup.normalizer (C : Set G) := Hyp331.le_normalizer_tC hTL
  have hVN : V ≤ Subgroup.normalizer (C : Set G) := (hVQ.trans hQT).trans hCN
  have hx₀ : ∃ x ∈ Q, x ^ 2 ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hF (frattini_eq_bot_of_isElemAbelian (Lem3331.isElemAbelian_of_sq_eq_one hall))
  have hCVe : ∀ x ∈ C ⊔ V, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨c, hc, v, hv, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hVN).mp hx
    have hcv : Commute c v := (hVZ v hv c (hCQ hc)).symm
    rw [hcv.mul_pow, hCe.2 c hc, hVe.2 v hv, one_mul]
  have hCVQ : C ⊔ V ≤ Q := sup_le hCQ hVQ
  have hlt : ¬ Q ≤ C ⊔ V := fun hle => by
    obtain ⟨x, hx, hx2⟩ := hx₀
    exact hx2 (hCVe x (hle hx))
  obtain ⟨u, ⟨huQ, huVd⟩, huCV⟩ : ∃ u ∈ Q ⊓ Subgroup.centralizer (Vd : Set G), u ∉ C ⊔ V := by
    by_contra hcon
    push Not at hcon
    apply hlt
    rw [hQdec]
    exact sup_le le_sup_right fun x hx => hcon x hx
  have hidx2 : (C ⊔ V).relIndex Q = 2 := by
    have hU := h.blockU_le_vPlus h38 h39 hA6.1 hTL
    have h1 : (blockU L ⊔ C).relIndex Q ≤ 2 := h.relIndex_qL_le_two h38 h39 hA6 hTL
    have h2 : (C ⊔ V).relIndex Q ≤ (blockU L ⊔ C).relIndex Q := by
      rw [sup_comm C V]
      exact Subgroup.relIndex_le_of_le_left (sup_le_sup_right hU C)
        Subgroup.index_ne_zero_of_finite
    have h3 : (C ⊔ V).relIndex Q ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact hlt
    have h4 : (C ⊔ V).relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hQgen : Q = Subgroup.zpowers u ⊔ (C ⊔ V) := by
    have hle : Subgroup.zpowers u ⊔ (C ⊔ V) ≤ Q := sup_le (Subgroup.zpowers_le.mpr huQ) hCVQ
    refine le_antisymm (fun x hx => ?_) hle
    by_cases hxW : x ∈ C ⊔ V
    · exact Subgroup.mem_sup_right hxW
    · have h2 : ((C ⊔ V).subgroupOf Q).index = 2 := hidx2
      have h3 := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨u, huQ⟩ : ↥Q)⁻¹)
        (b := ⟨x, hx⟩)).mpr (iff_of_false (fun h' => huCV (by
          have := Subgroup.mem_subgroupOf.mp h'
          simpa using this)) (fun h' => hxW (Subgroup.mem_subgroupOf.mp h')))
      have h4 : u⁻¹ * x ∈ C ⊔ V := Subgroup.mem_subgroupOf.mp h3
      have h5 : x = u * (u⁻¹ * x) := by group
      rw [h5]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
        (Subgroup.mem_sup_right h4)
  refine ⟨u, huQ, huVd, hsq u huQ, fun c hcC hcu => ?_⟩
  have hcL : c ∈ Subgroup.centralizer (L : Set G) := (Subgroup.mem_inf.mp hcC).2
  have hle : T ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hTdec]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro t ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hcL t ht.2)
    · rw [hQgen]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (sup_le ?_ ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcu.symm
      · intro c' hc'
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hCab c' hc' c hcC
      · intro v hv
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hVZ v hv c (hCQ hcC)
    · intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (hVdC hw) c hcC).symm
  have hcT : c ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle ht))
  exact ⟨Subgroup.subset_closure ⟨⟨hCT hcC, hcT⟩, hCe.2 c hcC⟩, hcL⟩

theorem exists_v [Finite G] {T L : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6))
    (β : ↥(blockU L) →* Multiplicative A6Coc.Vec4) (hβs : Function.Surjective β)
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ (g : ↥(Subgroup.normalizer (L : Set G))) (u u' : ↥(blockU L)),
      (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β u') = A6Coc.act (ρ g) (Multiplicative.toAdd (β u)))
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ sylowS6) {w₀ : G} (hw₀T : w₀ ∈ T)
    (hw₀w₀ : w₀ * w₀ = 1) (hρw : ρ ⟨w₀, hTL hw₀T⟩ ≠ 1) :
    ∃ v ∈ blockU L, ∃ zU ∈ blockU L, zU = (v * w₀) ^ 2 ∧ zU ∉ blockZ L := by
  have hσ : ρ ⟨w₀, hTL hw₀T⟩ ∈ S6Syl.elemsS := by
    have := hρT w₀ hw₀T
    rw [S6Syl.sylowS6_eq] at this
    exact this
  obtain ⟨x, hx⟩ := move_check _ hσ hρw
  obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd x)
  have hwi : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀w₀
  let v₁ : ↥(blockU L) := ⟨w₀ * v * w₀⁻¹, Mod32.conj_mem_blockU (hTL hw₀T) v⟩
  have hβ1 : Multiplicative.toAdd (β v₁) = A6Coc.act (ρ ⟨w₀, hTL hw₀T⟩) x := by
    rw [hβe ⟨w₀, hTL hw₀T⟩ v v₁ rfl, hv, toAdd_ofAdd]
  refine ⟨v, v.2, ((v * v₁ : ↥(blockU L)) : G), (v * v₁).2, ?_, ?_⟩
  · show (v : G) * (w₀ * v * w₀⁻¹) = ((v : G) * w₀) ^ 2
    rw [hwi, sq]
    group
  · intro hz
    have h1 : v * v₁ ∈ β.ker := by
      rw [hβk]
      exact Subgroup.mem_subgroupOf.mpr hz
    have h2 : Multiplicative.toAdd (β (v * v₁)) = 0 := by
      rw [MonoidHom.mem_ker.mp h1]
      rfl
    rw [map_mul, toAdd_mul, hv, toAdd_ofAdd, hβ1] at h2
    exact hx h2

theorem step3_3_31E4_aux [Finite G]
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h25 : Stmt3_3_25) (h27 : Stmt3_3_27)
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hA6 : IsAltBlockType L 6)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTC : tC L T ≠ ⊥) {d : G} (hdD : d ∈ D)
    (hdM : d ∉ M) (hdV : ¬ CFSG.conjugate (vPlus L T) d ≤ qL L T)
    (hF : frattini ↥(qL L T) ≠ ⊥) (hk4 : Nat.card ↥(tC L T) = 4) :
    Nonempty (↥(qL L T ⊔ CFSG.conjugate (vPlus L T) d) ≃* D8D8E4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hidx, hdS, hVdC, hQdec, hTdec, hZ2⟩ :=
    Lem3331S.step3_3_31S_aux h38 h39 h25 h27 h hA6 hTL hTC hdD hdM hdV
  obtain ⟨-, hFTC, -⟩ := h27 G T M L D h d hdD hdM hdV hTC
  obtain ⟨u, huQ, huVd, hu2, hCu⟩ := exists_u h h38 h39 hA6 hTL hF hFTC hVdC hQdec hTdec
  set Q := qL L T with hQdef
  set V := vPlus L T with hVdef
  set C := tC L T with hCdef
  set Vd := CFSG.conjugate V d with hVddef
  set U := blockU L with hUdef
  set Z := quasithinOmegaOneCenter T with hZdef
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hQT : Q ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hCT : C ≤ T := inf_le_left
  have hCe : IsElemAbelian 2 C := isElemAbelian_of_frattini_eq_bot (hT2.to_le hCT) hFTC
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb => by
    have := hCe.1
    exact setLike_mul_comm ha hb
  have hCQ : C ≤ Q := h.tC_le_qL h38 h39 hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hVQ : V ≤ Q := hred.1.trans inf_le_left
  have hVT : V ≤ T := hVQ.trans hQT
  have hVZ : ∀ v ∈ V, ∀ q ∈ Q, v * q = q * v := fun v hv q hq =>
    (Subgroup.mem_centralizer_iff.mp ((hred.1.trans inf_le_right) hv) q hq).symm
  have hVe := hred.2.1
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hVe.1
    exact setLike_mul_comm ha hb
  have hCN : T ≤ Subgroup.normalizer (C : Set G) := Hyp331.le_normalizer_tC hTL
  have huN : u ∈ Subgroup.normalizer (C : Set G) := hCN (hQT huQ)
  have hdT : d ∈ Subgroup.normalizer (T : Set G) := h.DN hdD
  have hUV : U ≤ V := h.blockU_le_vPlus h38 h39 hA6.1 hTL
  have hZT : Z ≤ T := L246C127.omegaOneCenter_le_self T
  have hZcT : Z ≤ Subgroup.centralizer (T : Set G) := L246C127.omegaOneCenter_le_centralizer T
  have hZV : Z ≤ V := le_conjClosure _ _
  have hCVd : C ≤ Subgroup.centralizer (Vd : Set G) := fun c hc =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hVdC hw) c hc).symm
  have hZL1 : Z ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hZ2
    omega
  obtain ⟨⟨z, hzZL⟩, hz1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZL1
  have hz1 : z ≠ 1 := fun h1 => hz1' (Subtype.ext h1)
  have hzC : z ∈ C := ⟨hZT hzZL.1, hzZL.2⟩
  have hzV : z ∈ V := hZV hzZL.1
  have hzz : z * z = 1 := by rw [← sq]; exact hCe.2 z hzC
  have hzT : ∀ t ∈ T, z * t = t * z := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp (hZcT hzZL.1) t ht).symm
  have hZLz : ∀ y ∈ Z ⊓ Subgroup.centralizer (L : Set G), y = 1 ∨ y = z := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      exact congrArg Subtype.val (Lem3328.eq_of_card_two hZ2 (x := ⟨y, hy⟩) (y := ⟨z, hzZL⟩)
        (fun h' => hy1 (congrArg Subtype.val h')) hz1')
  have hCu' : ∀ y ∈ C, y * u = u * y → y = 1 ∨ y = z := fun y hy hyu => hZLz y (hCu y hy hyu)
  obtain ⟨c, hcC, -, ρ₁, hρ₁Q, hρ₁Vd, hρ₁z, hcρ₁⟩ := exists_rho₁ huQ huVd huN hu2 hCQ hCVd
    hCab hCe.2 hzC (hzT u (hQT huQ)) hCu' hk4
  obtain ⟨ρ, β, hβs, hβk, hβe, hρT, -, -, -, hK, -⟩ := CZA6.exists_rho_cZ h38 h39 h hA6 hTL
  have hVdV : ∀ w ∈ Vd, d * w * d⁻¹ ∈ V := fun w hw => Lem3331S.mem_conjugate_iff.mp hw
  have hVdT : Vd ≤ T := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdT) _).mp (hVT (hVdV x hx))
    simpa [mul_assoc] using this
  obtain ⟨w₀, hw₀, hw₀Q⟩ := Set.not_subset.mp hdV
  have hw₀T : w₀ ∈ T := hVdT hw₀
  have hw₀w₀ : w₀ * w₀ = 1 := by
    have h1 := hVe.2 _ (hVdV w₀ hw₀)
    have e : (d * w₀ * d⁻¹) ^ 2 = d * (w₀ * w₀) * d⁻¹ := by rw [sq]; group
    rw [e] at h1
    have h2 := congrArg (fun g => d⁻¹ * g * d) h1
    simpa [mul_assoc] using h2
  have hρw : ρ ⟨w₀, hTL hw₀T⟩ ≠ 1 := fun h1 =>
    hw₀Q (hK w₀ (Subgroup.mem_sup_right hw₀T) (hTL hw₀T) h1)
  obtain ⟨v, hvU, zU, hzUU, hzUe, hzUZ⟩ := exists_v hTL ρ β hβs hβk hβe hρT hw₀T hw₀w₀ hρw
  have hvV : v ∈ V := hUV hvU
  have hvv : v * v = 1 := by rw [← sq]; exact hVe.2 v hvV
  have hzUV : zU ∈ V := hUV hzUU
  have hz'z' : (v * w₀) ^ 2 * (v * w₀) ^ 2 = 1 := by rw [← hzUe, ← sq]; exact hVe.2 zU hzUV
  have hz'1 : (v * w₀) ^ 2 ≠ 1 := fun h1 => hzUZ (by rw [hzUe, h1]; exact Subgroup.one_mem _)
  have hz'z : (v * w₀) ^ 2 ∉ Subgroup.zpowers z := by
    intro hmem
    rcases eq_one_or_of_mem_zpowers hzz hmem with h1 | h1
    · exact hz'1 h1
    · apply hzUZ
      have hzU : zU = z := hzUe.trans h1
      rw [hzU]
      exact ⟨hzU ▸ hzUU, hzZL.2⟩
  have hU16 := card_blockU_eq β hβs hβk
  have hV32 : 32 ≤ Nat.card V := card_ge_32 hUV hU16 (fun hZb => ⟨z, hzV, fun hzU => hz1 (by
    have h1 : z ∈ blockZ L := ⟨hzU, hzZL.2⟩
    rw [hZb] at h1
    exact h1)⟩)
  have hVW : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (Vd : Set G)) :=
    Lem3331S.card_le_two_mul (inv_mul_mem_of_relIndex_two hVQ le_sup_left hVZ hVdV hdS hidx)
  have hW16 : 16 ≤ Nat.card ↥(V ⊓ Subgroup.centralizer (Vd : Set G)) := by omega
  obtain ⟨e₁, he₁W, e₂, he₂W, hi₁, hi₂⟩ := exists_e hW16 hzz hz'z'
    (hzT _ (hVT (hzUe ▸ hzUV)))
    (fun w hw => (hzT w (hVT hw.1)).symm)
    (fun w hw => hVab w hw.1 _ (hzUe ▸ hzUV))
    (fun w hw => by rw [← sq]; exact hVe.2 w hw.1)
  have hS2 : Nat.card ↥(Q ⊔ Vd) = 2 * Nat.card Q := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := Q ⊔ Vd)
    rw [inf_of_le_left le_sup_left, hidx] at h1
    omega
  have hQ2 : Nat.card Q ≤ 2 * Nat.card ↥(U ⊔ C) := by
    have h1 := h.relIndex_qL_le_two h38 h39 hA6 hTL
    have h2 := Subgroup.relIndex_mul_card (H := U ⊔ C) (K := Q)
    rw [inf_of_le_left (sup_le (hUV.trans hVQ) hCQ)] at h2
    rw [← h2]
    exact Nat.mul_le_mul_right _ h1
  have hCU : C ≤ Subgroup.normalizer (U : Set G) := fun x hx =>
    C1.mem_normalizer_blockU (hTL (hCT hx))
  have hZl : ∀ y ∈ blockZ L, y = 1 ∨ y = z := by
    intro y hy
    have hyV : y ∈ V := hUV hy.1
    exact hCu' y ⟨hVT hyV, hy.2⟩ (hVZ y hyV u huQ)
  have hUC := card_sup_le_64 hCU hU16 hk4 (fun x hx => hx.1) hZl hzC hz1 hzz
  have hcard : Nat.card ↥(Q ⊔ Vd) ≤ 256 := by omega
  have hcV : ∀ q ∈ Q, ∀ g ∈ V, Commute q g := fun q hq g hg => (hVZ g hg q hq).symm
  have hcVd : ∀ q ∈ Subgroup.centralizer (Vd : Set G), ∀ w ∈ Vd, Commute q w :=
    fun q hq w hw => (Subgroup.mem_centralizer_iff.mp hq w hw).symm
  have hρ₁ρ₂ : Commute ρ₁ (v * w₀) := (hcV ρ₁ hρ₁Q v hvV).mul_right (hcVd ρ₁ hρ₁Vd w₀ hw₀)
  have hcρ₂ : Commute c (v * w₀) :=
    (hcV c (hCQ hcC) v hvV).mul_right (hcVd c (hCVd hcC) w₀ hw₀)
  have hρ₂e : ∀ e ∈ V ⊓ Subgroup.centralizer (Vd : Set G), Commute (v * w₀) e := fun e he =>
    (Commute.mul_left (hVab v hvV e he.1) (hcVd e he.2 w₀ hw₀).symm)
  have hcc : c * c = 1 := by rw [← sq]; exact hCe.2 c hcC
  have hwi : w₀⁻¹ = w₀ := inv_eq_of_mul_eq_one_right hw₀w₀
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hρ₁4 : ρ₁ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hρ₁z, sq, hzz]
  have hρ₂4 : (v * w₀) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq ((v * w₀) ^ 2), hz'z']
  have hc₂ : v * (v * w₀) * v = (v * w₀)⁻¹ := by
    calc v * (v * w₀) * v = (v * v) * w₀ * v := by group
      _ = w₀⁻¹ * v⁻¹ := by rw [hvv, one_mul, hwi, hvi]
      _ = (v * w₀)⁻¹ := by group
  rw [← hρ₁z] at hz'z hi₁ hi₂
  exact nonempty_mulEquiv (Subgroup.mem_sup_left hρ₁Q) (Subgroup.mem_sup_left (hCQ hcC))
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left (hVQ hvV)) (Subgroup.mem_sup_right hw₀))
    (Subgroup.mem_sup_left (hVQ hvV)) (Subgroup.mem_sup_left (hVQ he₁W.1))
    (Subgroup.mem_sup_left (hVQ he₂W.1)) hρ₁4 hcc hcρ₁ hρ₂4 hvv hc₂
    (by rw [← sq]; exact hVe.2 e₁ he₁W.1) (by rw [← sq]; exact hVe.2 e₂ he₂W.1)
    (hVab e₁ he₁W.1 e₂ he₂W.1) hρ₁ρ₂ (hcV ρ₁ hρ₁Q v hvV) hcρ₂ (hcV c (hCQ hcC) v hvV)
    (hcV ρ₁ hρ₁Q e₁ he₁W.1) (hcV ρ₁ hρ₁Q e₂ he₂W.1) (hcV c (hCQ hcC) e₁ he₁W.1)
    (hcV c (hCQ hcC) e₂ he₂W.1) (hρ₂e e₁ he₁W) (hρ₂e e₂ he₂W) (hVab v hvV e₁ he₁W.1)
    (hVab v hvV e₂ he₂W.1) (by rw [hρ₁z]; exact hz1) hz'z hi₁ hi₂ hcard

theorem step3_3_31E4_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h25 : Stmt3_3_25) (h27 : Stmt3_3_27) : Step3_3_31E4 := by
  intro G _ _ T M L D h hA6 hTL hTC d hdD hdM hdV hF hk4
  exact step3_3_31E4_aux h38 h39 h25 h27 h hA6 hTL hTC hdD hdM hdV hF hk4

end Main

end Lem3331E4

end CFSG.Quasithin.H13
