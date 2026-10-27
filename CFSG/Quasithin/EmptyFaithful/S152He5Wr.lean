module

public import CFSG.Quasithin.EmptyFaithful.S152He5Over

public section

namespace CFSG.Quasithin

namespace WrZ2

open RegularWreathProduct

variable {A : Type*} [Group A] {Q : Type*} [Group Q]

structure IsTwo (g : Q) : Prop where
  all : ∀ x : Q, x = 1 ∨ x = g
  ne : g ≠ 1

theorem IsTwo.mul_self {g : Q} (h : IsTwo g) : g * g = 1 := by
  rcases h.all (g * g) with h1 | h1
  · exact h1
  · exact absurd (mul_eq_right.mp h1) h.ne

theorem IsTwo.inv_eq {g : Q} (h : IsTwo g) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right h.mul_self

@[expose] def wrSub (Q : Type*) [Group Q] (P : Subgroup A) : Subgroup (A ≀ᵣ Q) where
  carrier := {w | ∀ x, w.left x ∈ P}
  one_mem' := fun x => P.one_mem
  mul_mem' := fun {a b} ha hb x => by
    rw [mul_left]
    exact P.mul_mem (ha x) (hb _)
  inv_mem' := fun {a} ha x => by
    rw [inv_left]
    exact P.inv_mem (ha _)

theorem mem_wrSub {P : Subgroup A} {w : A ≀ᵣ Q} : w ∈ wrSub Q P ↔ ∀ x, w.left x ∈ P := Iff.rfl

@[expose] def bs (Q : Type*) [Group Q] (f : Q → A) : A ≀ᵣ Q := ⟨f, 1⟩

@[expose] def sh (A : Type*) [Group A] (q : Q) : A ≀ᵣ Q := ⟨1, q⟩

theorem bs_mul_sh (w : A ≀ᵣ Q) : w = bs Q w.left * sh A w.right := by
  ext x <;> simp [bs, sh]

theorem bs_left_eq (w : A ≀ᵣ Q) : bs Q w.left = w * (sh A w.right)⁻¹ := by
  ext x <;> simp [bs, sh]

theorem bs_mul (f f' : Q → A) : bs Q f * bs Q f' = bs Q (f * f') := by
  ext x <;> simp [bs]

theorem bs_inv (f : Q → A) : (bs Q f)⁻¹ = bs Q f⁻¹ := by
  ext x <;> simp [bs]

theorem bs_one : (bs Q (1 : Q → A)) = 1 := by
  ext x <;> simp [bs]

theorem sh_mem_wrSub (P : Subgroup A) (q : Q) : sh A q ∈ wrSub Q P := fun _ => P.one_mem

theorem bs_mem_wrSub {P : Subgroup A} {f : Q → A} : bs Q f ∈ wrSub Q P ↔ ∀ x, f x ∈ P := Iff.rfl

theorem sh_mul_bs_mul_sh_inv (q : Q) (f : Q → A) :
    sh A q * bs Q f * (sh A q)⁻¹ = bs Q (fun x => f (q⁻¹ * x)) := by
  ext x <;> simp [sh, bs]

theorem wrSub_le_wrSub_iff {P P' : Subgroup A} : wrSub Q P ≤ wrSub Q P' ↔ P ≤ P' := by
  constructor
  · intro h a ha
    have : bs Q (fun _ => a) ∈ wrSub Q P := fun _ => ha
    exact h this 1
  · intro h w hw x
    exact h (hw x)

theorem wrSub_top : wrSub Q (⊤ : Subgroup A) = ⊤ := by
  ext w
  simp [mem_wrSub]

@[expose] def WrCollapse (D : Subgroup A) : Prop :=
  ∀ R P : Subgroup A, D ≤ R → R ≤ P → (∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) → R = P

theorem exists_wrSub_of_le {g : Q} (hg : IsTwo g) {D : Subgroup A} (hD : WrCollapse D)
    {S : Subgroup (A ≀ᵣ Q)} (hS : wrSub Q D ≤ S) : ∃ P : Subgroup A, D ≤ P ∧ S = wrSub Q P := by
  classical
  have hsh : ∀ q, sh A q ∈ S := fun q => hS (sh_mem_wrSub D q)
  let P₁ : Subgroup A :=
    { carrier := {a | ∃ f, bs Q f ∈ S ∧ f 1 = a}
      one_mem' := ⟨1, by rw [bs_one]; exact S.one_mem, rfl⟩
      mul_mem' := by
        rintro a b ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩
        exact ⟨f * f', by rw [← bs_mul]; exact S.mul_mem hf hf', rfl⟩
      inv_mem' := by
        rintro a ⟨f, hf, rfl⟩
        exact ⟨f⁻¹, by rw [← bs_inv]; exact S.inv_mem hf, rfl⟩ }
  let R₀ : Subgroup A :=
    { carrier := {a | bs Q (Pi.mulSingle (1 : Q) a) ∈ S}
      one_mem' := by
        change bs Q (Pi.mulSingle (1 : Q) (1 : A)) ∈ S
        rw [Pi.mulSingle_one, bs_one]; exact S.one_mem
      mul_mem' := by
        intro a b ha hb
        change bs Q (Pi.mulSingle (1 : Q) (a * b)) ∈ S
        rw [Pi.mulSingle_mul, ← bs_mul]
        exact S.mul_mem ha hb
      inv_mem' := by
        intro a ha
        change bs Q (Pi.mulSingle (1 : Q) a⁻¹) ∈ S
        rw [Pi.mulSingle_inv, ← bs_inv]
        exact S.inv_mem ha }
  have hDR₀ : D ≤ R₀ := by
    intro d hd
    refine hS ?_
    rw [bs_mem_wrSub]
    intro x
    by_cases hx : x = 1
    · subst hx; simp [hd]
    · simp [Pi.mulSingle_eq_of_ne hx, D.one_mem]
  have hR₀P₁ : R₀ ≤ P₁ := fun a ha => ⟨_, ha, by simp⟩
  have hnorm : ∀ p ∈ P₁, ∀ r ∈ R₀, p * r * p⁻¹ ∈ R₀ := by
    rintro p ⟨f, hf, rfl⟩ r hr
    have h1 : bs Q f * bs Q (Pi.mulSingle (1 : Q) r) * (bs Q f)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem hf hr) (S.inv_mem hf)
    have h2 : bs Q f * bs Q (Pi.mulSingle (1 : Q) r) * (bs Q f)⁻¹ =
        bs Q (Pi.mulSingle (1 : Q) (f 1 * r * (f 1)⁻¹)) := by
      rw [bs_inv, bs_mul, bs_mul]
      congr 1
      funext x
      by_cases hx : x = 1
      · subst hx; simp
      · simp [Pi.mulSingle_eq_of_ne hx]
    change bs Q (Pi.mulSingle (1 : Q) (f 1 * r * (f 1)⁻¹)) ∈ S
    rw [← h2]; exact h1
  have hEq : R₀ = P₁ := hD R₀ P₁ hDR₀ hR₀P₁ hnorm
  have hbs_mem : ∀ f : Q → A, bs Q f ∈ S ↔ ∀ x, f x ∈ P₁ := by
    intro f
    constructor
    · intro hf x
      rcases hg.all x with hx | hx
      · rw [hx]; exact ⟨f, hf, rfl⟩
      · rw [hx]
        refine ⟨fun x => f (g⁻¹ * x), ?_, ?_⟩
        · have := S.mul_mem (S.mul_mem (hsh g) hf) (S.inv_mem (hsh g))
          rwa [sh_mul_bs_mul_sh_inv] at this
        · simp [hg.inv_eq]
    · intro hf
      have hf1 : f 1 ∈ R₀ := hEq ▸ hf 1
      have hfg : f g ∈ R₀ := hEq ▸ hf g
      have e : bs Q f = bs Q (Pi.mulSingle (1 : Q) (f 1)) *
          (sh A g * bs Q (Pi.mulSingle (1 : Q) (f g)) * (sh A g)⁻¹) := by
        rw [sh_mul_bs_mul_sh_inv, bs_mul]
        congr 1
        funext x
        rcases hg.all x with hx | hx
        · simp [hx, hg.inv_eq, Pi.mulSingle_eq_of_ne hg.ne]
        · simp [hx, Pi.mulSingle_eq_of_ne hg.ne]
      rw [e]
      exact S.mul_mem hf1 (S.mul_mem (S.mul_mem (hsh g) hfg) (S.inv_mem (hsh g)))
  refine ⟨P₁, fun d hd => hEq ▸ hDR₀ hd, ?_⟩
  ext w
  constructor
  · intro hw
    have hw' : bs Q w.left ∈ S := by
      rw [bs_left_eq]
      exact S.mul_mem hw (S.inv_mem (hsh _))
    exact (hbs_mem _).mp hw'
  · intro hw
    have hw' : bs Q w.left ∈ S := (hbs_mem _).mpr hw
    rw [bs_mul_sh w]
    exact S.mul_mem hw' (hsh _)

theorem overBool2_wrSub {g : Q} (hg : IsTwo g) {D : Subgroup A} (hD : OverBool2 D)
    (hc : WrCollapse D) : OverBool2 (wrSub Q D) := by
  obtain ⟨C₁, C₂, h1, h2, h12, h21, hall⟩ := hD
  refine ⟨wrSub Q C₁, wrSub Q C₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_le_of_ne (wrSub_le_wrSub_iff.mpr h1.le) fun h =>
      h1.ne (le_antisymm h1.le (wrSub_le_wrSub_iff.mp h.ge))
  · exact lt_of_le_of_ne (wrSub_le_wrSub_iff.mpr h2.le) fun h =>
      h2.ne (le_antisymm h2.le (wrSub_le_wrSub_iff.mp h.ge))
  · exact fun h => h12 (wrSub_le_wrSub_iff.mp h)
  · exact fun h => h21 (wrSub_le_wrSub_iff.mp h)
  · intro S hS
    obtain ⟨P, hDP, rfl⟩ := exists_wrSub_of_le hg hc hS
    rcases hall P hDP with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr wrSub_top))

section Sylow

variable [Finite A] [Finite Q]

omit [Finite A] in
theorem card_wrSub (P : Subgroup A) :
    Nat.card (wrSub Q P) = Nat.card P ^ Nat.card Q * Nat.card Q := by
  let e : wrSub Q P ≃ (Q → P) × Q :=
    { toFun := fun w => (fun x => ⟨w.1.left x, w.2 x⟩, w.1.right)
      invFun := fun p => ⟨⟨fun x => (p.1 x : A), p.2⟩, fun x => (p.1 x).2⟩
      left_inv := fun w => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun]

theorem isPGroup_wrSub (hQ : Nat.card Q = 2) {D : Subgroup A} (hD : IsPGroup 2 D) :
    IsPGroup 2 (wrSub Q D) := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hD
  refine IsPGroup.of_card (n := a * 2 + 1) ?_
  rw [card_wrSub, hQ, ha, ← pow_mul, pow_succ]

theorem index_wrSub (hQ : Nat.card Q = 2) {D : Subgroup A} (hD : ¬ 2 ∣ D.index) :
    ¬ 2 ∣ (wrSub Q D).index := by
  have h1 := Subgroup.card_mul_index (wrSub Q D)
  have h2 : Nat.card (A ≀ᵣ Q) = Nat.card A ^ 2 * 2 := by
    have := RegularWreathProduct.card (D := A) (Q := Q)
    rwa [hQ] at this
  have h3 := Subgroup.card_mul_index D
  rw [card_wrSub, hQ, h2, ← h3] at h1
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hidx : (wrSub Q D).index = D.index ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card D ^ 2 * 2 by positivity)
    calc Nat.card D ^ 2 * 2 * (wrSub Q D).index = (Nat.card D * D.index) ^ 2 * 2 := h1
      _ = Nat.card D ^ 2 * 2 * D.index ^ 2 := by ring
  rw [hidx]
  intro h
  exact hD (Nat.prime_two.dvd_of_dvd_pow h)

end Sylow

end WrZ2

end CFSG.Quasithin
