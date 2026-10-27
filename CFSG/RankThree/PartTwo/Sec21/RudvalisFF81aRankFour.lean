module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aRankCount
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81aB2Elem

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.RankFour

open CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem (coord coord_injective exists_coord coord_mem)

variable {G : Type*} [Group G] [Finite G]

theorem card_cen_sign {b₁ b₂ b₃ t : G} (h12 : b₁ * b₂ = b₂ * b₁) (h13 : b₁ * b₃ = b₃ * b₁)
    (h23 : b₂ * b₃ = b₃ * b₂) (h1 : b₁ ^ 3 = 1) (h2 : b₂ ^ 3 = 1) (h3 : b₃ ^ 3 = 1)
    (hcard : Nat.card (Subgroup.closure ({b₁, b₂, b₃} : Set G)) = 27)
    (ht₁ : t * b₁ * t⁻¹ = b₁⁻¹) (ht₂ : t * b₂ * t⁻¹ = b₂) (ht₃ : t * b₃ * t⁻¹ = b₃) :
    Nat.card ↥(Subgroup.closure ({b₁, b₂, b₃} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) =
      3 ^ 2 := by
  have hinj := coord_injective h12 h13 h23 h1 h2 h3 hcard
  have hb1 : b₁ ≠ 1 := by
    intro e
    have e' : coord b₁ b₂ b₃ (1, 0, 0) = coord b₁ b₂ b₃ (0, 0, 0) := by simp [coord, e]
    exact absurd (hinj e') (by decide)
  have key : ∀ l m n : Fin 3, t * coord b₁ b₂ b₃ (l, m, n) * t⁻¹ =
      (b₁⁻¹) ^ (l : ℕ) * b₂ ^ (m : ℕ) * b₃ ^ (n : ℕ) := by
    intro l m n
    rw [← MulAut.conj_apply]
    simp only [coord, map_mul, map_pow, MulAut.conj_apply, ht₁, ht₂, ht₃]
  set C := Subgroup.closure ({b₁, b₂, b₃} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)
  have hmem : ∀ m n : Fin 3, coord b₁ b₂ b₃ (0, m, n) ∈ C := by
    intro m n
    refine Subgroup.mem_inf.mpr ⟨coord_mem _, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have e := key 0 m n
    simp only [Fin.val_zero, pow_zero] at e
    have e2 : coord b₁ b₂ b₃ (0, m, n) = b₂ ^ (m : ℕ) * b₃ ^ (n : ℕ) := by
      simp [coord]
    rw [e2] at e ⊢
    rw [one_mul] at e
    calc b₂ ^ (m : ℕ) * b₃ ^ (n : ℕ) * t
        = t * (b₂ ^ (m : ℕ) * b₃ ^ (n : ℕ)) * t⁻¹ * t := by rw [e]
      _ = t * (b₂ ^ (m : ℕ) * b₃ ^ (n : ℕ)) := by group
  let f : Fin 3 × Fin 3 → ↥C := fun p => ⟨coord b₁ b₂ b₃ (0, p.1, p.2), hmem p.1 p.2⟩
  have hfinj : Function.Injective f := by
    rintro ⟨m, n⟩ ⟨m', n'⟩ e
    have := hinj (congrArg Subtype.val e)
    simp only [Prod.mk.injEq] at this
    rw [this.2.1, this.2.2]
  have hfsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨⟨l, m, n⟩, rfl⟩ := exists_coord h12 h13 h23 h1 h2 h3 hz1
    have htz : t * coord b₁ b₂ b₃ (l, m, n) * t⁻¹ = coord b₁ b₂ b₃ (l, m, n) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hz2
      rw [← this, mul_inv_cancel_right]
    rw [key] at htz
    simp only [coord] at htz
    have hl : (b₁⁻¹) ^ (l : ℕ) = b₁ ^ (l : ℕ) := mul_right_cancel (mul_right_cancel htz)
    have hl0 : (l : ℕ) = 0 := by
      rcases (by omega : (l : ℕ) = 0 ∨ (l : ℕ) = 1 ∨ (l : ℕ) = 2) with h0 | h0 | h0
      · exact h0
      · exfalso
        rw [h0, pow_one, pow_one] at hl
        have hsq : b₁ * b₁ = 1 := by
          calc b₁ * b₁ = b₁⁻¹ * b₁ := by rw [hl]
            _ = 1 := inv_mul_cancel b₁
        apply hb1
        calc b₁ = b₁ ^ 3 * (b₁ * b₁)⁻¹ := by group
          _ = 1 := by rw [h1, hsq, inv_one, one_mul]
      · exfalso
        rw [h0] at hl
        have h4 : b₁ ^ 2 * b₁ ^ 2 = 1 := by
          calc b₁ ^ 2 * b₁ ^ 2 = (b₁⁻¹) ^ 2 * b₁ ^ 2 := by rw [hl]
            _ = 1 := by group
        apply hb1
        calc b₁ = b₁ ^ 2 * b₁ ^ 2 * (b₁ ^ 3)⁻¹ := by group
          _ = 1 := by rw [h4, h1, inv_one, one_mul]
    have hl' : l = 0 := Fin.ext hl0
    subst hl'
    exact ⟨(m, n), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩), Nat.card_prod, Nat.card_fin]
  norm_num

theorem exists_eq_of_ker {B₁ B₂ : Subgroup G} (hB₁B₂ : B₁ ≤ B₂) (φ : ↥B₂ →* ↥B₂)
    (hker : φ.ker = B₁.subgroupOf B₂) (hrange : φ.range ≤ B₁.subgroupOf B₂)
    (hcard : Nat.card B₂ = Nat.card B₁ * Nat.card B₁) {y : G} (hy : y ∈ B₁) :
    ∃ x : ↥B₂, (φ x : G) = y := by
  have hc1 : Nat.card φ.range * Nat.card φ.ker = Nat.card B₂ := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).symm
  have hsub : Nat.card (B₁.subgroupOf B₂) = Nat.card B₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁B₂).toEquiv
  rw [hker, hsub, hcard] at hc1
  have hr : Nat.card φ.range = Nat.card B₁ := Nat.eq_of_mul_eq_mul_right Nat.card_pos hc1
  have heq : φ.range = B₁.subgroupOf B₂ :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hr, hsub])
  have hmem : (⟨y, hB₁B₂ hy⟩ : ↥B₂) ∈ φ.range := by
    rw [heq, Subgroup.mem_subgroupOf]
    exact hy
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, congrArg Subtype.val hx⟩

section Kappa

variable {B₁ B₂ : Subgroup G} {b : G}

theorem kappa_mul (hB₁B₂ : B₁ ≤ B₂) (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hbB₂ : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ B₁) {x y : G} (hx : x ∈ B₂) (hy : y ∈ B₂) :
    b * (x * y) * b⁻¹ * (x * y)⁻¹ = (b * x * b⁻¹ * x⁻¹) * (b * y * b⁻¹ * y⁻¹) := by
  have hc : x * (b * y * b⁻¹ * y⁻¹) = (b * y * b⁻¹ * y⁻¹) * x :=
    hB₂ab x hx _ (hB₁B₂ (hbB₂ y hy))
  calc b * (x * y) * b⁻¹ * (x * y)⁻¹
      = (b * x * b⁻¹ * x⁻¹) * (x * (b * y * b⁻¹ * y⁻¹) * x⁻¹) := by group
    _ = (b * x * b⁻¹ * x⁻¹) * (b * y * b⁻¹ * y⁻¹) := by rw [hc, mul_inv_cancel_right]

theorem kappa_conj {g : G} (hgb : g * b * g⁻¹ = b) (x : G) :
    b * (g * x * g⁻¹) * b⁻¹ * (g * x * g⁻¹)⁻¹ = g * (b * x * b⁻¹ * x⁻¹) * g⁻¹ := by
  calc b * (g * x * g⁻¹) * b⁻¹ * (g * x * g⁻¹)⁻¹
      = (g * b * g⁻¹) * (g * x * g⁻¹) * (g * b * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ := by rw [hgb]
    _ = g * (b * x * b⁻¹ * x⁻¹) * g⁻¹ := by group

theorem kappa_eq_one (hbB₁ : ∀ y ∈ B₁, y * b = b * y)
    (hker : ∀ x ∈ B₂, x * b = b * x → x ∈ B₁) {x : G} (hx : x ∈ B₂) :
    b * x * b⁻¹ * x⁻¹ = 1 ↔ x ∈ B₁ := by
  constructor
  · intro e
    refine hker x hx ?_
    have e' : b * x * b⁻¹ = x := by
      have := congrArg (· * x) e
      simpa only [one_mul, inv_mul_cancel_right] using this
    calc x * b = b * x * b⁻¹ * b := by rw [e']
      _ = b * x := by group
  · intro hxB₁
    have e := hbB₁ x hxB₁
    calc b * x * b⁻¹ * x⁻¹ = x * b * b⁻¹ * x⁻¹ := by rw [e]
      _ = 1 := by group

theorem kappa_inv (hB₁B₂ : B₁ ≤ B₂) (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hbB₂ : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ B₁) {x : G} (hx : x ∈ B₂) :
    b * x⁻¹ * b⁻¹ * x⁻¹⁻¹ = (b * x * b⁻¹ * x⁻¹)⁻¹ := by
  have h0 := kappa_mul hB₁B₂ hB₂ab hbB₂ hx (inv_mem hx)
  simp only [mul_inv_cancel, mul_one, inv_one] at h0
  exact eq_inv_of_mul_eq_one_right h0.symm

theorem irreducible_of_kappa {T : Set G} (hB₁B₂ : B₁ ≤ B₂)
    (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x)
    (hbB₂ : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ B₁) (hbB₁ : ∀ y ∈ B₁, y * b = b * y)
    (hker : ∀ x ∈ B₂, x * b = b * x → x ∈ B₁) (hTb : ∀ g ∈ T, g * b * g⁻¹ = b)
    (hB₁irr : ∀ H : Subgroup G, H ≤ B₁ → H ≠ ⊥ → (∀ g ∈ T, ∀ x ∈ H, g * x * g⁻¹ ∈ H) →
      H = B₁) :
    ∀ U : Subgroup G, B₁ ≤ U → U ≤ B₂ → (∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) →
      U = B₁ ∨ U = B₂ := by
  intro U hB₁U hUB₂ hUT
  let φ : ↥B₂ →* G :=
    { toFun := fun x => b * x * b⁻¹ * (x : G)⁻¹
      map_one' := by simp
      map_mul' := fun x y => kappa_mul hB₁B₂ hB₂ab hbB₂ x.2 y.2 }
  let H : Subgroup G := (U.subgroupOf B₂).map φ
  have hHmem : ∀ y, y ∈ H ↔ ∃ u ∈ U, ∃ hu : u ∈ B₂, b * u * b⁻¹ * u⁻¹ = y := by
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, Subgroup.mem_subgroupOf.mp hu, u.2, rfl⟩
    · rintro ⟨u, hu, huB₂, rfl⟩
      exact ⟨⟨u, huB₂⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hHB₁ : H ≤ B₁ := by
    intro y hy
    obtain ⟨u, -, huB₂, rfl⟩ := (hHmem y).mp hy
    exact hbB₂ u huB₂
  have hHT : ∀ g ∈ T, ∀ y ∈ H, g * y * g⁻¹ ∈ H := by
    intro g hg y hy
    obtain ⟨u, hu, huB₂, rfl⟩ := (hHmem y).mp hy
    refine (hHmem _).mpr ⟨g * u * g⁻¹, hUT g hg u hu, hUB₂ (hUT g hg u hu), ?_⟩
    exact kappa_conj (hTb g hg) u
  by_cases hH : H = ⊥
  · left
    refine le_antisymm (fun u hu => ?_) hB₁U
    have : b * u * b⁻¹ * u⁻¹ ∈ H := (hHmem _).mpr ⟨u, hu, hUB₂ hu, rfl⟩
    rw [hH, Subgroup.mem_bot] at this
    exact (kappa_eq_one hbB₁ hker (hUB₂ hu)).mp this
  · right
    have hHeq := hB₁irr H hHB₁ hH hHT
    refine le_antisymm hUB₂ fun x hx => ?_
    have hκx : b * x * b⁻¹ * x⁻¹ ∈ H := by rw [hHeq]; exact hbB₂ x hx
    obtain ⟨u, hu, huB₂, hux⟩ := (hHmem _).mp hκx
    have hxu : x * u⁻¹ ∈ B₁ := by
      refine (kappa_eq_one hbB₁ hker (mul_mem hx (inv_mem huB₂))).mp ?_
      rw [kappa_mul hB₁B₂ hB₂ab hbB₂ hx (inv_mem huB₂), kappa_inv hB₁B₂ hB₂ab hbB₂ huB₂, hux,
        mul_inv_cancel]
    have := mul_mem (hB₁U hxu) hu
    rwa [inv_mul_cancel_right] at this

end Kappa

section Main

variable {B₂ : Subgroup G} {b b₁ b₂ b₃ t : G}

theorem four_le_localRank
    (hB₁card : Nat.card (Subgroup.closure ({b₁, b₂, b₃} : Set G)) = 27)
    (hB₁B₂ : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B₂)
    (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x) (hB₂3 : ∀ x ∈ B₂, x ^ 3 = 1)
    (hB₂card : Nat.card B₂ = 3 ^ 6)
    (hbB₂ : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hbB₁ : ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), y * b = b * y)
    (hker : ∀ x ∈ B₂, x * b = b * x → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htB₂ : ∀ x ∈ B₂, t * x * t⁻¹ ∈ B₂)
    (htb : t * b * t⁻¹ = b) (ht₁ : t * b₁ * t⁻¹ = b₁⁻¹) (ht₂ : t * b₂ * t⁻¹ = b₂)
    (ht₃ : t * b₃ * t⁻¹ = b₃) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  set B₁ := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁def
  have mem₁ : b₁ ∈ B₁ := Subgroup.subset_closure (by simp)
  have mem₂ : b₂ ∈ B₁ := Subgroup.subset_closure (by simp)
  have mem₃ : b₃ ∈ B₁ := Subgroup.subset_closure (by simp)
  have hB₁comm : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := fun x hx y hy =>
    hB₂ab x (hB₁B₂ hx) y (hB₁B₂ hy)
  have κ_mul : ∀ x ∈ B₂, ∀ y ∈ B₂, b * (x * y) * b⁻¹ * (x * y)⁻¹ =
      (b * x * b⁻¹ * x⁻¹) * (b * y * b⁻¹ * y⁻¹) := fun x hx y hy =>
    kappa_mul hB₁B₂ hB₂ab hbB₂ hx hy
  have κ_conj : ∀ x : G, b * (t * x * t⁻¹) * b⁻¹ * (t * x * t⁻¹)⁻¹ =
      t * (b * x * b⁻¹ * x⁻¹) * t⁻¹ := kappa_conj htb
  have κ_one : ∀ x ∈ B₂, b * x * b⁻¹ * x⁻¹ = 1 ↔ x ∈ B₁ := fun x hx =>
    kappa_eq_one hbB₁ hker hx
  let φ : ↥B₂ →* ↥B₂ :=
    { toFun := fun x => ⟨b * x * b⁻¹ * x⁻¹, hB₁B₂ (hbB₂ x x.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (κ_mul x x.2 y y.2) }
  have hφker : φ.ker = B₁.subgroupOf B₂ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (κ_one x x.2).mp (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext ((κ_one x x.2).mpr hx)
  have hφrange : φ.range ≤ B₁.subgroupOf B₂ := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (hbB₂ x x.2)
  have honto : ∀ y ∈ B₁, ∃ x ∈ B₂, b * x * b⁻¹ * x⁻¹ = y := by
    intro y hy
    obtain ⟨x, hx⟩ := exists_eq_of_ker hB₁B₂ φ hφker hφrange
      (by rw [hB₂card, hB₁card]; norm_num) hy
    exact ⟨x, x.2, hx⟩
  let F : Subgroup G :=
    { carrier := {x | x ∈ B₂ ∧ t * x * t⁻¹ * x⁻¹ ∈ B₁}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := fun {x y} hx hy => by
        refine ⟨mul_mem hx.1 hy.1, ?_⟩
        have hc : (t * y * t⁻¹ * y⁻¹) * x⁻¹ = x⁻¹ * (t * y * t⁻¹ * y⁻¹) :=
          hB₂ab _ (hB₁B₂ hy.2) _ (inv_mem hx.1)
        have e : t * (x * y) * t⁻¹ * (x * y)⁻¹ =
            (t * x * t⁻¹) * ((t * y * t⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [e, hc, ← mul_assoc]
        exact mul_mem hx.2 hy.2
      inv_mem' := fun {x} hx => by
        refine ⟨inv_mem hx.1, ?_⟩
        have hc : (t * x * t⁻¹)⁻¹ * x = x * (t * x * t⁻¹)⁻¹ :=
          hB₂ab _ (inv_mem (htB₂ x hx.1)) _ hx.1
        have e : t * x⁻¹ * t⁻¹ * x⁻¹⁻¹ = (t * x * t⁻¹)⁻¹ * x := by group
        rw [e, hc, show x * (t * x * t⁻¹)⁻¹ = (t * x * t⁻¹ * x⁻¹)⁻¹ by group]
        exact inv_mem hx.2 }
  have hFmem : ∀ x, x ∈ F ↔ x ∈ B₂ ∧ t * x * t⁻¹ * x⁻¹ ∈ B₁ := fun _ => Iff.rfl
  have htB₁ : ∀ y ∈ B₁, t * y * t⁻¹ ∈ B₁ := by
    have hle : B₁ ≤ B₁.comap (MulAut.conj t).toMonoidHom := by
      rw [hB₁def, Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      show t * z * t⁻¹ ∈ B₁
      rcases hz with rfl | rfl | rfl
      · rw [ht₁]; exact inv_mem mem₁
      · rw [ht₂]; exact mem₂
      · rw [ht₃]; exact mem₃
    intro y hy
    exact hle hy
  have hB₁F : B₁ ≤ F := fun y hy => ⟨hB₁B₂ hy, mul_mem (htB₁ y hy) (inv_mem hy)⟩
  have hFB₂ : F ≤ B₂ := fun _ hx => hx.1
  set C := B₁ ⊓ Subgroup.centralizer ({t} : Set G) with hCdef
  have hκC : ∀ x ∈ F, b * x * b⁻¹ * x⁻¹ ∈ C := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hbB₂ x hx.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    set w := t * x * t⁻¹ * x⁻¹ with hwdef
    have hw : w ∈ B₁ := hx.2
    have htx : t * x * t⁻¹ = w * x := by rw [hwdef, inv_mul_cancel_right]
    have hκw : b * w * b⁻¹ * w⁻¹ = 1 := (κ_one w (hB₁B₂ hw)).mpr hw
    have e : t * (b * x * b⁻¹ * x⁻¹) * t⁻¹ = b * x * b⁻¹ * x⁻¹ := by
      rw [← κ_conj, htx, κ_mul w (hB₁B₂ hw) x hx.1, hκw, one_mul]
    calc b * x * b⁻¹ * x⁻¹ * t = t * (b * x * b⁻¹ * x⁻¹) * t⁻¹ * t := by rw [e]
      _ = t * (b * x * b⁻¹ * x⁻¹) := by group
  let ρ : ↥F →* ↥C :=
    { toFun := fun x => ⟨b * x * b⁻¹ * x⁻¹, hκC x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (κ_mul x (hFB₂ x.2) y (hFB₂ y.2)) }
  have hρsurj : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨x, hx, rfl⟩ := honto y hy1
    have hxF : x ∈ F := by
      refine ⟨hx, (κ_one _ (mul_mem (htB₂ x hx) (inv_mem hx))).mp ?_⟩
      rw [κ_mul _ (htB₂ x hx) _ (inv_mem hx), κ_conj]
      have hty : t * (b * x * b⁻¹ * x⁻¹) * t⁻¹ = b * x * b⁻¹ * x⁻¹ := by
        have := Subgroup.mem_centralizer_singleton_iff.mp hy2
        rw [← this, mul_inv_cancel_right]
      rw [hty]
      have hinv : b * x⁻¹ * b⁻¹ * x⁻¹⁻¹ = (b * x * b⁻¹ * x⁻¹)⁻¹ :=
        kappa_inv hB₁B₂ hB₂ab hbB₂ hx
      rw [hinv, mul_inv_cancel]
    exact ⟨⟨x, hxF⟩, rfl⟩
  have hρker : ρ.ker = B₁.subgroupOf F := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact (κ_one x (hFB₂ x.2)).mp (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext ((κ_one x (hFB₂ x.2)).mpr hx)
  have hcardC : Nat.card C = 3 ^ 2 :=
    card_cen_sign (hB₁comm _ mem₁ _ mem₂) (hB₁comm _ mem₁ _ mem₃) (hB₁comm _ mem₂ _ mem₃)
      (hB₂3 _ (hB₁B₂ mem₁)) (hB₂3 _ (hB₁B₂ mem₂)) (hB₂3 _ (hB₁B₂ mem₃)) hB₁card ht₁ ht₂ ht₃
  have hcardF : Nat.card F = 3 ^ 2 * Nat.card B₁ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj).toEquiv, hρker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁F).toEquiv, hcardC] at h1
    exact h1
  have := CFSG.RankThree.PartTwo.Sec21.FF81.RankCount.le_localRank_of_fixed_quotient
    hB₁F hFB₂ hB₂ab hB₂3 ht1 ht2 htB₂ (fun f hf => hf.2) hcardC hcardF
  simpa using this

end Main

theorem ker_of_cenS {B₂ : Subgroup G} {b b₁ b₂ b₃ : G}
    (hB₁B₂ : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ B₂)
    (hB₂ab : ∀ x ∈ B₂, ∀ y ∈ B₂, x * y = y * x) (hB₂p : IsPGroup 3 B₂)
    (hBB₂ : ∀ x ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G), x ∈ B₂ →
      x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hCB : ∀ x ∈ Subgroup.centralizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G),
      IsPGroup 3 (Subgroup.zpowers x) → x ∈ Subgroup.closure ({b, b₁, b₂, b₃} : Set G)) :
    ∀ x ∈ B₂, x * b = b * x → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := by
  intro x hx hxb
  have hle : Subgroup.closure ({b, b₁, b₂, b₃} : Set G) ≤
      Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with rfl | hy
    · exact hxb.symm
    · exact hB₂ab y (hB₁B₂ (Subgroup.subset_closure hy)) x hx
  have hxC : x ∈ Subgroup.centralizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := hB₂p.to_le (Subgroup.zpowers_le.2 hx)
  exact hBB₂ x (hCB x hxC hxp) hx

theorem four_le_localRank_of_setup {b b₁ b₂ b₃ c t : G} {B₂ : Subgroup G}
    (h : CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.Setup b b₁ b₂ b₃ c B₂) {T : Set G}
    (hT : ∀ g ∈ T, ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂)
    (hirr : ∀ U : Subgroup G, Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ U → U ≤ B₂ →
      (∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U) →
        U = Subgroup.closure ({b₁, b₂, b₃} : Set G) ∨ U = B₂)
    (hB₂card : Nat.card B₂ = 3 ^ 6)
    (hbN' : ∀ hb : b ∈ Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G),
      (⟨b, hb⟩ : ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G))) ∈
        commutator ↥(Subgroup.normalizer (Subgroup.closure ({b, b₁, b₂, b₃} : Set G) : Set G)) →
      ∃ s : G, s * b₁ * s⁻¹ = b₁⁻¹ ∧
        ∀ x ∈ B₂, s * x * s⁻¹ * x⁻¹ ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hbG : b ∈ commutator G)
    (hker : ∀ x ∈ B₂, x * b = b * x → x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) (htB₂ : ∀ x ∈ B₂, t * x * t⁻¹ ∈ B₂)
    (htb : t * b * t⁻¹ = b) (ht₁ : t * b₁ * t⁻¹ = b₁⁻¹) (ht₂ : t * b₂ * t⁻¹ = b₂)
    (ht₃ : t * b₃ * t⁻¹ = b₃) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G :=
  four_le_localRank h.B₁card h.B₁B₂ h.B₂ab
    (CFSG.RankThree.PartTwo.Sec21.FF81.B2Elem.exp_three_of_irreducible' h hT hirr hB₂card hbN'
      hbG) hB₂card h.bB₂ (fun y hy => (h.bB₁ y hy).symm) hker ht1 ht2 htB₂ htb ht₁ ht₂ ht₃

end CFSG.RankThree.PartTwo.Sec21.FF81.RankFour
