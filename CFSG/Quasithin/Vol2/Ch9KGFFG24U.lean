module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF.G24

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog

theorem card_le_cube_of_law {ι : Type*} [Finite ι] {K : Type*} [Field K] [Finite K] [CharP K 2]
    {S : Set K} (mul : ι → ι → ι) (a b c d e f : ι → K)
    (hinj : ∀ x y, a x = a y → b x = b y → c x = c y → d x = d y → e x = e y → f x = f y → x = y)
    (hA : ∀ x y, a (mul x y) = a x + a y) (hB : ∀ x y, b (mul x y) = b x + b y)
    (hC : ∀ x y, c (mul x y) = c x + b x * a y + c y)
    (hD : ∀ x y, d (mul x y) = d x + b x * a y ^ 2 + d y)
    (hE : ∀ x y, e (mul x y) = e x + b x * a y ^ 3 + c x * a y ^ 2 + d x * a y + e y)
    (hF : ∀ x y, f (mul x y) = f x + b x ^ 2 * a y ^ 3 + b x * c x * a y ^ 2 + c x ^ 2 * a y +
      b y * (e x + b x * a y ^ 3 + c x * a y ^ 2 + d x * a y) + c y * (d x + b x * a y ^ 2) + f y)
    (hcomm : ∀ x y, mul x y = mul y x)
    (hsq1 : ∀ x, a x * b x = 0) (hsq3 : ∀ x, a x * c x ^ 2 + b x * e x + c x * d x = 0)
    (hS : ∀ x, a x ∈ S ∧ b x ∈ S ∧ c x ∈ S ∧ d x ∈ S ∧ e x ∈ S ∧ f x ∈ S) :
    Nat.card ι ≤ Nat.card S ^ 3 := by
  have h2 : ∀ x : K, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  have hcube : ∀ g : ι → S × S × S, Function.Injective g → Nat.card ι ≤ Nat.card S ^ 3 :=
    fun g hg => by
      have h := Nat.card_le_card_of_injective g hg
      rw [Nat.card_prod, Nat.card_prod] at h
      calc Nat.card ι ≤ _ := h
        _ = Nat.card S ^ 3 := by ring
  have step1 : (∀ x, a x = 0) ∨ (∀ x, b x = 0) := by
    by_contra h
    push Not at h
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := h
    have hbx : b x = 0 := (mul_eq_zero.mp (hsq1 x)).resolve_left hx
    have hay : a y = 0 := (mul_eq_zero.mp (hsq1 y)).resolve_right hy
    have h1 := hsq1 (mul x y)
    rw [hA, hB, hbx, hay, add_zero, zero_add] at h1
    exact (mul_ne_zero hx hy) h1
  have axis : ∀ (P : ι → Prop), (∀ x y, P x → P y → P (mul x y)) →
      (∀ x, P x → a x = 0 ∧ b x = 0) →
      (∀ x, P x → d x = 0) ∨ (∀ x, P x → c x = 0) := by
    intro P hP hab
    by_contra h
    push Not at h
    obtain ⟨⟨x, hPx, hx⟩, ⟨y, hPy, hy⟩⟩ := h
    obtain ⟨hax, hbx⟩ := hab x hPx
    obtain ⟨hay, hby⟩ := hab y hPy
    have hcx : c x = 0 := by
      have := hsq3 x
      rw [hax, hbx, zero_mul, zero_mul, zero_add, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_right hx
    have hdy : d y = 0 := by
      have := hsq3 y
      rw [hay, hby, zero_mul, zero_mul, zero_add, zero_add] at this
      exact (mul_eq_zero.mp this).resolve_left hy
    obtain ⟨hap, hbp⟩ := hab (mul x y) (hP x y hPx hPy)
    have h3 := hsq3 (mul x y)
    rw [hap, hbp, zero_mul, zero_mul, zero_add, zero_add, hC, hD, hcx, hdy, hbx] at h3
    simp only [zero_mul, zero_add, add_zero] at h3
    exact (mul_ne_zero hy hx) h3
  rcases step1 with ha | hb
  ·
    by_cases hb0 : ∀ x, b x = 0
    · rcases axis (fun _ => True) (fun _ _ _ _ => trivial) (fun x _ => ⟨ha x, hb0 x⟩) with
        hd | hc
      · refine hcube (fun x => (⟨c x, (hS x).2.2.1⟩, ⟨e x, (hS x).2.2.2.2.1⟩,
          ⟨f x, (hS x).2.2.2.2.2⟩)) fun x y hxy => ?_
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
        exact hinj x y (by rw [ha, ha]) (by rw [hb0, hb0]) hxy.1
          (by rw [hd x trivial, hd y trivial]) hxy.2.1 hxy.2.2
      · refine hcube (fun x => (⟨d x, (hS x).2.2.2.1⟩, ⟨e x, (hS x).2.2.2.2.1⟩,
          ⟨f x, (hS x).2.2.2.2.2⟩)) fun x y hxy => ?_
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
        exact hinj x y (by rw [ha, ha]) (by rw [hb0, hb0]) (by rw [hc x trivial, hc y trivial])
          hxy.1 hxy.2.1 hxy.2.2
    · push Not at hb0
      obtain ⟨x₀, hx₀⟩ := hb0
      have he : ∀ x y, b x = b y → c x = c y → d x = d y → e x = e y := by
        intro x y hbxy hcxy hdxy
        have hfx := congrArg f (hcomm x x₀)
        have hfy := congrArg f (hcomm y x₀)
        rw [hF, hF, ha, ha] at hfx hfy
        simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_pow (by norm_num : (2 : ℕ) ≠ 0),
          mul_zero, add_zero] at hfx hfy
        have h1 : b x₀ * e x = b x₀ * e y := by
          have hx' : b x₀ * e x + c x₀ * d x = b x * e x₀ + c x * d x₀ := by
            linear_combination hfx
          have hy' : b x₀ * e y + c x₀ * d y = b y * e x₀ + c y * d x₀ := by
            linear_combination hfy
          rw [hbxy, hcxy, hdxy] at hx'
          linear_combination hx' - hy'
        exact mul_left_cancel₀ hx₀ h1
      have hP : ∀ x y, b x = 0 → b y = 0 → b (mul x y) = 0 := fun x y hx hy => by
        rw [hB, hx, hy, add_zero]
      rcases axis (fun x => b x = 0) hP (fun x hx => ⟨ha x, hx⟩) with hd | hc
      · refine hcube (fun x => (⟨b x, (hS x).2.1⟩, ⟨c x, (hS x).2.2.1⟩,
          ⟨f x, (hS x).2.2.2.2.2⟩)) fun x y hxy => ?_
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
        have hdxy : d x = d y := by
          have := hd (mul x y) (by rw [hB, hxy.1, h2])
          rw [hD, ha y] at this
          simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at this
          exact CharTwo.add_eq_zero.mp this
        exact hinj x y (by rw [ha, ha]) hxy.1 hxy.2.1 hdxy (he x y hxy.1 hxy.2.1 hdxy) hxy.2.2
      · refine hcube (fun x => (⟨b x, (hS x).2.1⟩, ⟨d x, (hS x).2.2.2.1⟩,
          ⟨f x, (hS x).2.2.2.2.2⟩)) fun x y hxy => ?_
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
        have hcxy : c x = c y := by
          have := hc (mul x y) (by rw [hB, hxy.1, h2])
          rw [hC, ha y, mul_zero, add_zero] at this
          exact CharTwo.add_eq_zero.mp this
        exact hinj x y (by rw [ha, ha]) hxy.1 hcxy hxy.2.1 (he x y hxy.1 hcxy hxy.2.1) hxy.2.2
  ·
    by_cases ha0 : ∀ x, a x = 0
    · rcases axis (fun _ => True) (fun _ _ _ _ => trivial) (fun x _ => ⟨ha0 x, hb x⟩) with
        hd | hc
      · refine hcube (fun x => (⟨c x, (hS x).2.2.1⟩, ⟨e x, (hS x).2.2.2.2.1⟩,
          ⟨f x, (hS x).2.2.2.2.2⟩)) fun x y hxy => ?_
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
        exact hinj x y (by rw [ha0, ha0]) (by rw [hb, hb]) hxy.1
          (by rw [hd x trivial, hd y trivial]) hxy.2.1 hxy.2.2
      · refine hcube (fun x => (⟨d x, (hS x).2.2.2.1⟩, ⟨e x, (hS x).2.2.2.2.1⟩,
          ⟨f x, (hS x).2.2.2.2.2⟩)) fun x y hxy => ?_
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
        exact hinj x y (by rw [ha0, ha0]) (by rw [hb, hb]) (by rw [hc x trivial, hc y trivial])
          hxy.1 hxy.2.1 hxy.2.2
    · push Not at ha0
      obtain ⟨x₀, hx₀⟩ := ha0
      have hcd : ∀ p, a p = 0 → c p = 0 ∧ d p = 0 := by
        intro p hp
        have h1 := congrArg e (hcomm p x₀)
        rw [hE, hE, hb, hb, hp] at h1
        simp only [zero_mul, zero_pow (by norm_num : (3 : ℕ) ≠ 0),
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] at h1
        have h3 : c p * a x₀ ^ 2 + d p * a x₀ = 0 := by linear_combination h1
        have hdp : d p = c p * a x₀ := by
          have : a x₀ * (c p * a x₀ + d p) = 0 := by linear_combination h3
          exact (CharTwo.add_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hx₀)).symm
        have h4 := hsq3 p
        rw [hp, hb, zero_mul, zero_mul, zero_add, zero_add, hdp] at h4
        have hcp : c p = 0 := by
          have : c p ^ 2 * a x₀ = 0 := by linear_combination h4
          exact pow_eq_zero_iff (two_ne_zero) |>.mp ((mul_eq_zero.mp this).resolve_right hx₀)
        exact ⟨hcp, by rw [hdp, hcp, zero_mul]⟩
      refine hcube (fun x => (⟨a x, (hS x).1⟩, ⟨e x, (hS x).2.2.2.2.1⟩,
        ⟨f x, (hS x).2.2.2.2.2⟩)) fun x y hxy => ?_
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
      obtain ⟨hcp, hdp⟩ := hcd (mul x y) (by rw [hA, hxy.1, h2])
      rw [hC, hb x, zero_mul, add_zero] at hcp
      rw [hD, hb x, zero_mul, add_zero] at hdp
      exact hinj x y hxy.1 (by rw [hb, hb]) (CharTwo.add_eq_zero.mp hcp)
        (CharTwo.add_eq_zero.mp hdp) hxy.2.1 hxy.2.2

section Products

variable {K : Type} [Field K] [CharP K 2]

theorem g2N_mul_g2N
    (A B C D E F A' B' C' D' E' F' : K) :
    g2N A B C D E F * g2N A' B' C' D' E' F' =
      g2N (A + A') (B + B') (C + B * A' + C') (D + B * A' ^ 2 + D')
        (E + B * A' ^ 3 + C * A' ^ 2 + D * A' + E')
        (F + B ^ 2 * A' ^ 3 + B * C * A' ^ 2 + C ^ 2 * A' +
          B' * (E + B * A' ^ 3 + C * A' ^ 2 + D * A') + C' * (D + B * A' ^ 2) + F') := by
  rw [mul_g2N, g2N_mul_r, g2N_mul_a, g2N_mul_u, g2N_mul_v, g2N_mul_b, g2N_mul_c]

omit [CharP K 2] in
theorem units_map_entrywiseHom_pinnedX
    (δ : K →+* K) (α : Fin Tag.G2.rank → ℤ) (c : K) :
    Units.map (entrywiseHom δ) (pinnedX Tag.G2 K α c) = pinnedX Tag.G2 K α (δ c) :=
  Units.ext (entrywise_pinnedX δ α c)

omit [CharP K 2] in
theorem units_map_entrywiseHom_g2N
    (δ : K →+* K) (A B C D E F : K) :
    Units.map (entrywiseHom δ) (g2N A B C D E F) = g2N (δ A) (δ B) (δ C) (δ D) (δ E) (δ F) := by
  simp only [g2N, map_mul, units_map_entrywiseHom_pinnedX]

end Products

section Cube

variable {K : Type} [Field K] [CharP K 2]

theorem card_le_cube
    [Finite K] {S : Set K} {E : Subgroup (ModGL .G2 K)} (hEU : E ≤ posUnipotent .G2 K)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1)
    (hS : ∀ A B C D E' F : K, g2N A B C D E' F ∈ E →
      A ∈ S ∧ B ∈ S ∧ C ∈ S ∧ D ∈ S ∧ E' ∈ S ∧ F ∈ S) :
    Nat.card E ≤ Nat.card S ^ 3 := by
  have := finite_modGL (τ := .G2) (K := K)
  choose a b c d e f hg using fun x : ↥E => exists_g2N_of_mem_posUnipotent (hEU x.2)
  have hco : ∀ x y : ↥E, g2N (a (x * y)) (b (x * y)) (c (x * y)) (d (x * y)) (e (x * y))
      (f (x * y)) = g2N (a x) (b x) (c x) (d x) (e x) (f x) * g2N (a y) (b y) (c y) (d y) (e y)
        (f y) := fun x y => by
    rw [hg, hg, hg]
    rfl
  have hlaw := fun x y => g2N_injective ((hco x y).trans (g2N_mul_g2N _ _ _ _ _ _ _ _ _ _ _ _))
  have hsq' : ∀ x : ↥E, a x * b x = 0 ∧ a x * c x ^ 2 + b x * e x + c x * d x = 0 := by
    intro x
    have h1 : g2N (a x) (b x) (c x) (d x) (e x) (f x) * g2N (a x) (b x) (c x) (d x) (e x) (f x) =
        g2N 0 0 0 0 0 0 := by
      rw [hg, g2N_zero]
      exact hsq x x.2
    rw [g2N_mul_self] at h1
    obtain ⟨-, -, hab, -, -, hF⟩ := g2N_injective h1
    refine ⟨hab, ?_⟩
    have : a x ^ 2 * b x * c x = a x * (a x * b x) * c x := by ring
    rw [this, hab, mul_zero, zero_mul] at hF
    linear_combination hF
  refine card_le_cube_of_law (· * ·) a b c d e f (fun x y h1 h2 h3 h4 h5 h6 => ?_)
    (fun x y => (hlaw x y).1) (fun x y => (hlaw x y).2.1) (fun x y => (hlaw x y).2.2.1)
    (fun x y => (hlaw x y).2.2.2.1) (fun x y => (hlaw x y).2.2.2.2.1)
    (fun x y => (hlaw x y).2.2.2.2.2) (fun x y => Subtype.ext (hcomm x x.2 y y.2))
    (fun x => (hsq' x).1) (fun x => (hsq' x).2) (fun x => hS _ _ _ _ _ _ (by rw [hg]; exact x.2))
  apply Subtype.ext
  rw [← hg x, ← hg y, h1, h2, h3, h4, h5, h6]

end Cube

end CFSG.Quasithin.H13.Ch9.KGFF.G24
