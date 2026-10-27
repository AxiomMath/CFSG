module

public import CFSG.Quasithin.Vol2.F134LieOddHeis
public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.F134.LieOdd

open Matrix CFSG.SectionRank.OddCover CFSG.Assembly.LowTwoRank

theorem eq_one_of_norms {G : Type*} [CommGroup G] (h2 : ∀ x : G, x * x = 1)
    {x₀ x₁ x₂ y₁ y₂ z₁ z₂ : G} (h1 : x₀ * x₁ * x₂ = 1) (h2' : x₁ * y₁ * y₂ = 1)
    (h3 : x₂ * z₁ * z₂ = 1) (h4 : x₀ * y₁ * z₂ = 1) (h5 : x₀ * y₂ * z₁ = 1) : x₀ = 1 := by
  have e : (x₀ * x₁ * x₂) * ((x₁ * y₁ * y₂) * (x₂ * z₁ * z₂) * (x₀ * y₁ * z₂) * (x₀ * y₂ * z₁)) =
      x₀ * (x₀ * x₀) * (x₁ * x₁) * (x₂ * x₂) * (y₁ * y₁) * (y₂ * y₂) * (z₁ * z₁) * (z₂ * z₂) := by
    ac_rfl
  rw [h1, h2', h3, h4, h5] at e
  simp only [h2, mul_one] at e
  exact e.symm

theorem commute_of_sq_eq_one {G : Type*} [Group G] {W : Subgroup G} (hW2 : ∀ w ∈ W, w ^ 2 = 1) :
    ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  intro a ha b hb
  have hinv : ∀ w ∈ W, w⁻¹ = w := fun w hw =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hW2 w hw)
  have hab := hW2 _ (mul_mem ha hb)
  rw [sq] at hab
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b * a := by rw [_root_.mul_inv_rev, hinv a ha, hinv b hb]

theorem mem_normalizer_of_conj {G : Type*} [Group G] {R : Subgroup G} {g : G}
    (h1 : ∀ r ∈ R, g * r * g⁻¹ ∈ R) (h2 : ∀ r ∈ R, g⁻¹ * r * g⁻¹⁻¹ ∈ R) :
    g ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨h1 r, fun hr => ?_⟩
  have := h2 _ hr
  rwa [show g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r by group] at this

variable {K : Type} [Field K] {H : Subgroup (GL (Fin 3) K)} {M : Subgroup Kˣ}

theorem mat_commute_of_commute {a b : H} (h : a * b = b * a) :
    ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  simpa using congrArg (fun z : H => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h

theorem commute_of_mat_commute {a b : H}
    (h : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((b : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) : a * b = b * a :=
  Subtype.ext (Units.ext (by simpa using h))

@[expose] def norm3 {G : Type*} [Group G] (y w : G) : G :=
  w * (y * w * y⁻¹) * (y ^ 2 * w * (y ^ 2)⁻¹)

theorem norm3_mem {G : Type*} [Group G] {W : Subgroup G} {y w : G}
    (hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W) (hw : w ∈ W) : norm3 y w ∈ W := by
  have h1 := hyW w hw
  have h2 : y ^ 2 * w * (y ^ 2)⁻¹ ∈ W := by
    have := hyW _ h1
    rwa [show y * (y * w * y⁻¹) * y⁻¹ = y ^ 2 * w * (y ^ 2)⁻¹ by rw [sq]; group] at this
  exact mul_mem (mul_mem hw h1) h2

theorem conj_norm3 {G : Type*} [Group G] {W : Subgroup G} {y w : G}
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W) (hy3 : y ^ 3 = 1)
    (hw : w ∈ W) : y * norm3 y w * y⁻¹ = norm3 y w := by
  have h1 := hyW w hw
  have h2 : y ^ 2 * w * (y ^ 2)⁻¹ ∈ W := by
    have := hyW _ h1
    rwa [show y * (y * w * y⁻¹) * y⁻¹ = y ^ 2 * w * (y ^ 2)⁻¹ by rw [sq]; group] at this
  have e3 : y * (y ^ 2 * w * (y ^ 2)⁻¹) * y⁻¹ = w := by
    calc y * (y ^ 2 * w * (y ^ 2)⁻¹) * y⁻¹ = y ^ 3 * w * (y ^ 3)⁻¹ := by
          rw [pow_three', sq]; group
      _ = w := by rw [hy3, one_mul, inv_one, mul_one]
  have e2 : y * (y * w * y⁻¹) * y⁻¹ = y ^ 2 * w * (y ^ 2)⁻¹ := by rw [sq]; group
  unfold norm3
  calc y * (w * (y * w * y⁻¹) * (y ^ 2 * w * (y ^ 2)⁻¹)) * y⁻¹ =
        (y * w * y⁻¹) * (y * (y * w * y⁻¹) * y⁻¹) * (y * (y ^ 2 * w * (y ^ 2)⁻¹) * y⁻¹) := by
        group
    _ = (y * w * y⁻¹) * (y ^ 2 * w * (y ^ 2)⁻¹) * w := by rw [e2, e3]
    _ = w * (y * w * y⁻¹) * (y ^ 2 * w * (y ^ 2)⁻¹) := by
        rw [hWab _ (mul_mem h1 h2) _ hw]
        simp only [mul_assoc]

namespace OddModel

variable (h : OddModel H M)
include h

section HeisMain

variable [Finite K] {P : Subgroup (StatedProj H)}
  (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
  (hstd : ∀ x : H, proj H x ∈ P → (x : GL (Fin 3) K) ∈ torus3 M ⊔ Subgroup.zpowers cycGL)
  {x₀ : H} (hx₀ : proj H x₀ ∈ P) (hx₀T : (x₀ : GL (Fin 3) K) ∉ torus3 M)
  (hP : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1)
include hPab hstd hx₀ hx₀T hP hexp

theorem not_le_normalizer {U : Subgroup (StatedProj H)} (hU : IsPGroup 2 U)
    (hU16 : 16 ≤ Nat.card U) : ¬ ∀ u ∈ U, ∀ y ∈ P, u * y * u⁻¹ ∈ P := by
  intro hUP
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hcon
    rw [this, Subgroup.card_bot] at hP
    omega
  have : Finite U := Nat.finite_of_card_ne_zero (by omega)
  have : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite U
  have := Fintype.ofFinite P
  let f : U → P := fun u => ⟨u * a * (u : StatedProj H)⁻¹, hUP u u.2 a ha⟩
  obtain ⟨u₁, u₂, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hP]
    omega)
  set u : StatedProj H := (u₂ : StatedProj H)⁻¹ * u₁ with hudef
  have huU : u ∈ U := mul_mem (inv_mem u₂.2) u₁.2
  have hu1 : u ≠ 1 := by
    intro h1
    apply hne
    apply Subtype.ext
    rw [hudef, inv_mul_eq_one] at h1
    exact h1.symm
  have hua : u * a = a * u := by
    have e : (u₁ : StatedProj H) * a * (u₁ : StatedProj H)⁻¹ =
        (u₂ : StatedProj H) * a * (u₂ : StatedProj H)⁻¹ := congrArg Subtype.val hf
    have e2 : u * a * u⁻¹ = a := by
      calc u * a * u⁻¹ = (u₂ : StatedProj H)⁻¹ * ((u₁ : StatedProj H) * a *
            (u₁ : StatedProj H)⁻¹) * u₂ := by rw [hudef]; group
        _ = a := by rw [e]; group
    exact mul_inv_eq_iff_eq_mul.1 e2
  obtain ⟨k, hk⟩ := hU ⟨u, huU⟩
  have hk' : u ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, hj2, hj1⟩ := exists_involution_pow hu1 hk'
  have hvU : u ^ 2 ^ j ∈ U := pow_mem huU _
  have hva : u ^ 2 ^ j * a * (u ^ 2 ^ j)⁻¹ = a := by
    rw [((Commute.pow_left hua (2 ^ j)).eq), mul_inv_cancel_right]
  have hcent := h.centralizes_of_involution hPab hstd hx₀ hx₀T hP hexp hj2 (hUP _ hvU) ha ha1 hva
  exact hj1 (h.eq_one_of_involution_centralizes hPab hstd hx₀ hx₀T hP hj2 fun y hy =>
    mul_inv_eq_iff_eq_mul.1 (hcent y hy))

omit h hstd hx₀ hx₀T in
theorem exists_norm_ne_one {W : Subgroup (StatedProj H)} (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hPW : ∀ y ∈ P, ∀ w ∈ W, y * w * y⁻¹ ∈ W) {w : StatedProj H} (hw : w ∈ W) (hw1 : w ≠ 1) :
    ∃ y ∈ P, y ≠ 1 ∧ ∃ v ∈ W, norm3 y v ≠ 1 := by
  have hWab := commute_of_sq_eq_one hW2
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : P = ⊥ := (Subgroup.eq_bot_iff_forall P).2 hcon
    rw [this, Subgroup.card_bot] at hP
    omega
  obtain ⟨b, hb, hba⟩ : ∃ b ∈ P, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : P ≤ Subgroup.zpowers a := hcon
    have : Nat.card P ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
    rw [hP, Nat.card_zpowers, orderOf_eq_prime (hexp a ha) ha1] at this
    omega
  have hab : Commute a b := hPab a ha b hb
  have hb1 : b ≠ 1 := fun h1 => hba (h1 ▸ one_mem _)
  have hab1 : a * b ≠ 1 := fun h1 => hba (by
    rw [show b = a⁻¹ from (mul_eq_one_iff_inv_eq.1 h1).symm]
    exact inv_mem (Subgroup.mem_zpowers a))
  have ha2b1 : a ^ 2 * b ≠ 1 := fun h1 => hba (by
    rw [show b = (a ^ 2)⁻¹ from (mul_eq_one_iff_inv_eq.1 h1).symm]
    exact inv_mem (pow_mem (Subgroup.mem_zpowers a) 2))
  by_contra hcon
  push Not at hcon
  have hconjW : ∀ g ∈ P, g * w * g⁻¹ ∈ W := fun g hg => hPW g hg w hw
  have hab2 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := hab.mul_pow 2
  have ha2b2 : (a ^ 2 * b) ^ 2 = a * b ^ 2 := by
    rw [(hab.pow_left 2).mul_pow 2, ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ,
      hexp a ha, one_mul]
  have hPa2 : a ^ 2 ∈ P := pow_mem ha 2
  have hPb2 : b ^ 2 ∈ P := pow_mem hb 2
  let _ : CommGroup W :=
    { (inferInstance : Group W) with mul_comm := fun x y => Subtype.ext (hWab x x.2 y y.2) }
  have hW2' : ∀ x : W, x * x = 1 := fun x => Subtype.ext (by
    have := hW2 x x.2
    rw [sq] at this
    exact this)
  have h1 := hcon b hb hb1 w hw
  have h2 := hcon a ha ha1 _ (hconjW b hb)
  have h3 := hcon a ha ha1 _ (hconjW _ hPb2)
  have h4 := hcon (a * b) (mul_mem ha hb) hab1 w hw
  have h5 := hcon (a ^ 2 * b) (mul_mem hPa2 hb) ha2b1 w hw
  unfold norm3 at h1 h2 h3 h4 h5
  rw [hab2] at h4
  rw [ha2b2] at h5
  have e1 : a * (b * w * b⁻¹) * a⁻¹ = (a * b) * w * (a * b)⁻¹ := by group
  have e2 : a ^ 2 * (b * w * b⁻¹) * (a ^ 2)⁻¹ = (a ^ 2 * b) * w * (a ^ 2 * b)⁻¹ := by group
  have e3 : a * (b ^ 2 * w * (b ^ 2)⁻¹) * a⁻¹ = (a * b ^ 2) * w * (a * b ^ 2)⁻¹ := by group
  have e4 : a ^ 2 * (b ^ 2 * w * (b ^ 2)⁻¹) * (a ^ 2)⁻¹ =
      (a ^ 2 * b ^ 2) * w * (a ^ 2 * b ^ 2)⁻¹ := by group
  rw [e1, e2] at h2
  rw [e3, e4] at h3
  have key := eq_one_of_norms hW2' (x₀ := ⟨w, hw⟩) (x₁ := ⟨_, hconjW b hb⟩)
    (x₂ := ⟨_, hconjW _ hPb2⟩) (y₁ := ⟨_, hconjW _ (mul_mem ha hb)⟩)
    (y₂ := ⟨_, hconjW _ (mul_mem hPa2 hb)⟩) (z₁ := ⟨_, hconjW _ (mul_mem ha hPb2)⟩)
    (z₂ := ⟨_, hconjW _ (mul_mem hPa2 hPb2)⟩)
    (Subtype.ext h1) (Subtype.ext h2) (Subtype.ext h3) (Subtype.ext h4) (Subtype.ext h5)
  exact hw1 (congrArg Subtype.val key)

theorem exists_centralizes_of_elemAbelian {W : Subgroup (StatedProj H)} (hW1 : W ≠ ⊥)
    (hW2 : ∀ w ∈ W, w ^ 2 = 1) (hPW : ∀ y ∈ P, ∀ w ∈ W, y * w * y⁻¹ ∈ W) :
    ∃ y ∈ P, y ≠ 1 ∧ (∀ w ∈ W, y * w = w * y) ∧
      ∀ c₁ c₂ : StatedProj H, (∀ w ∈ W, c₁ * w = w * c₁) → (∀ w ∈ W, c₂ * w = w * c₂) →
        c₁ * c₂ = c₂ * c₁ := by
  have hWab := commute_of_sq_eq_one hW2
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hW1 ((Subgroup.eq_bot_iff_forall W).2 hcon)
  obtain ⟨y, hyP, hy1, v, hv, hN⟩ := exists_norm_ne_one hPab hP hexp hW2 hPW hw hw1
  have hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W := hPW y hyP
  set v₁ := norm3 y v with hv₁def
  have hv₁W : v₁ ∈ W := norm3_mem hyW hv
  have hyv₁ : y * v₁ * y⁻¹ = v₁ := conj_norm3 hWab hyW (hexp y hyP) hv
  obtain ⟨z, hzP, hz⟩ : ∃ z ∈ P, z * v₁ * z⁻¹ ≠ v₁ := by
    by_contra hcon
    push Not at hcon
    exact hN (h.eq_one_of_involution_centralizes hPab hstd hx₀ hx₀T hP (hW2 _ hv₁W)
      fun y' hy' => (mul_inv_eq_iff_eq_mul.1 (hcon y' hy')).symm)
  set v₂ := z * v₁ * z⁻¹ with hv₂def
  have hv₂W : v₂ ∈ W := hPW z hzP v₁ hv₁W
  have hyv₂ : y * v₂ * y⁻¹ = v₂ := by
    have hyz : y * z = z * y := hPab y hyP z hzP
    calc y * v₂ * y⁻¹ = z * (y * v₁ * y⁻¹) * z⁻¹ := by
          rw [hv₂def, show y * (z * v₁ * z⁻¹) * y⁻¹ = (y * z) * v₁ * (y * z)⁻¹ by group, hyz]
          group
      _ = v₂ := by rw [hyv₁]
  have hv₂1 : v₂ ≠ 1 := by
    intro h1
    apply hN
    rw [hv₂def] at h1
    calc v₁ = z⁻¹ * (z * v₁ * z⁻¹) * z := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨yt, rfl⟩ := proj_surjective y
  have hyt : yt ∉ scal H := fun hs => hy1 (proj_eq_one_iff.2 hs)
  have hreg := h.isRegular_of_mem hPab hstd hx₀ hx₀T hyP hyt
  obtain ⟨vt₁, hvt₁, hvt₁2⟩ := h.exists_involution_lift (hW2 _ hv₁W)
  obtain ⟨vt₂, hvt₂, hvt₂2⟩ := h.exists_involution_lift (hW2 _ hv₂W)
  have hlift : ∀ (g vt : H), vt ^ 2 = 1 → proj H g * proj H vt = proj H vt * proj H g →
      g * vt = vt * g := by
    intro g vt hvt hc
    exact mul_inv_eq_iff_eq_mul.1 (h.conj_eq_of_involution hvt (by
      rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]))
  have hsq : ∀ vt : H, vt ^ 2 = 1 →
      ((vt : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((vt : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    intro vt hvt
    have := congrArg (fun z : H => ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hvt
    simpa [sq] using this
  have hne1 : ∀ vt : H, proj H vt ≠ 1 → ((vt : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
    intro vt hvt h1
    apply hvt
    have : vt = 1 := Subtype.ext (Units.ext (by simpa using h1))
    rw [this, map_one]
  have hV₁Y := (mat_commute_of_commute (hlift yt vt₁ hvt₁2 (by
    rw [hvt₁]; exact (mul_inv_eq_iff_eq_mul.1 hyv₁)))).symm
  have hV₂Y := (mat_commute_of_commute (hlift yt vt₂ hvt₂2 (by
    rw [hvt₂]; exact (mul_inv_eq_iff_eq_mul.1 hyv₂)))).symm
  have hV₁₂ : ((vt₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      ((vt₂ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro he
    apply hz
    have : vt₁ = vt₂ := Subtype.ext (Units.ext he)
    rw [← hvt₁, ← hvt₂, this]
  have hkey : ∀ g : H, (∀ w ∈ W, proj H g * w = w * proj H g) →
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((yt : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((yt : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro g hg
    have hg₁ := hlift g vt₁ hvt₁2 (by rw [hvt₁]; exact hg v₁ hv₁W)
    have hg₂ := hlift g vt₂ hvt₂2 (by rw [hvt₂]; exact hg v₂ hv₂W)
    exact IsRegular.commute_of_involutions h.two hreg (hsq vt₁ hvt₁2) (hsq vt₂ hvt₂2)
      (h.det_eq_one vt₁) (h.det_eq_one vt₂) (hne1 vt₁ (by rw [hvt₁]; exact hN))
      (hne1 vt₂ (by rw [hvt₂]; exact hv₂1)) hV₁₂ hV₁Y hV₂Y (mat_commute_of_commute hg₁)
      (mat_commute_of_commute hg₂)
  refine ⟨proj H yt, hyP, hy1, fun w hw => ?_, fun c₁ c₂ hc₁ hc₂ => ?_⟩
  · obtain ⟨wt, rfl⟩ := proj_surjective w
    have e := commute_of_mat_commute (hkey wt fun w' hw' => hWab _ hw _ hw')
    rw [← map_mul, ← map_mul, e]
  · obtain ⟨g₁, rfl⟩ := proj_surjective c₁
    obtain ⟨g₂, rfl⟩ := proj_surjective c₂
    have e := commute_of_mat_commute (hreg.commute_of_commute (hkey g₁ hc₁) (hkey g₂ hc₂))
    rw [← map_mul, ← map_mul, e]

theorem exists_normal_three {U : Subgroup (StatedProj H)} {n : ℕ}
    (hG₀card : Nat.card (P ⊔ U : Subgroup (StatedProj H)) = 3 ^ 2 * 2 ^ n) :
    ∃ R : Subgroup (StatedProj H), R ≤ P ⊔ U ∧ R ≠ ⊥ ∧ (∀ r ∈ R, r ^ 9 = 1) ∧
      ∀ g ∈ P ⊔ U, ∀ r ∈ R, g * r * g⁻¹ ∈ R := by
  classical
  set G₀ := P ⊔ U with hG₀def
  have hG₀fin : Finite G₀ := Nat.finite_of_card_ne_zero (by rw [hG₀card]; positivity)
  have hsolv : Group.IsSolvable G₀ := by
    have := Fintype.ofFinite G₀
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_three Nat.prime_two (by norm_num) (by rw [← Nat.card_eq_fintype_card, hG₀card])
  have hG₀bot : G₀ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hG₀card
    have : 0 < 3 ^ 2 * 2 ^ n := by positivity
    omega
  have hPG : P ≤ G₀ := le_sup_left
  obtain ⟨A, hAG, hA1, hAab, hAn⟩ :=
    CFSG.LinearGroups.exists_abelian_normalized_of_isSolvable G₀ hG₀bot
  have hconjpow : ∀ (g r : StatedProj H) (k : ℕ), r ^ k = 1 → (g * r * g⁻¹) ^ k = 1 := by
    intro g r k hr
    rw [conj_pow, hr, mul_one, mul_inv_cancel]
  by_cases h3 : ∃ a ∈ A, a ≠ 1 ∧ a ^ 9 = 1
  · obtain ⟨a, ha, ha1, ha9⟩ := h3
    refine ⟨powSubgroup A hAab 9, fun x hx => hAG hx.1, ?_, fun r hr => hr.2,
      fun g hg r hr => ⟨hAn g hg r hr.1, hconjpow g r 9 hr.2⟩⟩
    intro hbot
    apply ha1
    have : a ∈ powSubgroup A hAab 9 := ⟨ha, ha9⟩
    rw [hbot] at this
    exact this
  · push Not at h3
    have h2 : ∀ a ∈ A, a ^ 2 ^ n = 1 := by
      intro a ha
      by_contra hne
      apply h3 (a ^ 2 ^ n) (pow_mem ha _) hne
      rw [← pow_mul, mul_comm, show 9 * 2 ^ n = Nat.card G₀ by rw [hG₀card]; ring]
      have := congrArg Subtype.val (pow_card_eq_one' (G := G₀) (x := ⟨a, hAG ha⟩))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    set W := powSubgroup A hAab 2 with hWdef
    have hW1 : W ≠ ⊥ := by
      obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hA1 ((Subgroup.eq_bot_iff_forall A).2 hcon)
      obtain ⟨j, hj2, hj1⟩ := exists_involution_pow ha1 (h2 a ha)
      intro hbot
      have : a ^ 2 ^ j ∈ W := ⟨pow_mem ha _, hj2⟩
      rw [hbot] at this
      exact hj1 this
    have hW2 : ∀ w ∈ W, w ^ 2 = 1 := fun w hw => hw.2
    have hGW : ∀ g ∈ G₀, ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
      ⟨hAn g hg w hw.1, hconjpow g w 2 hw.2⟩
    obtain ⟨y, hyP, hy1, hyW, hCab⟩ := h.exists_centralizes_of_elemAbelian hPab hstd hx₀ hx₀T
      hP hexp hW1 hW2 fun y hy => hGW y (hPG hy)
    set C := G₀ ⊓ Subgroup.centralizer (W : Set (StatedProj H)) with hCdef
    have hmemC : ∀ c ∈ C, ∀ w ∈ W, c * w = w * c := fun c hc w hw =>
      ((Subgroup.mem_centralizer_iff.1 hc.2) w hw).symm
    have hCab' : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
      hCab a b (hmemC a ha) (hmemC b hb)
    refine ⟨powSubgroup C hCab' 9, fun x hx => hx.1.1, ?_, fun r hr => hr.2, ?_⟩
    · intro hbot
      apply hy1
      have : y ∈ powSubgroup C hCab' 9 := ⟨⟨hPG hyP, Subgroup.mem_centralizer_iff.2
        fun w hw => (hyW w hw).symm⟩, by
          rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hexp y hyP, one_pow]⟩
      rw [hbot] at this
      exact this
    · intro g hg r hr
      refine ⟨⟨G₀.mul_mem (G₀.mul_mem hg hr.1.1) (G₀.inv_mem hg),
        Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩, hconjpow g r 9 hr.2⟩
      have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ W := hGW _ (G₀.inv_mem hg) w hw
      rw [inv_inv] at hw'
      have hrw := hmemC r hr.1 _ hw'
      calc w * (g * r * g⁻¹) = g * ((g⁻¹ * w * g) * r) * g⁻¹ := by group
        _ = g * (r * (g⁻¹ * w * g)) * g⁻¹ := by rw [hrw]
        _ = g * r * g⁻¹ * w := by group

theorem nontoral {U : Subgroup (StatedProj H)} (hU : IsPGroup 2 U) (hU16 : 16 ≤ Nat.card U)
    (hcard : Nat.card (P ⊔ U : Subgroup (StatedProj H)) = 9 * Nat.card U) :
    ∃ Q : Subgroup (StatedProj H), Q ≤ P ∧ Nat.card Q = 3 ∧ ∀ α : StatedProj H ≃* StatedProj H,
      P.map α.toMonoidHom = P → U.map α.toMonoidHom = U → Q.map α.toMonoidHom = Q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUfin : Finite U := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hU
  have hG₀card : Nat.card (P ⊔ U : Subgroup (StatedProj H)) = 3 ^ 2 * 2 ^ n := by
    rw [hcard, hn]
    norm_num
  have hG₀fin : Finite (P ⊔ U : Subgroup (StatedProj H)) :=
    Nat.finite_of_card_ne_zero (by rw [hG₀card]; positivity)
  have hPG : P ≤ P ⊔ U := le_sup_left
  have hUG : U ≤ P ⊔ U := le_sup_right
  have hnot := h.not_le_normalizer hPab hstd hx₀ hx₀T hP hexp hU hU16
  obtain ⟨R, hRG, hR1, hR9, hRn⟩ := h.exists_normal_three hPab hstd hx₀ hx₀T hP hexp hG₀card
  have hRP : R ≤ P := by
    have hR3 : IsPGroup 3 R := fun r => ⟨2, Subtype.ext (by simpa using hR9 r r.2)⟩
    have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP]; norm_num)
    have hPn : P ≤ Subgroup.normalizer (R : Set (StatedProj H)) := fun g hg =>
      mem_normalizer_of_conj (hRn g (hPG hg)) (hRn g⁻¹ (inv_mem (hPG hg)))
    have hRP3 := hR3.to_sup_of_normal_left' hP3 hPn
    have hle : R ⊔ P ≤ P ⊔ U := sup_le hRG hPG
    have hfin : Finite (R ⊔ P : Subgroup (StatedProj H)) := inferInstance
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hRP3
    have hdvd : 3 ^ m ∣ 3 ^ 2 * 2 ^ n := hm ▸ hG₀card ▸ Subgroup.card_dvd_of_le hle
    have hdvd' : 3 ^ m ∣ 3 ^ 2 :=
      (Nat.Coprime.pow _ _ (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right hdvd
    have hle9 : Nat.card (R ⊔ P : Subgroup (StatedProj H)) ≤ 9 := by
      rw [hm]
      exact Nat.le_of_dvd (by norm_num) hdvd'
    have heq : P = R ⊔ P := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hP]; exact hle9)
    rw [heq]
    exact le_sup_left
  have hRneP : R ≠ P := by
    rintro rfl
    exact hnot fun u hu y hy => hRn u (hUG hu) y hy
  have hR3 : Nat.card R = 3 := card_eq_three_of_lt hP hRP hR1 hRneP
  refine ⟨R, hRP, hR3, fun α hαP hαU => ?_⟩
  have hαG : (P ⊔ U).map α.toMonoidHom = P ⊔ U := by rw [Subgroup.map_sup, hαP, hαU]
  have hR'P : R.map α.toMonoidHom ≤ P := by
    rw [← hαP]
    exact Subgroup.map_mono hRP
  have hR'3 : Nat.card (R.map α.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective α.injective, hR3]
  have hR'n : ∀ g ∈ P ⊔ U, ∀ r ∈ R.map α.toMonoidHom, g * r * g⁻¹ ∈ R.map α.toMonoidHom := by
    intro g hg r hr
    rw [← hαG] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨r', hr', rfl⟩ := hr
    exact ⟨g' * r' * g'⁻¹, hRn g' hg' r' hr', by simp only [map_mul, map_inv]⟩
  by_contra hne
  have hsup := sup_eq_of_card_three hP hR'P hRP hR'3 hR3 hne
  apply hnot
  intro u hu y hy
  rw [← hsup] at hy ⊢
  exact conj_mem_sup (fun a ha => Subgroup.mem_sup_left (hR'n u (hUG hu) a ha))
    (fun b hb => Subgroup.mem_sup_right (hRn u (hUG hu) b hb)) y hy

end HeisMain

end OddModel

end CFSG.Quasithin.F134.LieOdd
