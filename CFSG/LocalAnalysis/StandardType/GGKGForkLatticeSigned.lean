module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative

private abbrev ggKGSg_V (p k : ℕ) := Fin k → Multiplicative (ZMod p)

private def ggKGSg_red {p k : ℕ} (y : Fin k → ℤ) : ggKGSg_V p k :=
  fun j => Multiplicative.ofAdd ((y j : ZMod p))

private theorem ggKGSg_red_apply {p k : ℕ} (y : Fin k → ℤ) (j : Fin k) :
    ggKGSg_red (p := p) y j = Multiplicative.ofAdd ((y j : ZMod p)) := rfl

private theorem ggKGSg_red_zero {p k : ℕ} : ggKGSg_red (p := p) (k := k) 0 = 1 := by
  funext j
  simp [ggKGSg_red]

private theorem ggKGSg_red_add {p k : ℕ} (y z : Fin k → ℤ) :
    ggKGSg_red (p := p) (y + z) = ggKGSg_red y * ggKGSg_red z := by
  funext j
  simp [ggKGSg_red, Pi.mul_apply, Int.cast_add]

private noncomputable def ggKGSg_d {p k : ℕ} (u : MulAut (ggKGSg_V p k)) :
    ggKGSg_V p k →* ggKGSg_V p k where
  toFun f := u f * f⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    simp [mul_assoc, mul_left_comm, mul_comm]

private theorem ggKGSg_d_apply {p k : ℕ} (u : MulAut (ggKGSg_V p k)) (f : ggKGSg_V p k) :
    ggKGSg_d u f = u f * f⁻¹ := rfl

private theorem ggKGSg_d_ker_card {p k : ℕ} (u : MulAut (ggKGSg_V p k)) :
    Nat.card (ggKGSg_d u).ker = Nat.card {f : ggKGSg_V p k // u f = f} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  rw [MonoidHom.mem_ker, ggKGSg_d_apply, mul_inv_eq_one, eq_comm]

private noncomputable def ggKGSg_pi {p k : ℕ} {L' : Type} [Group L'] {A : Subgroup L'}
    (Θ : ggKGSg_V p k ≃* ↥A) :
    (Fin k → ℤ) →+ Additive ↥A where
  toFun y := Additive.ofMul (Θ (ggKGSg_red y))
  map_zero' := by simp [ggKGSg_red_zero]
  map_add' y z := by simp [ggKGSg_red_add, map_mul]


private theorem ggKGSg_latForm_one {k : ℕ} :
    GGLatForm (1 : Matrix (Fin k) (Fin k) ℤ) := by
  refine ⟨Matrix.transpose_one, fun y hy => ?_⟩
  rw [Matrix.one_mulVec]
  simpa using (Matrix.dotProduct_self_star_pos_iff (v := y)).mpr hy

private theorem ggKGSg_cartan_one {k : ℕ} (y w : Fin k → ℤ) :
    ggLatCartan (1 : Matrix (Fin k) (Fin k) ℤ) y w =
      2 * dotProduct y w / dotProduct w w := by
  unfold ggLatCartan
  rw [Matrix.one_mulVec]

private theorem ggKGSg_cartan_single {k : ℕ} (i : Fin k) (y : Fin k → ℤ) :
    ggLatCartan (1 : Matrix (Fin k) (Fin k) ℤ) y (Pi.single i (1 : ℤ)) = 2 * y i := by
  rw [ggKGSg_cartan_one]
  have h1 : dotProduct y (Pi.single i (1 : ℤ)) = y i := dotProduct_single_one y i
  have h2 : dotProduct (Pi.single i (1 : ℤ)) (Pi.single i (1 : ℤ)) = 1 := by
    rw [dotProduct_single_one]
    simp
  rw [h1, h2, Int.ediv_one]

private theorem ggKGSg_refl_single {k : ℕ} (i : Fin k) (y : Fin k → ℤ) :
    ggLatRefl (1 : Matrix (Fin k) (Fin k) ℤ) (Pi.single i (1 : ℤ)) y =
      Function.update y i (- y i) := by
  funext l
  rw [ggLatRefl, ggKGSg_cartan_single]
  by_cases hl : l = i
  · subst hl
    simp [Pi.single_apply]
    ring
  · simp [Pi.single_apply, Function.update_of_ne hl, hl]

private theorem ggKGSg_cartan_sub {k : ℕ} {i j : Fin k} (hij : i ≠ j) (y : Fin k → ℤ) :
    ggLatCartan (1 : Matrix (Fin k) (Fin k) ℤ) y
        (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) = y i - y j := by
  rw [ggKGSg_cartan_one]
  have h1 : dotProduct y (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) = y i - y j := by
    rw [dotProduct_sub, dotProduct_single_one, dotProduct_single_one]
  have h2 : dotProduct (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ))
      (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) = (2 : ℤ) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
    simp [dotProduct_single_one, single_dotProduct, Pi.single_apply, Pi.sub_apply, hij,
      Ne.symm hij]
  rw [h1, h2]
  exact Int.mul_ediv_cancel_left (y i - y j) (by norm_num)

private theorem ggKGSg_refl_sub {k : ℕ} {i j : Fin k} (hij : i ≠ j) (y : Fin k → ℤ) :
    ggLatRefl (1 : Matrix (Fin k) (Fin k) ℤ)
        (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) y =
      fun l => if l = i then y j else if l = j then y i else y l := by
  funext l
  rw [ggLatRefl, ggKGSg_cartan_sub hij]
  by_cases hi : l = i
  · subst hi
    simp [Pi.single_apply, Pi.sub_apply, hij]
  · by_cases hj : l = j
    · subst hj
      simp [Pi.single_apply, Pi.sub_apply, hi, Ne.symm hij]
    · simp [Pi.single_apply, Pi.sub_apply, hi, hj]

private theorem ggKGSg_cartan_add {k : ℕ} {i j : Fin k} (hij : i ≠ j) (y : Fin k → ℤ) :
    ggLatCartan (1 : Matrix (Fin k) (Fin k) ℤ) y
        (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)) = y i + y j := by
  rw [ggKGSg_cartan_one]
  have h1 : dotProduct y (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)) = y i + y j := by
    rw [dotProduct_add, dotProduct_single_one, dotProduct_single_one]
  have h2 : dotProduct (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ))
      (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)) = (2 : ℤ) := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add]
    simp [dotProduct_single_one, single_dotProduct, Pi.single_apply, Pi.add_apply, hij,
      Ne.symm hij]
  rw [h1, h2]
  exact Int.mul_ediv_cancel_left (y i + y j) (by norm_num)

private theorem ggKGSg_refl_add {k : ℕ} {i j : Fin k} (hij : i ≠ j) (y : Fin k → ℤ) :
    ggLatRefl (1 : Matrix (Fin k) (Fin k) ℤ)
        (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)) y =
      fun l => if l = i then - y j else if l = j then - y i else y l := by
  funext l
  rw [ggLatRefl, ggKGSg_cartan_add hij]
  by_cases hi : l = i
  · subst hi
    simp [Pi.single_apply, Pi.add_apply, hij]
  · by_cases hj : l = j
    · subst hj
      simp [Pi.single_apply, Pi.add_apply, hi, Ne.symm hij]
    · simp [Pi.single_apply, Pi.add_apply, hi, hj]

private theorem ggKGSg_root_single {k : ℕ} (i : Fin k) :
    GGLatRoot (1 : Matrix (Fin k) (Fin k) ℤ) (Pi.single i (1 : ℤ)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := congrFun h i
    simp at h1
  · intro y
    rw [Matrix.one_mulVec]
    have h : dotProduct (Pi.single i (1 : ℤ)) (Pi.single i (1 : ℤ)) = 1 := by
      rw [dotProduct_single_one]
      simp
    rw [h]
    exact one_dvd _

private theorem ggKGSg_root_sub {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    GGLatRoot (1 : Matrix (Fin k) (Fin k) ℤ)
      (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := congrFun h i
    simp [hij] at h1
  · intro y
    rw [Matrix.one_mulVec]
    have h : dotProduct (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ))
        (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) = (2 : ℤ) := by
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
      simp [dotProduct_single_one, single_dotProduct, Pi.single_apply, Pi.sub_apply, hij,
        Ne.symm hij]
    rw [h]
    exact ⟨_, rfl⟩

private theorem ggKGSg_root_add {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    GGLatRoot (1 : Matrix (Fin k) (Fin k) ℤ)
      (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := congrFun h i
    simp [hij] at h1
  · intro y
    rw [Matrix.one_mulVec]
    have h : dotProduct (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ))
        (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)) = (2 : ℤ) := by
      rw [add_dotProduct, dotProduct_add, dotProduct_add]
      simp [dotProduct_single_one, single_dotProduct, Pi.single_apply, Pi.add_apply, hij,
        Ne.symm hij]
    rw [h]
    exact ⟨_, rfl⟩

private theorem ggKGSg_pi_apply {p k : ℕ} {L' : Type} [Group L'] {A : Subgroup L'}
    (Θ : ggKGSg_V p k ≃* ↥A) (y : Fin k → ℤ) :
    ggKGSg_pi (p := p) (k := k) Θ y = Additive.ofMul (Θ (ggKGSg_red y)) := rfl

private theorem ggKGSg_pi_surjective {p k : ℕ} {L' : Type} [Group L'] {A : Subgroup L'}
    (Θ : ggKGSg_V p k ≃* ↥A) :
    Function.Surjective (ggKGSg_pi (p := p) (k := k) Θ) := by
  intro a
  obtain ⟨f, hf⟩ := Θ.surjective (Additive.toMul a)
  refine ⟨fun i => (ZMod.intCast_surjective (toAdd (f i))).choose, ?_⟩
  have hred : ggKGSg_red (p := p) (fun i => (ZMod.intCast_surjective (toAdd (f i))).choose) = f := by
    funext i
    apply toAdd.injective
    rw [ggKGSg_red_apply, toAdd_ofAdd]
    exact (ZMod.intCast_surjective (toAdd (f i))).choose_spec
  rw [ggKGSg_pi_apply, hred, hf]
  rfl


private def ggKGSg_delta {p k : ℕ} (i : Fin k) : ggKGSg_V p k :=
  Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))

private theorem ggKGSg_delta_def {p k : ℕ} (i : Fin k) :
    ggKGSg_delta (p := p) i =
      Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p)) := rfl

private theorem ggKGSg_d_mulSingle_apply {p k : ℕ} {u : MulAut (ggKGSg_V p k)}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hπ : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (i j : Fin k) :
    toAdd (ggKGSg_d u (ggKGSg_delta i) j) =
      (if j = π i then ε i else 0) + (if j = i then -1 else 0) := by
  rw [ggKGSg_delta_def, ggKGSg_d_apply, toAdd_mul_apply, toAdd_inv_apply,
    IsSignedPerm.apply_mulSingle hπ i 1, toAdd_mulSingle, toAdd_mulSingle]
  by_cases h1 : j = π i <;> by_cases h2 : j = i <;> by_cases h3 : π i = i <;>
    simp [h1, h2, h3]

private theorem ggKGSg_range_card {p k : ℕ} (hp : p.Prime) {u : MulAut (ggKGSg_V p k)}
    (hcard : Nat.card {f : ggKGSg_V p k // u f = f} * p = Nat.card (ggKGSg_V p k)) :
    Nat.card (ggKGSg_d u).range = p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hK : Nat.card (ggKGSg_d u).ker = Nat.card {f : ggKGSg_V p k // u f = f} :=
    ggKGSg_d_ker_card u
  have hV : Nat.card (ggKGSg_V p k) =
      Nat.card (ggKGSg_d u).range * Nat.card (ggKGSg_d u).ker :=
    (TableB.card_range_mul_card_ker _).symm
  have h1 : Nat.card (ggKGSg_d u).range * Nat.card (ggKGSg_d u).ker =
      Nat.card (ggKGSg_d u).ker * p := by
    rw [← hV, hK]
    exact hcard.symm
  have h2 : Nat.card (ggKGSg_d u).range * Nat.card (ggKGSg_d u).ker =
      p * Nat.card (ggKGSg_d u).ker := by
    rw [h1, mul_comm]
  have hKpos : 0 < Nat.card (ggKGSg_d u).ker := by
    haveI : Nonempty (ggKGSg_d u).ker := ⟨⟨1, (ggKGSg_d u).ker.one_mem⟩⟩
    exact Nat.card_pos
  exact Nat.mul_right_cancel hKpos h2

private theorem ggKGSg_coord_supp {p k : ℕ} (hp : p.Prime) {x y : ggKGSg_V p k}
    (hy : y ≠ 1) (hpow : ∃ c : ℕ, x ^ c = y) :
    ∀ j, toAdd (y j) = 0 ↔ toAdd (x j) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := hpow
  have hc0 : ((c : ℕ) : ZMod p) ≠ 0 := by
    intro hc0
    apply hy
    funext j
    apply toAdd.injective
    have h1 : toAdd (y j) = ((c : ℕ) : ZMod p) * toAdd (x j) := by
      rw [← hc]
      exact toAdd_pow_apply x c j
    rw [h1, hc0, zero_mul]
    simp
  intro j
  have h1 : toAdd (y j) = ((c : ℕ) : ZMod p) * toAdd (x j) := by
    rw [← hc]
    exact toAdd_pow_apply x c j
  rw [h1]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left hc0, fun ha => by rw [ha, mul_zero]⟩

private theorem ggKGSg_mem_supp_self {p k : ℕ} (hp : p.Prime) {u : MulAut (ggKGSg_V p k)}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hπ : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i)) (j : Fin k)
    (hj : ggKGSg_d u (ggKGSg_delta j) ≠ 1) :
    toAdd (ggKGSg_d u (ggKGSg_delta j) j) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hpj : π j = j
  · intro h0
    apply hj
    apply eq_of_toAdd_eq
    intro l
    rw [ggKGSg_d_mulSingle_apply hπ]
    by_cases hl : l = j
    · subst hl
      rw [ggKGSg_d_mulSingle_apply hπ] at h0
      simpa using h0
    · have h1 : l ≠ π j := by rw [hpj]; exact hl
      simp [hl, h1]
  · rw [ggKGSg_d_mulSingle_apply hπ]
    have h1 : ¬ (j = π j) := fun h => hpj h.symm
    have hne : ((-1 : ZMod p)) ≠ 0 := coord_sign_ne_zero hp (Or.inr rfl)
    simpa [h1] using hne

private theorem ggKGSg_d_eq_one_iff {p k : ℕ} (hp : p.Prime) {u : MulAut (ggKGSg_V p k)}
    {π : Equiv.Perm (Fin k)} {ε : Fin k → ZMod p}
    (hπ : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (j : Fin k) :
    ggKGSg_d u (ggKGSg_delta j) = 1 ↔ π j = j ∧ ε j = 1 := by
  constructor
  · intro h
    have huδ : u (ggKGSg_delta j) = ggKGSg_delta j := by
      rw [ggKGSg_d_apply] at h
      exact mul_inv_eq_one.mp h
    rw [ggKGSg_delta_def, IsSignedPerm.apply_mulSingle hπ j 1] at huδ
    simp only [mul_one] at huδ
    exact mulSingle_ofAdd_eq_iff (coord_sign_ne_zero hp (hε j)) huδ
  · rintro ⟨h1, h2⟩
    apply eq_of_toAdd_eq
    intro l
    rw [ggKGSg_d_mulSingle_apply hπ]
    by_cases hl : l = j
    · subst hl
      simp [h1, h2]
    · have hl' : l ≠ π j := by rw [h1]; exact hl
      simp [hl, hl']


private theorem ggKGSg_congr_apply {p k : ℕ} {L' : Type} [Group L'] {A : Subgroup L'}
    (Θ : ggKGSg_V p k ≃* ↥A) (u : MulAut (ggKGSg_V p k)) (f : ggKGSg_V p k) :
    (MulAut.congr Θ u) (Θ f) = Θ (u f) := by
  rw [MulAut.congr_apply]
  simp

private theorem ggKGSg_classify {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (ggKGSg_V p k)} (hu : IsSignedPerm ⇑u) (hu2 : u * u = 1)
    (hcard : Nat.card {f : ggKGSg_V p k // u f = f} * p = Nat.card (ggKGSg_V p k)) :
    ∃ w : Fin k → ℤ, GGLatRoot (1 : Matrix (Fin k) (Fin k) ℤ) w ∧
      ∀ y : Fin k → ℤ, u (ggKGSg_red y) = ggKGSg_red (ggLatRefl (1 : Matrix (Fin k) (Fin k) ℤ) w y) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨π, ε, hε, hπ⟩ := hu
  have hrange : Nat.card (ggKGSg_d u).range = p := ggKGSg_range_card hp hcard
  have hex : ∃ i, ggKGSg_d u (ggKGSg_delta i) ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hd : ggKGSg_d u = 1 := by
      apply hom_ext_mulSingle
      intro i
      have h := hall i
      rw [ggKGSg_delta_def] at h
      simpa only [MonoidHom.one_apply] using h
    have hr : (ggKGSg_d u).range = ⊥ := by
      rw [hd]
      ext x
      simp [MonoidHom.mem_range, eq_comm]
    have h1 : Nat.card (ggKGSg_d u).range = 1 := by
      rw [hr]
      exact Subgroup.card_bot
    rw [hrange] at h1
    exact hp.ne_one h1
  obtain ⟨i0, hi0⟩ := hex
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : ∀ i, ggKGSg_d u (ggKGSg_delta i) ≠ 1 →
      ∃ c : ℕ, (ggKGSg_d u (ggKGSg_delta i0)) ^ c = ggKGSg_d u (ggKGSg_delta i) := by
    intro i hi
    have h := mem_powers_of_prime_card (G := (ggKGSg_d u).range) hrange
      (g := ⟨ggKGSg_d u (ggKGSg_delta i0), ⟨ggKGSg_delta i0, rfl⟩⟩)
      (g' := ⟨ggKGSg_d u (ggKGSg_delta i), ⟨ggKGSg_delta i, rfl⟩⟩)
      (by intro hc; exact hi0 (congrArg Subtype.val hc))
    obtain ⟨c, hc⟩ := h
    exact ⟨c, congrArg Subtype.val hc⟩
  have hsupp : ∀ i, ggKGSg_d u (ggKGSg_delta i) ≠ 1 →
      ∀ j, toAdd (ggKGSg_d u (ggKGSg_delta i) j) = 0 ↔
        toAdd (ggKGSg_d u (ggKGSg_delta i0) j) = 0 := by
    intro i hi j
    exact ggKGSg_coord_supp hp hi (hpow i hi) j
  have hx0 : ∀ j, toAdd (ggKGSg_d u (ggKGSg_delta i0) j) =
      (if j = π i0 then ε i0 else 0) + (if j = i0 then -1 else 0) := by
    intro j
    exact ggKGSg_d_mulSingle_apply hπ i0 j
  have hmem := fun (j : Fin k) (hj : ggKGSg_d u (ggKGSg_delta j) ≠ 1) =>
    ggKGSg_mem_supp_self hp hπ j hj
  by_cases hfix : π i0 = i0
  ·
    have hε0 : ε i0 = -1 := by
      rcases hε i0 with h | h
      · exfalso
        apply hi0
        apply eq_of_toAdd_eq
        intro j
        rw [ggKGSg_d_mulSingle_apply hπ]
        by_cases hj : j = i0
        · subst hj
          simp [hfix, h]
        · have hj' : j ≠ π i0 := by rw [hfix]; exact hj
          simp [hj, hj']
      · exact h
    have htriv : ∀ j, j ≠ i0 → ggKGSg_d u (ggKGSg_delta j) = 1 := by
      intro j hj
      by_contra hdj
      have hmemj : toAdd (ggKGSg_d u (ggKGSg_delta j) j) ≠ 0 := hmem j hdj
      have hsuppj := hsupp j hdj j
      have hx0j : toAdd (ggKGSg_d u (ggKGSg_delta i0) j) = 0 := by
        rw [hx0 j]
        have hj' : j ≠ π i0 := by rw [hfix]; exact hj
        simp [hj, hj']
      exact hmemj ((hsuppj).mpr hx0j)
    have hfx : ∀ j, j ≠ i0 → π j = j ∧ ε j = 1 := by
      intro j hj
      exact (ggKGSg_d_eq_one_iff hp hπ hε j).mp (htriv j hj)
    refine ⟨Pi.single i0 (1 : ℤ), ggKGSg_root_single i0, ?_⟩
    intro y
    rw [ggKGSg_refl_single]
    have hπapply : ∀ l, π l = l := by
      intro l
      by_cases hl : l = i0
      · subst hl
        exact hfix
      · exact (hfx l hl).1
    have hπinv : ∀ l, π.symm l = l := by
      intro l
      rw [Equiv.symm_apply_eq]
      exact (hπapply l).symm
    have hεv : ∀ l, ε l = if l = i0 then -1 else 1 := by
      intro l
      by_cases hl : l = i0
      · subst hl
        simp [hε0]
      · simp [hl, (hfx l hl).2]
    refine eq_of_toAdd_eq fun l => ?_
    have happ : toAdd (u (ggKGSg_red y) l) =
        ε (π.symm l) * toAdd (ggKGSg_red y (π.symm l)) := by
      have h := hπ (ggKGSg_red y) (π.symm l)
      simpa using h
    rw [happ, hπinv l, hεv l, ggKGSg_red_apply, ggKGSg_red_apply, toAdd_ofAdd]
    by_cases hl : l = i0
    · subst hl
      simp [Function.update_self]
      exact neg_one_mul _
    · simp [Function.update_of_ne hl, hl]
  ·
    set i1 : Fin k := π i0 with hi1def
    have hi1 : i1 ≠ i0 := by rw [hi1def]; exact hfix
    have hπi0 : π i0 = i1 := hi1def.symm
    have hx0i0 : toAdd (ggKGSg_d u (ggKGSg_delta i0) i0) = -1 := by
      rw [hx0 i0, if_neg (Ne.symm hi1), if_pos rfl]
      ring
    have hx0i1 : toAdd (ggKGSg_d u (ggKGSg_delta i0) i1) = ε i0 := by
      rw [hx0 i1, if_pos rfl, if_neg hi1]
      ring
    have hx0out : ∀ j, j ≠ i0 → j ≠ i1 →
        toAdd (ggKGSg_d u (ggKGSg_delta i0) j) = 0 := by
      intro j hj0 hj1
      rw [hx0 j, if_neg hj1, if_neg hj0]
      ring
    have htriv : ∀ j, j ≠ i0 → j ≠ i1 → ggKGSg_d u (ggKGSg_delta j) = 1 := by
      intro j hj0 hj1
      by_contra hdj
      have hmemj : toAdd (ggKGSg_d u (ggKGSg_delta j) j) ≠ 0 := hmem j hdj
      have hsuppj := hsupp j hdj j
      have hx0j : toAdd (ggKGSg_d u (ggKGSg_delta i0) j) = 0 := hx0out j hj0 hj1
      exact hmemj ((hsuppj).mpr hx0j)
    have hfx : ∀ j, j ≠ i0 → j ≠ i1 → π j = j ∧ ε j = 1 := by
      intro j hj0 hj1
      exact (ggKGSg_d_eq_one_iff hp hπ hε j).mp (htriv j hj0 hj1)
    have hπi1 : π i1 = i0 := by
      by_contra hne
      have h1 : π i1 ≠ i0 := hne
      have h2 : π i1 ≠ i1 := by
        intro h
        have hh : π i1 = π i0 := by rw [h, hπi0]
        exact hi1 (π.injective hh)
      have hfixj := hfx (π i1) h1 h2
      exact h2 (π.injective hfixj.1)
    have hεrel : ε i1 * ε i0 = 1 := by
      have hu2' : ∀ f, u (u f) = f := by
        intro f
        have h := congrArg (fun g : MulAut (ggKGSg_V p k) => g f) hu2
        simpa using h
      have h := hu2' (ggKGSg_delta i0)
      rw [ggKGSg_delta_def] at h
      rw [IsSignedPerm.apply_mulSingle hπ i0 1, mul_one,
        IsSignedPerm.apply_mulSingle hπ i1 (ε i0), hπi1] at h
      have h2 := congrArg (fun f => toAdd (f i0)) h
      simpa [toAdd_mulSingle] using h2
    have hπinv : ∀ l, π.symm l = if l = i0 then i1 else if l = i1 then i0 else l := by
      intro l
      by_cases h0 : l = i0
      · have hR : (if l = i0 then i1 else if l = i1 then i0 else l) = i1 := by simp [h0]
        rw [hR, h0, Equiv.symm_apply_eq, hπi1]
      · by_cases h1 : l = i1
        · have hR : (if l = i0 then i1 else if l = i1 then i0 else l) = i0 := by simp [h0, h1]
          rw [hR, h1, Equiv.symm_apply_eq]
        · have hR : (if l = i0 then i1 else if l = i1 then i0 else l) = l := by simp [h0, h1]
          rw [hR, Equiv.symm_apply_eq]
          exact ((hfx l h0 h1).1).symm
    rcases hε i0 with hε0 | hε0
    ·
      have hε1 : ε i1 = 1 := by
        rw [hε0] at hεrel
        simpa using hεrel
      have hεall : ∀ l, ε l = 1 := by
        intro l
        by_cases h0 : l = i0
        · rw [h0, hε0]
        · by_cases h1 : l = i1
          · rw [h1, hε1]
          · exact (hfx l h0 h1).2
      refine ⟨Pi.single i0 (1 : ℤ) - Pi.single i1 (1 : ℤ), ggKGSg_root_sub (Ne.symm hi1), ?_⟩
      intro y
      rw [ggKGSg_refl_sub (Ne.symm hi1)]
      refine eq_of_toAdd_eq fun l => ?_
      have happ : toAdd (u (ggKGSg_red y) l) =
          ε (π.symm l) * toAdd (ggKGSg_red y (π.symm l)) := by
        have h := hπ (ggKGSg_red y) (π.symm l)
        simpa using h
      rw [happ, hπinv l, hεall, ggKGSg_red_apply, ggKGSg_red_apply, toAdd_ofAdd]
      by_cases h0 : l = i0
      · subst h0
        simp
      · by_cases h1 : l = i1
        · subst h1
          simp [h0]
        · simp [h0, h1]
    ·
      have hε1 : ε i1 = -1 := by
        rcases hε i1 with h | h
        · rw [hε0, h] at hεrel
          have h2 : (2 : ZMod p) = 0 := by linear_combination -hεrel
          exact absurd h2 (coord_two_ne_zero hp hp2)
        · exact h
      have hεall : ∀ l, ε l = if l = i0 then -1 else if l = i1 then -1 else 1 := by
        intro l
        by_cases h0 : l = i0
        · subst h0
          simp [hε0]
          rfl
        · by_cases h1 : l = i1
          · subst h1
            simp [hε1]
          · simp [h0, h1, (hfx l h0 h1).2]
      refine ⟨Pi.single i0 (1 : ℤ) + Pi.single i1 (1 : ℤ), ggKGSg_root_add (Ne.symm hi1), ?_⟩
      intro y
      rw [ggKGSg_refl_add (Ne.symm hi1)]
      refine eq_of_toAdd_eq fun l => ?_
      have happ : toAdd (u (ggKGSg_red y) l) =
          ε (π.symm l) * toAdd (ggKGSg_red y (π.symm l)) := by
        have h := hπ (ggKGSg_red y) (π.symm l)
        simpa using h
      rw [happ, hπinv l, hεall, ggKGSg_red_apply, ggKGSg_red_apply, toAdd_ofAdd]
      by_cases h0 : l = i0
      · subst h0
        simp [hi1]
        exact neg_one_mul _
      · by_cases h1 : l = i1
        · subst h1
          simp [h0]
          exact neg_one_mul _
        · simp [h0, h1]


theorem ggTorusLattice_of_signedModel {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type}
    [Group L'] {A : Subgroup (MulAut L')} (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hS : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn))) :
    ∃ (m : ℕ) (Q : Matrix (Fin m) (Fin m) ℤ) (π : (Fin m → ℤ) →+ Additive ↥A),
      GGLatForm Q ∧ Function.Surjective π ∧
      ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
        ∃ w : Fin m → ℤ, GGLatRoot Q w ∧ ∀ y : Fin m → ℤ,
          φ (Additive.toMul (π y)) = Additive.toMul (π (ggLatRefl Q w y)) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  refine ⟨k, 1, ggKGSg_pi (p := p) (k := k) Θ, ggKGSg_latForm_one,
    ggKGSg_pi_surjective Θ, ?_⟩
  intro φ hφmem hφrefl
  obtain ⟨g, hgH, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφmem
  obtain ⟨n, hn⟩ := hgH
  have hgN' : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [hn]
    exact hgN
  have hφeq : φ = ggConjAut A hgN' := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply, hn]
    exact hφg b
  let u : MulAut (ggKGSg_V p k) := (MulAut.congr Θ).symm φ
  have hcongr : MulAut.congr Θ u = φ := by
    show MulAut.congr Θ ((MulAut.congr Θ).symm φ) = φ
    exact MulEquiv.apply_symm_apply _ _
  have hu : IsSignedPerm ⇑u := by
    have h := hS n hgN'
    dsimp only [u]
    rw [hφeq]
    exact h
  have hu2 : u * u = 1 := by
    have h2 : φ ^ 2 = 1 := hφrefl.1
    have h3 : u ^ 2 = 1 := by
      have h := map_pow (MulAut.congr Θ).symm φ 2
      rw [h2, map_one] at h
      exact h.symm
    simpa [sq] using h3
  have hcard : Nat.card {f : ggKGSg_V p k // u f = f} * p =
      Nat.card (ggKGSg_V p k) := by
    have hfixiff : ∀ f : ggKGSg_V p k, u f = f ↔ φ (Θ f) = Θ f := by
      intro f
      constructor
      · intro h
        rw [← hcongr, ggKGSg_congr_apply, h]
      · intro h
        apply Θ.injective
        rw [← ggKGSg_congr_apply, hcongr, h]
    have e : {f : ggKGSg_V p k // u f = f} ≃ {a : ↥A // φ a = a} :=
      Equiv.subtypeEquiv Θ.toEquiv (fun f => hfixiff f)
    have hc2 := hφrefl.2
    rw [← Nat.card_congr e, ← Nat.card_congr Θ.toEquiv] at hc2
    exact hc2
  obtain ⟨w, hroot, hval⟩ := ggKGSg_classify hp hp2 hu hu2 hcard
  refine ⟨w, hroot, fun y => ?_⟩
  rw [ggKGSg_pi_apply, ggKGSg_pi_apply]
  change φ (Θ (ggKGSg_red y)) = Θ (ggKGSg_red (ggLatRefl 1 w y))
  rw [← hcongr, ggKGSg_congr_apply, hval y]

end CFSG.StandardType
