module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_b

public section

open scoped commutatorElement

namespace CFSG.RankThree

@[expose] def lcomm {H : Type*} [Group H] (x y : H) : H := x⁻¹ * y⁻¹ * x * y

theorem lowerCentralSeries_three_eq_bot_of_card_le_pow_four {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) (hcard : Nat.card P ≤ p ^ 4) :
    (⊤ : Subgroup P).lowerCentralSeries 3 = ⊥ := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  rw [Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le,
    ← Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le]
  exact CFSG.nilpotencyClassLe_of_card_le_p_four hcard

section ClassThree

variable {H : Type*} [Group H]

theorem lcomm_eq_commutatorElement (x y : H) : lcomm x y = ⁅x⁻¹, y⁻¹⁆ := by
  simp [lcomm, commutatorElement_def]

theorem mul_eq_mul_lcomm (x y : H) : x * y = y * x * lcomm x y := by
  simp [lcomm, mul_assoc]

theorem mul_central {c : H} (hc : ∀ g : H, Commute c g) (x y : H) : x * c * y = x * y * c := by
  rw [mul_assoc, (hc y).eq, ← mul_assoc]

theorem commute_of_mem_lowerCentralSeries_two
    (hH : (⊤ : Subgroup H).lowerCentralSeries 3 = ⊥) {x : H}
    (hx : x ∈ (⊤ : Subgroup H).lowerCentralSeries 2) (g : H) : Commute x g := by
  have hmem : ⁅x, g⁆ ∈ (⊤ : Subgroup H).lowerCentralSeries 3 :=
    Subgroup.commutator_mem_commutator hx (Subgroup.mem_top g)
  rw [hH, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem lcomm_mem_lowerCentralSeries_succ (n : ℕ) {x : H}
    (hx : x ∈ (⊤ : Subgroup H).lowerCentralSeries n) (g : H) :
    lcomm x g ∈ (⊤ : Subgroup H).lowerCentralSeries (n + 1) := by
  rw [lcomm_eq_commutatorElement]
  exact Subgroup.commutator_mem_commutator (inv_mem hx) (Subgroup.mem_top _)

theorem commute_lcomm_lcomm (hH : (⊤ : Subgroup H).lowerCentralSeries 3 = ⊥)
    (u v w g : H) : Commute (lcomm (lcomm v u) w) g :=
  commute_of_mem_lowerCentralSeries_two hH
    (lcomm_mem_lowerCentralSeries_succ 1
      (lcomm_mem_lowerCentralSeries_succ 0 (Subgroup.mem_top v) u) w) g

theorem inv_mul_mul_eq_mul_lcomm (r v : H) : v⁻¹ * r * v = r * lcomm r v := by
  simp [lcomm, mul_assoc]

theorem conj_pow_of_central {r w c : H} (hc : ∀ g : H, Commute c g) (hrw : lcomm r w = c)
    (m : ℕ) : w⁻¹ * r ^ m * w = r ^ m * c ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : w⁻¹ * r ^ (m + 1) * w = (w⁻¹ * r ^ m * w) * (w⁻¹ * r * w) := by
      simp only [pow_succ]; group
    rw [h1, ih, inv_mul_mul_eq_mul_lcomm, hrw, pow_succ r m, pow_succ c m, ← mul_assoc,
      mul_central (fun g => (hc g).pow_left m) (r ^ m) r, mul_assoc]

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]

theorem choose_three_succ (n : ℕ) : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_succ_succ]

theorem lcomm_pow_left (hH : (⊤ : Subgroup H).lowerCentralSeries 3 = ⊥) (u v : H) (n : ℕ) :
    lcomm (v ^ n) u = lcomm v u ^ n * lcomm (lcomm v u) v ^ n.choose 2 := by
  set r := lcomm v u with hr
  set t := lcomm r v with ht
  have htc : ∀ g : H, Commute t g := fun g => commute_lcomm_lcomm hH u v v g
  have htk : ∀ k : ℕ, ∀ g : H, Commute (t ^ k) g := fun k g => (htc g).pow_left k
  induction n with
  | zero => simp [lcomm]
  | succ n ih =>
    have hsplit : lcomm (v ^ (n + 1)) u = v⁻¹ * lcomm (v ^ n) u * v * r := by
      simp only [hr, lcomm, pow_succ]; group
    rw [hsplit, ih, ← mul_assoc v⁻¹, mul_central (htk _) (v⁻¹ * r ^ n) v,
      conj_pow_of_central htc ht.symm n, choose_two_succ, pow_add t, pow_succ r n,
      mul_central (htk _) (r ^ n * t ^ n) r, mul_central (htk _) (r ^ n) r]
    simp only [mul_assoc]

theorem mul_pow_of_class_three (hH : (⊤ : Subgroup H).lowerCentralSeries 3 = ⊥) (u v : H)
    (n : ℕ) :
    (u * v) ^ n = u ^ n * v ^ n * lcomm v u ^ n.choose 2 *
      lcomm (lcomm v u) u ^ n.choose 3 *
      lcomm (lcomm v u) v ^ (2 * n.choose 3 + n.choose 2) := by
  set r := lcomm v u with hr
  set s := lcomm r u with hs
  set t := lcomm r v with ht
  have hsc : ∀ g : H, Commute s g := fun g => commute_lcomm_lcomm hH u v u g
  have htc : ∀ g : H, Commute t g := fun g => commute_lcomm_lcomm hH u v v g
  have hsk : ∀ k : ℕ, ∀ g : H, Commute (s ^ k) g := fun k g => (hsc g).pow_left k
  have htk : ∀ k : ℕ, ∀ g : H, Commute (t ^ k) g := fun k g => (htc g).pow_left k
  have hru : ∀ m : ℕ, r ^ m * u = u * r ^ m * s ^ m := fun m => by
    rw [mul_assoc u, ← conj_pow_of_central hsc hs.symm m]; group
  have hrv : ∀ m : ℕ, r ^ m * v = v * r ^ m * t ^ m := fun m => by
    rw [mul_assoc v, ← conj_pow_of_central htc ht.symm m]; group
  have hvu : ∀ m : ℕ, v ^ m * u = u * v ^ m * r ^ m * t ^ m.choose 2 := fun m => by
    rw [mul_eq_mul_lcomm (v ^ m) u, lcomm_pow_left hH u v m, ← mul_assoc]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    set a := n.choose 2
    set b := n.choose 3
    set c := 2 * n.choose 3 + n.choose 2
    set k := n.choose 2 with hk
    calc u ^ n * v ^ n * r ^ a * s ^ b * t ^ c * (u * v)
        = (u ^ n * v ^ n * r ^ a) * (s ^ b * t ^ c) * (u * v) := by group
      _ = (u ^ n * v ^ n * r ^ a) * (u * v) * (s ^ b * t ^ c) :=
          mul_central (fun g => ((hsk b g).mul_left (htk c g))) _ _
      _ = u ^ n * v ^ n * (r ^ a * u) * v * (s ^ b * t ^ c) := by group
      _ = u ^ n * v ^ n * (u * r ^ a * s ^ a) * v * (s ^ b * t ^ c) := by rw [hru a]
      _ = (u ^ n * v ^ n * u * r ^ a) * s ^ a * v * (s ^ b * t ^ c) := by group
      _ = (u ^ n * v ^ n * u * r ^ a) * v * s ^ a * (s ^ b * t ^ c) := by
          rw [mul_central (hsk a) (u ^ n * v ^ n * u * r ^ a) v]
      _ = u ^ n * (v ^ n * u) * r ^ a * v * s ^ a * (s ^ b * t ^ c) := by group
      _ = u ^ n * (u * v ^ n * r ^ n * t ^ k) * r ^ a * v * s ^ a * (s ^ b * t ^ c) := by
          rw [hvu n]
      _ = (u ^ n * u * v ^ n * r ^ n) * t ^ k * (r ^ a * v) * s ^ a * (s ^ b * t ^ c) := by
          group
      _ = (u ^ n * u * v ^ n * r ^ n) * (r ^ a * v) * t ^ k * s ^ a * (s ^ b * t ^ c) := by
          rw [mul_central (htk k) (u ^ n * u * v ^ n * r ^ n) (r ^ a * v)]
      _ = (u ^ n * u * v ^ n) * (r ^ (n + a) * v) * t ^ k * s ^ a * (s ^ b * t ^ c) := by
          group
      _ = (u ^ n * u * v ^ n) * (v * r ^ (n + a) * t ^ (n + a)) * t ^ k * s ^ a *
            (s ^ b * t ^ c) := by rw [hrv (n + a)]
      _ = u ^ (n + 1) * v ^ (n + 1) * r ^ (n + a) *
            (t ^ (n + a) * t ^ k * s ^ a * (s ^ b * t ^ c)) := by group
      _ = u ^ (n + 1) * v ^ (n + 1) * r ^ (n + a) *
            (s ^ (a + b) * t ^ (n + a + k + c)) := by
          congr 1
          have h1 : t ^ (n + a) * t ^ k * s ^ a * (s ^ b * t ^ c) =
              s ^ a * (t ^ (n + a) * t ^ k) * (s ^ b * t ^ c) := by
            rw [(hsk a (t ^ (n + a) * t ^ k)).eq]
          have h2 : s ^ a * (t ^ (n + a) * t ^ k) * (s ^ b * t ^ c) =
              s ^ a * s ^ b * (t ^ (n + a) * t ^ k) * t ^ c := by
            rw [mul_assoc, ← mul_assoc (t ^ (n + a) * t ^ k), ((hsk b _).eq).symm]
            group
          rw [h1, h2]
          group
      _ = u ^ (n + 1) * v ^ (n + 1) * r ^ (n + 1).choose 2 * s ^ (n + 1).choose 3 *
            t ^ (2 * (n + 1).choose 3 + (n + 1).choose 2) := by
          have ea : n + a = (n + 1).choose 2 := (choose_two_succ n).symm
          have eb : a + b = (n + 1).choose 3 := (choose_three_succ n).symm
          have ec : n + a + k + c = 2 * (n + 1).choose 3 + (n + 1).choose 2 := by
            rw [choose_three_succ, choose_two_succ]
            simp only [a, c, k]
            ring
          rw [ec, ea, eb]; group

end ClassThree

section ClassTwo

variable {B : Type*} [Group B]
variable {B : Type*} [Group B]

theorem lcomm_mem_commutator (u v : B) : lcomm u v ∈ commutator B := by
  rw [lcomm_eq_commutatorElement]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem central_of_mem (hB : commutator B ≤ Subgroup.center B) {c : B}
    (hc : c ∈ commutator B) (g : B) : Commute c g :=
  ((Subgroup.mem_center_iff.mp (hB hc)) g).symm

theorem lcomm_mul_right_mem (hB : commutator B ≤ Subgroup.center B) (u v c : B)
    (hc : c ∈ commutator B) : lcomm u (v * c) = lcomm u v := by
  have hcz := central_of_mem hB hc
  have hcz' := central_of_mem hB (inv_mem hc)
  calc lcomm u (v * c) = u⁻¹ * c⁻¹ * v⁻¹ * u * v * c := by simp only [lcomm]; group
    _ = u⁻¹ * v⁻¹ * u * v * c⁻¹ * c := by
        rw [mul_central hcz' u⁻¹ v⁻¹, mul_assoc (u⁻¹ * v⁻¹ * c⁻¹) u, mul_central hcz' _ (u * v)]
        group
    _ = lcomm u v := by simp only [lcomm]; group

theorem lcomm_mul_left_mem (hB : commutator B ≤ Subgroup.center B) (u v c : B)
    (hc : c ∈ commutator B) : lcomm (u * c) v = lcomm u v := by
  have hcz := central_of_mem hB hc
  have hcz' := central_of_mem hB (inv_mem hc)
  calc lcomm (u * c) v = c⁻¹ * (u⁻¹ * v⁻¹ * u) * c * v := by simp only [lcomm]; group
    _ = c⁻¹ * (u⁻¹ * v⁻¹ * u) * v * c := mul_central hcz _ v
    _ = (u⁻¹ * v⁻¹ * u * v) * c⁻¹ * c := by
        rw [(hcz' (u⁻¹ * v⁻¹ * u)).eq, mul_central hcz' (u⁻¹ * v⁻¹ * u) v]
    _ = lcomm u v := by simp only [lcomm]; group

@[expose] noncomputable def commPairing (hB : commutator B ≤ Subgroup.center B) :
    B ⧸ commutator B → B ⧸ commutator B → commutator B :=
  fun x y => Quotient.liftOn₂' x y
    (fun u v => (⟨lcomm u v, lcomm_mem_commutator u v⟩ : commutator B)) (by
      intro u₁ v₁ u₂ v₂ hu hv
      rw [QuotientGroup.leftRel_apply] at hu hv
      apply Subtype.ext
      show lcomm u₁ v₁ = lcomm u₂ v₂
      have h1 := lcomm_mul_left_mem hB u₁ v₁ _ hu
      rw [mul_inv_cancel_left] at h1
      have h2 := lcomm_mul_right_mem hB u₂ v₁ _ hv
      rw [mul_inv_cancel_left] at h2
      rw [← h1, h2])

theorem commPairing_mk (hB : commutator B ≤ Subgroup.center B) (u v : B) :
    ((commPairing hB (u : B ⧸ commutator B) (v : B ⧸ commutator B) : commutator B) : B) =
      lcomm u v := rfl

theorem commPairing_self (hB : commutator B ≤ Subgroup.center B) (x : B ⧸ commutator B) :
    commPairing hB x x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    apply Subtype.ext
    rw [commPairing_mk]
    simp [lcomm]

theorem commPairing_swap (hB : commutator B ≤ Subgroup.center B) (x y : B ⧸ commutator B) :
    commPairing hB y x = (commPairing hB x y)⁻¹ := by
  induction x using QuotientGroup.induction_on with
  | H u =>
  induction y using QuotientGroup.induction_on with
  | H v =>
    apply Subtype.ext
    rw [Subgroup.coe_inv, commPairing_mk, commPairing_mk]
    simp only [lcomm]; group

theorem commPairing_mul_left (hB : commutator B ≤ Subgroup.center B)
    (x x' y : B ⧸ commutator B) :
    commPairing hB (x * x') y = commPairing hB x y * commPairing hB x' y := by
  induction x using QuotientGroup.induction_on with
  | H u =>
  induction x' using QuotientGroup.induction_on with
  | H u' =>
  induction y using QuotientGroup.induction_on with
  | H v =>
    apply Subtype.ext
    rw [← QuotientGroup.mk_mul, Subgroup.coe_mul, commPairing_mk, commPairing_mk, commPairing_mk]
    have hcz := central_of_mem hB (lcomm_mem_commutator u v)
    calc lcomm (u * u') v = u'⁻¹ * lcomm u v * u' * lcomm u' v := by simp only [lcomm]; group
      _ = u'⁻¹ * u' * lcomm u v * lcomm u' v := by rw [mul_central hcz u'⁻¹ u']
      _ = lcomm u v * lcomm u' v := by group

theorem commPairing_mul_right (hB : commutator B ≤ Subgroup.center B)
    (x y y' : B ⧸ commutator B) :
    commPairing hB x (y * y') = commPairing hB x y * commPairing hB x y' := by
  rw [commPairing_swap hB (y * y') x, commPairing_mul_left, commPairing_swap hB x y,
    commPairing_swap hB x y', mul_inv_rev, inv_inv, inv_inv]
  apply Subtype.ext
  exact (central_of_mem hB (commPairing hB x y').2 _).eq

theorem commPairing_map (hB : commutator B ≤ Subgroup.center B) (σ : B ≃* B)
    (hσ : ∀ c ∈ commutator B, σ c = c) (u v : B) :
    commPairing hB (σ u : B ⧸ commutator B) (σ v : B ⧸ commutator B) =
      commPairing hB (u : B ⧸ commutator B) (v : B ⧸ commutator B) := by
  apply Subtype.ext
  rw [commPairing_mk, commPairing_mk, ← hσ (lcomm u v) (lcomm_mem_commutator u v)]
  simp [lcomm, map_mul, map_inv]

end ClassTwo

end CFSG.RankThree
