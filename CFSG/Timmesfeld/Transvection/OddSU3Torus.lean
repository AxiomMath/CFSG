module

public import CFSG.Timmesfeld.Transvection.OddSU3Chord
import CFSG.Timmesfeld.Transvection.OddModelHeis
import CFSG.Timmesfeld.Transvection.ModelRankBasic
import CFSG.Timmesfeld.ARS.BasicTwoGroup
import CFSG.GroupTheory.FixedPointFreeCommutator
import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.UniquenessCase
open Pres
open scoped commutatorElement

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {σ : F ≃+* F}
  {H : Type*} [Group H]

theorem exists_unitaryInvolution_eq_self_ne (hFn : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) :
    ∃ c : F, unitaryInvolution F 2 n c = c ∧ c ≠ 0 ∧ c ≠ 1 := by
  have hq2 : 2 ^ n ≠ 2 := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨s, hs0, hs1⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_ne_one hFn hq2
  refine ⟨unitaryInvolution F 2 n s * s, ?_, ?_, hs1⟩
  · rw [map_mul, unitaryInvolution_involutive hFn, mul_comm]
  · exact mul_ne_zero ((map_ne_zero _).2 hs0) hs0

theorem exists_mem_su3Top_sup_su3Bot_mat_eq (hFn : Nat.card F = (2 ^ n) ^ 2) {c : F}
    (hc : unitaryInvolution F 2 n c = c) (hc0 : c ≠ 0) :
    ∃ s ∈ su3Top (unitaryInvolution F 2 n) ⊔ su3Bot (unitaryInvolution F 2 n),
      mat (unitaryInvolution F 2 n) 3 s = Matrix.diagonal ![c, 1, c⁻¹] := by
  let σ := unitaryInvolution F 2 n
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hFn
  let t₂ := longTorus σ (b := (0 : Fin 2)) (by decide) ζ hc
  have h2 : mat σ 2 t₂ = Matrix.diagonal (longTorusFun (0 : Fin 2) c) := by
    rw [mat_apply]
    exact coe_longTorus σ (by decide) hζ hc hc0
  let s := su3Chord σ t₂
  refine ⟨s, ?_, ?_⟩
  · rw [← map_su2Top_su3Chord, ← map_su2Bot_su3Chord, ← Subgroup.map_sup,
      su2Top_sup_su2Bot hFn]
    exact Subgroup.mem_map_of_mem (su3Chord σ) (Subgroup.mem_top t₂)
  · rw [mat_su3Chord, h2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [longTorusFun]

private theorem conj_su3Top_of_mat_diagonal {g : SU σ 3} {d : Fin 3 → F}
    (hg : mat σ 3 g = Matrix.diagonal d) (hd : ∀ i, σ (d i) * d (Fin.rev i) = 1)
    {x : SU σ 3} (hx : x ∈ su3Top σ) : g * x * g⁻¹ ∈ su3Top σ := by
  obtain ⟨a, ha, rfl⟩ := (mem_su3Top_iff (σ := σ)).1 hx
  rw [conj_suLong_of_mat_diagonal (σ := σ) hg hd (Sum.inl (0 : Fin (3 / 2))) a]
  refine (mem_su3Top_iff (σ := σ)).2 ⟨d 0 * a * (d 2)⁻¹, ?_, rfl⟩
  have h0 : σ (d 0) = (d 2)⁻¹ := by
    have h := hd 0
    rw [show Fin.rev (0 : Fin 3) = 2 from rfl] at h
    exact eq_inv_of_mul_eq_one_left h
  have h2 : σ (d 2) = (d 0)⁻¹ := by
    have h := hd 2
    rw [show Fin.rev (2 : Fin 3) = 0 from rfl] at h
    exact eq_inv_of_mul_eq_one_left h
  rw [map_mul, map_mul, map_inv₀, h0, h2, inv_inv, ha]
  ring

private theorem conj_su3Bot_of_mat_diagonal {g : SU σ 3} {d : Fin 3 → F}
    (hg : mat σ 3 g = Matrix.diagonal d) (hd : ∀ i, σ (d i) * d (Fin.rev i) = 1)
    {x : SU σ 3} (hx : x ∈ su3Bot σ) : g * x * g⁻¹ ∈ su3Bot σ := by
  obtain ⟨a, ha, rfl⟩ := (mem_su3Bot_iff (σ := σ)).1 hx
  rw [conj_suLong_of_mat_diagonal (σ := σ) hg hd (Sum.inr (0 : Fin (3 / 2))) a]
  refine (mem_su3Bot_iff (σ := σ)).2 ⟨d 2 * a * (d 0)⁻¹, ?_, rfl⟩
  have h0 : σ (d 0) = (d 2)⁻¹ := by
    have h := hd 0
    rw [show Fin.rev (0 : Fin 3) = 2 from rfl] at h
    exact eq_inv_of_mul_eq_one_left h
  have h2 : σ (d 2) = (d 0)⁻¹ := by
    have h := hd 2
    rw [show Fin.rev (2 : Fin 3) = 0 from rfl] at h
    exact eq_inv_of_mul_eq_one_left h
  rw [map_mul, map_mul, map_inv₀, h0, h2, inv_inv, ha]
  ring

theorem conjSub_su3Top_su3Bot_of_mat_eq {c : F} (hc : σ c = c)
    (hc0 : c ≠ 0) {s : SU σ 3} (hs : mat σ 3 s = Matrix.diagonal ![c, 1, c⁻¹]) :
    conjSub (su3Top σ) s = su3Top σ ∧ conjSub (su3Bot σ) s = su3Bot σ := by
  have hd : ∀ i, σ ((![c, 1, c⁻¹] : Fin 3 → F) i) *
      (![c, 1, c⁻¹] : Fin 3 → F) (Fin.rev i) = 1 := by
    intro i
    fin_cases i <;> simp [hc, hc0]
  have hd' : ∀ i, σ (((fun j => ((![c, 1, c⁻¹] : Fin 3 → F) j)⁻¹) : Fin 3 → F) i) *
      ((fun j => ((![c, 1, c⁻¹] : Fin 3 → F) j)⁻¹) : Fin 3 → F) (Fin.rev i) = 1 := by
    intro i
    fin_cases i <;> simp [hc, hc0]
  have hinv : mat σ 3 s⁻¹ =
      Matrix.diagonal (fun j => ((![c, 1, c⁻¹] : Fin 3 → F) j)⁻¹) :=
    diagonal_inv_eq (fun i => by fin_cases i <;> simp [hc0]) hs
  constructor
  · rw [conjSub_eq_self_iff, Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => conj_su3Top_of_mat_diagonal hs hd hx, fun hx => by
      have hk := conj_su3Top_of_mat_diagonal hinv hd' hx
      rwa [show s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ = x from by group] at hk⟩
  · rw [conjSub_eq_self_iff, Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => conj_su3Bot_of_mat_diagonal hs hd hx, fun hx => by
      have hk := conj_su3Bot_of_mat_diagonal hinv hd' hx
      rwa [show s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ = x from by group] at hk⟩

private theorem mat_conj_diag_apply {g x : SU σ 3} {d : Fin 3 → F}
    (hg : mat σ 3 g = Matrix.diagonal d) (hd : ∀ i, d i ≠ 0) (i j : Fin 3) :
    mat σ 3 (g * x * g⁻¹) i j = d i * mat σ 3 x i j * (d j)⁻¹ := by
  have hinv : mat σ 3 g⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) :=
    diagonal_inv_eq hd hg
  rw [map_mul, map_mul, hg, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem eq_one_of_conj_diag_eq_self (hσ : ∀ c, σ (σ c) = c) {c : F}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) {s x : SU σ 3}
    (hs : mat σ 3 s = Matrix.diagonal ![c, 1, c⁻¹])
    (hx : x ∈ UC22.uc22pwsu3X hσ) (hfix : s * x * s⁻¹ = x) : x = 1 := by
  obtain ⟨a, b, -, hxm⟩ := (mem_rootGroup_three hσ).1 hx
  have hd : ∀ i, (![c, 1, c⁻¹] : Fin 3 → F) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hc0]
  have h01 := mat_conj_diag_apply (σ := σ) (x := x) hs hd (0 : Fin 3) 1
  have h01' : mat σ 3 x 0 1 = c * mat σ 3 x 0 1 := by
    rw [show mat σ 3 (s * x * s⁻¹) = mat σ 3 x from by rw [hfix]] at h01
    simpa using h01
  have h02 := mat_conj_diag_apply (σ := σ) (x := x) hs hd (0 : Fin 3) 2
  have h02' : mat σ 3 x 0 2 = c * mat σ 3 x 0 2 * c := by
    rw [show mat σ 3 (s * x * s⁻¹) = mat σ 3 x from by rw [hfix]] at h02
    simpa using h02
  have ha : mat σ 3 x 0 1 = 0 := by
    have h1 : (c - 1) * mat σ 3 x 0 1 = 0 := by
      have h : c * mat σ 3 x 0 1 = mat σ 3 x 0 1 := h01'.symm
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hc1)
  have hb : mat σ 3 x 0 2 = 0 := by
    have h2 : (c * c - 1) * mat σ 3 x 0 2 = 0 := by
      have h : c * c * mat σ 3 x 0 2 = mat σ 3 x 0 2 := by
        calc c * c * mat σ 3 x 0 2 = c * mat σ 3 x 0 2 * c := by ring
          _ = mat σ 3 x 0 2 := h02'.symm
      rw [sub_mul, one_mul, h, sub_self]
    have hcc : c * c - 1 ≠ 0 := by
      intro h0
      have hcc1 : c * c = 1 := sub_eq_zero.mp h0
      rcases (mul_self_eq_one_iff.mp hcc1) with h1 | h1
      · exact hc1 h1
      · rw [CharTwo.neg_eq] at h1
        exact hc1 h1
    exact (mul_eq_zero.mp h2).resolve_left hcc
  have hx01 : mat σ 3 x 0 1 = a := by rw [hxm]; simp
  have hx02 : mat σ 3 x 0 2 = b := by rw [hxm]; simp
  have hxmat : mat σ 3 x = 1 := by
    rw [hxm, ← hx01, ha, ← hx02, hb]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact mat_injective (hxmat.trans (map_one (mat σ 3)).symm)

theorem exists_eq_commutatorElement_of_mat_eq (hσ : ∀ c, σ (σ c) = c) {c : F} (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) {s : SU σ 3} (hs : mat σ 3 s = Matrix.diagonal ![c, 1, c⁻¹])
    {x : SU σ 3} (hx : x ∈ UC22.uc22pwsu3X hσ) : ∃ y ∈ UC22.uc22pwsu3X hσ, x = ⁅y, s⁆ := by
  classical
  haveI : Finite (SU σ 3) := inferInstance
  have hd : ∀ i, (![c, 1, c⁻¹] : Fin 3 → F) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hc0]
  have hN : s ∈ Subgroup.normalizer (UC22.uc22pwsu3X hσ : Set (SU σ 3)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => UC22.uc22pwsu3_conj_diag_mem hσ hd hs hy, fun hy => ?_⟩
    have hinv : mat σ 3 s⁻¹ =
        Matrix.diagonal (fun j => ((![c, 1, c⁻¹] : Fin 3 → F) j)⁻¹) :=
      diagonal_inv_eq hd hs
    have hd' : ∀ i, ((fun j => ((![c, 1, c⁻¹] : Fin 3 → F) j)⁻¹) : Fin 3 → F) i ≠ 0 :=
      fun i => inv_ne_zero (hd i)
    have hk := UC22.uc22pwsu3_conj_diag_mem hσ hd' hinv hy
    rwa [show s⁻¹ * (s * y * s⁻¹) * (s⁻¹)⁻¹ = y from by group] at hk
  have hfree : ∀ t ∈ UC22.uc22pwsu3X hσ, s * t * s⁻¹ = t → t = 1 :=
    fun t ht hfix => eq_one_of_conj_diag_eq_self hσ hc0 hc1 hs ht hfix
  obtain ⟨y, hy, hyx⟩ :=
    exists_eq_conj_mul_inv_of_fixedPointFree hN hfree x⁻¹ (Subgroup.inv_mem _ hx)
  refine ⟨y, hy, ?_⟩
  calc x = (x⁻¹)⁻¹ := (inv_inv x).symm
    _ = (s * y * s⁻¹ * y⁻¹)⁻¹ := by rw [hyx]
    _ = y * s * y⁻¹ * s⁻¹ := by group

theorem map_su3Top_su3Bot_of_comp_su3Chord {θ : SU σ 3 →* H} {ψ : SU σ 2 →* H}
    {A E : Subgroup H} (hθc : θ.comp (su3Chord σ) = ψ) (ht : (su2Top σ).map ψ = A)
    (hb : (su2Bot σ).map ψ = E) : (su3Top σ).map θ = A ∧ (su3Bot σ).map θ = E := by
  constructor
  · rw [← map_su2Top_su3Chord, Subgroup.map_map, hθc, ht]
  · rw [← map_su2Bot_su3Chord, Subgroup.map_map, hθc, hb]

theorem conjSub_eq_of_mem_map_heis (hσ : ∀ c, σ (σ c) = c) {θ : SU σ 3 →* H}
    {A : Subgroup H} (hθt : (su3Top σ).map θ = A) {b : H}
    (hb : b ∈ (UC22.uc22pwsu3X hσ).map θ) : conjSub A b = A := by
  obtain ⟨x, hx, rfl⟩ := hb
  rw [← hθt, ModelRank.conjSub_map, conjSub_su3Top_of_mem_X hσ hx]

theorem commuting_map_heis_map_su3Top (hσ : ∀ c, σ (σ c) = c) (θ : SU σ 3 →* H) :
    Commuting ((UC22.uc22pwsu3X hσ).map θ) ((su3Top σ).map θ) := by
  refine ModelRank.commuting_map θ ?_
  intro u hu x hx
  obtain ⟨β, hβ, rfl⟩ := (mem_su3Top_iff_Y (σ := σ)).1 hx
  exact UC22.uc22pwsu3Y_comm hσ hu β hβ

theorem exists_torus_map_heis (hFn : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} {A E : Subgroup H}
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = A)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = E) :
    ∃ s : SU (unitaryInvolution F 2 n) 3, θ s ∈ A ⊔ E ∧ conjSub A (θ s) = A ∧
      conjSub E (θ s) = E ∧
      ∀ x ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ,
        ∃ y ∈ (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ, x = ⁅y, θ s⁆ := by
  let σ := unitaryInvolution F 2 n
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  obtain ⟨c, hc, hc0, hc1⟩ := exists_unitaryInvolution_eq_self_ne hFn hn
  obtain ⟨s, hs_mem, hs_mat⟩ := exists_mem_su3Top_sup_su3Bot_mat_eq hFn hc hc0
  have hnorm := conjSub_su3Top_su3Bot_of_mat_eq hc hc0 hs_mat
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · rw [← hθt, ← hθb, ← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem θ hs_mem
  · rw [← hθt, ModelRank.conjSub_map, hnorm.1, hθt]
  · rw [← hθb, ModelRank.conjSub_map, hnorm.2, hθb]
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := exists_eq_commutatorElement_of_mat_eq hσ hc0 hc1 hs_mat hx
    exact ⟨θ y, Subgroup.mem_map_of_mem θ hy, by rw [hxy, map_commutatorElement]⟩

theorem eq_of_mem_heis_of_map_eq (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθk : Odd (Nat.card θ.ker))
    {x y : SU (unitaryInvolution F 2 n) 3}
    (hx : x ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn))
    (hy : y ∈ UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)) (hxy : θ x = θ y) : x = y := by
  have hXp : IsPGroup 2 (UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)) :=
    IsPGroup.of_card (n := 3 * n)
      (by rw [card_rootGroup_three hFn, ← pow_mul, mul_comm])
  exact congrArg Subtype.val (CFSG.RankThree.OddKernel.injective_restrict_of_odd θ hθk hXp
    (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

theorem card_map_heis_of_odd (hFn : Nat.card F = (2 ^ n) ^ 2)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} (hθk : Odd (Nat.card θ.ker)) :
    Nat.card ↥((UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)).map θ) = (2 ^ n) ^ 3 := by
  let Xh : Subgroup (SU (unitaryInvolution F 2 n) 3) :=
    UC22.uc22pwsu3X (unitaryInvolution_involutive hFn)
  let B : Subgroup H := Xh.map θ
  let φB : ↥Xh → ↥B := fun x => ⟨θ x, Subgroup.mem_map_of_mem θ x.2⟩
  have hφB : Function.Bijective φB := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact eq_of_mem_heis_of_map_eq hFn hθk x.2 y.2 (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hxy⟩ := y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  calc Nat.card ↥B = Nat.card ↥Xh := (Nat.card_congr (Equiv.ofBijective φB hφB)).symm
    _ = (2 ^ n) ^ 3 := by
        simpa [Xh, UC22.uc22pwsu3X] using card_rootGroup_three (p := 2) (f := n) hFn

end CFSG.Timmesfeld.Transvection
