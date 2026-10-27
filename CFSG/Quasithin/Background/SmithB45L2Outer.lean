module

public import CFSG.Quasithin.Background.SmithB45L2Inner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesOuterCore

public section

namespace CFSG.Quasithin.B45L2

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization
open CFSG.GorensteinWalter Projectivization

section Numerics

theorem num_lin_trivial {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m)
    (h : d * 2 ^ (2 * m) ≤ 2 + d * (2 ^ m * (2 ^ m + 1) / 2)) : m = 1 ∧ d ≤ 2 := by
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ m := ⟨_, rfl⟩
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpow : 2 ^ (2 * m) = q * q := by rw [hq, two_mul, pow_add]
  have hh : 2 * (q * (q + 1) / 2) = q * (q + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self q).two_dvd
  rw [hpow, ← hq] at h
  generalize q * (q + 1) / 2 = t at h hh
  have h3 : q = 2 := by
    by_contra hne
    have h3 : 3 ≤ q := by omega
    nlinarith [Nat.mul_le_mul hd h3, Nat.mul_le_mul (Nat.mul_le_mul hd h3) h3]
  subst h3
  refine ⟨Nat.pow_right_injective (le_refl 2) (show 2 ^ m = 2 ^ 1 from hq.symm), ?_⟩
  nlinarith

theorem four_mul_le_two_pow {m : ℕ} (hm : 2 ≤ m) : 4 * m ≤ 2 ^ (2 * m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : 2 * (m + 1) - 1 = (2 * m - 1) + 2 := by omega
    rw [h1, pow_add]
    omega

theorem num_semi_lt {r d : ℕ} (hr : 3 ≤ r) (hd : 1 ≤ d) : 2 * r * d + 4 < 3 * d * 2 ^ (r - 1) := by
  have h : 2 * r + 5 ≤ 3 * 2 ^ (r - 1) := by
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ r hr ih =>
      have h1 : r + 1 - 1 = (r - 1) + 1 := by omega
      rw [h1, pow_succ]
      omega
  nlinarith

theorem num_lin_triv {n s d m : ℕ} (hn : 3 ≤ n) (hns : n = 2 * s) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (horb : n ≤ 2 * m * d) (h : d * 2 ^ (2 * m) ≤ 2 + d * (2 ^ m * (2 ^ m + 1) / 2)) :
    m = 1 ∧ s = 2 ∧ d = 2 := by
  obtain ⟨hm1, hd2⟩ := num_lin_trivial hd hm h
  subst hm1
  omega

theorem num_lin_nontriv {n s d m : ℕ} (hns : n = 2 * s) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (horb : n ≤ 2 * m * d) (h : d * 2 ^ (2 * m) ≤ 2 * (s + 1) + d * 2 ^ (2 * m - 1)) :
    m = 1 ∧ s ≤ d ∧ d ≤ s + 1 := by
  have hpow : 2 ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at h
  have h3 : d * 2 ^ (2 * m - 1) ≤ 2 * s + 2 := by nlinarith
  have hm1 : m = 1 := by
    by_contra hne'
    have h4 := four_mul_le_two_pow (show 2 ≤ m by omega)
    have h5 : d * (4 * m) ≤ d * 2 ^ (2 * m - 1) := Nat.mul_le_mul_left d h4
    have hP : 2 ≤ m * d := le_trans (show 2 ≤ m by omega) (Nat.le_mul_of_pos_right m hd)
    rw [show d * (4 * m) = 4 * (m * d) by ring] at h5
    rw [hns, show 2 * m * d = 2 * (m * d) by ring] at horb
    omega
  subst hm1
  simp only [Nat.mul_one, Nat.add_one_sub_one, pow_one] at h3
  omega

theorem le_sixteen {x y : ℕ} (h1 : x ≤ 4 * y) (h2 : y ^ 2 ≤ x) : x ≤ 16 := by
  nlinarith

theorem num_semi_triv {n r d : ℕ} (hn : 3 ≤ n) (hr : 1 ≤ r) (horb : n ≤ r * d)
    (h : d * 2 ^ r ≤ 4) : False := by
  have h6 : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · interval_cases r <;> nlinarith
  · have h7 : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr3
    have hd : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        simp at horb
        omega
      · exact h0
    have h8 : 2 ^ r ≤ d * 2 ^ r := Nat.le_mul_of_pos_left _ hd
    omega

theorem num_semi_nontriv {n s r d : ℕ} (hn : 3 ≤ n) (hns : n = 2 * s) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (horb : n ≤ r * d) (h : 2 * (d * 2 ^ r) ≤ 4 * (s + 1) + d * 2 ^ (r - 1)) :
    (r = 1 ∧ 3 * d ≤ 2 * n + 4) ∨ (r = 2 ∧ d = 2 ∧ s = 2) := by
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at h
  have h6 : 3 * d * 2 ^ (r - 1) ≤ 2 * n + 4 := by nlinarith
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  · interval_cases r
    · left
      simp only [Nat.sub_self, pow_zero, mul_one] at h6
      exact ⟨rfl, h6⟩
    · right
      simp only [Nat.add_one_sub_one, pow_one] at h6
      omega
  · exfalso
    have h7 := num_semi_lt hr3 hd
    nlinarith

end Numerics

section Class

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

omit [Fintype F] [CharP F 2] [Finite W] in
theorem exists_inner_involution (ρ : Representation (ZMod 2) SL(2, F) W)
    (hρU : Function.Injective ρ.toHomUnits) {A : Subgroup (Module.End (ZMod 2) W)ˣ}
    (hA2 : ∀ a ∈ A, a * a = 1) (hB : ∃ b ∈ A, b ∈ ρ.toHomUnits.range ∧ b ≠ 1) :
    ∃ g : SL(2, F), g ≠ 1 ∧ g * g = 1 ∧ ρ.toHomUnits g ∈ A := by
  obtain ⟨b, hbA, ⟨g, rfl⟩, hb1⟩ := hB
  exact ⟨g, fun h => hb1 (by rw [h, map_one]), hρU (by rw [map_mul, hA2 _ hbA, map_one]), hbA⟩

theorem outer_lin {n s : ℕ} (hn : 3 ≤ n) (hs1 : 1 ≤ s) (hns : n = 2 * s)
    (hF : Fintype.card F = 2 ^ n) (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hρU : Function.Injective ρ.toHomUnits) (A : Subgroup (Module.End (ZMod 2) W)ˣ)
    (hA2 : ∀ a ∈ A, a * a = 1)
    (hoff : Nat.card W ≤ Nat.card A ^ 2 * Nat.card {w : W // ∀ a ∈ A, a.val w = w})
    (hAcard : Nat.card A ≤ 2 ^ (s + 1))
    (hAtriv : (∀ b ∈ A, b ∈ ρ.toHomUnits.range → b = 1) → Nat.card A = 2)
    {a : (Module.End (ZMod 2) W)ˣ} (haA : a ∈ A) (x : SL(2, F))
    (hxconj : ∀ g, ((ρ.toHomUnits x)⁻¹ * a * ρ.toHomUnits x) * ρ.toHomUnits g *
      ((ρ.toHomUnits x)⁻¹ * a * ρ.toHomUnits x)⁻¹ = ρ.toHomUnits (fieldAut F s g))
    (hlin : ∀ δ : EndRing ρ, a.val * epsHom ρ δ = epsHom ρ δ * a.val)
    {d : ℕ} (hd1 : 1 ≤ d) (hDcard : Nat.card (EndRing ρ) = 2 ^ d) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [Finite E] [CharP E 2]
    (ιF : F →+* E) (ιD : EndRing ρ →+* E) (J : Finset ℕ) (hJne : J.Nonempty)
    (hJn : ∀ i ∈ J, i < n) (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J)))
    (hshift : J.image (fun i => (i + d) % n) = J)
    (hdim : Module.finrank (EndRing ρ) W = 2 ^ J.card) :
    ∃ s', n = 2 * s' ∧ Nat.card (EndRing ρ) = 2 ^ s' ∧ Module.finrank (EndRing ρ) W = 4 := by
  classical
  let _ : Algebra F E := ιF.toAlgebra
  set ρU := ρ.toHomUnits with hρU_def
  have hρU_val : ∀ g, (ρU g).val = ρ g := fun g => by rw [hρU_def]; rfl
  have hF2 : Fintype.card F = 2 ^ (2 * s) := by rw [← hns]; exact hF
  have hJ2 : ∀ i ∈ J, i < 2 * s := fun i hi => hns ▸ hJn i hi
  set a' := (ρU x)⁻¹ * a * ρU x with ha'
  have ha'2 : a' * a' = 1 := by
    calc a' * a' = (ρU x)⁻¹ * (a * a) * ρU x := by simp only [ha']; group
      _ = 1 := by rw [hA2 a haA]; group
  have hcomm' : ∀ δ : EndRing ρ, a'.val * epsHom ρ δ = epsHom ρ δ * a'.val := by
    intro δ
    have h1 : ∀ g : SL(2, F), Commute (ρU g).val (epsHom ρ δ) := by
      intro g
      apply LinearMap.ext
      intro v
      rw [hρU_val]
      exact (epsHom_commutes ρ δ g v).symm
    have h3 : Commute (ρU x)⁻¹.val (epsHom ρ δ) := by
      rw [← map_inv ρU x]
      exact h1 x⁻¹
    have h2 : Commute a.val (epsHom ρ δ) := hlin δ
    have h4 := (h3.mul_left h2).mul_left (h1 x)
    show ((ρU x)⁻¹ * a * ρU x).val * _ = _ * ((ρU x)⁻¹ * a * ρU x).val
    rw [Units.val_mul, Units.val_mul]
    exact h4
  let aD : Module.End (EndRing ρ) W := linD ρ a'.val hcomm'
  have haD2 : aD * aD = 1 := by
    apply LinearMap.ext
    intro w
    have h := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val w) ha'2
    simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply] at h
    exact h
  have hconjD : ∀ g, aD * repD ρ g = repD ρ (fieldAut F s g) * aD := by
    intro g
    apply LinearMap.ext
    intro w
    have h := hxconj g
    have h' : a' * ρU g = ρU (fieldAut F s g) * a' := by
      calc a' * ρU g = (a' * ρU g * a'⁻¹) * a' := by group
        _ = ρU (fieldAut F s g) * a' := by rw [h]
    have h2 := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val w) h'
    simp only [Units.val_mul, Module.End.mul_apply, hρU_val] at h2
    exact h2
  obtain ⟨hJs, m', hm', hCa'⟩ := outer_involution_count ρ b ιD J Φ hs1 hF2 hJ2 aD haD2 hconjD
  have hCa2 : Nat.card {w : W // a.val w = w} = 2 ^ (d * (2 ^ m' * (2 ^ m' + 1) / 2)) := by
    rw [← natCard_fixed_conj_units a (ρU x)]
    have h2 : Nat.card {w : W // ((ρU x)⁻¹ * a * ρU x).val w = w} =
        Nat.card {w : W // aD w = w} := rfl
    rw [h2, hCa', hDcard, ← pow_mul]
  have hm1 : 1 ≤ m' := by
    have := Finset.card_pos.mpr hJne
    omega
  have hW : Nat.card W = 2 ^ (d * 2 ^ (2 * m')) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hdim, hm', hDcard, ← pow_mul]
  have horb : n ≤ 2 * m' * d := hm' ▸ n_le_card_mul (by omega) (by omega) hJn hJne hshift
  set C := Nat.card {w : W // ∀ a ∈ A, a.val w = w} with hCdef
  have hCa : C ≤ Nat.card {w : W // a.val w = w} := natCard_fixed_le A haA
  by_cases hB : ∀ b ∈ A, b ∈ ρU.range → b = 1
  ·
    have hA2c : Nat.card A = 2 := hAtriv hB
    have h1 : 2 ^ (d * 2 ^ (2 * m')) ≤ 2 ^ 2 * 2 ^ (d * (2 ^ m' * (2 ^ m' + 1) / 2)) := by
      rw [← hW, ← hCa2]
      calc Nat.card W ≤ Nat.card A ^ 2 * C := hoff
        _ ≤ 2 ^ 2 * Nat.card {w : W // a.val w = w} := by
          rw [hA2c]
          exact Nat.mul_le_mul_left _ hCa
    obtain ⟨hm1', hs2, hd2⟩ := num_lin_triv hn hns hd1 hm1 horb (exp_le_of_pow_le h1)
    subst hm1' hs2 hd2
    exact ⟨2, hns, hDcard, by rw [hdim, hm']; rfl⟩
  · push Not at hB
    obtain ⟨g, hg1, hg2, hgA⟩ := exists_inner_involution ρ hρU hA2 hB
    have hCg := natCard_fixW_involution ρ b ιF ιD J hJne Φ g hg1 hg2
    rw [hm', hDcard, ← pow_mul] at hCg
    have hCg' : C ≤ 2 ^ (d * 2 ^ (2 * m' - 1)) := by
      rw [← hCg]
      have h5 := natCard_fixed_le A hgA
      rwa [hρU_val] at h5
    have h1 : 2 ^ (d * 2 ^ (2 * m')) ≤ 2 ^ (2 * (s + 1)) * 2 ^ (d * 2 ^ (2 * m' - 1)) := by
      rw [← hW]
      calc Nat.card W ≤ Nat.card A ^ 2 * C := hoff
        _ ≤ (2 ^ (s + 1)) ^ 2 * 2 ^ (d * 2 ^ (2 * m' - 1)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hAcard 2) hCg'
        _ = _ := by rw [← pow_mul, mul_comm (s + 1) 2]
    obtain ⟨hm1', hsd, hds⟩ := num_lin_nontriv hns hd1 hm1 horb (exp_le_of_pow_le h1)
    subst hm1'
    refine ⟨s, hns, ?_, by rw [hdim, hm']; rfl⟩
    obtain ⟨y, z, hyz, hJyz⟩ := Finset.card_eq_two.mp hm'
    have hy : y < 2 * s := hJ2 y (by rw [hJyz]; simp)
    have hys : shiftExp s y ∈ J := by
      rw [← hJs]
      exact Finset.mem_image_of_mem _ (by rw [hJyz]; simp)
    have hyd : (y + d) % n ∈ J := by
      rw [← hshift]
      exact Finset.mem_image_of_mem _ (by rw [hJyz]; simp)
    rw [hJyz] at hys hyd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hys hyd
    have hys' : shiftExp s y = z := hys.resolve_left (shiftExp_ne hs1 hy)
    unfold shiftExp at hys'
    rw [hns] at hyd
    rcases hyd with h | h
    · exfalso
      have h1 : (y + d) % (2 * s) = (y + 0) % (2 * s) := by
        rw [h, add_zero, Nat.mod_eq_of_lt hy]
      have h2 := Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' y h1)
      have h3 := Nat.le_of_dvd (by omega) h2
      omega
    · rw [← hys'] at h
      have h2 : d % (2 * s) = s % (2 * s) := Nat.ModEq.add_left_cancel' y h
      rw [Nat.mod_eq_of_lt (show s < 2 * s by omega),
        Nat.mod_eq_of_lt (show d < 2 * s by omega)] at h2
      rw [hDcard, h2]

omit [Fintype F] [CharP F 2] in
theorem outer_semi {n s : ℕ} (hn : 3 ≤ n) (hns : n = 2 * s)
    (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hρU : Function.Injective ρ.toHomUnits) (A : Subgroup (Module.End (ZMod 2) W)ˣ)
    (hA2 : ∀ a ∈ A, a * a = 1)
    (hAN : A ≤ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ))
    (hoff : Nat.card W ≤ Nat.card A ^ 2 * Nat.card {w : W // ∀ a ∈ A, a.val w = w})
    (hAcard : Nat.card A ≤ 2 ^ (s + 1))
    (hAtriv : (∀ b ∈ A, b ∈ ρ.toHomUnits.range → b = 1) → Nat.card A = 2)
    {a : (Module.End (ZMod 2) W)ˣ} (haA : a ∈ A) {δ : EndRing ρ}
    (hδ : a.val * epsHom ρ δ ≠ epsHom ρ δ * a.val)
    {d : ℕ} (hd1 : 1 ≤ d) (hDcard : Nat.card (EndRing ρ) = 2 ^ d) {m : ℕ}
    (b : Module.Basis (Fin m) (EndRing ρ) W) {E : Type} [Field E] [Finite E] [CharP E 2]
    (ιF : F →+* E) (ιD : EndRing ρ →+* E) (J : Finset ℕ) (hJne : J.Nonempty)
    (hJn : ∀ i ∈ J, i < n) (Φ : (letI := ιF.toAlgebra; (matRepE b ιD).Equiv (frobTensor F E J)))
    (hshift : J.image (fun i => (i + d) % n) = J)
    (hdim : Module.finrank (EndRing ρ) W = 2 ^ J.card) :
    (Nat.card (EndRing ρ) = 2 ^ n ∧ Module.finrank (EndRing ρ) W = 2) ∨
      ∃ s', n = 2 * s' ∧ Nat.card (EndRing ρ) = 2 ^ s' ∧ Module.finrank (EndRing ρ) W = 4 := by
  classical
  let _ : Algebra F E := ιF.toAlgebra
  set ρU := ρ.toHomUnits with hρU_def
  have hρU_val : ∀ g, (ρU g).val = ρ g := fun g => by rw [hρU_def]; rfl
  obtain ⟨r, hr⟩ : ∃ r, J.card = r := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := hr ▸ Finset.card_pos.mpr hJne
  have hW : Nat.card W = 2 ^ (d * 2 ^ r) := by
    rw [natCard_eq_pow_finrank (ρ := ρ), hdim, hr, hDcard, ← pow_mul]
  have horb : n ≤ r * d := hr ▸ n_le_card_mul (by omega) (by omega) hJn hJne hshift
  set C := Nat.card {w : W // ∀ a ∈ A, a.val w = w} with hCdef
  have hCa : C ≤ Nat.card {w : W // a.val w = w} := natCard_fixed_le A haA
  have hnorm : ∀ g ∈ ρU.range, a⁻¹ * g * a ∈ ρU.range := by
    intro g hg
    exact (Subgroup.mem_normalizer_iff''.mp (hAN haA) g).mp hg
  have hav : ∀ v, a.val ((a⁻¹).val v) = v := fun v => by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have hva : ∀ v, (a⁻¹).val (a.val v) = v := fun v => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]
  obtain ⟨δ', hδ'⟩ : ∃ δ' : EndRing ρ, epsHom ρ δ' = a.val * epsHom ρ δ * (a⁻¹).val := by
    refine (mem_endRing_iff ρ (a.val * epsHom ρ δ * (a⁻¹).val)).mpr ?_ |>.imp fun ψ hψ => ?_
    · intro g v
      obtain ⟨g', hg'⟩ := hnorm (ρU g) ⟨g, rfl⟩
      have e1 : (a⁻¹).val (ρ g v) = ρ g' ((a⁻¹).val v) := by
        have h := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val ((a⁻¹).val v)) hg'
        simp only [Units.val_mul, Module.End.mul_apply, hρU_val, hav] at h
        exact h.symm
      have e2 : ∀ v', a.val (ρ g' v') = ρ g (a.val v') := by
        intro v'
        have h := congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val v') hg'
        simp only [Units.val_mul, Module.End.mul_apply, hρU_val] at h
        rw [h, hav]
      simp only [Module.End.mul_apply]
      rw [e1, epsHom_commutes, e2]
    · exact LinearMap.ext fun w => congrFun hψ w
  have hδne : δ' ≠ δ := by
    intro h
    apply hδ
    apply LinearMap.ext
    intro w
    have h1 := congrArg (fun f : Module.End (ZMod 2) W => f (a.val w)) hδ'
    simp only [Module.End.mul_apply, h, hva] at h1
    exact h1.symm
  have hsemi : ∀ U : AddSubgroup W, (∀ u ∈ U, epsHom ρ δ u ∈ U) →
      Nat.card {u : W // u ∈ U ∧ a.val u = u} ^ 2 ≤ Nat.card U := by
    intro U hU
    refine card_fixed_sq_le U a.val.toAddMonoidHom (epsHom ρ δ).toAddMonoidHom
      (epsHom ρ δ').toAddMonoidHom (fun w => ?_) (fun z hz => ?_) hU
    · show a.val (epsHom ρ δ w) = epsHom ρ δ' (a.val w)
      rw [hδ']
      simp only [Module.End.mul_apply, hva]
    · have h1 : epsHom ρ (δ - δ') z = 0 := by
        rw [map_sub, LinearMap.sub_apply]
        exact sub_eq_zero.mpr hz
      have hunit : δ - δ' ≠ 0 := sub_ne_zero.mpr hδne.symm
      have h2 : epsHom ρ (δ - δ')⁻¹ (epsHom ρ (δ - δ') z) = z := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hunit, map_one,
          Module.End.one_apply]
      rw [← h2, h1, map_zero]
  by_cases hB : ∀ b ∈ A, b ∈ ρU.range → b = 1
  ·
    exfalso
    have hA2c : Nat.card A = 2 := hAtriv hB
    have h1 := hsemi ⊤ (fun u _ => AddSubgroup.mem_top _)
    have h2 : Nat.card {u : W // u ∈ (⊤ : AddSubgroup W) ∧ a.val u = u} =
        Nat.card {w : W // a.val w = w} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun w => by simp)
    rw [h2, Nat.card_congr (AddSubgroup.topEquiv (G := W)).toEquiv] at h1
    have h3 : Nat.card W ≤ 4 * Nat.card {w : W // a.val w = w} := by
      calc Nat.card W ≤ Nat.card A ^ 2 * C := hoff
        _ ≤ 4 * Nat.card {w : W // a.val w = w} := by
          rw [hA2c]
          exact Nat.mul_le_mul_left _ hCa
    have h4 := le_sixteen h3 h1
    rw [hW] at h4
    exact num_semi_triv hn hr1 horb
      ((Nat.pow_le_pow_iff_right (by norm_num)).mp (h4.trans (by norm_num)))
  · push Not at hB
    obtain ⟨g, hg1, hg2, hgA⟩ := exists_inner_involution ρ hρU hA2 hB
    let U : AddSubgroup W :=
      { carrier := {w | ρ g w = w}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_ofPred_eq, map_add] at hx hy ⊢
          rw [hx, hy]
        zero_mem' := by simp
        neg_mem' := fun {x} hx => by
          simp only [Set.mem_ofPred_eq, map_neg] at hx ⊢
          rw [hx] }
    have hU : ∀ u ∈ U, epsHom ρ δ u ∈ U := by
      intro u hu
      show ρ g (epsHom ρ δ u) = epsHom ρ δ u
      rw [← epsHom_commutes, show ρ g u = u from hu]
    have h1 := hsemi U hU
    have hCg := natCard_fixW_involution ρ b ιF ιD J hJne Φ g hg1 hg2
    rw [hr, hDcard, ← pow_mul] at hCg
    have hUcard : Nat.card U = 2 ^ (d * 2 ^ (r - 1)) := by
      rw [← hCg]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun w => Iff.rfl)
    have hCU : C ≤ Nat.card {u : W // u ∈ U ∧ a.val u = u} := by
      refine Nat.card_le_card_of_injective
        (fun w => ⟨w.1, ?_, w.2 a haA⟩) (fun w w' h => ?_)
      · have h5 := w.2 (ρU g) hgA
        rwa [hρU_val] at h5
      · simp only [Subtype.mk.injEq] at h
        exact Subtype.ext h
    have h2 : C ^ 2 ≤ 2 ^ (d * 2 ^ (r - 1)) :=
      (Nat.pow_le_pow_left hCU 2).trans (h1.trans hUcard.le)
    have h4 : 2 ^ (2 * (d * 2 ^ r)) ≤ 2 ^ (4 * (s + 1)) * 2 ^ (d * 2 ^ (r - 1)) := by
      calc 2 ^ (2 * (d * 2 ^ r)) = Nat.card W ^ 2 := by rw [hW, ← pow_mul, mul_comm]
        _ ≤ (Nat.card A ^ 2 * C) ^ 2 := Nat.pow_le_pow_left hoff 2
        _ = Nat.card A ^ 4 * C ^ 2 := by ring
        _ ≤ (2 ^ (s + 1)) ^ 4 * 2 ^ (d * 2 ^ (r - 1)) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hAcard 4) h2
        _ = 2 ^ (4 * (s + 1)) * 2 ^ (d * 2 ^ (r - 1)) := by rw [← pow_mul, mul_comm (s + 1)]
    rcases num_semi_nontriv hn hns hr1 hd1 horb (exp_le_of_pow_le h4) with
      ⟨hr1', h6⟩ | ⟨hr2, hd2, hs2⟩
    ·
      subst hr1'
      left
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hr
      have hj : j < n := hJn j (Finset.mem_singleton_self j)
      have hjd : (j + d) % n = j := by
        have h := hshift
        rw [Finset.image_singleton, Finset.singleton_inj] at h
        exact h
      have hnd : n ∣ d := by
        have h1 : (j + d) % n = (j + 0) % n := by rw [hjd, add_zero, Nat.mod_eq_of_lt hj]
        exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' j h1)
      obtain ⟨c, hc⟩ := hnd
      have hc1 : c = 1 := by
        rcases Nat.lt_or_ge c 2 with h | h
        · interval_cases c
          · omega
          · rfl
        · nlinarith
      subst hc1
      exact ⟨by rw [hDcard, hc, mul_one], by rw [hdim]; rfl⟩
    ·
      subst hr2 hd2 hs2
      right
      exact ⟨2, hns, hDcard, by rw [hdim, hr]; rfl⟩

theorem outer_class {n : ℕ} (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) SL(2, F) W) (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible)
    (A : Subgroup (Module.End (ZMod 2) W)ˣ) [CFSG.IsElementaryAbelian 2 A]
    (hAN : A ≤ Subgroup.normalizer (ρ.toHomUnits.range : Set (Module.End (ZMod 2) W)ˣ))
    (hoff : Nat.card W ≤ Nat.card A ^ 2 * Nat.card {w : W // ∀ a ∈ A, a.val w = w})
    (hAL : ¬ A ≤ ρ.toHomUnits.range) :
    (Nat.card (EndRing ρ) = 2 ^ n ∧ Module.finrank (EndRing ρ) W = 2) ∨
      ∃ s, n = 2 * s ∧ Nat.card (EndRing ρ) = 2 ^ s ∧ Module.finrank (EndRing ρ) W = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hne : (uElt (1 : F) : SL(2, F)) ≠ 1 := fun h =>
    one_ne_zero (uElt_injective (h.trans uElt_zero.symm))
  have hnt : ∃ g, ρ g ≠ 1 := ⟨uElt 1, fun h => hne (hρ (h.trans (map_one ρ).symm))⟩
  have hρU : Function.Injective ρ.toHomUnits := fun g h e =>
    hρ (by simpa using congrArg Units.val e)
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  obtain ⟨s, hs1, hns, hAcard, hAtriv, a, haA, -, x, hxconj⟩ :=
    outer_data (n := n) (by omega) ((Nat.card_eq_fintype_card (α := F)).trans hF) ρ hirr hρU A
      hAN hAL
  have hDfin : Finite (EndRing ρ) := finite_endRing ρ
  obtain ⟨d, hd1, hDcard, hdesc⟩ :=
    binary_SL2_irreducible_Frobenius_descent (n := n) (by omega) hF ρ hnt
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, hEF, hEfin, hEchar, ιF, ιD, J, hJne, hJn, ⟨Φ⟩, hshift, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  by_cases hlin : ∀ δ : EndRing ρ, a.val * epsHom ρ δ = epsHom ρ δ * a.val
  · exact Or.inr (outer_lin hn hs1 hns hF ρ hρU A hA2 hoff hAcard hAtriv haA x hxconj hlin hd1
      hDcard _ ιF ιD J hJne hJn Φ hshift hdim)
  · push Not at hlin
    obtain ⟨δ, hδ⟩ := hlin
    exact outer_semi hn hns ρ hρU A hA2 hAN hoff hAcard hAtriv haA hδ hd1 hDcard _ ιF ιD J hJne
      hJn Φ hshift hdim

end Class

end CFSG.Quasithin.B45L2
