module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightBC
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16g_cube_mod_three (n : ℕ) : n ^ 3 % 3 = n % 3 := by
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [show n ^ 3 % 3 = (n % 3) ^ 3 % 3 from Nat.pow_mod n 3 3]
  rcases hcases with h | h | h <;> rw [h] <;> norm_num

private theorem w16g_two_pow_three_pow_mod_three (k : ℕ) : 2 ^ (3 ^ k) % 3 = 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show (3 : ℕ) ^ (k + 1) = 3 ^ k * 3 from by rw [pow_succ], pow_mul,
      w16g_cube_mod_three, ih]

private theorem w16g_pCore_centralizes_conj_z (h : Cfg133 A t 3) {z : MulAut W}
    {N : Subgroup (MulAut W)} (hD : Data8 A t z N) {g : MulAut W} (hg : g ∈ A) :
    ∀ y ∈ pCoreOf 3 A, y * (g * z * g⁻¹) = (g * z * g⁻¹) * y := by
  classical
  set P : Subgroup (MulAut W) := ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ with hPdef
  set P' : Subgroup (MulAut W) := P.map (MulAut.conj g).toMonoidHom with hP'def
  set z' : MulAut W := g * z * g⁻¹ with hz'def
  obtain ⟨hPleO, hPg, hPne, htP, hPP, hOP⟩ := s13_P_facts (p := 3) h
  have hzP : z ∈ P := by rw [hPdef]; exact hD.hNP hD.hzN
  have hz'P' : z' ∈ P' := by
    rw [hP'def]
    exact Subgroup.mem_map.mpr ⟨z, hzP, by rw [hz'def]; rfl⟩
  have hzc' : ∀ y ∈ P', y * z' = z' * y := by
    intro y hy
    rw [hP'def] at hy
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
    rw [hz'def]
    change (MulAut.conj g) p * (MulAut.conj g) z = (MulAut.conj g) z * (MulAut.conj g) p
    rw [← map_mul, ← map_mul, hD.hzc p hp]
  have hZP' : ∀ x ∈ P', (∀ y ∈ P', y * x = x * y) → x ∈ Subgroup.zpowers z' := by
    intro x hx hxcent
    rw [hP'def] at hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    have hpcent : ∀ y ∈ P, y * p = p * y := by
      intro y hy
      have h1 := hxcent ((MulAut.conj g) y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      have h2 : (MulAut.conj g) (y * p) = (MulAut.conj g) (p * y) := by
        rw [map_mul, map_mul]
        exact h1
      exact (MulAut.conj g).injective h2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hD.hZP p hp hpcent)
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [← hj, map_zpow]
    simp only [hz'def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hO' : pCoreOf 3 A ≤ Subgroup.normalizer (P' : Set (MulAut W)) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    rw [hP'def] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨(g⁻¹ * y * g) * p * (g⁻¹ * y * g)⁻¹,
      hOP (g⁻¹ * y * g) ((s13_pCore_facts A 3).1 g⁻¹ (A.inv_mem hg) y hy) p hp, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hnorm := w16g_le_normalizer_zpowers_of_le_normalizer hz'P' hzc' hZP' hO'
  have hOg : IsPGroup 3 ↥(pCoreOf 3 A) := (s13_pCore_facts A 3).2.2
  have hz'pow : z' ^ 3 = 1 := by
    have h3 : z ^ 3 = 1 := by rw [← hD.hz3]; exact pow_orderOf_eq_one z
    calc z' ^ 3 = ((MulAut.conj g) z) ^ 3 := by rw [hz'def, MulAut.conj_apply]
      _ = (MulAut.conj g) (z ^ 3) := by rw [map_pow]
      _ = 1 := by rw [h3, map_one]
  have hz'ne : z' ≠ 1 := by
    intro h1
    have h2 : z = 1 := by
      have h3 : (MulAut.conj g) z = 1 := by
        rw [MulAut.conj_apply]; rw [show z' = 1 from h1] at hz'def
        exact hz'def.symm
      have h4 : (MulAut.conj g) z = (MulAut.conj g) 1 := by rw [h3, map_one]
      exact (MulAut.conj g).injective h4
    have hzord : orderOf (1 : MulAut W) = 3 := by rw [← h2]; exact hD.hz3
    rw [orderOf_one] at hzord
    omega
  have hz'ord : orderOf z' = 3 := orderOf_eq_prime hz'pow hz'ne
  intro y hy
  have hmem : y * z' * y⁻¹ ∈ Subgroup.zpowers z' :=
    ((Subgroup.mem_normalizer_iff.mp (hnorm hy)) z').mp (Subgroup.mem_zpowers z')
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hconj : y * z' * y⁻¹ = z' := by
    have hj' : z' ^ (j % 3) = y * z' * y⁻¹ := by
      rw [← hj, ← zpow_mod_orderOf z' j, hz'ord]
      rfl
    have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by
      have h1 : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0)
      have h2 : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
      omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hj'
      exact hz'ne (by
        calc z' = y⁻¹ * (y * z' * y⁻¹) * y := by group
          _ = y⁻¹ * 1 * y := by rw [← hj']
          _ = 1 := by group)
    · rw [h1, zpow_one] at hj'
      exact hj'.symm
    · have hyz : y * z' * y⁻¹ = z' ^ 2 := by
        rw [← hj', h2]
        rfl
      have hiter : ∀ m : ℕ, (y ^ m) * z' * (y ^ m)⁻¹ = z' ^ (2 ^ m) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          calc (y ^ (m + 1)) * z' * (y ^ (m + 1))⁻¹
              = y * ((y ^ m) * z' * (y ^ m)⁻¹) * y⁻¹ := by group
            _ = y * z' ^ (2 ^ m) * y⁻¹ := by rw [ih]
            _ = ((MulAut.conj y) z') ^ (2 ^ m) := by
                  rw [← map_pow (MulAut.conj y) z' (2 ^ m)]
                  rfl
            _ = (z' ^ 2) ^ (2 ^ m) := by rw [MulAut.conj_apply, hyz]
            _ = z' ^ (2 ^ (m + 1)) := by
                  rw [← pow_mul, mul_comm, ← pow_succ]
      obtain ⟨k, hk⟩ := hOg ⟨y, hy⟩
      have hfix : (y ^ (3 ^ k)) * z' * (y ^ (3 ^ k))⁻¹ = z' := by
        have hk' : y ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
        rw [hk']; group
      rw [hiter (3 ^ k), ← pow_mod_orderOf z' (2 ^ (3 ^ k)), hz'ord,
        w16g_two_pow_three_pow_mod_three] at hfix
      have hz1 : z' = 1 := by
        have h2' : z' * z' = z' * 1 := by rw [mul_one]; simpa [pow_two] using hfix
        exact mul_left_cancel h2'
      exfalso
      exact hz'ne hz1
  calc y * z' = (y * z' * y⁻¹) * y := by group
    _ = z' * y := by rw [hconj]

theorem w16g_s13_eight_X_facts (h : Cfg133 A t 3) {z : MulAut W}
    {N : Subgroup (MulAut W)} (hD : Data8 A t z N) :
    IsElemAbelian 3 (conjClosure A (Subgroup.zpowers z)) ∧
      (∀ g ∈ A, ∀ x ∈ conjClosure A (Subgroup.zpowers z),
        g * x * g⁻¹ ∈ conjClosure A (Subgroup.zpowers z)) ∧
      conjClosure A (Subgroup.zpowers z) ≤ pCoreOf 3 A ∧
      ∀ y ∈ pCoreOf 3 A, ∀ x ∈ conjClosure A (Subgroup.zpowers z), y * x = x * y := by
  classical
  obtain ⟨hPleO, hPg, hPne, htP, hPP, hOP⟩ := s13_P_facts (p := 3) h
  have hzP : z ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ := hD.hNP hD.hzN
  have hzO : z ∈ pCoreOf 3 A := hPleO hzP
  have hON : ∀ g ∈ A, ∀ o ∈ pCoreOf 3 A, g * o * g⁻¹ ∈ pCoreOf 3 A :=
    (s13_pCore_facts A 3).1
  have hgen_mem : ∀ g ∈ A, ∀ y ∈ Subgroup.zpowers z,
      g * y * g⁻¹ ∈ conjClosure A (Subgroup.zpowers z) :=
    fun g hg y hy => Subgroup.subset_closure ⟨g, hg, y, hy, rfl⟩
  have hXO : conjClosure A (Subgroup.zpowers z) ≤ pCoreOf 3 A := by
    rw [conjClosure, Subgroup.closure_le]
    rintro x ⟨g, hg, y, hy, rfl⟩
    exact hON g hg y ((Subgroup.zpowers_le.mpr hzO) hy)
  have hcent : ∀ y ∈ pCoreOf 3 A, ∀ x ∈ conjClosure A (Subgroup.zpowers z), y * x = x * y := by
    intro y hy x hx
    refine Subgroup.closure_induction (p := fun x _ => y * x = x * y) ?_ ?_ ?_ ?_ hx
    · rintro c ⟨g, hg, w, hw, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hconv : g * z ^ n * g⁻¹ = (g * z * g⁻¹) ^ n := by
        rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      rw [hconv]
      exact (show Commute y (g * z * g⁻¹) from
        w16g_pCore_centralizes_conj_z h hD hg y hy).zpow_right n
    · rw [mul_one, one_mul]
    · intro a b _ _ ha hb
      exact (show Commute y a from ha).mul_right (show Commute y b from hb)
    · intro a _ ha
      exact (show Commute y a from ha).inv_right
  have hXA : ∀ g ∈ A, ∀ x ∈ conjClosure A (Subgroup.zpowers z),
      g * x * g⁻¹ ∈ conjClosure A (Subgroup.zpowers z) := by
    intro g hg x hx
    refine Subgroup.closure_induction
      (p := fun x _ => g * x * g⁻¹ ∈ conjClosure A (Subgroup.zpowers z)) ?_ ?_ ?_ ?_ hx
    · rintro c ⟨g', hg', w, hw, rfl⟩
      exact Subgroup.subset_closure ⟨g * g', A.mul_mem hg hg', w, hw, by group⟩
    · simpa using Subgroup.one_mem (conjClosure A (Subgroup.zpowers z))
    · intro a b _ _ ha hb
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  have hXe : IsElemAbelian 3 (conjClosure A (Subgroup.zpowers z)) := by
    rw [conjClosure]
    refine IsElemAbelian.closure_of_commute
      (s := {x | ∃ g ∈ A, ∃ y ∈ Subgroup.zpowers z, x = g * y * g⁻¹}) ?_ ?_
    · rintro a ⟨g, hg, y, hy, rfl⟩ b ⟨g', hg', y', hy', rfl⟩
      exact hcent (g * y * g⁻¹) (hXO (hgen_mem g hg y hy))
        (g' * y' * g'⁻¹) (hgen_mem g' hg' y' hy')
    · rintro a ⟨g, hg, y, hy, rfl⟩
      have hy3 : y ^ 3 = 1 := by
        have h1 : Nat.card ↥(Subgroup.zpowers y) ∣ Nat.card ↥(Subgroup.zpowers z) :=
          Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hy)
        rw [Nat.card_zpowers y, Nat.card_zpowers z, hD.hz3] at h1
        exact orderOf_dvd_iff_pow_eq_one.mp h1
      calc (g * y * g⁻¹) ^ 3 = ((MulAut.conj g) y) ^ 3 := by rw [MulAut.conj_apply]
        _ = (MulAut.conj g) (y ^ 3) := by rw [map_pow]
        _ = 1 := by rw [hy3, map_one]
  exact ⟨hXe, hXA, hXO, hcent⟩

end CFSG.LocalAnalysis.WeakClosure81
