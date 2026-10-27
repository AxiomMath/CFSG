module

public import CFSG.RankThree.PartTwo.Sec12.Item125Diag

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

@[expose] def KS125TypeCInvolSU : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
    (∃ (q : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
      Even q ∧ Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 q K)) →
    ∀ x : X, x ∉ Subgroup.center X → x ^ 3 = 1 →
    ∀ Y : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 Y → Nat.card Y = 9 →
      MulAut.conj x ∈ Y → (∀ σ ∈ Y, σ x = x) →
      ∃ σ ∈ Y, σ ≠ 1 ∧ ∃ P : Subgroup X, P ≠ ⊥ ∧ IsPGroup 2 P ∧ ∀ p ∈ P, σ p ∈ P

namespace Item125Diag

section Matrix

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_involution_commute_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hp2 : p ≠ 2) {x : GL (Fin 3) K} (hx : x ∈ slPi π 3 (p ^ f) K) (hx3 : x ^ 3 = 1)
    (hxs : x ∉ StatedScalars (Fin 3) K) :
    ∃ u ∈ slPi π 3 (p ^ f) K, u ^ 2 = 1 ∧ u ≠ 1 ∧ u * x = x * u := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hxH : x ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hx
  have hμ : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) ((1 : Kˣ) ^ 3) := by
    rw [one_pow, map_one, hx3]
  obtain ⟨y, ⟨z, hzZ, rfl⟩, g, hg, hcase⟩ := exists_diag_normal_form hK hq hτ hτ1 hxH hxs hμ
  have hzZ' := (zPi_eq hπ hq' hτ hτ1) ▸ hzZ
  have hzS : z ∈ StatedScalars (Fin 3) K := (Subgroup.mem_inf.mp hzZ').2
  have hzc : ∀ h : GL (Fin 3) K, h * z = z * h := fun h => commute_of_mem_statedScalars hzS h
  set Mg := g⁻¹ * (x * z) * g with hMg
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, (Mg : Matrix (Fin 3) (Fin 3) K) = diagonal v := by
    rcases hcase with hD | ⟨e, -, hD⟩
    · exact ⟨_, by rw [hD, coe_diagTau_eq_diagonal]⟩
    · exact ⟨_, by rw [hD, coe_diagE]⟩
  set D : GL (Fin 3) K := diagUnits (-1) (-1) 1 with hDdef
  have hDcoe : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![-1, -1, 1] := by
    rw [hDdef, coe_diagUnits]
    simp
  have hDcomm : D * Mg = Mg * D := by
    apply Units.ext
    rw [Units.val_mul D Mg, Units.val_mul Mg D, hv, hDcoe, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have hD2 : D ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hDcoe, diagonal_pow, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  have hDH : D ∈ glPi π 3 (p ^ f) K := by
    cases π
    · rw [mem_glPi_false (hπ rfl), hDcoe, diagonal_map (map_zero _), diagonal_transpose,
        diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp
    · exact mem_glPi_true _ D
  set u := g * D * g⁻¹ with hu
  refine ⟨u, (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hg hDH) (inv_mem hg), ?_⟩, ?_, ?_, ?_⟩
  · rw [hu, Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one, one_mul, hDcoe, det_diagonal,
      Fin.prod_univ_three]
    simp
  · rw [hu, conj_pow, hD2, mul_one, mul_inv_cancel]
  · intro h1
    have hD1 : D = 1 := by
      calc D = g⁻¹ * (g * D * g⁻¹) * g := by group
        _ = 1 := by rw [← hu, h1]; group
    have h00 := congrArg (fun w : GL (Fin 3) K => (w : Matrix (Fin 3) (Fin 3) K) 0 0) hD1
    simp only [hDcoe, Units.val_one, one_apply_eq, diagonal_apply_eq] at h00
    have h2 : (2 : K) = 0 := by
      have : (-1 : K) = 1 := by simpa using h00
      linear_combination -this
    have := hK.charP
    have hp2' : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h2)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_two).mp hp2')
  ·
    have h1 : u * (x * z) = (x * z) * u := by
      calc u * (x * z) = g * (D * Mg) * g⁻¹ := by rw [hu, hMg]; group
        _ = g * (Mg * D) * g⁻¹ := by rw [hDcomm]
        _ = (x * z) * u := by rw [hu, hMg]; group
    calc u * x = u * (x * z) * z⁻¹ := by group
      _ = (x * z) * u * z⁻¹ := by rw [h1]
      _ = x * (z * u) * z⁻¹ := by group
      _ = x * (u * z) * z⁻¹ := by rw [hzc u]
      _ = x * u := by group

@[expose] noncomputable def rootGroup (K : Type) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ a : K, (g : Matrix (Fin 3) (Fin 3) K) = transvection 0 1 a}
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by
      rw [Units.val_mul, ha, hb, transvection_mul_transvection_same _ _ (by decide)]⟩
  one_mem' := ⟨0, by rw [transvection_zero, Units.val_one]⟩
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have h1 : (g : Matrix (Fin 3) (Fin 3) K) * transvection 0 1 (-a) = 1 := by
      rw [ha, transvection_mul_transvection_same _ _ (by decide), add_neg_cancel,
        transvection_zero]
    calc ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : Matrix (Fin 3) (Fin 3) K) * transvection 0 1 (-a)) := by rw [h1, Matrix.mul_one]
      _ = transvection 0 1 (-a) := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem diagonal_mul_transvection (v : Fin 3 → K) (hv : v 1 ≠ 0) (a : K) :
    diagonal v * transvection 0 1 a = transvection 0 1 (v 0 * a / v 1) * diagonal v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, transvection, Matrix.single, diagonal, hv]

theorem exists_rootGroup_slPi (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    (hp2 : p = 2) {x : GL (Fin 3) K} (hx3 : x ^ 3 = 1) (hxs : x ∉ StatedScalars (Fin 3) K) :
    ∃ P : Subgroup (GL (Fin 3) K), P ≤ slPi true 3 (p ^ f) K ∧ P ≠ ⊥ ∧ IsPGroup 2 P ∧
      ∀ g ∈ P, x * g * x⁻¹ ∈ P := by
  have hπ : true = false → UnitaryFieldData p f K := fun h => absurd h (by decide)
  have hq' : true = false → ModThree false (p ^ f) := fun h => absurd h (by decide)
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hxH : x ∈ glPi true 3 (p ^ f) K := mem_glPi_true _ x
  have hμ : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) ((1 : Kˣ) ^ 3) := by
    rw [one_pow, map_one, hx3]
  obtain ⟨y, ⟨z, hzZ, rfl⟩, g, hg, hcase⟩ := exists_diag_normal_form hK hq hτ hτ1 hxH hxs hμ
  have hzZ' := (zPi_eq hπ hq' hτ hτ1) ▸ hzZ
  have hzS : z ∈ StatedScalars (Fin 3) K := (Subgroup.mem_inf.mp hzZ').2
  have hzc : ∀ h : GL (Fin 3) K, h * z = z * h := fun h => commute_of_mem_statedScalars hzS h
  set Mg := g⁻¹ * (x * z) * g with hMg
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, (Mg : Matrix (Fin 3) (Fin 3) K) = diagonal v := by
    rcases hcase with hD | ⟨e, -, hD⟩
    · exact ⟨_, by rw [hD, coe_diagTau_eq_diagonal]⟩
    · exact ⟨_, by rw [hD, coe_diagE]⟩
  have hv1 : v 1 ≠ 0 := by
    intro h0
    have hdet : (Mg : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
      have h1 := congrArg Matrix.det (Units.mul_inv Mg)
      rw [det_mul, det_one] at h1
      exact left_ne_zero_of_mul_eq_one h1
    rw [hv, det_diagonal, Fin.prod_univ_three, h0, mul_zero, zero_mul] at hdet
    exact hdet rfl
  set P := (rootGroup K).map (MulAut.conj g).toMonoidHom with hP
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨r, ⟨a, ha⟩, rfl⟩
    rw [mem_slPi_true]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, ha, det_transvection_of_ne _ _ (by decide),
      mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
  · intro h
    set r : GL (Fin 3) K := ⟨transvection 0 1 1, transvection 0 1 (-1),
      by rw [transvection_mul_transvection_same _ _ (by decide), add_neg_cancel,
        transvection_zero],
      by rw [transvection_mul_transvection_same _ _ (by decide), neg_add_cancel,
        transvection_zero]⟩ with hr
    have hrP : g * r * g⁻¹ ∈ P := ⟨r, ⟨1, rfl⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hrP
    have hr1 : r = 1 := by
      calc r = g⁻¹ * (g * r * g⁻¹) * g := by group
        _ = 1 := by rw [hrP]; group
    have h01 := congrArg (fun w : GL (Fin 3) K => (w : Matrix (Fin 3) (Fin 3) K) 0 1) hr1
    simp [hr, transvection, Matrix.single] at h01
  · have : CharP K 2 := hp2 ▸ hK.charP
    rintro ⟨w, ⟨r, ⟨a, ha⟩, rfl⟩⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← map_pow]
    have hr2 : r ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ha, sq, transvection_mul_transvection_same _ _ (by decide),
        ← two_mul, CharTwo.two_eq_zero, zero_mul, transvection_zero, Units.val_one]
    rw [hr2, map_one]
  · rintro _ ⟨r, ⟨a, ha⟩, rfl⟩
    have hconj : ((Mg * r * Mg⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        transvection 0 1 (v 0 * a / v 1) := by
      rw [Units.val_mul (Mg * r) Mg⁻¹, Units.val_mul Mg r, hv, ha,
        diagonal_mul_transvection v hv1 a, Matrix.mul_assoc, ← hv, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
    refine ⟨Mg * r * Mg⁻¹, ⟨_, hconj⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hxe : x = g * Mg * g⁻¹ * z⁻¹ := by rw [hMg]; group
    have hzi : ∀ w : GL (Fin 3) K, z⁻¹ * w * z = w := fun w => by
      rw [mul_assoc, hzc w, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hxe]
    calc g * (Mg * r * Mg⁻¹) * g⁻¹
        = g * Mg * g⁻¹ * (z⁻¹ * (g * r * g⁻¹) * z) * (g * Mg⁻¹ * g⁻¹) := by
          rw [hzi]; group
      _ = g * Mg * g⁻¹ * z⁻¹ * (g * r * g⁻¹) * (g * Mg * g⁻¹ * z⁻¹)⁻¹ := by group

end Matrix

theorem exists_involution_commute_of_odd {X : Type} [Group X] [Finite X] {q : ℕ}
    (hX : Sec4.IsSLThreePiAt X q) (hq2 : Odd q) {x : X} (hxZ : x ∉ Subgroup.center X)
    (hx3 : x ^ 3 = 1) : ∃ u : X, u ^ 2 = 1 ∧ u ≠ 1 ∧ u * x = x * u := by
  obtain ⟨K, _, _, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hp2 : ringChar K ≠ 2 := by
    intro h2
    have hKodd : Odd (Nat.card K) := by
      rcases hcase with ⟨hK, -, -⟩ | ⟨hK, -, -⟩
      · rw [hK]; exact hq2
      · rw [hK]; exact hq2.pow
    rw [hnc, h2] at hKodd
    exact (Nat.not_even_iff_odd.mpr hKodd) ((Nat.even_pow' n.2.ne').mpr even_two)
  obtain ⟨π, f, hK, hq, ⟨e⟩⟩ : ∃ (π : Bool) (f : ℕ), PiField π (ringChar K) f K ∧
      ModThree π (ringChar K ^ f) ∧ Nonempty (X ≃* slPi π 3 (ringChar K ^ f) K) := by
    rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
    · refine ⟨true, n, ⟨hp, n.2, hnc⟩, ?_, ⟨e⟩⟩
      change ringChar K ^ (n : ℕ) % 3 = 1
      rw [← hnc, hK]
      exact hq
    · have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, pow_zero] at hm
          rw [hm] at hq
          norm_num at hq
        · exact h0
      refine ⟨false, m, ⟨hp, hm1, by rw [hK, hm]; rfl⟩, ?_, ⟨hm ▸ e⟩⟩
      change ringChar K ^ m % 3 = 2
      rw [← hm]
      exact hq
  set A : GL (Fin 3) K := (e x : GL (Fin 3) K) with hA
  have hAmem : A ∈ slPi π 3 (ringChar K ^ f) K := (e x).2
  have hA3 : A ^ 3 = 1 := by
    rw [hA, ← Subgroup.coe_pow, ← map_pow, hx3, map_one]
    rfl
  have hAs : A ∉ StatedScalars (Fin 3) K := by
    intro hs
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro w
    apply e.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (commute_of_mem_statedScalars hs (e w : GL (Fin 3) K))
  obtain ⟨u, hu, hu2, hu1, hux⟩ := exists_involution_commute_slPi hK hq hp2 hAmem hA3 hAs
  refine ⟨e.symm ⟨u, hu⟩, ?_, ?_, ?_⟩
  · rw [← map_pow]
    have h1 : (⟨u, hu⟩ : slPi π 3 (ringChar K ^ f) K) ^ 2 = 1 := Subtype.ext hu2
    rw [h1, map_one]
  · intro h1
    apply hu1
    have h2 := congrArg e h1
    rw [MulEquiv.apply_symm_apply, map_one] at h2
    exact congrArg Subtype.val h2
  · apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext hux

theorem ks125TypeCInvol_odd {X : Type} [Group X] [Finite X] {q : ℕ}
    (hX : Sec4.IsSLThreePiAt X q) (hq2 : Odd q) {x : X} (hxZ : x ∉ Subgroup.center X)
    (hx3 : x ^ 3 = 1) {Y : Subgroup (MulAut X)} (hxY : MulAut.conj x ∈ Y) :
    ∃ σ ∈ Y, σ ≠ 1 ∧ ∃ P : Subgroup X, P ≠ ⊥ ∧ IsPGroup 2 P ∧ ∀ p ∈ P, σ p ∈ P := by
  obtain ⟨u, hu2, hu1, hux⟩ := exists_involution_commute_of_odd hX hq2 hxZ hx3
  refine ⟨MulAut.conj x, hxY, fun h => hxZ (mem_center_of_conj_eq_one h),
    Subgroup.zpowers u, ?_, ?_, ?_⟩
  · intro h
    apply hu1
    have hmem : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  · rintro ⟨w, hw⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hu2,
      _root_.one_zpow]
  · intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [map_zpow, MulAut.conj_apply, ← hux, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) k

theorem ks125TypeCInvol_sl_even {X : Type} [Group X] [Finite X] {q : ℕ} {K : Type} [Field K]
    [Finite K] (hKq : Nat.card K = q) (hq3 : q % 3 = 1) (hq2 : Even q)
    (e : X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) {x : X} (hxZ : x ∉ Subgroup.center X)
    (hx3 : x ^ 3 = 1) {Y : Subgroup (MulAut X)} (hxY : MulAut.conj x ∈ Y) :
    ∃ σ ∈ Y, σ ≠ 1 ∧ ∃ P : Subgroup X, P ≠ ⊥ ∧ IsPGroup 2 P ∧ ∀ p ∈ P, σ p ∈ P := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hp2 : ringChar K = 2 := by
    have h2 : 2 ∣ ringChar K ^ (n : ℕ) := by rw [← hnc, hKq]; exact even_iff_two_dvd.mp hq2
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hK : PiField true (ringChar K) n K := ⟨hp, n.2, hnc⟩
  have hq : ModThree true (ringChar K ^ (n : ℕ)) := by
    change ringChar K ^ (n : ℕ) % 3 = 1
    rw [← hnc, hKq]
    exact hq3
  set A : GL (Fin 3) K := (e x : GL (Fin 3) K) with hA
  have hA3 : A ^ 3 = 1 := by
    rw [hA, ← Subgroup.coe_pow, ← map_pow, hx3, map_one]
    rfl
  have hAs : A ∉ StatedScalars (Fin 3) K := by
    intro hs
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro w
    apply e.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (commute_of_mem_statedScalars hs (e w : GL (Fin 3) K))
  obtain ⟨P, hPS, hP1, hP2, hPx⟩ := exists_rootGroup_slPi hK hq hp2 hA3 hAs
  set P' : Subgroup X :=
    (P.subgroupOf (CFSG.Assembly.LowTwoRank.StatedSL 3 K)).map e.symm.toMonoidHom with hP'
  refine ⟨MulAut.conj x, hxY, fun h => hxZ (mem_center_of_conj_eq_one h), P', ?_, ?_, ?_⟩
  · obtain ⟨⟨w, hwP⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hP1
    intro hbot
    have hmem : e.symm ⟨w, hPS hwP⟩ ∈ P' :=
      ⟨⟨w, hPS hwP⟩, Subgroup.mem_subgroupOf.mpr hwP, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hw1
    apply Subtype.ext
    have h1 := congrArg e hmem
    rw [MulEquiv.apply_symm_apply, map_one] at h1
    exact congrArg (fun m : CFSG.Assembly.LowTwoRank.StatedSL 3 K => (m : GL (Fin 3) K)) h1
  · exact (hP2.comap_subtype).map _
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨e x * w * (e x)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have h1 := hPx _ (Subgroup.mem_subgroupOf.mp hw)
      simpa using h1
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      apply e.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end Item125Diag

theorem ks125TypeCInvol_of_su (h : KS125TypeCInvolSU) : KS125TypeCInvol := by
  intro X _ _ hq hX x hxZ hx3 Y hYe hY9 hxY hfix
  obtain ⟨q, hXq⟩ := hX
  rcases Nat.even_or_odd q with he | ho
  · obtain ⟨K, _, _, hcase⟩ := hXq
    rcases hcase with ⟨hK, hq3, ⟨e⟩⟩ | ⟨hK, hq3, ⟨e⟩⟩
    · exact Item125Diag.ks125TypeCInvol_sl_even hK hq3 he e hxZ hx3 hxY
    · exact h X hq ⟨q, K, inferInstance, inferInstance, hK, hq3, he, ⟨e⟩⟩ x hxZ hx3 Y hYe hY9
        hxY hfix
  · exact Item125Diag.ks125TypeCInvol_odd hXq ho hxZ hx3 hxY

theorem item125Diag_of_su
    (h45 : Sec4.Item4_5)
    (h : KS125TypeCInvolSU) : Item125Diag :=
  item125Diag_of h45 (ks125TypeCInvol_of_su h)

end CFSG.RankThree.PartTwo.Sec12
