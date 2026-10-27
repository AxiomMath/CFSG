module

public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section SL

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem cycThree_pow_three' : (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycThree, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem exists_conj_eq_smul_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {x : GL (Fin 3) K} (hx : x ∈ slPi π 3 (p ^ f) K) (hx3 : x ^ 3 = 1)
    (hxs : x ∉ StatedScalars (Fin 3) K) :
    ∃ w ∈ slPi π 3 (p ^ f) K, w ^ 3 = 1 ∧
      ((w * x * w⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        τ ^ 2 • (x : Matrix (Fin 3) (Fin 3) K) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hxH : x ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hx
  have hμ : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) ((1 : Kˣ) ^ 3) := by
    rw [one_pow, map_one, hx3]
  obtain ⟨y, ⟨z, hzZ, rfl⟩, g, hg, hcase⟩ := exists_diag_normal_form hK hq hτ hτ1 hxH hxs hμ
  have hzZ' := (zPi_eq hπ hq' hτ hτ1) ▸ hzZ
  have hzS : z ∈ StatedScalars (Fin 3) K := (Subgroup.mem_inf.mp hzZ').2
  have hzc : ∀ h : GL (Fin 3) K, h * z = z * h := fun h => commute_of_mem_statedScalars hzS h
  have hxz3 : (x * z) ^ 3 = z ^ 3 := by
    rw [(Commute.mul_pow (hzc x) 3), hx3, one_mul]
  rcases hcase with hD | ⟨e, he, hD⟩
  ·
    set w := g * cycThree * g⁻¹ with hw
    have hCH : cycThree ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ (cycThree_mem_slPi hπ)
    have hwH : w ∈ glPi π 3 (p ^ f) K := mul_mem (mul_mem hg hCH) (inv_mem hg)
    have hwdet : (w : Matrix (Fin 3) (Fin 3) K).det = 1 := by
      have hC := (mem_slPi_iff hπ).mp (cycThree_mem_slPi hπ (K := K))
      rw [hw, Units.val_mul, Units.val_mul, det_mul, det_mul, hC.2, mul_one,
        ← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    have hwS : w ∈ slPi π 3 (p ^ f) K := (mem_slPi_iff hπ).mpr ⟨hwH, hwdet⟩
    have hw3 : w ^ 3 = 1 := by rw [hw, conj_pow, cycThree_pow_three', mul_one, mul_inv_cancel]
    refine ⟨w, hwS, hw3, ?_⟩
    have hxe : x = g * diagTau hτ * g⁻¹ * z⁻¹ := by
      rw [← hD]
      group
    have hconj : w * x * w⁻¹ = g * (cycThree * diagTau hτ * cycThree⁻¹) * g⁻¹ * z⁻¹ := by
      have hzi : ∀ h : GL (Fin 3) K, h * z⁻¹ = z⁻¹ * h := fun h => by
        have := hzc h
        calc h * z⁻¹ = z⁻¹ * (z * h) * z⁻¹ := by group
          _ = z⁻¹ * (h * z) * z⁻¹ := by rw [this]
          _ = z⁻¹ * h := by group
      rw [hw, hxe]
      calc g * cycThree * g⁻¹ * (g * diagTau hτ * g⁻¹ * z⁻¹) * (g * cycThree * g⁻¹)⁻¹
          = g * cycThree * diagTau hτ * g⁻¹ * (z⁻¹ * (g * cycThree⁻¹ * g⁻¹)) := by group
        _ = g * cycThree * diagTau hτ * g⁻¹ * ((g * cycThree⁻¹ * g⁻¹) * z⁻¹) := by
          rw [hzi (g * cycThree⁻¹ * g⁻¹)]
        _ = g * (cycThree * diagTau hτ * cycThree⁻¹) * g⁻¹ * z⁻¹ := by group
    rw [hconj, Units.val_mul, Units.val_mul, Units.val_mul, cycThree_conj_diagTau hτ,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hxe]
    simp only [Units.val_mul, Matrix.mul_assoc]
  ·
    exfalso
    obtain ⟨ζ, rfl⟩ := hzS
    have he3 : (e : K) ^ 3 = 1 := by
      rcases he with he | he
      · rw [he, hτ]
      · rw [he, ← pow_mul, mul_comm, pow_mul, hτ, one_pow]
    have hD3 : (diagE e : GL (Fin 3) K) ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, coe_diagE, diagonal_pow, Units.val_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [he3]
    have hconj3 : ∀ a b : GL (Fin 3) K, (a⁻¹ * b * a) ^ 3 = a⁻¹ * b ^ 3 * a := fun a b => by
      simp only [pow_succ, pow_zero, one_mul]
      group
    have hy3 : (x * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 = 1 := by
      have h1 : g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 * g = 1 := by
        rw [← hconj3, hD, hD3]
      calc (x * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3
          = g * (g⁻¹ * (x * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 * g) * g⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
    have hz3 : GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) = 1 := by
      rw [map_pow, ← hxz3, hy3]
    have hζ3 : (ζ : K) ^ 3 = 1 := by
      have h := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K) 0 0) hz3
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Units.val_one, Matrix.one_apply_eq] at h
      rw [← Units.val_pow_eq_pow_val, h]
    have hdet := congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K).det) hD
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one, one_mul, Units.val_mul, det_mul,
      ((mem_slPi_iff hπ).mp hx).2, one_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      det_diagonal, Fin.prod_univ_three, coe_diagE, det_diagonal, Fin.prod_univ_three] at hdet
    have h1 : (e : K) = 1 := by
      have : (ζ : K) * ζ * ζ = 1 := by rw [← hζ3]; ring
      simpa [this] using hdet.symm
    rcases he with he | he
    · exact hτ1 (he ▸ h1)
    · apply hτ1
      have h2 : τ ^ 2 = 1 := he ▸ h1
      linear_combination hτ - τ * h2

theorem exists_normalizer_moves_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (T : Subgroup (slPi π 3 (p ^ f) K)) (hTe : ∀ t ∈ T, t ^ 3 = 1) (hT9 : Nat.card T = 9)
    (hZT : Subgroup.center (slPi π 3 (p ^ f) K) ≤ T) :
    ∃ x ∈ Subgroup.normalizer (T : Set (slPi π 3 (p ^ f) K)), IsPGroup 3 (Subgroup.zpowers x) ∧
      ∃ t ∈ T, x * t * x⁻¹ ≠ t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  set Z := Subgroup.center (slPi π 3 (p ^ f) K) with hZdef
  have hZ3 : Nat.card Z = 3 := card_center_slPi hK hq
  obtain ⟨d, hdT, hdZ⟩ : ∃ d ∈ T, d ∉ Z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show T ≤ Z from hcon)
    rw [hT9, hZ3] at this
    omega
  have hd3 : d ^ 3 = 1 := hTe d hdT
  have hd1 : d ≠ 1 := fun h => hdZ (h ▸ Z.one_mem)
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hds : (d : GL (Fin 3) K) ∉ StatedScalars (Fin 3) K := by
    intro hs
    apply hdZ
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_statedScalars hs (g : GL (Fin 3) K))
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ; norm_num at hτ
  obtain ⟨w, hwS, hw3, hwd⟩ := exists_conj_eq_smul_slPi hK hq hτ hτ1 d.2
    (by rw [← Subgroup.coe_pow, hd3]; rfl) hds
  set ζ : Kˣ := Units.mk0 (τ ^ 2) (pow_ne_zero _ hτ0) with hζ
  have hζ3 : ζ ^ 3 = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hζ, Units.val_mk0, ← pow_mul, mul_comm, pow_mul, hτ, one_pow,
      Units.val_one])
  set s : slPi π 3 (p ^ f) K :=
    ⟨GeneralLinearGroup.scalar (Fin 3) ζ, scalar_mem_slPi_of_pow_three hK hq hζ3⟩
  have hsZ : s ∈ Z := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ (g : GL (Fin 3) K)).eq
  have hs1 : s ≠ 1 := by
    intro h1
    have h := congrArg (fun u : slPi π 3 (p ^ f) K =>
      ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [s, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      OneMemClass.coe_one, Units.val_one, Matrix.one_apply_eq, hζ, Units.val_mk0] at h
    apply hτ1
    linear_combination hτ - τ * h
  set w' : slPi π 3 (p ^ f) K := ⟨w, hwS⟩
  have hw'd : w' * d * w'⁻¹ = s * d := by
    apply Subtype.ext
    apply Units.ext
    change ((w * d * w⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((GeneralLinearGroup.scalar (Fin 3) ζ * d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hwd, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, hζ, Units.val_mk0]
  have hdc : d ∈ Subgroup.centralizer (Z : Set (slPi π 3 (p ^ f) K)) :=
    Subgroup.mem_centralizer_iff.mpr fun z hz => (Subgroup.mem_center_iff.mp hz d).symm
  have hZe : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => hTe z (hZT hz)
  have hdisj : Z ⊓ Subgroup.zpowers d = ⊥ := by
    have hcard : Nat.card (Subgroup.zpowers d) = 3 := by rw [Nat.card_zpowers, hdo]
    have : Fact (Nat.card (Subgroup.zpowers d)).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Z.subgroupOf (Subgroup.zpowers d)) with h | h
    · rw [eq_bot_iff]
      intro y ⟨hyZ, hyd⟩
      have hy : (⟨y, hyd⟩ : Subgroup.zpowers d) ∈ Z.subgroupOf (Subgroup.zpowers d) := hyZ
      rw [h] at hy
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hy))
    · exfalso
      have hd : (⟨d, Subgroup.mem_zpowers d⟩ : Subgroup.zpowers d) ∈
          Z.subgroupOf (Subgroup.zpowers d) := by rw [h]; trivial
      exact hdZ hd
  obtain ⟨hcard9, -, -⟩ := card_sup_zpowers_of_disjoint hdc
    (⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm⟩⟩ : IsMulCommutative Z)
    hZe hdo
    hdisj
  have hTeq : Z ⊔ Subgroup.zpowers d = T := Subgroup.eq_of_le_of_card_ge
    (sup_le hZT (Subgroup.zpowers_le.mpr hdT)) (by rw [hT9, hcard9, hZ3])
  have hw'N : w' ∈ Subgroup.normalizer (T : Set (slPi π 3 (p ^ f) K)) := by
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    rw [← hTeq] at ht ⊢
    have hmap : (Z ⊔ Subgroup.zpowers d).map (MulAut.conj w').toMonoidHom ≤
        Z ⊔ Subgroup.zpowers d := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        refine Subgroup.mem_sup_left ?_
        change w' * z * w'⁻¹ ∈ Z
        rw [(Subgroup.mem_center_iff.mp hz w'), mul_inv_cancel_right]
        exact hz
      · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
        change w' * d * w'⁻¹ ∈ Z ⊔ Subgroup.zpowers d
        rw [hw'd]
        exact mul_mem (Subgroup.mem_sup_left hsZ) (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
    exact hmap ⟨t, ht, rfl⟩
  refine ⟨w', hw'N, fun g => ⟨1, ?_⟩, d, hdT, ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    have hw'3 : w' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hw3)
    change (g : slPi π 3 (p ^ f) K) ^ 3 ^ 1 = 1
    rw [← hk, pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      zpow_natCast, hw'3, _root_.one_zpow]
  · rw [hw'd]
    intro h
    apply hs1
    have := congrArg (fun u => u * d⁻¹) h
    simpa using this

end SL

theorem exists_normalizer_moves_of_isSLThreePi {X : Type} [Group X] [Finite X]
    (hX : Sec4.IsSLThreePi X) (T : Subgroup X) (hT : CFSG.Assembly.IsElemAbelian 3 T)
    (hT9 : Nat.card T = 9) (hZT : Subgroup.center X ≤ T) :
    ∃ x ∈ Subgroup.normalizer (T : Set X), IsPGroup 3 (Subgroup.zpowers x) ∧
      ∃ t ∈ T, x * t * x⁻¹ ≠ t := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
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
  set S := slPi π 3 (ringChar K ^ f) K
  set T' : Subgroup S := T.map e.toMonoidHom with hT'
  have hT'9 : Nat.card T' = 9 := by
    rw [hT', Subgroup.card_map_of_injective e.injective, hT9]
  have hT'e : ∀ t ∈ T', t ^ 3 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, hT.2 t ht, map_one]
  have hZT' : Subgroup.center S ≤ T' := by
    rw [← Subgroup.map_center_eq e, hT']
    exact Subgroup.map_mono hZT
  obtain ⟨x, hxN, hx3, t, htT, hxt⟩ := exists_normalizer_moves_slPi hK hq T' hT'e hT'9 hZT'
  obtain ⟨t₀, ht₀, rfl⟩ := htT
  refine ⟨e.symm x, ?_, ?_, t₀, ht₀, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    have h1 : x * e u * x⁻¹ ∈ T' := (Subgroup.mem_normalizer_iff.mp hxN _).mp ⟨u, hu, rfl⟩
    obtain ⟨v, hv, hve⟩ := h1
    have : e.symm x * u * (e.symm x)⁻¹ = v := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hve.symm
    rw [this]
    exact hv
  · have h := hx3.map e.symm.toMonoidHom
    rwa [MonoidHom.map_zpowers] at h
  · intro h
    apply hxt
    have := congrArg e h
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at this

end CFSG.RankThree.PartTwo.KFacts
