module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129G

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec12.KS128Move Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)

theorem exists_unit_orderOf_nine {K : Type} [Field K] [Finite K] (h9 : 9 ∣ Nat.card Kˣ) :
    ∃ μ : Kˣ, orderOf μ = 9 := by
  have := Fintype.ofFinite K
  classical
  have h9' : 9 ∣ Fintype.card Kˣ := by
    rw [← Nat.card_eq_fintype_card]; exact h9
  have hc := IsCyclic.card_orderOf_eq_totient h9'
  have hpos : 0 < (Finset.univ.filter fun a : Kˣ => orderOf a = 9).card := by
    rw [hc]
    exact Nat.totient_pos.mpr (by norm_num)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

section Involution

variable {K : Type} [Field K]

@[expose] def uMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, -1]

theorem uMat_mul_self : (uMat : Matrix (Fin 3) (Fin 3) K) * uMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def uGL : GL (Fin 3) K := ⟨uMat, uMat, uMat_mul_self, uMat_mul_self⟩

theorem coe_uGL : ((uGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = uMat := rfl

theorem uGL_mul_self : (uGL : GL (Fin 3) K) * uGL = 1 :=
  Units.ext (by rw [Units.val_mul, coe_uGL, uMat_mul_self]; rfl)

theorem uGL_ne_one : (uGL : GL (Fin 3) K) ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
  simp [coe_uGL, uMat] at this

theorem det_uMat : (uMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [uMat]

theorem uGL_mul_diagUnits (a c : Kˣ) :
    (uGL : GL (Fin 3) K) * diagUnits a a c = diagUnits a a c * uGL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_uGL, coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem uGL_mul_diagUnits_swap {a b : Kˣ} (h : (uGL : GL (Fin 3) K) * diagUnits a b 1 =
    diagUnits a b 1 * uGL) : a = b := by
  have h' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) h
  simp [coe_uGL, coe_diagUnits, uMat, Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.diagonal_apply] at h'
  exact (Units.ext h'.symm)

theorem uGL_mem_slPi {π : Bool} {p f : ℕ} (hK : PiField π p f K) :
    (uGL : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((uGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := det_uMat
  cases π
  · have h := hK.unitary
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    have hmap : ((uGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map h.bar = uMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [coe_uGL, uMat]
    have hT : (uMat : Matrix (Fin 3) (Fin 3) K)ᵀ = uMat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uMat]
    rw [hmap, hT, coe_uGL]
    exact uMat_mul_self
  · rw [mem_slPi_true]
    exact hdet

end Involution

section Data

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem exists_data_slPi (hK : PiField π p f K) (h9 : 9 ∣ qSubPi π (p ^ f)) :
    ∃ δ σ u z : slPi π 3 (p ^ f) K, z ∈ Subgroup.center (slPi π 3 (p ^ f) K) ∧ z ≠ 1 ∧
      z ^ 3 = 1 ∧ δ ^ 3 = z ∧ σ ^ 3 = 1 ∧ σ ∉ Subgroup.center (slPi π 3 (p ^ f) K) ∧
      (∀ k : ℤ, σ ≠ δ ^ k) ∧ σ * δ = δ * σ ∧ u ^ 2 = 1 ∧ u ≠ 1 ∧ u * δ = δ * u := by
  have hfin := hK.finite
  have h9K : 9 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK.card]
    cases π
    · change 9 ∣ p ^ f + 1 at h9
      simp only [piCard, Bool.cond_false]
      have : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
        have : 1 ≤ p ^ f := Nat.one_le_pow _ _ hK.prime.pos
        zify [this, Nat.one_le_pow _ _ hK.prime.pos, show 1 ≤ (p ^ f) ^ 2 from
          Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hK.prime.pos)]
        ring
      rw [this]
      exact Dvd.dvd.mul_right h9 _
    · exact h9
  obtain ⟨μ, hμ⟩ := exists_unit_orderOf_nine h9K
  have hμ9 : μ ^ 9 = 1 := by rw [← hμ]; exact pow_orderOf_eq_one μ
  have hμN : μ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    rw [mem_rootsOfUnity]
    obtain ⟨k, hk⟩ := h9
    rw [hk, pow_mul, hμ9, one_pow]
  set ω : Kˣ := μ ^ 3 with hω
  have hω3 : ω ^ 3 = 1 := by rw [hω, ← pow_mul]; exact hμ9
  have hω1 : ω ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hμ] at this
    omega
  have hωN : ω ∈ rootsOfUnity (qSubPi π (p ^ f)) K := pow_mem hμN 3
  have hωiN : ω⁻¹ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := inv_mem hωN
  have hωωω : ω * ω * ω = 1 := by
    rw [mul_assoc, ← pow_three]
    exact hω3
  have hinv : (ω * ω)⁻¹ = ω := inv_eq_of_mul_eq_one_right hωωω
  have hz : (torusHom (ω, ω) : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) ω := by
    change diagUnits ω ω (ω * ω)⁻¹ = _
    rw [hinv, scalar_eq_diagUnits]
  have hσ : (torusHom (ω, ω⁻¹) : GL (Fin 3) K) = diagUnits ω ω⁻¹ 1 := by
    change diagUnits ω ω⁻¹ (ω * ω⁻¹)⁻¹ = _
    rw [mul_inv_cancel, inv_one]
  have hδ : (torusHom (μ, μ) : GL (Fin 3) K) = diagUnits μ μ (μ * μ)⁻¹ := rfl
  refine ⟨⟨torusHom (μ, μ), torusHom_mem_slPi hK hμN hμN⟩,
    ⟨torusHom (ω, ω⁻¹), torusHom_mem_slPi hK hωN hωiN⟩,
    ⟨uGL, uGL_mem_slPi hK⟩, ⟨torusHom (ω, ω), torusHom_mem_slPi hK hωN hωN⟩, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    change (g : GL (Fin 3) K) * torusHom (ω, ω) = torusHom (ω, ω) * (g : GL (Fin 3) K)
    exact commute_of_mem_statedScalars (⟨ω, hz.symm⟩ : (torusHom (ω, ω) : GL (Fin 3) K) ∈
      StatedScalars (Fin 3) K) g
  ·
    intro h
    have h1 : (torusHom (ω, ω) : GL (Fin 3) K) = 1 := congrArg Subtype.val h
    have h2 : torusHom (ω, ω) = torusHom ((1 : Kˣ), (1 : Kˣ)) := by rw [h1]; exact (map_one _).symm
    exact hω1 (congrArg Prod.fst (torusHom_injective h2))
  ·
    apply Subtype.ext
    change (torusHom (ω, ω) : GL (Fin 3) K) ^ 3 = 1
    rw [← map_pow]
    have : ((ω, ω) : Kˣ × Kˣ) ^ 3 = 1 := Prod.ext (by simpa using hω3) (by simpa using hω3)
    rw [this, map_one]
  ·
    apply Subtype.ext
    change (torusHom (μ, μ) : GL (Fin 3) K) ^ 3 = torusHom (ω, ω)
    rw [← map_pow]
    congr 1
  ·
    apply Subtype.ext
    change (torusHom (ω, ω⁻¹) : GL (Fin 3) K) ^ 3 = 1
    rw [← map_pow]
    have : ((ω, ω⁻¹) : Kˣ × Kˣ) ^ 3 = 1 :=
      Prod.ext (by simpa using hω3) (by simp [inv_pow, hω3])
    rw [this, map_one]
  ·
    intro hc
    have h1 := (Subgroup.mem_center_iff.mp hc) ⟨uGL, uGL_mem_slPi hK⟩
    have h2 : (uGL : GL (Fin 3) K) * torusHom (ω, ω⁻¹) = torusHom (ω, ω⁻¹) * uGL :=
      congrArg Subtype.val h1
    rw [hσ] at h2
    have h3 := uGL_mul_diagUnits_swap h2
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by
        rw [hω3, one_mul, inv_eq_one, pow_two]
        calc ω * ω = ω * ω⁻¹ := by rw [← h3]
          _ = 1 := mul_inv_cancel ω
  ·
    intro k hk
    have h1 : (torusHom (ω, ω⁻¹) : GL (Fin 3) K) = torusHom (μ ^ k, μ ^ k) := by
      have := congrArg Subtype.val hk
      change (torusHom (ω, ω⁻¹) : GL (Fin 3) K) = (torusHom (μ, μ) : GL (Fin 3) K) ^ k at this
      rw [this, ← map_zpow]
      rfl
    have h2 := torusHom_injective h1
    have h3 : ω = ω⁻¹ := (congrArg Prod.fst h2).trans (congrArg Prod.snd h2).symm
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by
        rw [hω3, one_mul, inv_eq_one, pow_two]
        calc ω * ω = ω * ω⁻¹ := by rw [← h3]
          _ = 1 := mul_inv_cancel ω
  ·
    apply Subtype.ext
    change (torusHom (ω, ω⁻¹) : GL (Fin 3) K) * torusHom (μ, μ) =
      torusHom (μ, μ) * torusHom (ω, ω⁻¹)
    rw [← map_mul, ← map_mul, mul_comm]
  ·
    apply Subtype.ext
    change (uGL : GL (Fin 3) K) ^ 2 = 1
    rw [pow_two]
    exact uGL_mul_self
  ·
    intro h
    exact uGL_ne_one (congrArg Subtype.val h)
  ·
    apply Subtype.ext
    change (uGL : GL (Fin 3) K) * torusHom (μ, μ) = torusHom (μ, μ) * uGL
    rw [hδ]
    exact uGL_mul_diagUnits μ _

end Data

end CFSG.RankThree.PartTwo.Sec12.Hering129G
