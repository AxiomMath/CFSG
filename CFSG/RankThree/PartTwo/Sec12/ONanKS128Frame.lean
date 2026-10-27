module

public import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128Move

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem diagUnits_mem_glPi_iff (hK : PiField π p f K) (a b c : Kˣ) :
    (diagUnits a b c : GL (Fin 3) K) ∈ glPi π 3 (p ^ f) K ↔
      a ∈ rootsOfUnity (qSubPi π (p ^ f)) K ∧ b ∈ rootsOfUnity (qSubPi π (p ^ f)) K ∧
        c ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
  have := hK.finite
  cases π
  · have h := hK.unitary
    have hnorm : ∀ u : Kˣ, h.bar (u : K) * u = 1 ↔ u ∈ rootsOfUnity (p ^ f + 1) K := by
      intro u
      rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, h.bar_apply,
        ← pow_succ]
    rw [mem_glPi_false h, coe_diagUnits, diagonal_map (map_zero _), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    change _ ↔ a ∈ rootsOfUnity (p ^ f + 1) K ∧ b ∈ rootsOfUnity (p ^ f + 1) K ∧
      c ∈ rootsOfUnity (p ^ f + 1) K
    rw [← hnorm, ← hnorm, ← hnorm]
    constructor
    · intro hd
      have e0 := congrFun (congrFun hd 0) 0
      have e1 := congrFun (congrFun hd 1) 1
      have e2 := congrFun (congrFun hd 2) 2
      simp at e0 e1 e2
      exact ⟨e0, e1, e2⟩
    · rintro ⟨e0, e1, e2⟩
      congr 1
      funext i
      fin_cases i
      · exact e0
      · exact e1
      · exact e2
  · have hc : Nat.card K = p ^ f := by simpa [piCard] using hK.card
    exact iff_of_true (mem_glPi_true _ _)
      ⟨mem_rootsOfUnity_of_card hc a, mem_rootsOfUnity_of_card hc b,
        mem_rootsOfUnity_of_card hc c⟩

theorem exists_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {x : GL (Fin 3) K}
    (hx : x ∈ slPi π 3 (p ^ f) K) (hx3 : x ^ 3 = 1) (hxs : x ∉ StatedScalars (Fin 3) K) :
    ∃ g ∈ glPi π 3 (p ^ f) K, ∃ a ω : Kˣ, ω ≠ 1 ∧ ω ^ 3 = 1 ∧ a ^ 3 = 1 ∧
      g⁻¹ * x * g = diagUnits a (a * ω) (a * ω ^ 2) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hτ0 : τ ≠ 0 := fun h0 => by rw [h0] at hτ; norm_num at hτ
  have hxH : x ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hx
  have hμ : x ^ 3 = GeneralLinearGroup.scalar (Fin 3) ((1 : Kˣ) ^ 3) := by
    rw [one_pow, map_one, hx3]
  obtain ⟨y, ⟨z, hzZ, rfl⟩, g, hg, hcase⟩ := exists_diag_normal_form hK hq hτ hτ1 hxH hxs hμ
  have hzZ' := (zPi_eq hπ hq' hτ hτ1) ▸ hzZ
  have hzS : z ∈ StatedScalars (Fin 3) K := (Subgroup.mem_inf.mp hzZ').2
  have hzc : ∀ h : GL (Fin 3) K, h * z = z * h := fun h => commute_of_mem_statedScalars hzS h
  have hxz3 : (x * z) ^ 3 = z ^ 3 := by
    rw [(Commute.mul_pow (hzc x) 3), hx3, one_mul]
  obtain ⟨ζ, rfl⟩ := hzS
  rcases hcase with hD | ⟨e, he, hD⟩
  ·
    have hω3 : (Units.mk0 τ hτ0) ^ 3 = 1 := Units.ext (by simpa using hτ)
    have hω1 : Units.mk0 τ hτ0 ≠ 1 := fun h => hτ1 (by simpa using congrArg Units.val h)
    have hconj : g⁻¹ * x * g = diagTau hτ * (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by
      rw [← hD]
      have hzi : GeneralLinearGroup.scalar (Fin 3) ζ * g =
          g * GeneralLinearGroup.scalar (Fin 3) ζ := (hzc g).symm
      calc g⁻¹ * x * g = g⁻¹ * x * (g * GeneralLinearGroup.scalar (Fin 3) ζ) *
            (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by group
        _ = g⁻¹ * x * (GeneralLinearGroup.scalar (Fin 3) ζ * g) *
            (GeneralLinearGroup.scalar (Fin 3) ζ)⁻¹ := by rw [hzi]
        _ = _ := by group
    have hframe : g⁻¹ * x * g = diagUnits (Units.mk0 τ hτ0 * ζ⁻¹) (Units.mk0 τ hτ0 * ζ⁻¹ *
        Units.mk0 τ hτ0) (Units.mk0 τ hτ0 * ζ⁻¹ * Units.mk0 τ hτ0 ^ 2) := by
      rw [hconj, diagTau_eq_diagUnits hτ hτ0, scalar_eq_diagUnits, diagUnits_inv,
        diagUnits_mul, diagUnits_eq_iff]
      have hτ' : τ ^ 3 = 1 := hτ
      refine ⟨rfl, ?_, ?_⟩ <;>
      · apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
          Units.val_mk0, Units.val_one]
        have hζ0 := ζ.ne_zero
        field_simp
        try linear_combination -hτ'
    have hcube : (g⁻¹ * x * g) ^ 3 = 1 := by
      have := conj_pow (a := g⁻¹) (b := x) (i := 3)
      rw [inv_inv] at this
      rw [this, hx3]
      group
    refine ⟨g, hg, Units.mk0 τ hτ0 * ζ⁻¹, Units.mk0 τ hτ0, hω1, hω3, ?_, hframe⟩
    rw [hframe, diagUnits_pow, ← diagUnits_one, diagUnits_eq_iff] at hcube
    exact hcube.1
  ·
    exfalso
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

theorem action_in_frame {ζ : MulAut (slPi π 3 (p ^ f) K)} {τ : K ≃+* K} {g₁ : GL (Fin 3) K}
    (h : SemiAct ζ τ g₁) (g : GL (Fin 3) K) (s : slPi π 3 (p ^ f) K) :
    ((ζ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      g * ((g⁻¹ * g₁ * frobGL τ g) * frobGL τ (g⁻¹ * (s : GL (Fin 3) K) * g) *
        (g⁻¹ * g₁ * frobGL τ g)⁻¹) * g⁻¹ := by
  rw [h s, map_mul, map_mul, map_inv]
  group

theorem commute_of_fixed {ζ : MulAut (slPi π 3 (p ^ f) K)} {τ : K ≃+* K}
    {g₁ g D : GL (Fin 3) K} (h : SemiAct ζ τ g₁) {x : slPi π 3 (p ^ f) K} (hζx : ζ x = x)
    (hD : g⁻¹ * (x : GL (Fin 3) K) * g = D) (hfD : frobGL τ D = D) :
    (g⁻¹ * g₁ * frobGL τ g) * D = D * (g⁻¹ * g₁ * frobGL τ g) := by
  have h1 := action_in_frame h g x
  rw [hζx, hD, hfD] at h1
  have h2 : (x : GL (Fin 3) K) = g * D * g⁻¹ := by rw [← hD]; group
  set c := g⁻¹ * g₁ * frobGL τ g with hc
  have h3 : c * D * c⁻¹ = D := by
    have h4 : g * (c * D * c⁻¹) * g⁻¹ = g * D * g⁻¹ := h1.symm.trans h2
    exact mul_left_cancel (mul_right_cancel h4)
  calc c * D = c * D * c⁻¹ * c := by group
    _ = D * c := by rw [h3]

theorem cocycle_in_frame {ζ : MulAut (slPi π 3 (p ^ f) K)} {τ : K ≃+* K} {g₁ g : GL (Fin 3) K}
    (h : SemiAct ζ τ g₁) {u : slPi π 3 (p ^ f) K} {α₀ α₁ α₂ c₀ c₁ c₂ : Kˣ}
    (hu : (u : GL (Fin 3) K) = g * (diagUnits α₀ α₁ α₂ * cycThree) * g⁻¹)
    (hc : g⁻¹ * g₁ * frobGL τ g = diagUnits c₀ c₁ c₂) :
    ((ζ u * u⁻¹ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      g * diagUnits (c₀ * unitMap τ α₀ * c₂⁻¹ * α₀⁻¹) (c₁ * unitMap τ α₁ * c₀⁻¹ * α₁⁻¹)
        (c₂ * unitMap τ α₂ * c₁⁻¹ * α₂⁻¹) * g⁻¹ := by
  have h1 := action_in_frame h g u
  have h2 : g⁻¹ * (u : GL (Fin 3) K) * g = diagUnits α₀ α₁ α₂ * cycThree := by
    rw [hu]
    group
  rw [hc, h2] at h1
  rw [Subgroup.coe_mul, h1, Subgroup.coe_inv, hu, ← cocycle_value]
  group

theorem exists_u_of_frame (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : slPi π 3 (p ^ f) K} {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) {a ω : Kˣ}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hx : (x : GL (Fin 3) K) = g * diagUnits a (a * ω) (a * ω ^ 2) * g⁻¹)
    {α₀ α₁ α₂ : Kˣ} (hα₀ : α₀ ∈ rootsOfUnity (qSubPi π (p ^ f)) K)
    (hα₁ : α₁ ∈ rootsOfUnity (qSubPi π (p ^ f)) K) (hα : α₀ * α₁ * α₂ = 1) :
    ∃ u : slPi π 3 (p ^ f) K,
      (u : GL (Fin 3) K) = g * (diagUnits α₀ α₁ α₂ * cycThree) * g⁻¹ ∧
      u * x * u⁻¹ * x⁻¹ ∈ Subgroup.center (slPi π 3 (p ^ f) K) ∧ u * x * u⁻¹ ≠ x := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hα2 : α₂ = (α₀ * α₁)⁻¹ := eq_inv_of_mul_eq_one_right hα
  have hΔ : (diagUnits α₀ α₁ α₂ : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := by
    rw [hα2]
    exact torusHom_mem_slPi hK hα₀ hα₁
  have hũ : (diagUnits α₀ α₁ α₂ * cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K :=
    mul_mem hΔ (cycThree_mem_slPi hπ)
  have hu : g * (diagUnits α₀ α₁ α₂ * cycThree) * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    conj_mem_slPi hπ hg hũ
  have hω23 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  set Sω : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) with hSω
  set D : GL (Fin 3) K := diagUnits a (a * ω) (a * ω ^ 2) with hD
  set Δ : GL (Fin 3) K := diagUnits α₀ α₁ α₂ with hΔdef
  have hΔS : Δ * Sω = Sω * Δ := by
    rw [hSω, scalar_eq_diagUnits, hΔdef, diagUnits_comm]
  have hΔD : Δ * D = D * Δ := diagUnits_comm _ _ _ _ _ _
  have hPD : (cycThree : GL (Fin 3) K) * D * cycThree⁻¹ = Sω * D := cycThree_conj_frame hω3
  have hũD : Δ * cycThree * D * (Δ * cycThree)⁻¹ = Sω * D := by
    have h1 : Δ * (Sω * D) = (Sω * D) * Δ := by
      calc Δ * (Sω * D) = (Δ * Sω) * D := by group
        _ = (Sω * Δ) * D := by rw [hΔS]
        _ = Sω * (Δ * D) := by group
        _ = Sω * (D * Δ) := by rw [hΔD]
        _ = (Sω * D) * Δ := by group
    calc Δ * cycThree * D * (Δ * cycThree)⁻¹ = Δ * (cycThree * D * cycThree⁻¹) * Δ⁻¹ := by group
      _ = Δ * (Sω * D) * Δ⁻¹ := by rw [hPD]
      _ = Sω * D := by rw [h1]; group
  have hSωS : Sω ∈ slPi π 3 (p ^ f) K := scalar_mem_slPi_of_pow_three hK hq hω23
  have hSωc : ∀ h : GL (Fin 3) K, h * Sω = Sω * h :=
    fun h => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (ω ^ 2) h).eq
  have hcomm : (g * (Δ * cycThree) * g⁻¹) * (x : GL (Fin 3) K) * (g * (Δ * cycThree) * g⁻¹)⁻¹ *
      (x : GL (Fin 3) K)⁻¹ = Sω := by
    rw [hx]
    calc _ = g * (Δ * cycThree * D * (Δ * cycThree)⁻¹ * D⁻¹) * g⁻¹ := by group
      _ = g * Sω * g⁻¹ := by rw [hũD]; group
      _ = Sω := by rw [hSωc g]; group
  refine ⟨⟨_, hu⟩, rfl, ?_, ?_⟩
  · have hz : (⟨Sω, hSωS⟩ : slPi π 3 (p ^ f) K) ∈ Subgroup.center (slPi π 3 (p ^ f) K) :=
      Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hSωc (s : GL (Fin 3) K))
    convert hz using 1
    apply Subtype.ext
    exact hcomm
  · intro hux
    have h1 : (⟨g * (Δ * cycThree) * g⁻¹, hu⟩ : slPi π 3 (p ^ f) K) * x *
        (⟨g * (Δ * cycThree) * g⁻¹, hu⟩ : slPi π 3 (p ^ f) K)⁻¹ * x⁻¹ = 1 := by
      rw [hux, mul_inv_cancel]
    have h2 := congrArg (fun y : slPi π 3 (p ^ f) K => (y : GL (Fin 3) K)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at h2
    rw [hcomm] at h2
    rw [hSω, scalar_eq_diagUnits, ← diagUnits_one, diagUnits_eq_iff] at h2
    apply hω1
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2.1, inv_one, mul_one]

end CFSG.RankThree.PartTwo.Sec12.KS128Move
