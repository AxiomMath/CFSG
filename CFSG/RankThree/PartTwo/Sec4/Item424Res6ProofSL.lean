module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofFrame
import CFSG.RankThree.PartTwo.Sec4.Item417Res2ProofEven
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec15.KSL3Two
open Matrix Res417Frame

namespace Res424Six

variable {H : Type} [Group H] [Finite H] {L : Subgroup H} [L.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool}

theorem finRotate_three_facts :
    finRotate 3 ^ 3 = 1 ∧ (finRotate 3)⁻¹ (2 : Fin 3) = 1 := by
  decide

theorem exists_not_normalizes_of_slPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup H} {c : H}
    (hA : Maximal (fun B : Subgroup H => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hc3 : orderOf c = 3) (hAc : A ⊓ Subgroup.centralizer (L : Set H) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) {b : H} (hbA : b ∈ A) (hbL : b ∈ L)
    (hbc : b ∉ Subgroup.zpowers c) :
    ∃ n ∈ L, n ∈ Subgroup.normalizer (A : Set H) ∧ n * b * n⁻¹ ∉ Subgroup.zpowers b := by
  classical
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨-, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  set eb : GL (Fin 3) K := (e ⟨b, hbL⟩ : GL (Fin 3) K) with heb
  have hebZ : eb ∉ zPi π 3 (p ^ f) K := by
    intro hz
    apply hbc
    rw [← hLC]
    exact ⟨hbL, mem_centralizer_of_scalar hbL (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz)⟩
  have hb3 : b ^ 3 = 1 := hA.1.2 b hbA
  have hb1 : b ≠ 1 := fun h1 => hbc (h1 ▸ Subgroup.one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have heb3 : orderOf eb = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : eb ^ 3 = 1 := by
      rw [heb, ← Subgroup.coe_pow, ← map_pow]
      have : (⟨b, hbL⟩ : L) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hb3]; rfl)
      rw [this, map_one, Subgroup.coe_one]
    refine orderOf_eq_prime h3 fun h1 => hebZ ?_
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨g, hgH, hgD⟩ := rank3II_4_10_three hK hq hτ hτ1 (e ⟨b, hbL⟩).2 hebZ heb3
  set d : Fin 3 → K := ![τ, τ ^ 2, 1] with hddef
  have hd : Function.Injective d := Res417Two.injective_diagTau_entries hτ hτ1
  have hψb : ((g⁻¹ * eb * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [hgD, coe_diagTau_eq_diagonal]
  have hψmul : ∀ X Y : GL (Fin 3) K, g⁻¹ * (X * Y) * g = (g⁻¹ * X * g) * (g⁻¹ * Y * g) :=
    fun X Y => by group
  have hψinj : ∀ X Y : GL (Fin 3) K, g⁻¹ * X * g = g⁻¹ * Y * g → X = Y := fun X Y h => by
    have := congrArg (fun Z => g * Z * g⁻¹) h
    simpa [mul_assoc] using this
  have hdiag : ∀ a ∈ A, ∀ y, IsPGLAt e a y →
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro a ha y hy
    apply isDiag_of_commute_diagonal hd
    have hc := isPGLAt_commute_of_mem hbL (hAcomm a ha b hbA) hy
    rw [← hψb, ← Units.val_mul, ← Units.val_mul, ← hψmul, ← hψmul, hc]
  have hcube : ∀ a ∈ A, ∀ y, IsPGLAt e a y → ∀ i j,
      ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ^ 3 =
        ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j ^ 3 := by
    intro a ha y hy i j
    obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1
      (pow_three_mem_zPi hK hq (hA.1.2 a ha) hy)
    have h3 : ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 =
        (ℓ : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      have e1 : (g⁻¹ * y * g) ^ 3 = g⁻¹ * y ^ 3 * g := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      rw [← Units.val_pow_eq_pow_val, e1, ← hℓ,
        (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ℓ g⁻¹).eq, inv_mul_cancel_right,
        coe_scalar_eq_smul]
    have hD := hdiag a ha y hy
    have hk : ∀ k, ((g⁻¹ * y * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) k k ^ 3 = ℓ := by
      intro k
      have := congrFun (congrFun h3 k) k
      rw [← hD.diagonal_diag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq] at this
      simpa using this
    rw [hk i, hk j]
  have hcent : ∀ m (hm : m ∈ L),
      ((g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag → ∀ a ∈ A, a * m = m * a := by
    intro m hm hmD a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have hmL : a * m * a⁻¹ ∈ L := ‹L.Normal›.conj_mem m hm a
    have h1 := coe_e_conj_of_isPGLAt hy hm hmL
    have h2 : y * (e ⟨m, hm⟩ : GL (Fin 3) K) * y⁻¹ = (e ⟨m, hm⟩ : GL (Fin 3) K) := by
      apply hψinj
      have hc := commute_of_isDiag (hdiag a ha y hy) hmD
      have hc' : (g⁻¹ * y * g) * (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) =
          (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) * (g⁻¹ * y * g) := Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact hc)
      calc g⁻¹ * (y * (e ⟨m, hm⟩ : GL (Fin 3) K) * y⁻¹) * g =
            (g⁻¹ * y * g) * (g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g) * (g⁻¹ * y * g)⁻¹ := by
              group
        _ = g⁻¹ * (e ⟨m, hm⟩ : GL (Fin 3) K) * g := by rw [hc']; group
    rw [h2] at h1
    have h3 : (⟨a * m * a⁻¹, hmL⟩ : L) = ⟨m, hm⟩ :=
      e.injective (Subtype.ext h1)
    have h4 : a * m * a⁻¹ = m := congrArg Subtype.val h3
    calc a * m = a * m * a⁻¹ * a := by group
      _ = m * a := by rw [h4]
  obtain ⟨hσ3, hσ2⟩ := finRotate_three_facts
  set σ : Equiv.Perm (Fin 3) := finRotate 3 with hσdef
  have hP := permGL_mem_glPi (p := p) (f := f) hK σ
  have hsign := sign_eq_one_of_pow_three σ hσ3
  have hsl : g * permGL σ * g⁻¹ ∈ slPi π 3 (p ^ f) K := by
    refine (mem_slPi_iff hπ).mpr ⟨mul_mem (mul_mem hgH hP) (inv_mem hgH), ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, det_permGL_eq_sign, hsign,
      mul_comm, ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one]
    simp
  set n : H := (e.symm ⟨g * permGL σ * g⁻¹, hsl⟩ : H) with hndef
  have hnL : n ∈ L := (e.symm _).2
  have hen : ((e ⟨n, hnL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = g * permGL σ * g⁻¹ := by
    have : (⟨n, hnL⟩ : L) = e.symm ⟨g * permGL σ * g⁻¹, hsl⟩ := rfl
    rw [this, MulEquiv.apply_symm_apply]
  have hψn : g⁻¹ * ((e ⟨n, hnL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) * g = permGL σ := by
    rw [hen]
    group
  have hnA : ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
    intro a ha
    obtain ⟨y, hy⟩ := hpgl a ha
    have ht'L : a * n⁻¹ * a⁻¹ ∈ L := ‹L.Normal›.conj_mem _ (L.inv_mem hnL) a
    have hmL : n * (a * n⁻¹ * a⁻¹) ∈ L := L.mul_mem hnL ht'L
    have hem : ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        (e ⟨n, hnL⟩ : GL (Fin 3) K) * y * (e ⟨n, hnL⟩ : GL (Fin 3) K)⁻¹ * y⁻¹ := by
      have e1 : (⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : L) =
          ⟨n, hnL⟩ * ⟨a * n⁻¹ * a⁻¹, ht'L⟩ := rfl
      rw [e1, map_mul, Subgroup.coe_mul, coe_e_conj_of_isPGLAt hy (L.inv_mem hnL) ht'L]
      have e2 : (⟨n⁻¹, L.inv_mem hnL⟩ : L) = (⟨n, hnL⟩ : L)⁻¹ := rfl
      rw [e2, map_inv, Subgroup.coe_inv]
      group
    have hψm : g⁻¹ * ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) :
        GL (Fin 3) K) * g =
        permGL σ * (g⁻¹ * y * g) * (permGL σ)⁻¹ * (g⁻¹ * y * g)⁻¹ := by
      rw [hem, ← hψn]
      group
    obtain ⟨hmD, hm3⟩ := commutator_permGL σ (hdiag a ha y hy) (hcube a ha y hy)
    rw [← hψm] at hmD hm3
    have hmA : n * (a * n⁻¹ * a⁻¹) ∈ A := by
      refine mem_of_maximal_of_commute hA ?_ fun a' ha' => hcent _ hmL hmD a' ha'
      have h1 : ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) :
          GL (Fin 3) K) ^ 3 = 1 := by
        have e1 : (g⁻¹ * ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) :
            GL (Fin 3) K) * g) ^ 3 = g⁻¹ * ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ :
              slPi π 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 * g := by
          simp only [pow_succ, pow_zero, one_mul]
          group
        rw [e1] at hm3
        calc ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 =
            g * (g⁻¹ * ((e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩ : slPi π 3 (p ^ f) K) :
              GL (Fin 3) K) ^ 3 * g) * g⁻¹ := by group
          _ = 1 := by rw [hm3]; group
      have h2' : (e ⟨n * (a * n⁻¹ * a⁻¹), hmL⟩) ^ 3 = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, h1]; rfl)
      rw [← map_pow, map_eq_one_iff _ e.injective] at h2'
      exact congrArg Subtype.val h2'
    have : n * a * n⁻¹ = (n * (a * n⁻¹ * a⁻¹)) * a := by group
    rw [this]
    exact A.mul_mem hmA ha
  refine ⟨n, hnL, mem_normalizer_of_conj_mem hnA, fun hmem => ?_⟩
  rw [mem_zpowers_iff_mem_range_orderOf, hbo] at hmem
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
  have hnbL : n * b * n⁻¹ ∈ L := ‹L.Normal›.conj_mem b hbL n
  have hej : ((e ⟨n * b * n⁻¹, hnbL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = eb ^ j := by
    have e1 : (⟨n * b * n⁻¹, hnbL⟩ : L) = ⟨b, hbL⟩ ^ j := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hj.symm)
    rw [e1, map_pow, Subgroup.coe_pow]
  have hen' : ((e ⟨n * b * n⁻¹, hnbL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
      (e ⟨n, hnL⟩ : GL (Fin 3) K) * eb * (e ⟨n, hnL⟩ : GL (Fin 3) K)⁻¹ := by
    have e1 : (⟨n * b * n⁻¹, hnbL⟩ : L) = ⟨n, hnL⟩ * ⟨b, hbL⟩ * (⟨n, hnL⟩ : L)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hL1 : g⁻¹ * ((e ⟨n * b * n⁻¹, hnbL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) * g =
      permGL σ * (g⁻¹ * eb * g) * (permGL σ)⁻¹ := by
    rw [hen', ← hψn]
    group
  have hpowconj : ∀ k : ℕ, g⁻¹ * eb ^ k * g = (g⁻¹ * eb * g) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, ← ih]
      group
  have hR1 : g⁻¹ * ((e ⟨n * b * n⁻¹, hnbL⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) * g =
      (g⁻¹ * eb * g) ^ j := by
    rw [hej, hpowconj]
  have hconj : ((permGL σ * (g⁻¹ * eb * g) * (permGL σ)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (fun i => d (σ⁻¹ i)) := by
    rw [Units.val_mul, Units.val_mul, hψb, permGL_mul_diagonal, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hpowj : (((g⁻¹ * eb * g) ^ j : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal d ^ j := by
    rw [Units.val_pow_eq_pow_val, hψb]
  have h22 := congrFun (congrFun (show ((permGL σ * (g⁻¹ * eb * g) * (permGL σ)⁻¹ :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (((g⁻¹ * eb * g) ^ j : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) by rw [← hL1, hR1]) 2) 2
  rw [hconj, hpowj, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
    hσ2] at h22
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by
          have hτ0 : τ ≠ 0 := by
            rintro rfl
            simp at hτ
          field_simp
      _ = 1 := by rw [hτ, h, div_one]
  apply hτ2
  simpa [hddef] using h22

end Res424Six

end CFSG.RankThree.PartTwo.Sec4
