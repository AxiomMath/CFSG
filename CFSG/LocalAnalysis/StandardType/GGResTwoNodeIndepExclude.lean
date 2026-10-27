module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
public import CFSG.LocalAnalysis.StandardType.GGRCPermMonomial
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l6aE_tri (m : ℕ) (hm : 2 ≤ m) :
    m * (m - 1) / 2 = (m - 1) * (m - 2) / 2 + (m - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  rw [e1, e2]
  have h : (k + 2) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
  rw [h]
  exact Nat.add_mul_div_left _ _ (by norm_num)

private lemma l6aE_lin {p : ℕ} (hp : 5 ≤ p) (m : ℕ) (hm : 4 ≤ m) : m + 1 ≤ p ^ (m - 2) := by
  have h1 : 2 * (m - 2) < 2 ^ (2 * (m - 2)) := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * (m - 2)) = 4 ^ (m - 2) := by rw [pow_mul]; norm_num
  have h3 : 4 ^ (m - 2) ≤ p ^ (m - 2) := Nat.pow_le_pow_left (by omega) _
  omega

theorem ggIndep_order_ineq {p N : ℕ} (hp : 5 ≤ p) (hN : 10 ≤ N) :
    8 * (p ^ (N - 1) * (6 * (p - 1) * Nat.factorial N)) < p ^ ((N - 1) * (N - 2) / 2) := by
  have hp0 : 0 < p := by omega
  refine Nat.le_induction (m := 10)
    (P := fun n _ => 8 * (p ^ (n - 1) * (6 * (p - 1) * Nat.factorial n)) <
      p ^ ((n - 1) * (n - 2) / 2)) ?base ?step N hN
  · have hExp : (10 - 1) * (10 - 2) / 2 = 36 := by norm_num
    rw [hExp]
    have hf10 : Nat.factorial 10 = 3628800 := by decide
    have hX : 8 * (6 * (p - 1) * Nat.factorial 10) < p ^ 27 := by
      have hf : 48 * Nat.factorial 10 < 5 ^ 26 := by rw [hf10]; norm_num
      have hp1 : p - 1 < p := by omega
      calc
        8 * (6 * (p - 1) * Nat.factorial 10) = 48 * (p - 1) * Nat.factorial 10 := by ring
        _ < 48 * p * Nat.factorial 10 := by
              apply Nat.mul_lt_mul_of_pos_right
              · exact Nat.mul_lt_mul_of_pos_left hp1 (by norm_num)
              · rw [hf10]; norm_num
        _ = (48 * Nat.factorial 10) * p := by ring
        _ < 5 ^ 26 * p := Nat.mul_lt_mul_of_pos_right hf hp0
        _ ≤ p ^ 26 * p := Nat.mul_le_mul_right p (Nat.pow_le_pow_left hp 26)
        _ = p ^ 27 := by rw [← pow_succ]
    calc
      8 * (p ^ (10 - 1) * (6 * (p - 1) * Nat.factorial 10))
          = p ^ 9 * (8 * (6 * (p - 1) * Nat.factorial 10)) := by
            norm_num
            ring
      _ < p ^ 9 * p ^ 27 := Nat.mul_lt_mul_of_pos_left hX (pow_pos hp0 9)
      _ = p ^ 36 := by rw [← pow_add]
  · intro m hm ih
    have e1 : m + 1 - 1 = m := by omega
    have e2 : m + 1 - 2 = m - 1 := by omega
    rw [e1, e2]
    have hexp : m * (m - 1) / 2 = (m - 1) * (m - 2) / 2 + (m - 1) := l6aE_tri m (by omega)
    have hbound : p * (m + 1) ≤ p ^ (m - 1) := by
      calc p * (m + 1) ≤ p * p ^ (m - 2) := Nat.mul_le_mul_left p (l6aE_lin hp m (by omega))
        _ = p ^ (m - 1) := by
              rw [← pow_succ']
              congr 1
              omega
    have hident : 8 * (p ^ m * (6 * (p - 1) * Nat.factorial (m + 1)))
        = (p * (m + 1)) * (8 * (p ^ (m - 1) * (6 * (p - 1) * Nat.factorial m))) := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ, Nat.factorial_succ (k + 1)]
      ring
    calc
      8 * (p ^ m * (6 * (p - 1) * Nat.factorial (m + 1)))
          = (p * (m + 1)) * (8 * (p ^ (m - 1) * (6 * (p - 1) * Nat.factorial m))) := hident
      _ < (p * (m + 1)) * p ^ ((m - 1) * (m - 2) / 2) :=
            Nat.mul_lt_mul_of_pos_left ih (Nat.mul_pos hp0 (by omega))
      _ ≤ p ^ (m - 1) * p ^ ((m - 1) * (m - 2) / 2) := Nat.mul_le_mul_right _ hbound
      _ = p ^ (m * (m - 1) / 2) := by rw [← pow_add, hexp, add_comm]

private lemma l6aE_lin3 {p : ℕ} (hp : 3 ≤ p) (m : ℕ) (hm : 5 ≤ m) : m + 1 ≤ p ^ (m - 2) := by
  have h2 : ∀ k : ℕ, 3 ≤ k → k + 3 ≤ 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  have h3 : 2 ^ (m - 2) ≤ p ^ (m - 2) := Nat.pow_le_pow_left (by omega) _
  have h4 := h2 (m - 2) (by omega)
  omega

theorem ggIndep_order_ineq_N {p N : ℕ} (hp : 3 ≤ p) (hN : 9 ≤ N) :
    8 * (p ^ N * (6 * (p - 1) * Nat.factorial N)) < p ^ (N * (N - 1) / 2) := by
  have hp0 : 0 < p := by omega
  refine Nat.le_induction (m := 9)
    (P := fun n _ => 8 * (p ^ n * (6 * (p - 1) * Nat.factorial n)) <
      p ^ (n * (n - 1) / 2)) ?base ?step N hN
  · have hExp : 9 * (9 - 1) / 2 = 36 := by norm_num
    rw [hExp]
    have hf9 : Nat.factorial 9 = 362880 := by decide
    have hX : 8 * (6 * (p - 1) * Nat.factorial 9) < p ^ 27 := by
      have hf : 48 * Nat.factorial 9 < 3 ^ 26 := by rw [hf9]; norm_num
      have hp1 : p - 1 < p := by omega
      calc
        8 * (6 * (p - 1) * Nat.factorial 9) = 48 * (p - 1) * Nat.factorial 9 := by ring
        _ < 48 * p * Nat.factorial 9 := by
              apply Nat.mul_lt_mul_of_pos_right
              · exact Nat.mul_lt_mul_of_pos_left hp1 (by norm_num)
              · rw [hf9]; norm_num
        _ = (48 * Nat.factorial 9) * p := by ring
        _ < 3 ^ 26 * p := Nat.mul_lt_mul_of_pos_right hf hp0
        _ ≤ p ^ 26 * p := Nat.mul_le_mul_right p (Nat.pow_le_pow_left hp 26)
        _ = p ^ 27 := by rw [← pow_succ]
    calc
      8 * (p ^ 9 * (6 * (p - 1) * Nat.factorial 9))
          = p ^ 9 * (8 * (6 * (p - 1) * Nat.factorial 9)) := by ring
      _ < p ^ 9 * p ^ 27 := Nat.mul_lt_mul_of_pos_left hX (pow_pos hp0 9)
      _ = p ^ 36 := by rw [← pow_add]
  · intro m hm ih
    have e1 : m + 1 - 1 = m := by omega
    rw [e1]
    have hexp : (m + 1) * m / 2 = m * (m - 1) / 2 + m := by
      have h := l6aE_tri (m + 1) (by omega)
      rw [e1] at h
      have e2 : m + 1 - 2 = m - 1 := by omega
      rw [e2] at h
      exact h
    have hbound : p * (m + 1) ≤ p ^ m := by
      calc p * (m + 1) ≤ p * p ^ (m - 2) := Nat.mul_le_mul_left p (l6aE_lin3 hp m (by omega))
        _ = p ^ (m - 1) := by
              rw [← pow_succ']
              congr 1
              omega
        _ ≤ p ^ m := Nat.pow_le_pow_right hp0 (by omega)
    have hident : 8 * (p ^ (m + 1) * (6 * (p - 1) * Nat.factorial (m + 1)))
        = (p * (m + 1)) * (8 * (p ^ m * (6 * (p - 1) * Nat.factorial m))) := by
      rw [pow_succ, Nat.factorial_succ m]
      ring
    calc
      8 * (p ^ (m + 1) * (6 * (p - 1) * Nat.factorial (m + 1)))
          = (p * (m + 1)) * (8 * (p ^ m * (6 * (p - 1) * Nat.factorial m))) := hident
      _ < (p * (m + 1)) * p ^ (m * (m - 1) / 2) :=
            Nat.mul_lt_mul_of_pos_left ih (Nat.mul_pos hp0 (by omega))
      _ ≤ p ^ m * p ^ (m * (m - 1) / 2) := Nat.mul_le_mul_right _ hbound
      _ = p ^ ((m + 1) * m / 2) := by rw [← pow_add, hexp, add_comm]

theorem ggIndep_exclude (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime]
    (hp : 5 ≤ p) (hN : 10 ≤ N) (hpN : p ∣ N) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (hdim : Module.finrank (ZMod p) U = N - 1)
    (AU : Subgroup (U ≃ₗ[ZMod p] U)) (hirr : ZS.AbsIrred p AU)
    (hgen : AU = Subgroup.closure {t | t ∈ AU ∧ GGLinRefl t})
    (hcard : Nat.card ↥AU ≤ p ^ (N - 1) * (6 * (p - 1) * Nat.factorial N))
    (ψ : Equiv.Perm (Fin N) →* ↥AU) (hψ : Function.Injective ψ) : False := by
  have hp2 : p ≠ 2 := by omega
  obtain himp | hclass | ⟨hndvd, _e1, _he1⟩ | ⟨hdvd, _e2, _he2⟩ :=
    hKG p hp2 U (N - 1) hdim (by omega) AU hirr hgen
  ·
    obtain ⟨b, hmon⟩ :=
      ggRC_monomial_of_imprimitive (p := p) (n := N - 1) hdim AU hirr hgen himp
    obtain ⟨π, _hπ, _hπker, hπcomm, _hπp⟩ := ggRC_monomial_hom b AU hmon
    let π' : Equiv.Perm (Fin N) →* Equiv.Perm (Fin (N - 1)) := π.comp ψ
    have hπ'comm : IsMulCommutative π'.ker := by
      rw [isMulCommutative_iff]
      intro a b
      apply Subtype.ext
      apply hψ
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (isMulCommutative_iff.mp hπcomm
        ⟨ψ (a : Equiv.Perm (Fin N)), a.2⟩
        ⟨ψ (b : Equiv.Perm (Fin N)), b.2⟩)
    exact ggRC_perm_not_monomial (N := N) (m := N - 1) (by omega) (by omega) π' hπ'comm
  ·
    have h1 : N - 1 - 1 = N - 2 := by omega
    rw [h1] at hclass
    have hchain : p ^ ((N - 1) * (N - 2) / 2) ≤
        8 * (p ^ (N - 1) * (6 * (p - 1) * Nat.factorial N)) :=
      hclass.trans (Nat.mul_le_mul_left 8 hcard)
    exact absurd (lt_of_le_of_lt hchain (ggIndep_order_ineq hp hN)) (lt_irrefl _)
  ·
    have hN1 : N - 1 + 1 = N := by omega
    exact hndvd (hN1.symm ▸ hpN)
  ·
    have hN2 : N - 1 + 2 = N + 1 := by omega
    have hdvd' : p ∣ N + 1 := hN2 ▸ hdvd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hpN).mp hdvd'
    have hp1 : ¬ p ∣ 1 := by
      intro h
      have := Nat.le_of_dvd (by norm_num : 0 < 1) h
      omega
    exact hp1 h1

end CFSG.StandardType

end
