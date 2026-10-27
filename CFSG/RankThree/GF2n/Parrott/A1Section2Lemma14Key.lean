module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma14Pauli
public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma14U

public section

namespace CFSG.RankThree.GF2n.Parrott.A1Section2Local

open CFSG CFSG.Open QuotientV
open Subgroup (zpowers)
open scoped commutatorElement

section Algebra

variable {V : Type*} [Group V] [Finite V]

theorem exists_fix_of_sq (B : Subgroup V) (τ : MulAut V) (hτB : ∀ v, τ v ∈ B ↔ v ∈ B)
    (hτ2 : ∀ v ∈ B, (τ ^ 2) v = v) (hB : Even (Nat.card B)) :
    ∃ v ∈ B, v ≠ 1 ∧ τ v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype {v : V // v ∈ B ∧ v ≠ 1} := Fintype.ofFinite _
  let f := permNontrivial B τ hτB
  have hf2 : f ^ 2 ^ 1 = 1 := by
    ext s
    rw [pow_one, permNontrivial_pow_apply, hτ2 s.1 s.2.1]
    rfl
  have hmod := Equiv.Perm.card_compl_support_modEq hf2
  have hcard : Fintype.card {v : V // v ∈ B ∧ v ≠ 1} + 1 = Nat.card B := by
    rw [← Nat.card_eq_fintype_card, card_nontrivial]
    have : 0 < Nat.card B := Nat.card_pos
    omega
  have hne : f.supportᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.card_empty] at hmod
    obtain ⟨k, hk⟩ := hB
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨s, hs⟩ := hne
  simp only [Finset.mem_compl, Equiv.Perm.mem_support, ne_eq, not_not] at hs
  exact ⟨s.1, s.2.1, s.2.2, congrArg Subtype.val hs⟩

end Algebra

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Hyp

variable {s1 s2 : G} (hy : Hyp z s1 s2)
include hy

theorem inv_eq_self_of_mem_zpowers {d : G} (hd : d ∈ zpowers z) : d⁻¹ = d := by
  rcases hy.mem_zpowers_z_iff.mp hd with h | h
  · rw [h, inv_one]
  · rw [h]
    exact inv_eq_of_mul_eq_one_right hy.z_sq

theorem mul_self_eq_one_of_mem_zpowers {d : G} (hd : d ∈ zpowers z) : d * d = 1 := by
  rcases hy.mem_zpowers_z_iff.mp hd with h | h
  · rw [h, one_mul]
  · rw [h, hy.z_sq]

theorem comm_mul_left {a b c : G} (ha : a ∈ J z) (hb : b ∈ J z) (hc : c ∈ J z) :
    a * b * c * (a * b)⁻¹ * c⁻¹ = (a * c * a⁻¹ * c⁻¹) * (b * c * b⁻¹ * c⁻¹) := by
  set d := b * c * b⁻¹ * c⁻¹ with hd
  have hdz : d ∈ zpowers z := hy.comm_mem hb hc
  have had : a * d = d * a := hy.commute_of_mem_zpowers_of_mem_H (J_le_H ha) hdz
  have hacH : a * c * a⁻¹ * c⁻¹ ∈ H z := J_le_H (hy.zpowers_le_J (hy.comm_mem ha hc))
  have hd' := hy.commute_of_mem_zpowers_of_mem_H hacH hdz
  calc a * b * c * (a * b)⁻¹ * c⁻¹ = a * d * c * a⁻¹ * c⁻¹ := by rw [hd]; group
    _ = d * a * c * a⁻¹ * c⁻¹ := by rw [had]
    _ = d * (a * c * a⁻¹ * c⁻¹) := by group
    _ = (a * c * a⁻¹ * c⁻¹) * d := hd'.symm

theorem comm_mul_right {a b c : G} (ha : a ∈ J z) (hb : b ∈ J z) (hc : c ∈ J z) :
    a * (b * c) * a⁻¹ * (b * c)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by
  set d := a * c * a⁻¹ * c⁻¹ with hd
  have hdz : d ∈ zpowers z := hy.comm_mem ha hc
  have hab : a * b * a⁻¹ ∈ H z := J_le_H (conj_mem_J (J_le_H ha) hb)
  have hdb := hy.commute_of_mem_zpowers_of_mem_H hab hdz
  have habH : a * b * a⁻¹ * b⁻¹ ∈ H z := J_le_H (hy.zpowers_le_J (hy.comm_mem ha hb))
  have hd' := hy.commute_of_mem_zpowers_of_mem_H habH hdz
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹ = (a * b * a⁻¹) * d * b⁻¹ := by rw [hd]; group
    _ = d * (a * b * a⁻¹) * b⁻¹ := by rw [hdb]
    _ = d * (a * b * a⁻¹ * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * d := hd'.symm

theorem commute_conj_mul {g w₁ w₂ : G} (hg : g ∈ H z) (hg2 : g * g ∈ J z) (hw₁ : w₁ ∈ J z)
    (hw₂ : w₂ ∈ J z) :
    (g * w₁ * g⁻¹ * w₁) * (g * w₂ * g⁻¹ * w₂) = (g * w₂ * g⁻¹ * w₂) * (g * w₁ * g⁻¹ * w₁) := by
  set w₁' := g * w₁ * g⁻¹ with hw₁'
  set w₂' := g * w₂ * g⁻¹ with hw₂'
  have h₁' : w₁' ∈ J z := conj_mem_J hg hw₁
  have h₂' : w₂' ∈ J z := conj_mem_J hg hw₂
  have e1 : w₁' * w₂' * w₁'⁻¹ * w₂'⁻¹ = w₁ * w₂ * w₁⁻¹ * w₂⁻¹ := by
    have h := conj_eq_of_mem_zpowers hg (hy.comm_mem hw₁ hw₂)
    rw [← h, hw₁', hw₂']
    group
  have e2 : w₁ * w₂' * w₁⁻¹ * w₂'⁻¹ = w₁' * w₂ * w₁'⁻¹ * w₂⁻¹ := by
    set ε := (g * g)⁻¹ * w₁' * (g * g)⁻¹⁻¹ * w₁'⁻¹ with hε
    have hεz : ε ∈ zpowers z := hy.comm_mem ((J z).inv_mem hg2) h₁'
    have hεJ : ε ∈ J z := hy.zpowers_le_J hεz
    have hg1 : g⁻¹ * w₁ * g = ε * w₁' := by rw [hε, hw₁']; group
    have hg1J : g⁻¹ * w₁ * g ∈ J z := by rw [hg1]; exact (J z).mul_mem hεJ h₁'
    have h1 : w₁ * w₂' * w₁⁻¹ * w₂'⁻¹ =
        g * ((g⁻¹ * w₁ * g) * w₂ * (g⁻¹ * w₁ * g)⁻¹ * w₂⁻¹) * g⁻¹ := by
      rw [hw₂']; group
    rw [h1, conj_eq_of_mem_zpowers hg (hy.comm_mem hg1J hw₂), hg1,
      hy.comm_mul_left hεJ h₁' hw₂]
    have hε1 : ε * w₂ * ε⁻¹ * w₂⁻¹ = 1 := by
      have hc : ε * w₂ = w₂ * ε := (hy.commute_of_mem_zpowers_of_mem_H (J_le_H hw₂) hεz).symm
      calc ε * w₂ * ε⁻¹ * w₂⁻¹ = w₂ * ε * ε⁻¹ * w₂⁻¹ := by rw [hc]
        _ = 1 := by group
    rw [hε1, one_mul]
  have hA := hy.comm_mem hw₁ hw₂
  have hB := hy.comm_mem h₁' hw₂
  suffices h : (w₁' * w₁) * (w₂' * w₂) * (w₁' * w₁)⁻¹ * (w₂' * w₂)⁻¹ = 1 by
    calc (w₁' * w₁) * (w₂' * w₂)
        = ((w₁' * w₁) * (w₂' * w₂) * (w₁' * w₁)⁻¹ * (w₂' * w₂)⁻¹) * ((w₂' * w₂) * (w₁' * w₁)) := by
          group
      _ = (w₂' * w₂) * (w₁' * w₁) := by rw [h, one_mul]
  rw [hy.comm_mul_left h₁' hw₁ ((J z).mul_mem h₂' hw₂), hy.comm_mul_right h₁' h₂' hw₂,
    hy.comm_mul_right hw₁ h₂' hw₂, e1, e2]
  set A := w₁ * w₂ * w₁⁻¹ * w₂⁻¹ with hAdef
  set B := w₁' * w₂ * w₁'⁻¹ * w₂⁻¹ with hBdef
  calc A * B * (B * A) = A * (B * B) * A := by group
    _ = 1 := by rw [hy.mul_self_eq_one_of_mem_zpowers hB, mul_one,
        hy.mul_self_eq_one_of_mem_zpowers hA]

theorem orbit_mem_zpowers {x : G} (hx : x ∈ hy.R) :
    x * ((s1 * s2⁻¹) * x * (s1 * s2⁻¹)⁻¹) *
      ((s1 * s2⁻¹) * ((s1 * s2⁻¹) * x * (s1 * s2⁻¹)⁻¹) * (s1 * s2⁻¹)⁻¹) ∈ zpowers z := by
  set s := s1 * s2⁻¹ with hs
  have hsR : ∀ a, a ∈ hy.R ↔ s * a * s⁻¹ ∈ hy.R := mem_commutator_conj_iff hy.s_mem rfl
  have hRJ : hy.R ≤ J z := hy.R_le_J
  have hx1 : s * x * s⁻¹ ∈ hy.R := (hsR x).mp hx
  have hx2 : s * (s * x * s⁻¹) * s⁻¹ ∈ hy.R := (hsR _).mp hx1
  have hmem : x * (s * x * s⁻¹) * (s * (s * x * s⁻¹) * s⁻¹) ∈ hy.R :=
    hy.R.mul_mem (hy.R.mul_mem hx hx1) hx2
  set sH : ↥(H z) := ⟨s, hy.s_mem⟩ with hsH
  have hs3 : sH ^ 3 = 1 := Subtype.ext (by simpa [hsH] using hy.s_pow_three)
  set v := pi z ⟨x, hRJ hx⟩ with hv
  have hv1 : conjVA z sH v = pi z ⟨s * x * s⁻¹, hRJ hx1⟩ := conjVA_pi sH _
  have hv2 : conjVA z sH (conjVA z sH v) = pi z ⟨s * (s * x * s⁻¹) * s⁻¹, hRJ hx2⟩ := by
    rw [hv1, conjVA_pi]
  have hv3 : conjVA z sH (conjVA z sH (conjVA z sH v)) = v := by
    have h3 : (conjVA z sH ^ 3) v = v := by rw [← map_pow, hs3, map_one]; rfl
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply] using h3
  have hpi : pi z ⟨x * (s * x * s⁻¹) * (s * (s * x * s⁻¹) * s⁻¹), hRJ hmem⟩ =
      v * conjVA z sH v * conjVA z sH (conjVA z sH v) := by
    rw [hv2, hv1, ← map_mul, ← map_mul]
    rfl
  rw [← pi_eq_one_iff hy.hA1 (a := ⟨_, hRJ hmem⟩)]
  apply hy.s_fix_imV_R (pi_mem_imV hmem)
  rw [hpi, map_mul, map_mul, hv3,
    V_comm hy.hA1 (conjVA z sH v * conjVA z sH (conjVA z sH v)) v, mul_assoc]

theorem sq_eq_comm_of_mem_R {x : G} (hx : x ∈ hy.R) :
    x * x = ((s1 * s2⁻¹) * x * (s1 * s2⁻¹)⁻¹) * x * ((s1 * s2⁻¹) * x * (s1 * s2⁻¹)⁻¹)⁻¹ * x⁻¹ := by
  set s := s1 * s2⁻¹ with hs
  have hsH : s ∈ H z := hy.s_mem
  have hxJ : x ∈ J z := hy.R_le_J hx
  set x₂ := s * x * s⁻¹ with hx₂
  set x₃ := s * x₂ * s⁻¹ with hx₃
  have hx₂J : x₂ ∈ J z := conj_mem_J hsH hxJ
  set p := x * x₂ * x₃ with hp
  have hpz : p ∈ zpowers z := hy.orbit_mem_zpowers hx
  have hxx : x * x ∈ zpowers z := hy.sq_mem hxJ
  set c := x₂ * x * x₂⁻¹ * x⁻¹ with hc
  have hcz : c ∈ zpowers z := hy.comm_mem hx₂J hxJ
  have hx₂sq : x₂ * x₂ = x * x := by
    have h := conj_eq_of_mem_zpowers hsH hxx
    rw [← h, hx₂]
    group
  have hx₃sq : x₃ * x₃ = x * x := by
    have h := conj_eq_of_mem_zpowers hsH (show x₂ * x₂ ∈ zpowers z by rw [hx₂sq]; exact hxx)
    rw [← hx₂sq, ← h, hx₃]
    group
  have hcx : ∀ w ∈ H z, w * c = c * w := fun w hw => hy.commute_of_mem_zpowers_of_mem_H hw hcz
  have hsq : (x * x₂) * (x * x₂) = c := by
    have h1 : x₂ * x = c * (x * x₂) := by rw [hc]; group
    calc (x * x₂) * (x * x₂) = x * (x₂ * x) * x₂ := by group
      _ = x * (c * (x * x₂)) * x₂ := by rw [h1]
      _ = (x * c) * x * x₂ * x₂ := by group
      _ = (c * x) * x * x₂ * x₂ := by rw [hcx x (J_le_H hxJ)]
      _ = c * (x * x) * (x₂ * x₂) := by group
      _ = c * (x * x) * (x * x) := by rw [hx₂sq]
      _ = c := by rw [mul_assoc, hy.mul_self_eq_one_of_mem_zpowers hxx, mul_one]
  have hx₃eq : x₃ = (x * x₂)⁻¹ * p := by rw [hp]; group
  have hpc : ∀ w ∈ H z, w * p = p * w := fun w hw => hy.commute_of_mem_zpowers_of_mem_H hw hpz
  have hxx₂H : (x * x₂)⁻¹ ∈ H z := (H z).inv_mem ((H z).mul_mem (J_le_H hxJ) (J_le_H hx₂J))
  calc x * x = x₃ * x₃ := hx₃sq.symm
    _ = (x * x₂)⁻¹ * p * ((x * x₂)⁻¹ * p) := by rw [hx₃eq]
    _ = (x * x₂)⁻¹ * (p * (x * x₂)⁻¹) * p := by group
    _ = (x * x₂)⁻¹ * ((x * x₂)⁻¹ * p) * p := by rw [hpc _ hxx₂H]
    _ = ((x * x₂) * (x * x₂))⁻¹ * (p * p) := by group
    _ = c⁻¹ := by rw [hsq, hy.mul_self_eq_one_of_mem_zpowers hpz, mul_one]
    _ = c := hy.inv_eq_self_of_mem_zpowers hcz
    _ = x₂ * x * x₂⁻¹ * x⁻¹ := rfl

theorem conj_mul_mem_R {g w : G} (hgC : ∀ c ∈ CJ z (s1 * s2⁻¹), g * c = c * g)
    (hgR : ∀ a : G, a ∈ hy.R ↔ g * a * g⁻¹ ∈ hy.R) (hw : w ∈ J z) :
    g * w * g⁻¹ * w ∈ hy.R := by
  obtain ⟨c, hc, ρ, hρ, rfl⟩ := hy.exists_mul_of_mem_J hw
  have hρ' : g * ρ * g⁻¹ ∈ hy.R := (hgR ρ).mp hρ
  have hcρ : c * (g * ρ * g⁻¹) = (g * ρ * g⁻¹) * c := hy.commute_CJs_R c hc _ hρ'
  have e : g * (c * ρ) * g⁻¹ * (c * ρ) = (c * c) * ((g * ρ * g⁻¹) * ρ) := by
    calc g * (c * ρ) * g⁻¹ * (c * ρ) = (g * c) * ρ * g⁻¹ * c * ρ := by group
      _ = (c * g) * ρ * g⁻¹ * c * ρ := by rw [hgC c hc]
      _ = c * ((g * ρ * g⁻¹) * c) * ρ := by group
      _ = c * (c * (g * ρ * g⁻¹)) * ρ := by rw [hcρ]
      _ = (c * c) * ((g * ρ * g⁻¹) * ρ) := by group
  rw [e]
  exact hy.R.mul_mem (hy.zpowers_le_R (hy.sq_mem ((CJ_le_J _) hc))) (hy.R.mul_mem hρ' hρ)

theorem sq_conj_mul_t {t₁ w : G} (ht₁H : t₁ ∈ H z) (hts : t₁ * (s1 * s2⁻¹) = (s1 * s2⁻¹) * t₁)
    (htC : ∀ c ∈ CJ z (s1 * s2⁻¹), t₁ * c = c * t₁) (ht2 : t₁ * t₁ ∈ J z) (hw : w ∈ J z) :
    (t₁ * w * t₁⁻¹ * w) * (t₁ * w * t₁⁻¹ * w) = 1 := by
  set s := s1 * s2⁻¹ with hs
  have hxR := hy.conj_mul_mem_R htC (mem_commutator_conj_iff ht₁H hts) hw
  have hsw : s * w * s⁻¹ ∈ J z := conj_mem_J hy.s_mem hw
  have hx₂ : s * (t₁ * w * t₁⁻¹ * w) * s⁻¹ = t₁ * (s * w * s⁻¹) * t₁⁻¹ * (s * w * s⁻¹) := by
    have hts' : s * t₁ = t₁ * s := hts.symm
    have hts'' : t₁⁻¹ * s⁻¹ = s⁻¹ * t₁⁻¹ := by
      calc t₁⁻¹ * s⁻¹ = (s * t₁)⁻¹ := by group
        _ = (t₁ * s)⁻¹ := by rw [hts']
        _ = s⁻¹ * t₁⁻¹ := by group
    calc s * (t₁ * w * t₁⁻¹ * w) * s⁻¹ = (s * t₁) * w * (t₁⁻¹ * s⁻¹) * (s * w * s⁻¹) := by group
      _ = (t₁ * s) * w * (s⁻¹ * t₁⁻¹) * (s * w * s⁻¹) := by rw [hts', hts'']
      _ = t₁ * (s * w * s⁻¹) * t₁⁻¹ * (s * w * s⁻¹) := by group
  have hcomm := hy.commute_conj_mul ht₁H ht2 hw hsw
  rw [hy.sq_eq_comm_of_mem_R hxR, hx₂]
  set x := t₁ * w * t₁⁻¹ * w
  set x₂ := t₁ * (s * w * s⁻¹) * t₁⁻¹ * (s * w * s⁻¹)
  calc x₂ * x * x₂⁻¹ * x⁻¹ = x * x₂ * x₂⁻¹ * x⁻¹ := by rw [← hcomm]
    _ = 1 := by group

theorem sq_conj_mul_of_conj {t₁ u₁ b w : G} (hbH : b ∈ H z) (ht₁H : t₁ ∈ H z)
    (hbu : t₁⁻¹ * (b * u₁ * b⁻¹) ∈ J z)
    (hsqt : ∀ w ∈ J z, (t₁ * w * t₁⁻¹ * w) * (t₁ * w * t₁⁻¹ * w) = 1) (hw : w ∈ J z) :
    (u₁ * w * u₁⁻¹ * w) * (u₁ * w * u₁⁻¹ * w) = 1 := by
  set j := t₁⁻¹ * (b * u₁ * b⁻¹) with hj
  set w' := b * w * b⁻¹ with hw'
  have hw'J : w' ∈ J z := conj_mem_J hbH hw
  set ε := j * w' * j⁻¹ * w'⁻¹ with hε
  have hεz : ε ∈ zpowers z := hy.comm_mem hbu hw'J
  have hεc : ∀ g ∈ H z, g * ε = ε * g := fun g hg => hy.commute_of_mem_zpowers_of_mem_H hg hεz
  have hconj : b * (u₁ * w * u₁⁻¹ * w) * b⁻¹ = ε * (t₁ * w' * t₁⁻¹ * w') := by
    have hjw : j * w' * j⁻¹ = ε * w' := by rw [hε]; group
    calc b * (u₁ * w * u₁⁻¹ * w) * b⁻¹
        = t₁ * (j * w' * j⁻¹) * t₁⁻¹ * w' := by rw [hj, hw']; group
      _ = t₁ * (ε * w') * t₁⁻¹ * w' := by rw [hjw]
      _ = (t₁ * ε) * w' * t₁⁻¹ * w' := by group
      _ = (ε * t₁) * w' * t₁⁻¹ * w' := by rw [hεc t₁ ht₁H]
      _ = ε * (t₁ * w' * t₁⁻¹ * w') := by group
  have hsq : (b * (u₁ * w * u₁⁻¹ * w) * b⁻¹) * (b * (u₁ * w * u₁⁻¹ * w) * b⁻¹) = 1 := by
    rw [hconj]
    have hxH : t₁ * w' * t₁⁻¹ * w' ∈ H z :=
      (H z).mul_mem ((H z).mul_mem ((H z).mul_mem ht₁H (J_le_H hw'J)) ((H z).inv_mem ht₁H))
        (J_le_H hw'J)
    calc ε * (t₁ * w' * t₁⁻¹ * w') * (ε * (t₁ * w' * t₁⁻¹ * w'))
        = ε * ((t₁ * w' * t₁⁻¹ * w') * ε) * (t₁ * w' * t₁⁻¹ * w') := by group
      _ = ε * (ε * (t₁ * w' * t₁⁻¹ * w')) * (t₁ * w' * t₁⁻¹ * w') := by rw [hεc _ hxH]
      _ = (ε * ε) * ((t₁ * w' * t₁⁻¹ * w') * (t₁ * w' * t₁⁻¹ * w')) := by group
      _ = 1 := by rw [hy.mul_self_eq_one_of_mem_zpowers hεz, hsqt w' hw'J, one_mul]
  have e : (u₁ * w * u₁⁻¹ * w) * (u₁ * w * u₁⁻¹ * w) =
      b⁻¹ * ((b * (u₁ * w * u₁⁻¹ * w) * b⁻¹) * (b * (u₁ * w * u₁⁻¹ * w) * b⁻¹)) * b := by group
  rw [e, hsq]
  group

theorem mem_zpowers_of_mem_R_of_commute {c : G} (hc : c ∈ hy.R)
    (hcomm : ∀ d ∈ hy.R, c * d = d * c) : c ∈ zpowers z := by
  apply hy.mem_zpowers_of_commute_J (hy.R_le_J hc)
  intro b hb
  obtain ⟨d, hd, r, hr, rfl⟩ := hy.exists_mul_of_mem_J hb
  have h1 : c * d = d * c := (hy.commute_CJs_R d hd c hc).symm
  calc c * (d * r) = (c * d) * r := by group
    _ = (d * c) * r := by rw [h1]
    _ = d * (c * r) := by group
    _ = d * (r * c) := by rw [hcomm r hr]
    _ = d * r * c := by group

theorem card_le_eight_of_commute_R {A : Subgroup G} (hAR : A ≤ hy.R)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : Nat.card A ≤ 8 := by
  by_contra hcon
  push Not at hcon
  have hR32 : Nat.card hy.R = 32 := hy.card_R
  have hA16 : 16 ≤ Nat.card A := by
    have hdvd : Nat.card A ∣ 2 ^ 5 := by
      rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← hR32]
      exact Subgroup.card_dvd_of_le hAR
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hkeq] at hcon ⊢
    interval_cases k <;> simp_all
  obtain ⟨c, hcA, hcz⟩ : ∃ c ∈ A, c ∉ zpowers z := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show A ≤ zpowers z from h)
    rw [hy.card_zpowers_z] at this
    omega
  set CR := hy.R ⊓ Subgroup.centralizer ({c} : Set G) with hCR
  have hACR : A ≤ CR := fun a ha =>
    ⟨hAR ha, Subgroup.mem_centralizer_singleton_iff.mpr (hA a ha c hcA)⟩
  have hCR16 : Nat.card CR ≤ 16 := by
    have hne : CR ≠ hy.R := by
      intro h
      apply hcz
      apply hy.mem_zpowers_of_mem_R_of_commute (hAR hcA)
      intro d hd
      have hd' : d ∈ CR := h ▸ hd
      exact (Subgroup.mem_centralizer_singleton_iff.mp hd'.2).symm
    have hdvd : Nat.card CR ∣ 2 ^ 5 := by
      rw [show (2 : ℕ) ^ 5 = 32 by norm_num, ← hR32]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk5 : k ≠ 5 := by
      intro h5
      apply hne
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hkeq, h5, hR32]
      norm_num
    rw [hkeq]
    interval_cases k <;> simp_all
  have hAeq : A = CR := Subgroup.eq_of_le_of_card_ge hACR (by omega)
  obtain ⟨a, haR, b, hbR, hac, hbc, hab⟩ := hy.exists_not_commute_of_le_J hy.R_le_J
    (le_of_eq hR32.symm) (fun a ha hcomm => hy.mem_zpowers_of_mem_R_of_commute ha hcomm)
    (hy.R_le_J (hAR hcA))
  have haA : a ∈ A := by
    rw [hAeq]
    exact ⟨haR, Subgroup.mem_centralizer_singleton_iff.mpr hac⟩
  have hbA : b ∈ A := by
    rw [hAeq]
    exact ⟨hbR, Subgroup.mem_centralizer_singleton_iff.mpr hbc⟩
  exact hab (hA a haA b hbA)

@[expose] noncomputable def commV (τ : MulAut (V z)) : V z →* V z :=
  MonoidHom.mk' (fun v => τ v * v) (fun x y => by
    have h := V_comm hy.hA1 (τ y) x
    change τ (x * y) * (x * y) = τ x * x * (τ y * y)
    rw [map_mul]
    calc τ x * τ y * (x * y) = τ x * (τ y * x) * y := by simp only [mul_assoc]
      _ = τ x * (x * τ y) * y := by rw [h]
      _ = τ x * x * (τ y * y) := by simp only [mul_assoc])

theorem commV_apply (τ : MulAut (V z)) (v : V z) : hy.commV τ v = τ v * v := rfl

theorem eq_one_or_eq_of_mem_zpowers {a x : V z} (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact V_sq hy.hA1 a
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    obtain ⟨j, rfl⟩ : (2 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero hk
    rw [zpow_mul, ha2, one_zpow]
  · right
    have hk' : k = 2 * (k / 2) + 1 := by omega
    rw [hk', zpow_add, zpow_mul, ha2, one_zpow, one_mul, zpow_one]

theorem four_le_card_sup {a x : V z} (ha : a ≠ 1) (hx1 : x ≠ 1) (hxa : x ≠ a) :
    4 ≤ Nat.card (zpowers a ⊔ zpowers x : Subgroup (V z)) := by
  have hza : Nat.card (zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact V_sq hy.hA1 a) ha
  obtain ⟨m, hm⟩ : Nat.card (zpowers a) ∣ Nat.card (zpowers a ⊔ zpowers x : Subgroup (V z)) :=
    Subgroup.card_dvd_of_le le_sup_left
  rw [hza] at hm
  have hpos : 0 < Nat.card (zpowers a ⊔ zpowers x : Subgroup (V z)) := Nat.card_pos
  have hm1 : m ≠ 1 := by
    rintro rfl
    have heq : zpowers a = zpowers a ⊔ zpowers x :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, hza])
    have hxmem : x ∈ zpowers a := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rcases hy.eq_one_or_eq_of_mem_zpowers hxmem with h | h
    · exact hx1 h
    · exact hxa h
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m <;> omega
  · omega

theorem exists_key {t₁ u₁ c₁ b : G} (ht₁H : t₁ ∈ H z) (hu₁H : u₁ ∈ H z) (hc₁H : c₁ ∈ H z)
    (hbH : b ∈ H z) (hts : t₁ * (s1 * s2⁻¹) = (s1 * s2⁻¹) * t₁)
    (hus : u₁ * (s1 * s2⁻¹) * u₁⁻¹ = (s1 * s2⁻¹)⁻¹)
    (htC : ∀ c ∈ CJ z (s1 * s2⁻¹), t₁ * c = c * t₁)
    (huC : ∀ c ∈ CJ z (s1 * s2⁻¹), u₁ * c = c * u₁)
    (ht2 : t₁ * t₁ ∈ J z) (hu2 : u₁ * u₁ ∈ J z) (hut : u₁ * t₁ * u₁⁻¹ * t₁⁻¹ ∈ J z)
    (hc₁ : (u₁ * t₁)⁻¹ * c₁ ∈ J z) (hc₁2 : c₁ * c₁ ∈ zpowers z)
    (hc₁R : ∀ a : G, a ∈ hy.R ↔ c₁ * a * c₁⁻¹ ∈ hy.R)
    (hbu : t₁⁻¹ * (b * u₁ * b⁻¹) ∈ J z)
    (hFt : Nat.card (fixIn (imV z hy.R) (conjVA z (⟨t₁, ht₁H⟩ : ↥(H z)))) ^ 2 ≤
      Nat.card (imV z hy.R))
    (hfreec : ∀ v ∈ imV z hy.R, conjVA z (⟨c₁, hc₁H⟩ : ↥(H z)) v = v →
      ∃ w ∈ imV z hy.R, v = conjVA z (⟨c₁, hc₁H⟩ : ↥(H z)) w * w) :
    ∃ r ∈ hy.R, r * r = z ∧ c₁ * r * c₁⁻¹ * r⁻¹ = z := by
  classical
  set s := s1 * s2⁻¹ with hs
  have hRJ : hy.R ≤ J z := hy.R_le_J
  set Rb := imV z hy.R with hRb
  have hRb16 : Nat.card Rb = 16 := by
    have h : Nat.card Rb * 2 = Nat.card hy.R := card_imV hy.hA1 hRJ hy.zpowers_le_R
    rw [hy.card_R] at h
    omega
  set tH : ↥(H z) := ⟨t₁, ht₁H⟩ with htH
  set uH : ↥(H z) := ⟨u₁, hu₁H⟩ with huH
  set cH : ↥(H z) := ⟨c₁, hc₁H⟩ with hcH
  set sH : ↥(H z) := ⟨s, hy.s_mem⟩ with hsH
  set bH : ↥(H z) := ⟨b, hbH⟩ with hbH'
  set τt := conjVA z tH with hτt
  set τu := conjVA z uH with hτu
  set τc := conjVA z cH with hτc
  set β := conjVA z sH with hβ
  set τb := conjVA z bH with hτb
  have hcongr : ∀ g h : ↥(H z), (g : G)⁻¹ * h ∈ J z → ∀ v, conjVA z h v = conjVA z g v := by
    intro g h hgh v
    have e : h = g * (g⁻¹ * h) := by group
    have hJ : ((g⁻¹ * h : ↥(H z)) : G) ∈ J z := by simpa using hgh
    rw [e, map_mul, MulAut.mul_apply, conjVA_apply_of_mem_J hy.hA1 hJ]
  have hτc' : ∀ v, τc v = τu (τt v) := by
    intro v
    rw [hτc, hcongr (uH * tH) cH (by simpa using hc₁) v, map_mul, MulAut.mul_apply]
  have hτtu : ∀ v, τt (τu v) = τu (τt v) := by
    intro v
    have h : ((tH * uH : ↥(H z)) : G)⁻¹ * (uH * tH : ↥(H z)) ∈ J z := by
      have e : ((tH * uH : ↥(H z)) : G)⁻¹ * (uH * tH : ↥(H z)) =
          (t₁ * u₁)⁻¹ * (u₁ * t₁ * u₁⁻¹ * t₁⁻¹) * (t₁ * u₁)⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, htH, huH]; group
      rw [e]
      exact conj_mem_J ((H z).inv_mem ((H z).mul_mem ht₁H hu₁H)) hut
    have := hcongr (tH * uH) (uH * tH) h v
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at this
    exact this.symm
  have hτt2 : ∀ v, τt (τt v) = v := by
    intro v
    have h := conjVA_apply_of_mem_J hy.hA1 (g := tH * tH) ht2 v
    rwa [map_mul, MulAut.mul_apply] at h
  have hτu2 : ∀ v, τu (τu v) = v := by
    intro v
    have h := conjVA_apply_of_mem_J hy.hA1 (g := uH * uH) hu2 v
    rwa [map_mul, MulAut.mul_apply] at h
  have hs3 : sH ^ 3 = 1 := Subtype.ext (by simpa [hsH] using hy.s_pow_three)
  have hβ3 : ∀ v, β (β (β v)) = v := by
    intro v
    have h : (β ^ 3) v = v := by rw [hβ, ← map_pow, hs3, map_one]; rfl
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply] using h
  have hβt : ∀ v, τt (β v) = β (τt v) := by
    intro v
    have e : tH * sH = sH * tH := Subtype.ext hts
    rw [hτt, hβ, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, e]
  have hβu : ∀ v, τu (β v) = β (β (τu v)) := by
    intro v
    have e : uH * sH = sH * sH * uH := by
      apply Subtype.ext
      change u₁ * s = s * s * u₁
      have h1 : u₁ * s = s⁻¹ * u₁ := by
        calc u₁ * s = (u₁ * s * u₁⁻¹) * u₁ := by group
          _ = s⁻¹ * u₁ := by rw [hus]
      have h2 : s⁻¹ = s * s := by
        rw [inv_eq_iff_mul_eq_one, ← hy.s_pow_three, pow_succ', pow_two]
      rw [h1, h2]
    have h := congrArg (fun g => conjVA z g v) e
    simp only [map_mul, MulAut.mul_apply] at h
    exact h
  have hτbu : ∀ v, τb (τu v) = τt (τb v) := by
    intro v
    have h : ((tH * bH : ↥(H z)) : G)⁻¹ * (bH * uH : ↥(H z)) ∈ J z := by
      have e : ((tH * bH : ↥(H z)) : G)⁻¹ * (bH * uH : ↥(H z)) =
          b⁻¹ * (t₁⁻¹ * (b * u₁ * b⁻¹)) * b⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, htH, hbH', huH]; group
      rw [e]
      exact conj_mem_J ((H z).inv_mem hbH) hbu
    have := hcongr (tH * bH) (bH * uH) h v
    rwa [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at this
  have hτtRb : ∀ v, τt v ∈ Rb ↔ v ∈ Rb :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_R tH (mem_commutator_conj_iff ht₁H hts)
  have hβRb : ∀ v, β v ∈ Rb ↔ v ∈ Rb :=
    conjVA_mem_imV_iff hy.hA1 hy.zpowers_le_R sH (mem_commutator_conj_iff hy.s_mem rfl)
  have hβfix : ∀ v ∈ Rb, β v = v → v = 1 := fun v hv h => hy.s_fix_imV_R hv h
  have hβinj : ∀ v w, β v = β w → v = w := fun v w h => β.injective h
  have horbit : ∀ v ∈ Rb, β (β v) * v = β v := by
    intro v hv
    have hv1 := (hβRb v).mpr hv
    have hv2 := (hβRb _).mpr hv1
    have hp : v * β v * β (β v) = 1 := by
      apply hβfix _ (Rb.mul_mem (Rb.mul_mem hv hv1) hv2)
      rw [map_mul, map_mul, hβ3]
      rw [V_comm hy.hA1 (β v * β (β v)) v, mul_assoc]
    have h1 : β (β v) * v * β v = 1 := by
      rw [V_comm hy.hA1 (β (β v)) v, mul_assoc, V_comm hy.hA1 (β (β v)) (β v), ← mul_assoc]
      exact hp
    calc β (β v) * v = β (β v) * v * (β v * β v) := by rw [V_sq hy.hA1, mul_one]
      _ = (β (β v) * v * β v) * β v := by simp only [mul_assoc]
      _ = β v := by rw [h1, one_mul]
  set Ft := fixIn Rb τt with hFtdef
  have hFt4 : Nat.card Ft ≤ 4 := by
    have h16 : Nat.card Ft ^ 2 ≤ Nat.card Rb := hFt
    rw [hRb16] at h16
    by_contra h
    push Not at h
    have h25 : 5 * 5 ≤ Nat.card Ft ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul h h
    omega
  have hfreet := exists_eq_mul_of_card_fix_sq_le (V_comm hy.hA1) Rb τt hτtRb
    (fun v _ => hτt2 v) (fun v _ => V_sq hy.hA1 v) hFt
  set ψu := hy.commV τu with hψu
  set U := ψu.range with hU
  have hψu_pi : ∀ j : J z, ψu (pi z j) =
      pi z ⟨u₁ * j * u₁⁻¹ * j, (J z).mul_mem (conj_mem_J hu₁H j.2) j.2⟩ := by
    intro j
    rw [hψu, commV_apply, hτu, conjVA_pi, ← map_mul]
    rfl
  have hgR : ∀ a : G, a ∈ hy.R ↔ u₁ * a * u₁⁻¹ ∈ hy.R := mem_commutator_conj_iff_of_inv hu₁H hus
  have hURb : ∀ v ∈ U, v ∈ Rb := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨j, rfl⟩ := pi_surjective z w
    rw [hψu_pi]
    exact pi_mem_imV (hy.conj_mul_mem_R huC hgR j.2)
  have hUfix : ∀ v ∈ U, τu v = v := by
    rintro _ ⟨w, rfl⟩
    rw [hψu, commV_apply, map_mul, hτu2, V_comm hy.hA1]
  have hUt : ∀ v, τt v ∈ U ↔ v ∈ U := by
    have fwd : ∀ v, v ∈ U → τt v ∈ U := by
      rintro _ ⟨w, rfl⟩
      exact ⟨τt w, by rw [hψu, commV_apply, commV_apply, map_mul, hτtu]⟩
    intro v
    refine ⟨fun h => ?_, fwd v⟩
    have := fwd _ h
    rwa [hτt2] at this
  have hU4 : 4 ≤ Nat.card U := by
    let f : ↥Rb →* V z := (hy.commV τt).comp Rb.subtype
    have hker : f.ker.map Rb.subtype = Ft := by
      ext v
      simp only [Subgroup.mem_map, MonoidHom.mem_ker]
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.2, ?_⟩
        change τt (w : V z) = (w : V z)
        have h1 : τt w * w = 1 := hw
        have h2 : τt w = (w : V z)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h2]
        exact inv_eq_of_mul_eq_one_right (V_sq hy.hA1 w)
      · rintro ⟨hvRb, hvfix⟩
        refine ⟨⟨v, hvRb⟩, ?_, rfl⟩
        change τt v * v = 1
        rw [hvfix, V_sq hy.hA1]
    have hkercard : Nat.card f.ker = Nat.card Ft := by
      rw [← hker, Subgroup.card_map_of_injective Rb.subtype_injective]
    have h := Subgroup.card_ker_mul_card_range f
    rw [hkercard, hRb16] at h
    have hrange : 4 ≤ Nat.card f.range := by
      by_contra hcon
      push Not at hcon
      have : Nat.card Ft * Nat.card f.range < 16 := by
        calc Nat.card Ft * Nat.card f.range ≤ 4 * Nat.card f.range :=
              Nat.mul_le_mul_right _ hFt4
          _ < 16 := by omega
      omega
    have hle : f.range.map (conjVA z bH⁻¹).toMonoidHom ≤ U := by
      rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨conjVA z bH⁻¹ w, ?_⟩
      change τu (conjVA z bH⁻¹ w) * conjVA z bH⁻¹ w = conjVA z bH⁻¹ (τt w * w)
      have h1 : τu (conjVA z bH⁻¹ w) = conjVA z bH⁻¹ (τt w) := by
        have h2 := hτbu (conjVA z bH⁻¹ w)
        have h3 : τb (conjVA z bH⁻¹ w) = w := by
          rw [hτb, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          rfl
        rw [h3] at h2
        have h4 := congrArg (conjVA z bH⁻¹) h2
        rwa [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one] at h4
      rw [h1, map_mul]
    calc 4 ≤ Nat.card f.range := hrange
      _ = Nat.card (f.range.map (conjVA z bH⁻¹).toMonoidHom) :=
          (Subgroup.card_map_of_injective (conjVA z bH⁻¹).injective).symm
      _ ≤ Nat.card U := Subgroup.card_le_of_le hle
  have hUeven : Even (Nat.card U) := by
    have hdvd : Nat.card U ∣ 2 ^ 4 := by
      rw [show (2 : ℕ) ^ 4 = 16 by norm_num, ← hRb16]
      exact Subgroup.card_dvd_of_le hURb
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hkeq] at hU4 ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      norm_num at hU4
    exact (Nat.even_pow' hk0).mpr even_two
  obtain ⟨a, haU, ha1, hta⟩ := exists_fix_of_sq U τt hUt
    (fun v _ => by rw [pow_two, MulAut.mul_apply, hτt2]) hUeven
  have haRb := hURb a haU
  have haFt : a ∈ Ft := ⟨haRb, hta⟩
  have hua : τu a = a := hUfix a haU
  obtain ⟨b', hbU, hb1, hba⟩ : ∃ b' ∈ U, b' ≠ 1 ∧ b' ≠ a := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ zpowers a := by
      intro v hv
      by_cases h : v = 1
      · rw [h]; exact Subgroup.one_mem _
      · rw [hcon v hv h]; exact Subgroup.mem_zpowers a
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf a ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num)
      (by rw [pow_two]; exact V_sq hy.hA1 a)
    omega
  have hbRb := hURb b' hbU
  have hβaFt : β a ∈ Ft := ⟨(hβRb a).mpr haRb, by rw [hβt, hta]⟩
  have hβa1 : β a ≠ a := fun h => ha1 (hβfix a haRb h)
  have hβaU : β a ∉ U := by
    intro h
    have h1 := hUfix _ h
    rw [hβu, hua] at h1
    exact hβa1 (hβinj _ _ h1)
  have hUFt : ∀ x ∈ U, x ∈ Ft → x = 1 ∨ x = a := by
    intro x hxU hxFt
    by_contra hx
    push Not at hx
    have hP : zpowers a ⊔ zpowers x ≤ Ft :=
      sup_le (Subgroup.zpowers_le.mpr haFt) (Subgroup.zpowers_le.mpr hxFt)
    have hPU : zpowers a ⊔ zpowers x ≤ U :=
      sup_le (Subgroup.zpowers_le.mpr haU) (Subgroup.zpowers_le.mpr hxU)
    have hP4 := hy.four_le_card_sup ha1 hx.1 hx.2
    have hPeq : zpowers a ⊔ zpowers x = Ft := Subgroup.eq_of_le_of_card_ge hP (by omega)
    exact hβaU (hPU (hPeq ▸ hβaFt))
  have hbFt : b' ∉ Ft := fun h => (hUFt b' hbU h).elim hb1 hba
  have htb : τt b' * b' = a := by
    have h1 : τt b' * b' ∈ U := U.mul_mem ((hUt b').mpr hbU) hbU
    have h2 : τt b' * b' ∈ Ft :=
      ⟨Rb.mul_mem ((hτtRb b').mpr hbRb) hbRb, by rw [map_mul, hτt2, V_comm hy.hA1]⟩
    rcases hUFt _ h1 h2 with h | h
    · exfalso
      apply hbFt
      refine ⟨hbRb, ?_⟩
      have h3 : τt b' = b'⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h3]
      exact inv_eq_of_mul_eq_one_right (V_sq hy.hA1 b')
    · exact h
  have hFteq : zpowers a ⊔ zpowers (β a) = Ft := by
    have hP : zpowers a ⊔ zpowers (β a) ≤ Ft :=
      sup_le (Subgroup.zpowers_le.mpr haFt) (Subgroup.zpowers_le.mpr hβaFt)
    have hβa1' : β a ≠ 1 := by
      intro h
      apply ha1
      apply hβinj
      rw [h, map_one]
    have hP4 := hy.four_le_card_sup ha1 hβa1' hβa1
    exact Subgroup.eq_of_le_of_card_ge hP (by omega)
  have hFtcard : Nat.card Ft = 4 := by
    have hβa1' : β a ≠ 1 := by
      intro h
      apply ha1
      apply hβinj
      rw [h, map_one]
    have := hy.four_le_card_sup ha1 hβa1' hβa1
    rw [hFteq] at this
    omega
  set yv := β a * b' with hyv
  have hyfix : τc yv = yv := by
    rw [hτc', hyv, map_mul, map_mul, hβt, hta, hβu, hua]
    have htb' : τt b' = a * b' := by
      calc τt b' = τt b' * b' * b' := by rw [mul_assoc, V_sq hy.hA1, mul_one]
        _ = a * b' := by rw [htb]
    rw [htb', map_mul, hua, hUfix b' hbU, ← mul_assoc, horbit a haRb]
  obtain ⟨va, hva⟩ := haU
  obtain ⟨wa, rfl⟩ := pi_surjective z va
  obtain ⟨vb, hvb⟩ := hbU
  obtain ⟨wb, rfl⟩ := pi_surjective z vb
  set aL := u₁ * wa * u₁⁻¹ * wa with haLdef
  set bL := u₁ * wb * u₁⁻¹ * wb with hbLdef
  have haLR : aL ∈ hy.R := hy.conj_mul_mem_R huC hgR wa.2
  have hbLR : bL ∈ hy.R := hy.conj_mul_mem_R huC hgR wb.2
  have haLpi : pi z ⟨aL, hRJ haLR⟩ = a := by rw [← hva, hψu_pi]
  have hbLpi : pi z ⟨bL, hRJ hbLR⟩ = b' := by rw [← hvb, hψu_pi]
  have hsqt : ∀ w ∈ J z, (t₁ * w * t₁⁻¹ * w) * (t₁ * w * t₁⁻¹ * w) = 1 :=
    fun w hw => hy.sq_conj_mul_t ht₁H hts htC ht2 hw
  have haL2 : aL * aL = 1 := hy.sq_conj_mul_of_conj hbH ht₁H hbu hsqt wa.2
  have hbL2 : bL * bL = 1 := hy.sq_conj_mul_of_conj hbH ht₁H hbu hsqt wb.2
  have haLbL : aL * bL = bL * aL := hy.commute_conj_mul hu₁H hu2 wa.2 wb.2
  set a' := s * aL * s⁻¹ with ha'def
  have ha'R : a' ∈ hy.R := (mem_commutator_conj_iff hy.s_mem rfl aL).mp haLR
  have ha'pi : pi z ⟨a', hRJ ha'R⟩ = β a := by
    rw [← haLpi, hβ, conjVA_pi]
  have ha'2 : a' * a' = 1 := by
    rw [ha'def]
    calc s * aL * s⁻¹ * (s * aL * s⁻¹) = s * (aL * aL) * s⁻¹ := by group
      _ = 1 := by rw [haL2]; group
  set yL := a' * bL with hyLdef
  have hyLR : yL ∈ hy.R := hy.R.mul_mem ha'R hbLR
  have hyLpi : pi z ⟨yL, hRJ hyLR⟩ = yv := by
    have e : (⟨yL, hRJ hyLR⟩ : J z) = ⟨a', hRJ ha'R⟩ * ⟨bL, hRJ hbLR⟩ := rfl
    rw [e, map_mul, ha'pi, hbLpi]
  have ha'J : a' ∈ J z := hRJ ha'R
  have hbLJ : bL ∈ J z := hRJ hbLR
  set d := bL * a' * bL⁻¹ * a'⁻¹ with hd
  have hdz : d ∈ zpowers z := hy.comm_mem hbLJ ha'J
  have hyL2 : yL * yL = d := by
    have hdc : ∀ g ∈ H z, g * d = d * g := fun g hg => hy.commute_of_mem_zpowers_of_mem_H hg hdz
    have h1 : bL * a' = d * (a' * bL) := by rw [hd]; group
    calc yL * yL = a' * (bL * a') * bL := by rw [hyLdef]; group
      _ = a' * (d * (a' * bL)) * bL := by rw [h1]
      _ = (a' * d) * a' * bL * bL := by group
      _ = (d * a') * a' * bL * bL := by rw [hdc a' (J_le_H ha'J)]
      _ = d * (a' * a') * (bL * bL) := by group
      _ = d := by rw [ha'2, hbL2, mul_one, mul_one]
  have hdz' : d = z := by
    rcases hy.mem_zpowers_z_iff.mp hdz with h | h
    · exfalso
      have hbLa' : bL * a' = a' * bL := by
        calc bL * a' = (bL * a' * bL⁻¹ * a'⁻¹) * (a' * bL) := by group
          _ = a' * bL := by rw [← hd, h, one_mul]
      set N₁ := hy.R ⊓ centModZ z t₁ with hN₁
      have hN₁J : N₁ ≤ J z := inf_le_left.trans hRJ
      have hzN₁ : zpowers z ≤ N₁ := by
        rw [Subgroup.zpowers_le]
        refine ⟨hy.zpowers_le_R (Subgroup.mem_zpowers z), mem_centModZ.mpr ⟨J_le_H hy.z_mem_J, ?_⟩⟩
        have e : z * t₁ * z⁻¹ * t₁⁻¹ = 1 := by
          have hc : z * t₁ = t₁ * z := (commute_z_of_mem_H ht₁H).symm
          calc z * t₁ * z⁻¹ * t₁⁻¹ = t₁ * z * z⁻¹ * t₁⁻¹ := by rw [hc]
            _ = 1 := by group
        rw [e]
        exact Subgroup.one_mem _
      have hmemN₁ : ∀ r : J z, (r : G) ∈ hy.R → (pi z r ∈ Ft ↔ (r : G) ∈ N₁) := by
        intro r hrR
        constructor
        · rintro ⟨-, hfix⟩
          refine ⟨hrR, mem_centModZ.mpr ⟨J_le_H r.2, ?_⟩⟩
          have h1 := (conjVA_pi_eq_iff hy.hA1 tH r).mp hfix
          have e : (r : G) * t₁ * (r : G)⁻¹ * t₁⁻¹ = (t₁ * r * t₁⁻¹ * (r : G)⁻¹)⁻¹ := by group
          rw [e]
          exact (zpowers z).inv_mem h1
        · rintro ⟨-, hc⟩
          refine ⟨pi_mem_imV hrR, (conjVA_pi_eq_iff hy.hA1 tH r).mpr ?_⟩
          have h1 := (mem_centModZ.mp hc).2
          have e : t₁ * r * t₁⁻¹ * (r : G)⁻¹ = ((r : G) * t₁ * (r : G)⁻¹ * t₁⁻¹)⁻¹ := by group
          rw [e]
          exact (zpowers z).inv_mem h1
      have himN₁ : imV z N₁ = Ft := by
        ext v
        constructor
        · intro hv
          obtain ⟨r, hrN, rfl⟩ := mem_imV.mp hv
          exact (hmemN₁ r hrN.1).mpr hrN
        · intro hv
          obtain ⟨r, hrR, rfl⟩ := mem_imV.mp hv.1
          exact pi_mem_imV ((hmemN₁ r hrR).mp hv)
      have hN₁card : Nat.card N₁ = 8 := by
        have h := card_imV hy.hA1 hN₁J hzN₁
        rw [himN₁, hFtcard] at h
        omega
      have hN₁ab : ∀ x ∈ N₁, ∀ y ∈ N₁, x * y = y * x := by
        have hrep : ∀ x ∈ N₁, ∃ w ∈ J z, ∃ ε ∈ zpowers z, x = (t₁ * w * t₁⁻¹ * w) * ε := by
          intro x hx
          have hxJ : x ∈ J z := hN₁J hx
          have hxFt : pi z ⟨x, hxJ⟩ ∈ Ft := (hmemN₁ ⟨x, hxJ⟩ hx.1).mpr hx
          obtain ⟨wv, hwv, hxw⟩ := hfreet _ hxFt.1 hxFt.2
          obtain ⟨w, -, rfl⟩ := mem_imV.mp hwv
          refine ⟨w, w.2, (t₁ * w * t₁⁻¹ * w)⁻¹ * x, ?_, by group⟩
          have hJ1 : t₁ * w * t₁⁻¹ * w ∈ J z := (J z).mul_mem (conj_mem_J ht₁H w.2) w.2
          have h1 : pi z ⟨t₁ * w * t₁⁻¹ * w, hJ1⟩ = pi z ⟨x, hxJ⟩ := by
            rw [hxw, hτt, conjVA_pi, ← map_mul]
            rfl
          exact (pi_eq_pi_iff hy.hA1).mp h1
        intro x hx y hy'
        obtain ⟨w, hw, ε, hε, rfl⟩ := hrep x hx
        obtain ⟨w', hw', ε', hε', rfl⟩ := hrep y hy'
        have hcomm := hy.commute_conj_mul ht₁H ht2 hw hw'
        have hH1 : t₁ * w * t₁⁻¹ * w ∈ H z :=
          J_le_H ((J z).mul_mem (conj_mem_J ht₁H hw) hw)
        have hH2 : t₁ * w' * t₁⁻¹ * w' ∈ H z :=
          J_le_H ((J z).mul_mem (conj_mem_J ht₁H hw') hw')
        have hεc := hy.commute_of_mem_zpowers_of_mem_H hH2 hε
        have hε'c := hy.commute_of_mem_zpowers_of_mem_H hH1 hε'
        have hεε' := hy.commute_of_mem_zpowers_of_mem_H (J_le_H (hy.zpowers_le_J hε)) hε'
        calc t₁ * w * t₁⁻¹ * w * ε * (t₁ * w' * t₁⁻¹ * w' * ε')
            = (t₁ * w * t₁⁻¹ * w) * (ε * (t₁ * w' * t₁⁻¹ * w')) * ε' := by group
          _ = (t₁ * w * t₁⁻¹ * w) * ((t₁ * w' * t₁⁻¹ * w') * ε) * ε' := by rw [← hεc]
          _ = ((t₁ * w * t₁⁻¹ * w) * (t₁ * w' * t₁⁻¹ * w')) * (ε * ε') := by group
          _ = ((t₁ * w' * t₁⁻¹ * w') * (t₁ * w * t₁⁻¹ * w)) * (ε' * ε) := by
              rw [hcomm, hεε']
          _ = (t₁ * w' * t₁⁻¹ * w') * ((t₁ * w * t₁⁻¹ * w) * ε') * ε := by group
          _ = (t₁ * w' * t₁⁻¹ * w') * (ε' * (t₁ * w * t₁⁻¹ * w)) * ε := by rw [hε'c]
          _ = t₁ * w' * t₁⁻¹ * w' * ε' * (t₁ * w * t₁⁻¹ * w * ε) := by group
      set Cb := hy.R ⊓ Subgroup.centralizer ({bL} : Set G) with hCb
      have hzCb : zpowers z ≤ Cb := by
        rw [Subgroup.zpowers_le]
        exact ⟨hy.zpowers_le_R (Subgroup.mem_zpowers z),
          Subgroup.mem_centralizer_singleton_iff.mpr (commute_z_of_mem_H (J_le_H hbLJ)).symm⟩
      have hFtCb : Ft ≤ imV z Cb := by
        rw [← hFteq]
        apply sup_le
        · rw [Subgroup.zpowers_le, ← haLpi]
          exact pi_mem_imV ⟨haLR, Subgroup.mem_centralizer_singleton_iff.mpr haLbL⟩
        · rw [Subgroup.zpowers_le, ← ha'pi]
          exact pi_mem_imV ⟨ha'R, Subgroup.mem_centralizer_singleton_iff.mpr hbLa'.symm⟩
      have hN₁b : ∀ x ∈ N₁, x * bL = bL * x := by
        intro x hx
        have hxJ : x ∈ J z := hN₁J hx
        have h1 : pi z ⟨x, hxJ⟩ ∈ imV z Cb := hFtCb ((hmemN₁ ⟨x, hxJ⟩ hx.1).mpr hx)
        have h2 := (pi_mem_imV_iff hy.hA1 hzCb).mp h1
        exact Subgroup.mem_centralizer_singleton_iff.mp h2.2
      have hbLN₁ : bL ∉ N₁ := by
        intro h
        apply hbFt
        rw [← hbLpi]
        exact (hmemN₁ ⟨bL, hbLJ⟩ hbLR).mpr h
      set A := N₁ ⊔ zpowers bL with hA
      have hAR : A ≤ hy.R := sup_le inf_le_left (Subgroup.zpowers_le.mpr hbLR)
      have hn : zpowers bL ≤ Subgroup.normalizer (N₁ : Set G) := by
        apply le_normalizer_of_commute
        intro ρ hρ x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hρ
        exact (Commute.zpow_left (show Commute bL x from (hN₁b x hx).symm) k).eq
      have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
        intro x hx y hy'
        rw [hA, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hx hy'
        obtain ⟨n₁, hn₁, ρ₁, hρ₁, rfl⟩ := hx
        obtain ⟨n₂, hn₂, ρ₂, hρ₂, rfl⟩ := hy'
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hρ₁
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hρ₂
        have h1 : bL ^ i * n₂ = n₂ * bL ^ i :=
          (Commute.zpow_left (show Commute bL n₂ from (hN₁b n₂ hn₂).symm) i).eq
        have h2 : bL ^ j * n₁ = n₁ * bL ^ j :=
          (Commute.zpow_left (show Commute bL n₁ from (hN₁b n₁ hn₁).symm) j).eq
        have h3 : bL ^ i * bL ^ j = bL ^ j * bL ^ i := (Commute.zpow_zpow_self bL i j).eq
        calc n₁ * bL ^ i * (n₂ * bL ^ j) = n₁ * (bL ^ i * n₂) * bL ^ j := by group
          _ = n₁ * (n₂ * bL ^ i) * bL ^ j := by rw [h1]
          _ = (n₁ * n₂) * (bL ^ i * bL ^ j) := by group
          _ = (n₂ * n₁) * (bL ^ j * bL ^ i) := by rw [hN₁ab n₁ hn₁ n₂ hn₂, h3]
          _ = n₂ * (n₁ * bL ^ j) * bL ^ i := by group
          _ = n₂ * (bL ^ j * n₁) * bL ^ i := by rw [h2]
          _ = n₂ * bL ^ j * (n₁ * bL ^ i) := by group
      have hA16 : 16 ≤ Nat.card A := by
        obtain ⟨m, hm⟩ : Nat.card N₁ ∣ Nat.card A := Subgroup.card_dvd_of_le le_sup_left
        rw [hN₁card] at hm
        have hpos : 0 < Nat.card A := Nat.card_pos
        have hm1 : m ≠ 1 := by
          rintro rfl
          apply hbLN₁
          have hNA : N₁ = A := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, hN₁card])
          rw [hNA]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers bL)
        rcases Nat.lt_or_ge m 2 with h | h
        · interval_cases m <;> omega
        · omega
      have := hy.card_le_eight_of_commute_R hAR hAab
      omega
    · exact h
  have hyLfix : τc (pi z ⟨yL, hRJ hyLR⟩) = pi z ⟨yL, hRJ hyLR⟩ := by rw [hyLpi, hyfix]
  obtain ⟨wv, hwv, hyw⟩ := hfreec _ (pi_mem_imV hyLR) hyLfix
  obtain ⟨ω, hωR, rfl⟩ := mem_imV.mp hwv
  have hωJ : (ω : G) ∈ J z := ω.2
  set ω' := c₁ * ω * c₁⁻¹ with hω'
  have hω'J : ω' ∈ J z := conj_mem_J hc₁H hωJ
  have hω'R : ω' ∈ hy.R := (hc₁R ω).mp hωR
  set r := ω' * ω with hr
  have hrR : r ∈ hy.R := hy.R.mul_mem hω'R hωR
  have hrJ : r ∈ J z := hRJ hrR
  have hrpi : pi z ⟨r, hrJ⟩ = pi z ⟨yL, hRJ hyLR⟩ := by
    rw [hyw, hτc, conjVA_pi, ← map_mul]
    rfl
  have hry : yL⁻¹ * r ∈ zpowers z := (pi_eq_pi_iff hy.hA1).mp hrpi.symm
  have hr2 : r * r = z := by
    set ε := yL⁻¹ * r with hεdef
    have hreq : r = yL * ε := by rw [hεdef]; group
    have hεc := hy.commute_of_mem_zpowers_of_mem_H (J_le_H (hRJ hyLR)) hry
    rw [hreq]
    calc yL * ε * (yL * ε) = yL * (ε * yL) * ε := by group
      _ = yL * (yL * ε) * ε := by rw [hεc]
      _ = (yL * yL) * (ε * ε) := by group
      _ = z := by rw [hyL2, hy.mul_self_eq_one_of_mem_zpowers hry, mul_one, hdz']
  have hcomm : c₁ * r * c₁⁻¹ * r⁻¹ = r * r := by
    have hωc : (ω : G) * (c₁ * c₁) = (c₁ * c₁) * ω :=
      hy.commute_of_mem_zpowers_of_mem_H (J_le_H hωJ) hc₁2
    have h1 : c₁ * ω' * c₁⁻¹ = ω := by
      calc c₁ * ω' * c₁⁻¹ = (c₁ * c₁) * ω * (c₁ * c₁)⁻¹ := by rw [hω']; group
        _ = ω * (c₁ * c₁) * (c₁ * c₁)⁻¹ := by rw [hωc]
        _ = ω := by group
    have h2 : c₁ * r * c₁⁻¹ = ω * ω' := by
      calc c₁ * r * c₁⁻¹ = (c₁ * ω' * c₁⁻¹) * (c₁ * ω * c₁⁻¹) := by rw [hr]; group
        _ = ω * ω' := by rw [h1]
    set d' := (ω : G) * ω' * (ω : G)⁻¹ * ω'⁻¹ with hd'
    have hd'z : d' ∈ zpowers z := hy.comm_mem hωJ hω'J
    have hd'c : ∀ g ∈ H z, g * d' = d' * g := fun g hg =>
      hy.commute_of_mem_zpowers_of_mem_H hg hd'z
    have hω2 : (ω : G) * ω ∈ zpowers z := hy.sq_mem hωJ
    have hω'2 : ω' * ω' = (ω : G) * ω := by
      have h := conj_eq_of_mem_zpowers hc₁H hω2
      rw [← h, hω']
      group
    have e1 : (ω : G) * ω' = d' * (ω' * ω) := by rw [hd']; group
    calc c₁ * r * c₁⁻¹ * r⁻¹ = ω * ω' * (ω' * ω)⁻¹ := by rw [h2, hr]
      _ = d' := by rw [hd']; group
      _ = d' * (((ω : G) * ω) * ((ω : G) * ω)) := by
          rw [hy.mul_self_eq_one_of_mem_zpowers hω2, mul_one]
      _ = d' * (ω' * ω') * ((ω : G) * ω) := by rw [hω'2]; group
      _ = ω' * (d' * (ω' * ω)) * ω := by
          rw [show ω' * (d' * (ω' * ω)) * ω = (ω' * d') * ω' * ω * ω by group,
            hd'c ω' (J_le_H hω'J)]
          group
      _ = ω' * ((ω : G) * ω') * ω := by rw [← e1]
      _ = r * r := by rw [hr]; group
  exact ⟨r, hrR, hr2, by rw [hcomm, hr2]⟩

end Hyp

end CFSG.RankThree.GF2n.Parrott.A1Section2Local
