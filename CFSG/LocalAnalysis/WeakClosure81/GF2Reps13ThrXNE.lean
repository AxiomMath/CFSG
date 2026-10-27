module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXND
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

variable {A Q O : Subgroup (MulAut W)} {t : MulAut W}

private theorem w16n_zpow_eq_one_or_self_of_sq_eq_one {G : Type*} [Group G] {t : G}
    (ht : t * t = 1) (k : ℤ) : t ^ k = 1 ∨ t ^ k = t := by
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two, ht]
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem w16n_conj_commutatorElement_eq_inv' {G : Type*} [Group G] {t : G}
    (ht : orderOf t = 2) (e : G) : t * ⁅e, t⁆ * t⁻¹ = ⁅e, t⁆⁻¹ := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left htt
  have key : (e * t * e⁻¹ * t) * (t * e * t * e⁻¹) = 1 := by
    calc (e * t * e⁻¹ * t) * (t * e * t * e⁻¹)
        = e * t * e⁻¹ * (t * t) * e * t * e⁻¹ := by group
      _ = e * t * e⁻¹ * e * t * e⁻¹ := by rw [htt, mul_one]
      _ = e * (t * t) * e⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  rw [commutatorElement_def, hti]
  calc t * (e * t * e⁻¹ * t) * t = t * e * t * e⁻¹ * (t * t) := by group
    _ = t * e * t * e⁻¹ := by rw [htt, mul_one]
    _ = (e * t * e⁻¹ * t)⁻¹ := (inv_eq_of_mul_eq_one_right key).symm

private theorem w16n_abelian_conj_eq_inv_of_commutator_eq_self {G : Type*} [Group G]
    {P : Subgroup G} {t : G} (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (ht2 : orderOf t = 2) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hc : ⁅P, Subgroup.zpowers t⁆ = P) :
    ∀ x ∈ P, t * x * t⁻¹ = x⁻¹ := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  let J : Subgroup G :=
    { carrier := {x | x ∈ P ∧ t * x * t⁻¹ = x⁻¹}
      one_mem' := ⟨P.one_mem, by rw [mul_one, inv_one, mul_inv_cancel]⟩
      mul_mem' := by
        rintro x y ⟨hxP, hx⟩ ⟨hyP, hy⟩
        refine ⟨P.mul_mem hxP hyP, ?_⟩
        have hxy : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ :=
          hcomm x⁻¹ (P.inv_mem hxP) y⁻¹ (P.inv_mem hyP)
        calc t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [hx, hy]
          _ = (x * y)⁻¹ := by rw [mul_inv_rev, hxy]
      inv_mem' := by
        rintro x ⟨hxP, hx⟩
        refine ⟨P.inv_mem hxP, ?_⟩
        calc t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
          _ = (x⁻¹)⁻¹ := by rw [hx] }
  have hPleJ : P ≤ J := by
    rw [← hc]
    refine Subgroup.commutator_le.mpr ?_
    intro x hx s hs
    rcases Subgroup.mem_zpowers_iff.mp hs with ⟨k, rfl⟩
    rcases w16n_zpow_eq_one_or_self_of_sq_eq_one htt k with hk | hk
    · rw [hk, commutatorElement_one_right]
      exact J.one_mem
    · rw [hk]
      refine ⟨?_, w16n_conj_commutatorElement_eq_inv' ht2 x⟩
      rw [commutatorElement_def]
      simpa only [mul_assoc] using P.mul_mem hx (hn x⁻¹ (P.inv_mem hx))
  intro x hx
  exact (hPleJ hx).2

private theorem w16n_isElemAbelian_omegaOne_of_commute {p : ℕ} {P : Subgroup (MulAut W)}
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) : IsElemAbelian p (omegaOne p P) := by
  rw [omegaOne]
  refine IsElemAbelian.closure_of_commute ?_ ?_
  · intro a ha b hb
    exact hcomm a ha.1 b hb.1
  · intro a ha
    exact ha.2

private theorem w16n_conj_generators_commute {A Q : Subgroup (MulAut W)}
    (hcomm : ∀ g ∈ A, ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    ∀ g ∈ A, ∀ y ∈ Q, ∀ g' ∈ A, ∀ y' ∈ Q,
      (g * y * g⁻¹) * (g' * y' * g'⁻¹) = (g' * y' * g'⁻¹) * (g * y * g⁻¹) := by
  intro g hg y hy g' hg' y' hy'
  have hh : g'⁻¹ * g ∈ A := A.mul_mem (A.inv_mem hg') hg
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm (g'⁻¹ * g) hh)
  have hmem : (MulAut.conj (g'⁻¹ * g)) y ∈ Q.map (MulAut.conj (g'⁻¹ * g)).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj (g'⁻¹ * g)).toMonoidHom hy
  have hcy : (MulAut.conj (g'⁻¹ * g)) y * y' = y' * (MulAut.conj (g'⁻¹ * g)) y :=
    Subgroup.mem_centralizer_iff.mp (hle hy') ((MulAut.conj (g'⁻¹ * g)) y) hmem
  have key : g'⁻¹ * (g * y * g⁻¹) * g' = (MulAut.conj (g'⁻¹ * g)) y := by
    rw [MulAut.conj_apply]; group
  have hcy' : (g'⁻¹ * (g * y * g⁻¹) * g') * y' =
      y' * (g'⁻¹ * (g * y * g⁻¹) * g') := by
    rw [key]; exact hcy
  calc (g * y * g⁻¹) * (g' * y' * g'⁻¹)
      = g' * ((g'⁻¹ * (g * y * g⁻¹) * g') * y') * g'⁻¹ := by group
    _ = g' * (y' * (g'⁻¹ * (g * y * g⁻¹) * g')) * g'⁻¹ := by rw [hcy']
    _ = (g' * y' * g'⁻¹) * (g * y * g⁻¹) := by group

private theorem w16n_conjClosure_commute {A Q : Subgroup (MulAut W)}
    (hQe : IsElemAbelian 3 Q)
    (hcomm : ∀ g ∈ A, ⁅Q, Q.map (MulAut.conj g).toMonoidHom⁆ = ⊥) :
    ∀ a ∈ conjClosure A Q, ∀ b ∈ conjClosure A Q, a * b = b * a := by
  have hpair := w16n_conj_generators_commute (A := A) (Q := Q) hcomm
  have hXe : IsElemAbelian 3 (conjClosure A Q) := by
    rw [conjClosure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro x ⟨g, hg, y, hy, rfl⟩ z ⟨g', hg', y', hy', rfl⟩
      exact hpair g hg y hy g' hg' y' hy'
    · rintro x ⟨g, hg, y, hy, rfl⟩
      have h : (MulAut.conj g) y ^ 3 = 1 := by
        rw [← map_pow (MulAut.conj g) y 3, hQe.2 y hy, map_one]
      simpa only [MulAut.conj_apply] using h
  intro a ha b hb
  exact hXe.comm ha hb

theorem w16n_main (h : HNon A Q O t) (hOp : O ≤ pCoreOf 3 A) :
    ∃ L : Subgroup (MulAut W), L ≤ pCoreOf 3 A ∧ Conc4_133 A t L ∧ IsPOnePlusTwo 3 ↥L ∧
      rk ↥(commSub ⊤ L) = 6 ∧ ∀ n ∈ O, L.map (MulAut.conj n).toMonoidHom = L := by
  obtain ⟨K, hKO, hK3, hKrk, hKt, hKn, hKind⟩ := w16n_K h
  exact ⟨K, hKO.trans hOp,
    ⟨3, Nat.prime_three, hKO.trans hOp, hKt, hKind,
      Or.inr (Or.inr (Or.inl ⟨hK3, hKrk⟩))⟩, hK3, hKrk, hKn⟩

theorem w16n_hnon (h : Cfg133 A t 3)
    (hab : ∀ x ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, ∀ y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆,
      x * y = y * x)
    (hX : ∃ a ∈ conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆),
      ∃ b ∈ conjClosure A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆), a * b ≠ b * a) :
    HNon A (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆) (pCoreOf 3 A) t := by
  obtain ⟨hPO, hPgrp, hPne, htP, hcP, hOnP⟩ := s13_P_facts (p := 3) h
  have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have htord : orderOf t = 2 := orderOf_eq_prime h.ht2 h.ht1
  have hQleP : omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ ≤
      ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ := by
    rw [omegaOne, Subgroup.closure_le]
    rintro x ⟨hxP, -⟩
    exact hxP
  have hQe : IsElemAbelian 3 (omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆) :=
    w16n_isElemAbelian_omegaOne_of_commute hab
  have hQO : omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ ≤ pCoreOf 3 A :=
    hQleP.trans hPO
  have hQN : ∀ n ∈ pCoreOf 3 A, ∀ q ∈ omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆,
      n * q * n⁻¹ ∈ omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ := by
    intro n hn q hq
    rw [omegaOne] at hq
    rw [omegaOne]
    refine Subgroup.closure_induction (p := fun x _ => n * x * n⁻¹ ∈
      Subgroup.closure {y : MulAut W | y ∈ ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ ∧ y ^ 3 = 1})
      ?_ ?_ ?_ ?_ hq
    · intro x hx
      refine Subgroup.subset_closure ⟨hOnP n hn x hx.1, ?_⟩
      have h3 : ((MulAut.conj n) x) ^ 3 = 1 := by
        rw [← map_pow (MulAut.conj n) x 3, hx.2, map_one]
      simpa only [MulAut.conj_apply] using h3
    · rw [show n * 1 * n⁻¹ = 1 by group]
      exact Subgroup.one_mem _
    · intro x y hx hy ihx ihy
      rw [show n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) by group]
      exact Subgroup.mul_mem _ ihx ihy
    · intro x hx ihx
      rw [show n * x⁻¹ * n⁻¹ = (n * x * n⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ihx
  have hQ1 : omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ ≠ ⊥ := by
    intro hbot
    have hcne : ⁅⁅pCoreOf 3 A, Subgroup.zpowers t⁆, Subgroup.zpowers t⁆ ≠ ⊥ := by
      rw [hcP]; exact hPne
    obtain ⟨x, hxP, hxord, -⟩ :=
      exists_inverted_orderOf_eq_prime htt (p := 3) (by norm_num) hPgrp htP hcne
    have hxQ : x ∈ omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆ := by
      rw [omegaOne]
      exact Subgroup.subset_closure ⟨hxP, by rw [← hxord]; exact pow_orderOf_eq_one x⟩
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hxord
      exact (by norm_num : (1 : ℕ) ≠ 3) hxord
    exact hx1 (Subgroup.mem_bot.mp (hbot ▸ hxQ))
  have hQinv : ∀ q ∈ omegaOne 3 ⁅pCoreOf 3 A, Subgroup.zpowers t⁆, t * q * t⁻¹ = q⁻¹ :=
    fun q hq => w16n_abelian_conj_eq_inv_of_commutator_eq_self hab htord htP hcP q (hQleP hq)
  refine ⟨h.hW, h.htA, h.ht2, h.ht1, h.hrk, (s13_pCore_facts A 3).2.2,
    (s13_pCore_facts A 3).2.1, (s13_pCore_facts A 3).1, hQe, hQO, hQN, hQ1, hQinv, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, hne⟩ := hX
  exact hne (w16n_conjClosure_commute hQe hcon a ha b hb)

end CFSG.LocalAnalysis.WeakClosure81
