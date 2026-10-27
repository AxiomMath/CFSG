module

public import Mathlib
import CFSG.ClassicalInvolution.AschTight.S1916Alp
import CFSG.Walter.Cited.HuppertAlperin
import CFSG.LocalAnalysis.StandardType.FS81.GoldSharedFr

public section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup
open CFSG.RankTwoShapes

private structure q2cN7n_Data {X : Type} [Group X] (P : Sylow 2 X) (t : X) (A : Subgroup X) :
    Prop where
  htP : t ∈ (P : Subgroup X)
  htc : ∀ x ∈ (P : Subgroup X), x * t = t * x
  hA : A = Subgroup.closure {y | y ∈ (P : Subgroup X) ∧ ∃ m : X, y = m * t * m⁻¹}
  hab : IsMulCommutative A
  hD : ∀ a ∈ A, ∀ d : X, d * t = t * d → d⁻¹ * a * d ∈ (P : Subgroup X) →
      d⁻¹ * a * d ∈ A

private def q2cN7n_tOrbit {X : Type} [Group X] (t : X) (Q : Subgroup X) : Set X :=
  {y | ∃ n ∈ Subgroup.normalizer (Q : Set X), y = n * t * n⁻¹}

private def q2cN7n_C0 {X : Type} [Group X] (t : X) (Q : Subgroup X) : Subgroup X :=
  Subgroup.normalizer (Q : Set X) ⊓ Subgroup.centralizer (q2cN7n_tOrbit t Q)

private def q2cN7n_U0 {X : Type} [Group X] (P : Sylow 2 X) (t : X) (Q : Subgroup X) :
    Subgroup X :=
  ((P : Subgroup X) ⊓ Subgroup.normalizer (Q : Set X)) ⊓ q2cN7n_C0 t Q

private def q2cN7n_Claim {X : Type} [Group X] (P : Sylow 2 X) (t : X) (A : Subgroup X)
    (Q : Subgroup X) : Prop :=
  ∀ n ∈ Subgroup.normalizer (Q : Set X), ∀ x ∈ A ⊓ Q, n⁻¹ * x * n ∈ A

private theorem q2cN7n_mem_A {X : Type} [Group X] {P : Sylow 2 X} {t : X} {A : Subgroup X}
    (D : q2cN7n_Data P t A) {y : X} (hy : y ∈ (P : Subgroup X)) (m : X)
    (hm : y = m * t * m⁻¹) : y ∈ A := by
  rw [D.hA]
  exact subset_closure ⟨hy, m, hm⟩

private theorem q2cN7n_le_P {X : Type} [Group X] {P : Sylow 2 X} {t : X} {A : Subgroup X}
    (D : q2cN7n_Data P t A) : A ≤ (P : Subgroup X) := by
  rw [D.hA]
  exact (Subgroup.closure_le (P : Subgroup X)).mpr fun _ hy => hy.1

private theorem q2cN7n_conj_mem_A {X : Type} [Group X] {P : Sylow 2 X} {t : X} {A : Subgroup X}
    (D : q2cN7n_Data P t A) {g : X}
    (hg : ∀ y : X, y ∈ (P : Subgroup X) → (∃ m : X, y = m * t * m⁻¹) → g⁻¹ * y * g ∈ A) :
    ∀ a ∈ A, g⁻¹ * a * g ∈ A := by
  have key : ∀ x ∈ Subgroup.closure {y | y ∈ (P : Subgroup X) ∧ ∃ m : X, y = m * t * m⁻¹},
      g⁻¹ * x * g ∈ A := by
    intro x hx'
    induction hx' using Subgroup.closure_induction with
    | mem y hy => exact hg y hy.1 hy.2
    | one => simpa using one_mem A
    | mul a b _ _ ha hb =>
      have e : g⁻¹ * (a * b) * g = (g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  intro x hx
  exact key x (D.hA ▸ hx)

private theorem q2cN7n_le_normalizer {X : Type} [Group X] {P : Sylow 2 X} {t : X}
    {A : Subgroup X} (D : q2cN7n_Data P t A) :
    (P : Subgroup X) ≤ Subgroup.normalizer (A : Set X) := by
  intro p hp
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : p * h * p⁻¹ ∈ A := by
      simpa using q2cN7n_conj_mem_A D (g := p⁻¹) (fun y hy hy' => by
        obtain ⟨m, rfl⟩ := hy'
        exact q2cN7n_mem_A D
          (by simpa only [inv_inv] using mul_mem (mul_mem hp hy) (inv_mem hp))
          (p * m) (by group)) h hh
    exact h1
  · intro hh
    have h1 : p⁻¹ * (p * h * p⁻¹) * p ∈ A :=
      q2cN7n_conj_mem_A D (g := p) (fun y hy hy' => by
        obtain ⟨m, rfl⟩ := hy'
        exact q2cN7n_mem_A D (mul_mem (mul_mem (inv_mem hp) hy) hp) (p⁻¹ * m) (by group))
        (p * h * p⁻¹) hh
    simpa [mul_assoc] using h1

private theorem q2cN7n_tOrbit_subset_Q {X : Type} [Group X] {P : Sylow 2 X} {t : X}
    {A : Subgroup X} (D : q2cN7n_Data P t A) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) : q2cN7n_tOrbit t Q ⊆ Q := by
  intro y hy
  obtain ⟨n, hn, rfl⟩ := hy
  have htQ : t ∈ Q :=
    hQ.2.2.1 ⟨mem_centralizer_iff.mpr fun q hq => D.htc q (hQ.1 hq), D.htP⟩
  exact (mem_normalizer_iff.mp hn t).mp htQ

private theorem q2cN7n_tOrbit_subset_A {X : Type} [Group X] {P : Sylow 2 X} {t : X}
    {A : Subgroup X} (D : q2cN7n_Data P t A) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) : q2cN7n_tOrbit t Q ⊆ A := by
  intro y hy
  obtain ⟨n, hn, rfl⟩ := hy
  exact q2cN7n_mem_A D (hQ.1 (q2cN7n_tOrbit_subset_Q D hQ ⟨n, hn, rfl⟩)) n rfl

private theorem q2cN7n_normalizes_C0 {X : Type} [Group X] {t : X} {Q : Subgroup X} :
    ∀ n ∈ Subgroup.normalizer (Q : Set X), ∀ c ∈ q2cN7n_C0 t Q,
      n * c * n⁻¹ ∈ q2cN7n_C0 t Q := by
  intro n hn c hc
  refine mem_inf.mpr ⟨mul_mem (mul_mem hn (mem_inf.mp hc).1) (inv_mem hn),
    mem_centralizer_iff.mpr ?_⟩
  intro y hy
  obtain ⟨m, hm, rfl⟩ := hy
  have h1 := mem_centralizer_iff.mp hc.2 ((n⁻¹ * m) * t * (n⁻¹ * m)⁻¹)
    ⟨n⁻¹ * m, mul_mem (inv_mem hn) hm, rfl⟩
  calc m * t * m⁻¹ * (n * c * n⁻¹)
      = n * ((n⁻¹ * m) * t * (n⁻¹ * m)⁻¹ * c) * n⁻¹ := by group
    _ = n * (c * ((n⁻¹ * m) * t * (n⁻¹ * m)⁻¹)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * (m * t * m⁻¹) := by group

private theorem q2cN7n_C0_commutes_t {X : Type} [Group X] {t : X} {Q : Subgroup X} {c : X}
    (hc : c ∈ q2cN7n_C0 t Q) : c * t = t * c :=
  (mem_centralizer_iff.mp hc.2 t ⟨1, one_mem _, by group⟩).symm

private theorem q2cN7n_C0_normalizes_A_inf_Q {X : Type} [Group X] {P : Sylow 2 X} {t : X}
    {A : Subgroup X} (D : q2cN7n_Data P t A) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) :
    ∀ c ∈ q2cN7n_C0 t Q, ∀ x ∈ A ⊓ Q, c⁻¹ * x * c ∈ A ⊓ Q := by
  intro c hc x hx
  have hcN : c ∈ Subgroup.normalizer (Q : Set X) := (mem_inf.mp hc).1
  have hxQ : c⁻¹ * x * c ∈ Q := (mem_normalizer_iff''.mp hcN x).mp hx.2
  exact ⟨D.hD x hx.1 c (q2cN7n_C0_commutes_t hc) (hQ.1 hxQ), hxQ⟩

private theorem q2cN7n_A_inf_normalizer_le_Q {X : Type} [Group X] {P : Sylow 2 X} {t : X}
    {A : Subgroup X} (D : q2cN7n_Data P t A) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) (hU : q2cN7n_U0 P t Q ≤ Q) :
    A ⊓ Subgroup.normalizer (Q : Set X) ≤ Q := by
  intro w hw
  have hwA : w ∈ A := hw.1
  have hwN : w ∈ Subgroup.normalizer (Q : Set X) := hw.2
  have hwP : w ∈ (P : Subgroup X) := q2cN7n_le_P D hwA
  have hwC : w ∈ q2cN7n_C0 t Q := by
    refine mem_inf.mpr ⟨hwN, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    exact (congrArg Subtype.val (D.hab.is_comm.comm ⟨w, hwA⟩
      ⟨y, q2cN7n_tOrbit_subset_A D hQ hy⟩)).symm
  exact hU ⟨⟨hwP, hwN⟩, hwC⟩

private theorem q2cN7n_A_le_Q {X : Type} [Group X] [Finite X] {P : Sylow 2 X} {t : X}
    {A : Subgroup X}
    (D : q2cN7n_Data P t A) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) (hU : q2cN7n_U0 P t Q ≤ Q) :
    A ≤ Q := by
  by_contra hAQ
  have hQP : Q ≤ (P : Subgroup X) := hQ.1
  have hsupP : Q ⊔ A ≤ (P : Subgroup X) := sup_le hQP (q2cN7n_le_P D)
  have h2 : IsPGroup 2 (Q ⊔ A : Subgroup X) := P.isPGroup'.to_le hsupP
  have hne : Q ≠ Q ⊔ A := fun heq => hAQ (heq.symm ▸ le_sup_right)
  obtain ⟨x, hxQW, hxN, hxQ⟩ :=
    CFSG.Walter.Huppert.exists_mem_normalizer_not_mem h2 le_sup_left hne
  have hQA : Q ≤ Subgroup.normalizer (A : Set X) := hQP.trans (q2cN7n_le_normalizer D)
  have hx' : x ∈ ((Q ⊔ A : Subgroup X) : Set X) := hxQW
  rw [coe_mul_of_left_le_normalizer_right Q A hQA] at hx'
  obtain ⟨q, hq, a, ha, rfl⟩ := hx'
  have haN : a ∈ Subgroup.normalizer (Q : Set X) := by
    have e : a = q⁻¹ * (q * a) := by group
    rw [e]
    exact mul_mem (inv_mem (le_normalizer hq)) hxN
  have haQ : a ∈ Q := q2cN7n_A_inf_normalizer_le_Q D hQ hU ⟨ha, haN⟩
  exact hxQ (mul_mem hq haQ)

private theorem q2cN7n_claim_of_le {X : Type} [Group X] [Finite X] {P : Sylow 2 X} {t : X}
    {A : Subgroup X} (D : q2cN7n_Data P t A) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) (hU : q2cN7n_U0 P t Q ≤ Q) :
    q2cN7n_Claim P t A Q := by
  have hAQ := q2cN7n_A_le_Q D hQ hU
  intro n hn x hx
  refine q2cN7n_conj_mem_A D (g := n) (fun y hyP hy' => ?_) x hx.1
  obtain ⟨m, rfl⟩ := hy'
  have hyQ : m * t * m⁻¹ ∈ Q := hAQ (q2cN7n_mem_A D hyP m rfl)
  have h1 : n⁻¹ * (m * t * m⁻¹) * n ∈ Q :=
    (mem_normalizer_iff''.mp hn (m * t * m⁻¹)).mp hyQ
  exact q2cN7n_mem_A D (hQ.1 h1) (n⁻¹ * m) (by group)

private theorem q2cN7n_decomposition_step {X : Type} [Group X] [Finite X] {P : Sylow 2 X}
    {t : X} {A : Subgroup X} (D : q2cN7n_Data P t A) {Q₀ R : Subgroup X}
    (hRP : R ≤ (P : Subgroup X)) (hcard : Nat.card Q₀ < Nat.card R)
    (ih : ∀ Q' : Subgroup X, IsAlperinSubgroup 2 (P : Subgroup X) Q' →
      Nat.card Q₀ < Nat.card Q' → q2cN7n_Claim P t A Q')
    {c : X} (hc : AlperinDecomposition 2 (P : Subgroup X) R c) :
    ∀ y ∈ A ⊓ R, c⁻¹ * y * c ∈ A := by
  induction hc with
  | one => intro y hy; simpa using hy.1
  | @step c n Q' _ hQ' hRQ' hn ihc =>
    intro y hy
    have hy'A : c⁻¹ * y * c ∈ A := ihc y hy
    have hy'Q : c⁻¹ * y * c ∈ Q' := by
      have := hRQ' (mem_map_of_mem (MulAut.conj c⁻¹).toMonoidHom hy.2)
      simpa using this
    have hcard' : Nat.card Q₀ < Nat.card Q' := by
      have h1 : Nat.card R = Nat.card (R.map (MulAut.conj c⁻¹).toMonoidHom) :=
        (card_map_of_injective (MulAut.conj c⁻¹).injective).symm
      have h2 : Nat.card (R.map (MulAut.conj c⁻¹).toMonoidHom) ≤ Nat.card Q' :=
        card_le_of_le hRQ'
      omega
    have hstep := ih Q' hQ' hcard' n hn (c⁻¹ * y * c) ⟨hy'A, hy'Q⟩
    have e : (c * n)⁻¹ * y * (c * n) = n⁻¹ * (c⁻¹ * y * c) * n := by group
    rw [e]
    exact hstep

private theorem q2cN7n_claim_of_not_le {X : Type} [Group X] [Finite X] {P : Sylow 2 X} {t : X}
    {A : Subgroup X} (D : q2cN7n_Data P t A) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) (hU : ¬ q2cN7n_U0 P t Q ≤ Q)
    (ih : ∀ Q' : Subgroup X, IsAlperinSubgroup 2 (P : Subgroup X) Q' →
      Nat.card Q < Nat.card Q' → q2cN7n_Claim P t A Q') :
    q2cN7n_Claim P t A Q := by
  have hidx : Nat.Coprime 2
      (((P : Subgroup X) ⊓ Subgroup.normalizer (Q : Set X)).subgroupOf
        (Subgroup.normalizer (Q : Set X))).index := hQ.2.1
  have hfac := exists_mul_normalizer_inf_sylow (N := Subgroup.normalizer (Q : Set X))
    (C := q2cN7n_C0 t Q) (S₀ := (P : Subgroup X) ⊓ Subgroup.normalizer (Q : Set X))
    inf_le_left q2cN7n_normalizes_C0 inf_le_right P.isPGroup'.to_inf_left hidx
  intro n hn x hx
  obtain ⟨c, hcC0, m, hmN, hnm, hmU0⟩ := hfac n hn
  rw [hnm]
  have hRle : Q ⊔ q2cN7n_U0 P t Q ≤ (P : Subgroup X) :=
    sup_le hQ.1 (inf_le_left.trans inf_le_left)
  have hU0norm : m ∈ Subgroup.normalizer ((q2cN7n_U0 P t Q : Subgroup X) : Set X) := hmU0
  have hmR : m ∈ Subgroup.normalizer ((Q ⊔ q2cN7n_U0 P t Q : Subgroup X) : Set X) :=
    CFSG.Walter.Huppert.mem_normalizer_sup hmN hU0norm
  have hmapR : (Q ⊔ q2cN7n_U0 P t Q).map (MulAut.conj m⁻¹).toMonoidHom =
      (Q ⊔ q2cN7n_U0 P t Q) :=
    mem_normalizer_iff_map_conj_eq.mp (inv_mem hmR)
  have hgm : (Q ⊔ q2cN7n_U0 P t Q).map (MulAut.conj m⁻¹).toMonoidHom ≤
      (P : Subgroup X) := hmapR.le.trans hRle
  obtain ⟨c', hc', hc'eq⟩ :=
    CFSG.RankTwoShapes.alperin_centric_radical_fusion P hRle hgm
  have hQR : Q < Q ⊔ q2cN7n_U0 P t Q :=
    lt_of_le_of_ne le_sup_left fun heq => hU (le_trans le_sup_right (le_of_eq heq.symm))
  have hcard : Nat.card Q < Nat.card (Q ⊔ q2cN7n_U0 P t Q : Subgroup X) :=
    Subgroup.card_lt_of_lt hQR
  have hx' : c⁻¹ * x * c ∈ A ⊓ Q := q2cN7n_C0_normalizes_A_inf_Q D hQ c hcC0 x hx
  have hx'R : c⁻¹ * x * c ∈ A ⊓ (Q ⊔ q2cN7n_U0 P t Q) :=
    ⟨hx'.1, (le_sup_left : Q ≤ Q ⊔ q2cN7n_U0 P t Q) hx'.2⟩
  have hmx' : m⁻¹ * (c⁻¹ * x * c) * m ∈ A := by
    rw [← hc'eq (c⁻¹ * x * c) hx'R.2]
    exact q2cN7n_decomposition_step D hRle hcard ih hc' (c⁻¹ * x * c) hx'R
  have hcm : (c * m)⁻¹ * x * (c * m) = m⁻¹ * (c⁻¹ * x * c) * m := by group
  rw [hcm]
  exact hmx'

private theorem q2cN7n_claim_of_isAlperinSubgroup {X : Type} [Group X] [Finite X] {P : Sylow 2 X}
    {t : X} {A : Subgroup X} (D : q2cN7n_Data P t A) {Q : Subgroup X}
    (hQ : IsAlperinSubgroup 2 (P : Subgroup X) Q) : q2cN7n_Claim P t A Q := by
  suffices h : ∀ k : ℕ, ∀ Q : Subgroup X, IsAlperinSubgroup 2 (P : Subgroup X) Q →
      Nat.card (P : Subgroup X) - Nat.card Q = k → q2cN7n_Claim P t A Q by
    exact h _ Q hQ rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro Q hQ hk
    by_cases hU : q2cN7n_U0 P t Q ≤ Q
    · exact q2cN7n_claim_of_le D hQ hU
    · refine q2cN7n_claim_of_not_le D hQ hU fun Q' hQ' hlt => ?_
      have hQ'P : Nat.card Q' ≤ Nat.card (P : Subgroup X) := card_le_of_le hQ'.1
      have hQP : Nat.card Q ≤ Nat.card (P : Subgroup X) := card_le_of_le hQ.1
      have hk' : Nat.card (P : Subgroup X) - Nat.card Q' < k := by
        rw [← hk]
        omega
      exact ih (Nat.card (P : Subgroup X) - Nat.card Q') hk' Q' hQ' rfl

theorem stronglyClosed_of_centralizer {X : Type} [Group X] [Finite X] (P : Sylow 2 X) {t : X}
    (htP : t ∈ (P : Subgroup X)) (htc : ∀ x ∈ (P : Subgroup X), x * t = t * x) (A : Subgroup X)
    (hA : A = Subgroup.closure {y | y ∈ (P : Subgroup X) ∧ ∃ m : X, y = m * t * m⁻¹})
    (hab : IsMulCommutative A)
    (hD : ∀ a ∈ A, ∀ d : X, d * t = t * d → d⁻¹ * a * d ∈ (P : Subgroup X) →
      d⁻¹ * a * d ∈ A) :
    ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (P : Subgroup X) → g⁻¹ * a * g ∈ A := by
  let D : q2cN7n_Data P t A := ⟨htP, htc, hA, hab, hD⟩
  exact CFSG.ClassicalInvolution.Disconnected.AschTight.S1916.stronglyClosed_of_alperin P
    (q2cN7n_le_P D)
    (fun Q hQ n hn x hx => q2cN7n_claim_of_isAlperinSubgroup D hQ n hn x hx)

end CFSG.StandardType.FrameRoute.FS81

end
