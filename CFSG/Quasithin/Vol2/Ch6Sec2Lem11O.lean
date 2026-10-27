module

public import CFSG.Quasithin.Vol2.Ch6S5Parab

public section

namespace CFSG.Quasithin.H13

open Equiv

abbrev Mat4Ch611 := Matrix (Fin 4) (Fin 4) (ZMod 2)

@[expose] def matDCh611 : Mat4Ch611 := !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

@[expose] def vYCh611 (a b c d : ZMod 2) : Mat4Ch611 :=
  !![1, 0, a, b; 0, 1, c, d; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def vhatCh611 : Fin 4 → Mat4Ch611 :=
  ![1, vYCh611 1 0 1 1, vYCh611 0 1 1 0, vYCh611 1 1 0 1]

@[expose] def matT1Ch611 (β : Fin 3 → ZMod 2) : Mat4Ch611 :=
  !![1, β 0, β 1, β 2; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

@[expose] def matH0Ch611 (γ : Fin 3 → ZMod 2) : Mat4Ch611 :=
  !![1, γ 0, γ 1, γ 2; 0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0]

@[expose] def uniCh611 (x : Fin 6 → ZMod 2) : Mat4Ch611 :=
  !![1, x 0, x 1, x 2; 0, 1, x 3, x 4; 0, 0, 1, x 5; 0, 0, 0, 1]

@[expose] def SameModCh611 (A X : Mat4Ch611) : Prop := A 1 = X 1 ∧ A 2 = X 2 ∧ A 3 = X 3

instance (A X : Mat4Ch611) : Decidable (SameModCh611 A X) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem matDCh611_pow : matDCh611 * (matDCh611 * matDCh611) = 1 := by decide

theorem vhatCh611_sq : ∀ i, vhatCh611 i * vhatCh611 i = 1 := by decide

theorem vYCh611_mem_of_orbit : ∀ a b c d : ZMod 2,
    vYCh611 a b c d * (matDCh611 * vYCh611 a b c d * (matDCh611 * matDCh611)) *
      (matDCh611 * matDCh611 * vYCh611 a b c d * matDCh611) = 1 →
    ∃ i, vYCh611 a b c d = vhatCh611 i := by decide

theorem vhatCh611_orbit : ∀ i j : Fin 4, i ≠ 0 → j ≠ 0 →
    vhatCh611 j = vhatCh611 i ∨ vhatCh611 j = matDCh611 * vhatCh611 i * (matDCh611 * matDCh611) ∨
      vhatCh611 j = matDCh611 * matDCh611 * vhatCh611 i * matDCh611 := by decide

theorem uniCh611_sameMod_vhat : ∀ x : Fin 6 → ZMod 2, x 5 = 0 →
    ∃ i, SameModCh611 (uniCh611 x) (vhatCh611 i) := by decide

theorem uniCh611_eq_vhat_mul : ∀ x : Fin 6 → ZMod 2, x 5 = 1 →
    ∃ i β, vhatCh611 i * uniCh611 x = matT1Ch611 β := by decide

theorem uniCh611_sameMod_T : ∀ (x : Fin 6 → ZMod 2) (β : Fin 3 → ZMod 2), ∃ i, ∃ s : Bool,
    SameModCh611 (uniCh611 x) (vhatCh611 i * (if s then matT1Ch611 β else 1)) := by decide

theorem rels_sameMod_ch611 : ∀ β γ : Fin 3 → ZMod 2,
    SameModCh611 (matT1Ch611 β * matT1Ch611 β) 1 ∧ SameModCh611 (matH0Ch611 γ * matH0Ch611 γ) 1 ∧
    SameModCh611 (vhatCh611 1 * matT1Ch611 β * vhatCh611 2 * matT1Ch611 β) 1 ∧
    SameModCh611 (vhatCh611 1 * matH0Ch611 γ * vhatCh611 1 * matH0Ch611 γ * vhatCh611 1 *
      matH0Ch611 γ) 1 := by decide

@[expose] def GoodCh611 (β γ : Fin 3 → ZMod 2) : Prop :=
  β 0 = 1 ∧ β 1 = 0 ∧ ((γ 0 = 0 ∧ γ 1 = 1 ∧ γ 2 = 0) ∨ (γ 0 = 1 ∧ γ 1 = 1 ∧ γ 2 = 1))

instance (β γ : Fin 3 → ZMod 2) : Decidable (GoodCh611 β γ) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem good_of_rels_ch611 : ∀ β γ : Fin 3 → ZMod 2, matT1Ch611 β * matT1Ch611 β = 1 →
    matH0Ch611 γ * matH0Ch611 γ = 1 →
    vhatCh611 1 * matT1Ch611 β * vhatCh611 2 * matT1Ch611 β = 1 →
    vhatCh611 1 * matH0Ch611 γ * vhatCh611 1 * matH0Ch611 γ * vhatCh611 1 * matH0Ch611 γ = 1 →
    GoodCh611 β γ := by decide

theorem goodCh611_cases {β γ : Fin 3 → ZMod 2} (h : GoodCh611 β γ) :
    (β = ![1, 0, 0] ∨ β = ![1, 0, 1]) ∧ (γ = ![0, 1, 0] ∨ γ = ![1, 1, 1]) := by
  obtain ⟨h0, h1, h2⟩ := h
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  constructor
  · rcases hz (β 2) with h3 | h3
    · left; funext i; fin_cases i <;> simp [h0, h1, h3]
    · right; funext i; fin_cases i <;> simp [h0, h1, h3]
  · rcases h2 with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · left; funext i; fin_cases i <;> simp [a, b, c]
    · right; funext i; fin_cases i <;> simp [a, b, c]

@[expose] def LineLeCh611 (p q p' q' : Fin 4 → ZMod 2) : Prop :=
  ∀ α β : ZMod 2, ∃ α' β' : ZMod 2, α • p + β • q = α' • p' + β' • q'

instance (p q p' q' : Fin 4 → ZMod 2) : Decidable (LineLeCh611 p q p' q') :=
  inferInstanceAs (Decidable (∀ _ _ : ZMod 2, _))

@[expose] def LineEqCh611 (p q p' q' : Fin 4 → ZMod 2) : Prop :=
  LineLeCh611 p q p' q' ∧ LineLeCh611 p' q' p q

instance (p q p' q' : Fin 4 → ZMod 2) : Decidable (LineEqCh611 p q p' q') :=
  inferInstanceAs (Decidable (_ ∧ _))

@[expose] def wIdxCh611 (β γ : Fin 3 → ZMod 2) : Fin 4 :=
  if β 2 = 0 then (if γ 0 = 0 then 1 else 3) else (if γ 0 = 0 then 0 else 2)

@[expose] def omPCh611 (β γ : Fin 3 → ZMod 2) : Fin 5 → (Fin 4 → ZMod 2) :=
  if β 2 = 0 then
    (if γ 0 = 0 then ![![0, 0, 0, 1], ![0, 1, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 0], ![0, 1, 0, 0]]
     else ![![0, 1, 1, 0], ![0, 1, 1, 1], ![0, 1, 0, 1], ![0, 0, 0, 1], ![0, 1, 0, 0]])
  else
    (if γ 0 = 0 then ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 1, 0], ![0, 0, 1, 1], ![0, 1, 0, 0]]
     else ![![0, 1, 1, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 0, 1], ![0, 1, 0, 0]])

@[expose] def omQCh611 (β γ : Fin 3 → ZMod 2) : Fin 5 → (Fin 4 → ZMod 2) :=
  if β 2 = 0 then
    (if γ 0 = 0 then ![![0, 1, 1, 0], ![1, 0, 1, 0], ![1, 1, 0, 1], ![1, 0, 0, 1], ![1, 0, 0, 0]]
     else ![![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1], ![0, 0, 1, 0], ![1, 0, 0, 0]])
  else
    (if γ 0 = 0 then ![![1, 1, 1, 0], ![0, 1, 0, 1], ![1, 0, 1, 1], ![1, 0, 0, 1], ![1, 0, 0, 0]]
     else ![![1, 0, 0, 1], ![1, 1, 0, 1], ![0, 1, 0, 1], ![1, 0, 1, 0], ![1, 0, 0, 0]])

@[expose] def kIdxCh611 (β γ : Fin 3 → ZMod 2) : Fin 4 → Fin 5 :=
  if β 2 = 0 then (if γ 0 = 0 then ![4, 4, 3, 0] else ![4, 4, 3, 3])
  else (if γ 0 = 0 then ![4, 4, 1, 0] else ![4, 4, 1, 3])

@[expose] def formBCh611 (β _γ : Fin 3 → ZMod 2) : Mat4Ch611 :=
  if β 2 = 0 then !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  else !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

@[expose] def matYCh611 (β γ : Fin 3 → ZMod 2) : Mat4Ch611 :=
  matH0Ch611 γ * vhatCh611 (wIdxCh611 β γ) * matDCh611 * matH0Ch611 γ

@[expose] def matYinvCh611 (β γ : Fin 3 → ZMod 2) : Mat4Ch611 :=
  matH0Ch611 γ * (matDCh611 * matDCh611) * vhatCh611 (wIdxCh611 β γ) * matH0Ch611 γ

@[expose] def kleinCh611 : Fin 4 → Perm (Fin 5) :=
  ![1, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2, swap 0 2 * swap 1 3]

@[expose] def candACh611 (β γ : Fin 3 → ZMod 2) (c : Fin 4 → ZMod 2 × ZMod 2) : Mat4Ch611 :=
  Matrix.of fun i j =>
    ((c j).1 • omPCh611 β γ (kIdxCh611 β γ j) + (c j).2 • omQCh611 β γ (kIdxCh611 β γ j)) i

@[expose] def CaseFactsCh611 (β γ : Fin 3 → ZMod 2) : Prop :=
  (∀ k i, ∃ j, LineEqCh611 ((vhatCh611 k).mulVec (omPCh611 β γ i))
    ((vhatCh611 k).mulVec (omQCh611 β γ i)) (omPCh611 β γ j) (omQCh611 β γ j)) ∧
  (∀ k i, ∃ j, LineEqCh611 ((vhatCh611 k * matT1Ch611 β).mulVec (omPCh611 β γ i))
    ((vhatCh611 k * matT1Ch611 β).mulVec (omQCh611 β γ i)) (omPCh611 β γ j) (omQCh611 β γ j)) ∧
  (∀ i, ∃ j, LineEqCh611 ((matYCh611 β γ).mulVec (omPCh611 β γ i))
    ((matYCh611 β γ).mulVec (omQCh611 β γ i)) (omPCh611 β γ j) (omQCh611 β γ j)) ∧
  (∀ i j, i ≠ j → ∃ a b : ZMod 2, ∀ a' b' : ZMod 2,
    a • omPCh611 β γ i + b • omQCh611 β γ i ≠ a' • omPCh611 β γ j + b' • omQCh611 β γ j) ∧
  (∀ i, LineEqCh611 ((matT1Ch611 β).mulVec (omPCh611 β γ i))
    ((matT1Ch611 β).mulVec (omQCh611 β γ i)) (omPCh611 β γ (swap 0 2 i))
    (omQCh611 β γ (swap 0 2 i))) ∧
  (∀ i, LineEqCh611 ((vhatCh611 2 * matT1Ch611 β).mulVec (omPCh611 β γ i))
    ((vhatCh611 2 * matT1Ch611 β).mulVec (omQCh611 β γ i)) (omPCh611 β γ (L619.r4 i))
    (omQCh611 β γ (L619.r4 i))) ∧
  LineEqCh611 ((matYCh611 β γ).mulVec (omPCh611 β γ 4)) ((matYCh611 β γ).mulVec (omQCh611 β γ 4))
    (omPCh611 β γ 0) (omQCh611 β γ 0) ∧
  (∀ k i, LineEqCh611 ((vhatCh611 k).mulVec (omPCh611 β γ i))
    ((vhatCh611 k).mulVec (omQCh611 β γ i)) (omPCh611 β γ (kleinCh611 k i))
    (omQCh611 β γ (kleinCh611 k i))) ∧
  (∀ k, Matrix.transpose (vhatCh611 k) * formBCh611 β γ * vhatCh611 k = formBCh611 β γ) ∧
  (∀ k, Matrix.transpose (vhatCh611 k * matT1Ch611 β) * formBCh611 β γ *
    (vhatCh611 k * matT1Ch611 β) = formBCh611 β γ) ∧
  Matrix.transpose (matYCh611 β γ) * formBCh611 β γ * matYCh611 β γ = formBCh611 β γ ∧
  (∀ j : Fin 4, ∃ a b : ZMod 2, (Pi.single j 1 : Fin 4 → ZMod 2) =
    a • omPCh611 β γ (kIdxCh611 β γ j) + b • omQCh611 β γ (kIdxCh611 β γ j)) ∧
  (∃ k, ∀ k', matYCh611 β γ * vhatCh611 k * matYinvCh611 β γ ≠ vhatCh611 k') ∧
  matYCh611 β γ * matYinvCh611 β γ = 1 ∧
  omPCh611 β γ 4 = ![0, 1, 0, 0] ∧ omQCh611 β γ 4 = ![1, 0, 0, 0]

@[expose] def KerFactCh611 (β γ : Fin 3 → ZMod 2) : Prop :=
  ∀ c : Fin 4 → ZMod 2 × ZMod 2,
    Matrix.transpose (candACh611 β γ c) * formBCh611 β γ * candACh611 β γ c = formBCh611 β γ →
    (∀ i, LineEqCh611 ((candACh611 β γ c).mulVec (omPCh611 β γ i))
      ((candACh611 β γ c).mulVec (omQCh611 β γ i)) (omPCh611 β γ i) (omQCh611 β γ i)) →
    candACh611 β γ c = 1

theorem caseFacts_ch611 : ∀ β γ : Fin 3 → ZMod 2, GoodCh611 β γ → CaseFactsCh611 β γ := by
  intro β γ hg
  obtain ⟨rfl | rfl, rfl | rfl⟩ := goodCh611_cases hg <;> unfold CaseFactsCh611 <;>
    decide +kernel

theorem kerFact_ch611 : ∀ β γ : Fin 3 → ZMod 2, GoodCh611 β γ → KerFactCh611 β γ := by
  intro β γ hg
  obtain ⟨rfl | rfl, rfl | rfl⟩ := goodCh611_cases hg <;> unfold KerFactCh611 <;>
    decide +kernel

theorem kleinCh611_props : (∀ k, kleinCh611 k ∈ alternatingGroup (Fin 5)) ∧
    Function.Injective kleinCh611 := by
  have hs : ∀ k, Perm.sign (kleinCh611 k) = 1 := by decide
  exact ⟨fun k => Perm.mem_alternatingGroup.mpr (hs k), by decide⟩

end CFSG.Quasithin.H13
