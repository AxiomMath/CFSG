module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.B3CaseB

public section

namespace CFSG.Quasithin.B3

@[expose] def SQTKn (n : ℕ) : Prop := n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8

@[expose] def CaseA (n : ℕ) (k : Mod) : Prop := n % 2 = 1 ∨ k = Mod.u ∨ k = Mod.ut

@[expose] def CaseB (n : ℕ) (k : Mod) : Prop := n % 2 = 0 ∧ (k = Mod.u0 ∨ k = Mod.ut0)

@[expose] def PropB32A (n : ℕ) (k : Mod) : Prop :=
  (∀ A : Subgroup (Gp n), IsOffG n k A ↔ ∃ i < n / 2, A ∈ conjClass (Am n (i + 1))) ∧
  (∀ i < n / 2, rk (Am n (i + 1)) = i + 1 ∧
    rkIdx (fixV ((Am n (i + 1)).map (Mod.act n k))) = i + 1) ∧
  (∃ T : Sylow 2 (Gp n), (∀ i < n / 2, Am n (i + 1) ≤ T) ∧ A0 n ≤ T ∧
    ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (Dsub n).map (Mod.act n k)) ∧
  qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((1 : ℚ) : WithTop ℚ)

@[expose] def PropB32B5 (n : ℕ) (k : Mod) : Prop :=
  (∀ A : Subgroup (Gp n), IsOffG n k A ↔
    A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
      (∃ i < n / 2, A ∈ conjClass (Am n (i + 1))) ∨ A ∈ Hset n) ∧
  (∀ i < n / 2, rk (Am n (i + 1)) = i + 1 ∧
    rkIdx (fixV ((Am n (i + 1)).map (Mod.act n k))) =
      if i + 1 = n / 2 then n / 2 - 1 else i + 1) ∧
  (rk (A0 n) = n / 2 ∧ rkIdx (fixV ((A0 n).map (Mod.act n k))) = n / 2) ∧
  (∃ T : Sylow 2 (Gp n), (∀ i < n / 2, Am n (i + 1) ≤ T) ∧ A0 n ≤ T ∧
    ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) =
      (Dsub n ⊔ Subgroup.closure
        {x : Gp n | x ∈ (T : Subgroup (Gp n)) ∧ IsConj (ti n 0 * ti n 1) x}).map
          (Mod.act n k) ∧
    ∀ A : Subgroup (Gp n), A ≤ T →
      (IsStrongFFStarOffender ((T : Subgroup (Gp n)).map (Mod.act n k)) (A.map (Mod.act n k)) ↔
        A = Dsub n)) ∧
  qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) =
    ((((n : ℚ) - 2) / n : ℚ) : WithTop ℚ)

@[expose] def PropB32B6 (n : ℕ) (k : Mod) : Prop :=
  (∀ A : Subgroup (Gp n), IsOffG n k A ↔
    A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
      (∃ i < n / 2, A ∈ conjClass (Am n (i + 1))) ∨ A ∈ Hset n ∨ A ∈ Rset n) ∧
  (∀ i < n / 2, rk (Am n (i + 1)) = i + 1 ∧
    rkIdx (fixV ((Am n (i + 1)).map (Mod.act n k))) =
      if i + 1 = n / 2 then n / 2 - 1 else i + 1) ∧
  (rk (A0 n) = n / 2 ∧ rkIdx (fixV ((A0 n).map (Mod.act n k))) = n / 2) ∧
  (∀ A ∈ Rset n, rkIdx (fixV (A.map (Mod.act n k))) = 3) ∧
  (∃ T : Sylow 2 (Gp n), (∀ i < n / 2, Am n (i + 1) ≤ T) ∧ A0 n ≤ T ∧
    ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (T : Subgroup (Gp n)).map (Mod.act n k) ∧
    ∀ A : Subgroup (Gp n), A ≤ T →
      (IsStrongFFStarOffender ((T : Subgroup (Gp n)).map (Mod.act n k)) (A.map (Mod.act n k)) ↔
        A = Dsub n)) ∧
  qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) =
    ((((n : ℚ) - 2) / n : ℚ) : WithTop ℚ)

@[expose] def StrongTl6 (k : Mod) : Prop :=
  ∀ A : Subgroup (Gp 6), A ≤ subOf 6 (Tl 6) →
    (IsStrongFFStarOffender ((subOf 6 (Tl 6)).map (Mod.act 6 k)) (A.map (Mod.act 6 k)) ↔
      A = Dsub 6)

end CFSG.Quasithin.B3
