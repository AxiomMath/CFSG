module

public import CFSG.Sporadic.Co2Smith.CData
public import CFSG.Sporadic.Co2Smith.CInvar
public import CFSG.Sporadic.Co2Smith.ClassCount

public section

namespace CFSG.Sporadic.Co2Smith

abbrev XC
    (i : ℕ) : Subgroup Cz := Subgroup.centralizer ({cR i} : Set Cz)

abbrev DCi
    (i : ℕ) : Subgroup Cz := XC i ⊓ CFSG.pCore 2 Cz

structure CCFacts :
    Prop where
  classes : ∀ y : Cz, y * y = 1 → y = 1 ∨ y = zCz ∨ ∃ i : Fin 9, ∃ h : Cz, h * y * h⁻¹ = cR i
  cls : ∀ i : Fin 9, (conjSet (cR i)).ncard = Native.ccCls[(i : ℕ)]!
  sqrt : ∀ i : Fin 9, sqrtCnt zCz (cR i) = Native.ccSqZ[(i : ℕ)]! ∧
    sqrtCnt (cR i) (cR i) = Native.ccSqR[(i : ℕ)]!
  ce : ∀ i : Fin 9, ceInv (cR i) = Native.ccCE[(i : ℕ)]!
  invE : ∀ i : Fin 9, invEInv (cR i) = Native.ccInvE[(i : ℕ)]!
  c3 : ∃ w : Cz, w ∈ CFSG.pCore 2 Cz ∧ w ≠ 1 ∧ w * cR 8 = cR 8 * w ∧
    (∃ h : Cz, h * (cR 8 * w) * h⁻¹ = cR 8) ∧
    ∀ hw : w ∈ XC 8, ∀ α : XC 8 ≃* XC 8, α ⟨w, hw⟩ = ⟨w, hw⟩
  c2B_comm : ∀ a ∈ DCi 7, ∀ b ∈ DCi 7, a * b = b * a
  c2B_cxd : Nat.card (Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 : Subgroup Cz) ≤
    Nat.card (DCi 7) ^ 2
  c2B_zd : Nat.card {d : Cz // d ∈ DCi 7 ∧ ∀ x ∈ XC 7, x * d = d * x} ≤ 2
  c2B_za : 8 ≤ Nat.card {a : Cz // a ∈ Subgroup.centralizer (DCi 7 : Set Cz) ⊓ XC 7 ∧
    ∀ x ∈ XC 7, x * a = a * x}
  c2B_hmin : ∀ N : Subgroup Cz, N ≤ DCi 7 → (∀ x ∈ XC 7, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
    N ≠ ⊥ → zCz ∉ N → ∃ d ∈ N, d ≠ 1 ∧ ∃ h : Cz, h * (cR 7 * d) * h⁻¹ = cR 7
  c1_comm : ∀ a ∈ DCi 1, ∀ b ∈ DCi 1, a * b = b * a
  c1_hmin : ∀ N : Subgroup Cz, N ≤ DCi 1 → (∀ x ∈ XC 1, ∀ n ∈ N, x * n * x⁻¹ ∈ N) →
    N ≠ ⊥ → zCz ∈ N
  c1_cxd_card : Nat.card (Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1 : Subgroup Cz) ≤ 1024
  c1_cxd_sq : ∀ y ∈ Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1, y * y = 1
  c1_j : ∃ j ∈ Subgroup.centralizer (DCi 1 : Set Cz) ⊓ XC 1, invEInv j = 80
  c1_two : ∃ h : Cz, h * (cR 2 * zCz) * h⁻¹ = cR 1
  syl : ∀ k < 3, ∃ U : Subgroup Cz, U ≤ XC (k + 3) ∧ Nat.card U = Native.ccSylSize[k]! ∧
    zCz ∈ U ∧ ∀ y ∈ U, (∀ u ∈ U, u * y = y * u) → y * y = 1 → y ≠ 1 → y ≠ zCz →
      invEInv y ≠ 32

end CFSG.Sporadic.Co2Smith
