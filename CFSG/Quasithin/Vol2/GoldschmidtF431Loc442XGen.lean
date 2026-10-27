module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Gen

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.Loc442

universe u

variable {Mb : Type u} [Group Mb]

structure Loc442DatumX (M1 M2 T : Subgroup Mb) (z t : Mb) (Vb : Subgroup Mb) (q : Mb) : Prop where
  lie : F431LieI T M1 M2 z t
  V_le : Vb ≤ Subgroup.centralizer ({t} : Set Mb)
  V_card : Nat.card Vb = 4
  V_comm : ∀ a ∈ Vb, ∀ b ∈ Vb, a * b = b * a
  V_sq : ∀ a ∈ Vb, a ^ 2 = 1
  V_norm : ∀ x ∈ Subgroup.centralizer ({t} : Set Mb), ∀ v ∈ Vb, x * v * x⁻¹ ∈ Vb
  V_conj : ∀ v ∈ Vb, v ≠ 1 → ∃ x ∈ Subgroup.centralizer ({t} : Set Mb), v = x * z * x⁻¹
  q_mem : q ∈ Subgroup.centralizer ({t} : Set Mb)
  q_comm : ∀ v ∈ Vb, q * v = v * q
  q_sq : q ^ 2 ∈ Vb
  q_sq_ne : q ^ 2 ≠ 1
  Ct_cop : Nat.Coprime (Nat.card (Subgroup.centralizer ({t} : Set Mb))) 65
  fusion : ∀ u ∈ Subgroup.centralizer ({t} : Set Mb), IsConj z u → u ∈ Vb ∨
    ∃ n ∈ M2, ∃ a ∈ T, ∃ b ∈ T, u = n * a * n⁻¹ ∧ t = n * b * n⁻¹ ∧
      ∃ b' ∈ T, Relation.ReflTransGen (PairLink T M1 M2) (a, b) (z, b') ∧
        ∀ h ∈ M1, h * t * h⁻¹ ≠ b'

variable {M1 M2 T : Subgroup Mb} {z t q : Mb} {Vb : Subgroup Mb}

end CFSG.Quasithin
