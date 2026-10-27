module

public import CFSG.Monster.CodeAut.BridgeData
public import CFSG.Assembly.Defs
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Sporadic.Fi24.OctadFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open CFSG.Monster.Code CFSG.Sporadic.Fi24 CFSG.Sporadic.Mathieu

@[expose] def fi24ETau : Equiv.Perm (Fin 24) where
  toFun := ![0, 2, 3, 13, 14, 15, 21, 16, 1, 7, 20, 17, 12, 23, 8, 18, 11, 9, 19, 5, 4, 6, 22, 10]
  invFun := ![0, 8, 1, 2, 20, 19, 21, 9, 14, 17, 23, 16, 12, 3, 4, 5, 7, 11, 15, 18, 10, 6, 22, 13]
  left_inv := by decide
  right_inv := by decide

@[expose] def fi24EC : Equiv.Perm (Fin 24) := fi24ETau * bridgeQ⁻¹

@[expose] def fi24EKm : Fin 12 → Fin 759 :=
  ![498, 575, 554, 541, 387, 38, 637, 465, 385, 742, 36, 751]

@[expose] def octWord (S : Finset (Fin 24)) : Fin 24 → ZMod 2 :=
  fun i => if fi24ETau i ∈ S then 1 else 0

@[expose] noncomputable def wordE (w : List (Fin 2 × ℕ)) : Equiv.Perm (Fin 24) :=
  (w.map fun p => permE p.1 ^ p.2).prod

@[expose] def fi24EWA : List (Fin 2 × ℕ) := [(1, 20), (0, 1), (1, 2), (0, 1), (1, 16), (0, 1),
  (1, 4), (0, 1), (1, 3), (0, 1), (1, 20), (0, 1), (1, 19), (0, 1), (1, 2), (0, 1), (1, 20),
  (0, 1), (1, 1), (0, 1), (1, 20), (0, 1), (1, 20), (0, 1), (1, 1), (0, 1), (1, 20), (0, 1),
  (1, 1), (0, 1), (1, 6), (0, 1), (1, 20), (0, 1), (1, 1), (0, 1), (1, 4), (0, 1), (1, 20),
  (0, 1), (1, 5), (0, 1), (1, 20), (0, 1), (1, 1), (0, 1), (1, 20)]

@[expose] def fi24EWB : List (Fin 2 × ℕ) := [(1, 1), (0, 1), (1, 1), (0, 1), (1, 1), (0, 1),
  (1, 19), (0, 1), (1, 1), (0, 1), (1, 5), (0, 1), (1, 2), (0, 1), (1, 1), (0, 1), (1, 20),
  (0, 1), (1, 2), (0, 1), (1, 2), (0, 1), (1, 19), (0, 1), (1, 4), (0, 1), (1, 1), (0, 1),
  (1, 2), (0, 1), (1, 14), (0, 1), (1, 4), (0, 1), (1, 1), (0, 1), (1, 20), (0, 1), (1, 17),
  (0, 1), (1, 1), (0, 1), (1, 20), (0, 1), (1, 20), (0, 1), (1, 1), (0, 1), (1, 20), (0, 1),
  (1, 20), (0, 1), (1, 20), (0, 1), (1, 19), (0, 1)]

theorem basis_eq_octWord : ∀ m : Fin 12, B m = octWord (octF (fi24EKm m)) := by
  intro m
  funext i
  revert m i
  decide +kernel

theorem octWord_zero_mem : octWord (octF 0) ∈ C := by decide +kernel

theorem tauConj_basis_zero : ∀ m : Fin 12, B m ∘ ⇑(fi24ETau⁻¹ * permE 0 * fi24ETau) ∈ C := by
  decide +kernel

theorem tauConj_basis_one : ∀ m : Fin 12, B m ∘ ⇑(fi24ETau⁻¹ * permE 1 * fi24ETau) ∈ C := by
  decide +kernel

theorem tauConj_basis_one_pow :
    ∀ m : Fin 12, B m ∘ ⇑((fi24ETau⁻¹ * permE 1 * fi24ETau) ^ 20) ∈ C := by
  decide +kernel

theorem tauConj_zero_mul_self :
    fi24ETau⁻¹ * permE 0 * fi24ETau * (fi24ETau⁻¹ * permE 0 * fi24ETau) = 1 :=
  Equiv.ext (by decide +kernel)

theorem tauConj_one_pow : (fi24ETau⁻¹ * permE 1 * fi24ETau) ^ 21 = 1 :=
  Equiv.ext (by decide +kernel)

theorem tauConj_mem (l : Fin 2) : fi24ETau⁻¹ * permE l * fi24ETau ∈ AutPerm := by
  rcases (show ∀ l : Fin 2, l = 0 ∨ l = 1 by decide) l with rfl | rfl
  · refine mem_AutPerm_of_basis tauConj_basis_zero ?_
    rw [inv_eq_of_mul_eq_one_right tauConj_zero_mul_self]
    exact tauConj_basis_zero
  · refine mem_AutPerm_of_basis tauConj_basis_one ?_
    rw [inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact tauConj_one_pow)]
    exact tauConj_basis_one_pow

theorem conj_m24gA : fi24EC * m24gA * fi24EC⁻¹ = wordE fi24EWA :=
  Equiv.ext (by decide +kernel)

theorem conj_m24gB : fi24EC * m24gB * fi24EC⁻¹ = wordE fi24EWB :=
  Equiv.ext (by decide +kernel)

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
