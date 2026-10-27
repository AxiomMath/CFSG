module

public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalGroup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Monster.Code
open scoped IsMulCommutative

structure ModelDichotomies : Prop where
  su3 : ∀ (n : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    NormalDichotomy ↥(StatedSU 3 (2 ^ n) K)
  sz : ∀ (a : ℕ) (K : Type) [Field K] [Finite K], 1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
    NormalDichotomy ↥(suzukiGroup a K)
  sl3 : ∀ (n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n →
    NormalDichotomy ↥(StatedSL 3 K)
  sp4 : ∀ (n : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ n → Nat.card K = 2 ^ n →
    NormalDichotomy ↥(StatedSp 2 K)
  alt6 : NormalDichotomy ↥(alternatingGroup (Fin 6))
  alt7 : NormalDichotomy ↥(alternatingGroup (Fin 7))
  m24 : NormalDichotomy ↥AutPerm
  m23 : ∀ x : Fin 24, NormalDichotomy ↥(AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x)
  m22 : ∀ x y : Fin 24, x ≠ y → NormalDichotomy ↥(AutPerm ⊓
    MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) y)
  m12 : ∀ eY : CFSG.Quasithin.G6.PermMod 24, eY ∈ CFSG.Quasithin.golayC →
    hammingNorm (Multiplicative.toAdd eY) = 12 → NormalDichotomy ↥(CFSG.Quasithin.m24Fix eY)

theorem hmodel_of_realizes {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {D : CFSG.Quasithin.FFModel} (h : D.Realizes H U Z) (hQ : NormalDichotomy D.Gam) :
    ∃ (Γ : Type) (_ : Group Γ) (π : Γ →* ↥H), Function.Surjective π ∧ NormalDichotomy Γ := by
  obtain ⟨π, hπ, -⟩ := h
  exact ⟨D.Gam, inferInstance, π, hπ, hQ⟩

section Rows

variable {G : Type} [Group G] {T L I : Subgroup G} [IsMulCommutative ↥(fsuV T I)]

theorem hmodel_of_row (hD : ModelDichotomies)
    (h : Row711SU3 T L I ∨ Row711Sz T L I ∨ (∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M12 T L I ∨
        Row711M22Hat T L I ∨ Row711M22Code T L I ∨ Row711M22Cocode T L I ∨
        Row711M23Code T L I ∨ Row711M23Cocode T L I ∨ Row711M24Code T L I ∨
        Row711M24Cocode T L I ∨ (∃ n : ℕ, Row711SL3Pair T L I n) ∨ Row711Sp4Pair T L I ∨
        Row711S7Pair T L I) :
    ∃ (Γ : Type) (_ : Group Γ) (π : Γ →* ↥(autOn (fsuL0 T L) (fsuV T I))),
      Function.Surjective π ∧ NormalDichotomy Γ := by
  rcases h with h | h | ⟨n, h⟩ | h | h | h | h | h | h | h | h | ⟨n, h⟩ | h | h
  · obtain ⟨n, hn, K, _, _, hK, hr⟩ := h
    exact hmodel_of_realizes hr (hD.su3 n K hn hK)
  · obtain ⟨f, a, ha, hf, K, _, _, hK, hr⟩ := h
    exact hmodel_of_realizes hr (hD.sz a K ha (hf ▸ hK))
  · obtain ⟨-, K, _, _, _, hK, hr⟩ := h
    exact hmodel_of_realizes hr (hD.sl3 (2 * n) K hK)
  · obtain ⟨⟨eY, heY, hw, hr⟩, -⟩ := h
    exact hmodel_of_realizes hr (hD.m12 eY heY hw)
  · obtain ⟨K, _, _, Γ₀, -, hhat, -, hr⟩ := h
    exact hmodel_of_realizes hr (NormalDichotomy.of_perfect_simple_quotient
      hhat.1.1.commutator_eq_top hhat.1.2.1)
  · obtain ⟨x, y, hxy, hr⟩ := h
    exact hmodel_of_realizes hr (hD.m22 x y hxy)
  · obtain ⟨x, y, hxy, hr⟩ := h
    exact hmodel_of_realizes hr (hD.m22 x y hxy)
  · obtain ⟨x, hr⟩ := h
    exact hmodel_of_realizes hr (hD.m23 x)
  · obtain ⟨x, hr⟩ := h
    exact hmodel_of_realizes hr (hD.m23 x)
  · exact hmodel_of_realizes h hD.m24
  · exact hmodel_of_realizes h hD.m24
  · obtain ⟨-, K, _, _, hK, hr⟩ := h
    exact hmodel_of_realizes hr (hD.sl3 n K hK)
  · obtain ⟨-, h | h⟩ := h
    · obtain ⟨n, hn, K, _, _, hK, hr⟩ := h
      exact hmodel_of_realizes hr (hD.sp4 n K hn hK)
    · exact hmodel_of_realizes h hD.alt6
  · obtain ⟨-, α, hr⟩ := h
    exact hmodel_of_realizes hr hD.alt7

end Rows

end CFSG.Quasithin.H13
