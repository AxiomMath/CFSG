module

public import CFSG.Quasithin.Background.G1Basic
public import CFSG.Quasithin.Background.G2L2Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G]

theorem card_eq_mul_relIndex_of_le {A B : Subgroup G} (h : A ≤ B) :
    Nat.card ↥B = Nat.card ↥A * A.relIndex B := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf B)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  exact h1.symm

namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

omit [Finite G] in
theorem card_V : Nat.card ↥V = Nat.card (GaloisField 2 n) ^ 2 := by
  have h1 : Nat.card ↥V = Nat.card (Wm (GaloisField 2 n)) := Nat.card_congr S.D.ψ.toEquiv
  have h2 : Nat.card (Wm (GaloisField 2 n)) = Nat.card (Fin 2 → GaloisField 2 n) :=
    Nat.card_congr Multiplicative.toAdd
  rw [h1, h2, Nat.card_fun]
  simp

theorem card_U_eq {U I Sx W : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : Sx = pCoreOf 2 I) (hW : W = U ⊓ Sx) :
    Nat.card ↥U = Nat.card ↥W * Nat.card (GaloisField 2 n) := by
  obtain ⟨hI', hLI, hUI, hIle, hSxO, hINorm, hSxU⟩ := S.sx_facts hU hg hgN hI
  rw [← hS] at hSxO
  have hWU : W ≤ U := by
    rw [hW]
    exact inf_le_left
  subst hU
  have hker : S.betaU.ker = W.subgroupOf (conjClosure V H) := by
    ext u
    rw [MonoidHom.mem_ker, S.betaU_eq_one_iff, Subgroup.mem_subgroupOf, hW, Subgroup.mem_inf]
    constructor
    · intro hu
      refine ⟨u.2, ?_⟩
      rw [hS]
      exact mem_pCoreOf_of_mem_pCoreOf_of_le hIle (hUI u.2) hu
    · rintro ⟨-, hu⟩
      exact hSxO hu
  have h1 := Subgroup.card_ker_mul_card_range S.betaU
  rw [hker, show S.betaU.range = Rg (GaloisField 2 n) from S.Ubar_eq_Rg, Rg_card,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWU).toEquiv] at h1
  exact h1.symm

end L2Setting

end CFSG.Quasithin
