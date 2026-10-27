module

public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Monster.Code

theorem natCard_eq_of_realizes {W : Type} [CommGroup W] {D : FFModel} {H : Subgroup (MulAut W)}
    (h : D.Realizes H ⊤ ⊥) :
    Nat.card W = Nat.card (↥D.sec ⧸ D.ker.subgroupOf D.sec) := by
  obtain ⟨π, -, -, hker, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (by simpa using this)
  have hbij : Function.Bijective β := ⟨hinj, hβs⟩
  have h1 := Nat.card_congr (Equiv.ofBijective β hbij)
  rw [← h1]
  exact (Subgroup.card_top (G := W)).symm

theorem natCard_golayC : Nat.card golayC = 2 ^ 12 := by
  have h1 : Nat.card golayC = Nat.card (CFSG.Monster.Code.C : Submodule (ZMod 2) (Fin 24 → ZMod 2)) :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd (fun _ => Iff.rfl))
  rw [h1, Nat.card_congr basisC.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem natCard_zpowers_allOnes : Nat.card (Subgroup.zpowers (G6.allOnes 24)) = 2 := by
  rw [Nat.card_zpowers]
  apply orderOf_eq_prime
  · apply Multiplicative.toAdd.injective
    funext i
    have h2 : (2 : ZMod 2) = 0 := rfl
    simp [G6.allOnes, ← one_add_one_eq_two] at *
    exact h2
  · intro h
    have := congrFun (congrArg Multiplicative.toAdd h) 0
    simp [G6.allOnes] at this

theorem card_sec_eq {G : Type} [Group G] {sec ker : Subgroup G} (hle : ker ≤ sec) :
    Nat.card sec = Nat.card (↥sec ⧸ ker.subgroupOf sec) * Nat.card ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (ker.subgroupOf sec)]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem natCard_of_mathieu24 {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (h : MathieuCode24 H ⊤ ⊥ ∨ MathieuCocode24 H ⊤ ⊥) : Nat.card W = 2 ^ 11 := by
  rcases h with h | h
  · have h1 := natCard_eq_of_realizes h
    have h2 := card_sec_eq (sec := golayC) (ker := Subgroup.zpowers (G6.allOnes 24))
      (Subgroup.zpowers_le.2 allOnes_mem_golayC)
    rw [natCard_golayC, natCard_zpowers_allOnes] at h2
    change Nat.card W = Nat.card (↥golayC ⧸ (Subgroup.zpowers (G6.allOnes 24)).subgroupOf golayC)
      at h1
    omega
  · have h1 := natCard_eq_of_realizes h
    have h2 := card_sec_eq (sec := G6.coreMod 24) (ker := golayC) golayC_le_coreMod
    rw [Explicit.card_coreMod (by norm_num), natCard_golayC] at h2
    change Nat.card W = Nat.card (↥(G6.coreMod 24) ⧸ golayC.subgroupOf (G6.coreMod 24)) at h1
    omega

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
