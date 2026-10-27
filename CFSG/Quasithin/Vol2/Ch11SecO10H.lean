module

public import CFSG.Quasithin.Vol2.Ch11SecE42S2e
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 Matrix

variable {G : Type} [Group G] [Finite G]

theorem le_sup_pCoreOf_of_le {N B : Subgroup G} (hBN : B ≤ N) {F F₀ : Type} [Field F]
    [Finite F] [Field F₀] [Finite F₀] (hFF : Nat.card F = Nat.card F₀)
    (e : ↥B ⧸ CFSG.pCore 2 ↥B ≃* SpecialLinearGroup (Fin 2) F)
    (e₀ : ↥N ⧸ CFSG.pCore 2 ↥N ≃* SpecialLinearGroup (Fin 2) F₀) :
    N ≤ B ⊔ pCoreOf 2 N := by
  obtain ⟨φ, hφs, -⟩ := SecE.exists_modO2Image_lOf_map hBN e
  have hcard : Nat.card (↥N ⧸ CFSG.pCore 2 ↥N) ≤ Nat.card ↥(modO2Image N B) := by
    rw [Nat.card_congr e₀.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, ← hFF,
      ← CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Nat.card_le_card_of_surjective φ hφs
  have htop : modO2Image N B = ⊤ := Subgroup.eq_top_of_le_card _ hcard
  intro x hx
  have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥N) ⟨x, hx⟩ : ↥N ⧸ CFSG.pCore 2 ↥N) ∈
      modO2Image N B := htop ▸ Subgroup.mem_top _
  obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hbx
  have h1 : ((b⁻¹ * ⟨x, hx⟩ : ↥N) : G) ∈ pCoreOf 2 N := by
    rw [← SecD.pCoreOf_subgroupOf] at hbx
    exact hbx
  have h2 : x = (b : G) * ((b⁻¹ * ⟨x, hx⟩ : ↥N) : G) := by simp
  rw [h2]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hb) h1

theorem rOf_eq_of_le_normalizer (h1110 : Stmt11_1_0) {T L I K I' : Subgroup G} {n : ℕ}
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hK : Hyp11 G T K I' n)
    {i : ℕ} (hi : i = 1 ∨ i = 2) {U : Subgroup G} (hU : IsVi T K I' n i U)
    (hLK : LOf L V₁ ≤ K) (hLU : LOf L V₁ ≤ Subgroup.normalizer (U : Set G)) :
    ROf T L V₁ = ROf T K U := by
  have hle : LOf L V₁ ≤ LOf K U :=
    le_perfectCore_of_perfect (le_inf hLK hLU) (perfectCore_perfect _)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := (h1110 G T L I n h).2.1 1 (Or.inl rfl) V₁ hV₁
  obtain ⟨F₀, _, _, hF₀, ⟨e₀⟩⟩ := (h1110 G T K I' n hK).2.1 i hi U hU
  have hsup := le_sup_pCoreOf_of_le hle (hF.trans hF₀.symm) e e₀
  have hOT : pCoreOf 2 (LOf K U) ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer
        (SecA.T_le_normalizer_lOf hK.normal (SecA.IsVi.le_normalizer hU))).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)).trans (SecE.rOf_le_T hK U)
  have heq : LOf L V₁ ⊔ T = LOf K U ⊔ T :=
    le_antisymm (sup_le_sup_right hle T)
      (sup_le (hsup.trans (sup_le le_sup_left (hOT.trans le_sup_right))) le_sup_right)
  change pCoreOf 2 (LOf L V₁ ⊔ T) = pCoreOf 2 (LOf K U ⊔ T)
  rw [heq]

end CFSG.Quasithin.Vol2.Ch11.O10
