module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3331
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

@[expose] def Insp3_3_32Mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 → T ≤ Subgroup.normalizer (L : Set G) → tC L T = ⊥ →
    Nonempty (↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6)) →
      (qL L T = vPlus L T ∧ ∃ _ : IsMulCommutative ↥(vPlus L T),
          XMod.IsIrrSec ↥(autOn L (vPlus L T)) (⊥ : Subgroup ↥(vPlus L T)) ⊤) ∨
        (∃ _ : IsMulCommutative ↥(qL L T), Nat.card ↥(qL L T) = 2 ^ 5 ∧
          permQuot6Model.Realizes (autOn (L ⊔ T) (qL L T)) ⊤ ⊥)

@[expose] def Insp3_3_32Par : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsAltBlockType L 6 → T ≤ Subgroup.normalizer (L : Set G) → tC L T = ⊥ →
    Nat.card ↥(qL L T) ≤ 2 ^ 5 →
    Nat.card T < 2 ^ 12 ∧
    ∃ X₁ X₂ : Subgroup G,
      (oTwoUpper X₁ = X₁ ∧ T ≤ Subgroup.normalizer (X₁ : Set G) ∧
        Nonempty (↥(X₁ ⊔ T) ⧸ CFSG.pCore 2 ↥(X₁ ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ HasNoncentralTwoChief X₁ 5) ∧
      (oTwoUpper X₂ = X₂ ∧ T ≤ Subgroup.normalizer (X₂ : Set G) ∧
        Nonempty (↥(X₂ ⊔ T) ⧸ CFSG.pCore 2 ↥(X₂ ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ HasNoncentralTwoChief X₂ 5) ∧
      ((∃ φ : ↥(autOn (L ⊔ T) (vPlus L T)) ≃* Equiv.Perm (Fin 6),
          ((autOn T (vPlus L T)).subgroupOf (autOn (L ⊔ T) (vPlus L T))).map φ.toMonoidHom =
            sylowS6 ∧
          pCoreOf 2 (X₁ ⊔ T) ⊓ pCoreOf 2 (X₂ ⊔ T) = preimageA2 T L φ) ∨
        ∀ B : Subgroup G, IsMaxElemAbelian (pCoreOf 2 (X₁ ⊔ T) ⊓ pCoreOf 2 (X₂ ⊔ T)) B →
          B = qL L T)

variable {G : Type} [Group G]

theorem mem_normalizer_inf_of_both {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf] at hA hB ⊢
  exact and_congr (hA x) (hB x)

variable [Finite G]

theorem stmt3_3_32_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14) (h20 : Stmt3_3_20)
    (h30 : Stmt3_3_30) (h31 : Stmt3_3_31) (hM : Insp3_3_32Mod) (hP : Insp3_3_32Par) :
    Stmt3_3_32 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hA6 := h30 G T M L D h
  have hTC := h31 G T M L D h
  have hQ5 := h.card_qL_le_of_tC_eq_bot h38 h39 hA6 hTL hTC
  have h1 := hM G T M L D h hA6 hTL hTC
  obtain ⟨hcard, X₁, X₂, ⟨hX₁, hTX₁, hS₁, hγ₁⟩, ⟨hX₂, hTX₂, hS₂, hγ₂⟩, hcase⟩ :=
    hP G T M L D h hA6 hTL hTC hQ5
  have hR₁ : D ≤ Subgroup.normalizer (pCoreOf 2 (X₁ ⊔ T) : Set G) := by
    by_contra hD
    have h12 := ((h20 G T M L D X₁ h hX₁ hTX₁ hS₁ hD).2.2.2.2 hγ₁).1.2.2.2
    omega
  have hR₂ : D ≤ Subgroup.normalizer (pCoreOf 2 (X₂ ⊔ T) : Set G) := by
    by_contra hD
    have h12 := ((h20 G T M L D X₂ h hX₂ hTX₂ hS₂ hD).2.2.2.2 hγ₂).1.2.2.2
    omega
  have hT₁ : D ≤ Subgroup.normalizer
      ((pCoreOf 2 (X₁ ⊔ T) ⊓ pCoreOf 2 (X₂ ⊔ T) : Subgroup G) : Set G) :=
    fun d hd => mem_normalizer_inf_of_both (hR₁ hd) (hR₂ hd)
  rcases hcase with ⟨φ, hφT, hT₀⟩ | hJ
  · refine ⟨h1 ⟨φ⟩, ⟨φ⟩, φ, hφT, ?_⟩
    show D ≤ Subgroup.normalizer (preimageA2 T L φ : Set G)
    rw [← hT₀]
    exact hT₁
  ·
    exfalso
    obtain ⟨B₀, hB₀⟩ :=
      GammaExtra.exists_isMaxElemAbelian (pCoreOf 2 (X₁ ⊔ T) ⊓ pCoreOf 2 (X₂ ⊔ T))
    have hB₀Q := hJ B₀ hB₀
    have hDQ : D ≤ Subgroup.normalizer (qL L T : Set G) := by
      intro d hd
      have h1 := (isMaxElemAbelian_map_mulEquiv (MulAut.conj d)).mpr hB₀
      rw [A38.map_conj_eq_iff.mpr (hT₁ hd)] at h1
      have h2 := hJ _ h1
      rw [hB₀Q] at h2
      exact A38.map_conj_eq_iff.mp h2
    exact h.not_le_normalizer h38 h39 h.toSetup331.pCoreOf_ne_bot
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      hDQ

end CFSG.Quasithin.H13
