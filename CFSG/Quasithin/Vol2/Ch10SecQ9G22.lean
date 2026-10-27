module

public import CFSG.Quasithin.Vol2.Ch10SecQ9G15
public import CFSG.Quasithin.Vol2.Ch10SecQ9G20

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure C5Coord (L W : Subgroup G) (s : G) where
  D : NatData L W
  c : G → L3.Vec
  c_mul : ∀ b₁ ∈ CFSG.conjugate W s, ∀ b₂ ∈ CFSG.conjugate W s, c (b₁ * b₂) = c b₁ + c b₂
  c_inj : ∀ b₁ ∈ CFSG.conjugate W s, ∀ b₂ ∈ CFSG.conjugate W s, c b₁ = c b₂ → b₁ = b₂
  c_surj : ∀ y, ∃ b ∈ CFSG.conjugate W s, c b = y
  c_equi : ∀ l : ↥L, ∀ b ∈ CFSG.conjugate W s,
    c ((l : G) * b * (l : G)⁻¹) = L3.act (τ3 (D.ρ l)) (c b)

variable [Finite G] {T L I : Subgroup G}

theorem exists_c5Coord (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h1011 : Stmt10_1_1)
    (hyp : Hyp10 G T L I) {s : G} (hsL : s ∈ Subgroup.normalizer (L : Set G)) {W : Subgroup G}
    (hWV1 : W ≤ fsuUL T L I) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hsup : W ⊔ CFSG.conjugate W s = fsuUL T L I) [IsMulCommutative ↥W]
    (hnat : BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ 3 1)
    (hni : ¬ IsXSectionIso L ⊥ W (CFSG.conjugate W s)) : Nonempty (C5Coord L W s) := by
  obtain ⟨D⟩ := exists_natData hLW hnat
  set D' := D.conj hsL with hD'
  have hWsV1 : CFSG.conjugate W s ≤ fsuUL T L I := hsup ▸ le_sup_right
  have hLWs : L ≤ Subgroup.normalizer ((CFSG.conjugate W s : Subgroup G) : Set G) :=
    le_normalizer_conjugate_of' hsL hLW
  have hWne : ⁅W, L⁆ ≠ ⊥ := fun h => not_le_centralizer_of_natural hnat
    (Subgroup.le_centralizer_iff.mpr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)))
  have hWsne : ⁅CFSG.conjugate W s, L⁆ ≠ ⊥ := fun h => not_le_centralizer_of_natural hnat
    ((SecB.le_centralizer_conjugate_iff hsL).mp (Subgroup.le_centralizer_iff.mpr
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact h))))
  have hC1 := SecB.mem_centralizer_iff_of_le_fsuUL h37 h38 h322 hyp hWV1 hLW hWne
  have hC2 := SecB.mem_centralizer_iff_of_le_fsuUL h37 h38 h322 hyp hWsV1 hLWs hWsne
  have hker : ∀ l : ↥L, D.ρ l = 1 ↔ D'.ρ l = 1 := fun l => by
    rw [D.ker_ρ, D'.ker_ρ, ← hC1 _ l.2, hC2 _ l.2]
  rcases exists_twist D D' hker with ⟨g, hg⟩ | ⟨g, hg⟩
  · exfalso
    have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
    have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
    have hO : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G) :=
      (pCoreOf_L_le_centralizer hyp h1011).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hWV1.trans hV1V)))
    exact hni (isXSectionIso_of_twist_inner D hsL hLW hO
      (fun l hl => mem_pCoreOf_of_centralizer h37 h38 h1011 hyp l.2 ((hC1 _ l.2).mpr hl)) hg)
  · refine ⟨⟨D, fun b => L3.act g⁻¹ (D'.b b), ?_, ?_, ?_, ?_⟩⟩
    · intro b₁ h₁ b₂ h₂
      rw [D'.b_mul _ h₁ _ h₂, L3.act_add]
    · intro b₁ h₁ b₂ h₂ h
      exact D'.b_inj _ h₁ _ h₂ (act_injective _ h)
    · intro y
      obtain ⟨b, hb, hby⟩ := D'.b_surj (L3.act g y)
      refine ⟨b, hb, ?_⟩
      show L3.act g⁻¹ (D'.b b) = y
      rw [hby, ← L3.act_mul, inv_mul_cancel, L3.act_one]
    · intro l b hb
      show L3.act g⁻¹ (D'.b ((l : G) * b * (l : G)⁻¹)) = L3.act (τ3 (D.ρ l)) (L3.act g⁻¹ (D'.b b))
      have e : ∀ x : L3.Γ, g⁻¹ * (g * x * g⁻¹) = x * g⁻¹ := fun x => by group
      rw [D'.equi l b hb, hg l, ← L3.act_mul, ← L3.act_mul, e]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
