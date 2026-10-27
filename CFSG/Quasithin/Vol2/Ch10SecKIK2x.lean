module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2w
public import CFSG.Quasithin.Vol2.Ch10SecKIK2v

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace C10KH

@[expose] def FactK2Torus : Prop :=
  AsB56 → A36ForSQTK →
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H R J L V₁ V : Subgroup Γ) (hV : IsElemAbelian 2 V),
    S5Core H R J L V hV → V₁ ≤ L → IsElemAbelian 2 V₁ →
    L ⊔ R ≤ Subgroup.normalizer (V₁ : Set Γ) → ⁅V₁, L⁆ = V₁ →
    pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set Γ) →
    J ⊓ Subgroup.normalizer (V₁ : Set Γ) ≤ Subgroup.normalizer (L : Set Γ) → ModCase L V₁ →
    V₁ ≤ V → ∀ n : ℕ, 1 < n →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    A312C2 (modO2Image J L) ⊤ → GoodLie ↥(⊤ : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)) →
    B56QuasisimpleList ↥(autI hV J) →
    ∃ y ∈ J ⊓ Subgroup.normalizer (V₁ : Set Γ), y ∉ Subgroup.centralizer (V₁ : Set Γ) ∧
      (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ)) ∧
      y ^ (2 ^ n - 1) ∈ Subgroup.centralizer (V₁ : Set Γ)

end C10KH

open C10KH

theorem factK2_of (h56 : AsB56) (h312 : Vol2Native.A312ListFactsCat) (h36 : A36ForSQTK)
    (hT : FactK2Torus) : FactK2 := by
  intro Γ _ _ H R J L V₁ V hV hc hV₁L hV₁e hLRN hcomm hO2L hNJ hmod
  obtain ⟨hq, h⟩ := factK2_cases h36 h56 h312 hc hmod
  refine ⟨hq, ?_⟩
  rcases h with ⟨n, hn, F, hF, hFin, hFc, he, hC2, hG⟩ | hb | hcc
  · refine Or.inl ⟨n, hn, F, hF, hFin, hFc, he, fun hV₁V => ?_⟩
    obtain ⟨hJH, -, -, h2, -⟩ := s5_basic hc
    have hlist := b56List_autI h56 hV hc.1 hc.2.2.1 hc.2.2.2.2.2.2.2.1 hJH hc.2.2.2.2.1 h2
      (isQuasisimple_of_open hc.2.2.2.2.2.2.2.2.2.1) hc.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨y, hy, hyV, hyL, hyq⟩ := hT h56 h36 Γ H R J L V₁ V hV hc hV₁L hV₁e hLRN hcomm hO2L
      hNJ hmod hV₁V n hn ⟨F, hF, hFin, hFc, he⟩ hC2 hG hlist
    have hLN : L ≤ Subgroup.normalizer (V₁ : Set Γ) := le_sup_left.trans hLRN
    have hLV : ¬ L ≤ Subgroup.centralizer (V₁ : Set Γ) := by
      intro hLC
      apply hyV
      have hbot : V₁ = ⊥ := by
        rw [← hcomm]
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer).2 (fun v hv => by
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          exact (Subgroup.mem_centralizer_iff.mp (hLC hl) v hv).symm)
      rw [hbot]
      intro v hv
      rw [(Subgroup.mem_bot).1 hv, one_mul, mul_one]
    exact exists_torus_of_scalar hV₁e (by omega) hLN hNJ hO2L hc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hLV hy hyV hyL hyq
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hcc)

end CFSG.Quasithin.Vol2.Ch10.SecC
