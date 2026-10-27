module

public import CFSG.OddTranspositions.PartThree.Statements
import CFSG.OddTranspositions.SevenOne
import CFSG.OddTranspositions.BlockGraph
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
import CFSG.Timmesfeld.Bridge.OddTranspSecondKind
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
import CFSG.Walter.Defs

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem mem_Dalpha_of_commute_mem (hN : IsNormalSet D) (hodd : IsOddTransp D)
    {α β γ : Set G} (hα : IsBlock D α) (hβ : β ∈ blockClass α)
    (hγ : γ ∈ blockClass α) (hne : β ≠ γ) {x y : G} (hx : x ∈ β) (hy : y ∈ γ)
    (hxy : Commute x y) : γ ∈ Dalpha D β := by
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hN hα hβ
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp (mem_blockClass_of_mem_blockClass hβ hγ)
  refine mem_Dalpha_iff.mpr ⟨mem_blockClass_of_mem_blockClass hβ hγ,
    subset_of_mem_blockClass hN hα hγ, hne.symm, ?_⟩
  have hne' : (fun z => g * z * g⁻¹) '' β ≠ β := by
    rw [← hg]
    exact hne.symm
  rw [hg] at hy
  rw [hg]
  intro a ha b hb
  exact commute_block_of_mem_apply hN hodd hβblock hne' hx hy hxy a ha b hb

theorem exists_commute_of_commute_chain_of_thirdKind (hS : Setup G D)
    (h85 : ∀ u w v : G, IsTriangle D u w v → IsThirdKind u w v →
      ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w)
    {p₀ p₁ p₂ p₃ : G} (h₀ : p₀ ∈ D) (h₁ : p₁ ∈ D) (h₂ : p₂ ∈ D) (h₃ : p₃ ∈ D)
    (h01 : Commute p₀ p₁) (h12 : Commute p₁ p₂) (h23 : Commute p₂ p₃) :
    ∃ e ∈ D, Commute e p₀ ∧ Commute e p₃ := by
  classical
  by_cases h02 : Commute p₀ p₂
  · exact ⟨p₂, h₂, h02.symm, h23⟩
  by_cases h03 : Commute p₀ p₃
  · exact ⟨p₀, h₀, Commute.refl p₀, h03⟩
  by_cases h13 : Commute p₁ p₃
  · exact ⟨p₁, h₁, h01.symm, h13⟩
  have hne23 : p₂ ≠ p₃ := by
    intro h
    exact h13 (by simpa [h] using h12)
  have htri : IsTriangle D p₂ p₀ p₃ :=
    ⟨h₂, h₃, h₀, hne23, h23, fun h => h02 h.symm, fun h => h03 h.symm⟩
  rcases htri.orderOf_cases hS.oddT hS.normal with ⟨hodd, -⟩ | h4 | hthird
  ·
    have hmem : p₂ * p₃ ∈ D := htri.mul_mem_of_odd hS.oddT hS.normal hodd
    have hcent := centralizer_eq_of_mul_mem hS h₂ h₃ hne23 h23 hmem
    have hp1 : p₁ ∈ D ∩ Subgroup.centralizer ({p₂} : Set G) :=
      ⟨h₁, Subgroup.mem_centralizer_singleton_iff.mpr h12⟩
    have hp1' : p₁ ∈ D ∩ Subgroup.centralizer ({p₃} : Set G) := by
      rwa [hcent.1] at hp1
    exact absurd (Subgroup.mem_centralizer_singleton_iff.mp hp1'.2) h13
  ·
    by_cases hx : ∃ x ∈ D, x ∈ Subgroup.closure ({p₂, p₀} : Set G) ∧
        IsTriangle D p₂ x p₃ ∧ IsThirdKind p₂ x p₃
    · obtain ⟨x, hxD, hxcl, htri_x, hthird_x⟩ := hx
      obtain ⟨e, heD, he2, he3, hex⟩ := h85 p₂ x p₃ htri_x hthird_x
      have he0 : Commute e p₀ :=
        CFSG.Timmesfeld.Bridge.OddLocal.commute_of_commute_of_mem_closure
          hS.oddT h₂ h₀ (fun h => h02 h.symm) hxD hxcl
          htri_x.2.2.2.2.2.1 heD he2 hex
      exact ⟨e, heD, he0, he3⟩
    · have hno : ∀ x ∈ D, x ∈ Subgroup.closure ({p₂, p₀} : Set G) →
          IsTriangle D p₂ x p₃ → ¬ IsThirdKind p₂ x p₃ := by
        intro x hxD hxcl htri_x hthird_x
        exact hx ⟨x, hxD, hxcl, htri_x, hthird_x⟩
      have hstr : CFSG.Timmesfeld.Bridge.SecondKindStructure p₂ p₀ p₃ :=
        CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure
          hS.oddT hS.normal htri h4 hno
      obtain ⟨y, hy, hyconj⟩ := hstr.conj
      let e : G := y * p₁ * y⁻¹
      have heD : e ∈ D := hS.normal y p₁ h₁
      have hy0 : Commute y p₀ :=
        Subgroup.mem_centralizer_singleton_iff.mp (hstr.le_centralizer hy)
      have he0 : Commute e p₀ := by
        have hconj := (h01.conj y).symm
        have hy0eq : y * p₀ * y⁻¹ = p₀ := by
          rw [hy0.eq, mul_assoc, mul_inv_cancel, mul_one]
        rwa [hy0eq] at hconj
      have he3 : Commute e p₃ := by
        have hconj := h12.conj y
        rwa [hyconj] at hconj
      exact ⟨e, heD, he0, he3⟩
  ·
    obtain ⟨e, heD, -, he3, he0⟩ := h85 p₂ p₀ p₃ htri hthird
    exact ⟨e, heD, he0, he3⟩

theorem exists_commute_commute_of_thirdKind (hS : Setup G D) (hconn : ¬ Disconnected D)
    (h85 : ∀ u w v : G, IsTriangle D u w v → IsThirdKind u w v →
      ∃ d ∈ D, Commute d u ∧ Commute d v ∧ Commute d w) :
    ∀ x ∈ D, ∀ y ∈ D, ∃ e ∈ D, Commute e x ∧ Commute e y := by
  intro x hx y hy
  have hreach : Reach D x y :=
    CFSG.OddTranspositions.reach_of_not_disconnected hconn hx hy
  induction hreach with
  | refl => exact ⟨x, hx, Commute.refl x, Commute.refl x⟩
  | tail _ hbc ih =>
    obtain ⟨e, heD, hex, hey⟩ := ih hbc.1
    exact exists_commute_of_commute_chain_of_thirdKind hS h85 hx heD hbc.1 hbc.2.1
      hex.symm hey hbc.2.2

theorem exists_commute_commute (h85 : Theorem8_5) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D) :
    ∀ x ∈ D, ∀ y ∈ D, ∃ e ∈ D, Commute e x ∧ Commute e y :=
  exists_commute_commute_of_thirdKind hC.setup hC.conn (h85 G D hC hrad hO4)

theorem theorem8_7_of_theorem8_5 (h85 : Theorem8_5) : Theorem8_7 := by
  unfold Theorem8_7
  intro G _ _ D hC hrad hO4 β hβ γ hγ
  by_cases hβγ : β = γ
  · exact Or.inl hβγ
  right
  obtain ⟨x, hxβ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hβ
  obtain ⟨y, hyγ⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ
  have hxD : x ∈ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hβ hxβ
  have hyD : y ∈ D := subset_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ hyγ
  obtain ⟨e, heD, hex, hey⟩ := exists_commute_commute h85 hC hrad hO4 x hxD y hyD
  obtain ⟨ε, hεclass, heε⟩ :=
    exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha heD
  by_cases hεβ : ε = β
  ·
    have hγDα : γ ∈ Dalpha D β :=
      mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hβ hγ hβγ
        (hεβ ▸ heε) hyγ hey
    exact Or.inl hγDα
  by_cases hεγ : ε = γ
  ·
    have hγDα : γ ∈ Dalpha D β :=
      mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hβ hγ hβγ
        hxβ (hεγ ▸ heε) hex.symm
    exact Or.inl hγDα
  ·
    have hεDβ : ε ∈ Dalpha D β :=
      mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hβ hεclass
        (fun h => hεβ h.symm) hxβ heε hex.symm
    have hεDγ : ε ∈ Dalpha D γ :=
      mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hγ hεclass
        (fun h => hεγ h.symm) hyγ heε hey.symm
    exact Or.inr ⟨ε, hεDβ, hεDγ⟩

end CFSG.OddTranspositions.PartThree
