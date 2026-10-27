module

public import CFSG.Timmesfeld.ARS.CaseOADegSetting
public import CFSG.Timmesfeld.Transvection.FrameSubgroup
public import CFSG.Timmesfeld.Transvection.GenerateFrameLarge

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Transvection Sec13Restrict CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOADeg

namespace DegOA

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)} (hD : DegOA R A A₀ Δ₁ Δ₂)
include hD

theorem gen₁_le_levi : gen Δ₁ ≤ levi R A A₀ :=
  Sec9.gen_le_levi fun _ hX => hD.mem_leviSet₁ hX

theorem mem₁_of_le {B : Subgroup G} (hB : B ∈ R) (hBV : B ≤ gen Δ₁) : B ∈ Δ₁ := by
  have hBl := Levi.mem_leviSet_of_le_levi hD.hyp.root hD.mem hD.opp hB (hBV.trans hD.gen₁_le_levi)
  exact (hD.mem_or_mem hBl).resolve_right fun hB₂ => hD.not_le_gen₁ hB₂ hBV

theorem restrict_eq : restrict Δ₁ (gen Δ₁) = restrict R (gen Δ₁) := by
  change (fun B : Subgroup G => B.subgroupOf (gen Δ₁)) '' _ =
    (fun B : Subgroup G => B.subgroupOf (gen Δ₁)) '' _
  congr 1
  ext B
  exact ⟨fun h => ⟨(hD.mem_leviSet₁ h.1).1.1, h.2⟩, fun h => ⟨hD.mem₁_of_le h.1 h.2, h.2⟩⟩

theorem isTransvectionClass : IsTransvectionClass (restrict Δ₁ (gen Δ₁)) := by
  have hR := hD.hyp.root
  obtain ⟨E₀, hE₀, he⟩ := hD.comp₁
  have hE₀₁ : E₀ ∈ Δ₁ := he ▸ Sec9.self_mem_comp A A₀ E₀
  rw [hD.restrict_eq]
  refine ⟨ARS.isRootClass_restrict hR hE₀.1.1 (le_gen hE₀₁) (fun B hB hBV => ?_) ?_, ?_⟩
  · exact Sec9.exists_conjSub_eq hD.hyp hD.comp₁ hE₀₁ (hD.mem₁_of_le hB hBV)
  · exact gen_le fun X hX =>
      le_iSup₂ (f := fun B (_ : B ∈ {B | B ∈ R ∧ B ≤ gen Δ₁}) => B) X
        ⟨(hD.mem_leviSet₁ hX).1.1, le_gen hX⟩
  · rintro _ ⟨X, ⟨hX, hXV⟩, rfl⟩ _ ⟨Y, ⟨hY, hYV⟩, rfl⟩ hs
    rw [special_subgroupOf_iff hXV hYV] at hs
    exact hD.deg X (hD.mem₁_of_le hX hXV) Y (hD.mem₁_of_le hY hYV) hs

theorem pointsDetermined : PointsDetermined (restrict Δ₁ (gen Δ₁)) := by
  have hR := hD.hyp.root
  rintro _ ⟨X, ⟨hX, hXV⟩, rfl⟩ _ ⟨Y, ⟨hY, hYV⟩, rfl⟩ h
  congr 1
  obtain ⟨E₀, hE₀, he⟩ := hD.comp₁
  have hsame : ∀ Z ∈ leviSet R A A₀, Commuting X Z ↔ Commuting Y Z := by
    intro Z hZ
    rcases hD.mem_or_mem hZ with hZ₁ | hZ₂
    · have h' := h _ ⟨Z, ⟨hZ₁, le_gen hZ₁⟩, rfl⟩
      rwa [commuting_subgroupOf_iff' hXV (le_gen hZ₁),
        commuting_subgroupOf_iff' hYV (le_gen hZ₁)] at h'
    · exact ⟨fun _ => hD.commuting_of_mem hY hZ₂, fun _ => hD.commuting_of_mem hX hZ₂⟩
  refine Levi.eq_of_commuting_iff_of_degenerate hD.hyp hD.mem hD.ne hD.opp hE₀ ?_ (he ▸ hX)
    (he ▸ hY) hsame
  rw [← he]
  exact hD.deg

theorem exists_ne_commuting :
    ∃ X ∈ restrict Δ₁ (gen Δ₁), ∃ Y ∈ restrict Δ₁ (gen Δ₁), X ≠ Y ∧ Commuting X Y := by
  have hR := hD.hyp.root
  obtain ⟨E, C, P, Q, hfr, -, h1, h2⟩ := hD.exists_subframe
  have hc : Commuting (P 1) (P 2) := (hfr.commuting 1 2 (by decide)).mono le_sup_left le_sup_left
  have hne : P 1 ≠ P 2 := by
    intro h
    refine (hfr.opposite 2).not_commuting (hR.ne_bot _ (hfr.memP 2).1.1.1) ?_
    rw [← h]
    exact (hfr.commuting 1 2 (by decide)).mono le_sup_left le_sup_right
  exact ⟨_, SubgroupForm.subgroupOf_mem h1.1 (le_gen h1.1), _,
    SubgroupForm.subgroupOf_mem h2.1 (le_gen h2.1),
    fun e => hne ((subgroupOf_inj_of_le (le_gen h1.1) (le_gen h2.1)).1 e),
    (commuting_subgroupOf_iff' (le_gen h1.1) (le_gen h2.1)).2 hc⟩

theorem transvectionHyp
    (hO3 : (∃ X ∈ restrict Δ₁ (gen Δ₁), Nat.card X = 2) →
      ∀ N : Subgroup ↥(gen Δ₁), N.Normal → IsPGroup 3 N → N = ⊥) :
    TransvectionHyp ↥(gen Δ₁) (restrict Δ₁ (gen Δ₁)) := by
  have := hD.hyp.finite
  exact { finite := inferInstance
          cls := hD.isTransvectionClass
          points := hD.pointsDetermined
          center := hD.center_gen_eq_bot
          rank := hD.exists_ne_commuting
          small := fun h2 => small_of_meetsLines hD.isTransvectionClass hD.pointsDetermined
            hD.center_gen_eq_bot hD.exists_ne_commuting
            (SubgroupForm.meetsLines_restrict (fun _ hX => le_gen hX) hD.meetsLines) (hO3 h2) h2 }

theorem tim90
    (hO3 : (∃ X ∈ restrict Δ₁ (gen Δ₁), Nat.card X = 2) →
      ∀ N : Subgroup ↥(gen Δ₁), N.Normal → IsPGroup 3 N → N = ⊥) :
    ∃ f : ℕ, ∃ hf : 1 ≤ f, (∀ X ∈ Δ₁, Nat.card X = 2 ^ f) ∧
      ((∃ Φ : ↥(StatedSp 2 (GaloisField 2 f)) →* G, Function.Injective Φ ∧ Φ.range = gen Δ₁ ∧
          ∀ X : Subgroup G, X ∈ Δ₁ ↔ ∃ g, X = (conjSub ((Symplectic.rootDatum 2
            (GaloisField 2 f)).rootGroup (Pi.single (1 : Fin 2) 1)) g).map Φ) ∨
        (∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 4) →* G,
          Φ.ker = Subgroup.center _ ∧ Φ.range = gen Δ₁ ∧ ∀ X : Subgroup G, X ∈ Δ₁ ↔
            ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) 4).rootGroup
              (unitaryLongRoot 4 (by norm_num))) g).map Φ)) := by
  obtain ⟨E, C, P, Q, hfr, h0, h1, h2⟩ := hD.exists_subframe
  exact subgroupTransvectionStatementFrame_of (transvectionStatementFrame_of_large
    transvectionStatementFrameLarge) G (gen Δ₁) Δ₁ (fun _ hX => le_gen hX) (hD.transvectionHyp hO3)
    hD.meetsLines 2 le_rfl ![P 1, P 2] ![Q 1, Q 2] 1 (hD.isSmallFrame hfr h0 h1 h2)

end DegOA

end CaseOADeg

end CFSG.Timmesfeld.ARS
