module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S28
public import CFSG.Holt.TwoGroupsFocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankTwoShapes (IsAlperinSubgroup AlperinDecomposition alperin_centric_radical_fusion)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem alperinDecomposition_mem_uc6 {p : ℕ} {S P M : Subgroup G}
    (hN : ∀ Q : Subgroup G, IsAlperinSubgroup p S Q → normalizer (Q : Set G) ≤ M) {c : G}
    (hc : AlperinDecomposition p S P c) : c ∈ M := by
  induction hc with
  | one => exact M.one_mem
  | @step c n Q _ hQ _ hn ih => exact M.mul_mem ih (hN Q hQ hn)

theorem fusion_control_of_alperin_uc6 {p : ℕ} [Fact p.Prime] (S : Sylow p G) {M : Subgroup G}
    (hN : ∀ Q : Subgroup G, IsAlperinSubgroup p (S : Subgroup G) Q → normalizer (Q : Set G) ≤ M)
    {x g : G} (hx : x ∈ (S : Subgroup G)) (hg : g * x * g⁻¹ ∈ (S : Subgroup G)) :
    ∃ c ∈ M, g * x * g⁻¹ = c⁻¹ * x * c := by
  have hP : Subgroup.zpowers x ≤ (S : Subgroup G) := Subgroup.zpowers_le.2 hx
  have hPg : (Subgroup.zpowers x).map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom ≤ (S : Subgroup G) := by
    rw [MonoidHom.map_zpowers]
    refine Subgroup.zpowers_le.2 ?_
    simpa [MulAut.conj_apply] using hg
  obtain ⟨c, hc, hcg⟩ := alperin_centric_radical_fusion S hP hPg
  refine ⟨c, alperinDecomposition_mem_uc6 hN hc, ?_⟩
  have := hcg x (Subgroup.mem_zpowers x)
  simpa using this.symm

theorem sylow_le_commutator_of_fusion_uc6 (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] {M : Subgroup G} (S : Sylow p G)
    (hSM : (S : Subgroup G) ≤ M)
    (hfus : ∀ x ∈ (S : Subgroup G), ∀ g : G, g * x * g⁻¹ ∈ (S : Subgroup G) →
      ∃ c ∈ M, g * x * g⁻¹ = c⁻¹ * x * c) :
    (S : Subgroup G) ≤ ⁅M, M⁆ := by
  set U : Subgroup G := (S : Subgroup G) ⊓ (commutator ↥M).map M.subtype with hU
  have hfoc : ∀ x ∈ (S : Subgroup G), ∀ g : G, g * x * g⁻¹ ∈ (S : Subgroup G) →
      x⁻¹ * (g * x * g⁻¹) ∈ U := by
    intro x hx g hgx
    obtain ⟨c, hcM, hc⟩ := hfus x hx g hgx
    refine ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hx) hgx, ?_⟩
    refine ⟨⁅(⟨x⁻¹, M.inv_mem (hSM hx)⟩ : ↥M), (⟨c⁻¹, M.inv_mem hcM⟩ : ↥M)⁆, ?_, ?_⟩
    · rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · rw [hc]
      simp [commutatorElement_def, mul_assoc]
  obtain ⟨N, hN, hNp, hNi, -⟩ := CFSG.Holt.exists_normal_inf_eq_of_focal S inf_le_left hfoc
  haveI := hN
  have hcomm : (commutator ↥M).map M.subtype = ⁅M, M⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rcases hG.eq_bot_or_eq_top_of_normal N with hN0 | hN1
  · exfalso
    have hinj : Function.Injective (QuotientGroup.mk' N) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hN0]
    have hGp : IsPGroup p G := hNp.of_injective _ hinj
    haveI : Nontrivial G := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨⟨a, b, fun h => hab (h ▸ rfl)⟩⟩
    have hcn : Nontrivial (Subgroup.center G) := hGp.center_nontrivial
    rcases hG.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hcn hc
    · obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp this b).symm
  · have h1 : U.relIndex (S : Subgroup G) = 1 := by
      rw [← hNi, hN1]
      exact Subgroup.index_top
    have hSU : (S : Subgroup G) ≤ U := Subgroup.relIndex_eq_one.mp h1
    rw [← hcomm]
    exact hSU.trans inf_le_right

namespace Mc614

variable (c : Mc614 G)

theorem exists_sylow_eq_R : ∃ S : Sylow c.r G, (S : Subgroup G) = c.R := by
  haveI : Fact c.r.Prime := ⟨c.d.prime⟩
  have hRp : IsPGroup c.r c.R := c.d.sylow.isPGroup
  obtain ⟨S, hRS⟩ := hRp.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : c.R < (S : Subgroup G) := lt_of_le_of_ne hRS (fun h => hne h.symm)
  have hNR : normalizer (c.R : Set G) ≤ c.M :=
    c.d.normalizer_le_of_le_pGroup c.hC le_rfl (E_ne_bot c) c.E_le_R hRp
  have hN : c.R < (S : Subgroup G) ⊓ normalizer (c.R : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pGroup_proper_subgroup_lt_internal_normalizer c.r
      c.d.prime (S : Subgroup G) c.R S.isPGroup' hlt
  have hNM : (S : Subgroup G) ⊓ normalizer (c.R : Set G) ≤ c.M := fun x hx => hNR hx.2
  have hNp : IsPGroup c.r ((S : Subgroup G) ⊓ normalizer (c.R : Set G) : Subgroup G) :=
    S.isPGroup'.to_inf_left
  have := c.d.sylow.eq_of_le hN.le hNM hNp
  exact hN.ne this.symm

noncomputable def sylowTop : Sylow c.r G := (c.exists_sylow_eq_R).choose

theorem coe_sylowTop : (c.sylowTop : Subgroup G) = c.R := (c.exists_sylow_eq_R).choose_spec

theorem normalizer_le_of_alperin {Q : Subgroup G}
    (hQ : IsAlperinSubgroup c.r (c.sylowTop : Subgroup G) Q) : normalizer (Q : Set G) ≤ c.M := by
  have hQR : Q ≤ c.R := by
    have := hQ.1
    rwa [c.coe_sylowTop] at this
  have hEQ : c.E ≤ Q := fun e he => by
    have hES : e ∈ (c.sylowTop : Subgroup G) := by
      rw [c.coe_sylowTop]
      exact c.E_le_R he
    refine hQ.2.2.1 (Subgroup.mem_inf.2 ⟨?_, hES⟩)
    rw [mem_centralizer_iff]
    intro q hq
    exact mem_centralizer_iff.1 (c.d.E_le he).2 q (hQR hq)
  exact c.d.normalizer_le_of_le_pGroup c.hC le_rfl (E_ne_bot c) hEQ
    (c.d.sylow.isPGroup.to_le hQR)

theorem fusion_control {x g : G} (hx : x ∈ c.sylowTop) (hg : g * x * g⁻¹ ∈ c.sylowTop) :
    ∃ k ∈ c.M, g * x * g⁻¹ = k⁻¹ * x * k := by
  haveI : Fact c.r.Prime := ⟨c.d.prime⟩
  exact fusion_control_of_alperin_uc6 c.sylowTop (fun Q hQ => c.normalizer_le_of_alperin hQ) hx hg

theorem R_le_commutator : c.R ≤ ⁅c.M, c.M⁆ := by
  haveI : Fact c.r.Prime := ⟨c.d.prime⟩
  have hSM : (c.sylowTop : Subgroup G) ≤ c.M := by
    rw [c.coe_sylowTop]
    exact c.R_le_M
  have := sylow_le_commutator_of_fusion_uc6 c.hS.simple c.hS.nonab c.sylowTop hSM
    (fun x hx g hg => c.fusion_control hx hg)
  rwa [c.coe_sylowTop] at this

end Mc614

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem c627 : m.C627 := m.hZ.le.trans m.toMc614.R_le_commutator

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
