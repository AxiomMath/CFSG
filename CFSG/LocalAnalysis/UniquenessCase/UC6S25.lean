module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S19
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.UniquenessCase.UC6End
public import CFSG.LocalAnalysis.UniquenessCase.UC6S35

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

theorem isElemAbelian_subgroupOf_uc6 {G : Type*} [Group G] {p : ℕ} {K E : Subgroup G}
    (hEK : E ≤ K) (hE : CFSG.Open.IsElemAbelian p E) :
    CFSG.Open.IsElemAbelian p (E.subgroupOf K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · refine Subtype.ext (Subtype.ext ?_)
    have := hE.1.is_comm.comm ⟨(a : K).1, a.2⟩ ⟨(b : K).1, b.2⟩
    show ((a : K).1 * (b : K).1 : G) = (b : K).1 * (a : K).1
    exact congrArg Subtype.val this
  · apply Subtype.ext
    have := hE.2 (x : K).1 hx
    simpa using this

theorem pRank_map_subtype_uc6 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (K : Subgroup G) (H : Subgroup ↥K) :
    CFSG.Open.pRank p (H.map K.subtype) = CFSG.Open.pRank p H := by
  apply le_antisymm
  · obtain ⟨E, hEH, hEel, hEcard⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (H.map K.subtype)
    have hEK : E ≤ K := fun x hx => by
      obtain ⟨h, -, rfl⟩ := hEH hx
      exact h.2
    have hcard' : Nat.card (E.subgroupOf K) = p ^ CFSG.Open.pRank p (H.map K.subtype) := by
      rw [← hEcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
    have hle : E.subgroupOf K ≤ H := fun x hx => by
      obtain ⟨h, hh, hhx⟩ := hEH hx
      have : h = x := Subtype.ext hhx
      exact this ▸ hh
    exact le_pRank_of_elemAbelian hp hle (isElemAbelian_subgroupOf_uc6 hEK hEel) hcard'
  · obtain ⟨E, hEH, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp H
    exact le_pRank_of_elemAbelian hp (Subgroup.map_mono hEH) (IsElemAbelian.map hEel K.subtype)
      (by rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard])

theorem mem_conjugate_iff_uc6 {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def C623 : Prop := IsWeaklyClosedIn m.Z m.R

theorem conj_mem_K {g x : G} (hg : g ∈ m.M) (hx : x ∈ m.K) : g * x * g⁻¹ ∈ m.K := by
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ m.K) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨h, hh, z, hz, rfl⟩
    refine subset_closure ⟨g * h, m.M.mul_mem hg hh, z, hz, ?_⟩
    group
  · simp
  · intro a b _ _ ha hb
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]; exact m.K.mul_mem ha hb
  · intro a _ ha
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]; exact m.K.inv_mem ha

theorem K_eq_map_normalClosure :
    m.K = (Subgroup.normalClosure ((m.Z.subgroupOf m.M : Subgroup ↥m.M) : Set ↥m.M)).map
      m.M.subtype := by
  apply le_antisymm
  · refine (closure_le _).2 ?_
    rintro _ ⟨g, hg, z, hz, rfl⟩
    refine ⟨(⟨g, hg⟩ : ↥m.M) * ⟨z, m.Z_le_M hz⟩ * (⟨g, hg⟩ : ↥m.M)⁻¹, ?_, by simp⟩
    exact (Subgroup.normalClosure_normal).conj_mem _
      (Subgroup.subset_normalClosure (show (⟨z, m.Z_le_M hz⟩ : ↥m.M) ∈ m.Z.subgroupOf m.M from hz))
      _
  · rw [Subgroup.map_le_iff_le_comap]
    haveI : (m.K.comap m.M.subtype).Normal :=
      ⟨fun n hn g => by
        have := m.conj_mem_K g.2 (show (n : G) ∈ m.K from hn)
        show ((g * n * g⁻¹ : ↥m.M) : G) ∈ m.K
        simpa using this⟩
    refine Subgroup.normalClosure_le_normal ?_
    intro x hx
    exact m.Z_le_K hx

theorem three_lt_r' (h625 : m.r = 3 → m.C625) (h629 : m.C629) (h634 : m.r = 3 → m.C634) :
    3 < m.r := by
  by_cases h3 : m.r = 3
  · exact m.three_lt_r (h625 h3) h629 (h634 h3)
  · have hr2 : m.r ≠ 2 := m.d.odd
    have := m.hr.two_le
    omega

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
