module

public import CFSG.OddTranspositions.TheoremTwo.ThirdKindExclusion
import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralBlocks
import CFSG.OddTranspositions.SixSeven

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem isThirdKind_conj {u w v : G} (h : IsThirdKind u w v) (g : G) :
    IsThirdKind (g * u * g⁻¹) (g * w * g⁻¹) (g * v * g⁻¹) := by
  obtain ⟨n, hn, hn1, hord⟩ := h
  refine ⟨n, hn, hn1, ?_⟩
  have e : g * u * g⁻¹ * (g * v * g⁻¹) * (g * w * g⁻¹) = g * (u * v * w) * g⁻¹ := by group
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (u * v * w)
  rw [e, ← hord]
  simpa [MulAut.conj_apply] using h

theorem diffBlockStatement_holds : DiffBlockStatement := by
  intro G _ _ D hC hrad hL ⟨u, w, v, htri, h3⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj htri.1 hC.hd)
  have htri' := isTriangle_conj hC.setup.normal (g := g) htri
  rw [hg] at htri'
  obtain ⟨n, hn, hn1, hord⟩ := isThirdKind_conj h3 g
  rw [hg] at hord
  have htrans : ∀ x ∈ centSet D ((hC.d * (g * v * g⁻¹) * (g * w * g⁻¹)) ^ n),
      ∃ k ∈ localGroup D ((hC.d * (g * v * g⁻¹) * (g * w * g⁻¹)) ^ n), k * hC.d * k⁻¹ = x := by
    intro x hx
    rw [← Delta_eq_centSet] at hx
    obtain ⟨k, hk, hkx⟩ := thirdK_transitive hC.setup hL htri' hn hord x hx
    rw [thirdK_eq_localGroup] at hk
    exact ⟨k, hk, hkx⟩
  obtain ⟨v', hv', htri'', m, hm, hm1, hordm, -⟩ :=
    exists_thirdKind_mem_DalphaStar hC hrad hC.d_mem_alpha htri' hn hn1 hord rfl htrans
  exact ⟨_, v', htri'', ⟨m, hm, hm1, hordm⟩, hv'⟩

end CFSG.OddTranspositions
