module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Basic
import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75

namespace Br37

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem conj_le_Lgen {L : Subgroup G} {m : G} (hm : m ∈ M) : conjSubgroup m L ≤ Lgen M L := by
  unfold Lgen
  exact le_iSup₂_of_le m hm le_rfl

omit [Finite G] in
theorem Lgen_le_of {L P : Subgroup G} (h : ∀ m ∈ M, conjSubgroup m L ≤ P) : Lgen M L ≤ P := by
  unfold Lgen
  exact iSup₂_le h

theorem Lgen_LB_le_H0 (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ H0 M Z := by
  refine Lgen_le_of fun m hm x hx => Subgroup.mem_inf.mpr ⟨conj_le_M hc.LB_le_M hm hx, ?_⟩
  rw [← hc.LB_conj hm] at hx
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  exact (mul_inv_eq_iff_eq_mul.mp ((hc.conj_of_mem hm).LB_centralizes_Z hx z hz)).symm

omit [Finite G] in
theorem nonempty_bar_equiv_range [(Q.subgroupOf M).Normal] {S : Subgroup G} (hSM : S ≤ M)
    {H : Type*} [Group H] (ψ : ↥S →* H) (hψ : ∀ s : S, ψ s = 1 ↔ (s : G) ∈ Q) :
    Nonempty (↥(bar M Q S) ≃* ↥ψ.range) := by
  let f : ↥S →* ↥M ⧸ Q.subgroupOf M :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hSM)
  have hker : f.ker = ψ.ker := by
    ext s
    simp only [f, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion, hψ]
  have hrange : f.range = bar M Q S := by
    simp only [f, bar, MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans <|
    (QuotientGroup.quotientKerEquivRange f).symm.trans <|
      (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange ψ)⟩

theorem nonempty_bar_Lgen_equiv_closure [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {H : Type*} [Group H] (φ : ↥(H0 M Z) →* H) (hφ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) :
    Nonempty (↥(bar M Q (Lgen M (LB M Q B))) ≃* ↥(Subgroup.closure
      {T : H | ∃ m ∈ M, ∃ x : H0 M Z, (x : G) ∈ conjSubgroup m (LB M Q B) ∧ φ x = T})) := by
  have hSH := Lgen_LB_le_H0 hc
  set X : Set H := {T | ∃ m ∈ M, ∃ x : H0 M Z, (x : G) ∈ conjSubgroup m (LB M Q B) ∧ φ x = T}
  have hrange : (φ.comp (Subgroup.inclusion hSH)).range = Subgroup.closure X := by
    refine le_antisymm ?_ ((Subgroup.closure_le _).mpr ?_)
    ·
      have hP : Lgen M (LB M Q B) ≤ ((Subgroup.closure X).comap φ).map (H0 M Z).subtype :=
        Lgen_le_of fun m hm x hx => Subgroup.mem_map.mpr ⟨⟨x, hSH (conj_le_Lgen hm hx)⟩,
          Subgroup.subset_closure ⟨m, hm, ⟨x, hSH (conj_le_Lgen hm hx)⟩, hx, rfl⟩, rfl⟩
      rintro T ⟨s, rfl⟩
      obtain ⟨y, hy, hys⟩ := Subgroup.mem_map.mp (hP s.2)
      rw [MonoidHom.comp_apply, show Subgroup.inclusion hSH s = y from Subtype.ext hys.symm]
      exact hy
    · rintro T ⟨m, hm, x, hx, rfl⟩
      exact ⟨⟨(x : G), conj_le_Lgen hm hx⟩, rfl⟩
  obtain ⟨e⟩ := nonempty_bar_equiv_range (Lgen_le hc.LB_le_M) (φ.comp (Subgroup.inclusion hSH))
    fun s => hφ (Subgroup.inclusion hSH s)
  exact ⟨e.trans (MulEquiv.subgroupCongr hrange)⟩

end Br37

theorem Ctx.bar_Lgen_equiv {G : Type} [Group G] [Finite G]
    {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {K : Type} [Field K]
    [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφ : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) :
    Nonempty (↥(bar M Q (Lgen M (LB M Q B))) ≃*
      ↥(Subgroup.closure {T : M₀.E ≃ₗ[K] M₀.E | ∃ m ∈ M, ∃ x : H0 M Z,
        (x : G) ∈ conjSubgroup m (LB M Q B) ∧ φ x = T})) :=
  Br37.nonempty_bar_Lgen_equiv_closure hc φ hφ

end CFSG.RankThree.GF2n.Stroth80
