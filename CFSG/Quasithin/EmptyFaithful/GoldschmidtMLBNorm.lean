module

public import CFSG.Quasithin.Background.C2A3Orbits

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace GoldMLB

section Abstract

variable {Q : Type} [Group Q] [Finite Q]

theorem normal_of_not_a38 (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    (hQ : SQTKGroup Q) {L : Subgroup Q} (hL : L ∈ cComp (⊤ : Subgroup Q))
    (hnot : ¬ A38Types ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 Q)))) : L.Normal := by
  classical
  have hGb : SQTKHyp (Q ⧸ CFSG.pCore 2 Q) := SQTKHyp.of_sqtkGroup Q hQ
  have h38 := hA38 _ hGb
  have hNsolv : Group.IsSolvable (CFSG.pCore 2 Q) := by
    have := (CFSG.pCore_isPGroup (G := Q) (p := 2)).isNilpotent
    infer_instance
  have hbij := cComp_quotient_bijOn (CFSG.pCore 2 Q) hNsolv
  set π : Q →* Q ⧸ CFSG.pCore 2 Q := QuotientGroup.mk' (CFSG.pCore 2 Q) with hπ
  have hLb : L.map π ∈ cComp (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) := hbij.mapsTo hL
  have hnormb : (L.map π).Normal := by
    rcases (h38 (L.map π) hLb).1 with h | ⟨hA, -⟩
    · exact h
    · exact absurd hA hnot
  refine ⟨fun n hn g => ?_⟩
  have hc := C2A3Orbits.conj_mem_cComp_top hL g
  have himg : (L.map (MulAut.conj g).toMonoidHom).map π = L.map π := by
    rw [← C2A3Orbits.map_conj_map π L g]
    refine A38.map_conj_eq_iff.mpr ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr hnormb]
    exact Subgroup.mem_top _
  have heq : L.map (MulAut.conj g).toMonoidHom = L := hbij.injOn hc hL himg
  have hmem : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
    ⟨n, hn, by simp [MulAut.conj_apply]⟩
  rwa [heq] at hmem

end Abstract

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem normalizes_of_not_a38 (hA38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y)
    {X L : Subgroup G} (hX : IsSQTKIn X) (hL : L ∈ cComp X)
    (hnot : ¬ A38Types ↥((L.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)))) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hL' : L.subgroupOf X ∈ cComp (⊤ : Subgroup ↥X) := (cComp_subgroupOf_bijOn X).mapsTo hL
  have hnorm := normal_of_not_a38 hA38 hX hL' hnot
  intro g hg
  have h := (C2A3Orbits.mem_normalizer_map_subtype X (L.subgroupOf X) ⟨g, hg⟩).mpr
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]; exact Subgroup.mem_top _)
  rwa [Subgroup.map_subgroupOf_eq_of_le hLX] at h

end Ambient

end GoldMLB

end CFSG.Quasithin
