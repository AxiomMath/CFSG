module

public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_conjBy_le_of_isPGroup {G T' B : Subgroup (MulAut V)} (hT : IsSylowTwoOf T' G)
    (hBG : B ≤ G) (hB : IsPGroup 2 B) : ∃ g ∈ G, conjBy g B ≤ T' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 ↥G := A4.toSylow hT
  have hB' : IsPGroup 2 (B.subgroupOf G) := A4.isPGroup_subgroupOf_of_le hBG hB
  obtain ⟨Q, hQ⟩ := hB'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥G) Q P
  refine ⟨(g : MulAut V), g.2, ?_⟩
  rintro x ⟨b, hb, rfl⟩
  have hbG : b ∈ G := hBG hb
  have hbQ : (⟨b, hbG⟩ : ↥G) ∈ (Q : Subgroup ↥G) := hQ hb
  have h1 : ((g • Q : Sylow 2 ↥G) : Subgroup ↥G) =
      (Q : Subgroup ↥G).map (MulAut.conj g).toMonoidHom := rfl
  have h2 : (MulAut.conj g) ⟨b, hbG⟩ ∈ ((g • Q : Sylow 2 ↥G) : Subgroup ↥G) := by
    rw [h1]
    exact ⟨_, hbQ, rfl⟩
  rw [hg] at h2
  have h3 : (MulAut.conj g) ⟨b, hbG⟩ ∈ T'.subgroupOf G := by
    have := A4.toSylow_coe hT
    rw [← this]
    exact h2
  exact h3

theorem exists_qhatStar_le_sylow {G T' : Subgroup (MulAut V)} (hT : IsSylowTwoOf T' G)
    (hq : qhatOf G ≤ ((2 : ℚ) : WithTop ℚ)) : ∃ A ∈ QhatStar G, A ≤ T' := by
  have hne : qhatOf G ≠ ⊤ := (hq.trans_lt (WithTop.coe_lt_top _)).ne
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hr2 : r ≤ 2 := by
    rw [← hr] at hq
    exact WithTop.coe_le_coe.mp hq
  obtain ⟨B, hB⟩ := QhatStar_nonempty hr.symm hr2
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hB
  obtain ⟨g, hgG, hgB⟩ := exists_conjBy_le_of_isPGroup hT hA2.le hA2.isElemAbelian2.isPGroup
  exact ⟨conjBy g B, conjBy_mem_QhatStar hB hgG, hgB⟩

end CFSG.Quasithin
