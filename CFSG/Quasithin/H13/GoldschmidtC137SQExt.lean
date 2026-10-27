module

public import CFSG.Quasithin.H13.GoldschmidtC137SQKg
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.SectionRank CFSG.QuasithinUnique

theorem isPGroup_quotient_of_prod {G : Type} [Group G] {X T L : Subgroup G}
    (hT : IsSylowTwoOf T X) (hprod : ∀ x ∈ X, ∃ l ∈ L, ∃ t ∈ T, x = l * t) (hLX : L ≤ X)
    [(Subgroup.inclusion hLX).range.Normal] :
    IsPGroup 2 (↥X ⧸ (Subgroup.inclusion hLX).range) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨l, hl, t, ht, hx⟩ := hprod x.1 x.2
  obtain ⟨n, hn⟩ := hT.2.1 ⟨t, ht⟩
  refine ⟨n, ?_⟩
  have hxe : x = ⟨l, hLX hl⟩ * ⟨t, hT.1 ht⟩ := Subtype.ext hx
  have hl1 : (QuotientGroup.mk (⟨l, hLX hl⟩ : ↥X) : ↥X ⧸ (Subgroup.inclusion hLX).range) = 1 :=
    (QuotientGroup.eq_one_iff _).2 ⟨⟨l, hl⟩, rfl⟩
  rw [hxe, QuotientGroup.mk_mul, hl1, one_mul, ← QuotientGroup.mk_pow]
  have : (⟨t, hT.1 ht⟩ : ↥X) ^ 2 ^ n = 1 :=
    Subtype.ext (by simpa using congrArg Subtype.val hn)
  rw [this]
  rfl

theorem isKGroupCat_of_ext {X L : Type} [Group X] [Finite X] [Group L] (j : L →* X)
    (hj : Function.Injective j) [j.range.Normal] (hq : IsPGroup 2 (X ⧸ j.range))
    (O : Subgroup L) [O.Normal] (hO : IsPGroup 2 O) (hY : IsKGroupCat (L ⧸ O)) :
    IsKGroupCat X := by
  have : Finite L := Finite.of_injective j hj
  have hOk : IsKGroupCat (QuotientGroup.mk' O).ker := by
    have h2 : IsKGroupCat O := isKGroupCat_of_pGroup hO
    exact IsKGroupCat.of_mulEquiv h2 (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' O))
  have hL : IsKGroupCat L := isKGroupCat_of_ker (QuotientGroup.mk' O) hOk hY
  refine isKGroupCat_of_ker (QuotientGroup.mk' j.range) ?_ (isKGroupCat_of_pGroup hq)
  exact IsKGroupCat.of_mulEquiv hL
    ((MulEquiv.subgroupCongr (QuotientGroup.ker_mk' j.range)).trans
      (MonoidHom.ofInjective hj).symm)

end CFSG.Quasithin.H13.U3.GC137.SQ
