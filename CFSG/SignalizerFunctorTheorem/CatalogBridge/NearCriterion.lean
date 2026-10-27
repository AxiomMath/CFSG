module

public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.NearPSolvable

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem nearPSolvable_of_proper_solvable {p : ℕ} {Y : Type*} [Group Y] [Finite Y]
    [IsSimpleGroup Y] (hcop : Nat.Coprime p (Nat.card Y)) (hmodel : signalizerNearSimpleModel p Y)
    (hproper : ∀ H : Subgroup Y, H ≠ ⊤ → Group.IsSolvable H) : signalizerNearPSolvable p Y := by
  refine ⟨hcop, ?_⟩
  intro K L hLK hnorm hsimple hnonab
  by_cases hK : K = ⊤
  · subst hK
    have hLn : L.Normal := by
      have h := hnorm.map (⊤ : Subgroup Y).subtype (fun y => ⟨⟨y, trivial⟩, rfl⟩)
      rwa [Subgroup.map_subgroupOf_eq_of_le hLK] at h
    have := hLn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hL | hL
    · subst hL
      let e : (⊤ : Subgroup Y) ⧸ (⊥ : Subgroup Y).subgroupOf ⊤ ≃* Y :=
        (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := ⊤))).trans
          (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
      exact TransportA.nearSimpleModel_of_mulEquiv e.symm hmodel
    · exfalso
      subst hL
      have : Subsingleton ((⊤ : Subgroup Y) ⧸ (⊤ : Subgroup Y).subgroupOf ⊤) := by
        rw [Subgroup.subgroupOf_self]
        exact QuotientGroup.subsingleton_quotient_top
      exact hsimple.toNontrivial.exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)
  · exfalso
    have hsolvK : Group.IsSolvable K := hproper K hK
    have : Group.IsSolvable (K ⧸ L.subgroupOf K) :=
      Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
