module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Monster.B.TwoA

@[expose] def comapRestrict {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H) :
    K.comap f →* K where
  toFun g := ⟨f g.1, g.2⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' a b := Subtype.ext (map_mul f a.1 b.1)

theorem comapRestrict_surjective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Surjective f) (K : Subgroup H) : Function.Surjective (comapRestrict f K) := by
  intro k
  obtain ⟨g, hg⟩ := hf k
  exact ⟨⟨g, by rw [Subgroup.mem_comap, hg]; exact k.2⟩, Subtype.ext hg⟩

theorem ker_comapRestrict {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup H) :
    (comapRestrict f K).ker = f.ker.subgroupOf (K.comap f) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← Subtype.coe_inj]
  exact Iff.rfl

theorem natCard_comap_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] {f : G →* H}
    (hf : Function.Surjective f) (K : Subgroup H) :
    Nat.card (K.comap f) = Nat.card f.ker * Nat.card K := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((comapRestrict f K).ker)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (comapRestrict_surjective hf K)).toEquiv, ker_comapRestrict] at h1
  have hk : f.ker ≤ K.comap f := fun g hg => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hg]
    exact K.one_mem
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hk).toEquiv, mul_comm]

theorem natCard_ker_comp_of_surjective {G H K : Type*} [Group G] [Group H] [Group K] [Finite G]
    {f : G →* H} {g : H →* K} (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Nat.card (g.comp f).ker = Nat.card f.ker * Nat.card g.ker := by
  have hH : Finite H := Finite.of_surjective f hf
  have hK : Finite K := Finite.of_surjective g hg
  have hgf : Function.Surjective (g.comp f) := by
    rw [MonoidHom.coe_comp]
    exact hg.comp hf
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (g.comp f).ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hgf).toEquiv] at h1
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hf).toEquiv] at h2
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hg).toEquiv] at h3
  have hK0 : 0 < Nat.card K := Nat.card_pos
  rw [h2, h3, mul_assoc] at h1
  exact Nat.eq_of_mul_eq_mul_left hK0 (by rw [← h1]; ring)

theorem le_pCore_of_normal {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} (hN : N.Normal)
    (hp : IsPGroup p N) : N ≤ CFSG.pCore p G :=
  le_sSup ⟨hN, hp⟩

theorem ker_eq_pCore_of_surjective {G H : Type*} [Group G] [Group H] {p : ℕ} {φ : G →* H}
    (hφ : Function.Surjective φ) (hker : IsPGroup p φ.ker) (hH : CFSG.pCore p H = ⊥) :
    φ.ker = CFSG.pCore p G := by
  apply le_antisymm (le_pCore_of_normal φ.normal_ker hker)
  have hn : ((CFSG.pCore p G).map φ).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal φ hφ
  have hp : IsPGroup p ((CFSG.pCore p G).map φ) := CFSG.pCore_isPGroup.map φ
  have hmap : (CFSG.pCore p G).map φ = ⊥ :=
    eq_bot_iff.2 ((le_pCore_of_normal hn hp).trans hH.le)
  rw [← Subgroup.map_eq_bot_iff]
  exact hmap

end CFSG.Monster.B.TwoA
