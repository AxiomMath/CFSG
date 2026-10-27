module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Frontier7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Sit (H M S : Subgroup G) : Prop where
  glob : S34.Glob H M S
  b5 : 5 ≤ bMin H M
  orth : ∀ δ : Geo H M, vtype δ = false → IsOrthSec (stab δ) (S34.Cb δ) (Vn δ)
  cardZ5 : ∀ δ : Geo H M, vtype δ = false → Nat.card (Zv δ) = 2
  cardZ3 : ∀ l : Geo H M, vtype l = true → Nat.card (Zv l) = 4

theorem Sit.of_orth (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hα : vtype α = true) (hz : ⁅Zv α, Zv α'⁆ = ⊥)
    (ho : IsOrthSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β))
    (hb : 5 ≤ bMin H M) : Sit H M S := by
  have h28 := hss28At_of_hss26A hA h26
  have h34 := hss34At_of_hss26A hA h26 α β α' hc hα hz
  have hG := S34.Glob.of_crit hA h28 hc hα hz
  have hvβ : vtype β = false := by
    cases h : vtype β
    · rfl
    · exact absurd (hα.trans h.symm) (vtype_ne_of_adj hc.adj)
  refine ⟨hG, hb, fun δ hδ => ?_, fun δ hδ => ?_, fun δ hδ => ?_⟩
  · obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hvβ.trans hδ.symm)
    have := IsOrthSec.conj ho (g : G)
    rw [stab_smul, S34.Cb_smul, Vn_smul]
    exact this
  · obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hvβ.trans hδ.symm)
    rw [Zv_smul]
    exact (Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective).trans h34.2.1
  · obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hα.trans hδ.symm)
    rw [Zv_smul]
    exact (Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective).trans h34.1

end S35

end F53.Stellmacher

end CFSG.Quasithin
