module

public import CFSG.Quasithin.EmptyFaithful.S153XBlkB

public section

namespace CFSG.Quasithin.X1469

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Blk.Ctx

variable {I S Iz K₁ K₂ : Subgroup G} {P : AppC.A5Pi K₁} {p : Fin 5} (X : Ctx I S Iz K₁ K₂ P p)
include X

theorem exists_c₁ : ∃ c₁ ∈ K₁ ⊓ Iz, Odd (orderOf c₁) ∧ P.toPiData.pf c₁ = gam p := by
  obtain ⟨hs, hfix, h3⟩ := gam_spec p
  obtain ⟨g, hg⟩ := A5Cfg.exists_lift P (gam p) hs
  have hgIz := X.cfg.lift_mem_Iz P X.hp hfix g hg
  obtain ⟨k, hodd, hk3⟩ := A5Cfg.exists_odd_power (g : G)
  have hN : (g : G) ∈ Subgroup.normalizer (K₁ : Set G) := Subgroup.le_normalizer g.2
  have hgk : (g : G) ^ k ∈ Subgroup.normalizer (K₁ : Set G) := (Subgroup.normalizer _).pow_mem hN k
  refine ⟨(g : G) ^ k, ⟨K₁.pow_mem g.2 k, Iz.pow_mem hgIz k⟩, hodd, ?_⟩
  rw [P.toPiData.pf_eq hgk]
  have e : (⟨(g : G) ^ k, hgk⟩ : ↥(Subgroup.normalizer (K₁ : Set G))) = ⟨(g : G), hN⟩ ^ k := rfl
  have hπ : P.π ⟨(g : G), hN⟩ = gam p := by
    rw [← P.toPiData.pf_eq hN, pf_eq_toPerm P g.2]
    exact hg
  rw [e, map_pow, hπ, pow_eq_pow_mod k h3, hk3, pow_one]

theorem blockFacts {c₁ : G} (hc₁ : c₁ ∈ K₁ ⊓ Iz) (hodd : Odd (orderOf c₁))
    (hpf : P.toPiData.pf c₁ = gam p) : BlockFacts S Iz K₁ c₁ where
  mem := hc₁
  odd := hodd
  Y_le_N_B := X.Y_le_N_B
  card_E := X.card_E
  card_Z := X.card_Z
  Z_le_E := X.Z_le_E
  faith_E := X.faith_E
  irred_E := X.irred_E
  fix_E := X.fix_E
  irred_B := X.irred_B
  fix_B := X.fix_B hc₁ hpf
  gen_B := X.gen_B hc₁.1 hpf
  cent_B := X.cent_B hc₁.1 hpf
  centmod_B := X.centmod_B hc₁.1 hpf

end Blk.Ctx

theorem exists_blockFacts {I S Iz K₁ K₂ : Subgroup G} (c : A5Cfg I S Iz K₁ K₂)
    (hnot : ¬ K₁ ≤ Iz)
    (hD : S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) = ⊥) :
    ∃ c₁ : G, BlockFacts S Iz K₁ c₁ := by
  obtain ⟨α, hα, hαk, -⟩ := c.a5₁
  obtain ⟨P, -⟩ := AppC.exists_a5pi c.blk₁.1 c.a5₁ α hα hαk
  obtain ⟨p, hp⟩ := exists_fixed (α := P.α) c.sylow₁
  have X : Blk.Ctx I S Iz K₁ K₂ P p := ⟨c, hnot, hD, hp⟩
  obtain ⟨c₁, hc₁, hodd, hpf⟩ := X.exists_c₁
  exact ⟨c₁, X.blockFacts hc₁ hodd hpf⟩

end CFSG.Quasithin.X1469
