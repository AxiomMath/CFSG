module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34C3b

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
variable {δ δ' : Geo H M}

theorem c3_bMin_ne_three (hG : Glob H M S) (hirr : IrrSecSec) (h15 : Hss15Sec) (hng : NG H M)
    (hp : PD δ δ') : bMin H M ≠ 3 := by
  intro hb
  have hd : dist δ δ' = 1 + 1 := by have := hp.dist_eq; omega
  obtain ⟨γ, hγ', hγd⟩ := exists_adj_dist_eq (rfl : H ⊔ M = H ⊔ M) (α := δ) (δ := δ') hd
  have hγ : (graph (H ⊔ M) H M).Adj δ γ := dist_eq_one_iff_adj.mp hγd
  have hvγ : vtype γ = true := by
    have h := vtype_ne_of_adj hγ
    rw [hp.vδ] at h
    simpa using h
  have hne : δ ≠ δ' := by
    intro h
    rw [h, CosetGeom.dist_self] at hd
    omega
  have hz : Zv δ ≤ centerOf (stab δ) := hG.central δ hp.vδ
  have h := (EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_sup_eq_and_inf_eq_bot
    hG.amalg hvγ (hG.crit γ hvγ) (β := δ) (γ := δ')
    (show δ ∈ nbrs γ from hγ.symm) (show δ' ∈ nbrs γ from hγ'.symm) hne hz).2
  have h2 := (c3_E_le_two hG hirr h15 hng hp).1
  have h4 := c3_card_Zv hG hirr h15 hng hp
  rw [h] at h2
  have : (⊥ : Subgroup G).relIndex (Zv δ) = Nat.card (Zv δ) := by
    simp [Subgroup.relIndex_bot_left]
  omega

end S34

end F53.Stellmacher

end CFSG.Quasithin
