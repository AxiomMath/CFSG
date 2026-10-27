module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvEdgeCentralizer
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecOrthNatIff
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Alg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem isOrthSec_or_isNatSec_of_card_Zv_eq_two (hA : F53Amalgam H M S) {α β : Geo H M}
    (hα : vtype α = false) (hαβ : (graph (H ⊔ M) H M).Adj α β)
    (hz : Zv β ≤ centerOf (stab β)) (h2 : Nat.card (Zv β) = 2) :
    IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α) := by
  have hβn : β ∈ nbrs α := hαβ
  have hαn : α ∈ nbrs β := hαβ.symm
  have hTs : IsSylowTwoOf (stab α ⊓ stab β) (stab α) := sylow_stab_inf_left hA hβn
  have hZQ : Zv α ≤ Qv α := Zv_le_Qv hA α
  have hZT : Zv α ≤ stab α ⊓ stab β := hZQ.trans (isSylowTwoOf_pCoreOf_le hTs)
  have hZα : Zv α ≤ stab α := hZT.trans inf_le_left
  have hconj : ∀ g ∈ stab α, ∀ x ∈ Zv α, g * x * g⁻¹ ∈ Zv α := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hg) x).mp hx
  have hcent := EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_inf_centralizer_edge_eq hA hαβ hz
  have hZβ : Zv β = quasithinOmegaOneCenter (stab α ⊓ stab β) := by
    rw [inf_comm]; exact (Zv_eq_omegaOneCenter_inf hA hαn hz).1
  have hstep : IsChiefStep (stab α) (Zv α) ⊥ (Zv α) := by
    refine ⟨⟨le_rfl, hconj⟩, ⟨bot_le, fun g _ x hx => ?_⟩,
      bot_lt_iff_ne_bot.mpr (Zv_ne_bot hA α), fun K hK _ hKZ => ?_⟩
    · rw [Subgroup.mem_bot] at hx ⊢
      rw [hx]; group
    by_cases hK0 : K = ⊥
    · exact Or.inl hK0
    refine Or.inr (le_antisymm hKZ ?_)
    have hKT : K ≤ stab α ⊓ stab β := hKZ.trans hZT
    have hTK : stab α ⊓ stab β ≤ Subgroup.normalizer (K : Set G) := by
      intro t ht
      refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨fun hk => hK.2 t ht.1 k hk, fun hk => ?_⟩
      have h1 := hK.2 t⁻¹ (Subgroup.inv_mem _ ht.1) _ hk
      simpa [mul_assoc] using h1
    have hne := F53B3.O1.inf_centralizer_ne_bot_of_normalized hTs.2.1 hKT hTK hK0
    have hle : K ⊓ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) ≤ Zv β :=
      hcent ▸ inf_le_inf_right _ hKZ
    have hβK : Zv β ≤ K := by
      have heq := Subgroup.eq_of_le_of_card_ge hle
        (by rw [h2]; exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne)
      exact heq ▸ inf_le_left
    rw [Zv_eq_conjClosure hTs, ← hZβ]
    refine (Subgroup.closure_le K).mpr ?_
    rintro _ ⟨g, hg, z, hz', rfl⟩
    exact hK.2 g hg z (hβK hz')
  have hnc : ¬ IsCentralStep (stab α) ⊥ (Zv α) := by
    intro hc
    apply Zv_ne_bot hA α
    rw [eq_bot_iff, ← centerOf_eq_bot_of_Zv_central hA hαn hz]
    intro x hx
    refine ⟨hZα hx, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have h1 := hc g hg x hx
    rw [Subgroup.mem_bot] at h1
    calc g * x = (g * x * g⁻¹ * x⁻¹) * x * g := by group
      _ = x * g := by rw [h1, one_mul]
  exact (chiefStep_orth_or_nat (quot_stab_five hA hα) hZQ hstep hnc).2

end F53.Stellmacher

end CFSG.Quasithin
