module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB19
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB15
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB18

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem aZ_eq_card_img (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ)
    {j : Geo H M} (hj : j ∈ nbrs μ) (hjδ : j ≠ δ) : aZ δ j = Nat.card (fr.img (OoOf j)) := by
  rw [card_img fr (h.Oo_le_stab_at hA hj), inf_comm, ← h.relIndex_Oo_eq hA hj hjδ,
    ← h.relIndex_Zv_eq_Oo hA hj hjδ]
  rfl

theorem img_eq_That_of_a4 (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ)
    {j : Geo H M} (hj : j ∈ nbrs μ) (hjδ : j ≠ δ) (h4 : aZ δ j = 4) :
    fr.img (OoOf j) = S5That := by
  rcases h.classify hA fr hj hjδ with e | e | e
  · have := h.aZ_eq_card_img hA fr hj hjδ
    rw [h4, e, Nat.card_zpowers] at this
    have h2 : orderOf (swap (0 : Fin 5) 2) = 2 :=
      orderOf_eq_prime (by rw [pow_two, Equiv.swap_mul_self]) (fun h => by
        have := Equiv.swap_eq_one_iff.1 h; exact absurd this (by decide))
    omega
  · have := h.aZ_eq_card_img hA fr hj hjδ
    rw [h4, e, Nat.card_zpowers] at this
    have h2 : orderOf (swap (1 : Fin 5) 3) = 2 :=
      orderOf_eq_prime (by rw [pow_two, Equiv.swap_mul_self]) (fun h => by
        have := Equiv.swap_eq_one_iff.1 h; exact absurd this (by decide))
    omega
  · exact e

theorem edge_swap (hA : F53Amalgam H M S) (h : ConfR δ μ U) {V₀ : Subgroup G}
    (hVO : V₀ ≤ OoOf δ)
    (hVZ : V₀ ≤ CFSG.Quasithin.conjClosure (quasithinOmegaOneCenter (Qv μ ⊓ U)) U)
    {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab μ) (hne : ⁅V₀, conjSub (g : G) V₀⁆ ≠ ⊥) :
    g • δ ≠ δ ∧ g • g • δ = δ := by
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  constructor
  · intro hfix
    have hgδ : (g : G) ∈ stab δ := mem_stab_of_smul_eq hfix
    have hO : conjSub (g : G) (OoOf δ) = OoOf δ := by
      rw [← OoOf_smul, hfix]
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hyO : y ∈ OoOf δ := by
      rw [← hO]
      exact conjSub_mono (g : G) hVO hy
    exact h.Oo_comm hA y hyO x (hVO hx)
  · by_contra hb
    have hne1 : g • δ ≠ δ := by
      intro hfix
      apply hne
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      have hO : conjSub (g : G) (OoOf δ) = OoOf δ := by rw [← OoOf_smul, hfix]
      have hyO : y ∈ OoOf δ := by
        rw [← hO]
        exact conjSub_mono (g : G) hVO hy
      exact h.Oo_comm hA y hyO x (hVO hx)
    have hcube := cube_mem_Qv hA (h.vtype_mu hA) hg hδ hne1 hb
    obtain ⟨h1, h2⟩ := h.edge_normalizer hA hVZ hg hne
    have hPN : Qv μ ≤ Subgroup.normalizer (pCoreOf 2 U : Set G) := fun x hx =>
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 U (h.hQ hx)
    apply h2
    have e : (g : G) = ((g ^ 3 : ↥(H ⊔ M)) : G) * (((g : G) * (g : G))⁻¹) := by
      push_cast; group
    rw [e]
    exact (Subgroup.normalizer _).mul_mem (hPN hcube) ((Subgroup.normalizer _).inv_mem h1)

theorem exists_edge (hA : F53Amalgam H M S) (h : ConfR δ μ U) (fr : OrthFrame δ μ)
    {cb : Perm (Fin 5)} (hc : IsThreeCyc cb) {V₀ : Subgroup G}
    (hV : V₀ = (planeOf cb).map fr.γ)
    (h4 : ∀ n ∈ nbrs μ, n ≠ δ → aZ δ n = 4) {n : Geo H M} (hn : n ∈ nbrs μ) (hnδ : n ≠ δ) :
    ∃ g : ↥(H ⊔ M), (g : G) ∈ stab μ ∧ g • δ = n ∧ ⁅V₀, conjSub (g : G) V₀⁆ ≠ ⊥ := by
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  obtain ⟨g0, hg0, hg0n⟩ := stab_transitive_on_nbrs hδ hn
  obtain ⟨s, hs, hsP⟩ := h.exists_edge_not_Qv hA
  set sE : ↥(H ⊔ M) := toGeoElt μ hs.2 with hsE
  have hsδ : sE • δ = δ := smul_eq_of_mem_stab (g := sE) hs.1
  by_contra hcon
  push Not at hcon
  have e0 : ⁅V₀, conjSub (g0 : G) V₀⁆ = ⊥ := hcon g0 hg0 hg0n
  have e1 : ⁅V₀, conjSub ((g0 * sE : ↥(H ⊔ M)) : G) V₀⁆ = ⊥ :=
    hcon (g0 * sE) ((stab μ).mul_mem hg0 hs.2) (by rw [mul_smul, hsδ, hg0n])
  have hOn : OoOf n = conjSub (g0 : G) V₀ ⊔ conjSub ((g0 * sE : ↥(H ⊔ M)) : G) V₀ := by
    rw [← hg0n, OoOf_smul, ← h.Oo_eq_sup fr hc hV hs.1 hs.2 hsP, conjSub_sup]
    push_cast
    rw [conjSub_mul]
    rfl
  have hcen : OoOf n ≤ Subgroup.centralizer (V₀ : Set G) := by
    rw [hOn]
    refine sup_le ?_ ?_
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]; exact e0
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]; exact e1
  have himg := h.img_eq_That_of_a4 hA fr hn hnδ (h4 n hn hnδ)
  have hmem : swap (0 : Fin 5) 2 * swap 1 3 ∈ fr.img (OoOf n) := by
    rw [himg, mem_S5That_iff, O2.mem_S5ThatF_iff_eq]
    exact Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨k, hk, hkΨ⟩ := hmem
  have hkO : (k : G) ∈ OoOf n := Subgroup.mem_subgroupOf.mp hk
  have hkP : (k : G) ∈ Qv μ := h.Oo_le_Qv_mu_at hA hn hkO
  have := h.centralizes_V0 fr hc hV k hkP (fun v hv =>
    (Subgroup.mem_centralizer_iff.mp (hcen hkO) v hv).symm)
  rw [hkΨ, mem_zpowers_of_sq (by decide +kernel), mem_zpowers_of_sq (by decide +kernel)] at this
  revert this
  decide +kernel

end ConfR

end CFSG.Quasithin.F53
