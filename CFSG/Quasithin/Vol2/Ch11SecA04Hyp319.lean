module

public import CFSG.Quasithin.Vol2.Ch11SecA04NatSum
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A3Structure319Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped Matrix

variable {G : Type} [Group G]

theorem isElemAbelian_subgroupOf {V H : Subgroup G} (hV : IsElemAbelian 2 V) :
    IsElemAbelian 2 (V.subgroupOf H) := CFSG.Open.IsElemAbelian.subgroupOf hV H

@[expose] noncomputable def quotPCoreSubgroupOfEquiv {L H : Subgroup G} (hLH : L ≤ H) :
    (↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hLH) (by
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.subgroupOfEquivOfLe hLH)
    exact this)

theorem quotPCoreSubgroupOfEquiv_mk {L H : Subgroup G} (hLH : L ≤ H) (l : ↥(L.subgroupOf H)) :
    quotPCoreSubgroupOfEquiv hLH (QuotientGroup.mk l) =
      QuotientGroup.mk (Subgroup.subgroupOfEquivOfLe hLH l) :=
  rfl

theorem natOn_subgroupOf {H L W : Subgroup G} (hLH : L ≤ H) (hWH : W ≤ H)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) {K : Type} [Field K]
    {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)} (h : NatOn L W K φ) :
    ∃ θ : ↥(W.subgroupOf H) ≃* Multiplicative (Fin 3 → K),
      ∀ (l : ↥(L.subgroupOf H)) (v : ↥(W.subgroupOf H)),
        ∃ v' : ↥(W.subgroupOf H), (v' : ↥H) = (l : ↥H) * (v : ↥H) * (l : ↥H)⁻¹ ∧
          θ v' = Multiplicative.ofAdd
            (((((quotPCoreSubgroupOfEquiv hLH).trans φ) (QuotientGroup.mk l)).1 :
              GL (Fin 3) K) *ᵥ Multiplicative.toAdd (θ v)) := by
  obtain ⟨θ, hθ⟩ := h
  refine ⟨(Subgroup.subgroupOfEquivOfLe hWH).trans θ, fun l v => ?_⟩
  have hw : ((l : ↥H) : G) * ((v : ↥H) : G) * ((l : ↥H) : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hLW l.2) _).mp v.2
  refine ⟨⟨(l : ↥H) * (v : ↥H) * (l : ↥H)⁻¹, hw⟩, rfl, ?_⟩
  have h1 := hθ (Subgroup.subgroupOfEquivOfLe hLH l) (Subgroup.subgroupOfEquivOfLe hWH v) hw
  exact h1

theorem a319Hyp_one {H L V : Subgroup G} (hLH : L ≤ H) (hVH : V ≤ H)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ} (hn : Even n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n) {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)}
    (h : NatOn L V K φ) : A319Hyp (L.subgroupOf H) (V.subgroupOf H) := by
  obtain ⟨θ, hθ⟩ := natOn_subgroupOf hLH hVH hLV h
  exact ⟨n, 1, K, inferInstance, inferInstance, (quotPCoreSubgroupOfEquiv hLH).trans φ, hn, hK,
    le_rfl, by norm_num, fun _ => V.subgroupOf H, fun _ => le_rfl, iSup_const.symm,
    iSupIndep_subsingleton _, fun _ => ⟨θ, hθ⟩⟩

theorem a319Hyp_two {H L V W₁ W₂ : Subgroup G} (hLH : L ≤ H) (hVH : V ≤ H)
    (hLW₁ : L ≤ Subgroup.normalizer (W₁ : Set G)) (hLW₂ : L ≤ Subgroup.normalizer (W₂ : Set G))
    (hsum : W₁ ⊔ W₂ = V) (hinf : W₁ ⊓ W₂ = ⊥) {n : ℕ} (hn : Even n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ n) {φ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 K)}
    (h₁ : NatOn L W₁ K φ) (h₂ : NatOn L W₂ K φ) : A319Hyp (L.subgroupOf H) (V.subgroupOf H) := by
  have hW₁V : W₁ ≤ V := hsum ▸ le_sup_left
  have hW₂V : W₂ ≤ V := hsum ▸ le_sup_right
  obtain ⟨θ₁, hθ₁⟩ := natOn_subgroupOf hLH (hW₁V.trans hVH) hLW₁ h₁
  obtain ⟨θ₂, hθ₂⟩ := natOn_subgroupOf hLH (hW₂V.trans hVH) hLW₂ h₂
  refine ⟨n, 2, K, inferInstance, inferInstance, (quotPCoreSubgroupOfEquiv hLH).trans φ, hn, hK,
    by norm_num, le_rfl, ![W₁.subgroupOf H, W₂.subgroupOf H], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact fun _ hx => hW₁V hx
    · exact fun _ hx => hW₂V hx
  · have hsup : V.subgroupOf H = W₁.subgroupOf H ⊔ W₂.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hVH,
        Subgroup.map_subgroupOf_eq_of_le (hW₁V.trans hVH),
        Subgroup.map_subgroupOf_eq_of_le (hW₂V.trans hVH), hsum]
    rw [hsup]
    apply le_antisymm
    · exact sup_le (le_iSup (fun i => ![W₁.subgroupOf H, W₂.subgroupOf H] i) 0)
        (le_iSup (fun i => ![W₁.subgroupOf H, W₂.subgroupOf H] i) 1)
    · exact iSup_le fun i => by
        fin_cases i
        · exact le_sup_left
        · exact le_sup_right
  · rw [iSupIndep_pair (show (0 : Fin 2) ≠ 1 by decide) (fun k => by fin_cases k <;> simp)]
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have : ((x : ↥H) : G) ∈ W₁ ⊓ W₂ := ⟨hx.1, hx.2⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  · intro i
    fin_cases i
    · exact ⟨θ₁, hθ₁⟩
    · exact ⟨θ₂, hθ₂⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
