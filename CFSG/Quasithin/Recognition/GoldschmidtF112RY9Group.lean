module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

namespace F112R

variable {G : Type*} [Group G]

theorem eq_bot_of_nilpotent_perfect (H : Type*) [Group H] [Group.IsNilpotent H]
    (hperf : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤) : (⊤ : Subgroup H) = ⊥ := by
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries (G := H)).1 inferInstance
  have hall : ∀ k, (⊤ : Subgroup H).lowerCentralSeries k = ⊤ := by
    intro k
    induction k with
    | zero => exact Subgroup.lowerCentralSeries_zero _
    | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih]; exact hperf
  rw [← hn, hall n]

theorem normal_eq_top_of_perfect_of_pGroup_quotient [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hq : IsPGroup p (G ⧸ N))
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) : N = ⊤ := by
  haveI : Group.IsNilpotent (G ⧸ N) := hq.isNilpotent
  have hperfQ : ⁅(⊤ : Subgroup (G ⧸ N)), (⊤ : Subgroup (G ⧸ N))⁆ = ⊤ := by
    have hs : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
    have h1 : (⊤ : Subgroup G).map (QuotientGroup.mk' N) = ⊤ := Subgroup.map_top_of_surjective _ hs
    rw [← h1, ← Subgroup.map_commutator, hperf]
  have hbot := eq_bot_of_nilpotent_perfect (G ⧸ N) hperfQ
  rw [eq_top_iff]
  intro x _
  have hx : (QuotientGroup.mk' N x) ∈ (⊥ : Subgroup (G ⧸ N)) := hbot ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact hx

theorem eq_of_perfect_of_pGroup_quotient [Finite G] {p : ℕ} [Fact p.Prime] {L K : Subgroup G}
    (hLK : L ≤ K) [(L.subgroupOf K).Normal] (hq : IsPGroup p (K ⧸ L.subgroupOf K))
    (hperf : ⁅K, K⁆ = K) : L = K := by
  have hperfK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
  have htop := normal_eq_top_of_perfect_of_pGroup_quotient (L.subgroupOf K) hq hperfK
  refine le_antisymm hLK fun x hx => ?_
  have hmem : (⟨x, hx⟩ : K) ∈ L.subgroupOf K := htop ▸ Subgroup.mem_top _
  exact hmem

theorem isPGroup_quotient_of_sup_eq {p : ℕ} {L Q K : Subgroup G} (hQ : IsPGroup p Q)
    (hQK : Q ≤ K) (hN : Q ≤ Subgroup.normalizer (L : Set G)) (hsup : L ⊔ Q = K)
    [(L.subgroupOf K).Normal] : IsPGroup p (K ⧸ L.subgroupOf K) := by
  refine hQ.of_surjective ((QuotientGroup.mk' _).comp (Subgroup.inclusion hQK)) ?_
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hx : (x : G) ∈ ((L ⊔ Q : Subgroup G) : Set G) := hsup ▸ x.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L Q hN] at hx
  obtain ⟨l, hl, q, hq, hlq⟩ := hx
  refine ⟨⟨q, hq⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have : ((Subgroup.inclusion hQK ⟨q, hq⟩)⁻¹ * x : K) = (q⁻¹ * l * q : G) := by
    simp [← hlq, mul_assoc]
  rw [this]
  exact (Subgroup.mem_normalizer_iff''.mp (hN hq) l).mp hl

theorem pCoreOf_eq_inf_pCoreOf [Finite G] {p : ℕ} [Fact p.Prime] {L P : Subgroup G} (hLP : L ≤ P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.Open.pCoreOf p L = L ⊓ CFSG.Open.pCoreOf p P := by
  open CFSG.LieType.BorelTits in
  refine le_antisymm (le_inf (pCoreOf_le p L) ?_) ?_
  · exact le_pCoreOf_of_le_normalizer p ((pCoreOf_le p L).trans hLP)
      (hPL.trans (normalizer_le_normalizer_pCoreOf p L)) (pCoreOf_isPGroup p L)
  · refine le_pCoreOf_of_le_normalizer p inf_le_left ?_ ((pCoreOf_isPGroup p P).to_inf_right)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
    have h2 := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf p P (hLP hx)) y
    exact ⟨fun hy => ⟨h1.mp hy.1, h2.mp hy.2⟩, fun hy => ⟨h1.mpr hy.1, h2.mpr hy.2⟩⟩

end F112R

end CFSG.Quasithin
