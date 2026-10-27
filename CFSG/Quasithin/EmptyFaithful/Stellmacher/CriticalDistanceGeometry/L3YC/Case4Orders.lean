module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.SectionOrder
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.QChar
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_isE2' {X : Type} [Group X] {k : ℕ} (h : IsE2 k X) : Nat.card X = 2 ^ k := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin k → ZMod 2) = 2 ^ k
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

omit [Finite G] in
theorem relIndex_sup_eq_of_le_normalizer' {A D : Subgroup G}
    (h : A ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (A ⊔ D) = D.relIndex A := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A D h).toEquiv.symm

omit [Finite G] in
theorem card_sup_mul_card_inf {D K : Subgroup G} (h : D ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(D ⊔ K) * Nat.card ↥(D ⊓ K) = Nat.card ↥D * Nat.card ↥K := by
  have h1 := Subgroup.relIndex_mul_card K (D ⊔ K)
  have h2 := Subgroup.relIndex_mul_card K D
  rw [inf_eq_left.mpr le_sup_right] at h1
  rw [relIndex_sup_eq_of_le_normalizer' h] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_quot_pow_eight {G₀ R L : Subgroup G} (h : MS93.IsC134Case4Corr G₀ R L)
    (hC : Nat.card ↥(c134CQ G₀ L) = 4) {D : Subgroup G} (hDQ : D ≤ c134Q G₀ L)
    (hΦ : frattiniIn (c134Q G₀ L) ≤ D) (hDL : L ≤ Subgroup.normalizer (D : Set G)) :
    ∃ j : ℕ, Nat.card ↥(c134Q G₀ L) = Nat.card ↥D * 8 ^ j := by
  obtain ⟨⟨n, F, iF, iFin, α, hF, hα, hE, hZc, hCU, hU, hΦn, hK, hQ⟩, -⟩ := h
  have hn : n = 1 := by
    have h1 := card_isE2' hE
    rw [hC] at h1
    have h2 : (2 : ℕ) ^ (2 * n) = 2 ^ 2 := by rw [← h1]; norm_num
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hn
  have hFc : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
  have h8 : Nat.card F ^ 3 = 8 := by rw [hFc]; norm_num
  set Q := c134Q G₀ L with hQdef
  set P := frattiniIn Q with hPdef
  have hKQ : Q ⊓ Subgroup.centralizer (P : Set G) ≤ Q := inf_le_left
  have hPK : P ≤ Q ⊓ Subgroup.centralizer (P : Set G) := hK.2.1
  have hLK := hK.1
  have hPQ : P ≤ Q := hPK.trans hKQ
  have hPnorm : Q ≤ Subgroup.normalizer (P : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPQ).mp ?_
    have he : P.subgroupOf Q = frattini ↥Q :=
      Subgroup.comap_map_eq_self_of_injective Q.subtype_injective _
    rw [he]
    infer_instance
  have hQK : Q ≤ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) :=
    fun q hq => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hq, normalizer_le_normalizer_centralizer_of_mem (hPnorm hq)⟩
  have hDKN : L ≤ Subgroup.normalizer ((D ⊔ (Q ⊓ Subgroup.centralizer (P : Set G)) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hDL hg, hLK hg⟩
  have hDinfN : L ≤ Subgroup.normalizer ((D ⊓ (Q ⊓ Subgroup.centralizer (P : Set G)) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hDL hg, hLK hg⟩
  obtain ⟨-, s₁, -, hs₁⟩ := card_section_pow hα.1 hQ (D := D ⊔ (Q ⊓ Subgroup.centralizer (P : Set G)))
    (sup_le hDQ hKQ) le_sup_right hDKN
  obtain ⟨-, s₂, -, hs₂⟩ := card_section_pow hα.1 hK (D := D ⊓ (Q ⊓ Subgroup.centralizer (P : Set G)))
    inf_le_right (le_inf hΦ hPK) hDinfN
  have hiso := card_sup_mul_card_inf (D := D) (K := Q ⊓ Subgroup.centralizer (P : Set G))
    (hDQ.trans hQK)
  rw [h8] at hs₁ hs₂
  have hpos : 0 < Nat.card ↥(D ⊓ (Q ⊓ Subgroup.centralizer (P : Set G))) := Nat.card_pos
  have hsup : Nat.card ↥(D ⊔ (Q ⊓ Subgroup.centralizer (P : Set G))) = Nat.card ↥D * 8 ^ s₂ := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hiso, hs₂]
    ring
  refine ⟨s₂ + s₁, ?_⟩
  rw [hs₁, hsup, pow_add]
  ring

end Stellmacher.CD.L3YC

end CFSG.Quasithin
