module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NIndQuot

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

open CFSG

variable {G : Type} [Group G] [Finite G]

theorem nhyp_subgroupOf {Q L : Subgroup G} {b : G} (h : NHyp Q L b) (Γ : Subgroup G)
    (hQ : Q ≤ Γ) (hL : L ≤ Γ) :
    NHyp (Q.subgroupOf Γ) (L.subgroupOf Γ) ⟨b, hL h.mem⟩ := by
  obtain ⟨e⟩ := h.iso
  refine ⟨?_, ⟨(Subgroup.subgroupOfEquivOfLe hL).trans e⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.kgroup.of_mulEquiv CFSG.Assembly.inCatalog_isoInvariant
      (Subgroup.subgroupOfEquivOfLe hQ)
  · refine Subgroup.le_normalizer_iff.mpr fun l hl q hq => ?_
    rw [Subgroup.mem_subgroupOf] at hl hq ⊢
    simpa using Subgroup.le_normalizer_iff.mp h.normalizes _ hl _ hq
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv]
    exact h.coprime
  · exact h.mem
  · rw [Subgroup.orderOf_mk]
    exact h.order
  · rintro x ⟨hxQ, hxb⟩
    have hxb : x ∈ Subgroup.centralizer ({⟨b, hL h.mem⟩} : Set Γ) := hxb
    rw [Subgroup.mem_centralizer_iff] at hxb ⊢
    intro l hl
    have hb : b * (x : G) = x * b := by
      simpa using congrArg Subtype.val (hxb ⟨b, hL h.mem⟩ rfl)
    have := Subgroup.mem_centralizer_iff.mp
      (h.cent ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun g hg => by
        rw [Set.mem_singleton_iff.mp hg]; exact hb⟩) l hl
    exact Subtype.ext this

theorem comm_mem_of_ih {Q L : Subgroup G} {b : G} (h : NHyp Q L b) {R : Subgroup G}
    (hRQ : R ≤ Q) (hRQn : ∀ q ∈ Q, ∀ r ∈ R, q * r * q⁻¹ ∈ R)
    (hRLn : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ ∈ R) (hR : R ≠ ⊥)
    (IH : ∀ (G' : Type) [Group G'] [Finite G'] (Q' L' : Subgroup G') (b' : G'),
      Nat.card Q' < Nat.card Q → NHyp Q' L' b' → Q' ≤ Subgroup.centralizer (L' : Set G')) :
    ∀ x ∈ Q, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ R := by
  have hQΓ : Q ≤ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer_iff.mpr hRQn
  have hLΓ : L ≤ Subgroup.normalizer (R : Set G) := Subgroup.le_normalizer_iff.mpr hRLn
  set Γ := Subgroup.normalizer (R : Set G) with hΓ
  have h1 := nhyp_subgroupOf h Γ hQΓ hLΓ
  haveI : (R.subgroupOf Γ).Normal := Subgroup.normal_in_normalizer
  have hR'Q : R.subgroupOf Γ ≤ Q.subgroupOf Γ := fun x hx => hRQ hx
  have hR' : R.subgroupOf Γ ≠ ⊥ := by
    intro hbot
    apply hR
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, Subgroup.le_normalizer hr⟩ : Γ) ∈ R.subgroupOf Γ := hr
    rw [hbot, Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  have h2 := nhyp_quotient h1 (R.subgroupOf Γ) hR'Q
  have hlt := (card_map_lt (R.subgroupOf Γ) hR'Q hR').trans_eq
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQΓ).toEquiv)
  have h3 := IH _ _ _ _ hlt h2
  intro x hx l hl
  let xg : Γ := ⟨x, hQΓ hx⟩
  let lg : Γ := ⟨l, hLΓ hl⟩
  have hxm : QuotientGroup.mk' (R.subgroupOf Γ) xg ∈
      (Q.subgroupOf Γ).map (QuotientGroup.mk' (R.subgroupOf Γ)) :=
    Subgroup.mem_map_of_mem _ (show xg ∈ Q.subgroupOf Γ from hx)
  have hlm : QuotientGroup.mk' (R.subgroupOf Γ) lg ∈
      (L.subgroupOf Γ).map (QuotientGroup.mk' (R.subgroupOf Γ)) :=
    Subgroup.mem_map_of_mem _ (show lg ∈ L.subgroupOf Γ from hl)
  have hc := Subgroup.mem_centralizer_iff.mp (h3 hxm) _ hlm
  have hone : QuotientGroup.mk' (R.subgroupOf Γ) (xg * lg * xg⁻¹ * lg⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← hc]
    simp [mul_assoc]
  have := (QuotientGroup.eq_one_iff _).mp hone
  exact this

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
