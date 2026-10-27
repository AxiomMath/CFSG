module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NHyp
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42NAbSyl
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN

variable {G : Type} [Group G] {Q L : Subgroup G} {b : G}

theorem conj_mem_of_normalizes (hn : L ≤ Subgroup.normalizer (Q : Set G)) {l x : G} (hl : l ∈ L)
    (hx : x ∈ Q) : l * x * l⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.1 (hn hl) x).1 hx

theorem conj_inv_mem_of_normalizes (hn : L ≤ Subgroup.normalizer (Q : Set G)) {l x : G}
    (hl : l ∈ L) (hx : x ∈ Q) : l⁻¹ * x * l ∈ Q := by
  simpa using conj_mem_of_normalizes hn (inv_mem hl) hx

theorem cent_of_order_three (h : NHyp Q L b) {c : G} (hc : c ∈ L) (hc3 : orderOf c = 3) :
    Q ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.centralizer (L : Set G) := by
  obtain ⟨φ⟩ := h.iso
  haveI : Finite L := Finite.of_equiv _ φ.symm.toEquiv
  have hcard : Nat.card L = 168 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.ComponentClassification.GHarris.card_GL32_gh]
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers_of_card_168 hcard
    (a := (⟨c, hc⟩ : L)) (b := (⟨b, h.mem⟩ : L))
    (by rw [← Subgroup.orderOf_coe]; exact hc3) (by rw [← Subgroup.orderOf_coe]; exact h.order)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hk' : (g : G) * b * (g : G)⁻¹ = c ^ k := by
    have := congrArg (fun z : L => (z : G)) hk
    simpa using this.symm
  intro x ⟨hxQ, hxc⟩
  have hxk : x * c ^ k = c ^ k * x := by
    have hc' : Commute x c := by
      have := Subgroup.mem_centralizer_iff.1 hxc c (Set.mem_singleton c)
      exact this.symm
    exact (hc'.zpow_right k).eq
  have hy : (g : G)⁻¹ * x * g ∈ Q ⊓ Subgroup.centralizer ({b} : Set G) := by
    refine ⟨conj_inv_mem_of_normalizes h.normalizes g.2 hxQ, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hgb : (g : G) * z = c ^ k * g := by rw [← hk']; group
    have hbg : z * (g : G)⁻¹ = (g : G)⁻¹ * c ^ k := by
      rw [← hk']; group
    calc z * ((g : G)⁻¹ * x * g) = (z * (g : G)⁻¹) * x * g := by group
      _ = (g : G)⁻¹ * c ^ k * x * g := by rw [hbg]
      _ = (g : G)⁻¹ * (x * c ^ k) * g := by rw [hxk]; group
      _ = (g : G)⁻¹ * x * (c ^ k * g) := by group
      _ = (g : G)⁻¹ * x * ((g : G) * z) := by rw [hgb]
      _ = (g : G)⁻¹ * x * g * z := by group
  have hyL := h.cent hy
  have hxeq : x = (g : G)⁻¹ * x * g := by
    have := Subgroup.mem_centralizer_iff.1 hyL (g : G) g.2
    calc x = (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ := by group
      _ = ((g : G)⁻¹ * x * g) * (g : G) * (g : G)⁻¹ := by rw [this]
      _ = (g : G)⁻¹ * x * g := by group
  rw [hxeq]
  exact hyL

theorem inf_centralizer_eq_bot (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hmin : NLeast Q L)
    (hnot : ¬ Q ≤ Subgroup.centralizer (L : Set G)) :
    Q ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rcases hmin (Q ⊓ Subgroup.centralizer (L : Set G)) inf_le_left
    (fun q hq r hr => by
      have h1 : q * r = r * q := hab q hq r hr.1
      have : q * r * q⁻¹ = r := by rw [h1]; group
      rw [this]; exact hr)
    (fun l hl r hr => by
      have h1 := Subgroup.mem_centralizer_iff.1 hr.2 l hl
      have : l * r * l⁻¹ = r := by rw [h1]; group
      rw [this]; exact hr) with h | h
  · exact h
  · exact absurd (fun x hx => (show x ∈ Q ⊓ Subgroup.centralizer (L : Set G) by
      rw [h]; exact hx).2) hnot

theorem norm_eq_one (hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hn : L ≤ Subgroup.normalizer (Q : Set G))
    (hZ : Q ⊓ Subgroup.centralizer (L : Set G) = ⊥) {c : G} (hc : c ∈ L) (hc3 : c ^ 3 = 1)
    (hcent : Q ⊓ Subgroup.centralizer ({c} : Set G) ≤ Subgroup.centralizer (L : Set G))
    {x : G} (hx : x ∈ Q) :
    x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) = 1 := by
  have hA : c * x * c⁻¹ ∈ Q := conj_mem_of_normalizes hn hc hx
  have hB : c * (c * x * c⁻¹) * c⁻¹ ∈ Q := conj_mem_of_normalizes hn hc hA
  have hN : x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) ∈ Q :=
    mul_mem (mul_mem hx hA) hB
  have h3 : c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = x := by
    have : c * c * c = 1 := by simpa [pow_succ] using hc3
    calc c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * x * (c * c * c)⁻¹ := by group
      _ = x := by rw [this]; simp
  have hconj : c * (x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹)) * c⁻¹ =
      (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) * x := by
    calc c * (x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹)) * c⁻¹
        = (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) *
          (c * (c * (c * x * c⁻¹) * c⁻¹) * c⁻¹) := by group
      _ = _ := by rw [h3]
  have hcomm : x * ((c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹)) =
      ((c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹)) * x :=
    hab x hx _ (mul_mem hA hB)
  have hfix : c * (x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹)) * c⁻¹ =
      x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) := by
    rw [hconj, ← hcomm]; group
  have hmem : x * (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) ∈
      Q ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine ⟨hN, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [mul_inv_eq_iff_eq_mul] at hfix
    exact hfix
  have := hZ ▸ (show _ ∈ Q ⊓ Subgroup.centralizer (L : Set G) from ⟨hN, hcent hmem⟩)
  simpa using this

theorem le_centralizer_of_simple [IsSimpleGroup L] (hn : L ≤ Subgroup.normalizer (Q : Set G))
    {s : G} (hs : s ∈ L) (hs1 : s ≠ 1) (hsc : ∀ x ∈ Q, s * x = x * s) :
    Q ≤ Subgroup.centralizer (L : Set G) := by
  let K : Subgroup L := (Subgroup.centralizer (Q : Set G)).comap L.subtype
  haveI : K.Normal := ⟨fun k hk g => by
    show (g : G) * (k : G) * (g : G)⁻¹ ∈ Subgroup.centralizer (Q : Set G)
    have hk' : ∀ y ∈ Q, y * (k : G) = (k : G) * y :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hk)
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have h1 := hk' _ (conj_inv_mem_of_normalizes hn g.2 hx)
    calc x * ((g : G) * (k : G) * (g : G)⁻¹)
        = (g : G) * ((g : G)⁻¹ * x * g * (k : G)) * (g : G)⁻¹ := by group
      _ = (g : G) * ((k : G) * ((g : G)⁻¹ * x * g)) * (g : G)⁻¹ := by rw [h1]
      _ = (g : G) * (k : G) * (g : G)⁻¹ * x := by group⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with hK | hK
  · exfalso
    have hsK : (⟨s, hs⟩ : L) ∈ K :=
      Subgroup.mem_comap.2 (Subgroup.mem_centralizer_iff.2 fun x hx => (hsc x hx).symm)
    rw [hK] at hsK
    exact hs1 (congrArg Subtype.val (Subgroup.mem_bot.1 hsK))
  · intro x hx
    refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    have hlK : (⟨l, hl⟩ : L) ∈ K := hK ▸ Subgroup.mem_top _
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hlK) x hx).symm

end CFSG.RankThree.PartTwo.Sec21.FF79.LemmaN
