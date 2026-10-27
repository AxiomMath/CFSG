module

public import CFSG.RankThree.PartOne.S9.Defs
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartOne.Planes

open Subgroup

variable {G : Type*} [Group G]

theorem isElementaryAbelian_iff (p : ℕ) (E : Subgroup G) :
    IsElementaryAbelian p E ↔ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x ^ p = 1 := by
  rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian]
  constructor
  · rintro ⟨hc, hp⟩
    exact ⟨fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩), hp⟩
  · rintro ⟨hc, hp⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem isElementaryAbelian_of_le {p : ℕ} {E F : Subgroup G} (hEF : E ≤ F)
    (hF : IsElementaryAbelian p F) : IsElementaryAbelian p E :=
  CFSG.IsElementaryAbelian.of_le hF hEF

theorem not_isCyclic_of_isElementaryAbelian [Finite G] {p : ℕ} (hp : p.Prime) {E H : Subgroup G}
    (hEH : E ≤ H) (hE : IsElementaryAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) :
    ¬ IsCyclic H := by
  intro hH
  have : IsCyclic (E.subgroupOf H) := inferInstance
  have : IsCyclic E := isCyclic_of_surjective (subgroupOfEquivOfLe hEH).toMonoidHom
    (subgroupOfEquivOfLe hEH).surjective
  have h1 : Nat.card E ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p p E
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 : p < p ^ 2 := by nlinarith [hp.one_lt]
  omega

theorem le_pRank_iff [Finite G] {p : ℕ} (hp : p.Prime) (H : Subgroup G) (k : ℕ) :
    k ≤ CFSG.Assembly.pRank p H ↔
      ∃ E : Subgroup G, E ≤ H ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  rw [assembly_pRank_eq hp, CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp]
  constructor
  · intro hk
    obtain ⟨E, hEH, hE, hc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hk
    exact ⟨E, hEH, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE, hc⟩
  · rintro ⟨E, hEH, hE, hc⟩
    exact CFSG.SectionRank.le_pRank hp.one_lt hEH
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).1 hE) hc

theorem le_pRank_of_le_card [Finite G] {p : ℕ} (hp : p.Prime) {W H : Subgroup G} (hWH : W ≤ H)
    (hW : IsElementaryAbelian p W) {k : ℕ} (hcard : p ^ k ≤ Nat.card W) :
    k ≤ CFSG.Assembly.pRank p H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup p W).exists_card_eq
  have hkm : k ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hm ▸ hcard)
  exact hkm.trans ((le_pRank_iff hp H m).2 ⟨W, hWH, hW, hm⟩)

theorem pow_dvd_card_of_le_card [Finite G] {p : ℕ} (hp : p.Prime) {W : Subgroup G}
    (hW : IsElementaryAbelian p W) {k : ℕ} (hcard : p ^ k ≤ Nat.card W) :
    p ^ k ∣ Nat.card W := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (IsElementaryAbelian.isPGroup p W).exists_card_eq
  have hkm : k ≤ m := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hm ▸ hcard)
  rw [hm]
  exact pow_dvd_pow p hkm

theorem mem_conjugate_iff {Y : Subgroup G} {g x : G} :
    x ∈ conjugate Y g ↔ g * x * g⁻¹ ∈ Y := by
  rw [conjugate, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

theorem mem_normalizer_of_conjugate_eq {Y : Subgroup G} {g : G} (h : conjugate Y g = Y) :
    g ∈ normalizer (Y : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← mem_conjugate_iff, h]

theorem conjugate_one (Y : Subgroup G) : conjugate Y 1 = Y := by
  ext x
  rw [mem_conjugate_iff]
  simp

theorem isElementaryAbelian_conjugate {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (g : G) : IsElementaryAbelian p (conjugate E g) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  exact IsElementaryAbelian.map (MulAut.conj g⁻¹).toMonoidHom

theorem card_conjugate (E : Subgroup G) (g : G) : Nat.card (conjugate E g) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjugate_le_of_mem_normalizer {E U : Subgroup G} (hEU : E ≤ U) {g : G}
    (hg : g ∈ normalizer (U : Set G)) : conjugate E g ≤ U := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have := hEU hx
  have hU : x ∈ U ↔ g * x * g⁻¹ ∈ U := mem_normalizer_iff.1 hg x
  exact hU.2 this

theorem card_sup_zpowers [Finite G] {p : ℕ} (hp : p.Prime) (E : Subgroup G) {f : G}
    (hfp : f ^ p = 1) (hfE : f ∉ E) (hcomm : ∀ e ∈ E, e * f = f * e) :
    Nat.card ↥(E ⊔ zpowers f) = Nat.card E * p := by
  have : Fact p.Prime := ⟨hp⟩
  have hf1 : f ≠ 1 := fun h => hfE (h ▸ E.one_mem)
  have hord : orderOf f = p := orderOf_eq_prime hfp hf1
  have hcardz : Nat.card (zpowers f) = p := by rw [Nat.card_zpowers, hord]
  have hnorm : zpowers f ≤ normalizer (E : Set G) := by
    rw [zpowers_le]
    exact centralizer_le_normalizer (E : Set G) (mem_centralizer_iff.2 hcomm)
  have hdisj : Disjoint E (zpowers f) := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxf
    have : Fact (Nat.card (zpowers f)).Prime := ⟨by rw [hcardz]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (E.subgroupOf (zpowers f)) with h | h
    · have hx : (⟨x, hxf⟩ : zpowers f) ∈ E.subgroupOf (zpowers f) := hxE
      rw [h] at hx
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hx)
    · exfalso
      have hf : (⟨f, mem_zpowers f⟩ : zpowers f) ∈ E.subgroupOf (zpowers f) := by
        rw [h]
        trivial
      exact hfE hf
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E (zpowers f) hnorm
    hdisj, hcardz]

end CFSG.RankThree.PartOne.Planes
