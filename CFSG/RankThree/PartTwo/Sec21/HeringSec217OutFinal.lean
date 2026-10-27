module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutFrame

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section Group

variable {G : Type} [Group G] [Finite G]

theorem out_final {A L D : Subgroup G} {c d t x : G} (hcA : c ∈ A) (hcD : c ∈ D)
    (hcL : ∀ y ∈ L, c * y = y * c) (hdA : d ∈ A) (hdL : d ∈ L) (hd3 : d ^ 3 = 1)
    (hDL : D ⊓ L ≤ Subgroup.zpowers d) (hxL : x ∈ L) (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hxd : x ∉ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G))
    (htA : t ∈ Subgroup.normalizer (A : Set G))
    (ht3 : (A.normalizerMonoidHom ⟨t, htA⟩) ^ 3 = 1)
    (htF : ∀ y ∈ A ⊓ L, t * y * t⁻¹ = y)
    (htn : ∀ y ∈ A, ∃ n : ℤ, t * y * t⁻¹ = y * d ^ n) (htc : t * c * t⁻¹ ≠ c)
    (hJ : ∀ (s : G) (hs : s ∈ Subgroup.normalizer (A : Set G)), s * d = d * s →
      (A.normalizerMonoidHom ⟨s, hs⟩) ^ 3 = 1 → s ∈ Subgroup.normalizer (D : Set G)) : False := by
  set s : G := x * t * x⁻¹ with hs_def
  have hsA : s ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hxA htA) (Subgroup.inv_mem _ hxA)
  have hxdx : x⁻¹ * d * x ∈ A ⊓ L := by
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxA) d).1 hdA
      simpa using this
    · exact L.mul_mem (L.mul_mem (L.inv_mem hxL) hdL) hxL
  have hsd : s * d = d * s := by
    have h1 : s * d * s⁻¹ = d := by
      calc s * d * s⁻¹ = x * (t * (x⁻¹ * d * x) * t⁻¹) * x⁻¹ := by rw [hs_def]; group
        _ = x * (x⁻¹ * d * x) * x⁻¹ := by rw [htF _ hxdx]
        _ = d := by group
    calc s * d = (s * d * s⁻¹) * s := by group
      _ = d * s := by rw [h1]
  have hs3 : (A.normalizerMonoidHom ⟨s, hsA⟩) ^ 3 = 1 := by
    have hsub : (⟨s, hsA⟩ : ↥(Subgroup.normalizer (A : Set G))) =
        ⟨x, hxA⟩ * ⟨t, htA⟩ * ⟨x, hxA⟩⁻¹ := Subtype.ext rfl
    rw [hsub, map_mul, map_mul, map_inv, conj_pow, ht3]
    simp
  have hsN := hJ s hsA hsd hs3
  have hscD : s * c * s⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hsN c).1 hcD
  obtain ⟨n, hn⟩ := htn c hcA
  have hxc : x * c * x⁻¹ = c := by
    have := hcL x hxL
    calc x * c * x⁻¹ = (x * c) * x⁻¹ := rfl
      _ = (c * x) * x⁻¹ := by rw [this]
      _ = c := by group
  have hcx : x⁻¹ * c * x = c := by
    have := hcL x hxL
    calc x⁻¹ * c * x = x⁻¹ * (c * x) := by group
      _ = x⁻¹ * (x * c) := by rw [this]
      _ = c := by group
  have h1 : s * c * s⁻¹ = c * (x * d * x⁻¹) ^ n := by
    calc s * c * s⁻¹ = x * (t * (x⁻¹ * c * x) * t⁻¹) * x⁻¹ := by rw [hs_def]; group
      _ = x * (t * c * t⁻¹) * x⁻¹ := by rw [hcx]
      _ = x * (c * d ^ n) * x⁻¹ := by rw [hn]
      _ = (x * c * x⁻¹) * (x * d ^ n * x⁻¹) := by group
      _ = c * (x * d * x⁻¹) ^ n := by rw [hxc, conj_zpow]
  have h2 : (x * d * x⁻¹) ^ n ∈ D ⊓ L := by
    refine ⟨?_, ?_⟩
    · have : (x * d * x⁻¹) ^ n = c⁻¹ * (s * c * s⁻¹) := by rw [h1]; group
      rw [this]
      exact D.mul_mem (D.inv_mem hcD) hscD
    · exact Subgroup.zpow_mem _ (L.mul_mem (L.mul_mem hxL hdL) (L.inv_mem hxL)) n
  have h3 : (x * d * x⁻¹) ^ n ∈ Subgroup.zpowers d := hDL h2
  have hdn : d ^ n ≠ 1 := fun h => htc (by rw [hn, h, mul_one])
  have hg3 : (x * d * x⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hd3]; group
  have hgn : (x * d * x⁻¹) ^ n ≠ 1 := by
    intro h
    apply hdn
    have : x * d ^ n * x⁻¹ = 1 := by rw [← conj_zpow]; exact h
    have h' : d ^ n = x⁻¹ * (x * d ^ n * x⁻¹) * x := by group
    rw [h', this]; group
  have hg : x * d * x⁻¹ ∈ Subgroup.zpowers d := by
    have h4 : x * d * x⁻¹ ∈ Subgroup.zpowers ((x * d * x⁻¹) ^ n) :=
      mem_zpowers_of_mem_zpowers hg3 hgn (Subgroup.zpow_mem_zpowers _ n)
    exact (Subgroup.zpowers_le.2 h3) h4
  exact hxd (normalizer_zpowers_of_conj_mem hg)

theorem IsTransvectionOn.pow_three {P : Type*} [Group P] {φ : MulAut P}
    (h : IsTransvectionOn φ) : φ ^ 3 = 1 := by
  obtain ⟨hcard, hfix⟩ := h
  ext y
  have hn : ∀ z : P, z⁻¹ * φ z ∈ commOf φ := fun z => mem_commOf φ z
  have hnfix : ∀ z : P, φ (z⁻¹ * φ z) = z⁻¹ * φ z := fun z => hfix (hn z)
  have hn3 : ∀ z : P, (z⁻¹ * φ z) ^ 3 = 1 := by
    intro z
    have := pow_card_eq_one' (G := ↥(commOf φ)) (x := ⟨z⁻¹ * φ z, hn z⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  set n := y⁻¹ * φ y with hndef
  have hφy : φ y = y * n := by rw [hndef]; group
  have h2 : (φ ^ 3) y = φ (φ (φ y)) := by
    simp [pow_succ, MulAut.mul_apply]
  have hn' : φ n = n := hnfix y
  have e1 : φ (y * n) = y * n * n := by rw [map_mul, hn', hφy]
  have e2 : φ (y * n * n) = y * n * n * n := by rw [map_mul, hn', e1]
  have h3 : n ^ 3 = 1 := hn3 y
  have e3 : y * n * n * n = y * n ^ 3 := by simp [pow_succ, mul_assoc]
  rw [h2, hφy, e1, e2, e3, h3, mul_one]
  rfl

theorem transvection_elementwise {A F : Subgroup G} {d t : G}
    (ht : t ∈ Subgroup.normalizer (A : Set G))
    (hF : (fixedSubgroupOf (A.normalizerMonoidHom ⟨t, ht⟩)).map A.subtype = F)
    (hC : (commOf (A.normalizerMonoidHom ⟨t, ht⟩)).map A.subtype = Subgroup.zpowers d) :
    (∀ y ∈ A, (t * y * t⁻¹ = y ↔ y ∈ F)) ∧ ∀ y ∈ A, ∃ n : ℤ, t * y * t⁻¹ = y * d ^ n := by
  set φ := A.normalizerMonoidHom ⟨t, ht⟩ with hφ
  have hφapp : ∀ y : A, ((φ y : A) : G) = t * y * t⁻¹ := fun y => rfl
  constructor
  · intro y hy
    constructor
    · intro h
      rw [← hF]
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      show φ ⟨y, hy⟩ = ⟨y, hy⟩
      exact Subtype.ext (by rw [hφapp]; exact h)
    · intro h
      rw [← hF] at h
      obtain ⟨z, hz, hzy⟩ := h
      have hz' : φ z = z := hz
      have : ((φ z : A) : G) = z := congrArg Subtype.val hz'
      rw [hφapp] at this
      rw [← hzy]
      exact this
  · intro y hy
    have h1 := mem_commOf φ ⟨y, hy⟩
    have h2 : y⁻¹ * (t * y * t⁻¹) ∈ (commOf φ).map A.subtype := ⟨_, h1, rfl⟩
    rw [hC] at h2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h2
    refine ⟨n, ?_⟩
    calc t * y * t⁻¹ = y * (y⁻¹ * (t * y * t⁻¹)) := by group
      _ = y * d ^ n := by rw [← hn]

end Group

section Facts

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}

set_option linter.unusedSectionVars false

theorem CoverOut.c_mem_centralizer (h : CoverOut A E U c L) :
    c ∈ Subgroup.centralizer (L : Set G) :=
  Subgroup.mem_centralizer_iff.2 (fun x hx => (h.c_comm x hx).symm)

theorem CoverOut.frame_decomp (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) :
    ∃ l : ↥L, (l : G) ∈ A ∧ (∃ i : ℤ, a = (l : G) * c ^ i) ∧
      NonCentral 3 (l : ↥L ⧸ center ↥L) ∧ l ≠ 1 := by
  have hEA : E ≤ A := h.pair.mem_E.2
  obtain ⟨l', hl', i, hai⟩ := h.decomp_A h45 a (hEA hfr.mem)
  obtain ⟨l₀, ⟨w₀, hw₀, hlw⟩, hnc⟩ := hfr.proj
  have hLC := h.inf_centralizer_eq_bot h45
  have hci : c ^ i ∈ Subgroup.centralizer (L : Set G) := Subgroup.zpow_mem _ h.c_mem_centralizer i
  have hmem : l'⁻¹ * (l₀ : G) ∈ L ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨L.mul_mem (L.inv_mem hl'.2) l₀.2, ?_⟩
    have : l'⁻¹ * (l₀ : G) = c ^ i * w₀⁻¹ := by
      have h1 : (l₀ : G) * w₀ = l' * c ^ i := hlw.symm.trans hai
      calc l'⁻¹ * (l₀ : G) = l'⁻¹ * ((l₀ : G) * w₀) * w₀⁻¹ := by group
        _ = l'⁻¹ * (l' * c ^ i) * w₀⁻¹ := by rw [h1]
        _ = c ^ i * w₀⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hci (Subgroup.inv_mem _ hw₀)
  rw [hLC, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  have hl₀ : (l₀ : G) = l' := hmem.symm
  refine ⟨l₀, hl₀ ▸ hl'.1, ⟨i, hl₀ ▸ hai⟩, hnc, ?_⟩
  intro h1
  apply hfr.not_mem
  rw [hai, ← hl₀, h1]
  simpa using Subgroup.zpow_mem_zpowers c i

set_option maxRecDepth 20000 in
theorem CoverOut.dgroup_decomp (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) :
    ∃ l : ↥L, (l : G) ∈ A ∧ (∃ i : ℤ, a = (l : G) * c ^ i) ∧ l ≠ 1 ∧ (l : G) ^ 3 = 1 ∧
      NonCentral 3 (l : ↥L ⧸ center ↥L) ∧
      dGroup a c = Subgroup.zpowers (l : G) ⊔ Subgroup.zpowers c ∧
      dGroup a c ⊓ L = Subgroup.zpowers (l : G) ∧ dGroup a c ≤ A ∧ dGroup a c ≤ E := by
  obtain ⟨l, hlA, ⟨i, hai⟩, hlnc, hl1⟩ := h.frame_decomp h45 hfr
  have hEA : E ≤ A := h.pair.mem_E.2
  have hcE : c ∈ E := (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).1.1
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hab.1 x hx y hy
  have hl3 : (l : G) ^ 3 = 1 := hab.2 (l : G) hlA
  have hDA : dGroup a c ≤ A :=
    sup_le (Subgroup.zpowers_le.2 (hEA hfr.mem)) (Subgroup.zpowers_le.2 h.c_mem_A)
  have hDE : dGroup a c ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hfr.mem) (Subgroup.zpowers_le.2 hcE)
  have hDeq : dGroup a c = Subgroup.zpowers (l : G) ⊔ Subgroup.zpowers c := by
    apply le_antisymm
    · refine sup_le (Subgroup.zpowers_le.2 ?_) le_sup_right
      rw [hai]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers c i))
    · refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · have : (l : G) = a * (c ^ i)⁻¹ := by rw [hai]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
          (Subgroup.inv_mem _ (Subgroup.zpow_mem _
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) i))
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hcomm' : ∀ x ∈ Subgroup.zpowers (l : G), ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((show Commute (l : G) c from hcomm _ hlA c h.c_mem_A).zpow_zpow j k).eq
  have hDL : dGroup a c ⊓ L = Subgroup.zpowers (l : G) := by
    apply le_antisymm
    · rintro x ⟨hxD, hxL⟩
      rw [hDeq] at hxD
      obtain ⟨y, hy, z, hz, hyz⟩ := (mem_sup_of_commute hcomm').1 hxD
      have hyL : y ∈ L := by
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact L.zpow_mem l.2 j
      have hzL : z ∈ L := by
        have : z = y⁻¹ * x := by rw [← hyz]; group
        rw [this]
        exact L.mul_mem (L.inv_mem hyL) hxL
      have hz1 := h.eq_one_of_mem_zpowers_of_mem hz hzL
      rw [← hyz, hz1, mul_one]
      exact hy
    · exact le_inf (hDeq ▸ le_sup_left) (Subgroup.zpowers_le.2 l.2)
  exact ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩

set_option maxRecDepth 20000 in
theorem CoverOut.frame_of_zpowers_eq_inf (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {d : G} (hd : Subgroup.zpowers d = dGroup a c ⊓ L) :
    d ≠ 1 ∧ Frame217 E c L d := by
  obtain ⟨l, hlA, ⟨i, hai⟩, hl1, hl3, hlnc, hDeq, hDL, hDA, hDE⟩ := h.dgroup_decomp h45 hfr
  have hdDL : d ∈ dGroup a c ⊓ L := hd ▸ Subgroup.mem_zpowers d
  have hdl : d ∈ Subgroup.zpowers (l : G) := hDL ▸ hdDL
  have hd1 : d ≠ 1 := by
    intro hd1
    rw [hd1, Subgroup.zpowers_one_eq_bot, hDL] at hd
    have : (l : G) ∈ (⊥ : Subgroup G) := hd ▸ Subgroup.mem_zpowers (l : G)
    exact hl1 (Subtype.ext (Subgroup.mem_bot.1 this))
  refine ⟨hd1, hDE hdDL.1, ?_, ⟨⟨d, hdDL.2⟩, ⟨1, one_mem _, by simp⟩, ?_⟩⟩
  · intro hdc
    exact hd1 (h.eq_one_of_mem_zpowers_of_mem hdc hdDL.2)
  · have hlq3 : (l : ↥L ⧸ center ↥L) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : l ^ 3 = 1 := Subtype.ext hl3
      rw [this]; rfl
    rcases mem_zpowers_of_pow_three hl3 hdl with h1 | h1 | h1
    · exact absurd h1 hd1
    · have : (⟨d, hdDL.2⟩ : ↥L) = l := Subtype.ext h1
      rw [this]
      exact hlnc
    · have : (⟨d, hdDL.2⟩ : ↥L) = l ^ 2 := Subtype.ext (by simpa using h1)
      rw [this, QuotientGroup.mk_pow]
      exact nonCentral_sq hlq3 hlnc

end Facts

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
