module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.Quasithin.Background.FFC5T8

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Exact

variable {W : Type} [CommGroup W]

theorem exists_not_mem_of_nat {K : Type} [Field K] {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : ↥(StatedSL 3 K) →* ↥H} (h : (FFModel.nat (StatedSL 3 K)).RealizesVia H U Z π) :
    ∃ u ∈ U, u ∉ Z := by
  obtain ⟨f, hfs, hfk, -⟩ := exists_natMap h
  obtain ⟨u, hu⟩ := hfs (Multiplicative.ofAdd (Pi.single (0 : Fin 3) (1 : K)))
  refine ⟨u, u.2, fun hz => ?_⟩
  have h1 := (hfk u).2 hz
  rw [hu] at h1
  have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
  simp at h2

theorem fixV_inf_commV_eq_bot_of_two [Finite W] {K : Type} [Field K] {H : Subgroup (MulAut W)}
    (h1 : B56Case1 H) (hiso : Nonempty (↥H ≃* ↥(StatedSL 3 (ZMod 2))))
    (hT : (⊤ : Subgroup W) = commV H ⊔ fixV H)
    (hd : DirectSumOfCopies H ⊤ (fixV H) (FFModel.nat (StatedSL 3 K)) 2) :
    fixV H ⊓ commV H = ⊥ := by
  have hLH : CFSG.Open.quasithinGenFitting H ≤ H := quasithinGenFitting_le H
  have hLn : ((CFSG.Open.quasithinGenFitting H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 (le_normalizer_quasithinGenFitting H)
  have hsl0 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Bridge.isSimple_sl_zmod2 3 (le_refl 3)
  have hsl : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.isSimpleGroup
  have hH : IsSimpleGroup ↥H := hiso.some.isSimpleGroup
  have hLne : CFSG.Open.quasithinGenFitting H ≠ ⊥ := by
    have : Nontrivial ↥(CFSG.Open.quasithinGenFitting H) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial (B1Red.isQuasisimple_to_open h1.1)
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hLeq : CFSG.Open.quasithinGenFitting H = H := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.Open.quasithinGenFitting H).subgroupOf H) with hb | ht
    · exfalso
      apply hLne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hLH hx⟩ : ↥H) ∈ (CFSG.Open.quasithinGenFitting H).subgroupOf H := hx
      rw [hb, Subgroup.mem_bot] at this
      have := congrArg Subtype.val this
      exact Subgroup.mem_bot.2 this
    · refine le_antisymm hLH fun x hx => ?_
      have : (⟨x, hx⟩ : ↥H) ∈ (CFSG.Open.quasithinGenFitting H).subgroupOf H := by rw [ht]; trivial
      exact this
  have P2 : B51Part2 H := by
    have := h1.2.1.2.1
    rwa [hLeq] at this
  by_contra hZ
  have hnot : ¬ IsIntDirect (commV H) (fixV H) ⊤ := fun hd' => hZ (by rw [inf_comm]; exact hd'.2)
  have hirr : commV H ∈ IrrPlus H ⊤ := (P2.2 hnot).1
  have hfixed : XMod.fixed ↥H (commV H) = fixV H ⊓ commV H := by
    ext l
    constructor
    · intro hl
      exact ⟨fun g hg => hl.2 ⟨g, hg⟩, hl.1⟩
    · intro hl
      exact ⟨hl.2, fun a => hl.1 a a.2⟩
  have hirr' := hirr.2.2.2
  rw [hfixed] at hirr'
  obtain ⟨I, π, hCI, hind, hsup, hreal⟩ := hd
  obtain ⟨u₀, hu₀I, hu₀C⟩ := exists_not_mem_of_nat (hreal 0)
  obtain ⟨u₁, hu₁I, hu₁C⟩ := exists_not_mem_of_nat (hreal 1)
  have hXinv : XMod.IsInv ↥H (I 0 ⊓ commV H) := fun a l hl =>
    ⟨(hreal 0).2.2.2.1 a l hl.1, commV_invariant_self H a a.2 l hl.2⟩
  have hfixX : fixV H ⊓ commV H ≤ I 0 ⊓ commV H := fun l hl => ⟨hCI 0 hl.1, hl.2⟩
  rcases hirr'.2 (I 0 ⊓ commV H) hXinv hfixX inf_le_right with hX | hX
  ·
    apply hu₀C
    have hy : u₀ ∈ commV H ⊔ fixV H := by rw [← hT]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hy
    have haI : a ∈ I 0 := by
      have h2 : a = u₀ * b⁻¹ := by rw [← hab]; simp
      rw [h2]
      exact (I 0).mul_mem hu₀I ((I 0).inv_mem (hCI 0 hb))
    have haC : a ∈ fixV H ⊓ commV H := by rw [← hX]; exact ⟨haI, ha⟩
    rw [← hab]
    exact (fixV H).mul_mem haC.1 hb
  ·
    have htop : (⊤ : Subgroup W) ≤ I 0 := by
      rw [hT]
      exact sup_le ((le_of_eq hX.symm).trans inf_le_left) (hCI 0)
    have h1' : u₁ ∈ I 0 ⊓ (fixV H ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) :=
      ⟨htop trivial, Subgroup.mem_sup_right
        (Subgroup.mem_iSup_of_mem (1 : Fin 2) (Subgroup.mem_iSup_of_mem (by decide) hu₁I))⟩
    rw [hind 0] at h1'
    exact hu₁C h1'

end Exact

section Transport

variable {V : Type} [CommGroup V] [Finite V]

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem case1_of_iso (hc : B56Counterex G) (hG₁ : G₁ ≠ ⊥) (hG₂ : G₂ ≠ ⊥) (hs3 : S3Elems ↥G₁)
    (hiso : Nonempty (↥G₂ ≃* ↥(StatedSL 3 (ZMod 2)))) : B56Case1 (autSub G₂ (fixV G₁)) := by
  have hq := isQuotientOfSQTKTauCeti_of_b53 hc.hyp
  have hb53 := h.b53 hc.hyp.1 hc.hyp.2.1 hq
  have hV₂ : ∀ v : ↥(fixV G₁), v ^ 2 = 1 := fun v => Subtype.ext (hc.hV v)
  have hmin := hc.minimal ↥(fixV G₁) hV₂ (autSub G₂ (fixV G₁)) (h.autSub_ne_bot hG₂) hb53
    (h.card_lt hG₁)
  have hno : ¬ ThreeRank2 ↥(autSub G₂ (fixV G₁)) := fun hx =>
    h.false_of_threeRank2 hq hs3 (hx.of_mulEquiv (resEquiv h.stab h.faithful).symm)
  rcases hmin with hc1 | hc2 | hc3 | hc4 | hc5
  · exact hc1
  · exfalso
    obtain ⟨⟨e⟩, -⟩ := hc2
    have h1 : Nat.card ↥(StatedSL 3 (ZMod 2)) = Nat.card (Equiv.Perm (Fin 3)) :=
      Nat.card_congr (hiso.some.symm.trans ((resEquiv h.stab h.faithful).trans e)).toEquiv
    rw [card_perm_three, CFSG.SectionRank.OddCover.card_statedSL_three, Nat.card_zmod] at h1
    norm_num at h1
  · exact absurd (threeRank2_of_case3 hc3) hno
  · exact absurd (threeRank2_of_case4 hc4) hno
  · exact absurd (threeRank2_of_case5 hc5) hno

include h in
theorem exact_two (hc : B56Counterex G) (hG₁ : G₁ ≠ ⊥) (hG₂ : G₂ ≠ ⊥) (hs3 : S3Elems ↥G₁)
    (hiso : Nonempty (↥G₂ ≃* ↥(StatedSL 3 (ZMod 2)))) {K : Type} [Field K] [Finite K]
    (hT₀ : (⊤ : Subgroup ↥(fixV G₁)) =
      commV (autSub G₂ (fixV G₁)) ⊔ fixV (autSub G₂ (fixV G₁)))
    (hd : DirectSumOfCopies (autSub G₂ (fixV G₁)) ⊤ (fixV (autSub G₂ (fixV G₁)))
      (FFModel.nat (StatedSL 3 K)) 2) :
    commV G₂ ⊓ fixV G = ⊥ := by
  have h1 := h.case1_of_iso hc hG₁ hG₂ hs3 hiso
  have hisoH : Nonempty (↥(autSub G₂ (fixV G₁)) ≃* ↥(StatedSL 3 (ZMod 2))) :=
    ⟨(resEquiv h.stab h.faithful).symm.trans hiso.some⟩
  have hex := fixV_inf_commV_eq_bot_of_two h1 hisoH hT₀ hd
  have hperf : ⁅G₂, G₂⁆ = G₂ := perfect_of_equiv_sl3 hiso.some
  have hcomm : commV G₂ ≤ commSub (fixV G₁) G₂ := commV_le_commSub_of_perfect hperf h.hc₂
  have hmap : (commV (autSub G₂ (fixV G₁))).map (fixV G₁).subtype = commSub (fixV G₁) G₂ := by
    rw [commV_eq_commSub, map_commSub_autSub h.stab, map_top_eq]
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hx1' : x ∈ (commV (autSub G₂ (fixV G₁))).map (fixV G₁).subtype := by
    rw [hmap]
    exact hcomm hx1
  have hx2' : x ∈ (fixV (autSub G₂ (fixV G₁))).map (fixV G₁).subtype := by
    rw [map_fixV_eq h]
    exact hx2
  obtain ⟨y, hy, rfl⟩ := hx1'
  obtain ⟨y', hy', hyy'⟩ := hx2'
  have hyy : y' = y := (fixV G₁).subtype_injective hyy'
  rw [hyy] at hy'
  have hmem : y ∈ fixV (autSub G₂ (fixV G₁)) ⊓ commV (autSub G₂ (fixV G₁)) := ⟨hy', hy⟩
  rw [hex, Subgroup.mem_bot] at hmem
  rw [hmem]
  exact Subgroup.one_mem _

end B510Fa

end Transport

end FFC

end CFSG.Quasithin
