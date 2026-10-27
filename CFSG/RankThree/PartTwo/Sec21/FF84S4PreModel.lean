module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreBasic
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreGen
public import CFSG.RankThree.PartTwo.Sec21.FF84S3B
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Small

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

@[expose] def A8Model (L : Subgroup G) : Prop :=
  Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) ∧ Nat.card (Subgroup.center ↥L) ∣ 2

theorem a8Model_of_hyp
    {b : G} {L : Subgroup G}
    (h : FF84Hyp b L) : A8Model L := by
  obtain ⟨e⟩ : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :=
    CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
      (Or.inl ⟨by decide, h.model⟩)
  exact ⟨⟨e⟩, CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_two_of_eight
    h.quasi e⟩

theorem perfect_L {b : G} {L : Subgroup G} (h : FF84Hyp b L) : ⁅L, L⁆ = L := by
  have : Group.IsPerfect ↥L := h.quasi.1
  exact Subgroup.commutator_eq_self

theorem three_dvd_card_a8 : 3 ∣ Nat.card (alternatingGroup (Fin 8)) := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin]
  decide

theorem normal_three'_central {b : G} {L : Subgroup G} (h : FF84Hyp b L) (hA : A8Model L)
    {N : Subgroup G} (hNL : N ≤ L) (hNn : ∀ l ∈ L, ∀ x ∈ N, l * x * l⁻¹ ∈ N)
    (h3 : ¬ 3 ∣ Nat.card N) : ∀ x ∈ N, ∀ l ∈ L, x * l = l * x := by
  obtain ⟨⟨e⟩, -⟩ := hA
  set Z := Subgroup.center ↥L with hZ
  set N' : Subgroup ↥L := N.subgroupOf L with hN'
  have hN'n : N'.Normal := ⟨fun x hx l => by
    show ((l * x * l⁻¹ : ↥L) : G) ∈ N
    have := hNn l l.2 x hx
    simpa using this⟩
  have hsimple := h.quasi.2.1
  have hmapn : (N'.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map hN'n _ (QuotientGroup.mk'_surjective Z)
  intro x hx l hl
  haveI := hmapn
  rcases hsimple.eq_bot_or_eq_top_of_normal (N'.map (QuotientGroup.mk' Z)) with hb | ht
  · have hxN' : (⟨x, hNL hx⟩ : ↥L) ∈ N' := hx
    have : QuotientGroup.mk' Z ⟨x, hNL hx⟩ ∈ N'.map (QuotientGroup.mk' Z) := ⟨_, hxN', rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have := Subgroup.mem_center_iff.1 this ⟨l, hl⟩
    exact congrArg Subtype.val this.symm
  · exfalso
    have hsurj : Function.Surjective ((QuotientGroup.mk' Z).comp N'.subtype) := by
      intro q
      have hq : q ∈ N'.map (QuotientGroup.mk' Z) := by rw [ht]; trivial
      obtain ⟨n, hn, rfl⟩ := hq
      exact ⟨⟨n, hn⟩, rfl⟩
    have hdvd1 : Nat.card (↥L ⧸ Z) ∣ Nat.card N' := Subgroup.card_dvd_of_surjective hsurj
    have hdvd2 : Nat.card N' ∣ Nat.card N := by
      have : Nat.card N' = Nat.card (N'.map L.subtype) := by
        rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L)]
      have h2 : N'.map L.subtype = N := by
        rw [hN', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hNL]
      rw [this, h2]
    have h3a : 3 ∣ Nat.card (↥L ⧸ Z) := by
      rw [Nat.card_congr e.toEquiv]; exact three_dvd_card_a8
    exact h3 (h3a.trans (hdvd1.trans hdvd2))

theorem X_le_cenS_L {b : G} {L : Subgroup G} (h : FF84Hyp b L) (hA : A8Model L) :
    Opp 3 (Cen b) ≤ CenS L := by
  apply S3.B_perfect_comm L (Opp 3 (Cen b)) (perfect_L h)
  · exact le_nor_Opp 3 h.hLC
  · intro x hx; exact h.hLN (Opp_le 3 _ hx)
  · intro x hx l hl
    refine normal_three'_central h hA (N := Opp 3 (Cen b) ⊓ L) inf_le_right ?_ ?_ x hx l hl
    · intro l hl x hx
      exact ⟨Opp_conj 3 (h.hLC hl) hx.1, L.mul_mem (L.mul_mem hl hx.2) (L.inv_mem hl)⟩
    · intro h3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_Opp 3 (Cen b))
        (h3.trans (Subgroup.card_dvd_of_le inf_le_left))

theorem S41_cen_X {b b₁ b₂ : G} {L B K : Subgroup G} (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) : Opp 3 (Cen b) ≤ Cen b₁ := fun x hx =>
  Subgroup.mem_centralizer_singleton_iff.2
    ((X_le_cenS_L h.hyp hA hx b₁ (Subgroup.mem_inf.1 h.hb₁).2).symm)

theorem X_le_cenS_B {b b₁ b₂ : G} {L B K : Subgroup G} (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) : Opp 3 (Cen b) ≤ CenS B := by
  intro x hx y hy
  have hX := X_le_cenS_L h.hyp hA hx
  have hxb : x ∈ Cen b := Opp_le 3 _ hx
  have hB : B ≤ Cen x := B_le_of_mem' h
    (Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hxb).symm)
    (Subgroup.mem_centralizer_singleton_iff.2
      (X_le_cenS_L h.hyp hA hx b₁ (Subgroup.mem_inf.1 h.hb₁).2))
    (Subgroup.mem_centralizer_singleton_iff.2
      (X_le_cenS_L h.hyp hA hx b₂ (Subgroup.mem_inf.1 h.hb₂).2))
  exact Subgroup.mem_centralizer_singleton_iff.1 (hB hy)


end CFSG.RankThree.PartTwo.Sec21.FF84.S4
