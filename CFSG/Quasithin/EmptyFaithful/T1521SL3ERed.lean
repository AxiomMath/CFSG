module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3EAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinMaxRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Fin257
open scoped commutatorElement

theorem isQuasisimple_of_open1521 {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

section Pre

variable {G : Type} [Group G] {L : Subgroup G} {M : Type} [Group M] {π : ↥L →* M}

theorem isElemAbelian_pre1521 (hπ : Function.Injective π) {R : Subgroup M}
    (hR : IsElemAbelian 2 R) : IsElemAbelian 2 (pre π R) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨ha, ha'⟩ := mem_pre.mp a.2
    obtain ⟨hb, hb'⟩ := mem_pre.mp b.2
    apply Subtype.ext
    have h := congrArg Subtype.val (hR.1.is_comm.comm (⟨_, ha'⟩ : R) ⟨_, hb'⟩)
    have h' : π ⟨a.1, ha⟩ * π ⟨b.1, hb⟩ = π ⟨b.1, hb⟩ * π ⟨a.1, ha⟩ := h
    rw [← map_mul, ← map_mul] at h'
    have h3 : (⟨a.1, ha⟩ : ↥L) * ⟨b.1, hb⟩ = ⟨b.1, hb⟩ * ⟨a.1, ha⟩ := hπ h'
    exact congrArg (fun z : ↥L => (z : G)) h3
  · obtain ⟨hx', hx''⟩ := mem_pre.mp hx
    have h := hR.2 _ hx''
    rw [← map_pow] at h
    have h2 : (⟨x, hx'⟩ : ↥L) ^ 2 = 1 := hπ (by rw [h, map_one])
    simpa using congrArg Subtype.val h2

end Pre

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {M : Type} [Group M] [Finite M]
  {π : ↥L →* M}

theorem rankBound1521_of_red {S K₁ K₂ V V' : Subgroup G} {U R₁ R₂ : Subgroup M}
    (hq : CFSG.IsQuasisimple ↥L) (hred : Red257 L (S ⊓ L) K₁ K₂ V V' π U R₁ R₂)
    (hMR : MaxRankModel M U R₁ R₂) (hVe : IsElemAbelian 2 V) (hR₁U : R₁ ≤ U) (hR₂U : R₂ ≤ U)
    (hcard : 2 < Nat.card R₁) : RankBound1521 S L V V' := by
  have hVC : V ⊓ Subgroup.centralizer (L : Set G) = pre π ⊥ := by
    rw [hred.hV, pre_inf_centralizer hred.center_le hred.ker_central]
  have hVcard : Nat.card V = Nat.card ↥(pre π (⊥ : Subgroup M)) * Nat.card R₁ := by
    rw [hred.hV, card_pre hred.surj]
  refine ⟨hVe, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hred.hV, hred.hP]
    exact pre_mono hR₁U
  · rw [hred.hV', hred.hP]
    exact pre_mono hR₂U
  · rw [hVC, hVcard]
    have hpos : 0 < Nat.card ↥(pre π (⊥ : Subgroup M)) := Nat.card_pos
    nlinarith
  · intro A hAe hAL hAP
    exact (maxRank_of_red hq hred hMR A hAL hAP hAe).1
  · intro A hAe hAL hAP heq
    exact (maxRank_of_red hq hred hMR A hAL hAP hAe).2 heq

end CFSG.Quasithin
