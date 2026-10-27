module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTwo
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenMaxU

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem FiveTenHyp.sec5Hyp {H M T A : Subgroup G} {Ω : Set (Subgroup G)}
    (h : FiveTenHyp H M T Ω) (hA : A ∈ Ω) (hAT : A ≤ T) : Sec5Hyp H M A where
  isElemAbelian := h.invColl.isElemAbelian A hA
  le_group := hAT.trans h.sylow.le
  le_M := hAT.trans h.le_M
  not_le := h.not_le
  odd_relIndex := h.odd_relIndex

theorem isSylowIn_of_odd_relIndex {M D S : Subgroup G} (hS : IsSylowIn 2 S (M ⊓ D))
    (hodd : Odd (M.relIndex D)) : IsSylowIn 2 S D := by
  have hSD : S ≤ D := hS.le.trans inf_le_right
  have hmul : S.relIndex (M ⊓ D) * (M ⊓ D).relIndex D = S.relIndex D :=
    Subgroup.relIndex_mul_relIndex S (M ⊓ D) D hS.le inf_le_right
  have h2 : (M ⊓ D).relIndex D = M.relIndex D := Subgroup.inf_relIndex_right M D
  refine ⟨hSD, hS.isPGroup, fun hd => ?_⟩
  rw [← hmul, h2] at hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h1 | h1
  · exact hS.not_dvd_relIndex h1
  · exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h1)

theorem FiveTenHyp.exists_dFam {H M T : Subgroup G} {Ω : Set (Subgroup G)}
    (h : FiveTenHyp H M T Ω) :
    ∃ A ∈ Ω, A ≠ ⊥ ∧ A ≤ M ∧ ∃ D S : Subgroup G, D ≤ H ∧ A ≤ S ∧ S ≤ T ∧
      IsSylowIn 2 S D ∧ ¬ D ≤ M ∧ (maxOver D A).ncard = 1 := by
  obtain ⟨A, hA, hAT, hA1⟩ := h.exists_ne_bot
  obtain ⟨g, hg, hAg, D, hD⟩ := five_two_exists (h.sec5Hyp hA hAT)
  obtain ⟨hDH, hAD, hDM, hodd, hcard⟩ := mem_dFam.1 hD
  have hA₁Ω : conjSubgroup A g ∈ Ω := h.invColl.conj A hA g⁻¹ (H.inv_mem hg)
  have hne : ∀ (X : Subgroup G) (k : G), X ≠ ⊥ → A1b.conjSub k X ≠ ⊥ := by
    intro X k hX hbot
    apply hX
    exact (A1b.conjSub_inj k).1 (hbot.trans (Subgroup.map_bot _).symm)
  have hA₁1 : conjSubgroup A g ≠ ⊥ := hne A g⁻¹ hA1
  have hA₁2 : IsPGroup 2 (conjSubgroup A g) :=
    E1.isPGroup_of_isElemAbelian (h.invColl.isElemAbelian _ hA₁Ω)
  obtain ⟨S₁, hS₁, hA₁S₁⟩ := exists_isSylowIn_ge 2 (le_inf hAg hAD) hA₁2
  have hS₁D : IsSylowIn 2 S₁ D := isSylowIn_of_odd_relIndex hS₁ hodd
  have hS₁M : S₁ ≤ M := hS₁.le.trans inf_le_left
  have hS₁H : S₁ ≤ H := (hS₁.le.trans inf_le_right).trans hDH
  obtain ⟨m, hm, hmT⟩ := exists_conjSub_le_of_isSylowIn h.sylow h.le_M hS₁.isPGroup hS₁M hS₁H
  have hmM : m ∈ M := (Subgroup.mem_inf.1 hm).1
  have hmH : m ∈ H := (Subgroup.mem_inf.1 hm).2
  have hcH : A1b.conjSub m H = H := B6.conjSub_eq_self (Subgroup.le_normalizer hmH)
  refine ⟨A1b.conjSub m (conjSubgroup A g), h.invColl.conj _ hA₁Ω m hmH,
    hne _ m hA₁1, (conjSub_le_iff_of_mem hmM).2 hAg, A1b.conjSub m D, A1b.conjSub m S₁,
    (A1b.conjSub_mono m hDH).trans hcH.le, A1b.conjSub_mono m hA₁S₁, hmT,
    isSylowIn_conjSub hS₁D m, fun hle => hDM ((conjSub_le_iff_of_mem hmM).1 hle), ?_⟩
  exact ncard_maxOver_conjSub.trans hcard

end CFSG.LocalAnalysis.WeakClosure81
