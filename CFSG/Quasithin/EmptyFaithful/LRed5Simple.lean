module

public import CFSG.Quasithin.EmptyFaithful.LRed5Twist
public import CFSG.Quasithin.EmptyFaithful.LRed5Alt
public import CFSG.Quasithin.EmptyFaithful.LRed5Models
public import CFSG.Quasithin.EmptyFaithful.LRed4IrrA

public section

namespace CFSG.Quasithin

namespace LRed5

section SimpleFile


open CFSG.Open (pCoreOf quasithinGenFitting quasithinG2)
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Normalizer

variable {V : Type} [CommGroup V]

theorem fixV_invariant_of_normalizer {L : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut V))) {z : V} (hz : z ∈ fixV L) : g z ∈ fixV L :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hg hz

end Normalizer

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_simple_outer
    (h56 : AsB56) (hV : ∀ v : V, v * v = 1)
    {Γ L : Subgroup (MulAut V)} (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hLΓ : L ≤ Γ)
    (hn : (L.subgroupOf Γ).Normal) (hC : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥)
    (hq : CFSG.IsQuasisimple ↥L) (hc : Nat.card ↥L = 168 ∨ Nat.card ↥L = 360)
    (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) {s : MulAut V} (hs : s ∈ Γ)
    (h168 : Nat.card ↥L = 168 → ¬ ∃ g ∈ L, ∀ x ∈ L, s * x * s⁻¹ = g * x * g⁻¹)
    (h360 : Nat.card ↥L = 360 → ∃ y ∈ L, y ^ 3 = 1 ∧ y ≠ 1 ∧
      ∀ g ∈ L, s * y * s⁻¹ ≠ g * y * g⁻¹) : False := by
  have hZ := FFL.center_eq_bot hLΓ hC
  obtain ⟨hLG, hB53⟩ := FFL.b53Hyp_ffJ hQ hq hZ hC hLΓ hn hoff
  have hL1 : L ≠ ⊥ := by
    intro h
    have : Nontrivial ↥L := FFL.nontrivial_of_isQuasisimple hq
    rw [h] at this
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
  have hG1 : ffJ Γ ≠ ⊥ := fun h => hL1 (le_bot_iff.mp (h ▸ hLG))
  have hΓL := FFL.le_normalizer_of_normal hLΓ hn
  have hdich : ∀ H ≤ ffJ Γ, ffJ Γ ≤ Subgroup.normalizer (H : Set (MulAut V)) → L ≤ H ∨ H = ⊥ :=
    fun H hH hGH => FFL.le_or_eq_bot hq hZ hC (hH.trans (FFL.ffJ_le Γ)) (hLG.trans hGH)
      ((hH.trans (FFL.ffJ_le Γ)).trans hΓL)
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [sq]; exact hV v
  have hcard6 : 6 < Nat.card ↥L := by rcases hc with h | h <;> omega
  rcases h56 V hV2 (ffJ Γ) hG1 hB53 with ⟨hqF, ⟨h1, -⟩, -⟩ | h2 | h3 | h4 | h5
  ·
    have hFL : quasithinGenFitting (ffJ Γ) = L := by
      have hF := quasithinGenFitting_le (ffJ Γ)
      have hGF : ffJ Γ ≤ Subgroup.normalizer (quasithinGenFitting (ffJ Γ) : Set (MulAut V)) :=
        Subgroup.le_normalizer.trans (normalizer_le_normalizer_quasithinGenFitting _)
      rcases hdich _ hF hGF with hLF | hb
      · exact FFL.eq_of_isQuasisimple hq hqF hLF ((hF.trans (FFL.ffJ_le Γ)).trans hΓL)
      · exfalso
        have := FFL.nontrivial_of_isQuasisimple hqF
        rw [hb] at this
        exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
    rw [hFL] at h1
    have hsN : s ∈ Subgroup.normalizer (L : Set (MulAut V)) := hΓL hs
    have hsN' : s⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) := Subgroup.inv_mem _ hsN
    have hL : ∀ l ∈ L, s * l * s⁻¹ ∈ L := fun l hl => (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
    have hU : ∀ u ∈ commV L, s u ∈ commV L := fun u hu => LRed4.commV_invariant_of_normalizer hsN hu
    have hU' : ∀ u ∈ commV L, s⁻¹ u ∈ commV L := fun u hu =>
      LRed4.commV_invariant_of_normalizer hsN' hu
    have hZ1 : ∀ z ∈ fixV L ⊓ commV L, s z ∈ fixV L ⊓ commV L := fun z hz =>
      ⟨fixV_invariant_of_normalizer hsN hz.1, hU z hz.2⟩
    have hZ1' : ∀ z ∈ fixV L ⊓ commV L, s⁻¹ z ∈ fixV L ⊓ commV L := fun z hz =>
      ⟨fixV_invariant_of_normalizer hsN' hz.1, hU' z hz.2⟩
    rcases b51_cases hc h1 with ⟨h168', hnat | hsum⟩ | ⟨h360', π, hπ⟩
    · obtain ⟨π, hπ⟩ := hnat
      exact h168 h168' (inner_of_natural_section hπ hU hU' hZ1 hZ1' hL)
    · refine h168 h168' (inner_of_two_natural hsum hU hU' (fun z hz => ?_) (fun z hz => ?_) hL)
      · rw [Subgroup.mem_bot] at hz
        rw [hz, map_one]
        exact one_mem _
      · rw [Subgroup.mem_bot] at hz
        rw [hz, map_one]
        exact one_mem _
    · obtain ⟨y, hyL, hy3, hy1, hfuse⟩ := h360 h360'
      exact alt6_false hπ (FFC.injective_of_faithful_sec (G64.altDn_faithful (by norm_num)) hπ)
        hU hU' hZ1 hZ1' hL hyL hy3 hy1 hfuse
  · exact (FFL.false_of_case2 hLG hcard6 h2).elim
  · exact (FFL.false_of_case3 hL1 hdich h3).elim
  · exact (FFL.false_of_case4 hcard6 hdich h4).elim
  · exact (FFL.false_of_case5 hL1 hdich h5).elim

end SimpleFile

end LRed5

end CFSG.Quasithin
