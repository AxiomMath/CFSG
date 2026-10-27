module

public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvol

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section Wrappers


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem exists_field_involution_core (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    {e : G} (hce : e = c ∨ e = c⁻¹) {t : K ⧸ aschbacherSolvableCore 3 K} (ht2 : t ^ 2 = 1)
    (hrel : ∀ t₀ : K, (QuotientGroup.mk' (aschbacherSolvableCore 3 K) t₀ = t) →
      (t₀ : G) * c * (t₀ : G)⁻¹ * e⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) K)
    (hS6 : S6Act (imageSub K (Sec11.sec11K L d)) t) :
    ∃ s : G, s ^ 2 = 1 ∧ KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L s .field := by
  obtain ⟨t₀, ht₀⟩ := QuotientGroup.mk_surjective t
  have hπt : QuotientGroup.mk' (aschbacherSolvableCore 3 K) t₀ = t := ht₀
  have ht₀θ : (t₀ : G) ∉ inSubgroup (aschbacherSolvableCore 3) K := by
    intro h
    have h0 : t₀ ∈ aschbacherSolvableCore 3 K := mem_aschbacherSolvableCore_iff.mpr h
    have h1 : t = 1 := by rw [← hπt]; exact (QuotientGroup.eq_one_iff t₀).mpr h0
    obtain ⟨x, -, hx⟩ := hS6.nontrivial
    apply hx
    rw [h1]
    group
  have ht₀sq : (t₀ : G) ^ 2 ∈ inSubgroup (aschbacherSolvableCore 3) K := by
    have : t₀ ^ 2 ∈ aschbacherSolvableCore 3 K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ht₀, ht2]
    exact mem_aschbacherSolvableCore_iff.mp this
  refine exists_field_involution_of_s6 h45 C hce t₀.2 ht₀θ ht₀sq (hrel t₀ hπt) ?_
  have : QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨(t₀ : G), t₀.2⟩ = t := hπt
  rw [this]
  exact hS6

theorem exists_field_involution_fix (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    {hcN : c ∈ Subgroup.normalizer (K : Set G)} {t : K ⧸ aschbacherSolvableCore 3 K}
    (ht2 : t ^ 2 = 1) (hfix : Item426.thetaAut K hcN t = t)
    (hS6 : S6Act (imageSub K (Sec11.sec11K L d)) t) :
    ∃ s : G, s ^ 2 = 1 ∧ KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L s .field := by
  refine exists_field_involution_core h45 C (Or.inl rfl) ht2 ?_ hS6
  intro t₀ ht₀
  set w : K := t₀ * (compAction K ⟨c, hcN⟩ t₀)⁻¹ with hw
  have hwG : (w : G) = (t₀ : G) * c * (t₀ : G)⁻¹ * c⁻¹ := by
    rw [hw]
    change (t₀ : G) * (c * (t₀ : G) * c⁻¹)⁻¹ = _
    group
  have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) (compAction K ⟨c, hcN⟩ t₀) =
      Item426.thetaAut K hcN t := by
    rw [← ht₀]
    exact (Item426.thetaAut_mk K hcN t₀).symm
  have hw1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) w = 1 := by
    rw [hw, map_mul, map_inv, h1, hfix, ht₀]
    group
  have : w ∈ aschbacherSolvableCore 3 K := (QuotientGroup.eq_one_iff w).mp hw1
  rw [← hwG]
  exact mem_aschbacherSolvableCore_iff.mp this

theorem exists_field_involution_inv (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    (hcK : c ∈ K) {t : K ⧸ aschbacherSolvableCore 3 K} (ht2 : t ^ 2 = 1)
    (hinv : t * QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩ * t⁻¹ =
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K) ⟨c, hcK⟩)⁻¹)
    (hS6 : S6Act (imageSub K (Sec11.sec11K L d)) t) :
    ∃ s : G, s ^ 2 = 1 ∧ KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L s .field := by
  refine exists_field_involution_core h45 C (Or.inr rfl) ht2 ?_ hS6
  intro t₀ ht₀
  set w : K := t₀ * ⟨c, hcK⟩ * t₀⁻¹ * ⟨c, hcK⟩ with hw
  have hwG : (w : G) = (t₀ : G) * c * (t₀ : G)⁻¹ * (c⁻¹)⁻¹ := by
    rw [inv_inv]
    rfl
  have hw1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) w = 1 := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, ht₀, hinv]
    group
  have : w ∈ aschbacherSolvableCore 3 K := (QuotientGroup.eq_one_iff w).mp hw1
  rw [← hwG]
  exact mem_aschbacherSolvableCore_iff.mp this

end Wrappers

end CFSG.RankThree.PartTwo.Sec8.Hering611
