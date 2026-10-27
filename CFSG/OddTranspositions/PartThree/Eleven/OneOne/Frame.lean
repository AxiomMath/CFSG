module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Derived
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Lift
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.FrameD
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.FrameFields
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.FrameAut
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.QuotientGroup
import CFSG.OddTranspositions.PartThree.HalphaCentralizer

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity


variable {G : Type} [Group G] [Finite G] {D : Set G}

structure ElevenFrame (hC : HypothesisC D) (S : Subgroup G) (v : Fin 4 → G) : Prop where
  sylow : ∃ T : Sylow 2 (Halpha D hC.alpha),
    (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S
  injective : Function.Injective v
  mem : ∀ i, v i ∈ DalphaStar D hC.alpha
  inter_eq : (S : Set G) ∩ D = insert hC.d (Set.range v)
  prod_eq : v 0 * v 1 * v 2 * v 3 = hC.d
  card_closure : ∀ i, Nat.card (Subgroup.closure (Set.range v \ {v i})) = 8
  d_not_mem : ∀ i, hC.d ∉ Subgroup.closure (Set.range v \ {v i})
  even : ∀ g ∈ Halpha D hC.alpha, ∀ σ : Equiv.Perm (Fin 4), (∀ i, g * v i * g⁻¹ = v (σ i)) →
    σ ∈ alternatingGroup (Fin 4)
  alternating : ∀ σ ∈ alternatingGroup (Fin 4), ∃ g ∈ Halpha D hC.alpha,
    ∀ i, g * v i * g⁻¹ = v (σ i)
  aut : ∀ g ∈ Subgroup.centralizer {hC.d}, (∀ i, g * v i * g⁻¹ = v i) →
    ∃ c ∈ Subgroup.closure (Set.range v), ∀ x ∈ DalphaStar D hC.alpha,
      g * x * g⁻¹ = c * x * c⁻¹

namespace ElevenOneHyp

variable {hC : HypothesisC D}

theorem d_mem_Halpha (h : ElevenOneHyp hC) : hC.d ∈ Halpha D hC.alpha := by
  let T : Sylow 2 (Halpha D hC.alpha) := default
  obtain ⟨r, hr⟩ := h.exists_frame_map T
  obtain ⟨w, hwr, hw⟩ := h.exists_frameLift T hr
  obtain ⟨S, hTS, hdS⟩ := exists_sylow_frame hC T
  exact h.d_mem_Halpha_of_frameLift hr hwr hw hTS hdS
    (h.prod_frameLift_ne_one hr hwr hw hTS hdS)

theorem Malpha_eq (h : ElevenOneHyp hC) : Malpha D hC.alpha = Subgroup.zpowers hC.d := by
  have hu : hC.d ∈ Halpha D hC.alpha := h.d_mem_Halpha
  have hmem : hC.d ∈ Malpha D hC.alpha := by
    have hcenter : (⟨hC.d, hu⟩ : Halpha D hC.alpha) ∈
        Subgroup.center (Halpha D hC.alpha) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_d hC y.2))
    have hrad : (⟨hC.d, hu⟩ : Halpha D hC.alpha) ∈
        CFSG.solvableRadical (Halpha D hC.alpha) := by
      rw [h.center]
      exact hcenter
    show hC.d ∈ (CFSG.solvableRadical (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype
    exact Subgroup.mem_map.mpr ⟨_, hrad, rfl⟩
  have hcardM : Nat.card (Malpha D hC.alpha) ≤ 2 := by
    obtain ⟨A, B, hAB⟩ := h.facts.factors
    exact (h.derived hAB).2.2.2.2.2
  have hcardZ : Nat.card (Subgroup.zpowers hC.d) = 2 := by
    rw [Nat.card_zpowers, hC.setup.oddT.1 hC.d hC.hd]
  have hle : Subgroup.zpowers hC.d ≤ Malpha D hC.alpha :=
    Subgroup.zpowers_le_of_mem hmem
  have hcard : Nat.card (Malpha D hC.alpha) ≤ Nat.card (Subgroup.zpowers hC.d) := by
    rw [hcardZ]
    exact hcardM
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem exists_frame (h : ElevenOneHyp hC) (S : Sylow 2 G) (T : Sylow 2 (Halpha D hC.alpha))
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤
      (S : Subgroup G)) :
    ∃ v : Fin 4 → G, ElevenFrame hC (S : Subgroup G) v := by
  obtain ⟨r, hr⟩ := h.exists_frame_map T
  obtain ⟨w, hwr, hw⟩ := h.exists_frameLift T hr
  have hMalphad : hC.d ∈ Malpha D hC.alpha := by
    rw [h.Malpha_eq]
    exact Subgroup.mem_zpowers hC.d
  have hcardM : Nat.card (Malpha D hC.alpha) ≤ 2 := by
    obtain ⟨A, B, hAB⟩ := h.facts.factors
    exact (h.derived hAB).2.2.2.2.2
  have hcard_solv : Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) ≤ 2 := by
    rw [← Subgroup.card_subtype (Halpha D hC.alpha)
      (CFSG.solvableRadical (Halpha D hC.alpha))]
    simpa only [Malpha] using hcardM
  have h2grp : IsPGroup 2 (CFSG.solvableRadical (Halpha D hC.alpha)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    set k := Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) with hk
    have hle : k ≤ 2 := by rw [hk]; exact hcard_solv
    have hpos : 0 < k := by rw [hk]; exact Nat.card_pos
    have hcases : k = 1 ∨ k = 2 := by omega
    rcases hcases with h1 | h2
    · rw [h1]; norm_num
    · rw [h2]; norm_num
  have hsolv_le_T : CFSG.solvableRadical (Halpha D hC.alpha) ≤
      (T : Subgroup (Halpha D hC.alpha)) :=
    IsPGroup.le_sylow_of_normal h2grp T
  have hMT : Malpha D hC.alpha ≤ (T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype := by
    rw [Malpha]
    exact Subgroup.map_mono hsolv_le_T
  have hdS : hC.d ∈ (S : Subgroup G) := hTS (hMT hMalphad)
  have hwinj : Function.Injective w := by
    intro i j hij
    exact hr.injective (by rw [← hwr i, ← hwr j, hij])
  have hwDstar : ∀ i, w i ∈ DstarH hC := by
    intro i
    have hi : w i ∈ Set.range w := Set.mem_range_self i
    rw [← hw] at hi
    exact hi.2
  refine ⟨fun i => (w i : G), ?_⟩
  refine ⟨⟨T, hTS⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact hwinj (Subtype.ext hij)
  · intro i
    exact (mem_DstarH_iff hC).mp (hwDstar i)
  · exact h.inter_D_eq_of_frameLift hw S.isPGroup' hTS hdS
  · have hp : w 0 * w 1 * w 2 * w 3 ≠ 1 :=
      h.prod_frameLift_ne_one hr hwr hw hTS hdS
    have hp_mem : (w 0 * w 1 * w 2 * w 3 : Halpha D hC.alpha) ∈
        CFSG.solvableRadical (Halpha D hC.alpha) :=
      prod_frameLift_mem hr hwr
    have hpM : ((w 0 * w 1 * w 2 * w 3 : Halpha D hC.alpha) : G) ∈
        Malpha D hC.alpha := by
      rw [Malpha]
      exact Subgroup.mem_map.mpr ⟨_, hp_mem, rfl⟩
    have hp_ne : ((w 0 * w 1 * w 2 * w 3 : Halpha D hC.alpha) : G) ≠ 1 := by
      intro h1
      exact hp (Subtype.ext h1)
    have hpd : ((w 0 * w 1 * w 2 * w 3 : Halpha D hC.alpha) : G) = hC.d := by
      have hpZ : ((w 0 * w 1 * w 2 * w 3 : Halpha D hC.alpha) : G) ∈
          Subgroup.zpowers hC.d := by
        rw [← h.Malpha_eq]
        exact hpM
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hpZ
      have hord : (orderOf hC.d : ℤ) = 2 := by
        rw [hC.setup.oddT.1 hC.d hC.hd]
        norm_num
      have hk' : hC.d ^ (k % 2) =
          ((w 0 * w 1 * w 2 * w 3 : Halpha D hC.alpha) : G) := by
        have h := zpow_mod_orderOf hC.d k
        rw [hord] at h
        rw [h, hk]
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · rw [h0, zpow_zero] at hk'
        exact absurd hk'.symm hp_ne
      · rw [h1, zpow_one] at hk'
        exact hk'.symm
    show (w 0 : G) * (w 1 : G) * (w 2 : G) * (w 3 : G) = hC.d
    rw [← hpd]
    simp only [Subgroup.coe_mul]
  · intro i
    exact h.card_closure_frameLift hr hwr hw i
  · intro i
    exact h.d_not_mem_closure_frameLift hr hwr hw i
  · exact even_frameLift hr hwr
  · exact h.alternating_frameLift hr hwr hw
  · exact h.aut_frameLift hr hwr hw

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
