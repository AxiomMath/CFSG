module

public import CFSG.RankThree.PartOne.KFOUT3.KtyDih
public import CFSG.RankThree.PartOne.KF.D8Ctx

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.N1322

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {K' : Type} [Field K']

theorem kty_of_d8 (h : Sec12Hyp G p A c L E) (hG : Sec12TwoGeneric p c L E) (hEA : E = A)
    (hF13 : Sec13Facts G p A c L E) (hp2 : p ≠ 2) (hζ : ∃ ζ : K'ˣ, IsPrimitiveRoot ζ p)
    {Q : Type} [Group Q] {ε : ↥L →* Q} (hε : IsCentralPQuot p ε) (Temb : D8Mod p K' →* Q)
    (S : D8Ctx p K' L (E ⊓ L))
    (hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = Temb d)
    (Hconj : ∀ γ : DihedralGroup 4, ∃ m : Q, ∀ v, m * Temb v * m⁻¹ = Temb (d8Act γ v))
    {R : ℕ → Prop}
    (Hsmall : ∀ b : rootsOfUnity p K', b ≠ 1 → SmallAt (Temb (1, b)) R)
    (Hbig : ∀ a : rootsOfUnity p K', a ≠ 1 → BigAt p (Temb (a, a)) R) :
    ∀ t ∈ reflectionSet p E, ∀ s ∈ reflectionSet p E, DiffClass E L t s →
      ∀ (g : G) (hg : g ∈ Subgroup.normalizer (E : Set G)),
        conjAut E g hg * t * (conjAut E g hg)⁻¹ ≠ s := by
  have hp := h.prime
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine kty_of_dih (n := 4) (R := R) (by norm_num) h hG hEA hF13 (d8Act_injective hp hp2 hζ)
    (fun γ h2 h1 hc => exists_sr_of_card_moved hp hp2 hζ h2 h1 hc) hε Temb S hrel Hconj ?_ ?_
  ·
    intro v hv1 hfix
    have h1 := congrArg Prod.fst hfix
    rw [d8Act_sr_zero] at h1
    have h2 : v.1 = 1 := eq_one_of_inv_eq_self hpodd h1
    have h3 : v.2 ≠ 1 := fun h => hv1 (Prod.ext h2 h)
    have hv : v = (1, v.2) := Prod.ext h2 rfl
    rw [hv]
    exact Hsmall _ h3
  ·
    intro v hv1 hfix
    have h1 := congrArg Prod.fst hfix
    rw [d8Act_sr_one] at h1
    have h2 : v.2⁻¹ = v.1 := h1
    have h3 : v.2 = v.1⁻¹ := by rw [← h2, inv_inv]
    have ha : v.1 ≠ 1 := by
      intro h
      apply hv1
      have h4 : v.2 = 1 := by rw [h3, h, inv_one]
      exact Prod.ext h h4
    obtain ⟨m, hm⟩ := Hconj (DihedralGroup.r 1)
    have hv : v = d8Act (DihedralGroup.r 1) (v.1, v.1) := by
      rw [d8Act_r_one]
      exact Prod.ext rfl h3
    have hTv : Temb v = m * Temb (v.1, v.1) * m⁻¹ := by rw [hm, ← hv]
    rw [hTv]
    exact (Hbig _ ha).conj m

end Main

end CFSG.RankThree.PartOne.KFOUT3
