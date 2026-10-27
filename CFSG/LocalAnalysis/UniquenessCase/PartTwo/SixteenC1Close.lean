module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Five
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_47_gap (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 →
      ∀ x : IntMod V hV, Setup1645 D V hV x → Concl1647 V x.val → Concl1647a D V₀ V x.val →
        IsSL25By5p12 ↥(starImg (centralizer ({x.val} : Set G)) (yGen L x.val))

theorem s16c1_xInf_le_yGen (L : Subgroup G) (z : G) : xInf L z ≤ yGen L z := by
  rw [yGen, hConjClosure]
  exact le_iSup_of_le ⟨1, one_mem _⟩ (le_of_eq (conjSubgroup_one (xInf L z)).symm)

theorem s16c1_starImg_mono (K : Subgroup G) {X Y : Subgroup G} (h : X ≤ Y) :
    starImg K X ≤ starImg K Y := by
  unfold starImg
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono K h)

theorem s16c1_two_lt_pRank_five {H : Subgroup G} {Ys Xs : Subgroup (Bar2 H)} (hXY : Xs ≤ Ys)
    (hY : IsSL25By5p12 ↥Ys) (hX : IsSL2Prime ↥Xs 5) : 2 < CFSG.Open.pRank 5 H := by
  obtain ⟨N, hNnormal, hN, -⟩ := hY
  have hS : IsSL2Prime ↥(Xs.subgroupOf Ys) 5 :=
    s16c1_isSL2Prime_of_equiv hX (Subgroup.subgroupOfEquivOfLe hXY).symm
  haveI : N.Normal := hNnormal
  obtain ⟨E, hE, hEcard⟩ := s16c1_exists_elemAbelian_five_cube (Y := ↥Ys) hN hS
  have hEmap : IsElemAbelian 5 (E.map Ys.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hE Ys.subtype
  have hEmapcard : Nat.card (E.map Ys.subtype) = 5 ^ 3 := by
    rw [Subgroup.card_map_of_injective Ys.subtype_injective, hEcard]
  have h3 : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 H)) :=
    CFSG.SectionRank.le_pRank (p := 5) (by norm_num) le_top hEmap hEmapcard
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5notdvd : ¬ 5 ∣ Nat.card (CFSG.pCore 2 ↥H) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(CFSG.pCore 2 ↥H))).1
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
    intro hdvd
    have h52 : 5 ∣ 2 ^ n := hn ▸ hdvd
    exact absurd (Nat.prime_five.dvd_of_dvd_pow h52) (by norm_num)
  have hquot : CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 H)) =
      CFSG.Open.pRank 5 (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_quotient_eq (p := 5) (G := ↥H) (CFSG.pCore 2 ↥H) h5notdvd
  have htop : CFSG.Open.pRank 5 H = CFSG.Open.pRank 5 (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup H
  have h3H : 3 ≤ CFSG.Open.pRank 5 H := by
    rw [htop, ← hquot]
    exact h3
  omega

theorem r16_47_close_of (D : Data G) (h46 : R16_46 D) (hgap : R16_47_gap D) :
    R16_47_close D := by
  intro V₀ V L hV hSect hCase hLc hU4 x hx h47 h47a
  have h46' := h46 V₀ V L hV hSect hCase hLc hU4 x hx
  have hX : IsSL2Prime ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) 5 :=
    h46'.2.2.1
  have hY : IsSL25By5p12 ↥(starImg (centralizer ({x.val} : Set G)) (yGen L x.val)) :=
    hgap V₀ V L hV hSect hCase hLc hU4 x hx h47 h47a
  have hle : starImg (centralizer ({x.val} : Set G)) (xInf L x.val) ≤
      starImg (centralizer ({x.val} : Set G)) (yGen L x.val) :=
    s16c1_starImg_mono _ (s16c1_xInf_le_yGen L x.val)
  exact ⟨hY, s16c1_two_lt_pRank_five hle hY hX⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
