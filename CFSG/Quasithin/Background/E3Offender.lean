module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Offender

variable {G : Type u} [Group G] [Finite G] {V T : Subgroup G}

omit [Finite G] in
theorem le_centralizer_iff_comm {X Y : Subgroup G} :
    X ≤ Subgroup.centralizer (Y : Set G) ↔ Y ≤ Subgroup.centralizer (X : Set G) := by
  constructor <;> intro h a ha <;>
    exact Subgroup.mem_centralizer_iff.2 fun b hb =>
      (Subgroup.mem_centralizer_iff.1 (h hb) a ha).symm

omit [Finite G] in
theorem commutator_eq_bot_iff_le_centralizer' {X Y : Subgroup G} :
    ⁅X, Y⁆ = ⊥ ↔ X ≤ Subgroup.centralizer (Y : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer

omit [Finite G] in
theorem wClos_zero_le_of_wParam_pos (hw : 0 < wParam T V) :
    wClos V 0 T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  by_contra h
  have h1 : wParam T V ≤ ((0 : ℕ) : ℕ∞) := iInf₂_le 0 h
  have h2 : wParam T V ≤ 0 := by simpa using h1
  exact absurd hw (not_lt.2 h2)

theorem conj_le_centralizer_of_le_normalizer (hV : IsElemAbelian 2 V) (hT : HypE322 T V)
    (hw : 0 < wParam T V) {g : G} (hg : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G)) :
    conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := by
  have hTN : IsSylowIn 2 T (Subgroup.normalizer (V : Set G)) :=
    B6.isSylowTwoOf_mono hT.sylow hT.normal le_top
  have hVg2 : IsPGroup 2 (conjSubgroup V g) :=
    isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g
  obtain ⟨n, hn, hle⟩ := exists_le_conj_of_isSylowIn hTN hg hVg2
  have h1 : conjSubgroup V (g * n⁻¹) ≤ T := by
    rw [← conjSubgroup_conjSubgroup]
    have := conjSubgroup_mono_left n⁻¹ hle
    rwa [conjSubgroup_conj_inv] at this
  have hmem : conjSubgroup V (g * n⁻¹) ∈ gammaSet V 0 T :=
    ⟨h1, g * n⁻¹, le_rfl, mQuot_self _⟩
  have h2 : conjSubgroup V (g * n⁻¹) ≤ Subgroup.centralizer (V : Set G) :=
    ((le_wClos hmem).trans (wClos_zero_le_of_wParam_pos hw)).trans inf_le_right
  have hnV : conjSubgroup V n = V := conjSubgroup_eq_iff_mem_normalizer.2 hn
  have h3 := conjSubgroup_mono_left n h2
  rw [conjSubgroup_conjSubgroup, inv_mul_cancel_right, conjSubgroup_centralizer, hnV] at h3
  exact h3

theorem e3_25_normalizer_iff (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (hw : 0 < wParam T V)
    (g : G) :
    conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) ↔
      conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) :=
  ⟨conj_le_centralizer_of_le_normalizer hV hT hw, fun h => h.trans (Subgroup.centralizer_le_normalizer _)⟩

omit [Finite G] in
theorem e3_25_centralizer_iff (g : G) :
    conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) ↔
      V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) :=
  le_centralizer_iff_comm

theorem e3_25_centralizer_iff_normalizer (hV : IsElemAbelian 2 V) (hT : HypE322 T V)
    (hw : 0 < wParam T V) (g : G) :
    V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) ↔
      V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  refine ⟨fun h => h.trans (Subgroup.centralizer_le_normalizer _), fun h => ?_⟩
  have hg' : conjSubgroup V g⁻¹ ≤ Subgroup.normalizer (V : Set G) := by
    have := conjSubgroup_mono_left g⁻¹ h
    rwa [conjSubgroup_normalizer, conjSubgroup_conj_inv] at this
  have h1 := conj_le_centralizer_of_le_normalizer hV hT hw hg'
  have h2 := conjSubgroup_mono_left g h1
  rwa [conjSubgroup_inv_conj, conjSubgroup_centralizer] at h2

theorem e3_25 (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (hw : 0 < wParam T V) (g : G) :
    (conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) ↔
        conjSubgroup V g ≤ Subgroup.centralizer (V : Set G)) ∧
      (conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) ↔
        V ≤ Subgroup.centralizer (conjSubgroup V g : Set G)) ∧
      (V ≤ Subgroup.centralizer (conjSubgroup V g : Set G) ↔
        V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)) :=
  ⟨e3_25_normalizer_iff hV hT hw g, e3_25_centralizer_iff g,
    e3_25_centralizer_iff_normalizer hV hT hw g⟩

theorem e3_26 (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV) {g : G}
    (hg : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G))
    (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥) : ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  rcases h24 with hw | hFF
  · intro hVN
    apply hnc
    exact commutator_eq_bot_iff_le_centralizer'.2
      ((e3_25_centralizer_iff_normalizer hV hT hw g).2 hVN)
  · exact e3_11 hV hFF hg hnc

omit [Finite G] in
theorem inf_normalizer_inf_centralizer (X V : Subgroup G) :
    X ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (V : Set G) =
      X ⊓ Subgroup.centralizer (V : Set G) := by
  rw [inf_assoc, inf_eq_right.2 (Subgroup.centralizer_le_normalizer _)]

omit [Finite G] in
theorem rk_autI_eq_mQuot (hV : IsElemAbelian 2 V) {A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    rk ↥(autI hV A) = mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) := by
  unfold rk mQuot
  rw [card_autI_eq hV hA]

theorem e3_28_four_left (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV)
    {g : G} (hg : IsWOffenderAt T V g) : ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
  rcases eq_or_ne (wParam T V) 0 with h0 | hne
  · have hm : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) = 0 := by
      have := hg.2
      rw [h0] at this
      exact_mod_cast this.symm
    have hA := (mQuot_eq_zero_iff (isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g)
      inf_le_left).1 hm
    have hle : conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) := by
      rw [← hA]
      exact inf_le_right
    exact e3_26 hV hT h24 hle hg.1
  · have hw : 0 < wParam T V := pos_iff_ne_zero.2 hne
    intro hVN
    apply hg.1
    exact commutator_eq_bot_iff_le_centralizer'.2
      ((e3_25_centralizer_iff_normalizer hV hT hw g).2 hVN)

theorem e3_28_four_right (hV : IsElemAbelian 2 V) (hT : HypE322 T V) {g : G}
    (hg : IsWOffenderAt T V g) (hw : 0 < wParam T V) :
    ¬ conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) := by
  intro h
  apply hg.1
  have h1 := (e3_25_normalizer_iff hV hT hw g).1 h
  exact commutator_eq_bot_iff_le_centralizer'.2 ((e3_25_centralizer_iff g).1 h1)

theorem e3_28_one (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV) {g : G}
    (hg : IsWOffenderAt T V g) :
    rParam V ≤ mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (V : Set G)) := by
  rw [inf_normalizer_inf_centralizer]
  exact e3_4_two (e3_28_four_left hV hT h24 hg)

theorem mQuot_conj_inf_centralizer (hV : IsElemAbelian 2 V) (g : G) :
    mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (V : Set G)) =
      mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) +
        rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) := by
  rw [rk_autI_eq_mQuot hV inf_le_right, add_comm]
  exact mQuot_add inf_le_left inf_le_left

theorem rk_autI_le_pRank (hV : IsElemAbelian 2 V) {g : G} :
    rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) ≤
      CFSG.Open.pRank 2 (autI hV ⊤) := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup hV g
  have hAel : IsElemAbelian 2 (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) :=
    B2F.isElemAbelian_mono inf_le_left hVg
  have h2 := isElemAbelian2_autI hV hAel (inf_le_right :
    conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (V : Set G))
  have hE : IsElemAbelian 2 (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) :=
    ⟨⟨⟨fun a b => Subtype.ext (h2.1 a a.2 b b.2)⟩⟩, fun a ha => h2.2 a ha⟩
  exact le_pRank Nat.prime_two (autI_mono hV le_top) hE
    (card_eq_two_pow_of_isPGroup (isPGroup_of_isElemAbelian2 h2))

theorem e3_28_two_left (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV)
    {g : G} (hg : IsWOffenderAt T V g) :
    rParam V ≤ wParam T V +
      ((rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) : ℕ) : ℕ∞) := by
  have h1 := e3_28_one hV hT h24 hg
  rw [mQuot_conj_inf_centralizer hV g] at h1
  rw [hg.2]
  exact_mod_cast h1

theorem e3_28_two_right (hV : IsElemAbelian 2 V) {g : G} (w : ℕ∞) :
    w + ((rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) : ℕ) : ℕ∞) ≤
      w + ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) := by
  have := rk_autI_le_pRank (V := V) hV (g := g)
  exact add_le_add le_rfl (Nat.cast_le.2 this)

theorem e3_28_three (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV)
    {g : G} (hg : IsWOffenderAt T V g) :
    rParam V - wParam T V ≤
      ((rk ↥(autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) : ℕ) : ℕ∞) := by
  rw [tsub_le_iff_left]
  exact e3_28_two_left hV hT h24 hg

theorem e3_29 (hV : IsElemAbelian 2 V) (hT : HypE322 T V) (h24 : HypE324 T V hV) {g : G}
    (hg : IsWOffenderAt T V g) :
    rParam V ≤ ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + wParam T V := by
  rw [add_comm]
  exact (e3_28_two_left hV hT h24 hg).trans (e3_28_two_right hV _)

end Offender

end E3

end CFSG.Quasithin
