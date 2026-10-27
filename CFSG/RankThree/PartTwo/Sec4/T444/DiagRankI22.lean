module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagSetting
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagRank
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagRankLift

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open scoped commutatorElement

theorem ys03_I22_normalizer_map_le {K H : Type} [Group K] [Group H] (φ : K →* H)
    {R E : Subgroup K} (hE : E ≤ Subgroup.normalizer (R : Set K)) :
    E.map φ ≤ Subgroup.normalizer ((R.map φ : Subgroup H) : Set H) := by
  rintro _ ⟨e, he, rfl⟩
  have hem := Subgroup.mem_normalizer_iff.mp (hE he)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨e * r * e⁻¹, (hem r).mp hr, ?_⟩
    simp [map_mul, map_inv]
  · intro hh
    obtain ⟨r, hr, hreq⟩ := Subgroup.mem_map.mp hh
    have hconj : e * (e⁻¹ * r * e) * e⁻¹ = r := by group
    have hkey : e⁻¹ * r * e ∈ R := (hem _).mpr (by rw [hconj]; exact hr)
    refine Subgroup.mem_map.mpr ⟨e⁻¹ * r * e, hkey, ?_⟩
    rw [map_mul, map_mul, map_inv, hreq]
    group

theorem ys03_I22_witness_map {H K : Type} [Group H] [Group K] [Finite K] (ψ : K →* H)
    (hψ : Function.Injective ψ) {X : Subgroup H} (hX : ∀ k : K, ψ k ∈ X)
    (hk2 : 2 ≤ CFSG.Assembly.RankThreeEven.localRank 3 K) :
    ∃ R : Subgroup H, R ≤ X ∧ IsPGroup 2 R ∧ R ≠ ⊥ ∧ ∃ E : Subgroup H,
      E ≤ X ⊓ Subgroup.normalizer (R : Set H) ∧ CFSG.Assembly.IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ 2 := by
  obtain ⟨U, hU2, hU0, E, hEN, hE, hEc⟩ :=
    (CFSG.RankThree.PartOne.SourceSixThirteen.le_localRank_iff_exists Nat.prime_three
      (k := 2) (by norm_num)).mp hk2
  have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE
  have hRle : U.map ψ ≤ X := by
    rintro _ ⟨u, _, rfl⟩
    exact hX u
  have hEle : E.map ψ ≤ X := by
    rintro _ ⟨u, _, rfl⟩
    exact hX u
  refine ⟨U.map ψ, hRle, ?_, ?_, E.map ψ, le_inf hEle (ys03_I22_normalizer_map_le ψ hEN),
    hEab.map ψ, (Subgroup.card_map_of_injective hψ).trans hEc⟩
  · intro g
    obtain ⟨u, hu, hug⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨k, hkk⟩ := hU2 ⟨u, hu⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : u ^ 2 ^ k = 1 := congrArg Subtype.val hkk
    show (g : H) ^ 2 ^ k = 1
    rw [← hug, ← map_pow, h1, map_one]
  · intro h0
    apply hU0
    apply Subgroup.map_injective hψ
    rw [h0, Subgroup.map_bot]

theorem ys03_I22_commute_of_bot {Q : Type} [Group Q] {X Y : Subgroup Q} (hc : ⁅X, Y⁆ = ⊥) :
    ∀ x ∈ X, ∀ y ∈ Y, Commute x y := by
  intro x hx y hy
  have hxC : x ∈ Subgroup.centralizer (Y : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hx
  exact (Subgroup.mem_centralizer_iff.mp hxC y hy).symm

theorem ys03_I22_cap_le {Q : Type} [Group Q] [Finite Q] {X Y : Subgroup Q}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) :
    Nat.card (X ⊓ Y : Subgroup Q) ≤ Nat.card (Subgroup.center X) := by
  have hle : X ⊓ Y ≤ (Subgroup.center X).map X.subtype := by
    rintro x ⟨hxX, hxY⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact hXY (g : Q) g.2 x hxY
  exact (Subgroup.card_le_of_le hle).trans
    (le_of_eq (Subgroup.card_map_of_injective X.subtype_injective))

theorem ys03_I22_three_dvd_of_ne_bot {Y : Type} [Group Y] [Finite Y] {Z : Subgroup Y}
    (hZ : CFSG.Assembly.IsElemAbelian 3 Z) (hZ1 : Z ≠ ⊥) : 3 ∣ Nat.card Z := by
  obtain ⟨k, hk⟩ := card_eq_pow_of_isElemAbelian_three hZ
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · exact absurd (Subgroup.eq_bot_of_card_eq Z (by rw [hk, h0, pow_zero])) hZ1
  · rw [hk]
    exact dvd_pow_self 3 hpos.ne'

theorem ys03_I22_card_comap {Y : Type} [Group Y] [Finite Y] (Z : Subgroup Y) [Z.Normal]
    (V : Subgroup (Y ⧸ Z)) :
    Nat.card (V.comap (QuotientGroup.mk' Z)) = Nat.card V * Nat.card Z := by
  have h1 : (V.comap (QuotientGroup.mk' Z)).index = V.index :=
    V.index_comap_of_surjective (QuotientGroup.mk'_surjective Z)
  have h2 := (V.comap (QuotientGroup.mk' Z)).index_mul_card
  have h3 := V.index_mul_card
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hpos : 0 < V.index := Nat.pos_of_ne_zero V.index_ne_zero_of_finite
  rw [h1] at h2
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h2, h4, ← h3]
  ring

theorem ys03_I22_lift_E27 {Y : Type} [Group Y] [Finite Y]
    (hZ : CFSG.Assembly.IsElemAbelian 3 (Subgroup.center Y)) (hZ1 : Subgroup.center Y ≠ ⊥)
    (hZ9 : Nat.card (Subgroup.center Y) ≤ 9)
    {V : Subgroup (Y ⧸ Subgroup.center Y)} (hV : CFSG.Assembly.IsElemAbelian 3 V)
    (hV81 : 81 ≤ Nat.card V) :
    ∃ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 E ∧ 27 ≤ Nat.card E := by
  have hZN : Subgroup.center Y ≤ V.comap (QuotientGroup.mk' (Subgroup.center Y)) := by
    intro z hz
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
    exact V.one_mem
  have hcomm : ⁅V.comap (QuotientGroup.mk' (Subgroup.center Y)),
      V.comap (QuotientGroup.mk' (Subgroup.center Y))⁆ ≤ Subgroup.center Y := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : QuotientGroup.mk' (Subgroup.center Y) a * QuotientGroup.mk' (Subgroup.center Y) b =
        QuotientGroup.mk' (Subgroup.center Y) b * QuotientGroup.mk' (Subgroup.center Y) a :=
      congrArg Subtype.val
        (hV.1.is_comm.comm ⟨_, Subgroup.mem_comap.mp ha⟩ ⟨_, Subgroup.mem_comap.mp hb⟩)
    have hq1 : QuotientGroup.mk' (Subgroup.center Y) ⁅a, b⁆ = 1 := by
      simp only [commutatorElement_def, map_mul, map_inv]
      rw [hab]
      group
    exact (QuotientGroup.eq_one_iff ⁅a, b⁆).mp hq1
  have hcube : ∀ x ∈ V.comap (QuotientGroup.mk' (Subgroup.center Y)),
      x ^ 3 ∈ Subgroup.center Y := by
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center Y) (x ^ 3) = 1 := by
      rw [map_pow, hV.2 _ (Subgroup.mem_comap.mp hx)]
    exact (QuotientGroup.eq_one_iff (x ^ 3)).mp h1
  have hbig : 81 * Nat.card (Subgroup.center Y) ≤
      Nat.card (V.comap (QuotientGroup.mk' (Subgroup.center Y))) := by
    rw [ys03_I22_card_comap]
    exact Nat.mul_le_mul_right _ hV81
  obtain ⟨E, _, hE, h27⟩ := ys03_I19_lift_E81 (le_refl _) hZ hZ1 hZ9 hZN hcomm hcube hbig
  exact ⟨E, hE, h27⟩

section Certs


theorem ys03_I22_rank_contradiction {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G} {L J : Subgroup G}
    (h : DiagSetting G A M H s L) (hL : Nonempty (L.map (starQuot G) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)))
    (hJ : J ∈ thetaComponents 3 G) (hJL : ¬ J.map (starQuot G) ≤ L.map (starQuot G))
    (hZ : CFSG.Assembly.IsElemAbelian 3 (Subgroup.center (J.map (starQuot G))) ∧ Subgroup.center (J.map (starQuot G)) ≠ ⊥ ∧ Nat.card (Subgroup.center (J.map (starQuot G))) ≤ 9)
    (hV : ∃ V : Subgroup (J.map (starQuot G) ⧸ Subgroup.center (J.map (starQuot G))), CFSG.Assembly.IsElemAbelian 3 V ∧ 81 ≤ Nat.card V) : False := by
  obtain ⟨hZab, hZ1, hZ9⟩ := hZ
  obtain ⟨V, hVab, hV81⟩ := hV
  obtain ⟨e⟩ := hL
  have h3J : 3 ∣ Nat.card J :=
    ((ys03_I22_three_dvd_of_ne_bot hZab hZ1).trans (Subgroup.card_subgroup_dvd_card _)).trans
      (Subgroup.card_map_dvd J (starQuot G))
  have hJc : CFSG.IsComponent (J.map (starQuot G)) := isComponent_map_starQuot hJ h3J
  have hLc : CFSG.IsComponent (L.map (starQuot G)) := isComponent_map_starQuot h.mem h.three_dvd
  have hXY : ∀ x ∈ L.map (starQuot G), ∀ y ∈ J.map (starQuot G), Commute x y := by
    rcases CFSG.LocalCores.distinct_components_commute hLc hJc with hEq | hcomm
    · exact absurd (le_of_eq hEq.symm) hJL
    · exact ys03_I22_commute_of_bot hcomm
  have hcap : Nat.card ((L.map (starQuot G)) ⊓ (J.map (starQuot G)) :
      Subgroup (G ⧸ CFSG.pPrimeCore 3 G)) ≤ 3 :=
    (ys03_I22_cap_le hXY).trans
      (le_of_eq (CFSG.RankThree.PartTwo.KFacts.L34.card_center_of_mulEquiv e))
  have hH : CFSG.Assembly.RankThreeEven.localRank 3 (G ⧸ CFSG.pPrimeCore 3 G) ≤ 3 :=
    DiagSetting.localRank_three_quotient_le h.ctx.ctx444.sectionFourHyp
  have hψi : Function.Injective ((L.map (starQuot G)).subtype.comp e.symm.toMonoidHom) :=
    (L.map (starQuot G)).subtype_injective.comp e.symm.injective
  have hψX : ∀ k, ((L.map (starQuot G)).subtype.comp e.symm.toMonoidHom) k ∈
      L.map (starQuot G) := fun k => (e.symm k).2
  have hk2 : 2 ≤ CFSG.Assembly.RankThreeEven.localRank 3
      (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
    (CFSG.RankThree.PartTwo.KFacts.L34.localRank_three_specialLinearGroup
      CFSG.RankThree.PartTwo.KFacts.L34.card_galoisField_two_two).ge
  obtain ⟨R, hRX, hR2, hR1, E₂, hE₂, hE₂ab, hE₂card⟩ :=
    ys03_I22_witness_map _ hψi hψX hk2
  obtain ⟨E₀, hE₀ab, hE₀27⟩ := ys03_I22_lift_E27 hZab hZ1 hZ9 hVab hV81
  have hE₁ab : CFSG.Assembly.IsElemAbelian 3 (E₀.map (J.map (starQuot G)).subtype) :=
    CFSG.Open.IsElemAbelian.map hE₀ab _
  have hE₁card : Nat.card (E₀.map (J.map (starQuot G)).subtype) = Nat.card E₀ :=
    Subgroup.card_map_of_injective (J.map (starQuot G)).subtype_injective
  obtain ⟨k, hk⟩ := card_eq_pow_of_isElemAbelian_three hE₁ab
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have h9 : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h27 : 27 ≤ 3 ^ k := by rw [← hk, hE₁card]; exact hE₀27
    exact absurd (h27.trans h9) (by norm_num)
  have hEY : ∃ E : Subgroup (G ⧸ CFSG.pPrimeCore 3 G), E ≤ J.map (starQuot G) ∧
      CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k :=
    ⟨_, Subgroup.map_subtype_le E₀, hE₁ab, hk⟩
  have hI := ys03_I18_two_factors hH hXY hcap hRX hR2 hR1 ⟨E₂, hE₂, hE₂ab, hE₂card⟩ hEY
  omega

end Certs

end CFSG.RankThree.PartTwo.Sec4
