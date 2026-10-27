module

public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.B1MoreElevenE

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace B69

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isFFStarMin_mono {X X' A : Subgroup (MulAut V)} (h : IsFFStarMin X A) (hAX' : A ≤ X')
    (hXX' : X' ≤ X) : IsFFStarMin X' A := by
  refine ⟨⟨hAX', h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩, fun B hB hBA => ?_⟩
  refine h.2 B ⟨hB.1.trans hXX', hB.2.1, hB.2.2.1, hB.2.2.2⟩ ?_
  obtain ⟨⟨hB1, hB2, hB3⟩, ⟨hA1, hA2, hA3⟩, hle, heq⟩ := hBA
  exact ⟨⟨hB1.trans hXX', hB2, hB3⟩, ⟨hA1.trans hXX', hA2, hA3⟩, hle, heq⟩

omit [Finite V] in
theorem commutator_le_stabSub {L A : Subgroup (MulAut V)} {U : Subgroup V} (hL : L ≤ stabSub U)
    (hA : A ≤ stabSub U) : ⁅L, A⁆ ≤ stabSub U := by
  rw [Subgroup.commutator_le]
  intro l hl a ha
  have h1 := hL hl
  have h2 := hA ha
  show l * a * l⁻¹ * a⁻¹ ∈ stabSub U
  exact (stabSub U).mul_mem ((stabSub U).mul_mem ((stabSub U).mul_mem h1 h2)
    ((stabSub U).inv_mem h1)) ((stabSub U).inv_mem h2)

omit [Finite V] in
theorem autSub_commutator {L A : Subgroup (MulAut V)} {U : Subgroup V} (hL : L ≤ stabSub U)
    (hA : A ≤ stabSub U) : ⁅autSub L U, autSub A U⁆ = autSub ⁅L, A⁆ U := by
  have hLA := commutator_le_stabSub hL hA
  have key : ⁅L.subgroupOf (stabSub U), A.subgroupOf (stabSub U)⁆ =
      ⁅L, A⁆.subgroupOf (stabSub U) := by
    apply Subgroup.map_injective (stabSub U).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hL,
      Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hLA]
  unfold autSub
  rw [← Subgroup.map_commutator, key]

theorem rAV_autSub_lt_one (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) {U : Subgroup V} (hAU : ∀ a ∈ A, ∀ w ∈ U, a w ∈ U)
    (hnt : commSub U A ≠ ⊥) (hs : rAV A < 1) : rAV (autSub A U) < 1 := by
  obtain ⟨hmin, hfaith⟩ := B1_5_2 hV hA hAU hnt
  by_contra hnot
  have hns : ¬ IsStrongFFStarOffender (autSub X U) (autSub A U) := fun h => hnot h.2
  obtain ⟨hsup, hcent⟩ := hfaith hns
  have hAst : A ≤ stabSub U := B1.le_stabSub_of_invariant hAU
  have hcardA : Nat.card (autSub A U) = Nat.card A := by
    have := card_autSub_mul hAst
    rw [hcent, Subgroup.card_bot, mul_one] at this
    exact this
  have hsupcard := card_sup_mul_card_inf U (fixV A)
  rw [hsup, Subgroup.card_top] at hsupcard
  have hfixcard : Nat.card (fixV (autSub A U)) = Nat.card ↥(U ⊓ fixV A) := by
    rw [← map_subtype_fixV_autSub hAst, Subgroup.card_map_of_injective U.subtype_injective]
  have hAb2 : IsA2 (autSub X U) (autSub A U) := hmin.1.isA2
  have hnot' : ¬ Nat.card U < Nat.card (autSub A U) * Nat.card (fixV (autSub A U)) := fun h =>
    hnot ((rAV_lt_one_iff (B1.sq_eq_one_sub hV U) hAb2).2 h)
  have hs' : Nat.card V < Nat.card A * Nat.card (fixV A) :=
    (rAV_lt_one_iff hV hA.1.isA2).1 hs
  rw [hcardA, hfixcard] at hnot'
  push Not at hnot'
  have hcU : 0 < Nat.card ↥(U ⊓ fixV A) := Nat.card_pos
  have h1 : Nat.card V * Nat.card ↥(U ⊓ fixV A) < (Nat.card A * Nat.card (fixV A)) *
      Nat.card ↥(U ⊓ fixV A) := Nat.mul_lt_mul_of_pos_right hs' hcU
  have h2 : (Nat.card A * Nat.card (fixV A)) * Nat.card ↥(U ⊓ fixV A) ≤
      Nat.card V * Nat.card ↥(U ⊓ fixV A) := by
    calc (Nat.card A * Nat.card (fixV A)) * Nat.card ↥(U ⊓ fixV A)
        = Nat.card (fixV A) * (Nat.card A * Nat.card ↥(U ⊓ fixV A)) := by ring
      _ ≤ Nat.card (fixV A) * Nat.card U := Nat.mul_le_mul_left _ hnot'
      _ = Nat.card U * Nat.card (fixV A) := by ring
      _ = Nat.card V * Nat.card ↥(U ⊓ fixV A) := by rw [← hsupcard]
  exact absurd (h1.trans_le h2) (lt_irrefl _)

theorem sqtk_of_surj (hA21 : AsA21SQTKSection) {H₀ : Type} [Group H₀] [Finite H₀]
    (hH₀ : SQTKGroup H₀) {Hs : Subgroup H₀} {Q : Type} [Group Q] [Finite Q] (π : ↥Hs →* Q)
    (hπ : Function.Surjective π) (hQ : CFSG.IsQuasisimple Q) : SQTKGroup Q := by
  refine hA21 H₀ hH₀ Hs Q π hπ (⊤ : Subgroup Q) ?_ ?_
  · exact B5.layer_eq_top_of_quasisimple
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ)
  · intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨0, by simp⟩

theorem sqtk_subgroup (hA21 : AsA21SQTKSection) {X : Subgroup (MulAut V)} {H₀ : Type} [Group H₀]
    [Finite H₀] (hH₀ : SQTKGroup H₀) (φ : H₀ →* ↥X) (hφ : Function.Surjective φ)
    {L : Subgroup (MulAut V)} (hLX : L ≤ X) (hLq : CFSG.IsQuasisimple ↥L) : SQTKGroup ↥L := by
  let π : ↥((L.subgroupOf X).comap φ) →* ↥L :=
    (Subgroup.subgroupOfEquivOfLe hLX).toMonoidHom.comp (φ.subgroupComap (L.subgroupOf X))
  refine sqtk_of_surj hA21 hH₀ π ?_ hLq
  intro l
  obtain ⟨h, hh⟩ := hφ ⟨(l : MulAut V), hLX l.2⟩
  have hmem : h ∈ (L.subgroupOf X).comap φ := by
    rw [Subgroup.mem_comap, hh]
    exact l.2
  refine ⟨⟨h, hmem⟩, ?_⟩
  apply Subtype.ext
  show ((φ h : ↥X) : MulAut V) = l
  rw [hh]

theorem sqtk_autSub (hA21 : AsA21SQTKSection) {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hLU : L ≤ stabSub U) (hL : SQTKGroup ↥L) (hq : CFSG.IsQuasisimple ↥(autSub L U)) :
    SQTKGroup ↥(autSub L U) := by
  let π : ↥(⊤ : Subgroup ↥L) →* ↥(autSub L U) :=
    (((resHom U).comp (Subgroup.inclusion hLU)).codRestrict (autSub L U) (fun l =>
      mem_autSub.2 ⟨Subgroup.inclusion hLU l, l.2, rfl⟩)).comp (⊤ : Subgroup ↥L).subtype
  refine sqtk_of_surj hA21 hL π ?_ hq
  intro φ
  obtain ⟨g, hg, hgφ⟩ := mem_autSub.1 φ.2
  refine ⟨⟨⟨g, hg⟩, trivial⟩, Subtype.ext ?_⟩
  exact hgφ

theorem exists_red (hV : ∀ v : V, v ^ 2 = 1) {X A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hAs : rAV A < 1) (hLX : L ≤ X)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hLA : ⁅L, A⁆ = L) (hA21 : AsA21SQTKSection)
    (hSQ : SQTKGroup ↥L) :
    Red (autSub (L ⊔ A) (fixV (pCoreOf 2 (L ⊔ A)))) (autSub L (fixV (pCoreOf 2 (L ⊔ A))))
      (autSub A (fixV (pCoreOf 2 (L ⊔ A)))) := by
  have hLperf : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  have hAoff : IsFFStarOffender X A := hA.1
  have hAel : IsElemAbelian2 A := hAoff.2.2.1
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  set H₀ := L ⊔ A with hH₀def
  have hH₀X : H₀ ≤ X := sup_le hLX hAoff.1
  have hH₀n : ∀ x ∈ H₀, ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
    intro x hx l hl
    obtain ⟨l', hl', a, ha, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnL).1 hx
    have e : l' * a * l * (l' * a)⁻¹ = l' * (a * l * a⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' (hAn a ha l hl)) (L.inv_mem hl')
  have hsq : ∀ x ∈ H₀, x ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup hAnL hAel.2
  set Q := pCoreOf 2 H₀ with hQdef
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₀
  have hQH : Q ≤ H₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 H₀
  have hQL : ∀ q ∈ Q, ∀ l ∈ L, q * l = l * q := by
    refine B1Red.commute_of_normal_not_le hLq (fun q hq l hl => hH₀n q (hQH hq) l hl)
      (fun l hl q hq => B1Red.conj_mem_pCoreOf (Subgroup.mem_sup_left hl) hq) ?_
    intro hle
    exact Group.IsPerfect.not_isNilpotent ↥L (hQ2.to_le hle).isNilpotent
  have hker : H₀ ⊓ centSub (fixV Q) = Q :=
    B1Red.kernel_eq_pCoreOf hV (D := L)
      (fun x hx ho => B1Red.mem_of_sq_mem_of_odd (hsq x hx) ho)
      (fun x hx q hq => (hQL q hq x hx).symm)
  set U := fixV Q with hUdef
  have hst : H₀ ≤ stabSub U := B1Red.le_stabSub_fixV_pCoreOf H₀
  have hLU : L ≤ stabSub U := le_sup_left.trans hst
  have hAU' : A ≤ stabSub U := le_sup_right.trans hst
  have hLnc : ¬ L ≤ centSub U := by
    intro hle
    have hLQ : L ≤ Q := hker ▸ le_inf le_sup_left hle
    exact Group.IsPerfect.not_isNilpotent ↥L (hQ2.to_le hLQ).isNilpotent
  have hAnc : ¬ A ≤ centSub U := by
    intro hle
    have hAQ : A ≤ Q := hker ▸ le_inf le_sup_right hle
    have h0 : ⁅L, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro l hl a ha
      show ⁅l, a⁆ ∈ (⊥ : Subgroup (MulAut V))
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (hQL a (hAQ ha) l hl).symm
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hLnt (hLA ▸ h0)
  have hLbq : CFSG.Open.IsQuasisimple ↥(autSub L U) := B1Red.isQuasisimple_autSub hLU hLq hLnc
  have hLbH : autSub L U ≤ autSub H₀ U := autSub_mono le_sup_left U
  have hO2b : pCoreOf 2 (autSub H₀ U) = ⊥ := B1Red.pCoreOf_autSub_eq_bot hker
  have hLbn : ∀ g ∈ autSub H₀ U, ∀ l ∈ autSub L U, g * l * g⁻¹ ∈ autSub L U := fun g hg l hl =>
    autSub_conj_mem hH₀n hg hl
  have hHb2 : ∀ y ∈ autSub H₀ U, y ^ 2 ∈ autSub L U := by
    intro y hy
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
    refine mem_autSub.2 ⟨g ^ 2, ?_, by rw [map_pow]⟩
    simpa using hsq _ hgH
  have hFb : quasithinGenFitting (autSub H₀ U) = autSub L U :=
    B1Red.quasithinGenFitting_eq_of_two_quot hLbH hLbn hLbq hHb2 hO2b
  have hAUinv : ∀ a ∈ A, ∀ w ∈ U, a w ∈ U := fun a ha w hw =>
    (hAU' ha w).2 hw
  have hnt : commSub U A ≠ ⊥ := by
    intro h
    apply hAnc
    intro a ha u hu
    exact (commSub_eq_bot_iff.1 h) hu a ha
  have hAbmin : IsFFStarMin (autSub X U) (autSub A U) := (B1_5_2 hV hA hAUinv hnt).1
  have hAbmin' : IsFFStarMin (autSub H₀ U) (autSub A U) :=
    isFFStarMin_mono hAbmin (autSub_mono le_sup_right U) (autSub_mono hH₀X U)
  have hAbs : rAV (autSub A U) < 1 := rAV_autSub_lt_one hV hA hAUinv hnt hAs
  have hcomm : ⁅autSub L U, autSub A U⁆ = autSub L U := by
    rw [autSub_commutator hLU hAU', hLA]
  exact ⟨hO2b, hFb, hLbq, sqtk_autSub hA21 hLU hSQ (B1Red.isQuasisimple_of_open hLbq), hAbmin',
    hAbs, hcomm⟩

end B69

end CFSG.Quasithin
