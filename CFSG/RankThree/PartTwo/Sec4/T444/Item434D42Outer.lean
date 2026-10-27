module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIID42
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIOuterE9
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.Quasithin.Recognition.CertD4Bridge
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.LocalAnalysis.SectionRank.TrialityEvenCover
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank
public import CFSG.RankThree.PartOne.S11c.Sec66TModels
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIKit

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

namespace Item434SmallTwoIII

theorem center_eq_bot_of_simple_perfect {T : Type*} [Group T] [IsSimpleGroup T]
    [Group.IsPerfect T] : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : T, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    have htop : commutator T = ⊤ := Group.IsPerfect.commutator_eq_top
    have hbot : commutator T = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hcomm y x
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    apply hab
    have ha : a ∈ (⊥ : Subgroup T) := by rw [← hbot, htop]; exact Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup T) := by rw [← hbot, htop]; exact Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]

theorem le_inner_of_card_outer_three {X : Type*} [Group X] [Finite X]
    (hO : Nat.card (Outer X) = 3) {Y : Subgroup (MulAut X)} (hY : ¬ 3 ∣ Nat.card Y) :
    Y ≤ (MulAut.conj : X →* MulAut X).range := by
  set q : MulAut X →* Outer X := QuotientGroup.mk' (inner X) with hq
  intro φ hφ
  have h1 : orderOf (q φ) ∣ Nat.card Y :=
    (orderOf_map_dvd q φ).trans (Subgroup.orderOf_dvd_natCard Y hφ)
  have h2 : orderOf (q φ) ∣ 3 := hO ▸ orderOf_dvd_natCard (q φ)
  have h3 : orderOf (q φ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
    · exact h
    · exact absurd (h ▸ h1) hY
  have h4 : q φ = 1 := orderOf_eq_one_iff.mp h3
  exact (QuotientGroup.eq_one_iff φ).mp h4

theorem card_outer_d42
    {X : Type} [Group X]
    (hm : ChevalleyExceptionalModel X .trialityD4 2 1) : Nat.card (Outer X) = 3 := by
  obtain ⟨hp, hf, -⟩ := hm.1
  have hm' : TwistedChevalleyModel X .D4 (2 ^ 1) := hm.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf hm'
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker, -⟩, -, hcard, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := 1) hf K hK σ hσ
  have hker' : Θ.ker = inner C := hker
  have hle : inner C ≤ Θ.ker := hker'.ge
  set Φ := QuotientGroup.lift (inner C) Θ hle
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hle α⟩
  have hΦker : Φ.ker = ⊥ := by
    rw [QuotientGroup.ker_lift, hker', QuotientGroup.map_mk'_self]
  have : Finite (Outer C) := by
    have : Finite (MulAut C) := MulEquiv.finite_left
    infer_instance
  have hcardO : Nat.card (Outer C) = 3 * 1 := by
    rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hΦsurj,
      Subgroup.card_top, hcard, hΦker, Subgroup.card_bot, one_mul]
  rw [CFSG.LieType.SteinbergBR.OddSylow.card_outer_congr e, hcardO]

section Ctx

open CFSG.Quasithin CFSG.RankThree.PartOne.Sec66T

theorem false_of_d42_twentySeven {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}
    (h : Ctx434Core G A M Q) (hL : IsSmallTwoD42 (layer G ⧸ Subgroup.center (layer G)))
    (h27 : Nat.card (A.map (layerConj G)) = 27) : False := by
  have hmod := chevalleyExceptionalModel_of_d42 hL
  have hZ : Subgroup.center (layer G) = ⊥ := center_layer_eq_bot_of_cover h
    fun E _ _ _ π hπ hC hodd =>
      CFSG.SectionRank.triality_even_perfect_odd_cover_trivial hmod π hπ hC hodd
  have hZX : Subgroup.center (layer G ⧸ Subgroup.center (layer G)) = ⊥ := by
    have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := h.isQuasisimple.2.1
    have : Group.IsPerfect (layer G) := h.isQuasisimple.1
    have : Group.IsPerfect (layer G ⧸ Subgroup.center (layer G)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (layer G)))
        (QuotientGroup.mk'_surjective _)
    exact center_eq_bot_of_simple_perfect
  have hO : Nat.card (Outer (layer G ⧸ Subgroup.center (layer G))) = 3 := card_outer_d42 hmod
  have hCA : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
    have h1 := h.card_inf_mul_card_layerStar
    change _ * Nat.card (A.map (layerConj G)) = 27 at h1
    rw [h27] at h1
    rw [← Subgroup.card_eq_one]
    omega
  set e : layer G ⧸ Subgroup.center (layer G) ≃* layer G ⧸ Subgroup.center (layer G) :=
    MulEquiv.refl _ with he
  have hA27 := Item434Kit.card_map_quotConj h hCA e
  obtain ⟨E, hEe, hE9, hEN⟩ := exists_map_conj_le_of_card_27 hZX (by rw [hO]; norm_num)
    (Item434Kit.isElemAbelian_map_quotConj h e) hA27
  have hcard : Nat.card (layer G ⧸ Subgroup.center (layer G)) = 211341312 := by
    have h1 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hmod
    simp only at h1
    rw [h1]
    norm_num [ordTrialityD4]
  obtain ⟨e2⟩ := trialityD4ModelBridge_of_lieModel (layer G ⧸ Subgroup.center (layer G))
    (lieModel_trialityD4_iff.mpr ⟨rfl, hmod⟩)
  have hk8 : Nat.card GF8 = 8 := by rw [Nat.card_eq_fintype_card]; rfl
  obtain ⟨e3⟩ := d4bG8_equiv_quasithin GF8 hk8
  let φ : (layer G ⧸ Subgroup.center (layer G)) ≃* ↥trialityGroup8 := e2.trans e3.symm
  refine Item434Kit.false_of_normalizer h e fun Y hY3 hYN => ?_
  have hYin := le_inner_of_card_outer_three hO hY3
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hZX
  set W := Y.comap (MulAut.conj : (layer G ⧸ Subgroup.center (layer G)) →*
    MulAut (layer G ⧸ Subgroup.center (layer G))) with hW
  have hWmap : W.map MulAut.conj = Y := Subgroup.map_comap_eq_self hYin
  have hWcard : Nat.card W = Nat.card Y := by
    conv_rhs => rw [← hWmap]
    rw [Subgroup.card_map_of_injective hinj]
  have hEW : E ≤ Subgroup.normalizer (W : Set (layer G ⧸ Subgroup.center (layer G))) := by
    intro a ha
    have hYa := hYN (hEN ⟨a, ha, rfl⟩)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have := Subgroup.mem_normalizer_iff.mp hYa (MulAut.conj w)
    rw [hW, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact this
  have hbot := Item434D42.d4_k3_of_equiv φ hcard hEe hE9 (by rw [hWcard]; exact hY3) hEW
  rw [← hWmap, hbot, Subgroup.map_bot]

end Ctx

end Item434SmallTwoIII

section Families

theorem item434SmallTwoIII_D42_27 : Item434SmallTwoIII_D42_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  exact (Item434SmallTwoIII.false_of_d42_twentySeven hc hL h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
