module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217Out

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic CFSG.Blueprint
  CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement

section PureThreeB


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem false_of_pure3B_plain {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (hZ : center ↥L = ⊥)
    (ψ : ↥L ⧸ center ↥L ≃* ↥j3P) {E U : Subgroup G} (hEL : E ≤ L)
    (hE9 : Nat.card E = 9) (hE3 : ∀ x : ↥L, (x : G) ∈ E → x ^ 3 = 1)
    (hEB : ∀ x : ↥L, (x : G) ∈ E → x ≠ 1 →
      Nat.card (centralizer ({(x : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) = 243)
    (hUN : U ≤ normalizer (L : Set G)) (hU4 : Nat.card U = 4) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
    (hEU : ∀ x ∈ E, ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hLU : ⁅L, U⁆ = L) : False := by
  obtain ⟨T, hTR, hTinj, hTconj⟩ := exists_toR hq.1 ψ
  set Φ : ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 6156) :=
    T.comp L.normalizerMonoidHom with hΦ
  have hΦapp : ∀ (n : ↥(Subgroup.normalizer (L : Set G))) (x : ↥L),
      (((L.normalizerMonoidHom n) x : ↥L) : G) = (n : G) * x * (n : G)⁻¹ := fun n x => rfl
  have hmemN : ∀ x : ↥L, (x : G) ∈ (Subgroup.normalizer (L : Set G)) :=
    fun x => Subgroup.le_normalizer x.2
  have hΦL : ∀ x : ↥L, Φ ⟨(x : G), hmemN x⟩ =
      ((ψ (x : ↥L ⧸ center ↥L) : ↥j3P) : Equiv.Perm (Fin 6156)) := by
    intro x
    have : L.normalizerMonoidHom ⟨(x : G), hmemN x⟩ = MulAut.conj x :=
      MulEquiv.ext fun y => Subtype.ext (by rw [hΦapp]; simp [MulAut.conj_apply])
    show T (L.normalizerMonoidHom ⟨(x : G), hmemN x⟩) = _
    rw [this, hTconj]
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥L →* Equiv.Perm (Fin 6156), ∀ x : ↥L,
      θ x = ((ψ (x : ↥L ⧸ center ↥L) : ↥j3P) : Equiv.Perm (Fin 6156)) :=
    ⟨(j3P.subtype).comp (ψ.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))), fun x => rfl⟩
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hθ] at hx
    have h1 : ψ (x : ↥L ⧸ center ↥L) = 1 := Subtype.ext hx
    have h2 : (x : ↥L ⧸ center ↥L) = 1 := (map_eq_one_iff _ ψ.injective).1 h1
    have h3 : x ∈ center ↥L := (QuotientGroup.eq_one_iff x).1 h2
    rw [hZ, Subgroup.mem_bot] at h3
    exact h3
  set EX : Subgroup ↥L := E.subgroupOf L with hEX
  have hEXmem : ∀ x : ↥L, x ∈ EX ↔ (x : G) ∈ E := fun x => Subgroup.mem_subgroupOf
  have hEXcard : Nat.card EX = 9 := by
    rw [hEX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE9]
  set E' : Subgroup (Equiv.Perm (Fin 6156)) := EX.map θ with hE'
  have hE'card : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective hθinj, hEXcard]
  set W : Subgroup (Equiv.Perm (Fin 6156)) :=
    (U.subgroupOf (Subgroup.normalizer (L : Set G))).map Φ with hW
  have hUsub : Nat.card (U.subgroupOf (Subgroup.normalizer (L : Set G))) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv, hU4]
  have hWle : W ≤ j3R := by
    rintro _ ⟨n, -, rfl⟩
    exact hTR _
  have hW2 : ∀ w ∈ W, w ^ 2 = 1 := by
    rintro _ ⟨n, hn, rfl⟩
    rw [← map_pow]
    have : n ^ 2 = 1 := Subtype.ext (by simpa using hU2 n (Subgroup.mem_subgroupOf.1 hn))
    rw [this, map_one]
  have hW4 : Nat.card W ≤ 4 := by
    rw [← hUsub]
    exact Nat.card_le_card_of_surjective
      (Φ.subgroupMap (U.subgroupOf (Subgroup.normalizer (L : Set G))))
      (Φ.subgroupMap_surjective _)
  have hE'P : E' ≤ j3P := by
    rintro _ ⟨x, -, rfl⟩
    rw [hθ]; exact (ψ _).2
  have hE'3 : ∀ b ∈ E', b ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE3 x ((hEXmem x).1 hx), map_one]
  have hE'9 : 9 ≤ Nat.card E' := hE'card.ge
  have hodd : ∀ b ∈ E', b ≠ 1 →
      Odd (Nat.card (centralizer ({b} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
        Subgroup (Equiv.Perm (Fin 6156)))) := by
    rintro _ ⟨x, hx, rfl⟩ hb1
    have hx1 : x ≠ 1 := by
      intro hx1
      apply hb1
      rw [hx1, map_one]
    rw [hθ, ← CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv ψ,
      hEB x ((hEXmem x).1 hx) hx1]
    exact ⟨121, by norm_num⟩
  have hNW : ∀ b ∈ E', ∀ w ∈ W, b * w * b⁻¹ ∈ W := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨n, hn, rfl⟩
    have hxE : (x : G) ∈ E := (hEXmem x).1 hx
    have hnU : (n : G) ∈ U := Subgroup.mem_subgroupOf.1 hn
    have hconj : (⟨(x : G), hmemN x⟩ : ↥(Subgroup.normalizer (L : Set G))) * n *
        (⟨(x : G), hmemN x⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ ∈
        U.subgroupOf (Subgroup.normalizer (L : Set G)) := by
      rw [Subgroup.mem_subgroupOf]
      exact hEU _ hxE _ hnU
    have := Subgroup.mem_map_of_mem Φ hconj
    rw [map_mul, map_mul, map_inv, hΦL] at this
    rw [hθ]
    exact this
  have hW0 : W = ⊥ := R_key hWle hW2 hW4 hE'P hE'3 hE'9 hodd hNW
  have hUc : ∀ u ∈ U, ∀ x ∈ L, u * x * u⁻¹ = x := by
    intro u hu x hx
    have hΦu : Φ ⟨u, hUN hu⟩ = 1 := by
      have : Φ ⟨u, hUN hu⟩ ∈ W := Subgroup.mem_map_of_mem Φ (Subgroup.mem_subgroupOf.2 hu)
      rw [hW0] at this
      exact Subgroup.mem_bot.1 this
    have hσ : L.normalizerMonoidHom ⟨u, hUN hu⟩ = 1 := hTinj _ hΦu
    have := congrArg (fun σ : MulAut ↥L => ((σ ⟨x, hx⟩ : ↥L) : G)) hσ
    simpa [hΦapp] using this
  have hcomm : ⁅L, U⁆ = ⊥ := by
    rw [Subgroup.commutator_def, Subgroup.closure_eq_bot_iff]
    rintro _ ⟨l, hl, u, hu, rfl⟩
    show ⁅l, u⁆ = 1
    rw [commutatorElement_def]
    have h1 := hUc u hu l hl
    have hc : u * l = l * u := by
      calc u * l = (u * l * u⁻¹) * u := by group
        _ = l * u := by rw [h1]
    rw [← hc]; group
  have hL0 : L = ⊥ := by rw [← hLU, hcomm]
  have hsub : Subsingleton ↥L := ⟨fun a b => Subtype.ext
    ((Subgroup.mem_bot.1 (hL0 ▸ a.2)).trans (Subgroup.mem_bot.1 (hL0 ▸ b.2)).symm)⟩
  obtain ⟨-, -, a, b, hab⟩ := hq
  exact hab (by rw [Subsingleton.elim a b])

end PureThreeB

section FrameProof

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

theorem CoverOut.eq_one_of_mem_zpowers_of_mem (h : CoverOut A E U c L) {x : G}
    (hx : x ∈ Subgroup.zpowers c) (hxL : x ∈ L) : x = 1 := by
  rcases mem_zpowers_of_pow_three h.c_cubed hx with h1 | h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hxL) h.notMem
  · exfalso
    apply h.notMem
    have hcx : c = x ^ 2 := by
      rw [h1]
      have : (c ^ 2) ^ 2 = c ^ 3 * c := by group
      rw [this, h.c_cubed, one_mul]
    rw [hcx]
    exact L.pow_mem hxL 2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.card_inf_E (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) :
    Nat.card (E ⊓ L : Subgroup G) = 9 := by
  have hEA : E ≤ A := h.pair.mem_E.2
  have hcE : c ∈ E := (mem_lThreeStarPairs_iff.mp h.pair.mem_pair).1.1
  have hE27 : Nat.card E = 27 := h.pair.mem_E.1.2.1
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hab.1 x hx y hy
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((E ⊓ L : Subgroup G) : Set G))
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcomm x (hEA hx.1) c h.c_mem_A)
  have hdisj : Disjoint (E ⊓ L) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxc
    exact h.eq_one_of_mem_zpowers_of_mem hxc hxE.2
  have hcard := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj
  have hEeq : E ⊓ L ⊔ Subgroup.zpowers c = E := by
    apply le_antisymm
    · exact sup_le inf_le_left (Subgroup.zpowers_le.2 hcE)
    · intro x hx
      obtain ⟨l, hl, i, rfl⟩ := h.decomp_A h45 x (hEA hx)
      have hci : c ^ i ∈ E := Subgroup.zpow_mem _ hcE i
      have hlE : l ∈ E := by
        have : l = (l * c ^ i) * (c ^ i)⁻¹ := by group
        rw [this]
        exact E.mul_mem hx (E.inv_mem hci)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlE, hl.2⟩)
        (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers c i))
  rw [hEeq, hE27, Nat.card_zpowers, orderOf_eq_prime h.c_cubed h.c_ne_one] at hcard
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sec217OutFrame_of (h45 : Sec4.Item4_5) :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      CoverOut A E U c L → ∃ a : G, Frame217 E c L a := by
  intro G _ _ A E U c L h
  have hZ := h.center_eq_bot h45
  obtain ⟨e⟩ := h.quot
  have hQ : Nat.card (↥L ⧸ center ↥L) = 50232960 := by
    rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.J3.card_J3
  have hq : CFSG.IsQuasisimple ↥L := isQuasisimple_of_perfect_J3 h.perfect e
  have hEA : E ≤ A := h.pair.mem_E.2
  have hpairs := mem_lThreeStarPairs_iff.mp h.pair.mem_pair
  have hcE : c ∈ E := hpairs.1.1
  obtain ⟨hEN, hUea, hU4⟩ := mem_fourGroups_iff.1 h.pair.mem_U
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := (isElemAbelian_iff.1 hUea).2
  have hUN : U ≤ Subgroup.normalizer (L : Set G) := hpairs.2.2.2.1
  have hLU : ⁅L, U⁆ = L := hpairs.2.2.2.2.2.1
  have hEU : ∀ x ∈ E, ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro x hx u hu
    exact ((Subgroup.mem_normalizer_iff.1 (hEN hx)) u).1 hu
  have hab := isElemAbelian_iff.1 h.isElemAbelian_A
  obtain ⟨f, hfE, hf1, hfnc⟩ : ∃ f : ↥L, (f : G) ∈ E ∧ f ≠ 1 ∧
      NonCentral 3 (f : ↥L ⧸ center ↥L) := by
    by_contra hno
    push Not at hno
    refine false_of_pure3B_plain hq hZ (e.trans Item228CensusProof.j3CarrierEquiv)
      (E := E ⊓ L) inf_le_right (h.card_inf_E h45) ?_ ?_ hUN hU4 hU2
      (fun x hx u hu => hEU x hx.1 u hu) hLU
    · intro x hx
      exact Subtype.ext (hab.2 (x : G) (hEA hx.1))
    · intro x hx hx1
      have hx3 : (x : ↥L ⧸ center ↥L) ^ 3 = 1 := by
        rw [← QuotientGroup.mk_pow]
        have : x ^ 3 = 1 := Subtype.ext (hab.2 (x : G) (hEA hx.1))
        rw [this]; rfl
      have hx1' : (x : ↥L ⧸ center ↥L) ≠ 1 := fun h1 => by
        have := (QuotientGroup.eq_one_iff x).1 h1
        rw [hZ, Subgroup.mem_bot] at this
        exact hx1 this
      rcases card_centralizer_of_equiv_J3_dichotomy e hx3 hx1' with h1 | h1
      · exfalso
        exact hno x hx.1 hx1 (nonCentral_of_card_centralizer hQ h1)
      · exact h1
  refine ⟨(f : G), ⟨hfE, ?_, ⟨f, ⟨1, one_mem _, by simp⟩, hfnc⟩⟩⟩
  intro hmem
  apply hf1
  exact Subtype.ext (h.eq_one_of_mem_zpowers_of_mem hmem f.2)

end FrameProof

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
