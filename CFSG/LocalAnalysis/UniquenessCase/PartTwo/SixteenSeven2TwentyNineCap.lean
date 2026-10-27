module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCoreA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrame
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineNorm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_isIrr_action_nontrivial {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {V : Subgroup W} (hV : XMod.IsIrr ↥L V)
    (hc : Nat.card ↥V = 8) : ∃ x ∈ L, ∃ v ∈ V, x v ≠ v := by
  by_contra hcon
  have htriv : ∀ x ∈ L, ∀ v ∈ V, x v = v := by
    intro x hx v hv
    by_contra hne
    exact hcon ⟨x, hx, v, hv, hne⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥V) 2 (by rw [hc]; norm_num)
  let J : Subgroup W := Subgroup.zpowers (x₀ : W)
  have hxV : (x₀ : W) ∈ V := x₀.2
  have hJV : J ≤ V := Subgroup.zpowers_le.mpr hxV
  have hJcard : Nat.card J = 2 := by
    change Nat.card (Subgroup.zpowers (x₀ : W)) = 2
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx₀]
  have hJinv : XMod.IsInv ↥L J := by
    intro a l hl
    have hlV : l ∈ V := hJV hl
    have hfix : (a : MulAut W) l = l := htriv a a.2 l hlV
    show (a : MulAut W) l ∈ J
    rw [hfix]; exact hl
  have hJbot : J ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hJcard
    omega
  have hJtop : J ≠ V := by
    intro h
    rw [h, hc] at hJcard
    omega
  rcases hV.2.2 J hJinv bot_le hJV with h | h
  · exact hJbot h
  · exact hJtop h

private theorem s16c167_natSum3_ker_index_le_four {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L Z : Subgroup (MulAut W)} {J : Subgroup W}
    (hL : IsPSL 3 2 1 ↥L) (hJ : NatSum3 L J) (hZ : Nat.card ↥Z = 7)
    (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w)
    {A : Type} [Group A] [Finite A] (hA2 : IsPGroup 2 A) (f : A →* MulAut W)
    (hf2 : ∀ a : A, (f a) ^ 2 = 1)
    (hfL : ∀ a : A, L.map (MulAut.conj (f a)).toMonoidHom = L)
    (hfZ : ∀ a : A, Z.map (MulAut.conj (f a)).toMonoidHom = Z)
    (hfJ : ∀ a : A, J.map (f a).toMonoidHom = J)
    (hker : ∀ a : A, f a = 1 ↔ ∀ w ∈ J, f a w = w)
    {Y : Subgroup W} (hYJ : Y ≤ J) (hYfix : ∀ a : A, ∀ y ∈ Y, f a y = y)
    (hrk : 6 ≤ rk ↥Y) : (MonoidHom.ker f).index ≤ 4 := by
  classical
  have hJkeep := hJ
  obtain ⟨I₀, I₁, I₂, hI₀, -, -, hc₀, -, -, h01, h012, hsum⟩ := hJ
  have hI₀J : I₀ ≤ J := by
    rw [← hsum]
    exact le_sup_left.trans le_sup_left
  have hnt : ∃ x ∈ L, ∃ v ∈ I₀, x v ≠ v :=
    s16c167_isIrr_action_nontrivial hI₀ hc₀
  have hI₀inv : ∀ x ∈ L, ∀ v ∈ I₀, x v ∈ I₀ := fun x hx v hv => hI₀.1 ⟨x, hx⟩ v hv
  have hfaith : ∀ l ∈ L, (∀ w ∈ J, l w = w) → l = 1 := by
    intro l hl hfix
    exact rank3_inj hL hI₀inv hnt l hl (fun v hv => hfix v (hI₀J hv))
  have hex : ∀ a : A, ∃ l : L, ∀ w ∈ J, f a w = (l : MulAut W) w := by
    intro a
    have h2 : (f a) ^ (2 ^ 1) = 1 := by simpa using hf2 a
    obtain ⟨l, hl, hle⟩ := (s16c167_natSum3_normalizer_two hW hL hJkeep hZ hZL hZJ hZf h2
      (hfZ a) (hfL a) (hfJ a)).1
    exact ⟨⟨l, hl⟩, hle⟩
  let φfun : A → L := fun a => Classical.choose (hex a)
  have hφspec : ∀ a w (hw : w ∈ J), f a w = (φfun a : MulAut W) w :=
    fun a w hw => Classical.choose_spec (hex a) w hw
  have hmul : ∀ a b : A, φfun (a * b) = φfun a * φfun b := by
    intro a b
    apply Subtype.ext
    change (φfun (a * b) : MulAut W) = (φfun a : MulAut W) * (φfun b : MulAut W)
    rw [← inv_mul_eq_one]
    have hmem : ((φfun (a * b) : MulAut W))⁻¹ *
        ((φfun a : MulAut W) * (φfun b : MulAut W)) ∈ L :=
      L.mul_mem (L.inv_mem (φfun (a * b)).2) (L.mul_mem (φfun a).2 (φfun b).2)
    have hfix : ∀ w ∈ J, (((φfun (a * b) : MulAut W))⁻¹ *
        ((φfun a : MulAut W) * (φfun b : MulAut W))) w = w := by
      intro w hw
      have hbw : f b w ∈ J := by
        have hmem2 : f b w ∈ J.map (f b).toMonoidHom := Subgroup.mem_map_of_mem _ hw
        rwa [hfJ b] at hmem2
      have h1 : (φfun b : MulAut W) w = f b w := (hφspec b w hw).symm
      have h2 : (φfun a : MulAut W) (f b w) = f a (f b w) := (hφspec a (f b w) hbw).symm
      have h3 : (φfun (a * b) : MulAut W) w = f (a * b) w := (hφspec (a * b) w hw).symm
      calc (((φfun (a * b) : MulAut W))⁻¹ *
            ((φfun a : MulAut W) * (φfun b : MulAut W))) w
          = ((φfun (a * b) : MulAut W))⁻¹
              (((φfun a : MulAut W) * (φfun b : MulAut W)) w) := by rw [MulAut.mul_apply]
        _ = ((φfun (a * b) : MulAut W))⁻¹
              ((φfun a : MulAut W) ((φfun b : MulAut W) w)) := by rw [MulAut.mul_apply]
        _ = ((φfun (a * b) : MulAut W))⁻¹ (f a (f b w)) := by rw [h1, h2]
        _ = ((φfun (a * b) : MulAut W))⁻¹ (f (a * b) w) := by
              rw [show f (a * b) w = f a (f b w) by rw [map_mul, MulAut.mul_apply]]
        _ = ((φfun (a * b) : MulAut W))⁻¹ ((φfun (a * b) : MulAut W) w) := by rw [h3]
        _ = w := MulAut.inv_apply_self W (φfun (a * b) : MulAut W) w
    exact hfaith _ hmem hfix
  let φ : A →* L := MonoidHom.mk' φfun hmul
  have hφspec' : ∀ a w (hw : w ∈ J), f a w = (φ a : MulAut W) w := hφspec
  have hφker : MonoidHom.ker φ = MonoidHom.ker f := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro ha
      rw [hker a]
      intro w hw
      have h1 : (φ a : MulAut W) w = w := by rw [ha]; rfl
      rw [hφspec' a w hw]
      exact h1
    · intro ha
      apply Subtype.ext
      apply hfaith (φ a : MulAut W) (φ a).2
      intro w hw
      rw [← hφspec' a w hw, ha]
      rfl
  have hQ : IsPGroup 2 ((φ.range).map L.subtype) := by
    have h1 : IsPGroup 2 φ.range := by
      rw [MonoidHom.range_eq_map]
      exact (hA2.to_subgroup (⊤ : Subgroup A)).map φ
    exact h1.map L.subtype
  have hYfix' : ∀ q ∈ (φ.range).map L.subtype, ∀ y ∈ Y, q y = y := by
    intro q hq y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨a, -, rfl⟩ := MonoidHom.mem_range.1 hl
    change (φ a : MulAut W) y = y
    rw [← hφspec' a y (hYJ hy)]
    exact hYfix a y hy
  have hsub : (φ.range).map L.subtype ≤ L := Subgroup.map_subtype_le (H := L) φ.range
  have hYJfix : Y ≤ J ⊓ fixV ((φ.range).map L.subtype) :=
    le_inf hYJ (fun y hy => mem_fixV.2 (fun q hq => hYfix' q hq y hy))
  have hcard := s16c167_natSum3_few_fixers hW hL hJkeep hsub hQ hYJfix hrk
  have hcard2 : Nat.card ((φ.range).map L.subtype) = Nat.card φ.range :=
    Subgroup.card_map_of_injective (f := L.subtype) (K := φ.range) (Subgroup.subtype_injective L)
  have hidx : (MonoidHom.ker f).index = Nat.card φ.range := by
    rw [← hφker, Subgroup.index_ker φ]
  rw [hidx]
  exact hcard2 ▸ hcard

theorem s16c167_twenty_nine_cap (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hC : Counterex16 D ⊥ V L hV)
    (h14 : ((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V) {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)}
    (hA : Choice1613 D ⊥ V hV L A) (hAg : A ≤ conjSubgroup V g)
    (hΔ : Concl1617 D ⊥ V hV L A g Δ) (hI : Insp18 D ⊥ V hV L g Δ)
    (h9 : Case168_9 D ⊥ V hV L) {B U : Subgroup G} (hBU : Hyperplane1618 V A B U) :
    E3.mQuot U (V ⊓ centralizer (A : Set G)) ≤ 2 := by
  classical
  have h2f : ¬ Case168_2 D ⊥ V hV L := by
    intro h2
    have h3 : D.sig = {3} := ((case168_2_iff_shape D ⊥ V hV L).1 h2).2.2
    have h7 : D.sig = {7} := h9.2.2.2.2
    rw [h3] at h7
    exact absurd h7 (by norm_num)
  have hMV : D.M ≤ normalizer (V : Set G) :=
    le_of_eq hC.setting.hyp16.hyp125.normalizer_eq.symm
  have hV' : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hBA : B ≤ A := hBU.1
  have hUeq : U = V ⊓ centralizer (B : Set G) := hBU.2.2.1
  have h18 := s16c167_eighteen_core D hV hC.setting.hyp16 h14 hA.1 hAg hΔ hI hBU
  have hmB : E3.mQuot (conjSubgroup V g) B = D.k + 1 := h18.1.1.trans h18.1.2
  have huniq := h18.2.2.1 h2f
  have hBg : B ∈ E3.gammaSet V (D.k + 1) D.M :=
    ⟨hBA.trans (hA.1.1.trans D.sylowM.le), g, hBA.trans hAg, hmB⟩
  have h0 : mSub (⊥ : Subgroup G) = 0 := by rw [mSub]; exact rk_bot
  have hi : ((D.k + 1 + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
    rw [h0, Nat.add_zero]
    exact lt_trans (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self (D.k + 1))) h14
  have hUM : U ≤ conjSubgroup D.M g := by
    rw [hUeq]
    exact (sixteen_twentyThree_one_bot D hC.setting.hyp16 hBg (hBA.trans hAg) hi).2.2
  have hUV : U ≤ V := by rw [hUeq]; exact inf_le_left
  have hUVM : U ≤ V ⊓ conjSubgroup D.M g := le_inf hUV hUM
  have hk3 : D.k + 1 ≤ 3 := by
    have hle : mBar D.M ⊥ V hV ≤ 3 := by
      have hng := hC.setting.hyp16.not_gt
      have hiff := mBarGT_iff_lt_mBar D.M ⊥ V hV bot_le hMV
        (by
          intro m _
          rw [Subgroup.mem_normalizer_iff]
          intro x
          rw [Subgroup.mem_bot, Subgroup.mem_bot]
          constructor
          · intro h; rw [h]; group
          · intro h
            calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
              _ = 1 := by rw [h]; group) 3
      rw [hiff] at hng
      exact not_lt.1 hng
    omega
  have hfixG : ∀ u ∈ U, ∀ J ∈ deltaConj Δ g, conjSubgroup J u = J := by
    intro u huU J hJ
    obtain ⟨I, hIΔ, rfl⟩ := hJ
    have hIV : I ≤ V := hΔ.2.1 I hIΔ
    have hJV : conjSubgroup I g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hIV
    have huVM : u ∈ V ⊓ conjSubgroup D.M g := hUVM huU
    have huCB : u ∈ centralizer (B : Set G) := by
      have := huU
      rw [hUeq] at this
      exact this.2
    have hBCu : B ≤ conjSubgroup V g ⊓ centralizer ({u} : Set G) := by
      refine le_inf (hBA.trans hAg) ?_
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 huCB b hb
    have hmE_le : E3.mQuot (conjSubgroup V g)
        (conjSubgroup V g ⊓ centralizer ({u} : Set G)) ≤ D.k + 1 :=
      (E3.mQuot_mono hBCu).trans_eq hmB
    rcases hI.disj u huVM hmE_le (conjSubgroup I g) ⟨I, hIΔ, rfl⟩ with hfix | hbot
    · exact hfix
    · exfalso
      have hle := s16c167_swap_rk_le hV' hJV hbot rfl
      exact absurd (hI.big (conjSubgroup I g) ⟨I, hIΔ, rfl⟩)
        (not_lt.2 (hle.trans hmE_le))
  have hΓcard : (deltaConj Δ g).ncard = 2 := by
    unfold deltaConj
    have h := Set.ncard_image_of_injective (s := Δ) (f := fun I => conjSubgroup I g)
      (fun A B hAB => by
        have hc := congrArg (fun C => conjSubgroup C g⁻¹) hAB
        rwa [E3.conjSubgroup_conj_inv, E3.conjSubgroup_conj_inv] at hc)
    rw [h, hΔ.1]
  let F : Subgroup G := Classical.choose huniq
  have hFmem : F ∈ deltaConj Δ g ∧ F ≤ B := (Classical.choose_spec huniq).1
  have hFuniq : ∀ J, J ∈ deltaConj Δ g ∧ J ≤ B → J = F :=
    (Classical.choose_spec huniq).2
  have hexE : ∃ E ∈ deltaConj Δ g, E ≠ F :=
    Set.exists_ne_of_one_lt_ncard (s := deltaConj Δ g) (by rw [hΓcard]; norm_num) F
  let E : Subgroup G := Classical.choose hexE
  have hEmem : E ∈ deltaConj Δ g := (Classical.choose_spec hexE).1
  have hEF : E ≠ F := (Classical.choose_spec hexE).2
  have hEB : ¬ E ≤ B := fun h => hEF (hFuniq E ⟨hEmem, h⟩)
  let I_E : Subgroup G := conjSubgroup E g⁻¹
  let I_F : Subgroup G := conjSubgroup F g⁻¹
  have hIEΔ : I_E ∈ Δ := by
    obtain ⟨I, hIΔ, hIeq⟩ := hEmem
    have hIEeq : I_E = I := by
      show conjSubgroup E g⁻¹ = I
      rw [← hIeq, E3.conjSubgroup_conj_inv]
    rw [hIEeq]; exact hIΔ
  have hIFΔ : I_F ∈ Δ := by
    obtain ⟨I, hIΔ, hIeq⟩ := hFmem.1
    have hIFeq : I_F = I := by
      show conjSubgroup F g⁻¹ = I
      rw [← hIeq, E3.conjSubgroup_conj_inv]
    rw [hIFeq]; exact hIΔ
  have hIEg : conjSubgroup I_E g = E := by
    show conjSubgroup (conjSubgroup E g⁻¹) g = E
    exact E3.conjSubgroup_inv_conj E g
  have hIFg : conjSubgroup I_F g = F := by
    show conjSubgroup (conjSubgroup F g⁻¹) g = F
    exact E3.conjSubgroup_inv_conj F g
  have hIEneIF : I_E ≠ I_F := by
    intro h
    apply hEF
    have hc : conjSubgroup I_E g = conjSubgroup I_F g := congrArg _ h
    rwa [hIEg, hIFg] at hc
  have hΔpair : Δ = {I_E, I_F} := by
    have hsub : ({I_E, I_F} : Set (Subgroup G)) ⊆ Δ := by
      intro X hX
      rcases Set.mem_insert_iff.1 hX with rfl | hX
      · exact hIEΔ
      · rw [Set.mem_singleton_iff] at hX; rw [hX]; exact hIFΔ
    exact (Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_pair hIEneIF, hΔ.1])).symm
  have hΓpair : deltaConj Δ g = {E, F} := by
    unfold deltaConj
    rw [hΔpair, Set.image_pair, hIEg, hIFg]
  have hindΔ' : sSupIndep ({I_E, I_F} : Set (Subgroup G)) := hΔpair ▸ hΔ.2.2.1
  have hsupΔ' : sSup ({I_E, I_F} : Set (Subgroup G)) = V := hΔpair ▸ hΔ.2.2.2.1
  have hdisjIF : I_E ⊓ I_F = ⊥ := disjoint_iff.1 ((sSupIndep_pair hIEneIF).1 hindΔ')
  have hsupIF : I_E ⊔ I_F = V := by have h := hsupΔ'; rwa [sSup_pair] at h
  have hEV' : E ≤ conjSubgroup V g := hIEg ▸ E3.conjSubgroup_mono_left g (hΔ.2.1 I_E hIEΔ)
  have hFV' : F ≤ conjSubgroup V g := hIFg ▸ E3.conjSubgroup_mono_left g (hΔ.2.1 I_F hIFΔ)
  have hdisjEF : E ⊓ F = ⊥ := by
    rw [show E = conjSubgroup I_E g from hIEg.symm,
      show F = conjSubgroup I_F g from hIFg.symm, ← E3.conjSubgroup_inf, hdisjIF,
      E3.conjSubgroup_bot]
  have hsupEF : E ⊔ F = conjSubgroup V g := by
    rw [show E = conjSubgroup I_E g from hIEg.symm,
      show F = conjSubgroup I_F g from hIFg.symm]
    unfold conjSubgroup
    rw [← Subgroup.map_sup, hsupIF]
  have hFB : F ≤ B := hFmem.2
  have hBsplit : B = (E ⊓ B) ⊔ (F ⊓ B) := by
    have h := h18.2.1.2.2
    rw [hΓpair, iSup_pair] at h
    simpa only [inf_comm] using h
  have hsplitB := s16c167_mQuot_split hV' hEV' hFV' hdisjEF hsupEF (hBA.trans hAg) hBsplit
  have hmBE : E3.mQuot E (B ⊓ E) = E3.mQuot (conjSubgroup V g) B := by
    have hz : E3.mQuot F (F ⊓ B) = 0 := by
      rw [inf_eq_left.mpr hFB, E3.mQuot_self]
    rw [hsplitB, hz, Nat.add_zero, inf_comm]
  have hmBE_le : E3.mQuot E (B ⊓ E) ≤ 3 := by rw [hmBE, hmB]; exact hk3
  have hJ : NatSum3 (lBar ⊥ V hV L) (wTil ⊥ V hV L) :=
    s16c167_natSum3_of_sumOfNat h9.2.2.2.1
  have hIEV : I_E ≤ V := hΔ.2.1 I_E hIEΔ
  let J_E : Subgroup (Vtil ⊥ V hV) := imgTil ⊥ V hV I_E
  let J_F : Subgroup (Vtil ⊥ V hV) := imgTil ⊥ V hV I_F
  have hIEimg : rk J_E = rk ↥I_E := s16c167_rk_imgTil hV hIEV
  have hIErk : rk ↥I_E = rk ↥E := by
    show rk ↥(conjSubgroup E g⁻¹) = rk ↥E
    unfold rk
    rw [E3.card_conjSubgroup]
  have hcj : imgTil ⊥ V hV '' Δ =
      conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (lBar ⊥ V hV L)) := by
    rw [hΔ.2.2.2.2.2.2 (Or.inl h9)]
    exact s16c167_imgTil_wConj hV hMV L
  have hJE_mem : J_E ∈ conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (lBar ⊥ V hV L)) := by
    rw [← hcj]
    exact Set.mem_image_of_mem _ hIEΔ
  obtain ⟨φ, hφMbar, hφJE⟩ := hJE_mem
  have hrkE : rk ↥E = 9 := by
    have h1 : rk ↥((wTil ⊥ V hV L).map φ.toMonoidHom) = 9 :=
      s16c167_rk_natSum3 (s16c167_natSum3_conj (L := lBar ⊥ V hV L)
        (J := wTil ⊥ V hV L) hJ φ)
    have h2 : rk J_E = 9 := by rw [hφJE]; exact h1
    have h3 : rk J_E = rk ↥I_E := hIEimg
    have h4 : rk ↥I_E = rk ↥E := hIErk
    omega
  have hmqbot : ∀ X : Subgroup G, E3.mQuot X ⊥ = rk ↥X := by
    intro X
    unfold E3.mQuot rk
    rw [Subgroup.relIndex_bot_left]
  have hrkBE : rk ↥(B ⊓ E) = 9 - E3.mQuot E (B ⊓ E) := by
    have hadd := E3.mQuot_add (V := E) (U := (⊥ : Subgroup G)) (U' := B ⊓ E)
      bot_le inf_le_right
    rw [hmqbot, hmqbot] at hadd
    omega
  have hrkBE_ge : 6 ≤ rk ↥(B ⊓ E) := by rw [hrkBE]; omega
  have hBEV : conjSubgroup (B ⊓ E) g⁻¹ ≤ V := by
    calc conjSubgroup (B ⊓ E) g⁻¹ ≤ conjSubgroup (conjSubgroup V g) g⁻¹ :=
          E3.conjSubgroup_mono_left g⁻¹ (inf_le_right.trans hEV')
      _ = V := E3.conjSubgroup_conj_inv V g
  let Y : Subgroup (Vtil ⊥ V hV) := imgTil ⊥ V hV (conjSubgroup (B ⊓ E) g⁻¹)
  have hYrk : rk ↥Y = rk ↥(B ⊓ E) := by
    have h1 := s16c167_rk_imgTil hV hBEV
    have h2 : rk ↥(conjSubgroup (B ⊓ E) g⁻¹) = rk ↥(B ⊓ E) := by
      unfold rk; rw [E3.card_conjSubgroup]
    rw [show Y = imgTil ⊥ V hV (conjSubgroup (B ⊓ E) g⁻¹) from rfl, h1, h2]
  have hrk : 6 ≤ rk ↥Y := by rw [hYrk]; exact hrkBE_ge
  have hYJ : Y ≤ J_E :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono V (E3.conjSubgroup_mono_left g⁻¹ inf_le_right))
  obtain ⟨Z, -, hZcard, -, hZnorm, hZL, hZJ, hZf, -⟩ :=
    s16c167_case9_frame D hC hΔ h9
  have hL9 : IsPSL 3 2 1 ↥(lBar ⊥ V hV L) := s16c167_isPSL_of_isL3 h9.2.1
  let L_E : Subgroup (MulAut (Vtil ⊥ V hV)) := (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom
  have hL_E : IsPSL 3 2 1 ↥L_E := by
    have h := isPSL_conjAutSub φ hL9
    rwa [show conjAutSub φ (lBar ⊥ V hV L) = L_E from rfl] at h
  have hJ_E : NatSum3 L_E J_E := by
    rw [show J_E = (wTil ⊥ V hV L).map φ.toMonoidHom from hφJE]
    exact s16c167_natSum3_conj (L := lBar ⊥ V hV L) (J := wTil ⊥ V hV L) hJ φ
  have hZLE : ∀ z ∈ Z, ∀ l ∈ L_E, z * l = l * z := by
    intro z hz l hl
    obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.1 hl
    have hz' : MulAut.conj φ⁻¹ z ∈ Z := by
      have h := hZnorm φ⁻¹ ((Mbar D.M ⊥ V hV).inv_mem hφMbar)
      rw [← h]; exact Subgroup.mem_map_of_mem _ hz
    have hcomm := hZL (MulAut.conj φ⁻¹ z) hz' l₀ hl₀
    show z * (φ * l₀ * φ⁻¹) = (φ * l₀ * φ⁻¹) * z
    calc z * (φ * l₀ * φ⁻¹) = φ * ((MulAut.conj φ⁻¹) z * l₀) * φ⁻¹ := by
          rw [MulAut.conj_apply]; group
      _ = φ * (l₀ * (MulAut.conj φ⁻¹) z) * φ⁻¹ := by rw [hcomm]
      _ = (φ * l₀ * φ⁻¹) * z := by rw [MulAut.conj_apply]; group
  have hZJE : ∀ z ∈ Z, ∀ w ∈ J_E, z w ∈ J_E := by
    intro z hz w hw
    rw [show J_E = (wTil ⊥ V hV L).map φ.toMonoidHom from hφJE] at hw ⊢
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    have hz' : MulAut.conj φ⁻¹ z ∈ Z := by
      have h := hZnorm φ⁻¹ ((Mbar D.M ⊥ V hV).inv_mem hφMbar)
      rw [← h]; exact Subgroup.mem_map_of_mem _ hz
    have h1 := hZJ (MulAut.conj φ⁻¹ z) hz' w₀ hw₀
    have hφz : z ((MulEquiv.toMonoidHom φ) w₀) =
        (MulEquiv.toMonoidHom φ) (((MulAut.conj φ⁻¹) z) w₀) := by
      change z (φ w₀) = φ (((MulAut.conj φ⁻¹) z) w₀)
      rw [← MulAut.mul_apply, ← MulAut.mul_apply]
      congr 1
      rw [MulAut.conj_apply]; group
    rw [hφz]
    exact Subgroup.mem_map_of_mem _ h1
  have hZfE : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J_E, z w ≠ w := by
    intro z hz hz1
    by_contra hcon
    have hfixE : ∀ w ∈ J_E, z w = w := by
      intro w hw
      by_contra hne
      exact hcon ⟨w, hw, hne⟩
    have hz' : MulAut.conj φ⁻¹ z ∈ Z := by
      have h := hZnorm φ⁻¹ ((Mbar D.M ⊥ V hV).inv_mem hφMbar)
      rw [← h]; exact Subgroup.mem_map_of_mem _ hz
    have hz'ne : MulAut.conj φ⁻¹ z ≠ 1 := by
      intro h1
      refine hz1 ?_
      have hφz : (MulAut.conj φ) ((MulAut.conj φ⁻¹) z) = z := by
        rw [MulAut.conj_apply, MulAut.conj_apply]; group
      have h2 := congrArg (MulAut.conj φ) h1
      rw [hφz] at h2
      simpa [MulAut.conj_apply] using h2
    obtain ⟨w, hw, hne⟩ := hZf (MulAut.conj φ⁻¹ z) hz' hz'ne
    refine hne ?_
    have hmem : φ w ∈ J_E := by
      rw [show J_E = (wTil ⊥ V hV L).map φ.toMonoidHom from hφJE]
      exact Subgroup.mem_map_of_mem _ hw
    have h1 : z (φ w) = φ w := hfixE _ hmem
    have h2 : φ ((MulAut.conj φ⁻¹ z) w) = φ w := by
      rw [← MulAut.mul_apply, show φ * MulAut.conj φ⁻¹ z = z * φ by
        rw [MulAut.conj_apply]; group, MulAut.mul_apply, h1]
    exact φ.injective h2
  have huM : ∀ u : U, g * (u : G) * g⁻¹ ∈ D.M := fun u =>
    mem_conjSubgroup_iff.1 (hUM u.2)
  let conjU : U →* stabTil (⊥ : Subgroup G) V :=
    { toFun := fun u => ⟨g * (u : G) * g⁻¹, s16c167_mem_stabTil_bot (hMV (huM u))⟩
      map_one' := by
        apply Subtype.ext
        show g * ((1 : U) : G) * g⁻¹ = 1
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        show g * ((u * v : U) : G) * g⁻¹ =
          (g * (u : G) * g⁻¹) * (g * (v : G) * g⁻¹)
        rw [show ((u * v : U) : G) = (u : G) * (v : G) from rfl]
        group }
  let f : U →* MulAut (Vtil ⊥ V hV) := (actTil ⊥ V hV).comp conjU
  have hf_apply : ∀ a : U, f a = actTil ⊥ V hV (conjU a) := fun a => rfl
  have hW : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one ⊥ V hV
  have hconj2 : ∀ a : U, (conjU a : G) ^ 2 = 1 := by
    intro a
    show (g * (a : G) * g⁻¹) ^ 2 = 1
    have ha2 : (a : G) ^ 2 = 1 := hV.2 (a : G) (hUV a.2)
    rw [pow_two] at ha2 ⊢
    calc (g * (a : G) * g⁻¹) * (g * (a : G) * g⁻¹) =
          g * ((a : G) * (a : G)) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hf2 : ∀ a : U, (f a) ^ 2 = 1 := by
    intro a
    have ha1 : a * a = 1 := by
      apply Subtype.ext
      show (a : G) * (a : G) = 1
      rw [← pow_two]; exact hV.2 (a : G) (hUV a.2)
    show (f a) * (f a) = 1
    rw [← map_mul, ha1, map_one]
  have hfZ : ∀ a : U, Z.map (MulAut.conj (f a)).toMonoidHom = Z := fun a =>
    hZnorm (f a) (actTil_mem_barSub ⊥ V hV (huM a) (conjU a).2)
  have hIEnorm : ∀ a : U, conjSubgroup I_E (g * (a : G) * g⁻¹) = I_E := by
    intro a
    have hfixE : conjSubgroup E (a : G) = E := hfixG (a : U) a.2 E hEmem
    have hstep : conjSubgroup I_E (g * (a : G)) = conjSubgroup I_E g := by
      rw [← conjSubgroup_conjSubgroup I_E g (a : G), hIEg, hfixE]
    have h2 : conjSubgroup (conjSubgroup I_E (g * (a : G))) g⁻¹ =
        conjSubgroup (conjSubgroup I_E g) g⁻¹ := congrArg _ hstep
    rw [conjSubgroup_conjSubgroup, E3.conjSubgroup_conj_inv] at h2
    exact h2
  have hfJ : ∀ a : U, J_E.map (f a).toMonoidHom = J_E := by
    intro a
    have hstep := s16c167_imgTil_conjSubgroup hV (conjU a).2 (by simpa using hconj2 a) I_E
    have hIE0 : conjSubgroup I_E (conjU a : G) = I_E := by
      rw [show (conjU a : G) = g * (a : G) * g⁻¹ from rfl]; exact hIEnorm a
    rw [hIE0] at hstep
    exact hstep.symm
  have hcls : Set.ncard {Y : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ ψ ∈ Mbar D.M ⊥ V hV, Y = (lBar ⊥ V hV L).map (MulAut.conj ψ).toMonoidHom} = 2 := by
    have h := h9.2.2.1
    unfold s15 at h
    simpa only [lBar] using h
  have hJ_horb : (conjSubs (Mbar D.M ⊥ V hV) (commSub ⊤ (lBar ⊥ V hV L))).ncard = 2 := by
    obtain ⟨hnΔ, hleΔ, hindΔ, hsumΔ, -⟩ := hΔ
    obtain ⟨hn2, -, -⟩ := s16c167_imgTil_decomp hV hnΔ hleΔ hindΔ hsumΔ
    rw [hcj] at hn2
    exact hn2
  have hcommJ : commSub (⊤ : Subgroup (Vtil ⊥ V hV)) L_E = J_E := by
    rw [show L_E = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom from rfl,
      s16c167_commSub_top_conj φ (lBar ⊥ V hV L)]
    exact hφJE.symm
  have hfL : ∀ a : U, L_E.map (MulAut.conj (f a)).toMonoidHom = L_E := by
    intro a
    refine s16c167_normalizes_of_stab hcls hJ_horb L_E ⟨φ, hφMbar, rfl⟩ (f a)
      (actTil_mem_barSub ⊥ V hV (huM a) (conjU a).2) ?_
    rw [hcommJ, hfJ a]
  have hcenterB : ∀ a : U, ∀ x ∈ conjSubgroup B g⁻¹,
      (conjU a : G) * x * (conjU a)⁻¹ = x := by
    intro a x hx
    have haCB : (a : G) ∈ centralizer (B : Set G) :=
      (Subgroup.mem_inf.1 (hUeq.le a.2)).2
    have hxg : g⁻¹ * x * g ∈ B := by simpa using (mem_conjSubgroup_iff).1 hx
    have hcomm' : (g⁻¹ * x * g) * (a : G) = (a : G) * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_iff.1 haCB (g⁻¹ * x * g) hxg
    have hcomm : (a : G) * (g⁻¹ * x * g) * (a : G)⁻¹ = g⁻¹ * x * g := by
      rw [← hcomm']; group
    show (g * (a : G) * g⁻¹) * x * (g * (a : G) * g⁻¹)⁻¹ = x
    rw [show (g * (a : G) * g⁻¹)⁻¹ = g * (a : G)⁻¹ * g⁻¹ by group]
    calc (g * (a : G) * g⁻¹) * x * (g * (a : G)⁻¹ * g⁻¹)
        = g * ((a : G) * (g⁻¹ * x * g) * (a : G)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hcomm]
      _ = x := by group
  have hcenterBE : ∀ a : U, ∀ x ∈ conjSubgroup (B ⊓ E) g⁻¹,
      (conjU a : G) * x * (conjU a)⁻¹ = x :=
    fun a x hx => hcenterB a x (E3.conjSubgroup_mono_left g⁻¹ inf_le_left hx)
  have hfFixY : ∀ a : U, ∀ y ∈ Y, f a y = y := by
    intro a y hy
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V hV (conjSubgroup (B ⊓ E) g⁻¹) y).1 hy
    rw [hf_apply, actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    exact hcenterBE a x.val hx
  have hcenterIF : ∀ a : U, ∀ x ∈ I_F, (conjU a : G) * x * (conjU a)⁻¹ = x := by
    intro a x hx
    have haCB : (a : G) ∈ centralizer (B : Set G) :=
      (Subgroup.mem_inf.1 (hUeq.le a.2)).2
    have haCF : (a : G) ∈ centralizer (F : Set G) := Subgroup.centralizer_le hFB haCB
    have hxg : g⁻¹ * x * g ∈ F := by simpa using (mem_conjSubgroup_iff).1 hx
    have hcomm' : (g⁻¹ * x * g) * (a : G) = (a : G) * (g⁻¹ * x * g) :=
      Subgroup.mem_centralizer_iff.1 haCF (g⁻¹ * x * g) hxg
    have hcomm : (a : G) * (g⁻¹ * x * g) * (a : G)⁻¹ = g⁻¹ * x * g := by
      rw [← hcomm']; group
    show (g * (a : G) * g⁻¹) * x * (g * (a : G) * g⁻¹)⁻¹ = x
    rw [show (g * (a : G) * g⁻¹)⁻¹ = g * (a : G)⁻¹ * g⁻¹ by group]
    calc (g * (a : G) * g⁻¹) * x * (g * (a : G)⁻¹ * g⁻¹)
        = g * ((a : G) * (g⁻¹ * x * g) * (a : G)⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [hcomm]
      _ = x := by group
  have hfFixF : ∀ a : U, ∀ w ∈ J_F, f a w = w := by
    intro a w hw
    obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V hV I_F w).1 hw
    rw [hf_apply, actTil_mk]
    congr 1
    apply IntMod.val_injective
    rw [actStab_apply_val]
    exact hcenterIF a x.val hx
  have hΔimg : imgTil ⊥ V hV '' Δ = {J_E, J_F} := by
    rw [hΔpair, Set.image_pair]
  have hsupJF : J_E ⊔ J_F = ⊤ := by
    obtain ⟨-, -, hsup2⟩ := s16c167_imgTil_decomp hV hΔ.1 hΔ.2.1 hΔ.2.2.1 hΔ.2.2.2.1
    have h := hsup2
    rw [hΔimg, sSup_pair] at h
    exact h
  have hker : ∀ a : U, f a = 1 ↔ ∀ w ∈ J_E, f a w = w := by
    intro a
    constructor
    · intro h w hw
      rw [h]; rfl
    · intro h
      ext w
      show f a w = w
      have hw' : w ∈ J_E ⊔ J_F := by rw [hsupJF]; exact Subgroup.mem_top w
      rw [Subgroup.mem_sup] at hw'
      obtain ⟨y, hy, z, hz, rfl⟩ := hw'
      rw [map_mul, h y hy, hfFixF a z hz]
  have hA2 : IsPGroup 2 U := B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hUV hV)
  have hcap := s16c167_natSum3_ker_index_le_four hW hL_E hJ_E hZcard hZLE hZJE hZfE
    hA2 f hf2 hfL hfZ hfJ hker hYJ hfFixY hrk
  have hfker : ∀ a : U, f a = 1 ↔ (a : G) ∈ centralizer (conjSubgroup V g : Set G) := by
    intro a
    rw [hf_apply, actTil_eq_one_iff]
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxg : g * x * g⁻¹ ∈ V := (mem_conjSubgroup_iff).1 hx
      have h1 := h (g * x * g⁻¹) hxg
      rw [Subgroup.mem_bot] at h1
      have h2 : (g * (a : G) * g⁻¹) * (g * x * g⁻¹) =
          (g * x * g⁻¹) * (g * (a : G) * g⁻¹) := by
        have h3 := (mul_inv_eq_one.1 h1 : (g * (a : G) * g⁻¹) * (g * x * g⁻¹) *
          (g * (a : G) * g⁻¹)⁻¹ = g * x * g⁻¹)
        calc (g * (a : G) * g⁻¹) * (g * x * g⁻¹)
            = ((g * (a : G) * g⁻¹) * (g * x * g⁻¹) * (g * (a : G) * g⁻¹)⁻¹) *
              (g * (a : G) * g⁻¹) := by group
          _ = (g * x * g⁻¹) * (g * (a : G) * g⁻¹) := by rw [h3]
      have h4 : (a : G) * x = x * (a : G) := by
        have h5 := h2
        rw [show (g * (a : G) * g⁻¹) * (g * x * g⁻¹) = g * ((a : G) * x) * g⁻¹ by group,
          show (g * x * g⁻¹) * (g * (a : G) * g⁻¹) = g * (x * (a : G)) * g⁻¹ by group] at h5
        exact mul_left_cancel (mul_right_cancel h5)
      exact h4.symm
    · intro h
      intro v hv
      rw [Subgroup.mem_bot]
      have hv' : g⁻¹ * v * g ∈ conjSubgroup V g := by
        rw [mem_conjSubgroup_iff]
        convert hv using 1
        group
      have hcomm : (g⁻¹ * v * g) * (a : G) = (a : G) * (g⁻¹ * v * g) :=
        Subgroup.mem_centralizer_iff.1 h (g⁻¹ * v * g) hv'
      have h2 : (g * (a : G) * g⁻¹) * v = v * (g * (a : G) * g⁻¹) := by
        have h3 := hcomm
        calc (g * (a : G) * g⁻¹) * v = g * ((a : G) * (g⁻¹ * v * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * v * g) * (a : G)) * g⁻¹ := by rw [← h3]
          _ = v * (g * (a : G) * g⁻¹) := by group
      have h3 : (g * (a : G) * g⁻¹) * v * (g * (a : G) * g⁻¹)⁻¹ = v := by
        rw [h2]; group
      change (g * (a : G) * g⁻¹) * v * (g * (a : G) * g⁻¹)⁻¹ * v⁻¹ = 1
      rw [h3, mul_inv_cancel]
  have hCker : MonoidHom.ker f =
      (U ⊓ centralizer (conjSubgroup V g : Set G)).subgroupOf U := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨a.2, (hfker a).1 h⟩, fun h => (hfker a).2 h.2⟩
  have hidxker : (MonoidHom.ker f).index =
      (U ⊓ centralizer (conjSubgroup V g : Set G)).relIndex U := by
    rw [hCker]
    rfl
  have hmono : E3.mQuot U (V ⊓ centralizer (A : Set G)) ≤
      E3.mQuot U (U ⊓ centralizer (conjSubgroup V g : Set G)) :=
    E3.mQuot_mono (le_inf (inf_le_left.trans hUV)
      (inf_le_right.trans (Subgroup.centralizer_le hAg)))
  refine hmono.trans ?_
  rw [show E3.mQuot U (U ⊓ centralizer (conjSubgroup V g : Set G)) =
      padicValNat 2 ((MonoidHom.ker f).index) by rw [hidxker]; rfl]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (hA2.to_quotient (MonoidHom.ker f))
  have hk' : (MonoidHom.ker f).index = 2 ^ k := by
    rw [Subgroup.index, hk]
  rw [hk', padicValNat.prime_pow]
  have h2k : 2 ^ k ≤ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hk']
    exact hcap
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2k

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
