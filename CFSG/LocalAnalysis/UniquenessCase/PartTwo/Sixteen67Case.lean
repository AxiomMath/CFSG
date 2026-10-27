module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Quasithin.Background.OddCoprimeFixV
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isPGroup_of_isElemAbelian {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    IsPGroup 2 V :=
  fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩

private theorem wSub_eq_of_barSub_eq {V₀ V L L' : Subgroup G} (hV : IsElemAbelian 2 V)
    (h : barSub V₀ V hV L = barSub V₀ V hV L') :
    wSub V₀ V hV L = wSub V₀ V hV L' := by
  unfold wSub wTil
  rw [h]

theorem s1667_card_wSub (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_3 D V₀ V hV L) :
    Nat.card (wSub V₀ V hV L) = 4 * Nat.card V₀ := by
  have hpf := hS.setting.hyp16.hyp125.pairFacts
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hV₀W : V₀ ≤ wSub V₀ V hV L := s15_Two_le_wSub hV hpf.le L
  have hmSub : mSub (wSub V₀ V hV L) = 2 + mSub V₀ := by
    have h := s15_Infra_mSub_eq_rk_imgTil_add V₀ V (wSub V₀ V hV L) hV hWV
    have himg : imgTil V₀ V hV (wSub V₀ V hV L) = wTil V₀ V hV L :=
      imgTil_preTil V₀ V hV _
    rw [himg, hc.2.1, inf_eq_right.mpr hV₀W] at h
    exact h
  calc Nat.card (wSub V₀ V hV L)
      = 2 ^ mSub (wSub V₀ V hV L) :=
        card_eq_two_pow_mSub ((isPGroup_of_isElemAbelian hV).to_le hWV)
    _ = 2 ^ (2 + mSub V₀) := by rw [hmSub]
    _ = 4 * Nat.card V₀ := by
        rw [pow_add, pow_two, ← card_eq_two_pow_mSub (isPGroup_of_isElemAbelian hpf.elemAbelian₀)]
        ring

theorem s1667_inf_conj_eq (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_3 D V₀ V hV L) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) :
    wSub V₀ V hV L ⊓ conjSubgroup (wSub V₀ V hV L) x = V₀ := by
  have hpf := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hxS : x ∈ stabTil V₀ V := hMs hxM
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨hvW, hvWx⟩ := Subgroup.mem_inf.1 hv
    have hvV : v ∈ V := preTil_le V₀ V hV _ hvW
    have hqvW : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈ wTil V₀ V hV L :=
      (mem_preTil_iff_of_mem V₀ V hV _ hvV).1 hvW
    have hvWx' : v ∈ wSub V₀ V hV (conjSubgroup L x) := by
      rw [s15_Infra_wSub_conjSubgroup V₀ V L hV hxS]
      exact hvWx
    have hqvWx : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈
        wTil V₀ V hV (conjSubgroup L x) :=
      (mem_preTil_iff_of_mem V₀ V hV _ hvV).1 hvWx'
    have hcomm' : commSub (wTil V₀ V hV L)
        (barSub V₀ V hV (conjSubgroup L x)) = ⊥ :=
      (hS.setting.hyp151.commute x hxM hxn).2
    have hlefix : wTil V₀ V hV L ≤ fixV (barSub V₀ V hV (conjSubgroup L x)) :=
      commSub_eq_bot_iff.1 hcomm'
    have hqfix := hlefix hqvW
    have hqcomm : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈
        commSub ⊤ (barSub V₀ V hV (conjSubgroup L x)) := hqvWx
    have hcardK : Nat.card (barSub V₀ V hV (conjSubgroup L x)) = 3 := by
      rw [c23_card_barSub_conjSubgroup hV hxS L]
      exact hc.1.2
    have hoddK : Odd (Nat.card (barSub V₀ V hV (conjSubgroup L x))) := by
      rw [hcardK]
      norm_num
    have hbot := commV_inf_fixV_eq_bot_of_odd_card (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (barSub V₀ V hV (conjSubgroup L x)) hoddK
    rw [commV_eq_commSub] at hbot
    have hqbot : mkTil V₀ V hV (IntMod.mk hV ⟨v, hvV⟩) ∈
        (⊥ : Subgroup (Vtil V₀ V hV)) := by
      rw [← hbot]
      exact ⟨hqcomm, hqfix⟩
    have hq1 := Subgroup.mem_bot.1 hqbot
    have hxker : IntMod.mk hV ⟨v, hvV⟩ ∈ (mkTil V₀ V hV).ker := MonoidHom.mem_ker.2 hq1
    have hxmod : IntMod.mk hV ⟨v, hvV⟩ ∈ modNull V₀ V hV := by
      rw [← QuotientGroup.ker_mk' (modNull V₀ V hV)]
      exact hxker
    exact (mem_modNull V₀ V hV _).1 hxmod
  · refine le_inf (s15_Two_le_wSub hV hpf.le L) ?_
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV hxS]
    exact s15_Two_le_wSub hV hpf.le (conjSubgroup L x)

theorem s1667_conj_cases (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_3 D V₀ V hV L) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) {m : G} (hm : m ∈ D.M) :
    (conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV L ∧
        conjSubgroup (conjSubgroup (wSub V₀ V hV L) x) m = conjSubgroup (wSub V₀ V hV L) x) ∨
      (conjSubgroup (wSub V₀ V hV L) m = conjSubgroup (wSub V₀ V hV L) x ∧
        conjSubgroup (conjSubgroup (wSub V₀ V hV L) x) m = wSub V₀ V hV L) := by
  have hpf := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hmS : m ∈ stabTil V₀ V := hMs hm
  have hxS : x ∈ stabTil V₀ V := hMs hxM
  have hWm : conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV L ∨
      conjSubgroup (wSub V₀ V hV L) m = conjSubgroup (wSub V₀ V hV L) x := by
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV hmS]
    rcases c23_barSub_conj_cases D hS.setting.hyp151 hV hc.2.2.1 hxM hxn hm with hcase | hcase
    · left
      exact wSub_eq_of_barSub_eq hV hcase
    · right
      rw [wSub_eq_of_barSub_eq hV hcase]
      exact s15_Infra_wSub_conjSubgroup V₀ V L hV hxS
  have hxm : x * m ∈ D.M := D.M.mul_mem hxM hm
  have hWxm : conjSubgroup (conjSubgroup (wSub V₀ V hV L) x) m = wSub V₀ V hV L ∨
      conjSubgroup (conjSubgroup (wSub V₀ V hV L) x) m = conjSubgroup (wSub V₀ V hV L) x := by
    rw [conjSubgroup_conjSubgroup, ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hxm)]
    rcases c23_barSub_conj_cases D hS.setting.hyp151 hV hc.2.2.1 hxM hxn hxm with hcase | hcase
    · left
      exact wSub_eq_of_barSub_eq hV hcase
    · right
      rw [wSub_eq_of_barSub_eq hV hcase]
      exact s15_Infra_wSub_conjSubgroup V₀ V L hV hxS
  have hWne : wSub V₀ V hV L ≠ conjSubgroup (wSub V₀ V hV L) x := by
    intro heq
    have hcard := s1667_card_wSub D hS hc
    have hinf := s1667_inf_conj_eq D hS hc hxM hxn
    have hWV₀ : wSub V₀ V hV L = V₀ := by
      calc wSub V₀ V hV L
          = wSub V₀ V hV L ⊓ conjSubgroup (wSub V₀ V hV L) x :=
            (inf_eq_left.mpr heq.le).symm
        _ = V₀ := hinf
    rw [hWV₀] at hcard
    have hpos : 0 < Nat.card V₀ := by
      haveI : Nonempty ↥V₀ := ⟨1, V₀.one_mem⟩
      exact Nat.card_pos
    omega
  have hinj : Function.Injective (fun Y : Subgroup G => conjSubgroup Y m) := by
    intro A B h
    have h' : conjSubgroup A (m * m⁻¹) = conjSubgroup B (m * m⁻¹) := by
      simpa only [conjSubgroup_conjSubgroup] using
        congrArg (fun Y : Subgroup G => conjSubgroup Y m⁻¹) h
    simpa [conjSubgroup_one] using h'
  rcases hWm with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rcases hWxm with h2 | h2
    · exact absurd (hinj (h1.trans h2.symm)) hWne
    · exact h2
  · right
    refine ⟨h1, ?_⟩
    rcases hWxm with h2 | h2
    · exact h2
    · exact absurd (hinj (h1.trans h2.symm)) hWne

theorem s1667_sup_conj_eq (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_3 D V₀ V hV L) {x : G}
    (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V hV L) :
    wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) x = V := by
  have hpf := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  refine le_antisymm ?_ ?_
  · refine sup_le (preTil_le V₀ V hV _) ?_
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hxM)]
    exact preTil_le V₀ V hV _
  · have hspan : (⨆ X ∈ wConj D.M V₀ V hV L, X) = V :=
      iSup_wConj_eq D h1217 hS.setting.hyp151 hV hS.ne_bot
    calc V = ⨆ X ∈ wConj D.M V₀ V hV L, X := hspan.symm
      _ ≤ wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) x := by
          refine iSup_le fun X => iSup_le fun hX => ?_
          rw [wConj] at hX
          obtain ⟨m, hm, rfl⟩ := hX
          rcases s1667_conj_cases D hS hc hxM hxn hm with ⟨h1, -⟩ | ⟨h1, -⟩
          · rw [h1]
            exact le_sup_left
          · rw [h1]
            exact le_sup_right

theorem s1667_card_eq (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_3 D V₀ V hV L) :
    Nat.card V = 16 * Nat.card V₀ := by
  obtain ⟨x, hxM, hxn⟩ := c23_exists_mem_not_nBar D hS.setting.hyp151 hV hc.2.2.1
  have hpf := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hWxV : conjSubgroup (wSub V₀ V hV L) x ≤ V := by
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hxM)]
    exact preTil_le V₀ V hV _
  have hnorm : wSub V₀ V hV L ≤
      normalizer (conjSubgroup (wSub V₀ V hV L) x : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha b hb
    haveI : IsMulCommutative ↥V := hV.1
    have hcomm : a * b = b * a := setLike_mul_comm (hWV ha) (hWxV hb)
    have hab : a * b * a⁻¹ = b := by
      rw [hcomm]
      group
    rw [hab]
    exact hb
  have hmain := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf'
    (H := wSub V₀ V hV L) (N := conjSubgroup (wSub V₀ V hV L) x) hnorm
  rw [s1667_sup_conj_eq D h1217 hS hc hxM hxn,
      s1667_inf_conj_eq D hS hc hxM hxn,
      E3.card_conjSubgroup (wSub V₀ V hV L) x,
      s1667_card_wSub D hS hc] at hmain
  have hpos : 0 < Nat.card V₀ := by
    haveI : Nonempty ↥V₀ := ⟨1, V₀.one_mem⟩
    exact Nat.card_pos
  refine Nat.mul_right_cancel hpos ?_
  rw [hmain]
  ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
