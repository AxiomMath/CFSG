module

public import CFSG.RankThree.PartTwo.Sec15.Wales154KFacts
import CFSG.CGT.Timmesfeld75.A6Basic
import CFSG.LocalAnalysis.GLTheoremA.S8.I1425ONNative
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_RankAux
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.CentralizerM
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.ONOddCore.LocalAutDataCheckInputs
public import CFSG.Sporadic.ONOddCore.NonextPayload
public import CFSG.Sporadic.Schreier.ONOuterDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open Subgroup CFSG.Blueprint

private theorem le_centralizer_of_pow_five {Y : Type*} [Group Y] [Finite Y] {E : Subgroup Y}
    (hE : IsPGroup 2 E) (hE8 : Nat.card E ≤ 8) {y : Y} (hy : y ^ 5 = 1)
    (hyE : y ∈ normalizer (E : Set Y)) : E ≤ centralizer ({y} : Set Y) := by
  have hmod := CFSG.LocalAnalysis.RankThreeTheoremC.zjr_card_modEq (by norm_num) hy hyE
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hE)
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card.mp (hE.to_le (inf_le_left :
    E ⊓ centralizer ({y} : Set Y) ≤ E)))
  have hdvd : Nat.card (E ⊓ centralizer ({y} : Set Y) : Subgroup Y) ∣ Nat.card E :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [ha] at hE8 hdvd hmod
  rw [hb] at hdvd hmod
  have ha3 : a ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hba : b ≤ a := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hab : a = b := by
    interval_cases a <;> interval_cases b <;> simp_all [Nat.ModEq]
  have heq : Nat.card (E ⊓ centralizer ({y} : Set Y) : Subgroup Y) = Nat.card E := by
    rw [ha, hb, hab]
  have hle := Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ centralizer ({y} : Set Y) ≤ E)
    heq.ge
  rw [← hle]
  exact inf_le_right

private theorem card_eq_four_of_fixedPointFree {Y : Type*} [Group Y] [Finite Y] {E : Subgroup Y}
    (hE : IsPGroup 2 E) (hE1 : E ≠ ⊥) (hE8 : Nat.card E ≤ 8) {g : Y} (hg : g ^ 3 = 1)
    (hgE : g ∈ normalizer (E : Set Y)) (hfix : ∀ t ∈ E, g * t = t * g → t = 1) :
    Nat.card E = 4 := by
  have hmod := CFSG.LocalAnalysis.RankThreeTheoremC.zjr_card_modEq (by norm_num) hg hgE
  have hbot : E ⊓ centralizer ({g} : Set Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨htE, htC⟩
    exact (mem_bot).mpr (hfix t htE (mem_centralizer_singleton_iff.mp htC).symm)
  rw [hbot, Subgroup.card_bot] at hmod
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.mp hE)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hE1 (Subgroup.eq_bot_of_card_eq E (by simpa using ha))
  rw [ha] at hE8 hmod ⊢
  have ha3 : a ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases a <;> simp_all [Nat.ModEq]

private theorem mem_omegaOneCenter_iff {Y : Type*} [Group Y] {P : Subgroup Y} {x : Y} :
    x ∈ CFSG.omegaOneCenter P ↔ x ∈ P ∧ (∀ z ∈ P, x * z = z * x) ∧ x ^ 2 = 1 := by
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hx2⟩
    exact ⟨c.2, fun z hz => congrArg Subtype.val (mem_center_iff.mp hc ⟨z, hz⟩).symm, hx2⟩
  · rintro ⟨hxP, hxc, hx2⟩
    exact ⟨⟨⟨x, hxP⟩, mem_center_iff.mpr fun z => Subtype.ext (hxc z z.2).symm, rfl⟩, hx2⟩

private theorem omegaOneCenter_le' {Y : Type*} [Group Y] (P : Subgroup Y) :
    CFSG.omegaOneCenter P ≤ P :=
  fun _ hx => (mem_omegaOneCenter_iff.mp hx).1

private theorem isElemAbelian_omegaOneCenter {Y : Type*} [Group Y] (P : Subgroup Y) :
    CFSG.Assembly.IsElemAbelian 2 (CFSG.omegaOneCenter P) :=
  ⟨⟨⟨fun a b => Subtype.ext ((mem_omegaOneCenter_iff.mp a.2).2.1 b
    (mem_omegaOneCenter_iff.mp b.2).1)⟩⟩, fun _ hx => (mem_omegaOneCenter_iff.mp hx).2.2⟩

private theorem mem_normalizer_omegaOneCenter {Y : Type*} [Group Y] {P : Subgroup Y} {g : Y}
    (hg : g ∈ normalizer (P : Set Y)) : g ∈ normalizer (CFSG.omegaOneCenter P : Set Y) := by
  have hconj : ∀ h ∈ normalizer (P : Set Y), ∀ x ∈ CFSG.omegaOneCenter P,
      h * x * h⁻¹ ∈ CFSG.omegaOneCenter P := by
    intro h hh x hx
    obtain ⟨hxP, hxc, hx2⟩ := mem_omegaOneCenter_iff.mp hx
    refine mem_omegaOneCenter_iff.mpr ⟨(mem_normalizer_iff.mp hh x).mp hxP, fun z hz => ?_, ?_⟩
    · have hz' : h⁻¹ * z * h ∈ P := by
        have := (mem_normalizer_iff.mp (inv_mem hh) z).mp hz
        simpa using this
      have h1 := hxc _ hz'
      calc h * x * h⁻¹ * z = h * (x * (h⁻¹ * z * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * z * h) * x) * h⁻¹ := by rw [h1]
        _ = z * (h * x * h⁻¹) := by group
    · rw [conj_pow, hx2, mul_one, mul_inv_cancel]
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hconj g hg x hx, fun hx => ?_⟩
  have := hconj g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

private theorem omegaOneCenter_ne_bot' {Y : Type*} [Group Y] [Finite Y] {P : Subgroup Y}
    (hP : IsPGroup 2 P) (hne : P ≠ ⊥) : CFSG.omegaOneCenter P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center P) := by
    rcases (hP.to_subgroup (Subgroup.center P)).card_eq_or_dvd with hone | hdiv
    · have : Subsingleton (Subgroup.center P) := (Nat.card_eq_one_iff_unique.mp hone).1
      exact (not_subsingleton (Subgroup.center P) this).elim
    · exact hdiv
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2 hdvd
  have hc' : orderOf ((c : P) : Y) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hc
  intro hbot
  have hmem : ((c : P) : Y) ∈ CFSG.omegaOneCenter P := by
    refine mem_omegaOneCenter_iff.mpr ⟨(c : P).2, fun z hz => ?_, ?_⟩
    · have h := Subgroup.mem_center_iff.mp c.2 ⟨z, hz⟩
      exact (congrArg Subtype.val h).symm
    · rw [← hc']
      exact pow_orderOf_eq_one _
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hc'
  exact absurd hc' (by norm_num)

section Three


private theorem false_of_commute_of_mem_centralizer {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* NativeSporadic.Carrier .ONan) {d t y : Y} (hd : orderOf d = 3)
    (htd : t ∈ centralizer ({d} : Set Y)) (hyd : y ∈ centralizer ({d} : Set Y))
    (ht : orderOf t = 2) (hy : orderOf y = 5) (hty : t * y = y * t) : False := by
  set C := centralizer ({d} : Set Y)
  obtain ⟨E, hn, ⟨eE⟩, hidx⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S8.L84.alt6_normal_centralizer_ON e hd
  obtain ⟨hZ, hZE, hdec⟩ := CFSG.LocalAnalysis.GLTheoremA.S8.L84.alt6_split eE hidx
  have hmemE : ∀ c : C, ∀ n : ℕ, c ^ n = 1 → Nat.Coprime n 3 → c ∈ E := by
    intro c n hc hn
    obtain ⟨z, hz, x, hx, rfl⟩ := hdec c
    have hzx : Commute z x := (Subgroup.mem_center_iff.mp hz x).symm
    have h1 : z ^ n * x ^ n = 1 := by rw [← hzx.mul_pow]; exact hc
    have hzn : z ^ n ∈ Subgroup.center C ⊓ E := by
      refine ⟨pow_mem hz n, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1]
      exact E.inv_mem (E.pow_mem hx n)
    rw [hZE, mem_bot] at hzn
    have hz9 : z ^ 9 = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center C) (x := ⟨z, hz⟩)
      rw [hZ] at h
      exact congrArg Subtype.val h
    have hgcd : z ^ Nat.gcd n 9 = 1 := pow_gcd_eq_one.mpr ⟨hzn, hz9⟩
    have hcop : Nat.Coprime n 9 := by
      have := Nat.Coprime.pow_right 2 hn
      norm_num at this
      exact this
    rw [hcop.gcd_eq_one, pow_one] at hgcd
    rw [hgcd, one_mul]
    exact hx
  set t' : C := ⟨t, htd⟩
  set y' : C := ⟨y, hyd⟩
  have ht2 : t' ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← ht]; exact pow_orderOf_eq_one t)
  have hy5 : y' ^ 5 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy]; exact pow_orderOf_eq_one y)
  have htE := hmemE t' 2 ht2 (by norm_num)
  have hyE := hmemE y' 5 hy5 (by norm_num)
  set a : E := ⟨t', htE⟩
  set b : E := ⟨y', hyE⟩
  have hoa : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe a, ← Subgroup.orderOf_coe t', ← ht]
  have hob : orderOf b = 5 := by
    rw [← Subgroup.orderOf_coe b, ← Subgroup.orderOf_coe y', ← hy]
  have hab : Commute a b := Subtype.ext (Subtype.ext hty)
  have h10 : orderOf (a * b) = 10 := by
    rw [hab.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hoa, hob]; norm_num), hoa, hob]
  exact CFSG.CGT.Timmesfeld75.A6_no_order_ten eE (a * b) h10

end Three

section Local

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter
open CFSG.ComponentClassification (PSL3Four.F4 PSL3Four.frob)


private theorem congr_thetaX_conj (x : onX) :
    MulAut.congr thetaX.symm (MulAut.conj x) = MulAut.conj (thetaX.symm x) := by
  refine MulEquiv.ext fun p => ?_
  simp [MulAut.congr_apply]

private theorem congr_thetaX_sigmaX :
    MulAut.congr thetaX.symm (sigmaX 0 1 1) =
      fieldAut 3 PSL3Four.F4 PSL3Four.frob * dualAut 3 PSL3Four.F4 := by
  refine MulEquiv.ext fun p => ?_
  have h := thetaX_symm_sigmaX 0 1 1 (thetaX p)
  simp only [MulEquiv.symm_apply_apply] at h
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm, h, gammaAut,
    pow_zero, map_one, one_mul, pow_one]

private theorem resX_conj_b5 : resX (MulAut.conj (piR (bElem 5))) = sigmaX 0 1 1 := by
  have hk : (3 : ℕ) < 12 := by norm_num
  have hi : 1 < (recK 3).lifts.length := by
    rw [recK_lifts_length hk]
    decide
  have he := getD_mem hi default
  have h5 : flatLifts.getD 5 default = (recK 3).lifts.getD 1 default := flat_rec3 hi
  have hconj : MulAut.conj (bElem 5) = liftAut hk he := by
    refine MulEquiv.ext fun m => ?_
    rw [MulAut.conj_apply, ← betaFun_inner (by decide : 5 ∈ innerIdx) m,
      congrFun (liftAut_eq_liftFun hk he) m, betaFun, h5]
  have hdesc : MulAut.conj (piR (bElem 5)) = tauAut 3 := by
    rw [← descendAut_conj, hconj]
    exact liftAut_mem hk he
  have ht := recK_triple hk
  simp only [tripleList, List.getD_cons_succ, List.getD_cons_zero, Prod.mk.injEq] at ht
  rw [hdesc, resX_tauAut hk, ht.1, ht.2.1, ht.2.2]

private theorem false_of_outer {r : RM} (hr : (r : Equiv.Perm (Fin 120)) ∉ onX)
    (hr2 : r * r = 1) {x : onX} (hx : orderOf x = 5)
    (hrx : r * ⟨x, onX_le_RM x.2⟩ = ⟨x, onX_le_RM x.2⟩ * r) : False := by
  have hk := CFSG.ComponentClassification.PSL3Four.natCard_F4
  have hσ := CFSG.ComponentClassification.PSL3Four.frob_apply
  have hXR : ∀ u : RM, u ∈ XR ↔ (u : Equiv.Perm (Fin 120)) ∈ onX := fun u => mem_subgroupOf
  set b : RM := piR (bElem 5) with hbdef
  have hb : (b : Equiv.Perm (Fin 120)) ∉ onX := by
    intro hb
    have h1 := resX_conj hb
    rw [resX_conj_b5] at h1
    have h2 := congrArg (MulAut.congr thetaX.symm) h1
    rw [congr_thetaX_sigmaX, congr_thetaX_conj] at h2
    have h3 : conjAut 3 PSL3Four.F4 1 * fieldAut 3 PSL3Four.F4 PSL3Four.frob *
        dualAut 3 PSL3Four.F4 ^ 1 ∈
          (MulAut.conj : projectiveSL 3 PSL3Four.F4 →* _).range := by
      rw [map_one, one_mul, pow_one, h2]
      exact ⟨_, rfl⟩
    have := (CFSG.RankThree.PartTwo.KFacts.L34.eq_of_conjAut_mul_mem_range hk hσ 1
      PSL3Four.frob le_rfl h3).2.1
    exact absurd this (by norm_num)
  have hx0 : r * b⁻¹ ∈ XR :=
    (mul_mem_iff_of_index_two XR_index).mpr (iff_of_false (fun h => hr ((hXR r).mp h))
      (fun h => hb ((hXR b).mp (inv_mem_iff.mp h))))
  set x0 : onX := ⟨((r * b⁻¹ : RM) : Equiv.Perm (Fin 120)), (hXR _).mp hx0⟩ with hx0def
  have hres : resX (MulAut.conj r) = MulAut.conj x0 * sigmaX 0 1 1 := by
    calc resX (MulAut.conj r) = resX (MulAut.conj ((r * b⁻¹) * b)) := by
          rw [inv_mul_cancel_right]
      _ = resX (MulAut.conj (r * b⁻¹)) * resX (MulAut.conj b) := by rw [map_mul, map_mul]
      _ = MulAut.conj x0 * sigmaX 0 1 1 := by rw [resX_conj ((hXR _).mp hx0), resX_conj_b5]
  set α := MulAut.congr thetaX.symm (resX (MulAut.conj r)) with hαdef
  obtain ⟨B, hB⟩ := conj_proj_eq (thetaX.symm x0)
  have hα : α = nf PSL3Four.frob B 1 1 := by
    rw [hαdef, hres, map_mul, congr_thetaX_conj, congr_thetaX_sigmaX, hB, nf, val_one_two,
      pow_one, pow_one, mul_assoc]
  have hα2 : α * α = 1 := by
    rw [hαdef, ← map_mul, ← map_mul, ← map_mul, hr2, map_one, map_one, map_one]
  have hfix : α (thetaX.symm x) = thetaX.symm x := by
    rw [hαdef, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
    congr 1
    apply Subtype.ext
    rw [resX_apply, MulAut.conj_apply, hrx, mul_inv_cancel_right]
  have hp5 : orderOf (thetaX.symm x) = 5 := by rw [MulEquiv.orderOf_eq, hx]
  have hff := fieldAut_sigma_mul_self hσ hk
  rcases CFSG.RankThree.PartTwo.KFacts.L34.involution_cases_card hk hσ hα2 with
    hin | ⟨⟨H, hH⟩, -⟩ | ⟨⟨H, hH⟩, -⟩ | ⟨-, h72⟩
  · have h3 : conjAut 3 PSL3Four.F4 B * fieldAut 3 PSL3Four.F4 PSL3Four.frob *
        dualAut 3 PSL3Four.F4 ^ 1 ∈
          (MulAut.conj : projectiveSL 3 PSL3Four.F4 →* _).range := by
      have : conjAut 3 PSL3Four.F4 B * fieldAut 3 PSL3Four.F4 PSL3Four.frob *
          dualAut 3 PSL3Four.F4 ^ 1 = α := by
        rw [hα, nf, val_one_two, pow_one (fieldAut 3 PSL3Four.F4 PSL3Four.frob)]
      rw [this]
      exact hin
    have := (CFSG.RankThree.PartTwo.KFacts.L34.eq_of_conjAut_mul_mem_range hk hσ B
      PSL3Four.frob le_rfl h3).2.1
    exact absurd this (by norm_num)
  · have h1 : nf PSL3Four.frob B 1 1 = nf PSL3Four.frob H 0 0 * nf PSL3Four.frob 1 1 0 *
        nf PSL3Four.frob H⁻¹ 0 0 := by
      rw [← hα, hH, nf_zero_zero, nf_one_zero, nf_zero_zero, map_inv]
    rw [nf_mul _ hff, nf_mul _ hff] at h1
    exact absurd (nf_inj hσ hk h1).2.2 (by decide)
  · have h1 : nf PSL3Four.frob B 1 1 = nf PSL3Four.frob H 0 0 * nf PSL3Four.frob 1 0 1 *
        nf PSL3Four.frob H⁻¹ 0 0 := by
      rw [← hα, hH, nf_zero_zero, nf_zero_one, nf_zero_zero, map_inv]
    rw [nf_mul _ hff, nf_mul _ hff] at h1
    exact absurd (nf_inj hσ hk h1).2.1 (by decide)
  · have hmem : thetaX.symm x ∈ GL3TwoFixedModel.autFixed α :=
      GL3TwoFixedModel.mem_autFixed.mpr hfix
    have hdvd := orderOf_dvd_natCard (⟨_, hmem⟩ : GL3TwoFixedModel.autFixed α)
    rw [Subgroup.orderOf_mk, hp5, h72] at hdvd
    norm_num at hdvd

private theorem false_of_inner {r : RM} (hr : (r : Equiv.Perm (Fin 120)) ∈ onX) (hr1 : r ≠ 1)
    (hr2 : r * r = 1) {x : onX} (hx : orderOf x = 5)
    (hrx : r * ⟨x, onX_le_RM x.2⟩ = ⟨x, onX_le_RM x.2⟩ * r) : False := by
  set a : CFSG.ComponentClassification.PSL3Four.S := xEquivS ⟨r, hr⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply hr1
    have : (⟨r, hr⟩ : onX) = 1 := xEquivS.injective (by rw [map_one]; exact h)
    exact Subtype.ext (show (r : Equiv.Perm (Fin 120)) = 1 from congrArg Subtype.val this)
  have ha2 : a * a = 1 := by
    rw [← map_mul]
    have : (⟨r, hr⟩ : onX) * ⟨r, hr⟩ = 1 :=
      Subtype.ext (show (r : Equiv.Perm (Fin 120)) * r = 1 by
        rw [← Subgroup.coe_mul, hr2, Subgroup.coe_one])
    rw [this, map_one]
  have hoa : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hcomm : xEquivS x ∈ centralizer ({a} : Set CFSG.ComponentClassification.PSL3Four.S) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (congrArg Subtype.val hrx).symm
  have hdvd := orderOf_dvd_natCard (⟨_, hcomm⟩ :
    centralizer ({a} : Set CFSG.ComponentClassification.PSL3Four.S))
  rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hx,
    CFSG.ComponentClassification.PSL3Four.card_centralizer_involution_S a hoa] at hdvd
  norm_num at hdvd

private theorem false_of_commute_RM {r y : RM} (hr1 : r ≠ 1) (hr2 : r * r = 1) (hy5 : y ^ 5 = 1)
    (hy1 : y ≠ 1) (hry : r * y = y * r) : False := by
  have hyX : (y : Equiv.Perm (Fin 120)) ∈ onX := by
    have h2 : y * y ∈ XR := mul_self_mem_of_index_two XR_index y
    have h6 : y = (y * y) ^ 3 := by
      rw [← sq, ← pow_mul, show 2 * 3 = 5 + 1 by norm_num, pow_succ, hy5, one_mul]
    rw [h6]
    exact mem_subgroupOf.mp (pow_mem h2 3)
  set x : onX := ⟨y, hyX⟩
  have hx1 : x ≠ 1 := fun h =>
    hy1 (Subtype.ext (show (y : Equiv.Perm (Fin 120)) = 1 from congrArg Subtype.val h))
  have hx5 : orderOf x = 5 :=
    orderOf_eq_prime (Subtype.ext (show (y : Equiv.Perm (Fin 120)) ^ 5 = 1 by
      rw [← Subgroup.coe_pow, hy5, Subgroup.coe_one])) hx1
  have hxy : (⟨x, onX_le_RM x.2⟩ : RM) = y := rfl
  by_cases hr : (r : Equiv.Perm (Fin 120)) ∈ onX
  · exact false_of_inner hr hr1 hr2 hx5 (by rw [hxy]; exact hry)
  · exact false_of_outer hr hr2 hx5 (by rw [hxy]; exact hry)

end Local

section Klein

open CFSG.ONSchreier CFSG.Sporadic.ONOddCore


private theorem eq_one_or_eq_sq_of_mem_onQ {w : Equiv.Perm (Fin N)} (hw : w ∈ onQ)
    (hw2 : w ^ 2 = 1) : w = 1 ∨ w = onq ^ 2 := by
  rw [onQ] at hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  have h4 : orderOf onq = 4 := orderOf_onq
  have hdvd : ((orderOf onq : ℕ) : ℤ) ∣ k * 2 := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul]
    exact_mod_cast hw2
  rw [h4] at hdvd
  rw [← zpow_mod_orderOf, h4]
  have : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 2 := by omega
  rcases this with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h]
    rfl

private theorem false_of_klein {Γ : Type} [Group Γ] [Finite Γ] (e : Γ ≃* NativeSporadic.ON)
    {y : Γ} (hy : orderOf y = 5) {E : Subgroup Γ} (hE : CFSG.Assembly.IsElemAbelian 2 E)
    (hE4 : Nat.card E = 4) (hEy : E ≤ centralizer ({y} : Set Γ)) : False := by
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨t1, ht1E, ht1⟩ : ∃ t ∈ E, t ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h x hx)
    rw [hbot, card_bot] at hE4
    norm_num at hE4
  have ht1o : orderOf t1 = 2 := orderOf_eq_prime (hE.2 t1 ht1E) ht1
  obtain ⟨s1, hs1E, hs1⟩ : ∃ s ∈ E, s ∉ zpowers t1 := by
    by_contra h
    push Not at h
    have hle := card_le_of_le (show E ≤ zpowers t1 from h)
    rw [Nat.card_zpowers, hE4, ht1o] at hle
    norm_num at hle
  have hs1_1 : s1 ≠ 1 := fun h => hs1 (h ▸ one_mem _)
  have hs2E : t1 * s1 ∈ E := mul_mem ht1E hs1E
  have hs2_1 : t1 * s1 ≠ 1 := fun h => hs1 (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_mem (mem_zpowers t1))
  have hs12 : s1 ≠ t1 * s1 := fun h => ht1 (by
    have := congrArg (· * s1⁻¹) h
    simpa using this.symm)
  set φ := CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.centralizerEquivM e ht1o
  set πC : centralizer ({t1} : Set Γ) →* RM := piR.comp φ.toMonoidHom with hπC
  have hmemC : ∀ a ∈ E, a ∈ centralizer ({t1} : Set Γ) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (hEc a ha t1 ht1E)
  have hyC : y ∈ centralizer ({t1} : Set Γ) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hEy ht1E)).symm
  have hq : ∀ s ∈ E, s ≠ 1 → ∀ hs : s ∈ centralizer ({t1} : Set Γ), πC ⟨s, hs⟩ = 1 →
      ((φ ⟨s, hs⟩ : onM) : Equiv.Perm (Fin N)) = onq ^ 2 := by
    intro s hsE hs1 hs hπ
    have hk : φ ⟨s, hs⟩ ∈ piR.ker := hπ
    rw [ker_piR, mem_subgroupOf] at hk
    have hsq : ((φ ⟨s, hs⟩ : onM) : Equiv.Perm (Fin N)) ^ 2 = 1 := by
      have h2 : (⟨s, hs⟩ : centralizer ({t1} : Set Γ)) ^ 2 = 1 := Subtype.ext (hE.2 s hsE)
      rw [← Subgroup.coe_pow, ← map_pow, h2, map_one, Subgroup.coe_one]
    rcases eq_one_or_eq_sq_of_mem_onQ hk hsq with h0 | h0
    · exfalso
      apply hs1
      have h1 : φ ⟨s, hs⟩ = 1 := Subtype.ext h0
      have : (⟨s, hs⟩ : centralizer ({t1} : Set Γ)) = 1 := φ.injective (by rw [h1, map_one])
      exact congrArg Subtype.val this
    · exact h0
  obtain ⟨s, hsE, hsC, hπs⟩ : ∃ s ∈ E, ∃ hs : s ∈ centralizer ({t1} : Set Γ),
      πC ⟨s, hs⟩ ≠ 1 := by
    by_contra h
    push Not at h
    have h1 := hq s1 hs1E hs1_1 (hmemC s1 hs1E) (h s1 hs1E (hmemC s1 hs1E))
    have h2 := hq _ hs2E hs2_1 (hmemC _ hs2E) (h _ hs2E (hmemC _ hs2E))
    have h12 : φ ⟨s1, hmemC s1 hs1E⟩ = φ ⟨t1 * s1, hmemC _ hs2E⟩ := Subtype.ext (h1.trans h2.symm)
    exact hs12 (congrArg Subtype.val (φ.injective h12))
  have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hr2 : πC ⟨s, hsC⟩ * πC ⟨s, hsC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨s, hsC⟩ : centralizer ({t1} : Set Γ)) * ⟨s, hsC⟩ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact hE.2 s hsE)
    rw [this, map_one]
  have hyc5 : (⟨y, hyC⟩ : centralizer ({t1} : Set Γ)) ^ 5 = 1 := Subtype.ext hy5
  have hpy5 : πC ⟨y, hyC⟩ ^ 5 = 1 := by rw [← map_pow, hyc5, map_one]
  have hpy1 : πC ⟨y, hyC⟩ ≠ 1 := by
    intro h
    have hk : φ ⟨y, hyC⟩ ∈ piR.ker := h
    rw [ker_piR] at hk
    have h4 : (⟨φ ⟨y, hyC⟩, hk⟩ : onQ.subgroupOf onM) ^ 4 = 1 := by
      rw [← card_onQ_subgroupOf_M]
      exact pow_card_eq_one'
    have h4' : φ ⟨y, hyC⟩ ^ 4 = 1 := congrArg Subtype.val h4
    have h5' : φ ⟨y, hyC⟩ ^ 5 = 1 := by rw [← map_pow, hyc5, map_one]
    have h1 : φ ⟨y, hyC⟩ = 1 := by
      have h := pow_gcd_eq_one.mpr ⟨h4', h5'⟩
      rwa [show Nat.gcd 4 5 = 1 by norm_num, pow_one] at h
    have : (⟨y, hyC⟩ : centralizer ({t1} : Set Γ)) = 1 := φ.injective (by rw [h1, map_one])
    have hy1 : y = 1 := congrArg Subtype.val this
    rw [hy1, orderOf_one] at hy
    norm_num at hy
  have hry : πC ⟨s, hsC⟩ * πC ⟨y, hyC⟩ = πC ⟨y, hyC⟩ * πC ⟨s, hsC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hEy hsE))
  exact false_of_commute_RM hπs hr2 hpy5 hpy1 hry

end Klein

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator in
theorem ks154ONCore :
    KS154ONCore := by
  intro Γ _ ⟨e⟩ V g _ h5 hg3 hVg P hP hVP hgP
  have : Finite Γ := by
    have : Finite NativeSporadic.ON :=
      Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
    exact Finite.of_equiv _ e.symm.toEquiv
  have e' : Γ ≃* NativeSporadic.Carrier .ONan := e.trans (MulEquiv.refl _)
  by_contra hP1
  obtain ⟨y, hyV, hy5⟩ : ∃ y ∈ V, orderOf y = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := V) 5 h5
    exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  have hyg : y ∈ centralizer ({g} : Set Γ) := hVg hyV
  set E := CFSG.omegaOneCenter P with hEdef
  have hE1 : E ≠ ⊥ := omegaOneCenter_ne_bot' hP hP1
  have hE2 : IsPGroup 2 E := hP.to_le (omegaOneCenter_le' P)
  have hEab : CFSG.Assembly.IsElemAbelian 2 E := isElemAbelian_omegaOneCenter P
  have hE8 : Nat.card E ≤ 8 :=
    ONTwoRank.card_le_eight_of_mulEquiv_Pv (e.trans CFSG.ONSchreier.onEquivPv) E hEab
  have hyE : y ∈ normalizer (E : Set Γ) := mem_normalizer_omegaOneCenter (hVP hyV)
  have hgE : g ∈ normalizer (E : Set Γ) := mem_normalizer_omegaOneCenter hgP
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hg3' : g ^ 3 = 1 := by rw [← hg3]; exact pow_orderOf_eq_one g
  have hEy : E ≤ centralizer ({y} : Set Γ) := le_centralizer_of_pow_five hE2 hE8 hy5' hyE
  have hfix : ∀ t ∈ E, g * t = t * g → t = 1 := by
    intro t htE hgt
    by_contra ht1
    have ht2 : orderOf t = 2 := orderOf_eq_prime (mem_omegaOneCenter_iff.mp htE).2.2 ht1
    have htg : t ∈ centralizer ({g} : Set Γ) := mem_centralizer_singleton_iff.mpr hgt.symm
    have hty : t * y = y * t := mem_centralizer_singleton_iff.mp (hEy htE)
    exact false_of_commute_of_mem_centralizer e' hg3 htg hyg ht2 hy5 hty
  have hE4 : Nat.card E = 4 := card_eq_four_of_fixedPointFree hE2 hE1 hE8 hg3' hgE hfix
  exact false_of_klein e hy5 hEab hE4 hEy

end CFSG.RankThree.PartTwo.Sec15.Wales154
