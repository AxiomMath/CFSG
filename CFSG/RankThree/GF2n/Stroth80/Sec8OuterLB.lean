module

public import CFSG.RankThree.GF2n.Stroth80.Sec8OuterElt
public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec8CommNorm
public import CFSG.RankThree.GF2n.Stroth80.Sec8StepsNorm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec83NatSection
public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_outer_exists_l_Vt_eq (hc : Ctx M Q Z B) {x l : G} (hxM : x ∈ M)
    (hq : ⁅l, x⁆ ∈ Q) :
    Vt M (LB M Q B) B Z (l * x * l⁻¹) = Vt M (LB M Q B) B Z x := by
  have hy : x⁻¹ * (l * x * l⁻¹) ∈ Q := by
    have e : x⁻¹ * (l * x * l⁻¹) = x⁻¹ * ⁅l, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [e]
    have hN := (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (M.inv_mem hxM)) ⁅l, x⁆).mp hq
    rwa [inv_inv] at hN
  have e' : l * x * l⁻¹ = x * (x⁻¹ * (l * x * l⁻¹)) := (mul_inv_cancel_left _ _).symm
  rw [e', Vt_mul_of_mem_Q hc hy]

theorem sec8_outer_exists_l (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t r g : G}
    (h : Sec8Outer hc n t r g)
    (hinter : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z) :
    ∃ l ∈ LB M Q B, ⁅l, g * t * g⁻¹⁆ ∉ Q := by
  by_contra hne
  push_neg at hne
  obtain ⟨m, hm2, hsp⟩ := h.hs.sp
  have htL : t ∈ LB M Q B := h.hs.toSec5.mem
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hgM : g ∈ M := h.hg
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM (hLM htL)) (M.inv_mem hgM)
  have hZg : conjSubgroup g Z = Z := hc.conj_Z_eq hgM
  have hPeq : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z (g * t * g⁻¹) :=
    conjSubgroup_Vt_eq hgM hZg t
  have hPQ : conjSubgroup g (Vt M (LB M Q B) B Z t) ≤ Q := by
    rw [hPeq]
    exact hc.Vt_le_Q _
  have hZP : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    have h1 : conjSubgroup g Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      Subgroup.map_mono sec39_Z_le_Vt
    rwa [hZg] at h1
  have hnormL : ∀ l ∈ LB M Q B,
      conjSubgroup l (conjSubgroup g (Vt M (LB M Q B) B Z t)) =
        conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro l hl
    have hlM : l ∈ M := hLM hl
    rw [hPeq, conjSubgroup_Vt_eq hlM (hc.conj_Z_eq hlM),
      sec8_outer_exists_l_Vt_eq hc hxM (hne l hl)]
  have hsec : SecHyp (LB M Q B) (conjSubgroup g (Vt M (LB M Q B) B Z t)) Z :=
    ⟨hZP, fun x hx y hy => hc.hyp.toHyp79.comm_mem_V (hPQ hx) (hPQ hy),
      fun x hx => hc.hyp.toHyp79.sq_mem_V (hPQ hx),
      fun r hr x hx => by
        have h1 : r * x * r⁻¹ ∈ conjSubgroup r (conjSubgroup g (Vt M (LB M Q B) B Z t)) := by
          rw [mem_conjSubgroup]
          have e : r⁻¹ * (r * x * r⁻¹) * r = x := by group
          rw [e]
          exact hx
        rwa [hnormL r hr] at h1,
      fun r hr x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hLM hr)) x).mp hx⟩
  obtain ⟨Mo, iMo, iAct, κ, hκ⟩ := exists_sectionModule hsec
  haveI : Finite Mo := hκ.finite
  have hcardP : Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ (2 * m + 1) :=
    (card_conjSubgroup g (Vt M (LB M Q B) B Z t)).trans hsp.card_V
  have hcardS : Nat.card ↥(conjSubgroup g (Vt M (LB M Q B) B Z t)) = Nat.card Z * Nat.card Mo :=
    natCard_eq_of_isSecMod hZP hκ
  have hZpos : 0 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hMo : Nat.card Mo = Nat.card Z ^ (2 * m) := by
    have h1 : Nat.card Z * Nat.card Mo = Nat.card Z * Nat.card Z ^ (2 * m) := by
      rw [← hcardS, hcardP]
      ring
    exact Nat.eq_of_mul_eq_mul_left hZpos h1
  obtain ⟨n', -, hZn, -⟩ := hc.hyp.cp
  have hn0 : n' ≠ 0 := by
    rintro rfl
    have h4 := hc.hyp.q4
    rw [hZn, pow_zero] at h4
    omega
  have h2Z : 2 ∣ Nat.card Z := by
    rw [hZn]
    exact dvd_pow_self 2 hn0
  have h2M : 2 ∣ Nat.card Mo := by
    rw [hMo]
    exact dvd_pow h2Z (by omega)
  have hLB2 : IsPGroup 2 ↥(LB M Q B) :=
    hc.isPGroup_LB h34 h.hs.toSec5.width h.hs.toSec5.n_gt h.hs.toSec5.noA2 h.hs.toSec5.gen
  have h0 : (0 : Mo) ∈ MulAction.fixedPoints ↥(LB M Q B) Mo := by
    rw [MulAction.mem_fixedPoints]
    intro l
    exact smul_zero l
  obtain ⟨b, hbfix, hb0⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point hLB2 Mo h2M h0
  have hbfix' : ∀ l : ↥(LB M Q B), l • b = b := MulAction.mem_fixedPoints.mp hbfix
  have hbne : b ≠ 0 := fun hb => hb0 hb.symm
  obtain ⟨v, hv⟩ := hκ.surj (Multiplicative.ofAdd b)
  have hvb : Multiplicative.toAdd (κ v) = b := by
    rw [hv, toAdd_ofAdd]
  have hvZ : (v : G) ∉ Z := by
    intro hvZ
    apply hbne
    have h1 : κ v = 1 := (hκ.ker v).mpr hvZ
    rw [hv] at h1
    exact ofAdd_eq_one.mp h1
  have hlv : ∀ l ∈ LB M Q B, ⁅l, (v : G)⁆ ∈ Z := by
    intro l hl
    have hlP : l * (v : G) * l⁻¹ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      hsec.normP l hl v v.2
    have hact := hκ.act ⟨l, hl⟩ v ⟨l * (v : G) * l⁻¹, hlP⟩ rfl
    rw [hvb, hbfix' ⟨l, hl⟩] at hact
    have heq : κ v = κ ⟨l * (v : G) * l⁻¹, hlP⟩ := by
      rw [hv, hact]
    have hmem := (hκ.eq_iff v ⟨l * (v : G) * l⁻¹, hlP⟩).mp heq
    have e : ⁅l, (v : G)⁆ = ((v : G) * (l * (v : G) * l⁻¹)⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Z.inv_mem hmem
  have hvQ : (v : G) ∈ Q := hPQ v.2
  have hmemC : (v : G) ∈ CQt Q Z (LB M Q B) :=
    show (v : G) ∈ Q ∧ ∀ l ∈ LB M Q B, ⁅l, (v : G)⁆ ∈ Z from ⟨hvQ, hlv⟩
  have hCQt := (stroth_3_5 h34 hc h.hs.toSec5.width h.hs.toSec5.n_gt h.hs.toSec5.noA2
    h.hs.toSec5.gen).2.1
  rw [hCQt] at hmemC
  have hBZV : B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le (hc.B_le_Vt htL) sec39_Z_le_Vt
  have hvV : (v : G) ∈ Vt M (LB M Q B) B Z t := hBZV hmemC
  have hmemI : (v : G) ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    Subgroup.mem_inf.mpr ⟨hvV, v.2⟩
  rw [hinter] at hmemI
  exact hvZ hmemI

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_outer_claimB (hD' : Sec8DPrimeStatement) (hS : Sec8StrongClosureStatement)
    (hZV : Sec8ZVStatement) {hc : Ctx M Q Z B} {n : ℕ} {t r g l : G} (h : Sec8Outer hc n t r g)
    (hinter : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z)
    (hl : l ∈ LB M Q B) (hlx : ⁅l, g * t * g⁻¹⁆ ∉ Q)
    (hnorm : conjSubgroup (g * t * g⁻¹) (LB M Q B) = LB M Q B) :
    conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ conjSubgroup (l * g) (Vt M (LB M Q B) B Z t) = Z := by
  have ht : t ∈ LB M Q B := h.hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hlM : l ∈ M := hc.LB_le_M hl
  have hgN : g ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 h.hg
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem h.hg htM) (M.inv_mem h.hg)
  have hZV0 : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVV1 : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r :=
    le_inf le_sup_right le_sup_right
  have hlR : l ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hl
  have hZg : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro z hz
    have hz' : z ∈ conjSubgroup g Z := by
      rw [hc.conj_Z_eq h.hg]
      exact hz
    exact mem_conjSubgroup.mpr (hZV0 (mem_conjSubgroup.mp hz'))
  have hZl : Z ≤ conjSubgroup (l * g) (Vt M (LB M Q B) B Z t) := by
    intro z hz
    have hz' : z ∈ conjSubgroup (l * g) Z := by
      rw [hc.conj_Z_eq (M.mul_mem hlM h.hg)]
      exact hz
    exact mem_conjSubgroup.mpr (hZV0 (mem_conjSubgroup.mp hz'))
  refine le_antisymm ?_ (le_inf hZg hZl)
  by_contra hnot
  have hlt : Z < conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓
      conjSubgroup (l * g) (Vt M (LB M Q B) B Z t) :=
    lt_of_le_of_ne (le_inf hZg hZl) (fun e => hnot e.symm.le)
  obtain ⟨u, hu⟩ : ∃ u : G, u = g⁻¹ * l * g := ⟨_, rfl⟩
  have huM : u ∈ M := by
    rw [hu]
    exact M.mul_mem (M.mul_mem (M.inv_mem h.hg) hlM) h.hg
  have hI1 : conjSubgroup g⁻¹ (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓
      conjSubgroup (l * g) (Vt M (LB M Q B) B Z t)) =
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup u (Vt M (LB M Q B) B Z t) := by
    rw [hu, conjSubgroup_inf, ← conjSubgroup_mul, ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one, ← mul_assoc]
  have hlt_u : Z < Vt M (LB M Q B) B Z t ⊓ conjSubgroup u (Vt M (LB M Q B) B Z t) := by
    have hmono : conjSubgroup g⁻¹ Z ≤ conjSubgroup g⁻¹ (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓
        conjSubgroup (l * g) (Vt M (LB M Q B) B Z t)) :=
      fun z hz => mem_conjSubgroup.mpr (hlt.le (mem_conjSubgroup.mp hz))
    have hne : conjSubgroup g⁻¹ Z ≠ conjSubgroup g⁻¹ (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓
        conjSubgroup (l * g) (Vt M (LB M Q B) B Z t)) :=
      fun e => hlt.ne (conjSubgroup_inj.mp e)
    have h1 := lt_of_le_of_ne hmono hne
    rw [hc.conj_Z_eq (M.inv_mem h.hg), hI1] at h1
    exact h1
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  obtain ⟨h', hh'R, hh'⟩ := hD' G M Q Z B hc n t h.hs h.hna Z0 hZ0 u huM hlt_u
  have hh'M : h' ∈ M := hc.Rt_le_M t hh'R
  have hRQ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hn' : h' ∈ Subgroup.normalizer (Z0 : Set G) := hZ0.mem_normalizer hRQ hh'R
  have hut : u * t * u⁻¹ ∈ conjSubgroup u Z0 := by
    refine mem_conjSubgroup.mpr ?_
    rw [show u⁻¹ * (u * t * u⁻¹) * u = t by group]
    exact htZ0
  obtain ⟨hutL, hutN⟩ := Subgroup.mem_inf.mp (hh' hut)
  have hLN : h'⁻¹ * (u * t * u⁻¹) * h' ∈ LB M Q B ⊓ hc.CN t := by
    refine Subgroup.mem_inf.mpr ⟨mem_conjSubgroup.mp hutL, ?_⟩
    have h2 := hc.CN_conj_mem ht ((Rt M (LB M Q B) t).inv_mem hh'R) hutN
    rwa [inv_inv] at h2
  have hM' : h'⁻¹ * u ∈ M := M.mul_mem (M.inv_mem hh'M) huM
  have hs1 : (h'⁻¹ * u) * t * (h'⁻¹ * u)⁻¹ ∈ Z0 := by
    refine hS G M Q Z B hc n t h.hs Z0 hZ0 t htZ0 (h'⁻¹ * u) hM' ?_
    rw [show (h'⁻¹ * u) * t * (h'⁻¹ * u)⁻¹ = h'⁻¹ * (u * t * u⁻¹) * h' by group]
    exact hLN
  have hut0 : u * t * u⁻¹ ∈ Z0 := by
    have h3 := (Subgroup.mem_normalizer_iff.mp hn' _).mp hs1
    rwa [show h' * ((h'⁻¹ * u) * t * (h'⁻¹ * u)⁻¹) * h'⁻¹ = u * t * u⁻¹ by group] at h3
  have hxZ : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
    refine mem_conjSubgroup.mpr ?_
    rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group]
    exact htZ0
  have hlxZ : l * (g * t * g⁻¹) * l⁻¹ ∈ conjSubgroup g Z0 := by
    refine mem_conjSubgroup.mpr ?_
    rw [show g⁻¹ * (l * (g * t * g⁻¹) * l⁻¹) * g = u * t * u⁻¹ by rw [hu]; group]
    exact hut0
  have hēC : ⁅l, g * t * g⁻¹⁆ ∈ conjSubgroup g Z0 := by
    rw [commutatorElement_def]
    exact (conjSubgroup g Z0).mul_mem hlxZ ((conjSubgroup g Z0).inv_mem hxZ)
  have hs0 : g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g ∈ Z0 := mem_conjSubgroup.mp hēC
  have hs0Q : g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g ∉ Q := by
    intro hQ
    apply hlx
    have h4 := (Subgroup.mem_normalizer_iff.mp hgN _).mp hQ
    rwa [show g * (g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g) * g⁻¹ = ⁅l, g * t * g⁻¹⁆ by group] at h4
  have hxl : (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹ ∈ LB M Q B := by
    have h5 : (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹ ∈
        conjSubgroup (g * t * g⁻¹) (LB M Q B) := by
      refine mem_conjSubgroup.mpr ?_
      rw [show (g * t * g⁻¹)⁻¹ * ((g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) =
        l⁻¹ by group]
      exact (LB M Q B).inv_mem hl
    rwa [hnorm] at h5
  have hēL : ⁅l, g * t * g⁻¹⁆ ∈ LB M Q B := by
    rw [commutatorElement_def]
    have e : l * (g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹ =
        l * ((g * t * g⁻¹) * l⁻¹ * (g * t * g⁻¹)⁻¹) := by group
    rw [e]
    exact (LB M Q B).mul_mem hl hxl
  have hēN : ⁅l, g * t * g⁻¹⁆ ∈ hc.CN t := by
    have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z :=
      fun v hv => h.hvan v (hVV1 hv)
    rw [commutatorElement_def]
    exact sec8_comm_mem_CN hc ht hxM h.hxt hxV hlR
  have hēLN : g * (g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g) * g⁻¹ ∈ LB M Q B ⊓ hc.CN t := by
    rw [show g * (g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g) * g⁻¹ = ⁅l, g * t * g⁻¹⁆ by group]
    exact Subgroup.mem_inf.mpr ⟨hēL, hēN⟩
  have hēZ0 : ⁅l, g * t * g⁻¹⁆ ∈ Z0 := by
    have h6 := hS G M Q Z B hc n t h.hs Z0 hZ0 _ hs0 g h.hg hēLN
    rwa [show g * (g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g) * g⁻¹ = ⁅l, g * t * g⁻¹⁆ by group] at h6
  have hZe : Ut Q Z (⁅l, g * t * g⁻¹⁆) = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t h.hs Z0 hZ0 _ hēZ0 hlx
  have hZs : Ut Q Z (g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g) = Vt M (LB M Q B) B Z t :=
    hZV G M Q Z B hc n t h.hs Z0 hZ0 _ hs0 hs0Q
  have hcj := Ut_conj_of_normalizes (hc.conj_Q_eq h.hg) (hc.conj_Z_eq h.hg)
    (g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g)
  rw [show g * (g⁻¹ * ⁅l, g * t * g⁻¹⁆ * g) * g⁻¹ = ⁅l, g * t * g⁻¹⁆ by group, hZs, hZe] at hcj
  have hVg : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := hcj.symm
  rw [hVg, inf_idem] at hinter
  have hZlt : Z < Vt M (LB M Q B) B Z t := lt_of_lt_of_le hlt_u inf_le_left
  rw [hinter] at hZlt
  exact lt_irrefl _ hZlt

end

end CFSG.RankThree.GF2n.Stroth80
