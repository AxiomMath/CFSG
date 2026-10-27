module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpConj
public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.OddTranspositions.O4CloseReduction
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveLocalIso
import CFSG.OddTranspositions.PartThree.Twelve.SevenForm
import CFSG.OddTranspositions.O4PairCommSet
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpArith
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelChart
import CFSG.OddTranspositions.PartThree.Twelve.SevenClasses
import CFSG.OddTranspositions.PartThree.Twelve.NineSp
import CFSG.OddTranspositions.PartThree.Twelve.Ten
import CFSG.OddTranspositions.PartThree.Twelve.TenMarked
import CFSG.RankThree.PartOne.CTP.SeitzSpClosure
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldSemilinear
import CFSG.ClassicalGroups.Alternating.I4SpInvolTwo
import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.RankThree.PartOne.S11d.OddAlt
import CFSG.OddTranspositions.SevenFourEight.SevenSix
import CFSG.GroupTheory.InvolutionPow
import TauCeti.Combinatorics.Enumerative.PerfectMatching
import TauCeti.GroupTheory.Perm.Basic
import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QCount

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
open CFSG.OddTranspositions.QZ CFSG.GroupTheory.WeirSylow
open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D} {B : SpBranch hC}
  {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

omit [Fintype F] [DecidableEq F] in
private theorem exists_mem_Halpha_of_mem_closure_spTransvection
    (c : SpChart hC B.hα k F) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d) :
    ∀ u ∈ Subgroup.closure
      ((fun b => spTransvection b 1) ''
        {b | b ≠ 0 ∧ spForm k F (c.vec (hC.conj g).d) b = 0}),
      ∃ h' : Halpha D hC.alpha, (h' : G) ∈ Halpha D (hC.conj g).alpha ∧ c.ρ h' = u := by
  obtain ⟨hu, -, -, -⟩ := twelveTen_sp_center (hC := hC.conj g)
    (B.conj g).hMZ (B.conj g).hs (B.conj g).hn (B.conj g).hf (B.conj g).hSp
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨z, hz, hzv⟩ := c.exists_vec b hb.1
      have hzD : z ∈ D := hz.1
      have hzH : z ∈ Halpha D hC.alpha := mem_Halpha_of_mem_commSet hC B.hα hz
      have hzHv : z ∈ Halpha D (hC.conj g).alpha := by
        by_cases hzv' : z = (hC.conj g).d
        · rw [hzv']; exact hu
        · refine mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα ?_
          refine ⟨hzD, ?_, hzv'⟩
          exact (c.commute_iff z hz (hC.conj g).d hv).mpr (by
            rw [hzv, CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt, hb.2])
      refine ⟨⟨z, hzH⟩, hzHv, ?_⟩
      rw [c.map_eq z hz, hzv]
  | one => exact ⟨1, Subgroup.one_mem _, c.ρ.map_one⟩
  | mul x y _ _ ihx ihy =>
      obtain ⟨x', hx'v, hx'⟩ := ihx
      obtain ⟨y', hy'v, hy'⟩ := ihy
      exact ⟨x' * y', Subgroup.mul_mem _ hx'v hy'v, by rw [map_mul, hx', hy']⟩
  | inv x _ ih =>
      obtain ⟨x', hx'v, hx'⟩ := ih
      exact ⟨x'⁻¹, Subgroup.inv_mem _ hx'v, by rw [map_inv, hx']⟩

omit [DecidableEq F] in
theorem inf_centralizer_le_Halpha_conj (c : SpChart hC B.hα k F) (g : G)
    (hv : g * hC.d * g⁻¹ ∈ commSet D hC.d) :
    Halpha D hC.alpha ⊓ Subgroup.centralizer {g * hC.d * g⁻¹} ≤
      Halpha D (hC.conj g).alpha := by
  classical
  intro h hh
  obtain ⟨hH, hCv⟩ := hh
  set v : G := (hC.conj g).d with hvdef
  set Hv : Subgroup G := Halpha D (hC.conj g).alpha with hHvdef
  have hvd : v ∈ commSet D hC.d := hv
  have hvdD : v ∈ D := hvd.1
  have hvcomm : Commute v hC.d := hvd.2.1
  have hvne : v ≠ hC.d := hvd.2.2
  obtain ⟨hu, hcenter, -, -⟩ := twelveTen_sp_center (hC := hC.conj g)
    (B.conj g).hMZ (B.conj g).hs (B.conj g).hn (B.conj g).hf (B.conj g).hSp
  have hvHv : v ∈ Hv := hu
  have hdComm : hC.d ∈ commSet D v := ⟨hC.hd, hvcomm.symm, hvne.symm⟩
  have hdHv : hC.d ∈ Hv := mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdComm
  have hconjv : h * v * h⁻¹ = v := by
    have hc : Commute h v := Subgroup.mem_centralizer_singleton_iff.mp hCv
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hfix : spEnd (c.ρ ⟨h, hH⟩) (c.vec v) = c.vec v := by
    have h1 := (c.vec_conj ⟨h, hH⟩ hvd).2
    rw [hconjv] at h1
    exact h1.symm
  have hgen := mem_closure_spTransvection_of_spEnd_apply_eq hfix
  obtain ⟨h', h'v, h'ρ⟩ :=
    exists_mem_Halpha_of_mem_closure_spTransvection (B := B) c g hv _ hgen
  obtain ⟨hu₀, -, -, -⟩ := twelveTen_sp_center hC B.hMZ B.hs B.hn B.hf B.hSp
  have hker : (⟨h, hH⟩ * h'⁻¹ : Halpha D hC.alpha) ∈ c.ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h'ρ, mul_inv_cancel]
  have hzpow : (⟨h, hH⟩ * h'⁻¹ : Halpha D hC.alpha) ∈
      Subgroup.zpowers ⟨hC.d, hu₀⟩ := by
    rw [← c.ker_eq_zpowers B hu₀]
    exact hker
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzpow
  have hpow : ((hC.d : G) ^ m) = ((⟨h, hH⟩ * h'⁻¹ : Halpha D hC.alpha) : G) := by
    simpa using congrArg (fun y : Halpha D hC.alpha => (y : G)) hm
  have hxmem : ((h : G) * (h' : G)⁻¹) ∈ Hv := by
    have hval : ((⟨h, hH⟩ * h'⁻¹ : Halpha D hC.alpha) : G) = (h : G) * (h' : G)⁻¹ := rfl
    rw [← hval, ← hpow]
    exact Subgroup.zpow_mem _ hdHv m
  have hdecomp : (h : G) = ((h : G) * (h' : G)⁻¹) * (h' : G) := by group
  rw [hdecomp]
  exact Subgroup.mul_mem _ hxmem h'v

omit [Fintype F] in
private theorem exists_mem_Halpha_commute_of_spForm_eq_zero
    {g : G} (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (hdv : hC.d ∈ commSet D (hC.conj g).d)
    (hdH : hC.d ∈ Halpha D hC.alpha) (w : Fin k ⊕ Fin k → F)
    (hw : spForm k F (cv.vec hC.d) w = 0) :
    ∃ z : G, z ∈ Halpha D hC.alpha ∧
      ∃ hzHv : z ∈ Halpha D (hC.conj g).alpha,
        Commute z (hC.conj g).d ∧ cv.ρ ⟨z, hzHv⟩ = spTransvection w 1 := by
  by_cases hw0 : w = 0
  · subst hw0
    refine ⟨1, Subgroup.one_mem _, Subgroup.one_mem _, Commute.one_left _, ?_⟩
    rw [CFSG.RankThree.PartOne.CTP.spTransvection_zero,
      show (⟨1, Subgroup.one_mem _⟩ : Halpha D (hC.conj g).alpha) = 1 from rfl,
      map_one]
  · obtain ⟨z, hz, hzv⟩ := cv.exists_vec w hw0
    have hcommzd : Commute z hC.d := by
      refine (cv.commute_iff z hz hC.d hdv).mpr ?_
      rw [hzv, CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
      exact hw
    have hzH : z ∈ Halpha D hC.alpha := by
      by_cases hzd : z = hC.d
      · simpa [hzd] using hdH
      · exact mem_Halpha_of_mem_commSet hC B.hα ⟨hz.1, hcommzd, hzd⟩
    have hzHv : z ∈ Halpha D (hC.conj g).alpha :=
      mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz
    exact ⟨z, hzH, hzHv, hz.2.1, by rw [cv.map_eq z hz, hzv]⟩

theorem exists_conj_of_spForm_eq (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d) (cv : SpChart (hC.conj g) (B.conj g).hα k F) {x x' : G}
    (hx : x ∈ commSet D (hC.conj g).d) (hx' : x' ∈ commSet D (hC.conj g).d)
    (hxu : ¬ Commute x hC.d)
    (hb : spForm k F (cv.vec hC.d) (cv.vec x) =
      spForm k F (cv.vec hC.d) (cv.vec x')) :
    ∃ r ∈ Halpha D hC.alpha ⊓ Subgroup.centralizer {(hC.conj g).d}, r * x * r⁻¹ = x' := by
  classical
  set v : G := (hC.conj g).d with hvdef
  set y : Fin k ⊕ Fin k → F := cv.vec hC.d with hydef
  have hvd : v ∈ commSet D hC.d := hv
  have hdv : hC.d ∈ commSet D v := ⟨hC.hd, hvd.2.1.symm, hvd.2.2.symm⟩
  obtain ⟨hu₀, -, -, -⟩ := twelveTen_sp_center hC B.hMZ B.hs B.hn B.hf B.hSp
  have hdH : hC.d ∈ Halpha D hC.alpha := hu₀
  have h0 : spForm k F y (cv.vec x) ≠ 0 := by
    intro hzero
    exact hxu ((cv.commute_iff x hx hC.d hdv).mpr (by
      rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]; exact hzero))
  obtain ⟨w₁, w₂, hw₁, hw₂, hprod⟩ :=
    exists_spTransvection_mul_apply_eq (k := k) (F := F) h0 hb
  have hlift := exists_mem_Halpha_commute_of_spForm_eq_zero (B := B) cv hdv hdH
  obtain ⟨z₁, hz₁H, hz₁Hv, hz₁v, hz₁ρ⟩ := hlift w₁ hw₁
  obtain ⟨z₂, hz₂H, hz₂Hv, hz₂v, hz₂ρ⟩ := hlift w₂ hw₂
  have hrH : z₂ * z₁ ∈ Halpha D hC.alpha := Subgroup.mul_mem _ hz₂H hz₁H
  have hrHv : z₂ * z₁ ∈ Halpha D (hC.conj g).alpha := Subgroup.mul_mem _ hz₂Hv hz₁Hv
  have hrv : Commute (z₂ * z₁) v := hz₂v.mul_left hz₁v
  refine ⟨z₂ * z₁, ⟨hrH, Subgroup.mem_centralizer_singleton_iff.mpr hrv⟩, ?_⟩
  have hvec := (cv.vec_conj ⟨z₂ * z₁, hrHv⟩ hx).2
  have hρeq : cv.ρ ⟨z₂ * z₁, hrHv⟩ = spTransvection w₂ 1 * spTransvection w₁ 1 := by
    have heq : (⟨z₂ * z₁, hrHv⟩ : Halpha D (hC.conj g).alpha) =
        ⟨z₂, hz₂Hv⟩ * ⟨z₁, hz₁Hv⟩ := rfl
    rw [heq, map_mul, hz₂ρ, hz₁ρ]
  have hvecx : cv.vec ((z₂ * z₁) * x * (z₂ * z₁)⁻¹) = cv.vec x' := by
    rw [hvec, hρeq, hprod]
  exact cv.injOn (cv.vec_conj ⟨z₂ * z₁, hrHv⟩ hx).1 hx' hvecx

private def Fusion.S (g : G) : Set G :=
  commSet D (hC.conj g).d ∩ {x | ¬ Commute x hC.d}

private def Fusion.A : Set G := {x | x ∈ D ∧ ¬ Commute x hC.d}

private def Fusion.R (g : G) : Subgroup G :=
  Halpha D hC.alpha ⊓ Subgroup.centralizer {(hC.conj g).d}

omit [Finite G] in
private theorem Fusion.mem_S_iff {g x : G} :
    x ∈ Fusion.S (D := D) (hC := hC) g ↔
      x ∈ commSet D (hC.conj g).d ∧ ¬ Commute x hC.d := Iff.rfl

omit [Finite G] in
private theorem Fusion.mem_A_iff {x : G} :
    x ∈ Fusion.A (D := D) (hC := hC) ↔ x ∈ D ∧ ¬ Commute x hC.d := Iff.rfl

omit [Fintype F] [DecidableEq F] in
private theorem Fusion.beta_invariant (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (r : ↥(Halpha D hC.alpha ⊓ Subgroup.centralizer {(hC.conj g).d}))
    {x : G} (hx : x ∈ commSet D (hC.conj g).d) :
    spForm k F (cv.vec hC.d) (cv.vec ((r : G) * x * (r : G)⁻¹)) =
      spForm k F (cv.vec hC.d) (cv.vec x) := by
  classical
  have hrH : (r : G) ∈ Halpha D hC.alpha := r.2.1
  have hrv : Commute (r : G) (hC.conj g).d :=
    Subgroup.mem_centralizer_singleton_iff.mp r.2.2
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  obtain ⟨k₀, F₀, _, _, _, hnk₀, hF₀, ⟨c₀⟩⟩ :=
    exists_spChart hC B.hMZ B.hα B.hs B.hSp
  have hrHv : (r : G) ∈ Halpha D (hC.conj g).alpha :=
    (inf_centralizer_le_Halpha_conj (B := B) (c := c₀) g
      (by simpa [HypothesisC.conj_d] using hv)) ⟨hrH, r.2.2⟩
  let rv : Halpha D (hC.conj g).alpha := ⟨(r : G), hrHv⟩
  have hvecx := (cv.vec_conj rv hx).2
  have hvecd := (cv.vec_conj rv hdv).2
  have hfixr : (r : G) * hC.d * (r : G)⁻¹ = hC.d := by
    have hc := commute_d_of_mem_Halpha hC B.hα ⟨(r : G), hrH⟩
    rw [hc.eq, mul_inv_cancel_right]
  have hfix : spEnd (cv.ρ rv) (cv.vec hC.d) = cv.vec hC.d := by
    rw [← hvecd, hfixr]
  calc spForm k F (cv.vec hC.d) (cv.vec ((r : G) * x * (r : G)⁻¹))
      = spForm k F (cv.vec hC.d) (spEnd (cv.ρ rv) (cv.vec x)) := by rw [hvecx]
    _ = spForm k F (spEnd (cv.ρ rv) (cv.vec hC.d)) (spEnd (cv.ρ rv) (cv.vec x)) := by
        rw [hfix]
    _ = spForm k F (cv.vec hC.d) (cv.vec x) :=
        spForm_spEnd_spEnd (cv.ρ rv) (cv.vec hC.d) (cv.vec x)

omit [Finite G] in
private theorem Fusion.mul_d_mul_inv_eq {hα : hC.alpha = {hC.d}} {r : G}
    (hrH : r ∈ Halpha D hC.alpha) :
    r * hC.d * r⁻¹ = hC.d := by
  have hc := commute_d_of_mem_Halpha hC hα ⟨r, hrH⟩
  rw [hc.eq, mul_inv_cancel_right]

private noncomputable def Fusion.beta (g : G)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F) (x : G) : F :=
  spForm k F (cv.vec hC.d) (cv.vec x)

omit [Fintype F] [DecidableEq F] in
private theorem Fusion.beta_ne_zero (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    {x : G} (hx : x ∈ Fusion.S (D := D) (hC := hC) g) :
    Fusion.beta (hC := hC) (B := B) g cv x ≠ 0 := by
  obtain ⟨hxV, hxd⟩ := (Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mp hx
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  intro h0
  exact hxd ((cv.commute_iff x hxV hC.d hdv).mpr (by
    rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
    exact h0))

private theorem Fusion.exists_beta (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    {b : F} (hb : b ≠ 0) :
    ∃ x : G, x ∈ Fusion.S (D := D) (hC := hC) g ∧
      Fusion.beta (hC := hC) (B := B) g cv x = b := by
  classical
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  set y : Fin k ⊕ Fin k → F := cv.vec hC.d with hydef
  have hy : y ≠ 0 := cv.vec_ne_zero hC.d hdv
  obtain ⟨z, hz⟩ : ∃ z, spForm k F y z ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (spForm_nondegenerate.2 y (fun z => by
      rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]; exact h z))
  have hz0 : z ≠ 0 := fun h0 => hz (by rw [h0, map_zero])
  set w : Fin k ⊕ Fin k → F := (b / spForm k F y z) • z with hwdef
  have hcoef : b / spForm k F y z ≠ 0 := div_ne_zero hb hz
  have hw0 : w ≠ 0 := by
    rw [hwdef]
    exact smul_ne_zero hcoef hz0
  have hyw : spForm k F y w = b := by
    rw [hwdef, map_smul, smul_eq_mul]
    exact div_mul_cancel₀ b hz
  obtain ⟨x, hxV, hxv⟩ := cv.exists_vec w hw0
  have hxd : ¬ Commute x hC.d := by
    intro hcomm
    have h1 := (cv.commute_iff x hxV hC.d hdv).mp hcomm
    rw [hxv, CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt, hyw] at h1
    exact hb h1
  refine ⟨x, (Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mpr ⟨hxV, hxd⟩, ?_⟩
  show spForm k F (cv.vec hC.d) (cv.vec x) = b
  rw [hxv, ← hydef]
  exact hyw

private abbrev Fusion.R_setoid (g : G) : Setoid ↥(Fusion.S (D := D) (hC := hC) g) :=
  CFSG.Quasithin.Loc442Q.orbSetoid (Fusion.R (D := D) (hC := hC) g)
    (Fusion.S (D := D) (hC := hC) g)

omit [Fintype F] [DecidableEq F] in
private theorem Fusion.R_rel_beta (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    {x y : ↥(Fusion.S (D := D) (hC := hC) g)}
    (h : (Fusion.R_setoid (D := D) (hC := hC) g).r x y) :
    Fusion.beta (hC := hC) (B := B) g cv (x : G) =
      Fusion.beta (hC := hC) (B := B) g cv (y : G) := by
  obtain ⟨r, hrR, hy⟩ := h
  have hxV : (x : G) ∈ commSet D (hC.conj g).d :=
    ((Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mp x.2).1
  let r' : ↥(Fusion.R (D := D) (hC := hC) g) :=
    ⟨r⁻¹, (Fusion.R (D := D) (hC := hC) g).inv_mem hrR⟩
  have hry : (r' : G) * (x : G) * (r' : G)⁻¹ = (y : G) := by
    change r⁻¹ * (x : G) * (r⁻¹)⁻¹ = (y : G)
    rw [inv_inv]
    exact hy.symm
  rw [← hry]
  exact (Fusion.beta_invariant (B := B) g hv cv r' hxV).symm

private noncomputable def Fusion.betaBar (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F) :
    Quotient (Fusion.R_setoid (D := D) (hC := hC) g) → {b : F // b ≠ 0} :=
  Quotient.lift
    (fun x => ⟨Fusion.beta (hC := hC) (B := B) g cv (x : G),
      Fusion.beta_ne_zero g hv cv x.2⟩)
    (by
      intro x y hxy
      apply Subtype.ext
      exact Fusion.R_rel_beta (B := B) g hv cv hxy)

private theorem Fusion.betaBar_injective (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F) :
    Function.Injective (Fusion.betaBar (hC := hC) (B := B) g hv cv) := by
  intro q q' h
  revert q'
  refine Quotient.inductionOn q (fun x => ?_)
  intro q'
  refine Quotient.inductionOn q' (fun y => ?_)
  intro h
  have hβ : Fusion.beta (hC := hC) (B := B) g cv (x : G) =
      Fusion.beta (hC := hC) (B := B) g cv (y : G) := by
    have h1 := congrArg Subtype.val h
    simpa [Fusion.betaBar] using h1
  have hxu : ¬ Commute (x : G) hC.d :=
    ((Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mp x.2).2
  have hxV : (x : G) ∈ commSet D (hC.conj g).d :=
    ((Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mp x.2).1
  have hyV : (y : G) ∈ commSet D (hC.conj g).d :=
    ((Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mp y.2).1
  obtain ⟨r, hrR, hrx⟩ :=
    exists_conj_of_spForm_eq (B := B) g hv cv hxV hyV hxu hβ
  exact Quotient.sound (show (Fusion.R_setoid (D := D) (hC := hC) g).r x y from
    ⟨r⁻¹, (Fusion.R (D := D) (hC := hC) g).inv_mem hrR, by
      rw [inv_inv]
      exact hrx.symm⟩)

private theorem Fusion.betaBar_surjective (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F) :
    Function.Surjective (Fusion.betaBar (hC := hC) (B := B) g hv cv) := by
  intro b
  obtain ⟨x, hxS, hxb⟩ := Fusion.exists_beta (B := B) g hv cv b.2
  refine ⟨Quotient.mk (Fusion.R_setoid (D := D) (hC := hC) g) ⟨x, hxS⟩, ?_⟩
  apply Subtype.ext
  simpa [Fusion.betaBar] using hxb

private theorem Fusion.card_R_orbits (hF : Nat.card F = 2 ^ B.f) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F) :
    Nat.card (Quotient (Fusion.R_setoid (D := D) (hC := hC) g)) = 2 ^ B.f - 1 := by
  let e : Quotient (Fusion.R_setoid (D := D) (hC := hC) g) ≃ {b : F // b ≠ 0} :=
    Equiv.ofBijective (Fusion.betaBar (hC := hC) (B := B) g hv cv)
      ⟨Fusion.betaBar_injective g hv cv, Fusion.betaBar_surjective g hv cv⟩
  have h1 := Nat.card_congr e
  rw [h1]
  have h2 : Nat.card {b : F // b ≠ 0} = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (p := fun b : F => b = 0)]
    simp
  rw [h2, hF]

private def Fusion.tau (hC : HypothesisC D) (x : G) : G := hC.d * x * hC.d⁻¹

omit [Finite G] in
private theorem Fusion.tau_involutive (x : G) :
    Fusion.tau hC (Fusion.tau hC x) = x := by
  have hd2 := hC.setup.oddT.mul_self_eq_one hC.hd
  rw [Fusion.tau, Fusion.tau, hC.setup.oddT.inv_eq hC.hd]
  calc hC.d * (hC.d * x * hC.d) * hC.d
      = (hC.d * hC.d) * x * (hC.d * hC.d) := by group
    _ = x := by rw [hd2]; simp

omit [Finite G] in
private theorem Fusion.tau_mem_line {w x : G} (hx : x ∈ lineMem D hC.d w) :
    Fusion.tau hC x ∈ lineMem D hC.d w := by
  rw [mem_lineMem] at hx ⊢
  refine ⟨hC.setup.conj_mem _ hx.1, ?_⟩
  rintro y hy
  have hyd : Commute y hC.d := hy.1.2
  have hyx : Commute y x := (hx.2 hy).2
  have h1 : Commute (hC.d * y * hC.d⁻¹) (hC.d * x * hC.d⁻¹) :=
    (Commute.conj_iff hC.d).mpr hyx
  have h2 : hC.d * y * hC.d⁻¹ = y := by rw [hyd.eq.symm, mul_inv_cancel_right]
  rw [h2] at h1
  exact ⟨hy.1.1, h1⟩

omit [Finite G] in
private theorem Fusion.tau_ne_d {x : G} (hxne : x ≠ hC.d) :
    Fusion.tau hC x ≠ hC.d := by
  intro h
  have hd2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hh : hC.d * x * hC.d = hC.d := by
    simpa [Fusion.tau, hC.setup.oddT.inv_eq hC.hd] using h
  have hxeq : x = hC.d := by
    have h1 : hC.d * (hC.d * x * hC.d) * hC.d = x := by
      rw [show hC.d * (hC.d * x * hC.d) * hC.d =
        (hC.d * hC.d) * x * (hC.d * hC.d) by group, hd2]
      simp
    rw [← h1, hh]
    rw [hd2, one_mul]
  exact hxne hxeq

omit [Finite G] in
private theorem Fusion.tau_ne_self (hL : IsHypLineSpace D) {w : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) {x : G} (hx : x ∈ lineMem D hC.d w) (hxne : x ≠ hC.d) :
    Fusion.tau hC x ≠ x := by
  intro h
  have hxd := (hL hC.d hC.hd w hw hwd x hx hxne).1
  have hd2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hh : hC.d * x * hC.d = x := by
    simpa [Fusion.tau, hC.setup.oddT.inv_eq hC.hd] using h
  have h1 : (hC.d * x * hC.d) * hC.d = hC.d * x := by
    rw [mul_assoc, hd2, mul_one]
  have hdx : hC.d * x = x * hC.d := by
    rw [← h1, hh]
  exact hxd hdx.symm

private abbrev Fusion.A_setoid : Setoid ↥(Fusion.A (D := D) (hC := hC)) :=
  CFSG.Quasithin.Loc442Q.orbSetoid (Halpha D hC.alpha) (Fusion.A (D := D) (hC := hC))

private def Fusion.pair_tau {w : G} (x : ↥(lineMem D hC.d w \ {hC.d})) :
    ↥(lineMem D hC.d w \ {hC.d}) :=
  ⟨Fusion.tau hC (x : G), by
    have hxℓ : (x : G) ∈ lineMem D hC.d w := x.2.1
    have hxne : (x : G) ≠ hC.d := x.2.2
    exact ⟨Fusion.tau_mem_line hxℓ, Fusion.tau_ne_d hxne⟩⟩

omit [Finite G] in
private theorem Fusion.pair_tau_involutive {w : G} (x : ↥(lineMem D hC.d w \ {hC.d})) :
    Fusion.pair_tau (Fusion.pair_tau x) = x := by
  apply Subtype.ext
  exact Fusion.tau_involutive (x : G)

omit [Finite G] in
private theorem Fusion.pair_tau_ne_self (hL : IsHypLineSpace D) {w : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (x : ↥(lineMem D hC.d w \ {hC.d})) :
    Fusion.pair_tau x ≠ x := by
  intro h
  exact Fusion.tau_ne_self hL hw hwd x.2.1 x.2.2 (congrArg Subtype.val h)

private def Fusion.pair_setoid {w : G} : Setoid ↥(lineMem D hC.d w \ {hC.d}) :=
  Equiv.Perm.SameCycle.setoid
    (Function.Involutive.toPerm (Fusion.pair_tau (D := D) (hC := hC) (w := w))
      (show Function.Involutive (Fusion.pair_tau (D := D) (hC := hC) (w := w)) from
        Fusion.pair_tau_involutive (D := D) (hC := hC) (w := w)))

private theorem Fusion.card_pairs (hL : IsHypLineSpace D) {w : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) :
    Nat.card (Quotient (Fusion.pair_setoid (D := D) (hC := hC) (w := w))) * 2 =
      Nat.card ↥(lineMem D hC.d w \ {hC.d}) := by
  classical
  let τ := Fusion.pair_tau (D := D) (hC := hC) (w := w)
  let hτ : Function.Involutive τ :=
    Fusion.pair_tau_involutive (D := D) (hC := hC) (w := w)
  have hpm : TauCeti.IsPerfectMatching (Function.Involutive.toPerm τ hτ) := by
    rw [TauCeti.isPerfectMatching_iff]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [Function.Involutive.coe_toPerm]
      exact Fusion.pair_tau_involutive x
    · rw [Function.Involutive.coe_toPerm]
      exact Fusion.pair_tau_ne_self hL hw hwd x
  have h := TauCeti.IsPerfectMatching.two_mul_orbitCount hpm
  rw [TauCeti.orbitCount_def] at h
  change 2 * Nat.card (Quotient (Fusion.pair_setoid (D := D) (hC := hC) (w := w))) =
    Nat.card ↥(lineMem D hC.d w \ {hC.d}) at h
  rw [mul_comm] at h
  exact h

private theorem Fusion.mem_normalizer_hypLineGroup {hα : hC.alpha = {hC.d}}
    (hL : IsHypLineSpace D) {w x y h : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hx : x ∈ lineMem D hC.d w) (hxne : x ≠ hC.d)
    (hy : y ∈ lineMem D hC.d w) (hyne : y ≠ hC.d)
    (hh : h ∈ Halpha D hC.alpha) (hxy : h * x * h⁻¹ = y) :
    h ∈ Subgroup.normalizer (hypLineGroup D hC.d x : Set G) := by
  have hcomm : Commute h hC.d := commute_d_of_mem_Halpha hC hα ⟨h, hh⟩
  have hΓ : commSet D hC.d ∩ commSet D y = commSet D hC.d ∩ commSet D x :=
    (IsHypLineSpace.commSet_inter_eq hL hC.hd hw hwd hy hyne).trans
      (IsHypLineSpace.commSet_inter_eq hL hC.hd hw hwd hx hxne).symm
  refine Subgroup.mem_normalizer_fintype (S := (hypLineGroup D hC.d x : Set G)) ?_
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨hzV, hzx⟩ := hz
      have hmemd : h * z * h⁻¹ ∈ commSet D hC.d :=
        conj_mem_commSet_of_commute hC.setup.normal hcomm hzV
      have hmemx : h * z * h⁻¹ ∈ commSet D y := by
        have h1 := conj_mem_commSet hC.setup.normal h hzx
        rwa [hxy] at h1
      have hboth : h * z * h⁻¹ ∈ commSet D hC.d ∩ commSet D y := ⟨hmemd, hmemx⟩
      rw [hΓ] at hboth
      exact Subgroup.subset_closure hboth
  | one => simp
  | mul a b ha hb iha ihb =>
      rw [show h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) by group]
      exact Subgroup.mul_mem _ iha ihb
  | inv a ha iha =>
      rw [show h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ iha

private theorem Fusion.pair_rel_of_conj (B : SpBranch hC) {hα : hC.alpha = {hC.d}}
    (hL : IsHypLineSpace D) {w x y h : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hx : x ∈ lineMem D hC.d w) (hxne : x ≠ hC.d)
    (hy : y ∈ lineMem D hC.d w) (hyne : y ≠ hC.d)
    (hh : h ∈ Halpha D hC.alpha) (hxy : h * x * h⁻¹ = y) :
    y = x ∨ y = Fusion.tau hC x := by
  have hN := Fusion.mem_normalizer_hypLineGroup (hα := hα) hL hw hwd hx hxne hy hyne hh hxy
  have hxD : x ∈ D := (mem_lineMem.mp hx).1
  have hxd : ¬ Commute x hC.d := (hL hC.d hC.hd w hw hwd x hx hxne).1
  obtain ⟨v, hv⟩ := B.hdiam x hxD hC.d hC.hd hxd
  have hstab := (twelveTen_sp_stabilizers_of_commSet_inter B.hIH hC B.hMZ B.hα B.hs
    B.hn B.hf B.hSp hv.2 hxD hxd hv.1.2.1.symm).1
  rcases hstab h hh hN with hLmem | hdLmem
  · have hcomm := OddLocal.commute_of_mem_closure_commSet
      (Subgroup.closure_mono Set.inter_subset_right hLmem)
    have h3 : h * x * h⁻¹ = x := by rw [hcomm.eq, mul_inv_cancel_right]
    left
    rw [← hxy]
    exact h3
  · have hcomm := OddLocal.commute_of_mem_closure_commSet
      (Subgroup.closure_mono Set.inter_subset_right hdLmem)
    have h1 : (hC.d * h) * x * (hC.d * h)⁻¹ = x := by
      rw [hcomm.eq, mul_inv_cancel_right]
    have hd2 := hC.setup.oddT.mul_self_eq_one hC.hd
    have h2a : hC.d * ((hC.d * h) * x * (hC.d * h)⁻¹) * hC.d =
        hC.d * x * hC.d := by rw [h1]
    have hh1 : (hC.d * h) * x * (hC.d * h)⁻¹ = x := h1
    rw [mul_inv_rev, hC.setup.oddT.inv_eq hC.hd] at hh1
    have h2b : hC.d * ((hC.d * h) * x * (hC.d * h)⁻¹) * hC.d =
        h * x * h⁻¹ := by
      rw [mul_inv_rev, hC.setup.oddT.inv_eq hC.hd]
      calc hC.d * ((hC.d * h) * x * (h⁻¹ * hC.d)) * hC.d
          = (hC.d * hC.d) * h * x * h⁻¹ * (hC.d * hC.d) := by group
        _ = h * x * h⁻¹ := by rw [hd2]; group
    have h2 : h * x * h⁻¹ = hC.d * x * hC.d⁻¹ := by
      rw [← h2b, h2a, hC.setup.oddT.inv_eq hC.hd]
    right
    rw [← hxy]
    exact h2

omit [Finite G] in
private theorem Fusion.A_mem_of_line (hL : IsHypLineSpace D) {w x : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (hx : x ∈ lineMem D hC.d w) (hxne : x ≠ hC.d) :
    x ∈ Fusion.A (D := D) (hC := hC) :=
  ⟨(mem_lineMem.mp hx).1, (hL hC.d hC.hd w hw hwd x hx hxne).1⟩

private noncomputable def Fusion.pair_map (hL : IsHypLineSpace D) {w : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (hdH : hC.d ∈ Halpha D hC.alpha) :
    Quotient (Fusion.pair_setoid (D := D) (hC := hC) (w := w)) →
      Quotient (Fusion.A_setoid (D := D) (hC := hC)) :=
  Quotient.lift
    (fun x => Quotient.mk (Fusion.A_setoid (D := D) (hC := hC))
      ⟨(x : G), Fusion.A_mem_of_line hL hw hwd x.2.1 x.2.2⟩)
    (by
      intro x y hxy
      change (Function.Involutive.toPerm
          (Fusion.pair_tau (D := D) (hC := hC) (w := w))
          (show Function.Involutive (Fusion.pair_tau (D := D) (hC := hC) (w := w)) from
            Fusion.pair_tau_involutive (D := D) (hC := hC) (w := w))).SameCycle x y at hxy
      have hxy' := hxy.symm
      rw [TauCeti.sameCycle_toPerm_iff] at hxy'
      apply Quotient.sound
      rcases hxy' with h | h
      · refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [h]
        simp
      · refine ⟨hC.d, hdH, ?_⟩
        have hτ : hC.d * (x : G) * hC.d⁻¹ = (y : G) :=
          congrArg Subtype.val h.symm
        rw [hC.setup.oddT.inv_eq hC.hd] at hτ
        rw [hC.setup.oddT.inv_eq hC.hd]
        exact hτ.symm)

private theorem Fusion.pair_map_injective (B : SpBranch hC) (hL : IsHypLineSpace D)
    {w : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (hdH : hC.d ∈ Halpha D hC.alpha) :
    Function.Injective (Fusion.pair_map (hC := hC) hL hw hwd hdH) := by
  intro q q' h
  revert q'
  refine Quotient.inductionOn q (fun x => ?_)
  intro q'
  refine Quotient.inductionOn q' (fun y => ?_)
  intro h
  change Quotient.mk (Fusion.A_setoid (D := D) (hC := hC))
      ⟨(x : G), Fusion.A_mem_of_line hL hw hwd x.2.1 x.2.2⟩ =
    Quotient.mk (Fusion.A_setoid (D := D) (hC := hC))
      ⟨(y : G), Fusion.A_mem_of_line hL hw hwd y.2.1 y.2.2⟩ at h
  obtain ⟨r, hrH, hrrel⟩ := Quotient.exact h
  let r' : ↥(Halpha D hC.alpha) := ⟨r⁻¹, (Halpha D hC.alpha).inv_mem hrH⟩
  have hrxy : (r' : G) * (x : G) * (r' : G)⁻¹ = (y : G) := by
    change r⁻¹ * (x : G) * (r⁻¹)⁻¹ = (y : G)
    rw [inv_inv]
    exact hrrel.symm
  have hpairG : (y : G) = (x : G) ∨ (y : G) = Fusion.tau hC (x : G) :=
    Fusion.pair_rel_of_conj (B := B) (hα := B.hα) hL hw hwd x.2.1 x.2.2 y.2.1 y.2.2
      r'.2 hrxy
  have hpair : (Function.Involutive.toPerm
      (Fusion.pair_tau (D := D) (hC := hC) (w := w))
      (show Function.Involutive (Fusion.pair_tau (D := D) (hC := hC) (w := w)) from
        Fusion.pair_tau_involutive (D := D) (hC := hC) (w := w))).SameCycle x y := by
    rw [TauCeti.sameCycle_toPerm_iff]
    rcases hpairG with h | h
    · exact Or.inl (Subtype.ext h.symm)
    · refine Or.inr (Subtype.ext ?_)
      change (x : G) = Fusion.tau hC (y : G)
      rw [h]
      exact congrArg Subtype.val (Fusion.pair_tau_involutive x).symm
  exact Quotient.sound hpair

private theorem Fusion.A_orbit_meets_S (B : SpBranch hC) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d) {a : G}
    (ha : a ∈ Fusion.A (D := D) (hC := hC)) :
    ∃ y : G, y ∈ Fusion.S (D := D) (hC := hC) g ∧
      ∃ h ∈ Halpha D hC.alpha, h * a * h⁻¹ = y := by
  obtain ⟨haD, hau⟩ := (Fusion.mem_A_iff (D := D) (hC := hC)).mp ha
  obtain ⟨u, hu⟩ := B.hdiam a haD hC.d hC.hd hau
  have huE : u ∈ DalphaStar D hC.alpha := by
    rw [DalphaStar_eq_commSet_of_alpha_eq hC B.hα]
    exact hu.2
  have hvE : (hC.conj g).d ∈ DalphaStar D hC.alpha := by
    rw [DalphaStar_eq_commSet_of_alpha_eq hC B.hα]
    exact hv
  obtain ⟨h, hhH, hhu⟩ := hC.Halpha_transitive u huE (hC.conj g).d hvE
  have hfixd : h * hC.d * h⁻¹ = hC.d := Fusion.mul_d_mul_inv_eq (hα := B.hα) hhH
  refine ⟨h * a * h⁻¹, ?_, ⟨h, hhH, rfl⟩⟩
  have hyD : h * a * h⁻¹ ∈ D := hC.setup.conj_mem _ haD
  have hyv : Commute (h * a * h⁻¹) (hC.conj g).d := by
    have h1 : Commute (h * a * h⁻¹) (h * u * h⁻¹) :=
      (Commute.conj_iff h).mpr hu.1.2.1.symm
    rwa [hhu] at h1
  have hynv : h * a * h⁻¹ ≠ (hC.conj g).d := by
    intro heq
    have hcomm : Commute (h * a * h⁻¹) hC.d := by
      rw [heq]
      exact hv.2.1
    have h1 : Commute (h * a * h⁻¹) (h * hC.d * h⁻¹) := by rwa [← hfixd] at hcomm
    exact hau ((Commute.conj_iff h).mp h1)
  have hynu : ¬ Commute (h * a * h⁻¹) hC.d := by
    intro hcomm
    have h1 : Commute (h * a * h⁻¹) (h * hC.d * h⁻¹) := by rwa [← hfixd] at hcomm
    exact hau ((Commute.conj_iff h).mp h1)
  exact (Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mpr
    ⟨⟨hyD, hyv, hynv⟩, hynu⟩

omit [Finite G] in
private theorem Fusion.R_le_Halpha (g : G) :
    Fusion.R (D := D) (hC := hC) g ≤ Halpha D hC.alpha :=
  inf_le_left

omit [Finite G] in
private theorem Fusion.S_subset_A (g : G) :
    Fusion.S (D := D) (hC := hC) g ⊆ Fusion.A (D := D) (hC := hC) := by
  intro x hx
  obtain ⟨hxV, hxu⟩ := (Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mp hx
  exact ⟨hxV.1, hxu⟩

private noncomputable abbrev Fusion.R_to_A_map (g : G) :
    Quotient (Fusion.R_setoid (D := D) (hC := hC) g) →
      Quotient (Fusion.A_setoid (D := D) (hC := hC)) :=
  CFSG.Quasithin.Loc442Q.OrbSet.map
    (Fusion.R_le_Halpha (D := D) (hC := hC) g)
    (Fusion.S_subset_A (D := D) (hC := hC) g)

private theorem Fusion.R_to_A_map_surjective (B : SpBranch hC) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d) :
    Function.Surjective (Fusion.R_to_A_map (hC := hC) g) := by
  intro q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  obtain ⟨y, hyS, h, hhH, hhay⟩ := Fusion.A_orbit_meets_S B g hv a.2
  refine ⟨CFSG.Quasithin.Loc442Q.OrbSet.mk (A := Fusion.R (D := D) (hC := hC) g)
    (S := Fusion.S (D := D) (hC := hC) g) ⟨y, hyS⟩, ?_⟩
  change CFSG.Quasithin.Loc442Q.OrbSet.map
      (Fusion.R_le_Halpha (D := D) (hC := hC) g)
      (Fusion.S_subset_A (D := D) (hC := hC) g)
      (CFSG.Quasithin.Loc442Q.OrbSet.mk ⟨y, hyS⟩) =
    CFSG.Quasithin.Loc442Q.OrbSet.mk a
  rw [CFSG.Quasithin.Loc442Q.OrbSet.map_mk]
  rw [CFSG.Quasithin.Loc442Q.OrbSet.mk_eq_mk]
  refine ⟨h, hhH, ?_⟩
  change (a : G) = h⁻¹ * y * h
  rw [← hhay]
  group

private theorem Fusion.two_lines (B : SpBranch hC) :
    ∃ w₁ w₂ : G, w₁ ∈ D ∧ ¬ Commute w₁ hC.d ∧
      (lineMem D hC.d w₁).ncard = 2 ^ B.f + 1 ∧
      w₂ ∈ D ∧ ¬ Commute w₂ hC.d ∧ (lineMem D hC.d w₂).ncard = 2 ^ B.f - 1 := by
  obtain ⟨-, -, ⟨w₁, hw₁, hw₁d, hℓ₁⟩, ⟨w₂, hw₂, hw₂d, hℓ₂⟩⟩ :=
    twelveSeven_sp B.hIH hC B.hMZ B.hα B.hs B.hn B.hf B.hSp
  exact ⟨w₁, w₂, hw₁, hw₁d, hℓ₁, hw₂, hw₂d, hℓ₂⟩

private theorem Fusion.isHypLineSpace (B : SpBranch hC) : IsHypLineSpace D :=
  isHypLineSpace_sp B.hIH hC B.hMZ B.hα B.hs B.hn B.hf B.hSp
    (fun w hw hwd => B.hdiam hC.d hC.hd w hw (fun h => hwd h.symm))

omit [Finite G] in
private theorem Fusion.lineMem_of_mem (hL : IsHypLineSpace D) {w x : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (hx : x ∈ lineMem D hC.d w) (hxne : x ≠ hC.d) :
    lineMem D hC.d x = lineMem D hC.d w := by
  have hdmem : hC.d ∈ lineMem D hC.d w := by
    rw [mem_lineMem]
    exact ⟨hC.hd, fun z hz => hz.1⟩
  exact (hL.lineMem_eq hC.hd hw hwd hdmem hx hxne).2

omit [Finite G] in
private theorem Fusion.pair_ranges_disjoint (B : SpBranch hC) (hL : IsHypLineSpace D)
    {w₁ w₂ : G} (hw₁ : w₁ ∈ D) (hwd₁ : ¬ Commute w₁ hC.d)
    (hw₂ : w₂ ∈ D) (hwd₂ : ¬ Commute w₂ hC.d)
    (hℓ₁ : (lineMem D hC.d w₁).ncard = 2 ^ B.f + 1)
    (hℓ₂ : (lineMem D hC.d w₂).ncard = 2 ^ B.f - 1)
    (hdH : hC.d ∈ Halpha D hC.alpha) :
    Disjoint (Set.range (Fusion.pair_map (hC := hC) hL hw₁ hwd₁ hdH))
      (Set.range (Fusion.pair_map (hC := hC) hL hw₂ hwd₂ hdH)) := by
  rw [Set.disjoint_left]
  rintro z ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q₂
  have hEq : Fusion.pair_map (hC := hC) hL hw₁ hwd₁ hdH ⟦x⟧ =
      Fusion.pair_map (hC := hC) hL hw₂ hwd₂ hdH ⟦y⟧ := by
    rw [hq₁, hq₂]
  simp only [Fusion.pair_map, Quotient.lift_mk] at hEq
  obtain ⟨r, hrH, hrrel⟩ := Quotient.exact hEq
  let r' : ↥(Halpha D hC.alpha) := ⟨r⁻¹, (Halpha D hC.alpha).inv_mem hrH⟩
  have hrxy : (r' : G) * (x : G) * (r' : G)⁻¹ = (y : G) := by
    change r⁻¹ * (x : G) * (r⁻¹)⁻¹ = (y : G)
    rw [inv_inv]
    exact hrrel.symm
  have hlinex : lineMem D hC.d (x : G) = lineMem D hC.d w₁ :=
    Fusion.lineMem_of_mem hL hw₁ hwd₁ x.2.1 x.2.2
  have hliney : lineMem D hC.d (y : G) = lineMem D hC.d w₂ :=
    Fusion.lineMem_of_mem hL hw₂ hwd₂ y.2.1 y.2.2
  have hfixd : (r' : G) * hC.d * (r' : G)⁻¹ = hC.d :=
    Fusion.mul_d_mul_inv_eq (hα := B.hα) r'.2
  have hconj : lineMem D hC.d (y : G) =
      MulAut.conj (r' : G) '' lineMem D hC.d (x : G) := by
    have h := lineMem_conj hC.setup.normal (r' : G) hC.d (x : G)
    rw [hfixd, hrxy] at h
    exact h
  have hcardeq : (lineMem D hC.d (y : G)).ncard = (lineMem D hC.d (x : G)).ncard := by
    rw [hconj, Set.ncard_image_of_injective _ (MulAut.conj (r' : G)).injective]
  rw [hliney, hlinex, hℓ₁, hℓ₂] at hcardeq
  have hq : 4 ≤ 2 ^ B.f := B.four_le_two_pow
  omega

private theorem Fusion.card_pairs_plus (hL : IsHypLineSpace D) {w : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (hℓ : (lineMem D hC.d w).ncard = 2 ^ B.f + 1) :
    Nat.card (Quotient (Fusion.pair_setoid (D := D) (hC := hC) (w := w))) * 2 =
      2 ^ B.f := by
  rw [Fusion.card_pairs hL hw hwd]
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (by
    rw [mem_lineMem]
    exact ⟨hC.hd, fun z hz => hz.1⟩), hℓ]
  exact Nat.add_sub_cancel _ _

private theorem Fusion.card_pairs_minus (hL : IsHypLineSpace D) {w : G} (hw : w ∈ D)
    (hwd : ¬ Commute w hC.d) (hℓ : (lineMem D hC.d w).ncard = 2 ^ B.f - 1) :
    Nat.card (Quotient (Fusion.pair_setoid (D := D) (hC := hC) (w := w))) * 2 =
      2 ^ B.f - 2 := by
  rw [Fusion.card_pairs hL hw hwd]
  rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem (by
    rw [mem_lineMem]
    exact ⟨hC.hd, fun z hz => hz.1⟩), hℓ]
  rw [Nat.sub_sub]

private theorem Fusion.A_orbits_card (B : SpBranch hC) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d) (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (hF : Nat.card F = 2 ^ B.f) :
    Nat.card (Quotient (Fusion.A_setoid (D := D) (hC := hC))) = 2 ^ B.f - 1 := by
  have hL := Fusion.isHypLineSpace B
  obtain ⟨w₁, w₂, hw₁, hwd₁, hℓ₁, hw₂, hwd₂, hℓ₂⟩ := Fusion.two_lines B
  obtain ⟨hdH, -, -, -⟩ := twelveTen_sp_center hC B.hMZ B.hs B.hn B.hf B.hSp
  let f₁ := Fusion.pair_map (hC := hC) hL hw₁ hwd₁ hdH
  let f₂ := Fusion.pair_map (hC := hC) hL hw₂ hwd₂ hdH
  have hinj₁ := Fusion.pair_map_injective B hL hw₁ hwd₁ hdH
  have hinj₂ := Fusion.pair_map_injective B hL hw₂ hwd₂ hdH
  have hdisj := Fusion.pair_ranges_disjoint B hL hw₁ hwd₁ hw₂ hwd₂ hℓ₁ hℓ₂ hdH
  have hcard₁ := Fusion.card_pairs_plus (B := B) hL hw₁ hwd₁ hℓ₁
  have hcard₂ := Fusion.card_pairs_minus (B := B) hL hw₂ hwd₂ hℓ₂
  have hAle : 2 ^ B.f - 1 ≤
      Nat.card (Quotient (Fusion.A_setoid (D := D) (hC := hC))) := by
    have hrange₁ := Set.ncard_range_of_injective hinj₁
    have hrange₂ := Set.ncard_range_of_injective hinj₂
    have hunion := Set.ncard_union_eq hdisj
    have hle := Set.ncard_le_ncard
      (Set.subset_univ (Set.range f₁ ∪ Set.range f₂)) (Set.toFinite _)
    rw [Set.ncard_univ] at hle
    have hsum : (Set.range f₁ ∪ Set.range f₂).ncard = 2 ^ B.f - 1 := by
      rw [hunion, hrange₁, hrange₂]
      omega
    rwa [hsum] at hle
  have hRcard := Fusion.card_R_orbits (B := B) hF g hv cv
  have hsurj := Fusion.R_to_A_map_surjective (B := B) g hv
  have hQAle : Nat.card (Quotient (Fusion.A_setoid (D := D) (hC := hC))) ≤
      Nat.card (Quotient (Fusion.R_setoid (D := D) (hC := hC) g)) :=
    Nat.card_le_card_of_surjective _ hsurj
  have hQAle' : Nat.card (Quotient (Fusion.A_setoid (D := D) (hC := hC))) ≤
      2 ^ B.f - 1 := by
    rw [← hRcard]
    exact hQAle
  exact le_antisymm hQAle' hAle

private theorem exists_mem_inf_centralizer_conj_eq_of_mem_Halpha
    (hF : Nat.card F = 2 ^ B.f) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d) (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    {x x' : G} (hx : x ∈ commSet D (hC.conj g).d)
    (hx' : x' ∈ commSet D (hC.conj g).d) (hxd : ¬ Commute x hC.d)
    {h : G} (hh : h ∈ Halpha D hC.alpha) (hhx : h * x * h⁻¹ = x') :
    ∃ r ∈ Halpha D hC.alpha ⊓ Subgroup.centralizer {(hC.conj g).d}, r * x * r⁻¹ = x' := by
  have hxd' : ¬ Commute x' hC.d := by
    intro hc
    have hfixd : h * hC.d * h⁻¹ = hC.d := Fusion.mul_d_mul_inv_eq (hα := B.hα) hh
    have h1 : Commute (h * x * h⁻¹) (h * hC.d * h⁻¹) := by
      rw [← hhx] at hc
      rwa [← hfixd] at hc
    exact hxd ((Commute.conj_iff h).mp h1)
  have hQAeq : Nat.card (Quotient (Fusion.A_setoid (D := D) (hC := hC))) =
      2 ^ B.f - 1 := Fusion.A_orbits_card (B := B) g hv cv hF
  have hRcard := Fusion.card_R_orbits (B := B) hF g hv cv
  have hsurj := Fusion.R_to_A_map_surjective (B := B) g hv
  have hcard : Nat.card (Quotient (Fusion.R_setoid (D := D) (hC := hC) g)) ≤
      Nat.card (Quotient (Fusion.A_setoid (D := D) (hC := hC))) := by
    rw [hRcard, hQAeq]
  let xS : ↥(Fusion.S (D := D) (hC := hC) g) :=
    ⟨x, (Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mpr ⟨hx, hxd⟩⟩
  let xS' : ↥(Fusion.S (D := D) (hC := hC) g) :=
    ⟨x', (Fusion.mem_S_iff (D := D) (hC := hC) (g := g)).mpr ⟨hx', hxd'⟩⟩
  have hHrel : ∃ a ∈ Halpha D hC.alpha, (xS' : G) = a⁻¹ * (xS : G) * a := by
    refine ⟨h⁻¹, (Halpha D hC.alpha).inv_mem hh, ?_⟩
    rw [inv_inv]
    exact hhx.symm
  obtain ⟨r, hrR, hrrel⟩ :=
    CFSG.Quasithin.Loc442Q.OrbSet.map_injective_of_surjective
      (A := Fusion.R (D := D) (hC := hC) g)
      (A' := Halpha D hC.alpha)
      (S := Fusion.S (D := D) (hC := hC) g)
      (S' := Fusion.A (D := D) (hC := hC))
      (Fusion.R_le_Halpha (D := D) (hC := hC) g)
      (Fusion.S_subset_A (D := D) (hC := hC) g)
      hsurj hcard xS xS' hHrel
  let r' : ↥(Fusion.R (D := D) (hC := hC) g) :=
    ⟨r⁻¹, (Fusion.R (D := D) (hC := hC) g).inv_mem hrR⟩
  have hrxy : (r' : G) * x * (r' : G)⁻¹ = x' := by
    change r⁻¹ * x * (r⁻¹)⁻¹ = x'
    rw [inv_inv]
    exact hrrel.symm
  refine ⟨(r' : G), r'.2, ?_⟩
  simpa using hrxy

theorem spForm_eq_of_conj_eq (hF : Nat.card F = 2 ^ B.f) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d) (cv : SpChart (hC.conj g) (B.conj g).hα k F) {x x' : G}
    (hx : x ∈ commSet D (hC.conj g).d) (hx' : x' ∈ commSet D (hC.conj g).d)
    {h : G} (hh : h ∈ Halpha D hC.alpha) (hhx : h * x * h⁻¹ = x') :
    spForm k F (cv.vec hC.d) (cv.vec x) =
      spForm k F (cv.vec hC.d) (cv.vec x') := by
  classical
  have hdv : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  by_cases hxd : Commute x hC.d
  · have hfixd : h * hC.d * h⁻¹ = hC.d := Fusion.mul_d_mul_inv_eq (hα := B.hα) hh
    have hxd' : Commute x' hC.d := by
      have h1 : Commute (h * x * h⁻¹) (h * hC.d * h⁻¹) :=
        (Commute.conj_iff h).mpr hxd
      rwa [hfixd, hhx] at h1
    have hβx : spForm k F (cv.vec hC.d) (cv.vec x) = 0 := by
      have h := (cv.commute_iff x hx hC.d hdv).mp hxd
      rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
    have hβx' : spForm k F (cv.vec hC.d) (cv.vec x') = 0 := by
      have h := (cv.commute_iff x' hx' hC.d hdv).mp hxd'
      rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
    rw [hβx, hβx']
  · obtain ⟨r, hrR, hrxy⟩ :=
      exists_mem_inf_centralizer_conj_eq_of_mem_Halpha (B := B) hF g hv cv hx hx' hxd hh hhx
    rw [← hrxy]
    exact (Fusion.beta_invariant (B := B) g hv cv ⟨r, hrR⟩ hx).symm

section LinearAlgebra

variable {V : Type} [AddCommGroup V] [Module F V]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem Lines.apply_smul_add_smul {B : LinearMap.BilinForm F V} (hB : B.IsAlt) {a b : V}
    {lam : F} (hab : B a b = lam) (s t : F) :
    B a (s • a + t • b) = t * lam ∧ B b (s • a + t • b) = -s * lam := by
  have hba : B b a = -lam := by rw [(hB.neg_eq a b).symm, hab]
  simp only [map_add, map_smul, smul_eq_mul, hB.self_eq_zero, hab, hba]
  constructor <;> ring

section FiniteDimensional

variable [FiniteDimensional F V]

omit [FiniteDimensional F V] [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem Lines.mem_span_singleton_of_form_eq_zero {B : LinearMap.BilinForm F V}
    (hB : B.IsAlt) {a b x u : V} (hab : B a b ≠ 0)
    (hu : u ∈ Submodule.span F ({a, b} : Set V)) (hx : x ∈ Submodule.span F ({a, b} : Set V))
    (hu0 : u ≠ 0) (hxu : B u x = 0) : x ∈ Submodule.span F ({u} : Set V) := by
  classical
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hu
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hx
  have hkey : s * β = t * α := by
    have hBa : B a (α • a + β • b) = β * B a b :=
      (Lines.apply_smul_add_smul hB rfl α β).1
    have hBb : B b (α • a + β • b) = -α * B a b :=
      (Lines.apply_smul_add_smul hB rfl α β).2
    have h1 : B (s • a + t • b) (α • a + β • b) = (s * β - t * α) * B a b := by
      calc B (s • a + t • b) (α • a + β • b)
          = s * B a (α • a + β • b) + t * B b (α • a + β • b) := by
            simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
              smul_eq_mul]
            ring
        _ = (s * β - t * α) * B a b := by rw [hBa, hBb]; ring
    rw [h1] at hxu
    exact sub_eq_zero.mp ((mul_eq_zero.mp hxu).resolve_right hab)
  rcases eq_or_ne s 0 with hs0 | hs
  · have ht0 : t ≠ 0 := by
      intro ht0
      apply hu0
      rw [hs0, ht0, zero_smul, zero_smul, add_zero]
    have hα0 : α = 0 := by
      have h1 : t * α = 0 := by
        rw [← hkey, hs0, zero_mul]
      exact (mul_eq_zero.mp h1).resolve_left ht0
    refine Submodule.mem_span_singleton.mpr ⟨β * t⁻¹, ?_⟩
    rw [hs0, hα0]
    simp only [zero_smul, zero_add]
    rw [smul_smul]
    have h1 : β * t⁻¹ * t = β := by field_simp
    rw [h1]
  · have hβ : β = t * α * s⁻¹ := by
      calc β = s⁻¹ * (s * β) := (inv_mul_cancel_left₀ hs β).symm
        _ = s⁻¹ * (t * α) := by rw [hkey]
        _ = t * α * s⁻¹ := by ring
    refine Submodule.mem_span_singleton.mpr ⟨α * s⁻¹, ?_⟩
    rw [hβ, smul_add, smul_smul, smul_smul]
    have h1 : α * s⁻¹ * s = α := by field_simp
    have h2 : α * s⁻¹ * t = t * α * s⁻¹ := by ring
    rw [h1, h2]

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem Lines.maps_span_pair_of_isometry {B : LinearMap.BilinForm F V}
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {a b : V}
    {f : Module.End F V} (hf : ∀ x y, B (f x) (f y) = B x y)
    (hfix : ∀ y ∈ B.orthogonal (Submodule.span F ({a, b} : Set V)), f y = y) :
    ∀ x ∈ Submodule.span F ({a, b} : Set V),
      f x ∈ Submodule.span F ({a, b} : Set V) := by
  intro x hx
  have hmem : f x ∈ B.orthogonal (B.orthogonal (Submodule.span F ({a, b} : Set V))) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hxy : B x y = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) x hx
    calc B y (f x) = B (f y) (f x) := by rw [hfix y hy]
      _ = B y x := hf y x
      _ = 0 := by rw [(hB.neg_eq x y).symm, hxy, neg_zero]
  rwa [LinearMap.BilinForm.orthogonal_orthogonal hBn hB.isRefl] at hmem

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem Lines.sub_one_maps_span_pair_into_span_singleton
    {B : LinearMap.BilinForm F V}
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {a b u : V} (hab : B a b ≠ 0)
    (hu : u ∈ Submodule.span F ({a, b} : Set V)) (hu0 : u ≠ 0)
    {f : Module.End F V} (hf : ∀ x y, B (f x) (f y) = B x y)
    (hfix : ∀ y ∈ B.orthogonal (Submodule.span F ({a, b} : Set V)), f y = y)
    (hfu : f u = u) :
    ∀ x ∈ Submodule.span F ({a, b} : Set V),
      (f - 1) x ∈ Submodule.span F ({u} : Set V) := by
  set P : Submodule F V := Submodule.span F ({a, b} : Set V)
  set W : Submodule F V := B.orthogonal P
  have hcompl : IsCompl P W :=
    CFSG.ClassicalGroups.Alternating.isCompl_span_pair_orthogonal (BN := B) hB hab
  have hfP := Lines.maps_span_pair_of_isometry (B := B) hB hBn hf hfix
  have hNapp : ∀ x, (f - 1) x = f x - x := fun x => rfl
  have hNW : ∀ y ∈ W, (f - 1) y = 0 := by
    intro y hy
    rw [hNapp, hfix y hy, sub_self]
  intro x hx
  have hx' : x ∈ P ⊔ W := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hx'
  have hxP : (f - 1) x = (f - 1) p := by
    rw [← hpw, map_add, hNW w hw, add_zero]
  have hsub : (f - 1) p ∈ P := Submodule.sub_mem _ (hfP p hp) hp
  have horth : B u ((f - 1) p) = 0 := by
    have h1 : B u (f p) = B u p := by
      have h2 := hf u p
      rwa [hfu] at h2
    rw [hNapp, map_sub, h1, sub_self]
  rw [hxP]
  exact Lines.mem_span_singleton_of_form_eq_zero hB hab hu hsub hu0 horth

omit [FiniteDimensional F V] [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem Lines.sub_one_mul_self_eq_zero {f : Module.End F V}
    {P W : Submodule F V} (hcompl : IsCompl P W) {u : V} (hfu : f u = u)
    (hNW : ∀ y ∈ W, (f - 1) y = 0)
    (hNPspan : ∀ x ∈ P, (f - 1) x ∈ Submodule.span F ({u} : Set V)) :
    (f - 1) * (f - 1) = 0 := by
  have hNapp : ∀ x, (f - 1) x = f x - x := fun x => rfl
  have hNzero : ∀ z ∈ Submodule.span F ({u} : Set V), (f - 1) z = 0 := by
    intro z hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    rw [← hc, map_smul, hNapp, hfu, sub_self, smul_zero]
  ext x
  have hx : x ∈ P ⊔ W := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp hx
  have h1 : (f - 1) x = (f - 1) p := by
    rw [← hpw, map_add, hNW w hw, add_zero]
  have h2 : (f - 1) p ∈ Submodule.span F ({u} : Set V) := hNPspan p hp
  rw [Module.End.mul_apply, h1]
  exact hNzero ((f - 1) p) h2

omit [Fintype F] [DecidableEq F] in
private theorem Lines.mul_self_eq_one_of_fix_plane {B : LinearMap.BilinForm F V}
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {a b u : V} (hab : B a b ≠ 0)
    (hu : u ∈ Submodule.span F ({a, b} : Set V)) (hu0 : u ≠ 0)
    {f : Module.End F V} (hf : ∀ x y, B (f x) (f y) = B x y)
    (hfix : ∀ y ∈ B.orthogonal (Submodule.span F ({a, b} : Set V)), f y = y)
    (hfu : f u = u) : f * f = 1 := by
  classical
  set P : Submodule F V := Submodule.span F ({a, b} : Set V) with hP
  set W : Submodule F V := B.orthogonal P with hW
  have hcompl : IsCompl P W :=
    CFSG.ClassicalGroups.Alternating.isCompl_span_pair_orthogonal (BN := B) hB hab
  have hfP := Lines.maps_span_pair_of_isometry (B := B) hB hBn hf hfix
  set N : Module.End F V := f - 1 with hN
  have hNapp : ∀ x, N x = f x - x := fun x => rfl
  have hNW : ∀ y ∈ W, N y = 0 := by
    intro y hy
    rw [hNapp, hfix y hy, sub_self]
  have hNPspan :=
    Lines.sub_one_maps_span_pair_into_span_singleton (B := B) hB hBn hab hu hu0 hf hfix hfu
  have hNN : N * N = 0 := Lines.sub_one_mul_self_eq_zero hcompl hfu hNW hNPspan
  have hdecomp : f = 1 + N := by
    rw [hN]
    abel
  have h2N : N + N = 0 := by
    have h2 : (2 : F) = 0 := by
      rw [show (2 : F) = 1 + 1 by norm_num, CharTwo.add_self_eq_zero]
    calc N + N = (1 + 1 : F) • N := by rw [add_smul, one_smul]
      _ = (2 : F) • N := by norm_num
      _ = 0 := by rw [h2, zero_smul]
  have hff : f * f = 1 := by
    conv_lhs => rw [hdecomp]
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, hNN, add_zero, one_mul]
    rw [add_assoc, h2N, add_zero]
  exact hff

end FiniteDimensional

end LinearAlgebra

private theorem exists_form_ne_zero_spForm_ne_zero {Q : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQpol : ∀ a b, polar Q a b = spForm k F a b) (hq : 3 ≤ Nat.card F)
    {u : Fin k ⊕ Fin k → F} (hu0 : u ≠ 0) (huQ : Q u = 1) :
    ∃ x, Q x ≠ 0 ∧ spForm k F u x ≠ 0 := by
  have hQadd : ∀ x y : Fin k ⊕ Fin k → F, Q (x + y) = Q x + Q y + spForm k F x y := by
    intro x y
    rw [QuadraticMap.map_add Q, hQpol]
  have hQsmul : ∀ (cc : F) (x : Fin k ⊕ Fin k → F), Q (cc • x) = cc ^ 2 * Q x := by
    intro cc x
    rw [QuadraticMap.map_smul Q, smul_eq_mul]
    ring
  obtain ⟨m, hm⟩ : ∃ m : Fin k ⊕ Fin k → F, spForm k F u m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (spForm_nondegenerate.1 u hcon)
  set m' : Fin k ⊕ Fin k → F := (spForm k F u m)⁻¹ • m with hm'def
  have hm' : spForm k F u m' = 1 := by
    rw [hm'def, map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hm
  obtain ⟨t₀, ht₀0, ht₀1⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_ne_zero_ne_one_of_two_lt_card hq
  by_cases hQm : Q m' = 0
  · refine ⟨u + t₀ • m', ?_, ?_⟩
    · have h1 : Q (u + t₀ • m') = 1 + t₀ := by
        rw [hQadd, hQsmul, hQm, huQ]
        rw [map_smul, smul_eq_mul, hm', mul_one, mul_zero, add_zero]
      rw [h1]
      intro h0
      apply ht₀1
      have h0' : t₀ + 1 = 0 := by rw [add_comm]; exact h0
      have h3 : t₀ = -1 := eq_neg_of_add_eq_zero_left h0'
      rwa [CharTwo.neg_eq] at h3
    · rw [map_add, map_smul, smul_eq_mul, hm', spForm_self, mul_one, zero_add]
      exact ht₀0
  · exact ⟨m', hQm, by rw [hm']; exact one_ne_zero⟩

omit [Finite G] [DecidableEq F] in
private theorem exists_mem_commSet_form_eq_one_spForm_ne_zero
    (c : SpChart hC B.hα k F) {w v : G}
    (Q : QuadraticForm F (Fin k ⊕ Fin k → F))
    (hQw : ∀ z, z ∈ commSet D hC.d → (z ∈ commSet D w ↔ Q (c.vec z) = 1))
    {u : Fin k ⊕ Fin k → F} (huQ : Q u ≠ 0) (huB : spForm k F (c.vec v) u ≠ 0) :
    ∃ z : G, z ∈ commSet D hC.d ∧ z ∈ commSet D w ∧
      spForm k F (c.vec v) (c.vec z) ≠ 0 := by
  have hQsmul : ∀ (cc : F) (x : Fin k ⊕ Fin k → F), Q (cc • x) = cc ^ 2 * Q x := by
    intro cc x
    rw [QuadraticMap.map_smul Q, smul_eq_mul]
    ring
  obtain ⟨mu, hmu⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (Q u)⁻¹
  have hmu0 : mu ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmu
    exact inv_ne_zero huQ hmu
  have huQ1 : Q (mu • u) = 1 := by
    rw [hQsmul, pow_two, ← hmu]
    exact inv_mul_cancel₀ huQ
  have huB1 : spForm k F (c.vec v) (mu • u) ≠ 0 := by
    rw [map_smul, smul_eq_mul]
    exact mul_ne_zero hmu0 huB
  have hune : mu • u ≠ 0 := by
    intro h0
    exact huB1 (by rw [h0, map_zero])
  obtain ⟨z, hz, hzv⟩ := c.exists_vec (mu • u) hune
  refine ⟨z, hz, ?_, ?_⟩
  · exact (hQw z hz).mpr (by rw [hzv]; exact huQ1)
  · rw [hzv]; exact huB1

private theorem notMem_lineMem_of_common (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {w v : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hvd : v ∈ commSet D hC.d) (hvw : v ∈ commSet D w) :
    v ∉ lineMem D hC.d w := by
  intro hvmem
  obtain ⟨Q, hQpol, hQw, -⟩ := exists_quadraticForm_commSet_inter (hIH := B.hIH) (hC := hC)
    (hMZ := B.hMZ) (hα := B.hα) (hs := B.hs) (hn := B.hn) (hf := B.hf) (hSp := B.hSp)
    (c := c) (hnk := hnk) (hF := hF) (hv := hvd) (hw := hw) (hwd := hwd) (hwv := hvw.2.1.symm)
  have hu0 : c.vec v ≠ 0 := c.vec_ne_zero v hvd
  have hu0Q : Q (c.vec v) = 1 := (hQw v hvd).mp hvw
  obtain ⟨u, huQ, huB⟩ :=
    exists_form_ne_zero_spForm_ne_zero hQpol (B.two_lt_card hF) hu0 hu0Q
  obtain ⟨z, hz, hzw, hzB⟩ :=
    exists_mem_commSet_form_eq_one_spForm_ne_zero (B := B) c Q hQw huQ huB
  have hzne : ¬ Commute v z := by
    intro hc
    have h1 : spForm k F (c.vec v) (c.vec z) = 0 := (c.commute_iff v hvd z hz).mp hc
    exact hzB h1
  have hsub := (mem_lineMem.mp hvmem).2
  have hzmem : z ∈ perpMem D hC.d ∩ perpMem D w :=
    ⟨mem_perpMem.mpr ⟨hz.1, hz.2.1⟩, mem_perpMem.mpr ⟨hzw.1, hzw.2.1⟩⟩
  have hzv : Commute z v := (mem_perpMem.mp (hsub hzmem)).2
  exact hzne hzv.symm

omit [Finite G] in
private theorem lineMem_subset_commSet {w v : G} (hvd : v ∈ commSet D hC.d)
    (hvw : v ∈ commSet D w) (hvdℓ : v ∉ lineMem D hC.d w) :
    ∀ x ∈ lineMem D hC.d w, x ∈ commSet D v := by
  intro x hx
  have hxsub := (mem_lineMem.mp hx).2
  have hxv : Commute v x := (mem_perpMem.mp (hxsub
    ⟨mem_perpMem.mpr ⟨hvd.1, hvd.2.1⟩, mem_perpMem.mpr ⟨hvw.1, hvw.2.1⟩⟩)).2
  exact ⟨(mem_lineMem.mp hx).1, hxv.symm, fun h0 => hvdℓ (h0 ▸ hx)⟩

omit [Fintype F] in
private theorem vec_mem_plane_of_mem_line {g v w : G}
    (hgv : (hC.conj g).d = v) (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    (hdv : hC.d ∈ commSet D v) (hwv : w ∈ commSet D v)
    (hℓDv : ∀ x ∈ lineMem D hC.d w, x ∈ commSet D v)
    (hhab : spForm k F (cv.vec hC.d) (cv.vec w) ≠ 0) {x : G}
    (hx : x ∈ lineMem D hC.d w) :
    cv.vec x ∈ Submodule.span F {cv.vec hC.d, cv.vec w} := by
  subst hgv
  suffices hmem : cv.vec x ∈ (spForm k F).orthogonal
      ((spForm k F).orthogonal (Submodule.span F {cv.vec hC.d, cv.vec w})) by
    rwa [LinearMap.BilinForm.orthogonal_orthogonal spForm_nondegenerate spForm_isAlt.isRefl]
      at hmem
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  have hyab : spForm k F (cv.vec hC.d) y = 0 ∧ spForm k F (cv.vec w) y = 0 :=
    (CFSG.ClassicalGroups.Alternating.mem_orthogonal_span_pair (BN := spForm k F)).mp hy
  by_cases hy0 : y = 0
  · rw [hy0]
    simp
  · obtain ⟨z, hz, hzv⟩ := cv.exists_vec y hy0
    have hzd : z ∈ commSet D hC.d := by
      refine ⟨hz.1, ?_, ?_⟩
      · refine (cv.commute_iff z hz hC.d hdv).mpr ?_
        rw [hzv, CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
        exact hyab.1
      · intro hzd
        apply hhab
        have h1 : y = cv.vec hC.d := by rw [← hzv, hzd]
        have h2 : spForm k F (cv.vec w) (cv.vec hC.d) = 0 := by rw [← h1]; exact hyab.2
        rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt] at h2
    have hzw : z ∈ commSet D w := by
      refine ⟨hz.1, ?_, ?_⟩
      · refine (cv.commute_iff z hz w hwv).mpr ?_
        rw [hzv, CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
        exact hyab.2
      · intro hzw
        apply hhab
        have h1 : y = cv.vec w := by rw [← hzv, hzw]
        rw [← h1]
        exact hyab.1
    have hxcomm : Commute x z := (mem_perpMem.mp ((mem_lineMem.mp hx).2
      ⟨mem_perpMem.mpr ⟨hzd.1, hzd.2.1⟩, mem_perpMem.mpr ⟨hzw.1, hzw.2.1⟩⟩)).2.symm
    have h1 : spForm k F (cv.vec x) (cv.vec z) = 0 :=
      (cv.commute_iff x (hℓDv x hx) z hz).mp hxcomm
    have h2 : spForm k F (cv.vec x) y = 0 := by rw [← hzv]; exact h1
    rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt] at h2

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem orderOf_mul_dvd_ncard_lineMem_radical
    (hC : HypothesisC D) {g v : G} (hgv : (hC.conj g).d = v)
    (Bconj : SpBranch (hC.conj g))
    (hvd : v ∈ commSet D hC.d) {cv : SpChart (hC.conj g) Bconj.hα k F}
    {t : G} {n : ℕ} {htnHv : t ^ n ∈ Halpha D (hC.conj g).alpha}
    (hρ1 : cv.ρ ⟨t ^ n, htnHv⟩ = 1) (hodd : Odd (orderOf t)) :
    t ^ n = 1 := by
  classical
  obtain ⟨hu₀, -, -, -⟩ := twelveTen_sp_center (hC := hC.conj g) Bconj.hMZ
    Bconj.hs Bconj.hn Bconj.hf Bconj.hSp
  have hker : (⟨t ^ n, htnHv⟩ : Halpha D (hC.conj g).alpha) ∈ cv.ρ.ker := by
    rw [MonoidHom.mem_ker]; exact hρ1
  have hzpow : (⟨t ^ n, htnHv⟩ : Halpha D (hC.conj g).alpha) ∈
      Subgroup.zpowers ⟨(hC.conj g).d, hu₀⟩ := by
    rw [← cv.ker_eq_zpowers Bconj hu₀]
    exact hker
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzpow
  have hval : t ^ n = ((hC.conj g).d) ^ j := by
    have h1 := congrArg (fun z : Halpha D (hC.conj g).alpha => (z : G)) hj
    simpa using h1.symm
  rw [hgv] at hval
  have hv2 : v * v = 1 := hC.setup.oddT.mul_self_eq_one hvd.1
  have hsq2 : (t ^ n) ^ 2 = 1 := by
    rw [pow_two, hval, ← zpow_add]
    have h2j : j + j = (2 : ℤ) * j := by ring
    rw [h2j, zpow_mul]
    have hv2' : v ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hv2]
    rw [hv2', one_zpow]
  rw [pow_two] at hsq2
  exact CFSG.Timmesfeld.Bridge.OddTransp.eq_one_of_mul_self_of_odd hsq2
    (Odd.of_dvd_nat hodd (orderOf_pow_dvd n))

omit [Fintype F] [DecidableEq F] in
private theorem orderOf_mul_dvd_ncard_lineMem_inv
    {w : G}
    {g : G}
    {cv : SpChart (hC.conj g) (B.conj g).hα k F}
    {t : G} {n : ℕ}
    {htnHv : t ^ n ∈ Halpha D (hC.conj g).alpha}
    {x : G} (hfix : t ^ n * x * (t ^ n)⁻¹ = x)
    (hxcvH : x ∈ commSet D (hC.conj g).d)
    (hxvec : cv.vec x ∈ Submodule.span F {cv.vec hC.d, cv.vec w})
    (hxne : cv.vec x ≠ 0)
    (hab : spForm k F (cv.vec hC.d) (cv.vec w) ≠ 0)
    (hfixW : ∀ y : Fin k ⊕ Fin k → F, y ∈ (spForm k F).orthogonal
      (Submodule.span F {cv.vec hC.d, cv.vec w}) →
      spEnd (cv.ρ ⟨t ^ n, htnHv⟩) y = y)
    (hodd : Odd (orderOf t)) :
    cv.ρ ⟨t ^ n, htnHv⟩ = 1 := by
  classical
  have hvec : spEnd (cv.ρ ⟨t ^ n, htnHv⟩) (cv.vec x) = cv.vec x := by
    have h1 := (cv.vec_conj ⟨t ^ n, htnHv⟩ hxcvH).2
    rw [hfix] at h1
    exact h1.symm
  have hiso : ∀ p q : Fin k ⊕ Fin k → F,
      spForm k F (spEnd (cv.ρ ⟨t ^ n, htnHv⟩) p) (spEnd (cv.ρ ⟨t ^ n, htnHv⟩) q) =
        spForm k F p q := by
    intro p q
    exact CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup.mp
      (spLin_mem (cv.ρ ⟨t ^ n, htnHv⟩)) p q
  have hsq : cv.ρ ⟨t ^ n, htnHv⟩ ^ 2 = 1 := by
    apply CFSG.RankThree.PartOne.KCSpComm.eq_of_spEnd_eq
    intro y
    rw [pow_two, spEnd_mul, spEnd_one]
    exact congrArg (fun f => f y) (Lines.mul_self_eq_one_of_fix_plane (B := spForm k F)
      spForm_isAlt spForm_nondegenerate hab hxvec hxne hiso hfixW hvec)
  have hoddρ : Odd (orderOf (cv.ρ ⟨t ^ n, htnHv⟩)) := by
    have h1 : Odd (orderOf (t ^ n)) := Odd.of_dvd_nat hodd (orderOf_pow_dvd n)
    refine Odd.of_dvd_nat h1 ?_
    have h3 : orderOf (cv.ρ ⟨t ^ n, htnHv⟩) ∣
        orderOf (⟨t ^ n, htnHv⟩ : Halpha D (hC.conj g).alpha) :=
      orderOf_map_dvd cv.ρ ⟨t ^ n, htnHv⟩
    rwa [← Subgroup.orderOf_coe ⟨t ^ n, htnHv⟩] at h3
  rw [pow_two] at hsq
  exact CFSG.Timmesfeld.Bridge.OddTransp.eq_one_of_mul_self_of_odd hsq hoddρ

omit [Finite G] in
private theorem orderOf_mul_dvd_ncard_lineMem_act {t w : G} {ℓ : Set G}
    (ht : t = hC.d * w) (hℓ : ℓ = lineMem D hC.d w) :
    ∀ (i : ℤ) {x : G}, x ∈ ℓ → t ^ i * x * (t ^ i)⁻¹ ∈ ℓ := by
  intro i x hx
  rw [hℓ] at hx ⊢
  have hxD : x ∈ D := (mem_lineMem.mp hx).1
  refine mem_lineMem.mpr ⟨hC.setup.normal (t ^ i) x hxD, ?_⟩
  intro z hz
  have hzd : Commute z hC.d := (mem_perpMem.mp hz.1).2
  have hzw : Commute z w := (mem_perpMem.mp hz.2).2
  have hzt : Commute z t := by rw [ht]; exact hzd.mul_right hzw
  have hzti : Commute z (t ^ i) := hzt.zpow_right i
  have hxz : Commute x z := ((mem_lineMem.mp hx).2 hz).2.symm
  refine mem_perpMem.mpr ⟨(mem_perpMem.mp hz.1).1, ?_⟩
  show z * (t ^ i * x * (t ^ i)⁻¹) = (t ^ i * x * (t ^ i)⁻¹) * z
  have hzi : z * (t ^ i) = (t ^ i) * z := hzti.eq
  calc z * (t ^ i * x * (t ^ i)⁻¹)
      = (z * (t ^ i)) * x * (t ^ i)⁻¹ := by group
    _ = ((t ^ i) * z) * x * (t ^ i)⁻¹ := by rw [hzi]
    _ = (t ^ i) * (z * x) * (t ^ i)⁻¹ := by group
    _ = (t ^ i) * (x * z) * (t ^ i)⁻¹ := by rw [← hxz.eq]
    _ = (t ^ i) * x * (z * (t ^ i)⁻¹) := by group
    _ = (t ^ i) * x * ((t ^ i)⁻¹ * z) := by rw [← hzti.inv_right.eq]
    _ = (t ^ i * x * (t ^ i)⁻¹) * z := by group

private theorem orderOf_mul_dvd_ncard_lineMem_orbit (t : G) (ℓ : Set G)
    (hactz : ∀ (i : ℤ) {x : G}, x ∈ ℓ → t ^ i * x * (t ^ i)⁻¹ ∈ ℓ)
    (hsem : ∀ (n : ℕ) {x : G}, x ∈ ℓ → t ^ n * x * (t ^ n)⁻¹ = x → t ^ n = 1) :
    orderOf t ∣ ℓ.ncard := by
  have hsemz : ∀ (i : ℤ) {x : G}, x ∈ ℓ → t ^ i * x * (t ^ i)⁻¹ = x → t ^ i = 1 := by
    intro i x hx hfix
    rcases Int.eq_nat_or_neg i with ⟨n, hn | hn⟩
    · rw [hn] at hfix ⊢
      rw [zpow_natCast] at hfix ⊢
      exact hsem n hx hfix
    · rw [hn] at hfix ⊢
      rw [zpow_neg, zpow_natCast]
      have h3 : t ^ n * x * (t ^ n)⁻¹ = x := by
        have h4 := congrArg (fun z => t ^ n * z * (t ^ n)⁻¹) hfix
        simpa [mul_assoc] using h4.symm
      rw [hsem n hx h3, inv_one]
  have hX : ∀ u ∈ ℓ, ∀ h ∈ Subgroup.zpowers t, h * u * h⁻¹ ∈ ℓ := by
    intro u hu h hh
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [show h = t ^ i from hi.symm]
    exact hactz i hu
  have hfree : ∀ u ∈ ℓ, ∀ h ∈ Subgroup.zpowers t, h * u = u * h → h = 1 := by
    intro u hu h hh hcomm
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hfix : t ^ i * u * (t ^ i)⁻¹ = u := by
      have h1 : h * u * h⁻¹ = u := by rw [hcomm, mul_inv_cancel_right]
      rwa [show h = t ^ i from hi.symm] at h1
    have hti : t ^ i = 1 := hsemz i hu hfix
    rw [show h = t ^ i from hi.symm, hti]
  have hdvd := CFSG.Walter.J1.card_dvd_ncard_of_free
    (H := Subgroup.zpowers t) (X := ℓ) hX hfree
  rwa [Nat.card_zpowers] at hdvd

omit [Fintype F] [DecidableEq F] in
private theorem orderOf_mul_dvd_ncard_lineMem_fixW (t : G) {w : G} (ht : t = hC.d * w)
    {g : G} (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    {a b : Fin k ⊕ Fin k → F} (ha : cv.vec hC.d = a) (hb : cv.vec w = b)
    {P : Submodule F (Fin k ⊕ Fin k → F)}
    (horth : ∀ y : Fin k ⊕ Fin k → F,
      y ∈ (spForm k F).orthogonal P ↔ spForm k F a y = 0 ∧ spForm k F b y = 0)
    (hdvH : hC.d ∈ commSet D (hC.conj g).d)
    (hwvH : w ∈ commSet D (hC.conj g).d)
    (htHv : t ∈ Halpha D (hC.conj g).alpha)
    (hdHv : hC.d ∈ Halpha D (hC.conj g).alpha)
    (hwHv : w ∈ Halpha D (hC.conj g).alpha)
    {n : ℕ} (htnHv : t ^ n ∈ Halpha D (hC.conj g).alpha) :
    ∀ y : Fin k ⊕ Fin k → F, y ∈ (spForm k F).orthogonal P →
      spEnd (cv.ρ ⟨t ^ n, htnHv⟩) y = y := by
  intro y hy
  have hρt : cv.ρ ⟨t, htHv⟩ =
      spTransvection (cv.vec hC.d) 1 * spTransvection (cv.vec w) 1 := by
    have h1 : (⟨t, htHv⟩ : Halpha D (hC.conj g).alpha) =
        (⟨hC.d, hdHv⟩ : Halpha D (hC.conj g).alpha) * ⟨w, hwHv⟩ := Subtype.ext ht
    rw [h1, map_mul, cv.map_eq hC.d hdvH, cv.map_eq w hwvH]
  have hstep : ∀ y : Fin k ⊕ Fin k → F, y ∈ (spForm k F).orthogonal P →
      spEnd (cv.ρ ⟨t, htHv⟩) y = y := by
    intro y hy
    have hyab : spForm k F a y = 0 ∧ spForm k F b y = 0 := (horth y).mp hy
    have h1 : spForm k F y b = 0 := by
      rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]; exact hyab.2
    have h2 : spForm k F y a = 0 := by
      rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]; exact hyab.1
    have hy1 : spEnd (spTransvection (cv.vec w) 1) y = y := by
      rw [spEnd_spTransvection, hb, h1]
      simp
    have hy2 : spEnd (spTransvection (cv.vec hC.d) 1) y = y := by
      rw [spEnd_spTransvection, ha, h2]
      simp
    rw [hρt, spEnd_mul, Module.End.mul_apply, hy1, hy2]
  have hpow : cv.ρ ⟨t ^ n, htnHv⟩ = (cv.ρ ⟨t, htHv⟩) ^ n := by
    rw [show (⟨t ^ n, htnHv⟩ : Halpha D (hC.conj g).alpha) =
      (⟨t, htHv⟩ : Halpha D (hC.conj g).alpha) ^ n from Subtype.ext rfl, map_pow]
  rw [hpow]
  have hgen : ∀ m : ℕ, spEnd ((cv.ρ ⟨t, htHv⟩) ^ m) y = y := by
    intro m
    induction m with
    | zero =>
        rw [pow_zero, spEnd_one]
        rfl
    | succ j ih =>
        rw [pow_succ, spEnd_mul, Module.End.mul_apply, hstep y hy, ih]
  exact hgen n

omit [Fintype F] [DecidableEq F] in
private theorem orderOf_mul_dvd_ncard_lineMem_sem (t : G) (ℓ : Set G)
    {w : G} (hw : w ∈ D) (ht : t = hC.d * w) {v : G} (hvd : v ∈ commSet D hC.d)
    (hvw : w ∈ commSet D v) {g : G} (hgv : (hC.conj g).d = v)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F)
    {a b : Fin k ⊕ Fin k → F} (ha : cv.vec hC.d = a) (hb : cv.vec w = b)
    {P : Submodule F (Fin k ⊕ Fin k → F)}
    (horth : ∀ y : Fin k ⊕ Fin k → F,
      y ∈ (spForm k F).orthogonal P ↔ spForm k F a y = 0 ∧ spForm k F b y = 0)
    (hP : P = Submodule.span F {a, b})
    (hab : spForm k F a b ≠ 0)
    (hℓDv : ∀ x, x ∈ lineMem D hC.d w → x ∈ commSet D v)
    (hvecℓ : ∀ x, x ∈ lineMem D hC.d w → cv.vec x ∈ P)
    (htHv : t ∈ Halpha D (hC.conj g).alpha)
    (hdHv : hC.d ∈ Halpha D (hC.conj g).alpha)
    (hwHv : w ∈ Halpha D (hC.conj g).alpha)
    (hodd : Odd (orderOf t)) (hℓ : ℓ = lineMem D hC.d w) :
    ∀ (n : ℕ) {x : G}, x ∈ ℓ → t ^ n * x * (t ^ n)⁻¹ = x → t ^ n = 1 := by
  intro n x hx hfix
  rw [hℓ] at hx
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0; simp
  have hxcv : x ∈ commSet D v := hℓDv x hx
  have hxcvH : x ∈ commSet D (hC.conj g).d := by rw [hgv]; exact hxcv
  have hxvec : cv.vec x ∈ P := hvecℓ x hx
  have hxne : cv.vec x ≠ 0 := cv.vec_ne_zero x hxcvH
  have htnHv : t ^ n ∈ Halpha D (hC.conj g).alpha := Subgroup.pow_mem _ htHv n
  have hdvH : hC.d ∈ commSet D (hC.conj g).d := by
    rw [hgv]
    exact ⟨hC.hd, hvd.2.1.symm, hvd.2.2.symm⟩
  have hwvH : w ∈ commSet D (hC.conj g).d := by
    rw [hgv]
    exact ⟨hw, hvw.2.1, hvw.2.2⟩
  have hfixW : ∀ y : Fin k ⊕ Fin k → F, y ∈ (spForm k F).orthogonal P →
      spEnd (cv.ρ ⟨t ^ n, htnHv⟩) y = y :=
    orderOf_mul_dvd_ncard_lineMem_fixW (B := B) (t := t) (w := w) (g := g) ht cv ha hb horth
      hdvH hwvH htHv hdHv hwHv htnHv
  have hab' : spForm k F (cv.vec hC.d) (cv.vec w) ≠ 0 := by
    simpa [ha, hb] using hab
  have hxvec' : cv.vec x ∈ Submodule.span F {cv.vec hC.d, cv.vec w} := by
    simpa [ha, hb, hP] using hxvec
  have hfixW' : ∀ y : Fin k ⊕ Fin k → F,
      y ∈ (spForm k F).orthogonal (Submodule.span F {cv.vec hC.d, cv.vec w}) →
      spEnd (cv.ρ ⟨t ^ n, htnHv⟩) y = y := by
    intro y hy
    exact hfixW y (by simpa [ha, hb, hP] using hy)
  have hρ1 : cv.ρ ⟨t ^ n, htnHv⟩ = 1 :=
    orderOf_mul_dvd_ncard_lineMem_inv (B := B) (htnHv := htnHv)
      hfix hxcvH hxvec' hxne hab' hfixW' hodd
  exact orderOf_mul_dvd_ncard_lineMem_radical (htnHv := htnHv) hC hgv (B.conj g) hvd hρ1 hodd

private theorem exists_conj_mem_Halpha (B : SpBranch hC) {v w : G}
    (hv : v ∈ commSet D hC.d) (hvw : w ∈ commSet D v) :
    ∃ g : G,
      (hC.conj g).d = v ∧ hC.d ∈ Halpha D (hC.conj g).alpha ∧
        w ∈ Halpha D (hC.conj g).alpha ∧
        hC.d * w ∈ Halpha D (hC.conj g).alpha := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hv.1)
  have hgv : (hC.conj g).d = v := by rw [HypothesisC.conj_d]; exact hg
  have hdvH : hC.d ∈ commSet D (hC.conj g).d := by rw [hgv]; exact mem_commSet_symm hC.hd hv
  have hwvH : w ∈ commSet D (hC.conj g).d := by rw [hgv]; exact hvw
  have hdH := mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hdvH
  have hwH := mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hwvH
  exact ⟨g, hgv, hdH, hwH, Subgroup.mul_mem _ hdH hwH⟩

theorem orderOf_mul_dvd_ncard_lineMem (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d) :
    orderOf (hC.d * w) ∣ (lineMem D hC.d w).ncard := by
  classical
  set t : G := hC.d * w with htdef
  set ℓ : Set G := lineMem D hC.d w with hℓdef
  have hwd' : ¬ Commute hC.d w := fun hc => hwd hc.symm
  have hodd : Odd (orderOf t) := hC.setup.oddT.odd_of_not_commute hC.hd hw hwd'
  obtain ⟨v, hvd, hvw⟩ := B.hdiam hC.d hC.hd w hw hwd'
  have hdv : hC.d ∈ commSet D v := ⟨hC.hd, hvd.2.1.symm, hvd.2.2.symm⟩
  have hwv : w ∈ commSet D v := ⟨hw, hvw.2.1.symm, hvw.2.2.symm⟩
  obtain ⟨g, hgv, hdHv, hwHv, htw⟩ := exists_conj_mem_Halpha (B := B) hvd hwv
  obtain ⟨cv, -⟩ := exists_spChart_conj (hC := hC) (B := B) g c
  have hdvH : hC.d ∈ commSet D (hC.conj g).d := by rw [hgv]; exact hdv
  have hwvH : w ∈ commSet D (hC.conj g).d := by rw [hgv]; exact hwv
  have htHv : t ∈ Halpha D (hC.conj g).alpha := by rw [htdef]; exact htw
  set a : Fin k ⊕ Fin k → F := cv.vec hC.d with hadef
  set b : Fin k ⊕ Fin k → F := cv.vec w with hbdef
  set P : Submodule F (Fin k ⊕ Fin k → F) := Submodule.span F ({a, b} : Set _) with hPdef
  have ha0 : a ≠ 0 := cv.vec_ne_zero hC.d hdvH
  have hb0 : b ≠ 0 := cv.vec_ne_zero w hwvH
  have hab : spForm k F a b ≠ 0 := by
    intro h0
    exact hwd' ((cv.commute_iff hC.d hdvH w hwvH).mpr h0)
  have horth : ∀ y : Fin k ⊕ Fin k → F,
      y ∈ (spForm k F).orthogonal P ↔ spForm k F a y = 0 ∧ spForm k F b y = 0 :=
    fun y => CFSG.ClassicalGroups.Alternating.mem_orthogonal_span_pair (BN := spForm k F)
  have hvdℓ : v ∉ ℓ := by
    rw [hℓdef]
    exact notMem_lineMem_of_common c hnk hF hw hwd hvd hvw
  have hℓDv : ∀ x ∈ ℓ, x ∈ commSet D v := by
    rw [hℓdef]
    exact lineMem_subset_commSet hvd hvw hvdℓ
  have hvecℓ : ∀ x ∈ ℓ, cv.vec x ∈ P := by
    rw [hℓdef]
    intro x hx
    exact vec_mem_plane_of_mem_line (B := B) hgv cv hdv hwv hℓDv hab hx
  have hactz : ∀ (i : ℤ) {x : G}, x ∈ ℓ → t ^ i * x * (t ^ i)⁻¹ ∈ ℓ :=
    orderOf_mul_dvd_ncard_lineMem_act (t := t) (w := w) (ℓ := ℓ) htdef hℓdef
  have ha' := hadef.symm
  have hb' := hbdef.symm
  have hsem : ∀ (n : ℕ) {x : G}, x ∈ ℓ → t ^ n * x * (t ^ n)⁻¹ = x → t ^ n = 1 :=
    orderOf_mul_dvd_ncard_lineMem_sem (B := B) (t := t) (ℓ := ℓ) hw htdef hvd hwv hgv cv
      ha' hb' horth hPdef hab (fun x hx => hℓDv x hx)
      (fun x hx => hvecℓ x hx) htHv hdHv hwHv hodd hℓdef
  have hdvd := orderOf_mul_dvd_ncard_lineMem_orbit t ℓ hactz hsem
  exact hdvd

theorem orderOf_mul_dvd_iff_ncard_lineMem (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {w : G} (hw : w ∈ D) (hwd : ¬ Commute w hC.d) :
    orderOf (hC.d * w) ∣ 2 ^ B.f - 1 ↔ (lineMem D hC.d w).ncard = 2 ^ B.f - 1 := by
  classical
  have hwd' : ¬ Commute hC.d w := fun hc => hwd hc.symm
  have hodd : Odd (orderOf (hC.d * w)) :=
    hC.setup.oddT.odd_of_not_commute hC.hd hw hwd'
  constructor
  · intro hdvd
    have hΓ : (commSet D hC.d ∩ commSet D w).Nonempty :=
      B.hdiam hC.d hC.hd w hw hwd'
    have hsize := (twelveSeven_sp B.hIH hC B.hMZ B.hα B.hs B.hn B.hf B.hSp).1
    rcases hsize w hw hwd hΓ with h | h
    · exfalso
      have hT := orderOf_mul_dvd_ncard_lineMem c hnk hF hw hwd
      rw [h] at hT
      have hg : orderOf (hC.d * w) ∣ 2 := by
        have h1 : orderOf (hC.d * w) ∣
            Nat.gcd (2 ^ B.f - 1) (2 ^ B.f + 1) := Nat.dvd_gcd hdvd hT
        refine h1.trans ?_
        have h2 : 2 ^ B.f + 1 - (2 ^ B.f - 1) = 2 := by
          have h3 : 1 ≤ 2 ^ B.f := Nat.one_le_pow _ _ (by norm_num)
          omega
        have h3 : Nat.gcd (2 ^ B.f - 1) (2 ^ B.f + 1) ∣
            2 ^ B.f + 1 - (2 ^ B.f - 1) :=
          Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
        rwa [h2] at h3
      have hm1 : orderOf (hC.d * w) = 1 := by
        exact hodd.coprime_two_right.eq_one_of_dvd hg
      have hdw : hC.d = w := by
        have h1 : hC.d * w = 1 := orderOf_eq_one_iff.mp hm1
        calc hC.d = hC.d * (w * w) := by rw [hC.setup.oddT.mul_self_eq_one hw, mul_one]
          _ = (hC.d * w) * w := by rw [mul_assoc]
          _ = w := by rw [h1, one_mul]
      rw [hdw] at hwd
      exact hwd (Commute.refl w)
    · exact h
  · intro hncard
    have hT := orderOf_mul_dvd_ncard_lineMem c hnk hF hw hwd
    rwa [hncard] at hT

@[expose] def IsFormOfLine {hα : hC.alpha = {hC.d}} (c : SpChart hC hα k F)
(Q : QuadraticForm F (Fin k ⊕ Fin k → F)) (w : G) : Prop :=
  (∀ a b, polar Q a b = spForm k F a b) ∧
  ∀ z, z ∈ commSet D hC.d → (z ∈ commSet D w ↔ Q (c.vec z) = 1)

omit [Finite G] [DecidableEq F] in
theorem eq_of_isFormOfLine {hα : hC.alpha = {hC.d}} {c : SpChart hC hα k F}
    (hq : 2 < Nat.card F) {x : G} {Q Q' : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ : IsFormOfLine c Q x) (hQ' : IsFormOfLine c Q' x) : Q = Q' := by
  classical
  have hB : polarBilin Q = spForm k F := by
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hQ.1 a b
  have hnd : (polarBilin Q).Nondegenerate := by rw [hB]; exact spForm_nondegenerate
  refine eq_of_polar_eq_of_subset (fun a b => by rw [hQ.1, hQ'.1])
    (span_setOf_eq_one_eq_top hq hnd) ?_
  intro a ha
  by_cases ha0 : a = 0
  · rw [ha0, map_zero] at ha
    exact absurd ha zero_ne_one
  · obtain ⟨z, hz, hzv⟩ := c.exists_vec a ha0
    have h1 : z ∈ commSet D x := (hQ.2 z hz).mpr (by rw [hzv]; exact ha)
    rw [← hzv]
    exact (hQ'.2 z hz).mp h1

omit [Finite G] [Fintype F] [DecidableEq F] in
private theorem form_eq_one_contra (c : SpChart hC B.hα k F) {w : G}
    {Q : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ : IsFormOfLine (hα := B.hα) c Q w) (lam : F) (hlam0 : lam ≠ 0) (hlam1 : lam ≠ 1)
    {a : Fin k ⊕ Fin k → F} (ha0 : a ≠ 0)
    (hmem : ∀ x, x ∈ commSet D hC.d → (c.vec x = a ∨ c.vec x = lam • a) →
      x ∈ commSet D w) : False := by
  have hlam_a0 : lam • a ≠ 0 := smul_ne_zero hlam0 ha0
  obtain ⟨z₁, hz₁, hvz₁⟩ := c.exists_vec a ha0
  obtain ⟨z₂, hz₂, hvz₂⟩ := c.exists_vec (lam • a) hlam_a0
  have hz₁w : z₁ ∈ commSet D w := hmem z₁ hz₁ (Or.inl hvz₁)
  have hz₂w : z₂ ∈ commSet D w := hmem z₂ hz₂ (Or.inr hvz₂)
  have hQ₁ : Q a = 1 := by
    rw [← hvz₁]
    exact (hQ.2 z₁ hz₁).mp hz₁w
  have hQ₂ : Q (lam • a) = 1 := by
    rw [← hvz₂]
    exact (hQ.2 z₂ hz₂).mp hz₂w
  have hsmul : Q (lam • a) = (lam * lam) • Q a :=
    QuadraticMap.map_smul (N := F) Q lam a
  rw [hQ₁, smul_eq_mul, mul_one] at hsmul
  have hsq : lam * lam = 1 := by rw [← hsmul, hQ₂]
  have hfac : (lam - 1) * (lam + 1) = 0 := by
    have h1 : (lam - 1) * (lam + 1) = lam * lam - 1 := by ring
    rw [h1, hsq, sub_self]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · exact hlam1 (sub_eq_zero.mp h1)
  · have hneg : lam = -1 := by
      rw [eq_neg_iff_add_eq_zero]
      exact h1
    rw [show (-1 : F) = 1 from CharTwo.neg_eq 1] at hneg
    exact hlam1 hneg

omit [Finite G] [DecidableEq F] [Fintype F] in
private theorem not_commute_of_isFormOfLine (c : SpChart hC B.hα k F) (hk : 2 ≤ k)
    (hF : Nat.card F = 2 ^ B.f) {w : G} (hw : w ∈ D)
    {Q : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ : IsFormOfLine (hα := B.hα) c Q w) :
    ¬ Commute w hC.d := by
  classical
  intro hcomm
  obtain ⟨lam, hlam0, hlam1⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_ne_zero_ne_one_of_two_lt_card (B.two_lt_card hF)
  have hdimV : Module.finrank F (Fin k ⊕ Fin k → F) = 2 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  by_cases hwd : w = hC.d
  · subst hwd
    have hpos : 0 < Module.finrank F (Fin k ⊕ Fin k → F) := by rw [hdimV]; omega
    obtain ⟨a, ha0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact form_eq_one_contra (B := B) c hQ lam hlam0 hlam1 ha0 (fun x hx _ => hx)
  · have hwDd : w ∈ commSet D hC.d := ⟨hw, hcomm, hwd⟩
    have hb0 : c.vec w ≠ 0 := c.vec_ne_zero w hwDd
    have h4 : 4 ≤ Module.finrank F (⊤ : Submodule F (Fin k ⊕ Fin k → F)) := by
      rw [finrank_top, hdimV]
      have := B.hn
      omega
    obtain ⟨a, -, hab, hnotspan⟩ :=
      CFSG.ClassicalGroups.Alternating.exists_orthogonal_not_mem_span (spForm k F)
        (Y := ⊤) h4 (Submodule.mem_top) hb0
    have ha0 : a ≠ 0 := fun h0 => hnotspan 0 (by rw [h0, zero_smul])
    refine form_eq_one_contra (B := B) c hQ lam hlam0 hlam1 ha0 ?_
    intro x hx hxa
    have hxw : x ≠ w := by
      intro h
      rcases hxa with h' | h'
      · exact hnotspan 1 (by rw [one_smul, ← h', h])
      · refine hnotspan lam⁻¹ ?_
        have hb : c.vec w = lam • a := by rw [← h', h]
        rw [hb, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    have hzw : Commute x w := by
      refine (c.commute_iff x hx w hwDd).mpr ?_
      rcases hxa with h' | h'
      · rw [h', CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
        exact hab
      · rw [h', CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
        rw [LinearMap.map_smul, hab, smul_zero]
    exact ⟨hx.1, hzw, hxw⟩

omit [DecidableEq F] in
theorem isPlusType_iff_ncard (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {w w₀ : G} (hw : w ∈ D) (hw₀ : w₀ ∈ D)
    (hl₀ : (lineMem D hC.d w₀).ncard = 2 ^ B.f - 1) {Q Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ : IsFormOfLine c Q w) (hQ₀ : IsFormOfLine c Q₀ w₀) :
    (IsPlusType Q ↔ IsPlusType Q₀) ↔ (lineMem D hC.d w).ncard = 2 ^ B.f - 1 := by
  classical
  have hk : 2 ≤ k := by have := B.hn; omega
  have hwd : ¬ Commute w hC.d := not_commute_of_isFormOfLine c hk hF hw hQ
  have hw₀d : ¬ Commute w₀ hC.d := not_commute_of_isFormOfLine c hk hF hw₀ hQ₀
  have hQpol : ∀ a b, polar Q a b = spForm k F a b := hQ.1
  have hQ₀pol : ∀ a b, polar Q₀ a b = spForm k F a b := hQ₀.1
  have hQw : ∀ z ∈ commSet D hC.d, (z ∈ commSet D w ↔ Q (c.vec z) = 1) := hQ.2
  have hQ₀w : ∀ z ∈ commSet D hC.d, (z ∈ commSet D w₀ ↔ Q₀ (c.vec z) = 1) := hQ₀.2
  constructor
  · intro htypes
    obtain ⟨x, hx⟩ := exists_conj_lineMem_of_isPlusType_iff hC c hwd hw₀d hQpol hQ₀pol hQw hQ₀w
      htypes
    have heq : (lineMem D hC.d w).ncard = (lineMem D hC.d w₀).ncard := by
      rw [← hx, Set.ncard_image_of_injective _ (MulAut.conj (x : G)).injective]
    rw [heq, hl₀]
  · intro hline
    by_contra hdiff
    obtain ⟨-, -, ⟨w₁, hw₁, hw₁d, hl₁⟩, -⟩ :=
      twelveSeven_sp B.hIH hC B.hMZ B.hα B.hs B.hn B.hf B.hSp
    obtain ⟨v, hv⟩ := B.hdiam w₁ hw₁ hC.d hC.hd hw₁d
    obtain ⟨Q₁, hQ₁pol, hQ₁w, -⟩ := exists_quadraticForm_commSet_inter (hIH := B.hIH)
      (hC := hC) (hMZ := B.hMZ) (hα := B.hα) (hs := B.hs) (hn := B.hn) (hf := B.hf)
      (hSp := B.hSp) (c := c) (hnk := hnk) (hF := hF) (hv := hv.2) (hw := hw₁)
      (hwd := hw₁d) (hwv := hv.1.2.1.symm)
    have hagree : (IsPlusType Q₁ ↔ IsPlusType Q) ∨ (IsPlusType Q₁ ↔ IsPlusType Q₀) := by
      tauto
    rcases hagree with h | h
    · obtain ⟨x, hx⟩ := exists_conj_lineMem_of_isPlusType_iff hC c hw₁d hwd hQ₁pol hQpol
        hQ₁w hQw h
      have heq : (lineMem D hC.d w).ncard = (lineMem D hC.d w₁).ncard := by
        rw [← hx, Set.ncard_image_of_injective _ (MulAut.conj (x : G)).injective]
      omega
    · obtain ⟨x, hx⟩ := exists_conj_lineMem_of_isPlusType_iff hC c hw₁d hw₀d hQ₁pol hQ₀pol
        hQ₁w hQ₀w h
      have heq : (lineMem D hC.d w₀).ncard = (lineMem D hC.d w₁).ncard := by
        rw [← hx, Set.ncard_image_of_injective _ (MulAut.conj (x : G)).injective]
      omega

omit [DecidableEq F] in
theorem mem_lineMem_of_vec_pencil (hnk : B.n = 2 * k) (hF : Nat.card F = 2 ^ B.f) (g : G)
    (cv : SpChart (hC.conj g) (B.conj g).hα k F) {x₁ x₂ x₃ : G}
    (h₁ : x₁ ∈ commSet D (hC.conj g).d) (h₂ : x₂ ∈ commSet D (hC.conj g).d)
    (h₃ : x₃ ∈ commSet D (hC.conj g).d) (h₁₂ : Commute x₁ x₂) {t : F}
    (hvec : cv.vec x₃ = (1 - t) • cv.vec x₁ + t • cv.vec x₂) :
    x₃ ∈ lineMem D x₁ x₂ := by
  classical
  rw [mem_lineMem]
  refine ⟨h₃.1, ?_⟩
  rintro z ⟨hz₁, hz₂⟩
  by_cases hzv : z = (hC.conj g).d
  · subst hzv
    exact ⟨hz₁.1, h₃.2.1.symm⟩
  · by_cases hzCv : Commute z (hC.conj g).d
    · have hzDv : z ∈ commSet D (hC.conj g).d := ⟨hz₁.1, hzCv, hzv⟩
      have hzx₁ : spForm k F (cv.vec z) (cv.vec x₁) = 0 :=
        (cv.commute_iff z hzDv x₁ h₁).mp hz₁.2
      have hzx₂ : spForm k F (cv.vec z) (cv.vec x₂) = 0 :=
        (cv.commute_iff z hzDv x₂ h₂).mp hz₂.2
      have hzx₃ : spForm k F (cv.vec z) (cv.vec x₃) = 0 := by
        rw [hvec, map_add, map_smul, map_smul, hzx₁, hzx₂, smul_zero, smul_zero, add_zero]
      exact ⟨hz₁.1, (cv.commute_iff z hzDv x₃ h₃).mpr hzx₃⟩
    · have hnk' : (B.conj g).n = 2 * k := by rw [B.conj_n]; exact hnk
      have hF' : Nat.card F = 2 ^ (B.conj g).f := by rw [B.conj_f]; exact hF
      obtain ⟨Q, hQpol, hQz, -⟩ := exists_quadraticForm_commSet_inter (hIH := (B.conj g).hIH)
        (hC := hC.conj g) (hMZ := (B.conj g).hMZ) (hα := (B.conj g).hα)
        (hs := (B.conj g).hs) (hn := (B.conj g).hn) (hf := (B.conj g).hf)
        (hSp := (B.conj g).hSp) (c := cv) (hnk := hnk') (hF := hF')
        (hv := h₁) (hw := hz₁.1) (hwd := hzCv) (hwv := hz₁.2)
      have hx₁z : x₁ ∈ commSet D z :=
        ⟨h₁.1, hz₁.2.symm, fun h => hzCv (h ▸ h₁.2.1)⟩
      have hx₂z : x₂ ∈ commSet D z :=
        ⟨h₂.1, hz₂.2.symm, fun h => hzCv (h ▸ h₂.2.1)⟩
      have hQ₁ : Q (cv.vec x₁) = 1 := (hQz x₁ h₁).mp hx₁z
      have hQ₂ : Q (cv.vec x₂) = 1 := (hQz x₂ h₂).mp hx₂z
      have hpolar : polar Q (cv.vec x₁) (cv.vec x₂) = 0 := by
        rw [hQpol]
        exact (cv.commute_iff x₁ h₁ x₂ h₂).mp h₁₂
      have hQ₃ : Q (cv.vec x₃) = 1 := by
        simp only [hvec, QuadraticMap.map_add, QuadraticMap.map_smul,
          QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hQ₁, hQ₂, hpolar,
          smul_eq_mul, mul_one, mul_zero, add_zero]
        rw [sub_eq_add_neg, CharTwo.neg_eq]
        ring_nf
        have h2 : (2 : F) = 0 := by
          rw [show (2 : F) = 1 + 1 by norm_num, CharTwo.add_self_eq_zero]
        calc 1 + t * 2 + t ^ 2 * 2 = 1 + t * 0 + t ^ 2 * 0 := by rw [h2]
          _ = 1 := by rw [mul_zero, mul_zero, add_zero, add_zero]
      exact ⟨hz₁.1, ((hQz x₃ h₃).mpr hQ₃).2.1.symm⟩

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem exists_nondegenerate_plane_in_orthogonal (hk : 2 ≤ k)
    {bb : Fin k ⊕ Fin k → F} (hbb : bb ≠ 0) :
    ∃ P : Submodule F (Fin k ⊕ Fin k → F),
      P ≤ (spForm k F).orthogonal (Submodule.span F {bb}) ∧
        Module.finrank F P = 2 ∧ ((spForm k F).restrict P).Nondegenerate := by
  classical
  have hB : (spForm k F).IsAlt := spForm_isAlt
  have hBnd : (spForm k F).Nondegenerate := spForm_nondegenerate
  obtain ⟨e, he⟩ := (CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting
    (B := spForm k F) hB hBnd hbb).1
  obtain ⟨-, -, -, -, hWnd, hWdim⟩ :=
    (CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting (B := spForm k F)
      hB hBnd hbb).2 e he
  let W : Submodule F (Fin k ⊕ Fin k → F) :=
    (spForm k F).orthogonal (Submodule.span F {bb, e})
  have hdimV : Module.finrank F (Fin k ⊕ Fin k → F) = 2 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hWdim' : Module.finrank F W = Module.finrank F (Fin k ⊕ Fin k → F) - 2 := hWdim
  have hWpos : 0 < Module.finrank F W := by omega
  obtain ⟨u, hu0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hWpos
  have hWalt : ((spForm k F).restrict W).IsAlt :=
    CFSG.ClassicalGroups.Alternating.isAlt_restrict hB W
  obtain ⟨v, hv⟩ := (CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting
    (B := (spForm k F).restrict W) hWalt hWnd hu0).1
  let P : Submodule F (Fin k ⊕ Fin k → F) :=
    Submodule.span F {(u : Fin k ⊕ Fin k → F), (v : Fin k ⊕ Fin k → F)}
  have hPle : P ≤ W := by
    refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl)
    · exact u.2
    · exact v.2
  have hvval : spForm k F (u : Fin k ⊕ Fin k → F) (v : Fin k ⊕ Fin k → F) = 1 := by
    simpa using hv
  have huval : (u : Fin k ⊕ Fin k → F) ≠ 0 := fun h0 => hu0 (Subtype.ext h0)
  have hPdata := (CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting
    (B := spForm k F) hB hBnd huval).2 (v : Fin k ⊕ Fin k → F) hvval
  have hPnd : ((spForm k F).restrict P).Nondegenerate := hPdata.2.1
  have hPdim : Module.finrank F P = 2 := hPdata.1
  have hWle : W ≤ (spForm k F).orthogonal (Submodule.span F {bb}) :=
    LinearMap.BilinForm.orthogonal_le
      (Submodule.span_mono (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        exact Or.inl hx))
  exact ⟨P, hPle.trans hWle, hPdim, hPnd⟩

omit [Finite G] [DecidableEq F] in
private theorem exists_spForm_eq_zero_form_eq_one (hk : 2 ≤ k)
    (hF : Nat.card F = 2 ^ B.f) {bb : Fin k ⊕ Fin k → F} (hbb : bb ≠ 0)
    (Q : QuadraticForm F (Fin k ⊕ Fin k → F)) (hQ : ∀ a b, polar Q a b = spForm k F a b) :
    ∃ x, spForm k F bb x = 0 ∧ Q x = 1 := by
  obtain ⟨P, hPle, hPdim, hPnd⟩ := exists_nondegenerate_plane_in_orthogonal hk hbb
  have hpolar : polarBilin (Q.comp P.subtype) = (spForm k F).restrict P := by
    ext x y
    exact hQ x y
  have hQPnd : (polarBilin (Q.comp P.subtype)).Nondegenerate := by
    rw [hpolar]
    exact hPnd
  have hK : 2 < Nat.card F := B.two_lt_card hF
  have hspan :=
    CFSG.OddTranspositions.PartThree.span_setOf_eq_one_eq_top (K := F) (V := P) hK hQPnd
  have _hNontrivial : Nontrivial P := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hne : {x : P | Q.comp P.subtype x = 1}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, Submodule.span_empty] at hspan
    exact bot_ne_top hspan
  obtain ⟨x, hxQ⟩ := hne
  refine ⟨(x : Fin k ⊕ Fin k → F), (LinearMap.BilinForm.mem_orthogonal_iff.mp (hPle x.2)) bb
    (Submodule.subset_span (by simp)), ?_⟩
  simpa using hxQ

omit [DecidableEq F] in
theorem commSet_inter_inter_nonempty (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {a b : G} (ha : a ∈ D) (hb : b ∈ D)
    (hau : ¬ Commute a hC.d) (hbu : ¬ Commute b hC.d) (hab : Commute a b) (hne : a ≠ b) :
    (commSet D hC.d ∩ commSet D a ∩ commSet D b).Nonempty := by
  classical
  have hk : 2 ≤ k := by have := B.hn; omega
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd ha)
  have hga : (hC.conj g).d = a := by rw [HypothesisC.conj_d, hg]
  let ca : SpChart (hC.conj g) (B.conj g).hα k F := SpChart.conj (B := B) c g
  obtain ⟨v, hv⟩ := (B.conj g).hdiam a ha hC.d hC.hd hau
  have hnk' : (B.conj g).n = 2 * k := by rw [B.conj_n]; exact hnk
  have hF' : Nat.card F = 2 ^ (B.conj g).f := by rw [B.conj_f]; exact hF
  obtain ⟨Q, hQpol, hQz, -⟩ := exists_quadraticForm_commSet_inter (hIH := (B.conj g).hIH)
    (hC := hC.conj g) (hMZ := (B.conj g).hMZ) (hα := (B.conj g).hα)
    (hs := (B.conj g).hs) (hn := (B.conj g).hn) (hf := (B.conj g).hf)
    (hSp := (B.conj g).hSp) (c := ca) (hnk := hnk') (hF := hF')
    (hv := by simpa [hga] using hv.1) (hw := hC.hd)
    (hwd := by intro h; rw [hga] at h; exact hau h.symm) (hwv := hv.2.2.1.symm)
  have hbDa : b ∈ commSet D a := ⟨hb, hab.symm, hne.symm⟩
  have hbDa' : b ∈ commSet D (hC.conj g).d := by simpa [hga] using hbDa
  obtain ⟨x, hxbb, hxQ⟩ := exists_spForm_eq_zero_form_eq_one (B := B) hk hF
    (ca.vec_ne_zero b hbDa') Q hQpol
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, QuadraticMap.map_zero] at hxQ
    exact zero_ne_one hxQ
  obtain ⟨z, hz, hzv⟩ := ca.exists_vec x hx0
  have hzd : z ∈ commSet D hC.d := by
    refine (hQz z hz).mpr ?_
    rw [hzv]
    exact hxQ
  have hzb : z ∈ commSet D b := by
    have hcomm : Commute z b := by
      refine (ca.commute_iff z hz b hbDa').mpr ?_
      rw [hzv, CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
      exact hxbb
    refine ⟨hz.1, hcomm, ?_⟩
    intro hzb'
    exact hbu (hzb' ▸ hzd.2.1)
  have hza : z ∈ commSet D a := by simpa [hga] using hz
  exact ⟨z, ⟨⟨hzd, hza⟩, hzb⟩⟩

theorem not_o4PairData_of_isSymplecticTransvection (hMZ :
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hs : s ∈ imageClass hC) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s) :
    ¬ O4PairData G D := by
  intro hO4
  have hα := alpha_eq_singleton_of_isSymplecticTransvection hC hMZ hs hn hf hSp
  obtain ⟨k, F, _, _, _, hnk, hF, ⟨c⟩⟩ := exists_spChart hC hMZ hα hs hSp
  have hle := c.le_ncard
  rw [hF] at hle
  have h10 := ncard_commSet_of_o4PairData hO4 hC.hd
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h2k : 4 ≤ 2 * k := by omega
  have h255 : 255 ≤ (2 ^ f) ^ (2 * k) - 1 := by
    have h1 : (4 : ℕ) ^ 4 ≤ (2 ^ f) ^ (2 * k) := by
      calc (4 : ℕ) ^ 4 ≤ (2 ^ f) ^ 4 := by gcongr
        _ ≤ (2 ^ f) ^ (2 * k) := Nat.pow_le_pow_right (by positivity) h2k
    calc 255 = 4 ^ 4 - 1 := by norm_num
      _ ≤ (2 ^ f) ^ (2 * k) - 1 := Nat.sub_le_sub_right h1 1
  omega

omit [Finite G] [DecidableEq F] [Fintype F] in
private theorem exists_ne_zero_ne_one_sq_ne_one (hK : 2 < Nat.card F) :
    ∃ μ : F, μ ≠ 0 ∧ μ ≠ 1 ∧ μ ^ 2 ≠ 1 := by
  obtain ⟨μ, hμ0, hμ1⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_ne_zero_ne_one_of_two_lt_card hK
  refine ⟨μ, hμ0, hμ1, ?_⟩
  intro h
  rcases (sq_eq_one_iff.mp h) with h' | h'
  · exact hμ1 h'
  · rw [CharTwo.neg_eq] at h'
    exact hμ1 h'

omit [Finite G] [DecidableEq F] [Fintype F] in
private theorem mStabForm_eq_d_contra (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {Y : MSpace k F}
    (hform : ∀ z, z ∈ commSet D hC.d →
      (z ∈ commSet D hC.d ↔ mStabForm Q₀ Y (c.vec z) = 1)) : False := by
  classical
  let S : QuadraticForm F (Fin k ⊕ Fin k → F) := mStabForm Q₀ Y
  have hS_smul : ∀ (a : F) (v : Fin k ⊕ Fin k → F), S (a • v) = a ^ 2 * S v := by
    intro a v
    rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]
  have hK : 2 < Nat.card F := B.two_lt_card hF
  obtain ⟨lam, hlam0, hlam1', hlamsq⟩ := exists_ne_zero_ne_one_sq_ne_one hK
  have hdim : 0 < Module.finrank F (Fin k ⊕ Fin k → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    have hk : 2 ≤ k := by have := B.hn; omega
    omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
  obtain ⟨z, hz, hzv⟩ := c.exists_vec v hv
  have hSv : S v = 1 := by
    have h := (hform z hz).mp hz
    rwa [hzv] at h
  have hsv : S (lam • v) = 1 := by
    have hv' : lam • v ≠ 0 := smul_ne_zero hlam0 hv
    obtain ⟨z', hz', hzv'⟩ := c.exists_vec (lam • v) hv'
    have h := (hform z' hz').mp hz'
    rwa [hzv'] at h
  rw [hS_smul, hSv, mul_one] at hsv
  exact hlamsq hsv

omit [Finite G] [Fintype F] [DecidableEq F] in
private theorem mStabForm_smul_relation (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {x : G} (hx' : x ∈ commSet D hC.d) {Y : MSpace k F}
    (hform : ∀ z ∈ commSet D hC.d,
      (z ∈ commSet D x ↔ mStabForm Q₀ Y (c.vec z) = 1))
    (hS_polar : ∀ a b, polar (mStabForm Q₀ Y) a b = spForm k F a b)
    (hS_smul : ∀ (a : F) (v : Fin k ⊕ Fin k → F),
      (mStabForm Q₀ Y) (a • v) = a ^ 2 * (mStabForm Q₀ Y) v)
    {w : Fin k ⊕ Fin k → F} (huw : spForm k F (c.vec x) w = 0)
    (hnotspan : ∀ μ : F, μ ≠ 0 → c.vec x + μ • w ∉ Submodule.span F {c.vec x}) :
    ∀ μ : F, μ ≠ 0 →
      (mStabForm Q₀ Y) (c.vec x) + μ ^ 2 * (mStabForm Q₀ Y) w = 1 := by
  intro μ hμ
  have hvec : c.vec x + μ • w ≠ 0 := by
    intro h0
    exact hnotspan μ hμ (h0 ▸ Submodule.zero_mem _)
  obtain ⟨z, hz, hzv⟩ := c.exists_vec (c.vec x + μ • w) hvec
  have hzx : z ∈ commSet D x := by
    refine ⟨hz.1, ?_, ?_⟩
    · refine (c.commute_iff z hz x hx').mpr ?_
      rw [hzv]
      have hsw : spForm k F w (c.vec x) = 0 := by
        rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt, huw]
      simp only [map_add, LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply,
        (spForm_isAlt (r := k) (K := F)) (c.vec x), hsw, smul_zero, add_zero]
    · intro h
      apply hnotspan μ hμ
      rw [← hzv, h]
      exact Submodule.subset_span (Set.mem_singleton (c.vec x))
  have hS := (hform z hz).mp hzx
  rw [hzv] at hS
  rw [QuadraticMap.map_add (mStabForm Q₀ Y) (c.vec x) (μ • w),
    hS_polar (c.vec x) (μ • w), hS_smul μ w] at hS
  have hpol : spForm k F (c.vec x) (μ • w) = 0 := by
    rw [LinearMap.map_smul, huw, smul_zero]
  rw [hpol, add_zero] at hS
  exact hS

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem exists_orthogonal_not_span_of_mStabForm (c : SpChart hC B.hα k F)
    (hnk : B.n = 2 * k)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {x : G} {Y : MSpace k F}
    (hx' : x ∈ commSet D hC.d)
    (hform : ∀ z ∈ commSet D hC.d,
      (z ∈ commSet D x ↔ mStabForm Q₀ Y (c.vec z) = 1)) :
    ∃ w : Fin k ⊕ Fin k → F,
      spForm k F (c.vec x) w = 0 ∧
        (∀ μ : F, μ ≠ 0 → c.vec x + μ • w ∉ Submodule.span F {c.vec x}) ∧
        (mStabForm Q₀ Y) (c.vec x) ≠ 1 := by
  have hSu : (mStabForm Q₀ Y) (c.vec x) ≠ 1 := by
    intro h
    have hxinx : x ∈ commSet D x := (hform x hx').mpr h
    exact hxinx.2.2 rfl
  have hk : 2 ≤ k := by have := B.hn; omega
  have h4 : 4 ≤ Module.finrank F (⊤ : Submodule F (Fin k ⊕ Fin k → F)) := by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨w, -, huw, hw⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_orthogonal_not_mem_span (spForm k F)
      (Y := ⊤) h4 (Submodule.mem_top) (c.vec_ne_zero x hx')
  refine ⟨w, huw, ?_, hSu⟩
  intro μ hμ h
  have h1 : μ • w ∈ Submodule.span F {c.vec x} := by
    have h2 := Submodule.sub_mem _ h
      (Submodule.subset_span (Set.mem_singleton (c.vec x)))
    simpa [add_sub_cancel_left] using h2
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp
    (by simpa [smul_smul, inv_mul_cancel₀ hμ] using Submodule.smul_mem _ μ⁻¹ h1)
  exact hw s hs.symm

omit [Finite G] [Fintype F] in
private theorem false_of_stabForm_smul_relation
    {S : QuadraticForm F (Fin k ⊕ Fin k → F)} {x w : Fin k ⊕ Fin k → F}
    (hF : Nat.card F = 2 ^ B.f)
    (hmain : ∀ μ : F, μ ≠ 0 → S x + μ ^ 2 * S w = 1)
    (hSu : S x ≠ 1) : False := by
  have hK : 2 < Nat.card F := B.two_lt_card hF
  obtain ⟨lam, hlam0, hlam1', hlamsq⟩ := exists_ne_zero_ne_one_sq_ne_one hK
  have h1 : S x + S w = 1 := by simpa using hmain 1 one_ne_zero
  have h2 : S x + lam ^ 2 * S w = 1 := hmain lam hlam0
  have h3 : S w = lam ^ 2 * S w := add_left_cancel (h1.trans h2.symm)
  have h4 : (lam ^ 2 - 1) * S w = 0 := by
    rw [sub_mul, one_mul, ← h3, sub_self]
  by_cases hSw : S w = 0
  · rw [hSw, mul_zero, add_zero] at h2
    exact hSu h2
  · have h5 : lam ^ 2 - 1 = 0 := by
      rcases mul_eq_zero.mp h4 with h5 | h5
      · exact h5
      · exact absurd h5 hSw
    exact hlamsq (sub_eq_zero.mp h5)

omit [Finite G] [Fintype F] in
private theorem not_commute_d_of_mStabForm (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {x : G} (hx : x ∈ D) {Y : MSpace k F}
    (hform : ∀ z ∈ commSet D hC.d,
      (z ∈ commSet D x ↔ mStabForm Q₀ Y (c.vec z) = 1)) :
    ¬ Commute x hC.d := by
  classical
  intro hxd
  have hS_polar : ∀ a b, polar (mStabForm Q₀ Y) a b = spForm k F a b := by
    intro a b
    exact polar_mStabForm hQ₀ Y a b
  have hS_smul : ∀ (a : F) (v : Fin k ⊕ Fin k → F),
      (mStabForm Q₀ Y) (a • v) = a ^ 2 * (mStabForm Q₀ Y) v := by
    intro a v
    rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]
  by_cases hxd' : x = hC.d
  · subst hxd'
    exact mStabForm_eq_d_contra c hnk hF hform
  · have hx' : x ∈ commSet D hC.d := ⟨hx, hxd, hxd'⟩
    obtain ⟨w, huw, hnotspan, hSu⟩ :=
      exists_orthogonal_not_span_of_mStabForm (B := B) c hnk hx' hform
    have hmain : ∀ μ : F, μ ≠ 0 →
        (mStabForm Q₀ Y) (c.vec x) + μ ^ 2 * (mStabForm Q₀ Y) w = 1 :=
      mStabForm_smul_relation (B := B) c hx' hform hS_polar hS_smul huw hnotspan
    exact false_of_stabForm_smul_relation (B := B) (S := mStabForm Q₀ Y)
      (x := c.vec x) (w := w) hF hmain hSu

omit [Fintype F] [DecidableEq F] in
private theorem commute_iff_mUmY {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0) :
    ¬ Commute (mRefl Q₀ mU) (mRefl Q₀ Y) := by
  intro hcomm
  have hmU1 : mForm Q₀ mU = 1 := by
    rw [mForm_apply]
    simp [mU]
  have hcomm' : Commute (reflect (mForm Q₀) mU) (reflect (mForm Q₀) Y) :=
    hcomm.map (Subgroup.subtype (TauCeti.QuadraticMap.orthogonalGroup (mForm Q₀)))
  have hpol := (commute_reflect_iff (Q := mForm Q₀) hmU1 hY).mp hcomm'
  rw [polar_mForm hQ₀] at hpol
  simp [mU] at hpol
  exact hβ hpol

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem commute_iff_exists_conj (c : SpChart hC B.hα k F)
    {Qx : QuadraticForm F (Fin k ⊕ Fin k → F)} {x : G}
    (hQx_val : ∀ z, z ∈ commSet D hC.d →
      (z ∈ commSet D x ↔ Qx (c.vec z) = 1))
    (hstab2 : Halpha D hC.alpha ⊓ Subgroup.centralizer {x} =
      hypLineGroup D hC.d x)
    {kk : ↥(Halpha D hC.alpha)}
    (hgen : c.ρ kk ∈ Subgroup.closure
      ((fun a => spTransvection a 1) '' {a | Qx a = 1})) :
    ∃ kk' : ↥(Halpha D hC.alpha),
      (kk' : G) ∈ hypLineGroup D hC.d x ∧ c.ρ kk' = c.ρ kk ∧
        Commute (kk' : G) x := by
  let Sgen : Set G := commSet D hC.d ∩ commSet D x
  let SgenH : Set ↥(Halpha D hC.alpha) := {x | (x : G) ∈ Sgen}
  have hmap : Subgroup.closure ((fun a => spTransvection a 1) '' {a | Qx a = 1}) ≤
      (Subgroup.closure SgenH).map c.ρ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha0 : a ≠ 0 := by
      intro h0
      have h1 : Qx 0 = 1 := by
        simp [h0] at ha ⊢
      rw [QuadraticMap.map_zero] at h1
      exact zero_ne_one h1
    obtain ⟨z, hz, hzv⟩ := c.exists_vec a ha0
    have hz_x : z ∈ commSet D x := (hQx_val z hz).mpr (by rwa [hzv])
    have hzS : z ∈ Sgen := ⟨hz, hz_x⟩
    have hzSH : (⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩ :
        ↥(Halpha D hC.alpha)) ∈ SgenH := hzS
    refine ⟨⟨z, mem_Halpha_of_mem_commSet hC B.hα hz⟩,
      Subgroup.subset_closure hzSH, ?_⟩
    rw [c.map_eq z hz, hzv]
  have hgen' : c.ρ kk ∈ (Subgroup.closure SgenH).map c.ρ := hmap hgen
  obtain ⟨kk', hk', hk'ρ⟩ := Subgroup.mem_map.mp hgen'
  have hSgenH_sub : Subgroup.closure SgenH ≤
      (hypLineGroup D hC.d x).comap (Subgroup.subtype (Halpha D hC.alpha)) := by
    rw [Subgroup.closure_le]
    rintro ⟨z, hzH⟩ hzS
    exact Subgroup.subset_closure hzS
  have hk'L : (kk' : G) ∈ hypLineGroup D hC.d x := hSgenH_sub hk'
  have hk'comm : Commute (kk' : G) x := by
    have hmem : (kk' : G) ∈ Halpha D hC.alpha ⊓ Subgroup.centralizer {x} := by
      rw [hstab2]
      exact hk'L
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem.2
  exact ⟨kk', hk'L, hk'ρ, hk'comm⟩

omit [Fintype F] [DecidableEq F] [CharP F 2] in
private theorem commute_iff_kernel_cases (c : SpChart hC B.hα k F)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {kk kk' : ↥(Halpha D hC.alpha)}
    (hk'ρ : c.ρ kk' = c.ρ kk) :
    kk = kk' ∨ kk = (⟨hC.d, hu⟩ : Halpha D hC.alpha) * kk' := by
  have hker : (kk' * kk⁻¹ : Halpha D hC.alpha) ∈ c.ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk'ρ, mul_inv_cancel]
  have hzpow : (kk' * kk⁻¹ : Halpha D hC.alpha) ∈ Subgroup.zpowers ⟨hC.d, hu⟩ := by
    rw [← c.ker_eq_zpowers B hu]
    exact hker
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hzpow
  have hk_eq : kk = (⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ (-m) * kk' := by
    have h1 : (⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ (-m) *
        (⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ m = 1 := by
      rw [← zpow_add, neg_add_cancel, zpow_zero]
    calc kk = 1 * kk := by rw [one_mul]
      _ = ((⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ (-m) *
          (⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ m) * kk := by rw [h1]
      _ = (⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ (-m) *
          ((⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ m * kk) := by rw [mul_assoc]
      _ = (⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ (-m) * (kk' * kk⁻¹ * kk) := by rw [hm]
      _ = (⟨hC.d, hu⟩ : Halpha D hC.alpha) ^ (-m) * kk' := by
            rw [mul_assoc, inv_mul_cancel, mul_one]
  have hd2 : (⟨hC.d, hu⟩ : Halpha D hC.alpha) * ⟨hC.d, hu⟩ = 1 :=
    (mul_self_eq_one_and_ne_one_of_mem_alpha hC hC.d_mem_alpha hu).1
  have hzpow_d := CFSG.GroupTheory.zpow_eq_one_or_self_of_mul_self_eq_one hd2
  rcases hzpow_d (-m) with h1 | h1
  · left
    rw [h1, one_mul] at hk_eq
    exact hk_eq
  · right
    rw [h1] at hk_eq
    exact hk_eq

omit [Finite G] [DecidableEq F] in
private theorem commute_mLift_of_mem_hypLineGroup (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    {x : G} {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (hform : ∀ z ∈ commSet D hC.d,
      (z ∈ commSet D x ↔ mStabForm Q₀ Y (c.vec z) = 1))
    {kk : ↥(Halpha D hC.alpha)}
    (hk_mem : (kk : G) ∈ hypLineGroup D hC.d x) :
    Commute (θ kk : MGroup Q₀) (mRefl Q₀ Y) := by
  let Sgen : Set G := commSet D hC.d ∩ commSet D x
  have hL_le : hypLineGroup D hC.d x ≤ Halpha D hC.alpha := by
    rw [show hypLineGroup D hC.d x = Subgroup.closure Sgen from rfl]
    rw [Subgroup.closure_le]
    intro z hz
    exact mem_Halpha_of_mem_commSet hC B.hα hz.1
  have hprop : ∀ z (hz : z ∈ hypLineGroup D hC.d x),
      Commute (θ ⟨z, hL_le hz⟩ : MGroup Q₀) (mRefl Q₀ Y) := by
    intro z hz
    change z ∈ Subgroup.closure Sgen at hz
    induction hz using Subgroup.closure_induction with
    | mem y hy =>
      have hy_d : y ∈ commSet D hC.d := hy.1
      have hy_x : y ∈ commSet D x := hy.2
      have hyH : y ∈ Halpha D hC.alpha := mem_Halpha_of_mem_commSet hC B.hα hy_d
      have harg : (⟨y, hL_le (Subgroup.subset_closure hy)⟩ : Halpha D hC.alpha) =
          ⟨y, hyH⟩ := Subtype.ext rfl
      rw [harg, hθ.2.2 y hy_d]
      exact (commute_mLift_iff hQ₀ hY hβ (c.vec y)).mpr ((hform y hy_d).mp hy_x)
    | one =>
      have harg : (⟨1, hL_le (Subgroup.one_mem _)⟩ : Halpha D hC.alpha) = 1 :=
        Subtype.ext rfl
      rw [harg, map_one]
      exact Commute.one_left _
    | mul a b ha hb iha ihb =>
      have harg : (⟨a * b, hL_le (Subgroup.mul_mem _ ha hb)⟩ : Halpha D hC.alpha) =
          ⟨a, hL_le ha⟩ * ⟨b, hL_le hb⟩ := Subtype.ext rfl
      rw [harg, map_mul]
      exact iha.mul_left ihb
    | inv a ha iha =>
      have harg : (⟨a⁻¹, hL_le (Subgroup.inv_mem _ ha)⟩ : Halpha D hC.alpha) =
          (⟨a, hL_le ha⟩ : Halpha D hC.alpha)⁻¹ := Subtype.ext rfl
      rw [harg, map_inv]
      exact iha.inv_left
  have hfin := hprop (kk : G) hk_mem
  rwa [show (⟨(kk : G), hL_le hk_mem⟩ : Halpha D hC.alpha) = kk from
    Subtype.ext rfl] at hfin

omit [Finite G] [DecidableEq F] in
private theorem commute_iff_forward (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    {x : G} {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (hform : ∀ z ∈ commSet D hC.d,
      (z ∈ commSet D x ↔ mStabForm Q₀ Y (c.vec z) = 1))
    (hstab2 : Halpha D hC.alpha ⊓ Subgroup.centralizer {x} =
      hypLineGroup D hC.d x) :
    ∀ kk : ↥(Halpha D hC.alpha),
      Commute (kk : G) x → Commute (θ kk : MGroup Q₀) (mRefl Q₀ Y) := by
  intro kk hk
  have hk_mem : (kk : G) ∈ hypLineGroup D hC.d x := by
    have hmem : (kk : G) ∈ Halpha D hC.alpha ⊓ Subgroup.centralizer {x} :=
      ⟨kk.2, Subgroup.mem_centralizer_singleton_iff.mpr hk⟩
    rwa [hstab2] at hmem
  exact commute_mLift_of_mem_hypLineGroup (B := B) c hQ₀ hθ hY hβ hform hk_mem

omit [Finite G] [DecidableEq F] in
private theorem commute_iff_backward_apply (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    {x : G} {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (hform : ∀ z ∈ commSet D hC.d,
      (z ∈ commSet D x ↔ mStabForm Q₀ Y (c.vec z) = 1))
    {Qx : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQx_pol : ∀ a b, polar Qx a b = spForm k F a b)
    (hQx_val : ∀ z, z ∈ commSet D hC.d →
      (z ∈ commSet D x ↔ Qx (c.vec z) = 1))
    (hK : 2 < Nat.card F)
    {kk : ↥(Halpha D hC.alpha)}
    (hk : Commute (θ kk : MGroup Q₀) (mRefl Q₀ Y)) :
    ∀ a, Qx (spEnd (c.ρ kk) a) = Qx a := by
  have hkY : (((θ kk : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) Y) = Y :=
    (CFSG.ClassicalGroups.Orthogonal.commute_reflect_iff_apply_eq
      (Q := mForm Q₀) (nondegenerate_polarBilin_mForm hQ₀)
      (θ kk) (by rw [hY]; exact one_ne_zero)).mp (by
        simpa [mRefl] using hk)
  have hQx_eq : Qx = mStabForm Q₀ Y :=
    eq_of_isFormOfLine hK ⟨hQx_pol, hQx_val⟩ ⟨polar_mStabForm hQ₀ Y, hform⟩
  intro a
  rw [hQx_eq]
  have h := mStabForm_apply_eq_of_mem_centralizer hQ₀ hβ (θ kk).2 a
  rw [show (((θ kk : MGroup Q₀) : MSpace k F ≃ₗ[F] MSpace k F) Y) = Y
    from hkY] at h
  rw [← hθ.1 kk a] at h
  exact h

omit [DecidableEq F] in
private theorem commute_iff_backward (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    {x : G} {Y : MSpace k F} (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (hform : ∀ z ∈ commSet D hC.d,
      (z ∈ commSet D x ↔ mStabForm Q₀ Y (c.vec z) = 1))
    (hstab2 : Halpha D hC.alpha ⊓ Subgroup.centralizer {x} =
      hypLineGroup D hC.d x)
    {Qx : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQx_pol : ∀ a b, polar Qx a b = spForm k F a b)
    (hQx_val : ∀ z, z ∈ commSet D hC.d →
      (z ∈ commSet D x ↔ Qx (c.vec z) = 1))
    (hQx_gen : ∀ g : StatedSp k F, (∀ a, Qx (spEnd g a) = Qx a) →
      g ∈ Subgroup.closure ((fun a => spTransvection a 1) '' {a | Qx a = 1}))
    (hK : 2 < Nat.card F) :
    ∀ kk : ↥(Halpha D hC.alpha),
      Commute (θ kk : MGroup Q₀) (mRefl Q₀ Y) → Commute (kk : G) x := by
  intro kk hk
  have hQxinv := commute_iff_backward_apply (B := B) c hQ₀ hθ hY hβ hform hQx_pol hQx_val hK hk
  have hgen := hQx_gen (c.ρ kk) hQxinv
  obtain ⟨kk', hk'L, hk'ρ, hk'comm⟩ :=
    commute_iff_exists_conj (B := B) c hQx_val hstab2 hgen
  have hk'θ : Commute (θ kk' : MGroup Q₀) (mRefl Q₀ Y) :=
    commute_iff_forward (B := B) c hQ₀ hθ hY hβ hform hstab2 kk' hk'comm
  rcases commute_iff_kernel_cases (B := B) (hu := hu) c hk'ρ with h1 | h1
  · rw [h1]
    exact hk'comm
  · exfalso
    have hdcomm : Commute (θ (⟨hC.d, hu⟩ : Halpha D hC.alpha) : MGroup Q₀)
        (mRefl Q₀ Y) := by
      have h1' : (θ kk : MGroup Q₀) = (θ ⟨hC.d, hu⟩ : MGroup Q₀) * θ kk' := by
        rw [h1, map_mul]
        rfl
      have h2 : Commute ((θ kk')⁻¹ : MGroup Q₀) (mRefl Q₀ Y) := hk'θ.inv_left
      have h3 : Commute ((θ kk : MGroup Q₀) * (θ kk')⁻¹) (mRefl Q₀ Y) :=
        hk.mul_left h2
      rw [h1'] at h3
      simpa [mul_assoc] using h3
    rw [hθ.2.1] at hdcomm
    exact commute_iff_mUmY hQ₀ hY hβ hdcomm

theorem commute_iff_of_form_eq (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ)
    {x : G} (hx : x ∈ D) {Y : MSpace k F}
    (hY : mForm Q₀ Y = 1) (hβ : Y.1.2 ≠ 0)
    (hform : ∀ z ∈ commSet D hC.d,
      (z ∈ commSet D x ↔ mStabForm Q₀ Y (c.vec z) = 1)) :
    ∀ h : ↥(Halpha D hC.alpha),
      Commute (h : G) x ↔ Commute (θ h : MGroup Q₀) (mRefl Q₀ Y) := by
  classical
  have hxu : ¬ Commute x hC.d :=
    not_commute_d_of_mStabForm c hnk hF hQ₀ hx hform
  obtain ⟨v, hv⟩ := B.hdiam x hx hC.d hC.hd hxu
  have hstab := twelveTen_sp_stabilizers_of_commSet_inter B.hIH hC B.hMZ B.hα B.hs B.hn B.hf
    B.hSp hv.2 hx hxu (hv.1.2.1.symm)
  obtain ⟨Qx, hQx_pol, hQx_val, hQx_gen⟩ :=
    exists_quadraticForm_commSet_inter B.hIH hC B.hMZ B.hα B.hs B.hn B.hf B.hSp c hnk hF
      hv.2 hx hxu (hv.1.2.1.symm)
  have hK : 2 < Nat.card F := B.two_lt_card hF
  intro h
  exact ⟨commute_iff_forward (B := B) c hQ₀ hθ hY hβ hform hstab.2 h,
    commute_iff_backward (B := B) c hQ₀ hθ hY hβ hform hstab.2 hQx_pol hQx_val hQx_gen hK h⟩

end CFSG.OddTranspositions.PartThree.ElevenSp

end
