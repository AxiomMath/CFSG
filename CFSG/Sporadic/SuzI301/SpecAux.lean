module

public import Certificates.Certificate810302
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.Sporadic.Co1Block.TwoBTri
public import CFSG.Sporadic.FischerOddCore.PairComp
public import Certificates.Kernel.Sporadic.SuzH.Proof

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.Sporadic.SuzI301.SpecAux

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.ComponentClassification.PSL3Four
  CFSG.PSL3Four.Native CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabSuzA
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.Sporadic.SuzI301
open CFSG.RankThree.Native (validA rep_of_validA rep_inv_of_validA permOfArr_eq_of_rep commA
  commA_iff commutatorA rep_commutatorA)
open scoped commutatorElement

private theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

private theorem rep_invCand_gen {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

private theorem rep_of_eqA_left {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (hu : Rep n u g)
    (h : eqA n t u = true) : Rep n t g := fun x => by
  have := allLt_spec h x.2
  rw [beq_iff_eq] at this
  rw [this]
  exact hu x

private theorem comm1782_iff {t u : Array ℕ} {G H : Equiv.Perm (Fin 1782)} (ht : Rep 1782 t G)
    (hu : Rep 1782 u H) : comm1782 t u = true ↔ Commute G H :=
  eqA_iff (rep_compA ht hu) (rep_compA hu ht)

private theorem commutator_mem_closure_pair {G : Type*} [Group G] {a b x : G} (ha : Commute a x)
    (hb : Commute b x) {u v : G} (hu : u ∈ Subgroup.closure ({a, b, x} : Set G))
    (hv : v ∈ Subgroup.closure ({a, b, x} : Set G)) :
    ⁅u, v⁆ ∈ Subgroup.closure ({a, b} : Set G) := by
  set H := Subgroup.closure ({a, b} : Set G) with hH
  have hxH : ∀ h ∈ H, Commute h x := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    | one => exact Commute.one_left x
    | mul y z _ _ hy hz => exact hy.mul_left hz
    | inv y _ hy => exact hy.inv_left
  have key : ∀ g ∈ Subgroup.closure ({a, b, x} : Set G), ∃ h ∈ H, ∃ k : ℤ, g = h * x ^ k := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with h | h | h
      · exact ⟨y, Subgroup.subset_closure (by rw [h]; exact Set.mem_insert _ _), 0,
          by rw [zpow_zero, mul_one]⟩
      · exact ⟨y, Subgroup.subset_closure (by rw [h]; exact Set.mem_insert_of_mem _ rfl), 0,
          by rw [zpow_zero, mul_one]⟩
      · exact ⟨1, H.one_mem, 1, by rw [zpow_one, one_mul, h]⟩
    | one => exact ⟨1, H.one_mem, 0, by rw [zpow_zero, mul_one]⟩
    | mul y z _ _ hy hz =>
      obtain ⟨h₁, hh₁, k₁, rfl⟩ := hy
      obtain ⟨h₂, hh₂, k₂, rfl⟩ := hz
      refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ + k₂, ?_⟩
      have c : h₂ * x ^ k₁ = x ^ k₁ * h₂ := ((hxH h₂ hh₂).zpow_right k₁).eq
      rw [zpow_add, show h₁ * x ^ k₁ * (h₂ * x ^ k₂) = h₁ * (x ^ k₁ * h₂) * x ^ k₂ by group, ← c]
      group
    | inv y _ hy =>
      obtain ⟨h, hh, k, rfl⟩ := hy
      refine ⟨h⁻¹, H.inv_mem hh, -k, ?_⟩
      have c : h⁻¹ * x ^ (-k) = x ^ (-k) * h⁻¹ := (((hxH h hh).inv_left).zpow_right (-k)).eq
      rw [mul_inv_rev, ← zpow_neg, c]
  obtain ⟨h₁, hh₁, k, rfl⟩ := key u hu
  obtain ⟨h₂, hh₂, l, rfl⟩ := key v hv
  have c₁ : h₁ * x ^ l = x ^ l * h₁ := ((hxH h₁ hh₁).zpow_right l).eq
  have c₂ : h₂ * x ^ k = x ^ k * h₂ := ((hxH h₂ hh₂).zpow_right k).eq
  have e : ⁅h₁ * x ^ k, h₂ * x ^ l⁆ = ⁅h₁, h₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def,
      show h₁ * x ^ k * (h₂ * x ^ l) * (h₁ * x ^ k)⁻¹ * (h₂ * x ^ l)⁻¹ =
        h₁ * (x ^ k * h₂) * x ^ l * x ^ (-k) * h₁⁻¹ * x ^ (-l) * h₂⁻¹ by
          simp only [mul_inv_rev, zpow_neg]; group,
      ← c₂, show h₁ * (h₂ * x ^ k) * x ^ l * x ^ (-k) * h₁⁻¹ * x ^ (-l) * h₂⁻¹ =
        h₁ * h₂ * x ^ l * h₁⁻¹ * x ^ (-l) * h₂⁻¹ by
          rw [show h₁ * (h₂ * x ^ k) * x ^ l * x ^ (-k) = h₁ * h₂ * (x ^ k * x ^ l * x ^ (-k)) by
            group, ← zpow_add, ← zpow_add, show k + l + -k = l by ring],
      show h₁ * h₂ * x ^ l * h₁⁻¹ * x ^ (-l) * h₂⁻¹ = h₁ * h₂ * (x ^ l * h₁⁻¹) * x ^ (-l) * h₂⁻¹ by
        group]
    have c₁' : x ^ l * h₁⁻¹ = h₁⁻¹ * x ^ l := (((hxH h₁ hh₁).inv_left).zpow_right l).eq.symm
    rw [c₁']
    group
  rw [e, commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)

private def hlTabs : Array (Array ℕ) :=
  #[comp 64 (mat64 (sD ())) (comp 64 (mat64 (sB2 ())) (comp 64 (mat64 (sB3 ())) (mat64 (sB3 ())))),
    comp 64 (mat64 (sB2 ())) (comp 64 (mat64 (sB2 ())) (comp 64 (mat64 (sB3 ())) (mat64 (sB3 ()))))]

private def oEnum : Enum := enumBFS 64 (matTabs.push (mat64 (sTau ()))) 51840

private structure SuzFacts : Prop where
  validH : validA 1782 (sH ()) = true
  inPH : inP (levels ()) (sH ()) = true
  validD : validA 1782 (sD ()) = true
  validB2 : validA 1782 (sB2 ()) = true
  validB3 : validA 1782 (sB3 ()) = true
  validM : validA 1782 (sM ()) = true
  inPM : inP (levels ()) (sM ()) = true
  inPB2 : inP (levels ()) (sB2 ()) = true
  inPB3 : inP (levels ()) (sB3 ()) = true
  validXA : validA 1782 (xAArr (levels ())) = true
  conjD : eqA 1782 (sD ()) (conj1782 (sH ()) (invCand 1782 (sH ())) (xAArr (levels ()))) = true
  tD : comm1782 tTab (sD ()) = true
  tB2 : comm1782 tTab (sB2 ()) = true
  tB3 : comm1782 tTab (sB3 ()) = true
  tTau : comm1782 tTab (sTau ()) = true
  dB2 : comm1782 (sD ()) (sB2 ()) = true
  dB3 : comm1782 (sD ()) (sB3 ()) = true
  b2B3 : comm1782 (sB2 ()) (sB3 ()) = true
  powD : eqA 1782 (CFSG.Monster.B.Mathieu.powArr 1782 (sD ()) 3) (idA 1782) = true
  powB2 : eqA 1782 (CFSG.Monster.B.Mathieu.powArr 1782 (sB2 ()) 3) (idA 1782) = true
  powB3 : eqA 1782 (CFSG.Monster.B.Mathieu.powArr 1782 (sB3 ()) 3) (idA 1782) = true
  indep : allBelow 27 (fun t => t == 0 || !(eqA 1782 (compA 1782
    (CFSG.Monster.B.Mathieu.powArr 1782 (sD ()) (t % 3))
    (compA 1782 (CFSG.Monster.B.Mathieu.powArr 1782 (sB2 ()) (t / 3 % 3))
      (CFSG.Monster.B.Mathieu.powArr 1782 (sB3 ()) (t / 9)))) (idA 1782))) = true
  coordsD : coordsOK (sD ()) = true
  coordsB2 : coordsOK (sB2 ()) = true
  coordsB3 : coordsOK (sB3 ()) = true
  coordsTau : coordsOK (sTau ()) = true
  validMD : validA 64 (mat64 (sD ())) = true
  validMB2 : validA 64 (mat64 (sB2 ())) = true
  validMB3 : validA 64 (mat64 (sB3 ())) = true
  validMT : validA 64 (mat64 (sTau ())) = true
  hlCube : allBelow hlTabs.size (fun k => comp 64 hlTabs[k]! (comp 64 hlTabs[k]! hlTabs[k]!) ==
    idTab 64) = true
  enumO : enumOK 64 (matTabs.push (mat64 (sTau ()))) oEnum = true
  sizeO : (oEnum.tabs.size == 51840) = true
  invO : allBelow oEnum.tabs.size (fun k => invTest hlTabs oEnum.tabs[k]!) = true
  tauOut : (!(matEnum.tabs.any fun x => x == mat64 (sTau ()))) = true
  centOm : allBelow matEnum.tabs.size (fun k => !(comm64 matEnum.tabs[k]! (mat64 (sD ()))) ||
    pow12 matEnum.tabs[k]! == idTab 64) = true
  r0 : allBelow 128 (fun j => comm1782 (sD ()) qElts[j]! == ((mat64 (sD ()))[j / 2]! == j / 2)) =
    true
  nondeg : allBelow 64 (fun v => v == 0 || (mat64 (sD ()))[v]! != v || anyBelow 64 fun w =>
    (mat64 (sD ()))[w]! == w && (gammaBit v w + gammaBit w v) % 2 == 1) = true
  fixCount : (countBelow 64 (fun v => (mat64 (sD ()))[v]! == v) == 16) = true

section Facts


private theorem suzFacts : SuzFacts := by
  have h := Certificates.certificate810302
  simp only [suzCheck, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38,
    h39⟩

local notation "PH" => permOfArr 1782 (sH ())
local notation "PD" => permOfArr 1782 (sD ())
local notation "PB₂" => permOfArr 1782 (sB2 ())
local notation "PB₃" => permOfArr 1782 (sB3 ())
local notation "PM" => permOfArr 1782 (sM ())

private theorem rep_H : Rep 1782 (sH ()) PH := rep_of_validA suzFacts.validH

private theorem rep_Hi : Rep 1782 (invCand 1782 (sH ())) PH⁻¹ := rep_inv_of_validA suzFacts.validH

private theorem rep_D : Rep 1782 (sD ()) PD := rep_of_validA suzFacts.validD

private theorem rep_B2 : Rep 1782 (sB2 ()) PB₂ := rep_of_validA suzFacts.validB2

private theorem rep_B3 : Rep 1782 (sB3 ()) PB₃ := rep_of_validA suzFacts.validB3

private theorem rep_M : Rep 1782 (sM ()) PM := rep_of_validA suzFacts.validM

private theorem rep_XA : Rep 1782 (xAArr (levels ())) fuseXA := rep_of_validA suzFacts.validXA

private theorem rep_Tau : Rep 1782 (sTau ()) (suzV * PM) := by
  rw [sTau]
  exact rep_compA CFSG.Sporadic.SuzOddCore.rep_v rep_M

theorem hP_mem : PH ∈ suzM := mem_suzM_of_inP rep_H suzFacts.inPH

theorem dP_eq : PD = PH * fuseXA * PH⁻¹ := by
  have h : Rep 1782 (conj1782 (sH ()) (invCand 1782 (sH ())) (xAArr (levels ())))
      (PH * fuseXA * PH⁻¹) := by
    rw [mul_assoc]
    exact rep_compA rep_H (rep_compA rep_XA rep_Hi)
  exact eq_of_eqA rep_D h suzFacts.conjD

private theorem fuseXA_mem_suzM : fuseXA ∈ suzM := by
  have F := caseA_facts
  have rA : Rep 1782 (aStrong ())[0]! (permOfArr 1782 (aStrong ())[0]!) := rep_of_validA F.vala
  have rB : Rep 1782 (aStrong ())[1]! (permOfArr 1782 (aStrong ())[1]!) := rep_of_validA F.valb
  have rX : Rep 1782 (aStrong ())[2]! fuseXA := rep_of_eqA_left rep_XA F.eqx
  have hchain := F.chain
  have hsu := F.siftu
  have hsv := F.siftv
  rw [← aBs_map] at hchain hsu hsv
  have hk : 3 ≤ (aStrong ()).size := by rw [F.size]; norm_num
  have hU := CFSG.RankThree.PartOne.mem_closure_three_of_siftG (by norm_num) hk aBs_nodup rA rB
    rX hchain (rep_of_validA F.valu) hsu
  have hV := CFSG.RankThree.PartOne.mem_closure_three_of_siftG (by norm_num) hk aBs_nodup rA rB
    rX hchain (rep_of_validA F.valv) hsv
  have hc : ⁅permOfArr 1782 (rebuild (levels ()) vTuple),
      permOfArr 1782 (rebuild (levels ()) uTuple)⁆ = fuseXA :=
    eq_of_eqA (rep_commutatorA F.valv F.valu) rep_XA F.comm
  have hle : Subgroup.closure ({permOfArr 1782 (aStrong ())[0]!, permOfArr 1782 (aStrong ())[1]!} :
      Set (Equiv.Perm (Fin 1782))) ≤ suzM := by
    rw [Subgroup.closure_le]
    intro g hg
    rcases hg with h | h
    · rw [h]
      exact mem_suzM_of_inP rA F.ina
    · rw [Set.mem_singleton_iff.1 h]
      exact mem_suzM_of_inP rB F.inb
  rw [← hc]
  exact hle (commutator_mem_closure_pair ((commA_iff rA rep_XA).1 F.comma)
    ((commA_iff rB rep_XA).1 F.commb) hV hU)

private theorem mem_invE {t : Array ℕ} {G : Equiv.Perm (Fin 1782)} (ht : Rep 1782 t G)
    (hG : G ∈ suzM) (hc : comm1782 tTab t = true) : G ∈ invE 1 := by
  rw [invE_eq_centM (by norm_num)]
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
    ((comm1782_iff rep_tTab ht).1 hc).eq.symm, hG⟩

theorem gens_mem : PD ∈ invE 1 ∧ PB₂ ∈ invE 1 ∧ PB₃ ∈ invE 1 ∧ PM ∈ suzM := by
  have F := suzFacts
  have hD : PD ∈ suzM := by
    rw [dP_eq]
    exact suzM.mul_mem (suzM.mul_mem hP_mem fuseXA_mem_suzM) (suzM.inv_mem hP_mem)
  exact ⟨mem_invE rep_D hD F.tD, mem_invE rep_B2 (mem_suzM_of_inP rep_B2 F.inPB2) F.tB2,
    mem_invE rep_B3 (mem_suzM_of_inP rep_B3 F.inPB3) F.tB3, mem_suzM_of_inP rep_M F.inPM⟩

theorem commute_facts : Commute PD PB₂ ∧ Commute PD PB₃ ∧ Commute PB₂ PB₃ ∧
    Commute (suzInv 1) (suzV * PM) := by
  have F := suzFacts
  exact ⟨(comm1782_iff rep_D rep_B2).1 F.dB2, (comm1782_iff rep_D rep_B3).1 F.dB3,
    (comm1782_iff rep_B2 rep_B3).1 F.b2B3, (comm1782_iff rep_tTab rep_Tau).1 F.tTau⟩

theorem pow_facts : PD ^ 3 = 1 ∧ PB₂ ^ 3 = 1 ∧ PB₃ ^ 3 = 1 := by
  have F := suzFacts
  exact ⟨eq_of_eqA (CFSG.Monster.B.Mathieu.rep_powArr rep_D 3) rep_idA F.powD,
    eq_of_eqA (CFSG.Monster.B.Mathieu.rep_powArr rep_B2 3) rep_idA F.powB2,
    eq_of_eqA (CFSG.Monster.B.Mathieu.rep_powArr rep_B3 3) rep_idA F.powB3⟩

private theorem indep_spec (t : ℕ) (ht : t < 27) :
    t = 0 ∨ PD ^ (t % 3) * (PB₂ ^ (t / 3 % 3) * PB₃ ^ (t / 9)) ≠ 1 := by
  have h := allBelow_eq_true.1 suzFacts.indep t ht
  have hr := rep_compA (CFSG.Monster.B.Mathieu.rep_powArr rep_D (t % 3))
    (rep_compA (CFSG.Monster.B.Mathieu.rep_powArr rep_B2 (t / 3 % 3))
      (CFSG.Monster.B.Mathieu.rep_powArr rep_B3 (t / 9)))
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr fun e => ?_
    rw [(eqA_iff hr rep_idA).2 e] at h
    exact Bool.noConfusion h

theorem indep_facts : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 → PD ^ i * PB₂ ^ j * PB₃ ^ k = 1 →
    i = 0 ∧ j = 0 ∧ k = 0 := by
  intro i j k hi hj hk h
  rcases indep_spec (i + 3 * j + 9 * k) (by omega) with h0 | h0
  · omega
  · exfalso
    apply h0
    rw [show (i + 3 * j + 9 * k) % 3 = i by omega, show (i + 3 * j + 9 * k) / 3 % 3 = j by omega,
      show (i + 3 * j + 9 * k) / 9 = k by omega, ← mul_assoc]
    exact h

private theorem find?_getD_spec {n : ℕ} {p : ℕ → Bool} (h : ((List.range n).find? p).getD n < n) :
    p (((List.range n).find? p).getD n) = true := by
  cases hf : (List.range n).find? p with
  | none => rw [hf] at h; simp at h
  | some j => exact List.find?_some hf

private theorem qIdx_spec {c ci : Array ℕ} {i : ℕ} (h : qIdx c ci i < 128) :
    eqA 1782 (conj1782 c ci (qArr i)) qElts[qIdx c ci i]! = true :=
  find?_getD_spec (n := 128) (p := fun j => eqA 1782 (conj1782 c ci (qArr i)) qElts[j]!) h

private theorem conj_qGen {c : Array ℕ} {C : Equiv.Perm (Fin 1782)} (hc : Rep 1782 c C) {i : ℕ}
    (hi : i < 6) (h : qIdx c (invCand 1782 c) i < 128) :
    C * qGen i * C⁻¹ = qVec (qIdx c (invCand 1782 c) i / 2) *
      suzInv 1 ^ (qIdx c (invCand 1782 c) i % 2) := by
  have h1 : Rep 1782 (conj1782 c (invCand 1782 c) (qArr i)) (C * qGen i * C⁻¹) := by
    rw [mul_assoc]
    exact rep_compA hc (rep_compA (rep_qArr hi) (rep_invCand_gen hc))
  have h2 : Rep 1782 qElts[qIdx c (invCand 1782 c) i]! (qVec (qIdx c (invCand 1782 c) i / 2) *
      suzInv 1 ^ (qIdx c (invCand 1782 c) i % 2)) := by
    rw [qElts_get h]
    exact rep_compA (rep_qProds (by omega)) (rep_tPow (Nat.mod_lt _ (by norm_num)))
  exact eq_of_eqA h1 h2 (qIdx_spec h)

private theorem conj_foldl {C : Equiv.Perm (Fin 1782)} {w : ℕ → ℕ} (hw : ∀ i < 6, w i < 64)
    {b : ℕ → ℕ} (hC : ∀ i < 6, C * qGen i * C⁻¹ = qVec (w i) * suzInv 1 ^ b i) (v : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < 6) → ∀ (g : Equiv.Perm (Fin 1782)) (s a : ℕ), s < 64 →
      C * g * C⁻¹ = qVec s * suzInv 1 ^ a →
      l.foldl (fun r i => if v.testBit i then r ^^^ w i else r) s < 64 ∧ ∃ a' : ℕ,
        C * l.foldl (fun r i => if v.testBit i then r * qGen i else r) g * C⁻¹ =
          qVec (l.foldl (fun r i => if v.testBit i then r ^^^ w i else r) s) * suzInv 1 ^ a'
  | [], _, _, _, a, hs, h => ⟨hs, a, h⟩
  | i :: l, hl, g, s, a, hs, h => by
    have hi := hl i List.mem_cons_self
    have hl' : ∀ j ∈ l, j < 6 := fun j hj => hl j (List.mem_cons_of_mem i hj)
    simp only [List.foldl_cons]
    by_cases hv : v.testBit i = true
    · rw [if_pos hv, if_pos hv]
      refine conj_foldl hw hC v l hl' (g * qGen i) (s ^^^ w i) ((gammaBit s (w i) + a + b i) % 2)
        (xor_lt hs (hw i hi)) ?_
      rw [show C * (g * qGen i) * C⁻¹ = C * g * C⁻¹ * (C * qGen i * C⁻¹) by group, h, hC i hi,
        coord_qVec.mul_mul hs (hw i hi)]
    · rw [if_neg hv, if_neg hv]
      exact conj_foldl hw hC v l hl' g s a hs h

private theorem mat64_get (c : Array ℕ) {v : ℕ} (hv : v < 64) :
    (mat64 c)[v]! = (List.range 6).foldl
      (fun r i => if v.testBit i then r ^^^ qIdx c (invCand 1782 c) i / 2 else r) 0 := by
  simp only [mat64]
  rw [getElem!_ofFn' _ hv]
  refine List.foldl_ext _ _ _ fun r i hi => ?_
  have hi6 : i < 6 := List.mem_range.1 hi
  rw [getElem!_pos _ i (by simpa using hi6), Array.getElem_map, Array.getElem_range]

private theorem conj_qVec_of_coordsOK {c : Array ℕ} {C : Equiv.Perm (Fin 1782)}
    (hc : Rep 1782 c C) (hok : coordsOK c = true) :
    ∀ v < 64, (mat64 c)[v]! < 64 ∧ ∃ a < 2,
      C * qVec v * C⁻¹ = qVec (mat64 c)[v]! * suzInv 1 ^ a := by
  have hlt : ∀ i < 6, qIdx c (invCand 1782 c) i < 128 := by
    intro i hi
    have := allBelow_eq_true.1 hok i hi
    simpa using this
  intro v hv
  obtain ⟨hlt64, a, ha⟩ := conj_foldl (C := C) (w := fun i => qIdx c (invCand 1782 c) i / 2)
    (fun i hi => by have := hlt i hi; omega) (fun i hi => conj_qGen hc hi (hlt i hi)) v
    (List.range 6) (fun i hi => List.mem_range.1 hi) 1 0 0 (by norm_num)
    (by rw [mul_one, mul_inv_cancel, coord_qVec.q_zero, pow_zero, mul_one])
  beta_reduce at hlt64 ha
  rw [← mat64_get c hv] at hlt64 ha
  refine ⟨hlt64, a % 2, Nat.mod_lt _ (by norm_num), ?_⟩
  rw [← coord_qVec.t_pow_mod]
  exact ha

private theorem mat64_size (c : Array ℕ) : (mat64 c).size = 64 := by
  simp [mat64]

private theorem tabRep_mat64 {c : Array ℕ} (h : validA 64 (mat64 c) = true) :
    TabRep (mat64 c) (permOfArr 64 (mat64 c)) :=
  ⟨mat64_size c, rep_of_validA h⟩

theorem conj_qVec_facts :
    (∀ v < 64, (mat64 (sD ()))[v]! < 64 ∧ ∃ a < 2,
      PD * qVec v * PD⁻¹ = qVec (mat64 (sD ()))[v]! * suzInv 1 ^ a) ∧
    (∀ v < 64, (mat64 (sB2 ()))[v]! < 64 ∧ ∃ a < 2,
      PB₂ * qVec v * PB₂⁻¹ = qVec (mat64 (sB2 ()))[v]! * suzInv 1 ^ a) ∧
    (∀ v < 64, (mat64 (sB3 ()))[v]! < 64 ∧ ∃ a < 2,
      PB₃ * qVec v * PB₃⁻¹ = qVec (mat64 (sB3 ()))[v]! * suzInv 1 ^ a) ∧
    (∀ v < 64, (mat64 (sTau ()))[v]! < 64 ∧ ∃ a < 2,
      suzV * PM * qVec v * (suzV * PM)⁻¹ = qVec (mat64 (sTau ()))[v]! * suzInv 1 ^ a) ∧
    (∀ t ∈ [mat64 (sD ()), mat64 (sB2 ()), mat64 (sB3 ()), mat64 (sTau ())],
      Rep 64 t (permOfArr 64 t)) := by
  have F := suzFacts
  refine ⟨conj_qVec_of_coordsOK rep_D F.coordsD, conj_qVec_of_coordsOK rep_B2 F.coordsB2,
    conj_qVec_of_coordsOK rep_B3 F.coordsB3, conj_qVec_of_coordsOK rep_Tau F.coordsTau, ?_⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact rep_of_validA F.validMD
  · exact rep_of_validA F.validMB2
  · exact rep_of_validA F.validMB3
  · exact rep_of_validA F.validMT

private theorem tabRep_matTabs {j : ℕ} (hj : j < 10) :
    TabRep matTabs[j]! (permOfArr 64 matTabs[j]!) := by
  obtain ⟨g, hg, hrep⟩ := rep_gen hj
  have h := tabRep_gen hj ⟨g, Subgroup.subset_closure hg⟩ hrep
  rw [permOfArr_eq_of_rep h.2]
  exact h

private theorem oGens_size : (matTabs.push (mat64 (sTau ()))).size = 11 := by
  rw [Array.size_push, matTabs_size]

private theorem oGens_get_lt {j : ℕ} (hj : j < 10) :
    (matTabs.push (mat64 (sTau ())))[j]! = matTabs[j]! := by
  rw [getElem!_pos _ j (by rw [oGens_size]; omega),
    getElem!_pos _ j (by rw [matTabs_size]; exact hj), Array.getElem_push_lt]

private theorem oGens_get_ten : (matTabs.push (mat64 (sTau ())))[10]! = mat64 (sTau ()) := by
  have h : matTabs.size = 10 := matTabs_size
  rw [getElem!_pos _ 10 (by rw [oGens_size]; omega)]
  simp only [Array.getElem_push, h, lt_self_iff_false, dite_false]

private theorem tabRep_oGens {j : ℕ} (hj : j < 11) :
    TabRep (matTabs.push (mat64 (sTau ())))[j]!
      (permOfArr 64 (matTabs.push (mat64 (sTau ())))[j]!) := by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [oGens_get_lt hj]
    exact tabRep_matTabs hj
  · rw [oGens_get_ten]
    exact tabRep_mat64 suzFacts.validMT

private theorem enumerates_of_tabRep {gens : Array (Array ℕ)} {m : ℕ} (hm : gens.size = m)
    {E : Enum} (hgen : ∀ j < m, TabRep gens[j]! (permOfArr 64 gens[j]!))
    (h : enumOK 64 gens E = true) :
    Enumerates (Subgroup.closure (Set.range fun j : Fin m => permOfArr 64 gens[(j : ℕ)]!))
      E.tabs.toList := by
  refine enumerates_closure ?_ ?_ h
  · rintro _ ⟨j, rfl⟩
    exact ⟨j, by rw [hm]; exact j.2, hgen j j.2⟩
  · intro j hj
    rw [hm] at hj
    exact ⟨_, ⟨⟨j, hj⟩, rfl⟩, hgen j hj⟩

private theorem oEnumerates : Enumerates (Subgroup.closure (Set.range fun j : Fin 11 =>
    permOfArr 64 (matTabs.push (mat64 (sTau ())))[(j : ℕ)]!)) oEnum.tabs.toList :=
  enumerates_of_tabRep oGens_size (fun _ hj => tabRep_oGens hj) suzFacts.enumO

private theorem omEnumerates : Enumerates (Subgroup.closure (Set.range fun j : Fin 10 =>
    permOfArr 64 matTabs[(j : ℕ)]!)) matEnum.tabs.toList :=
  enumerates_of_tabRep matTabs_size (fun _ hj => tabRep_matTabs hj) b0_parts.2.2.2.2.1

private theorem invTest_spec {HL : Array (Array ℕ)} {Y : ℕ → Equiv.Perm (Fin 64)}
    (hY : ∀ k < HL.size, TabRep HL[k]! (Y k)) (hY3 : ∀ k < HL.size, Y k * (Y k * Y k) = 1)
    {t : Array ℕ} {G : Equiv.Perm (Fin 64)} (hG : TabRep t G) (h : invTest HL t = true)
    (hGG : G * G = 1) (hG1 : G ≠ 1) : ∃ k < HL.size, ¬ Commute G (Y k * G * (Y k)⁻¹) := by
  have e1 : (comp 64 t t == idTab 64) = true := ((hG.comp hG).beq_iff TabRep.idTab).2 hGG
  have e2 : (t == idTab 64) = false := by
    cases h2 : (t == idTab 64)
    · rfl
    · exact absurd ((hG.beq_iff TabRep.idTab).1 h2) hG1
  simp only [invTest, e1, e2, Bool.not_true, Bool.false_or] at h
  obtain ⟨k, hk, hc⟩ := anyBelow_eq_true.1 h
  refine ⟨k, hk, fun hcomm => ?_⟩
  have hYk := hY k hk
  have hinv : (Y k)⁻¹ = Y k * Y k := inv_eq_of_mul_eq_one_right (hY3 k hk)
  have hb : TabRep (comp 64 HL[k]! (comp 64 t (comp 64 HL[k]! HL[k]!))) (Y k * G * (Y k)⁻¹) := by
    rw [hinv, mul_assoc]
    exact hYk.comp (hG.comp (hYk.comp hYk))
  have hc' : comm64 t (comp 64 HL[k]! (comp 64 t (comp 64 HL[k]! HL[k]!))) = true :=
    ((hG.comp hb).beq_iff (hb.comp hG)).2 hcomm.eq
  rw [hc'] at hc
  exact absurd hc (by decide)

private def hlY (k : ℕ) : Equiv.Perm (Fin 64) :=
  if k = 0 then permOfArr 64 (mat64 (sD ())) * (permOfArr 64 (mat64 (sB2 ())) *
    (permOfArr 64 (mat64 (sB3 ())) * permOfArr 64 (mat64 (sB3 ()))))
  else permOfArr 64 (mat64 (sB2 ())) * (permOfArr 64 (mat64 (sB2 ())) *
    (permOfArr 64 (mat64 (sB3 ())) * permOfArr 64 (mat64 (sB3 ()))))

private theorem hlTabs_size : hlTabs.size = 2 := by
  simp [hlTabs]

private theorem tabRep_hl {k : ℕ} (hk : k < hlTabs.size) : TabRep hlTabs[k]! (hlY k) := by
  have F := suzFacts
  have hD := tabRep_mat64 F.validMD
  have hB2 := tabRep_mat64 F.validMB2
  have hB3 := tabRep_mat64 F.validMB3
  rw [hlTabs_size] at hk
  interval_cases k
  · rw [show hlTabs[0]! = comp 64 (mat64 (sD ())) (comp 64 (mat64 (sB2 ()))
      (comp 64 (mat64 (sB3 ())) (mat64 (sB3 ())))) by simp [hlTabs], hlY, if_pos rfl]
    exact hD.comp (hB2.comp (hB3.comp hB3))
  · rw [show hlTabs[1]! = comp 64 (mat64 (sB2 ())) (comp 64 (mat64 (sB2 ()))
      (comp 64 (mat64 (sB3 ())) (mat64 (sB3 ())))) by simp [hlTabs], hlY, if_neg (by norm_num)]
    exact hB2.comp (hB2.comp (hB3.comp hB3))

private theorem hl_cube {k : ℕ} (hk : k < hlTabs.size) : hlY k * (hlY k * hlY k) = 1 :=
  (((tabRep_hl hk).comp ((tabRep_hl hk).comp (tabRep_hl hk))).beq_iff TabRep.idTab).1
    (allBelow_eq_true.1 suzFacts.hlCube k hk)

private theorem hlY_zero : hlY 0 = permOfArr 64 (mat64 (sD ())) * permOfArr 64 (mat64 (sB2 ())) *
    permOfArr 64 (mat64 (sB3 ())) ^ 2 := by
  rw [hlY, if_pos rfl, sq, mul_assoc]

private theorem hlY_one :
    hlY 1 = permOfArr 64 (mat64 (sB2 ())) ^ 2 * permOfArr 64 (mat64 (sB3 ())) ^ 2 := by
  rw [hlY, if_neg (by norm_num), sq, sq, mul_assoc]

theorem six4_facts :
    ∀ g ∈ Subgroup.closure (Set.range fun j : Fin 11 =>
      permOfArr 64 (matTabs.push (mat64 (sTau ())))[(j : ℕ)]!), g * g = 1 → g ≠ 1 →
      ∃ y ∈ ({permOfArr 64 (mat64 (sD ())) * permOfArr 64 (mat64 (sB2 ())) *
          permOfArr 64 (mat64 (sB3 ())) ^ 2,
        permOfArr 64 (mat64 (sB2 ())) ^ 2 * permOfArr 64 (mat64 (sB3 ())) ^ 2} :
          Set (Equiv.Perm (Fin 64))), ¬ Commute g (y * g * y⁻¹) := by
  intro g hg hgg hg1
  obtain ⟨k, hk, hrep⟩ := oEnumerates.exists_pos hg
  obtain ⟨k', hk', hc⟩ := invTest_spec (fun _ hk => tabRep_hl hk) (fun _ hk => hl_cube hk) hrep
    (allBelow_eq_true.1 suzFacts.invO k hk) hgg hg1
  rw [hlTabs_size] at hk'
  interval_cases k'
  · refine ⟨hlY 0, ?_, hc⟩
    rw [hlY_zero]
    exact Set.mem_insert _ _
  · refine ⟨hlY 1, ?_, hc⟩
    rw [hlY_one]
    exact Set.mem_insert_of_mem _ rfl

theorem tau_not_mem_omega : permOfArr 64 (mat64 (sTau ())) ∉
    Subgroup.closure (Set.range fun j : Fin 10 => permOfArr 64 matTabs[(j : ℕ)]!) := by
  intro hmem
  obtain ⟨t, ht, hrep⟩ := omEnumerates.complete _ hmem
  have he : t = mat64 (sTau ()) := hrep.tab_eq (tabRep_mat64 suzFacts.validMT)
  have hany : (matEnum.tabs.any fun x => x == mat64 (sTau ())) = true := by
    rw [← Array.any_toList, List.any_eq_true]
    exact ⟨t, ht, by rw [he, beq_self_eq_true]⟩
  have h := suzFacts.tauOut
  rw [hany] at h
  exact absurd h (by decide)

private theorem tabRep_pow12 {t : Array ℕ} {G : Equiv.Perm (Fin 64)} (ht : TabRep t G) :
    TabRep (pow12 t) (G ^ 12) := by
  have h2 : TabRep (comp 64 t t) (G ^ 2) := by
    rw [sq]
    exact ht.comp ht
  have h4 : TabRep (comp 64 (comp 64 t t) (comp 64 t t)) (G ^ 4) := by
    rw [show G ^ 4 = G ^ 2 * G ^ 2 by rw [← pow_add]]
    exact h2.comp h2
  have h12 := h4.comp (h4.comp h4)
  rw [← pow_add, ← pow_add, show 4 + (4 + 4) = 12 by norm_num] at h12
  exact h12

theorem omega_cent_facts : ∀ g ∈ Subgroup.closure (Set.range fun j : Fin 10 =>
    permOfArr 64 matTabs[(j : ℕ)]!), Commute g (permOfArr 64 (mat64 (sD ()))) → g ^ 12 = 1 := by
  intro g hg hc
  obtain ⟨k, hk, hrep⟩ := omEnumerates.exists_pos hg
  have h := allBelow_eq_true.1 suzFacts.centOm k hk
  have hD := tabRep_mat64 suzFacts.validMD
  have hcomm : comm64 matEnum.tabs[k]! (mat64 (sD ())) = true :=
    ((hrep.comp hD).beq_iff (hD.comp hrep)).2 hc.eq
  rw [hcomm, Bool.not_true, Bool.false_or] at h
  exact ((tabRep_pow12 hrep).beq_iff TabRep.idTab).1 h

theorem r0_facts :
    (∀ v < 64, ∀ a < 2, Commute PD (qVec v * suzInv 1 ^ a) ↔ (mat64 (sD ()))[v]! = v) ∧
    ∀ v < 64, v ≠ 0 → (mat64 (sD ()))[v]! = v → ∃ w < 64, (mat64 (sD ()))[w]! = w ∧
      (gammaBit v w + gammaBit w v) % 2 = 1 := by
  refine ⟨fun v hv a ha => ?_, fun v hv hv0 hfix => ?_⟩
  · have hj : 2 * v + a < 128 := by omega
    have h := allBelow_eq_true.1 suzFacts.r0 _ hj
    have e1 : (2 * v + a) / 2 = v := by omega
    have e2 : (2 * v + a) % 2 = a := by omega
    rw [e1] at h
    have hr : Rep 1782 qElts[2 * v + a]! (qVec v * suzInv 1 ^ a) := by
      rw [qElts_get hj, e1, e2]
      exact rep_compA (rep_qProds hv) (rep_tPow ha)
    rw [← comm1782_iff rep_D hr, beq_iff_eq.1 h, beq_iff_eq]
  · have h := allBelow_eq_true.1 suzFacts.nondeg v hv
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, anyBelow_eq_true,
      Bool.and_eq_true] at h
    rcases h with (h | h) | ⟨w, hw, h1, h2⟩
    · exact absurd h hv0
    · exact absurd hfix h
    · exact ⟨w, hw, h1, h2⟩

theorem r0_card : ((Finset.range 64).filter fun v => (mat64 (sD ()))[v]! = v).card = 16 := by
  have h := beq_iff_eq.1 suzFacts.fixCount
  rw [countBelow_eq] at h
  rw [Finset.filter_congr (q := fun v => ((mat64 (sD ()))[v]! == v) = true)
    (fun x _ => beq_iff_eq.symm)]
  exact h

end Facts

end CFSG.Sporadic.SuzI301.SpecAux
