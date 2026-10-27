module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 Equiv

@[expose] def wv (s : List (Fin 6)) : Wr 6 := ⟨v6 s, 1⟩

@[expose] def wp (σ : Perm (Fin 6)) : Wr 6 := ⟨0, σ⟩

@[expose] def wPi3 : Wr 6 := wv [4, 5]

@[expose] def wPi12 : Wr 6 := wv [0, 1, 2, 3]

@[expose] def wMu : Wr 6 := wv [0, 2]

@[expose] def wMu' : Wr 6 := wv [0, 4]

@[expose] def wTau : Wr 6 := wp (swap 0 2 * swap 1 3)

@[expose] def wXi : Wr 6 := wp (swap 0 4 * swap 0 2 * (swap 1 5 * swap 1 3))

@[expose] def blk (i : Fin 6) : Fin 3 := ![0, 0, 1, 1, 2, 2] i

@[expose] def partner (i : Fin 6) : Fin 6 := ![1, 0, 3, 2, 5, 4] i

theorem partner_partner : ∀ i, partner (partner i) = i := by decide

theorem blk_partner : ∀ i, blk (partner i) = blk i := by decide

@[expose] def swapsOf (d : Fin 3 → ZMod 2) : Perm (Fin 6) :=
  Function.Involutive.toPerm (fun i => if d (blk i) = 1 then partner i else i) (by
    intro i
    by_cases h : d (blk i) = 1
    · simp only [h, if_true, blk_partner, partner_partner]
    · simp only [h, if_false])

@[expose] def cS (c d : Fin 3 → ZMod 2) : Wr 6 := ⟨fun i => c (blk i), swapsOf d⟩

theorem blk_swapsOf (d : Fin 3 → ZMod 2) (i : Fin 6) : blk (swapsOf d i) = blk i := by
  show blk (if d (blk i) = 1 then partner i else i) = blk i
  split_ifs
  · exact blk_partner i
  · rfl

theorem swapsOf_symm : ∀ d : Fin 3 → ZMod 2, (swapsOf d).symm = swapsOf d := by decide

theorem swapsOf_add : ∀ d d' : Fin 3 → ZMod 2, swapsOf (d + d') = swapsOf d * swapsOf d' := by
  decide

theorem swapsOf_zero : swapsOf 0 = 1 := by decide

theorem cS_add (c d c' d' : Fin 3 → ZMod 2) : cS (c + c') (d + d') = cS c d * cS c' d' := by
  refine Wr.ext (funext fun i => ?_) (swapsOf_add d d')
  show c (blk i) + c' (blk i) = c (blk i) + c' (blk ((swapsOf d).symm i))
  rw [swapsOf_symm, blk_swapsOf]

theorem cS_zero : cS 0 0 = 1 := Wr.ext (funext fun _ => rfl) swapsOf_zero

theorem blk_even : ∀ k : Fin 3, blk (![0, 2, 4] k) = k := by decide

theorem swapsOf_even : ∀ (d : Fin 3 → ZMod 2) (k : Fin 3),
    swapsOf d (![0, 2, 4] k) = if d k = 1 then ![1, 3, 5] k else ![0, 2, 4] k := by decide

theorem swapsOf_injective {d d' : Fin 3 → ZMod 2} (h : swapsOf d = swapsOf d') : d = d' := by
  funext k
  have h1 := congrArg (fun σ : Perm (Fin 6) => σ (![0, 2, 4] k)) h
  simp only [swapsOf_even] at h1
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hne : ∀ k : Fin 3, (![1, 3, 5] k : Fin 6) ≠ ![0, 2, 4] k := by decide
  rcases h01 (d k) with hd | hd <;> rcases h01 (d' k) with hd' | hd'
  · rw [hd, hd']
  · rw [hd, hd'] at h1; simp at h1; exact absurd h1.symm (hne k)
  · rw [hd, hd'] at h1; simp at h1; exact absurd h1 (hne k)
  · rw [hd, hd']

theorem cS_injective {c d c' d' : Fin 3 → ZMod 2} (h : cS c d = cS c' d') : c = c' ∧ d = d' := by
  have hv := congrArg Wr.vec h
  have hp := congrArg Wr.perm h
  refine ⟨funext fun k => ?_, swapsOf_injective hp⟩
  have := congrFun hv (![0, 2, 4] k)
  simpa only [cS, blk_even] using this

theorem cS_mem_Wsub : ∀ c d : Fin 3 → ZMod 2, cS c d ∈ Wsub := by
  intro c d
  show ∑ i, c (blk i) = 0
  revert c; decide

abbrev SC : Type := (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)

@[expose] def cSp (x : SC) : Wr 6 := cS x.1 x.2

@[expose] def actMu (x : SC) : SC := (x.1 + ![x.2 0, x.2 1, 0], x.2)

@[expose] def actMu' (x : SC) : SC := (x.1 + ![x.2 0, 0, x.2 2], x.2)

@[expose] def actTau (x : SC) : SC := (![x.1 1, x.1 0, x.1 2], ![x.2 1, x.2 0, x.2 2])

@[expose] def actXi (x : SC) : SC := (![x.1 2, x.1 0, x.1 1], ![x.2 2, x.2 0, x.2 1])

theorem conj_cS_wMu : ∀ x : SC, wMu * cSp x * wMu⁻¹ = cSp (actMu x) := by decide

theorem conj_cS_wMu' : ∀ x : SC, wMu' * cSp x * wMu'⁻¹ = cSp (actMu' x) := by decide

theorem conj_cS_wTau : ∀ x : SC, wTau * cSp x * wTau⁻¹ = cSp (actTau x) := by decide

theorem conj_cS_wXi : ∀ x : SC, wXi * cSp x * wXi⁻¹ = cSp (actXi x) := by decide

@[expose] def InS (a : Wr 6) : Prop :=
  (∀ i, a.vec (partner i) = a.vec i) ∧ ∀ i, a.perm i = i ∨ a.perm i = partner i

instance (a : Wr 6) : Decidable (InS a) := by unfold InS; infer_instance

theorem inS_cSp : ∀ x : SC, InS (cSp x) := by decide

set_option maxRecDepth 100000 in
theorem exists_swapsOf : ∀ σ : Perm (Fin 6), (∀ i, σ i = i ∨ σ i = partner i) →
    ∃ d, σ = swapsOf d := by decide +kernel

theorem exists_blkVec : ∀ v : Fin 6 → ZMod 2, (∀ i, v (partner i) = v i) →
    v = fun i => v (![0, 2, 4] (blk i)) := by decide

theorem exists_cSp_of_inS {a : Wr 6} (h : InS a) : ∃ x : SC, a = cSp x := by
  obtain ⟨d, hd⟩ := exists_swapsOf a.perm h.2
  refine ⟨(fun k => a.vec (![0, 2, 4] k), d), Wr.ext ?_ hd⟩
  exact exists_blkVec a.vec h.1

theorem inS_iff {a : Wr 6} : InS a ↔ ∃ x : SC, a = cSp x :=
  ⟨exists_cSp_of_inS, fun ⟨x, hx⟩ => hx ▸ inS_cSp x⟩

@[expose] def pact (σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 := fun i => v (σ.symm i)

theorem mk_mul_mk (v w : Fin 6 → ZMod 2) (σ τ : Perm (Fin 6)) :
    (⟨v, σ⟩ : Wr 6) * ⟨w, τ⟩ = ⟨v + pact σ w, σ * τ⟩ := rfl

theorem mk_inv (v : Fin 6 → ZMod 2) (σ : Perm (Fin 6)) :
    (⟨v, σ⟩ : Wr 6)⁻¹ = ⟨pact σ⁻¹ v, σ⁻¹⟩ := by
  refine Wr.ext (funext fun i => ?_) rfl
  show v (σ i) = v (σ⁻¹.symm i)
  rfl

theorem conj_wp (π σ : Perm (Fin 6)) (v : Fin 6 → ZMod 2) :
    wp π * ⟨v, σ⟩ * (wp π)⁻¹ = ⟨pact π v, π * σ * π⁻¹⟩ := by
  refine Wr.ext (funext fun i => ?_) rfl
  show (0 : ZMod 2) + v (π.symm i) + 0 = v (π.symm i)
  ring

theorem conj_mkVec (u v : Fin 6 → ZMod 2) (σ : Perm (Fin 6)) :
    (⟨u, 1⟩ : Wr 6) * ⟨v, σ⟩ * (⟨u, 1⟩ : Wr 6)⁻¹ = ⟨u + v + pact σ u, σ⟩ := by
  refine Wr.ext (funext fun i => ?_) (by simp [Wr.mul_perm, Wr.inv_perm])
  show u i + v ((1 : Perm (Fin 6)).symm i) + u ((σ * 1).symm i) = u i + v i + u (σ.symm i)
  rfl

theorem cSp_add (x y : SC) : cSp (x + y) = cSp x * cSp y := cS_add x.1 x.2 y.1 y.2

theorem SC_add_self : ∀ x : SC, x + x = 0 := by decide

theorem cSp_mul_self (x : SC) : cSp x * cSp x = 1 := by
  rw [← cSp_add, SC_add_self]
  exact cS_zero

@[expose] def SW : Subgroup (Wr 6) where
  carrier := {a | InS a}
  mul_mem' {a b} ha hb := by
    obtain ⟨x, rfl⟩ := exists_cSp_of_inS ha
    obtain ⟨y, rfl⟩ := exists_cSp_of_inS hb
    rw [← cSp_add]
    exact inS_cSp _
  one_mem' := by
    rw [show (1 : Wr 6) = cSp 0 from cS_zero.symm]
    exact inS_cSp 0
  inv_mem' {a} ha := by
    obtain ⟨x, rfl⟩ := exists_cSp_of_inS ha
    rw [inv_eq_of_mul_eq_one_right (cSp_mul_self x)]
    exact inS_cSp x

theorem mem_SW {a : Wr 6} : a ∈ SW ↔ InS a := Iff.rfl

theorem cSp_mem_SW (x : SC) : cSp x ∈ SW := inS_cSp x

theorem mem_SW_iff {a : Wr 6} : a ∈ SW ↔ ∃ x : SC, a = cSp x := inS_iff

theorem SW_le_Wsub : SW ≤ Wsub := fun a ha => by
  obtain ⟨x, rfl⟩ := mem_SW_iff.mp ha
  exact cS_mem_Wsub x.1 x.2

theorem SW_comm {a b : Wr 6} (ha : a ∈ SW) (hb : b ∈ SW) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := mem_SW_iff.mp ha
  obtain ⟨y, rfl⟩ := mem_SW_iff.mp hb
  rw [← cSp_add, ← cSp_add, add_comm]

@[expose] def bv (c : Fin 3 → ZMod 2) : Fin 6 → ZMod 2 := fun i => c (blk i)

@[expose] def sw1 (k : Fin 3) : Perm (Fin 6) := swapsOf (fun k' => if k' = k then 1 else 0)

theorem pact_one (v : Fin 6 → ZMod 2) : pact 1 v = v := rfl

theorem pair_of_fix : ∀ σ : Perm (Fin 6), pact σ (bv ![1, 0, 0]) = bv ![1, 0, 0] →
    pact σ (bv ![0, 1, 0]) = bv ![0, 1, 0] → pact σ (bv ![0, 0, 1]) = bv ![0, 0, 1] →
    ∀ i, σ i = i ∨ σ i = partner i := by decide +kernel

theorem pairConst_of_fix : ∀ v : Fin 6 → ZMod 2, (∀ k, pact (sw1 k) v = v) →
    ∀ i, v (partner i) = v i := by decide

theorem mem_SW_of_commute {a : Wr 6} (h : ∀ x : SC, a * cSp x = cSp x * a) : a ∈ SW := by
  obtain ⟨v, σ⟩ := a
  have hvec : ∀ c : Fin 3 → ZMod 2, pact σ (bv c) = bv c := by
    intro c
    have h1 : v + pact σ (bv c) = bv c + pact (swapsOf 0) v := congrArg Wr.vec (h (c, 0))
    rw [swapsOf_zero, pact_one, add_comm (bv c)] at h1
    exact add_left_cancel h1
  have hσ := pair_of_fix σ (hvec _) (hvec _) (hvec _)
  refine ⟨pairConst_of_fix v fun k => ?_, hσ⟩
  have h1 : v + pact σ (bv 0) = bv 0 + pact (sw1 k) v :=
    congrArg Wr.vec (h (0, fun k' => if k' = k then 1 else 0))
  have h0 : bv (0 : Fin 3 → ZMod 2) = 0 := rfl
  have hp0 : pact σ (0 : Fin 6 → ZMod 2) = 0 := rfl
  rw [h0, hp0, add_zero, zero_add] at h1
  exact h1.symm

theorem pact_mul (σ τ : Perm (Fin 6)) (u : Fin 6 → ZMod 2) :
    pact (σ * τ) u = pact σ (pact τ u) := rfl

theorem pact_add (σ : Perm (Fin 6)) (u w : Fin 6 → ZMod 2) :
    pact σ (u + w) = pact σ u + pact σ w := rfl

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

theorem commute_wPi3_iff (a : Wr 6) :
    a * wPi3 = wPi3 * a ↔ pact a.perm (v6 [4, 5]) = v6 [4, 5] := by
  obtain ⟨v, σ⟩ := a
  constructor
  · intro h
    have h1 : v + pact σ (v6 [4, 5]) = v6 [4, 5] + pact 1 v := congrArg Wr.vec h
    rw [pact_one, add_comm (v6 [4, 5])] at h1
    exact add_left_cancel h1
  · intro h
    refine Wr.ext ?_ (by simp [wPi3, wv, Wr.mul_perm])
    show v + pact σ (v6 [4, 5]) = v6 [4, 5] + pact 1 v
    rw [h, pact_one, add_comm]

theorem mt_witness : ∀ σ : Perm (Fin 6), σ * σ = 1 → pact σ (v6 [4, 5]) = v6 [4, 5] → σ ≠ 1 →
    σ ≠ swap 4 5 → ∃ a b c : Fin 6, ∑ i, v6 [a, 4] i = 0 ∧ pact (swap b c) (v6 [4, 5]) = v6 [4, 5] ∧
      pact (swap b c * σ * swap b c) (v6 [a, 4] + pact σ (v6 [a, 4])) ≠
        v6 [a, 4] + pact σ (v6 [a, 4]) := by decide +kernel

theorem perm_of_commuting_class {X : Set (Wr 6)} (hX : ∀ x ∈ X, x * wPi3 = wPi3 * x)
    (hinv : ∀ x ∈ X, x * x = 1) (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hconj : ∀ k ∈ Wsub, k * wPi3 = wPi3 * k → ∀ x ∈ X, k * x * k⁻¹ ∈ X) :
    ∀ x ∈ X, x.perm = 1 ∨ x.perm = swap 4 5 := by
  intro x hx
  obtain ⟨v, σ⟩ := x
  have hsq := hinv _ hx
  have hσσ : σ * σ = 1 := congrArg Wr.perm hsq
  have hvv : v + pact σ v = 0 := congrArg Wr.vec hsq
  have h45 := (commute_wPi3_iff _).mp (hX _ hx)
  by_contra hne
  push Not at hne
  obtain ⟨a, b, c, hsum, hbc, hw⟩ := mt_witness σ hσσ h45 hne.1 hne.2
  set u := v6 [a, 4]
  have hq : (⟨u, 1⟩ : Wr 6) ∈ Wsub := hsum
  have hqc : (⟨u, 1⟩ : Wr 6) * wPi3 = wPi3 * ⟨u, 1⟩ := by
    rw [commute_wPi3_iff]; rfl
  have hy1 := hconj _ hq hqc _ hx
  rw [conj_mkVec] at hy1
  have hk : wp (swap b c) ∈ Wsub := by
    show ∑ i, (0 : Fin 6 → ZMod 2) i = 0
    simp
  have hkc : wp (swap b c) * wPi3 = wPi3 * wp (swap b c) := (commute_wPi3_iff _).mpr hbc
  have hy2 := hconj _ hk hkc _ hx
  rw [conj_wp] at hy2
  have hw1 := hcomm _ hx _ hy2
  have hw2 := hcomm _ hy1 _ hy2
  have hcw : ((⟨v, σ⟩ : Wr 6) * ⟨u + v + pact σ u, σ⟩) * ⟨pact (swap b c) v, swap b c * σ * (swap b c)⁻¹⟩ =
      ⟨pact (swap b c) v, swap b c * σ * (swap b c)⁻¹⟩ * ((⟨v, σ⟩ : Wr 6) * ⟨u + v + pact σ u, σ⟩) := by
    rw [mul_assoc, hw2, ← mul_assoc, hw1, mul_assoc]
  have hxy : (⟨v, σ⟩ : Wr 6) * ⟨u + v + pact σ u, σ⟩ = ⟨u + pact σ u, 1⟩ := by
    rw [mk_mul_mk, hσσ]
    refine Wr.ext ?_ rfl
    rw [pact_add, pact_add, ← pact_mul, hσσ, pact_one]
    calc v + (pact σ u + pact σ v + u) = (v + pact σ v) + (u + pact σ u) := by abel
      _ = u + pact σ u := by rw [hvv, zero_add]
  rw [hxy, mk_mul_mk, mk_mul_mk, pact_one, one_mul, mul_one, Equiv.swap_inv] at hcw
  have hv := congrArg Wr.vec hcw
  apply hw
  have : u + pact σ u + pact (swap b c) v = pact (swap b c) v +
      pact (swap b c * σ * swap b c) (u + pact σ u) := hv
  rw [add_comm (u + pact σ u)] at this
  exact (add_left_cancel this).symm

theorem exists_perm_vec : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → v ≠ 0 → v ≠ (fun _ => 1) →
    ∃ π : Perm (Fin 6), pact π v = v6 [4, 5] ∨ pact π v = v6 [0, 1, 2, 3] := by decide +kernel

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
