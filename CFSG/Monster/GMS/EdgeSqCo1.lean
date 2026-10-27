module

public import CFSG.Monster.GMS.EdgeSqFact
public import CFSG.Monster.GMS.S365Root
public import CFSG.Sporadic.Co1.Module.TwoB
public import Certificates.Data.CFSGNative.Co1.EdgeSq
public import CFSG.Monster.GMS.EdgeSqCo1Inputs
public import Certificates.Certificate10030
public meta import CFSG.Monster.GMS.S365Root
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import Certificates.Data.CFSGNative.Co1.EdgeSq
public import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace EdgeSq

open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.EdgeSqNative CFSG.Sporadic.Co1.S365UNative
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.S365Native

theorem edgeCheck_sA_ok : edgeCheck rowsSA = true :=
  Certificates.certificate10030.1

theorem edgeCheck_sC_ok : edgeCheck rowsSC = true :=
  Certificates.certificate10030.2

@[expose] def EdgeFactAt (s : Co1) : Prop :=
  ∀ a b : Fin 24 → ZMod 2, a ∈ co1Orbit 0 → b ∈ co1Orbit 0 → a + b ∈ co1Orbit 0 →
    co1Act s a = a → co1Act s b = b → (∀ x, co1Act s x = x → bil₀ a x = 0) →
      ∃ y, y + co1Act s y = b ∧ bil₀ a y = 1

theorem bil0N_iff (u c : ℕ) :
    bil0N (transposeRows 24 f0Rows) u c = true ↔ bil₀ (toVecD 24 u) (toVecD 24 c) = 1 := by
  rw [CFSG.Sporadic.Co1.Module.Pairs.bil₀_toVecD]
  have h : bil0N (transposeRows 24 f0Rows) u c = parity24 (u &&& dualCode c) := rfl
  rw [h]
  cases parity24 (u &&& dualCode c) <;> simp

theorem exists_pt_of_mem_co1Orbit_zero
    {u : Fin 24 → ZMod 2} (hu : u ∈ co1Orbit 0) :
    ∃ p < 98280, u = toVecD 24 (orbitOf 2 98280).pts[p]! := by
  rw [co1Orbit_zero, orbit_Co1_eq, orbit_v₂_eq] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  exact ⟨p, hp, rfl⟩

theorem pts_lt
    {p : ℕ} (hp : p < 98280) : (orbitOf 2 98280).pts[p]! < 2 ^ 24 :=
  ((vOrbitOK_facts orbitOK_v₂).2 p hp).1

theorem tyLab_three_iff
    {w : ℕ} (hw : w < 2 ^ 24) :
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = 3 ↔
      toVecD 24 w ∈ co1Orbit 0 := by
  rw [co1Orbit_zero, orbit_Co1_eq]
  exact tyLab_spec w hw 3 (by norm_num)

theorem edgeFactAt_of_check
    {S : Array ℕ} (h : edgeCheck S = true) {s : Co1}
    (hs : matHom s = rowsMatrix 24 S) : EdgeFactAt s := by
  intro a b ha hb hab hfa hfb hperp
  unfold edgeCheck edgeCheckN at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hX, hF⟩ := h
  obtain ⟨p, hp, rfl⟩ := exists_pt_of_mem_co1Orbit_zero ha
  obtain ⟨p', hp', rfl⟩ := exists_pt_of_mem_co1Orbit_zero hb
  have hpa : (orbitOf 2 98280).pts[p]! < 2 ^ 24 := pts_lt hp
  have hpb : (orbitOf 2 98280).pts[p']! < 2 ^ 24 := pts_lt hp'
  have hfixed : ∀ {x : ℕ}, x < 2 ^ 24 → (co1Act s (toVecD 24 x) = toVecD 24 x ↔
      isFixedN (transposeRows 24 S) x = true) := by
    intro x hx
    rw [isFixedN_iff S hx, ← hs]
    rfl
  have hmem : ∀ {q : ℕ}, q < 98280 → co1Act s (toVecD 24 (orbitOf 2 98280).pts[q]!) =
      toVecD 24 (orbitOf 2 98280).pts[q]! → q ∈ fixedIdx (orbitOf 2 98280).pts 98280
        (transposeRows 24 S) := by
    intro q hq hfq
    exact List.mem_filter.2 ⟨List.mem_range.2 hq, (hfixed (pts_lt hq)).1 hfq⟩
  have hpair := hF p (hmem hp hfa) p' (hmem hp' hfb)
  unfold pairOKN at hpair
  simp only [Bool.or_eq_true] at hpair
  rcases hpair with (h1 | h2) | h3
  ·
    exfalso
    have hxor : (orbitOf 2 98280).pts[p]! ^^^ (orbitOf 2 98280).pts[p']! < 2 ^ 24 :=
      Nat.xor_lt_two_pow hpa hpb
    have hab' : toVecD 24 ((orbitOf 2 98280).pts[p]! ^^^ (orbitOf 2 98280).pts[p']!) ∈
        co1Orbit 0 := by
      rw [toVecD_xor]
      exact hab
    have h3 := (tyLab_three_iff hxor).2 hab'
    have h4 : (tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
        ((orbitOf 2 98280).pts[p]! ^^^ (orbitOf 2 98280).pts[p']!) == 3) = true := by
      rw [beq_iff_eq]
      exact h3
    simp [h4] at h1
  ·
    exfalso
    obtain ⟨x, hxX, hx⟩ := List.any_eq_true.1 h2
    obtain ⟨hx24, hxfix⟩ := hX x hxX
    have h5 := hperp (toVecD 24 x) ((hfixed hx24).2 hxfix)
    have h6 := (bil0N_iff _ _).1 hx
    rw [h5] at h6
    exact absurd h6 (by decide)
  ·
    cases hm : memPre (imBasis (transposeRows 24 S)) (orbitOf 2 98280).pts[p']! with
    | none =>
      rw [hm] at h3
      simp at h3
    | some y =>
      rw [hm] at h3
      simp only [Bool.and_eq_true, beq_iff_eq] at h3
      obtain ⟨h7, h8⟩ := h3
      refine ⟨toVecD 24 y, ?_, (bil0N_iff _ _).1 h8⟩
      have e : toVecD 24 (orbitOf 2 98280).pts[p']! =
          toVecD 24 y + rowsMatrix 24 S *ᵥ toVecD 24 y := by
        rw [← h7]
        unfold onePlus
        rw [toVecD_xor, rowsMatrix_mulVec]
      rw [e, ← hs]
      rfl

theorem co1Act_mul_apply (g h : Co1) (v : Fin 24 → ZMod 2) :
    co1Act (g * h) v = co1Act g (co1Act h v) := by
  rw [map_mul]
  rfl

theorem co1Act_inv_apply (c : Co1) (v : Fin 24 → ZMod 2) : co1Act c⁻¹ (co1Act c v) = v := by
  rw [← co1Act_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem EdgeFactAt.conj
    {t : Co1} (ht : EdgeFactAt t) {s : Co1} (c : Co1) (hc : c * s * c⁻¹ = t) :
    EdgeFactAt s := by
  intro a b ha hb hab hfa hfb hperp
  have hts : t * c = c * s := by
    rw [← hc]
    group
  have hst : s * c⁻¹ = c⁻¹ * t := by
    rw [← hc]
    group
  have hfixt : ∀ {x : Fin 24 → ZMod 2}, co1Act s x = x → co1Act t (co1Act c x) = co1Act c x := by
    intro x hx
    rw [← co1Act_mul_apply, hts, co1Act_mul_apply, hx]
  have hperp' : ∀ x, co1Act t x = x → bil₀ (co1Act c a) x = 0 := by
    intro x hx
    have hxs : co1Act s (co1Act c⁻¹ x) = co1Act c⁻¹ x := by
      rw [← co1Act_mul_apply, hst, co1Act_mul_apply, hx]
    have h1 := Leech.bil₀_co1Act c⁻¹ (co1Act c a) x
    rw [co1Act_inv_apply] at h1
    rw [← h1]
    exact hperp _ hxs
  obtain ⟨y, hy1, hy2⟩ := ht (co1Act c a) (co1Act c b) (Leech.co1Act_mem_co1Orbit ha c)
    (Leech.co1Act_mem_co1Orbit hb c)
    (by rw [← map_add]; exact Leech.co1Act_mem_co1Orbit hab c) (hfixt hfa) (hfixt hfb) hperp'
  refine ⟨co1Act c⁻¹ y, ?_, ?_⟩
  · have h1 : co1Act s (co1Act c⁻¹ y) = co1Act c⁻¹ (co1Act t y) := by
      rw [← co1Act_mul_apply, hst, co1Act_mul_apply]
    rw [h1, ← map_add, hy1, co1Act_inv_apply]
  · have h1 := Leech.bil₀_co1Act c⁻¹ (co1Act c a) y
    rw [co1Act_inv_apply] at h1
    rw [h1]
    exact hy2

theorem EdgeFactAt.of_isConj
    {s t : Co1} (ht : EdgeFactAt t) (h : IsConj s t) : EdgeFactAt s := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact ht.conj c hc

theorem invariants_of_packed {S : Array ℕ} {a b : ℕ} (h : countsOK S a b = true) {s : Co1}
    (hs : matHom s = rowsMatrix 24 S) :
    (co1Fix s).ncard = a ∧
      {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act s v = v ∧ q₀ v = 1}.ncard = b := by
  obtain ⟨h1, h2⟩ := countsOK_facts h
  refine ⟨?_, ?_⟩
  · have hset : co1Fix s = {v : Fin 24 → ZMod 2 | rowsMatrix 24 S *ᵥ v = v} := by
      ext v
      simp only [co1Fix, Set.mem_ofPred_eq]
      rw [← hs]
      rfl
    rw [hset, h1]
  · have hset : {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act s v = v ∧ q₀ v = 1} =
        {v : Fin 24 → ZMod 2 | rowsMatrix 24 S *ᵥ v = v ∧ q₀ v = 1} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      rw [← hs]
      rfl
    rw [hset, h2]

theorem isConj_of_invariants
    {s t : Co1} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (h1 : (co1Fix s).ncard = (co1Fix t).ncard)
    (h2 : {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act s v = v ∧ q₀ v = 1}.ncard =
      {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act t v = v ∧ q₀ v = 1}.ncard) :
    IsConj s t := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := S365.co1_classes
  obtain ⟨-, -, -, hfA, hfB, hfC, hqA, hqB, hqC, -⟩ := hrep
  have eA : (co1Fix sA).ncard = 2 ^ 16 := hfA
  have eB : (co1Fix sB).ncard = 2 ^ 12 := hfB
  have eC : (co1Fix sC).ncard = 2 ^ 12 := hfC
  have inv : ∀ {x y : Co1}, IsConj x y → (co1Fix x).ncard = (co1Fix y).ncard ∧
      {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act x v = v ∧ q₀ v = 1}.ncard =
        {v : Fin 24 → ZMod 2 | CFSG.Sporadic.Co1.Module.co1Act y v = v ∧ q₀ v = 1}.ncard :=
    fun h => ⟨(co1Inv_isConj_invariants h).1, (co1Inv_isConj_invariants h).2.1⟩
  rcases hcls s hs with hsX | hsX | hsX <;> rcases hcls t ht with htX | htX | htX
  · exact hsX.trans htX.symm
  · exfalso
    have := (inv hsX).1.symm.trans (h1.trans (inv htX).1)
    rw [eA, eB] at this
    norm_num at this
  · exfalso
    have := (inv hsX).1.symm.trans (h1.trans (inv htX).1)
    rw [eA, eC] at this
    norm_num at this
  · exfalso
    have := (inv hsX).1.symm.trans (h1.trans (inv htX).1)
    rw [eB, eA] at this
    norm_num at this
  · exact hsX.trans htX.symm
  · exfalso
    have := (inv hsX).2.symm.trans (h2.trans (inv htX).2)
    rw [hqB, hqC] at this
    norm_num at this
  · exfalso
    have := (inv hsX).1.symm.trans (h1.trans (inv htX).1)
    rw [eC, eA] at this
    norm_num at this
  · exfalso
    have := (inv hsX).2.symm.trans (h2.trans (inv htX).2)
    rw [hqC, hqB] at this
    norm_num at this
  · exact hsX.trans htX.symm

theorem exists_sC :
    ∃ s : Co1, matHom s = rowsMatrix 24 rowsSC := by
  obtain ⟨kN, hkN⟩ := exists_gen_family nWord1 nWord2
  have hkN' : ∀ l < nGens.size, matHom (kN l) = rowsMatrix 24 nGens[l]! := hkN
  obtain ⟨hNs, -⟩ := repOK_facts repOK_C
  exact exists_rep nGens kN hkN' wordC (by rw [hNs]; decide) 5

theorem edgeFactAt_of_orderOf_two
    {s : Co1} (hs : orderOf s = 2) : EdgeFactAt s := by
  obtain ⟨sA, sB, sC, hrep, hcls⟩ := S365.co1_classes
  obtain ⟨-, -, -, hfA, hfB, hfC, hqA, hqB, hqC, -⟩ := hrep
  have eA : (co1Fix sA).ncard = 2 ^ 16 := hfA
  have eB : (co1Fix sB).ncard = 2 ^ 12 := hfB
  have eC : (co1Fix sC).ncard = 2 ^ 12 := hfC
  obtain ⟨EA, hEA⟩ := exists_sA
  obtain ⟨EC, hEC⟩ := exists_sC
  obtain ⟨hEAo, -⟩ := S365.sA_facts hEA
  obtain ⟨hEAf, hEAq⟩ := invariants_of_packed counts_A hEA
  obtain ⟨hECf, hECq⟩ := invariants_of_packed counts_C hEC
  have hECo : orderOf EC = 2 :=
    orderOf_eq_of_orderIs hEC (by norm_num) (repOK_facts repOK_C).2.2.1
  have hA : EdgeFactAt EA := edgeFactAt_of_check edgeCheck_sA_ok hEA
  have hC : EdgeFactAt EC := edgeFactAt_of_check edgeCheck_sC_ok hEC
  rcases hcls s hs with h | h | h
  · obtain ⟨i1, i2, -⟩ := co1Inv_isConj_invariants h
    refine hA.of_isConj (isConj_of_invariants hs hEAo ?_ ?_)
    · rw [i1, eA, hEAf]
      norm_num
    · rw [i2, hqA, hEAq]
  ·
    obtain ⟨i1, i2, -⟩ := co1Inv_isConj_invariants h
    have hB : IsCo1TwoB s := by
      refine ⟨hs, by rw [i1, eB], fun v hv => ?_⟩
      by_contra hne
      have hq1 : q₀ v = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hne
      have hmem : v ∈ {v : Fin 24 → ZMod 2 |
          CFSG.Sporadic.Co1.Module.co1Act s v = v ∧ q₀ v = 1} := ⟨hv, hq1⟩
      have hpos := Set.ncard_pos (Set.toFinite _) |>.2 ⟨v, hmem⟩
      rw [i2, hqB] at hpos
      exact absurd hpos (by norm_num)
    intro a b ha hb hab hfa hfb hperp
    exfalso
    have hfa' : a ∈ co1Fix s := hfa
    have h2 := (co1TwoBFacts s hB).2.1 a hfa' (Leech.ne_zero_of_mem_co1Orbit ha)
    exact absurd (Leech.eq_of_mem_co1Orbit ha h2) (by decide)
  · obtain ⟨i1, i2, -⟩ := co1Inv_isConj_invariants h
    refine hC.of_isConj (isConj_of_invariants hs hECo ?_ ?_)
    · rw [i1, eC, hECf]
      norm_num
    · rw [i2, hqC, hECq]

theorem co1EdgeFact :
    Co1EdgeFact := fun _ hs => edgeFactAt_of_orderOf_two hs

end EdgeSq

end CFSG.Monster.GMS
