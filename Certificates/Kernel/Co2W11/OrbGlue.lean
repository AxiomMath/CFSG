module

public import Certificates.Kernel.Co2W11.Glue
public import Certificates.Kernel.Co2W11.Orb
public import CFSG.Certificates.Kernel.F2PtSetSound
import CFSG.Certificates.Kernel.Co1FixCount
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCount
import all CFSG.Blueprint.NativeSporadic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.KernelCo2W11

open CFSG.GF2Type.Widths1112 CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.GF2W1112 CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.F2TriSep CFSG.KC.F2FormId
  CFSG.KC.F2OrbW CFSG.KC.F2PtSet CFSG.KLie.CT CertificateChecks.KernelLC.Co2Ops Matrix

theorem ob_rep0 : w12Co2Rep 0 = 40 := by decide +kernel

theorem ob_rep1 : w12Co2Rep 1 = 65536 := by decide +kernel

theorem ob_rep2 : w12Co2Rep 2 = 8 := by decide +kernel

theorem ob_p0 : fget Ob.P0 0 22 = 40 := by decide +kernel

theorem ob_lam2 : Ob.lam2 = vecMulN 22 (w12Co2FT ()) 8 := by decide +kernel

theorem ob_hyp_bits : ∀ i < 22, ∀ j < 22,
    (hypF 11).testBit (22 * i + j) = decide (i < 11 ∧ j = i + 11) := by
  decide +kernel

theorem ob_span_rows : ∀ j < 22, getL 0 Ob.bidx j < 2300 ∧
    rowF 22 (packL 22 (ptsL 22 Ob.P0 Ob.bidx)) j = fget Ob.P0 (getL 0 Ob.bidx j) 22 := by
  decide +kernel

theorem ob_fget_lt (X i : Nat) : fget X i 22 < 2 ^ 22 := by
  have e : fget X i 22 = (X >>> (i * 22)) &&& (2 ^ 22 - 1) := by
    change (X >>> (i * 22)) &&& ((1 <<< 22) - 1) = _
    rw [Nat.one_shiftLeft]
  rw [e]
  exact Nat.and_lt_two_pow _ (by norm_num)

theorem ob_tv_xor (x y : Nat) : toVecD 22 (Nat.xor x y) = toVecD 22 x + toVecD 22 y :=
  toVecD_xor 22 x y

theorem ob_notB {b : Bool} (h : notB b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem ob_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.blt_eq.mp h

theorem eqL_eq : ∀ L M : List Nat, eqL L M = true → L = M
  | [], [], _ => rfl
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h (by decide)
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h (by decide)
  | x :: L, y :: M, h => by
    change andB (Nat.beq x y) (eqL L M) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqL_eq L M h.2]

theorem mem_trL {G : List Nat} {h : Nat} (hh : h ∈ trL 22 G) : ∃ g ∈ G, h = trK 22 g := by
  induction G with
  | nil => exact absurd hh List.not_mem_nil
  | cons g G ih =>
    change h ∈ trK 22 g :: trL 22 G at hh
    rcases List.mem_cons.1 hh with rfl | h'
    · exact ⟨g, by simp, rfl⟩
    · obtain ⟨g', hg', e⟩ := ih h'
      exact ⟨g', List.mem_cons_of_mem _ hg', e⟩

theorem gen_elt {ws : List (List Bool)} {w : Nat}
    (hfix : fixL 22 (gensOf ws) w = true) {h : Nat} (hh : h ∈ trL 22 (gensOf ws)) :
    ∃ x : NativeSporadic.Co2, co2Act x (toVecD 22 w) = toVecD 22 w ∧
      ∀ v, toVecD 22 (vmF 22 h v) = co2Act x (toVecD 22 v) := by
  obtain ⟨g, hg, rfl⟩ := mem_trL hh
  obtain ⟨wd, rfl⟩ := mem_gensOf hg
  obtain ⟨x, hx⟩ := exists_word_elt wd
  refine ⟨x, ?_, fun v => ?_⟩
  · rw [hx, mat_mulVec, fixL_mem hfix _ hg]
  · rw [hx, mat_mulVec]

theorem word_mem {v : Nat} {P : List (Nat × List Bool)}
    (h : wordsToK 22 SA.M SB.M v P = true) {p : Nat × List Bool} (hp : p ∈ P) :
    ∃ x : NativeSporadic.Co2, co2Act x (toVecD 22 v) = toVecD 22 p.1 := by
  obtain ⟨x, hx⟩ := exists_word_elt p.2
  exact ⟨x, by rw [hx, mat_mulVec, wordsToK_mem h p hp]⟩

theorem orb_act (i : ℕ) (g : NativeSporadic.Co2) {v : Vec22} (hv : v ∈ co2Orbit i) :
    co2Act g v ∈ co2Orbit i := by
  obtain ⟨h, rfl⟩ := hv
  exact ⟨g * h, co2Act_mul g h _⟩

theorem orb_act_iff (i : ℕ) (g : NativeSporadic.Co2) (v : Vec22) :
    co2Act g v ∈ co2Orbit i ↔ v ∈ co2Orbit i := by
  refine ⟨fun h => ?_, orb_act i g⟩
  have h' := orb_act i g⁻¹ h
  rwa [co2Act_inv_apply] at h'

theorem co2Act_inj (g : NativeSporadic.Co2) : Function.Injective (co2Act g) := by
  intro a b h
  have h' := congrArg (co2Act g⁻¹) h
  rwa [co2Act_inv_apply, co2Act_inv_apply] at h'

theorem q_orb {i : ℕ} (hi : i < 3) {v : Vec22} (hv : v ∈ co2Orbit i) : q₀₂ v = 0 := by
  obtain ⟨g, rfl⟩ := hv
  beta_reduce
  rw [forms_q]
  exact (forms_reps i hi).2

theorem co2Act_inv' (g : NativeSporadic.Co2) (v : Vec22) : co2Act g (co2Act g⁻¹ v) = v := by
  rw [← co2Act_mul, mul_inv_cancel, co2Act_one]

theorem ob_fib (j : ℕ) (g : NativeSporadic.Co2) (a : Vec22) :
    {y | y ∈ co2Orbit j ∧ y + co2Act g a ∈ co2Orbit 0} =
      (co2Act g) '' {y | y ∈ co2Orbit j ∧ y + a ∈ co2Orbit 0} := by
  ext y
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨co2Act g⁻¹ y, ⟨(orb_act_iff j g⁻¹ y).2 h1, ?_⟩, co2Act_inv' g y⟩
    rw [← orb_act_iff 0 g, co2Act_add, co2Act_inv']
    exact h2
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    refine ⟨orb_act j g h1, ?_⟩
    rw [← co2Act_add]
    exact orb_act 0 g h2

theorem ob_fib' (i : ℕ) (g : NativeSporadic.Co2) (a : Vec22) :
    {x | x ∈ co2Orbit i ∧ co2Act g a + x ∈ co2Orbit 0} =
      (co2Act g) '' {x | x ∈ co2Orbit i ∧ a + x ∈ co2Orbit 0} := by
  ext y
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨co2Act g⁻¹ y, ⟨(orb_act_iff i g⁻¹ y).2 h1, ?_⟩, co2Act_inv' g y⟩
    rw [← orb_act_iff 0 g, co2Act_add, co2Act_inv']
    exact h2
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    refine ⟨orb_act i g h1, ?_⟩
    rw [← co2Act_add]
    exact orb_act 0 g h2

theorem co2_count {i j a b : ℕ}
    (ha : a ≤ {y | y ∈ co2Orbit j ∧ y + toVecD 22 (w12Co2Rep i) ∈ co2Orbit 0}.ncard)
    (hb : {x | x ∈ co2Orbit i ∧ toVecD 22 (w12Co2Rep j) + x ∈ co2Orbit 0}.ncard ≤ b) :
    (co2Orbit i).ncard * a ≤ (co2Orbit j).ncard * b := by
  classical
  have hs := (co2Orbit i).toFinite
  have ht := (co2Orbit j).toFinite
  rw [Set.ncard_eq_toFinset_card _ hs, Set.ncard_eq_toFinset_card _ ht]
  refine Finset.card_mul_le_card_mul (fun x y : Vec22 => y + x ∈ co2Orbit 0) (fun x hx => ?_)
    (fun y hy => ?_)
  · obtain ⟨g, rfl⟩ := hs.mem_toFinset.1 hx
    beta_reduce
    have e : ((ht.toFinset.bipartiteAbove (fun x y : Vec22 => y + x ∈ co2Orbit 0)
        (co2Act g (toVecD 22 (w12Co2Rep i))) : Finset Vec22) : Set Vec22) =
        {y | y ∈ co2Orbit j ∧ y + co2Act g (toVecD 22 (w12Co2Rep i)) ∈ co2Orbit 0} := by
      ext y
      simp [Finset.bipartiteAbove]
    rw [← Set.ncard_coe_finset, e, ob_fib, Set.ncard_image_of_injective _ (co2Act_inj g)]
    exact ha
  · obtain ⟨g, rfl⟩ := ht.mem_toFinset.1 hy
    beta_reduce
    have e : ((hs.toFinset.bipartiteBelow (fun x y : Vec22 => y + x ∈ co2Orbit 0)
        (co2Act g (toVecD 22 (w12Co2Rep j))) : Finset Vec22) : Set Vec22) =
        {x | x ∈ co2Orbit i ∧ co2Act g (toVecD 22 (w12Co2Rep j)) + x ∈ co2Orbit 0} := by
      ext x
      simp [Finset.bipartiteBelow]
    rw [← Set.ncard_coe_finset, e, ob_fib', Set.ncard_image_of_injective _ (co2Act_inj g)]
    exact hb

theorem ncard_img {n P : Nat} (hs : sortK 22 n P = true) (s : Finset ℕ) (hsub : ∀ i ∈ s, i < n) :
    ((fun i => toVecD 22 (fget P i 22)) '' (s : Set ℕ)).ncard = s.card := by
  refine (Set.InjOn.ncard_image ?_).trans (Set.ncard_coe_finset s)
  intro i hi j hj e
  have e' := toVecD_injective (ob_fget_lt P i) (ob_fget_lt P j) e
  have hS := sortK_spec hs
  rcases lt_trichotomy i j with h | h | h
  · exact absurd e' (ne_of_lt (hS i j h (hsub j hj)))
  · exact h
  · exact absurd e' (ne_of_gt (hS j i h (hsub i hi)))

theorem o0_sorted : sortK 22 2300 Ob.P0 = true := by
  have h := o0_ok
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem o0_sub :
    ∀ i < 2300, toVecD 22 (fget Ob.P0 i 22) ∈ co2Orbit 0 := by
  have h := o0_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨-, hf⟩, -⟩, -⟩ := h
  refine forK_spec hf {x | toVecD 22 x ∈ co2Orbit 0} ?_ ?_
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    refine ⟨1, ?_⟩
    beta_reduce
    rw [co2Act_one, ob_rep0]
  · intro g hg x hx
    obtain ⟨b, rfl⟩ : ∃ b : Bool, g = trK 22 (if b then SA.M else SB.M) := by
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨true, by simp⟩
      · rw [List.mem_singleton] at hg
        exact ⟨false, by simp [hg]⟩
    obtain ⟨y, hy⟩ := exists_seed_elt b
    change toVecD 22 _ ∈ co2Orbit 0
    rw [← mat_mulVec, ← hy]
    exact orb_act _ _ hx

theorem o0_sup (g : NativeSporadic.Co2) :
    ∃ k < 2300, toVecD 22 (fget Ob.P0 k 22) = co2Act g (toVecD 22 (w12Co2Rep 0)) := by
  have h := o0_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hA⟩, hB⟩ := h
  have hmem : (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) ∈ Submonoid.closure
      ({NativeSporadic.decode 2 22 1 NativeSporadic.Co2Seed1,
        NativeSporadic.decode 2 22 1 NativeSporadic.Co2Seed2} :
        Set (Matrix (Fin 22) (Fin 22) (ZMod 2))) := g.val.2
  have key : ∀ v : Vec22, (∃ k < 2300, toVecD 22 (fget Ob.P0 k 22) = v) →
      ∃ k < 2300, toVecD 22 (fget Ob.P0 k 22) =
        (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) *ᵥ v := by
    generalize (g.val.val : Matrix (Fin 22) (Fin 22) (ZMod 2)) = M at hmem
    induction hmem using Submonoid.closure_induction with
    | mem x hx =>
      rintro v ⟨i, hi, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · obtain ⟨k, hk, e⟩ := imgK_spec hA i hi
        exact ⟨k, hk, by rw [← mat_SA, mat_mulVec, e]⟩
      · obtain ⟨k, hk, e⟩ := imgK_spec hB i hi
        exact ⟨k, hk, by rw [← mat_SB, mat_mulVec, e]⟩
    | one =>
      intro v hv
      rwa [Matrix.one_mulVec]
    | mul x y _ _ hx hy =>
      intro v hv
      rw [← Matrix.mulVec_mulVec]
      exact hx _ (hy v hv)
  rw [co2Act_def]
  exact key _ ⟨0, by norm_num, by rw [ob_p0, ob_rep0]⟩

theorem mem_O0 (v : Vec22) :
    v ∈ co2Orbit 0 ↔ ∃ k < 2300, toVecD 22 (fget Ob.P0 k 22) = v := by
  constructor
  · rintro ⟨g, rfl⟩
    exact o0_sup g
  · rintro ⟨k, hk, rfl⟩
    exact o0_sub k hk

theorem mem_O0_code {z : Nat} (hz : z < 2 ^ 22) :
    toVecD 22 z ∈ co2Orbit 0 ↔ ∃ k < 2300, fget Ob.P0 k 22 = z := by
  rw [mem_O0]
  constructor
  · rintro ⟨k, hk, e⟩
    exact ⟨k, hk, toVecD_injective (ob_fget_lt _ _) hz e⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem n0_eq : (co2Orbit 0).ncard = 2300 := by
  have e : co2Orbit 0 = (fun i => toVecD 22 (fget Ob.P0 i 22)) '' ↑(Finset.range 2300) := by
    ext v
    rw [mem_O0]
    simp
  rw [e, ncard_img o0_sorted _ (fun i hi => Finset.mem_range.1 hi), Finset.card_range]

theorem b_scan {c W : Nat} (hc : c < 2 ^ 22)
    (hg : gapsK 22 2300 Ob.P0 2300 Ob.P0 W (Nat.xor c) = true) :
    {x | x ∈ co2Orbit 0 ∧ toVecD 22 c + x ∈ co2Orbit 0}.ncard =
      cntK 22 2300 Ob.P0 Ob.P0 W (Nat.xor c) (fun _ => true) true := by
  rw [cnt_card o0_sorted hg, ← ncard_img o0_sorted _ (fun i hi =>
    Finset.mem_range.1 (Finset.mem_filter.1 hi).1)]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Finset.mem_range]
  constructor
  · rintro ⟨hx0, hx1⟩
    obtain ⟨i, hi, rfl⟩ := (mem_O0 x).1 hx0
    rw [← ob_tv_xor, mem_O0_code (z := Nat.xor c (fget Ob.P0 i 22))
      (Nat.xor_lt_two_pow hc (ob_fget_lt _ _))] at hx1
    exact ⟨i, ⟨hi, trivial, iff_of_true hx1 trivial⟩, rfl⟩
  · rintro ⟨i, ⟨hi, -, hk⟩, rfl⟩
    refine ⟨o0_sub i hi, ?_⟩
    rw [← ob_tv_xor, mem_O0_code (z := Nat.xor c (fget Ob.P0 i 22))
      (Nat.xor_lt_two_pow hc (ob_fget_lt _ _))]
    exact hk.2 trivial

theorem scan_parts : gapsK 22 2300 Ob.P0 2300 Ob.P0 Ob.W1 (Nat.xor 65536) = true ∧
    cntK 22 2300 Ob.P0 Ob.P0 Ob.W1 (Nat.xor 65536) (fun _ => true) true = 44 ∧
    gapsK 22 2300 Ob.P0 2300 Ob.P0 Ob.W2 (Nat.xor 8) = true ∧
    cntK 22 2300 Ob.P0 Ob.P0 Ob.W2 (Nat.xor 8) (fun _ => true) true = Ob.b2 ∧
    gapsK 22 2300 Ob.P0 2300 Ob.P0 Ob.W3 (Nat.xor (Nat.xor 8 Ob.urep)) = true ∧
    cntK 22 2300 Ob.P0 Ob.P0 Ob.W3 (Nat.xor (Nat.xor 8 Ob.urep)) (fun _ => true) true = Ob.b3 ∧
    gapK 22 2300 Ob.P0 65536 Ob.g1 = true ∧ inW 22 Ob.P0 65536 Ob.g1 = false ∧
    gapK 22 2300 Ob.P0 8 Ob.g2 = true ∧ inW 22 Ob.P0 8 Ob.g2 = false := by
  have h := scan_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, Nat.eq_of_beq_eq_true h2, h3, Nat.eq_of_beq_eq_true h4, h5, Nat.eq_of_beq_eq_true h6,
    h7, ob_notB h8, h9, ob_notB h10⟩

theorem rel_parts : Ob.iu0 < 2300 ∧ fget Ob.P0 Ob.iu0 22 = Ob.u0 ∧
    Ob.iurep < 2300 ∧ fget Ob.P0 Ob.iurep 22 = Ob.urep ∧
    Ob.ws1.map Prod.fst = [Nat.xor 40 Ob.u0] ∧
    (Ob.ws2.map Prod.fst).map (Nat.xor 65536) = Ob.izs.map (fun k => fget Ob.P0 k 22) ∧
    (∀ k ∈ Ob.izs, k < 2300) ∧ Ob.b2 ≠ 44 ∧ Ob.b3 ≠ 44 := by
  have h := rel_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, -⟩ := h
  refine ⟨ob_blt h1, Nat.eq_of_beq_eq_true h2, ob_blt h3, Nat.eq_of_beq_eq_true h4,
    eqL_eq _ _ h5, eqL_eq _ _ h6, fun k hk => ob_blt (List.all_eq_true.1 h7 k hk), ?_, ?_⟩
  · exact fun e => absurd (ob_notB h8) (by rw [e]; decide)
  · exact fun e => absurd (ob_notB h9) (by rw [e]; decide)

theorem b1 :
    {x | x ∈ co2Orbit 0 ∧ toVecD 22 (w12Co2Rep 1) + x ∈ co2Orbit 0}.ncard = 44 := by
  rw [ob_rep1, b_scan (by norm_num) scan_parts.1]
  exact scan_parts.2.1

theorem b2 :
    {x | x ∈ co2Orbit 0 ∧ toVecD 22 (w12Co2Rep 2) + x ∈ co2Orbit 0}.ncard = Ob.b2 := by
  rw [ob_rep2, b_scan (by norm_num) scan_parts.2.2.1]
  exact scan_parts.2.2.2.1

theorem b3 :
    {x | x ∈ co2Orbit 0 ∧ (toVecD 22 (w12Co2Rep 2) + toVecD 22 Ob.urep) + x ∈ co2Orbit 0}.ncard =
      Ob.b3 := by
  have hu : Ob.urep < 2 ^ 22 := by
    rw [← rel_parts.2.2.2.1]
    exact ob_fget_lt _ _
  rw [ob_rep2, ← ob_tv_xor, b_scan (c := Nat.xor 8 Ob.urep) (Nat.xor_lt_two_pow (by norm_num) hu)
    scan_parts.2.2.2.2.1]
  exact scan_parts.2.2.2.2.2.1

theorem b_orb1 {z : Vec22} (hz : z ∈ co2Orbit 1) :
    {x | x ∈ co2Orbit 0 ∧ z + x ∈ co2Orbit 0}.ncard = 44 := by
  obtain ⟨g, rfl⟩ := hz
  beta_reduce
  have e : {x | x ∈ co2Orbit 0 ∧ co2Act g (toVecD 22 (w12Co2Rep 1)) + x ∈ co2Orbit 0} =
      (fun x => co2Act g x) '' {x | x ∈ co2Orbit 0 ∧ toVecD 22 (w12Co2Rep 1) + x ∈ co2Orbit 0} := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨co2Act g⁻¹ x, ⟨(orb_act_iff 0 g⁻¹ x).2 h1, ?_⟩, co2Act_inv' g x⟩
      rw [← orb_act_iff 0 g, co2Act_add, co2Act_inv']
      exact h2
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      refine ⟨orb_act 0 g h1, ?_⟩
      rw [← co2Act_add]
      exact orb_act 0 g h2
  rw [e, Set.ncard_image_of_injective _ (co2Act_inj g), b1]

theorem orb_disj {i j : ℕ}
    (h : toVecD 22 (w12Co2Rep j) ∉ co2Orbit i) : Disjoint (co2Orbit i) (co2Orbit j) := by
  rw [Set.disjoint_left]
  rintro v ⟨g, rfl⟩ ⟨k, e⟩
  beta_reduce at e
  apply h
  refine ⟨k⁻¹ * g, ?_⟩
  beta_reduce
  rw [co2Act_mul, ← e, co2Act_inv_apply]

theorem r1_not0 : toVecD 22 (w12Co2Rep 1) ∉ co2Orbit 0 := by
  rw [ob_rep1, mem_O0_code (by norm_num), ← inW_iff o0_sorted scan_parts.2.2.2.2.2.2.1,
    scan_parts.2.2.2.2.2.2.2.1]
  decide

theorem r2_not0 : toVecD 22 (w12Co2Rep 2) ∉ co2Orbit 0 := by
  rw [ob_rep2, mem_O0_code (by norm_num), ← inW_iff o0_sorted scan_parts.2.2.2.2.2.2.2.2.1,
    scan_parts.2.2.2.2.2.2.2.2.2]
  decide

theorem r2_not1 : toVecD 22 (w12Co2Rep 2) ∉ co2Orbit 1 := by
  intro h
  have e := b_orb1 h
  rw [b2] at e
  exact rel_parts.2.2.2.2.2.2.2.1 e

theorem z1_low :
    891 ≤ {y | y ∈ co2Orbit 1 ∧ y + toVecD 22 (w12Co2Rep 0) ∈ co2Orbit 0}.ncard := by
  have hz := z1_ok
  simp only [Bool.and_eq_true] at hz
  obtain ⟨hs, hf⟩ := hz
  have hfix : fixL 22 (gensOf S0.words) (w12Co2Rep 0) = true := by
    rw [ob_rep0, ← s0_w]
    exact fix0_ok
  have hX := forK_spec hf
    {x | toVecD 22 x ∈ co2Orbit 1 ∧ toVecD 22 x + toVecD 22 (w12Co2Rep 0) ∈ co2Orbit 0} ?_ ?_
  · calc 891 = (Finset.range 891).card := (Finset.card_range 891).symm
      _ = ((fun i => toVecD 22 (fget Ob.PZ1 i 22)) '' ↑(Finset.range 891)).ncard :=
        (ncard_img hs _ (fun i hi => Finset.mem_range.1 hi)).symm
      _ ≤ _ := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨i, hi, rfl⟩
        exact hX i (Finset.mem_range.1 hi)
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    obtain ⟨hiu, hu, -, -, hw1, -⟩ := rel_parts
    have hmem : Nat.xor 40 Ob.u0 ∈ Ob.ws1.map Prod.fst := by rw [hw1]; simp
    obtain ⟨p, hp, hp1⟩ := List.mem_map.1 hmem
    have hw := words_ok
    rw [Bool.and_eq_true] at hw
    obtain ⟨x, hx⟩ := word_mem hw.2 hp
    refine ⟨⟨x, by beta_reduce; rw [ob_rep1, hx, hp1]⟩, ?_⟩
    rw [ob_tv_xor, ob_rep0, add_comm (toVecD 22 40) (toVecD 22 Ob.u0), add_assoc, add_self_vec,
      add_zero, ← hu]
    exact o0_sub _ hiu
  · intro g hg x hx
    obtain ⟨y, hyfix, hy⟩ := gen_elt hfix hg
    refine ⟨by rw [hy]; exact orb_act _ _ hx.1, ?_⟩
    have e : co2Act y (toVecD 22 x) + toVecD 22 (w12Co2Rep 0) =
        co2Act y (toVecD 22 x + toVecD 22 (w12Co2Rep 0)) := by rw [co2Act_add, hyfix]
    change toVecD 22 (vmF 22 g x) + _ ∈ _
    rw [hy, e]
    exact orb_act _ _ hx.2

theorem count1 :
    (co2Orbit 0).ncard * 891 ≤ (co2Orbit 1).ncard * 44 := by
  exact co2_count z1_low b1.le

theorem z_low :
    1232 ≤ {y | y ∈ co2Orbit 2 ∧ y + toVecD 22 (w12Co2Rep 1) ∈ co2Orbit 0}.ncard := by
  have hz := z_ok
  rw [Bool.and_eq_true] at hz
  obtain ⟨hs, hf⟩ := hz
  have hfix : fixL 22 (gensOf S1.words) (w12Co2Rep 1) = true := by
    rw [← s1_w]
    exact fix1_ok
  have hX := forK_spec hf
    {x | toVecD 22 x ∈ co2Orbit 2 ∧ toVecD 22 x + toVecD 22 (w12Co2Rep 1) ∈ co2Orbit 0} ?_ ?_
  · calc 1232 = (Finset.range 1232).card := (Finset.card_range 1232).symm
      _ = ((fun i => toVecD 22 (fget Ob.PZ i 22)) '' ↑(Finset.range 1232)).ncard :=
        (ncard_img hs _ (fun i hi => Finset.mem_range.1 hi)).symm
      _ ≤ _ := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        rintro _ ⟨i, hi, rfl⟩
        exact hX i (Finset.mem_range.1 hi)
  · intro r hr
    obtain ⟨-, -, -, -, -, hw2, hizs, -⟩ := rel_parts
    obtain ⟨p, hp, hp1⟩ := List.mem_map.1 hr
    have hw := words_ok
    rw [Bool.and_eq_true] at hw
    obtain ⟨x, hx⟩ := word_mem hw.1 hp
    refine ⟨⟨x, by beta_reduce; rw [ob_rep2, hx, hp1]⟩, ?_⟩
    have hm : Nat.xor 65536 r ∈ Ob.izs.map (fun k => fget Ob.P0 k 22) := by
      rw [← hw2]
      exact List.mem_map.2 ⟨r, hr, rfl⟩
    obtain ⟨k, hk, e⟩ := List.mem_map.1 hm
    rw [ob_rep1, add_comm, ← ob_tv_xor, ← e]
    exact o0_sub k (hizs k hk)
  · intro g hg x hx
    obtain ⟨y, hyfix, hy⟩ := gen_elt hfix hg
    refine ⟨by rw [hy]; exact orb_act _ _ hx.1, ?_⟩
    have e : co2Act y (toVecD 22 x) + toVecD 22 (w12Co2Rep 1) =
        co2Act y (toVecD 22 x + toVecD 22 (w12Co2Rep 1)) := by rw [co2Act_add, hyfix]
    change toVecD 22 (vmF 22 g x) + _ ∈ _
    rw [hy, e]
    exact orb_act _ _ hx.2

theorem d2_mem : ∀ k < 1120, ∃ g : NativeSporadic.Co2,
    co2Act g (toVecD 22 (w12Co2Rep 2)) = toVecD 22 (w12Co2Rep 2) ∧
      toVecD 22 (fget Ob.PD2 k 22) = co2Act g (toVecD 22 Ob.urep) := by
  have hd := d2_ok
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨-, hf⟩, -⟩, -⟩ := hd
  have hfix : fixL 22 (gensOf S2.words) (w12Co2Rep 2) = true := by
    rw [← s2_w]
    exact fix2_ok
  refine forK_spec hf {x | ∃ g : NativeSporadic.Co2,
    co2Act g (toVecD 22 (w12Co2Rep 2)) = toVecD 22 (w12Co2Rep 2) ∧
      toVecD 22 x = co2Act g (toVecD 22 Ob.urep)} ?_ ?_
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact ⟨1, co2Act_one _, (co2Act_one _).symm⟩
  · rintro g hg x ⟨h, hh, hx⟩
    obtain ⟨y, hyfix, hy⟩ := gen_elt hfix hg
    refine ⟨y * h, by rw [co2Act_mul, hh, hyfix], ?_⟩
    change toVecD 22 (vmF 22 g x) = _
    rw [hy, hx, co2Act_mul]

theorem ob_bil (a : Nat) : bil₀₂ (toVecD 22 a) (toVecD 22 (w12Co2Rep 2)) =
    if dotK 22 a Ob.lam2 = true then 1 else 0 := by
  rw [ob_rep2, bil₀₂_toVecD, ob_lam2, CFSG.KC.Co1Fix.dotK_eq]
  rfl

theorem c2_hb :
    {x | x ∈ co2Orbit 1 ∧ toVecD 22 (w12Co2Rep 2) + x ∈ co2Orbit 0}.ncard ≤ 28 := by
  have hd := d2_ok
  simp only [Bool.and_eq_true] at hd
  obtain ⟨⟨⟨hs, -⟩, hg⟩, hc⟩ := hd
  have hcnt := cnt_card (f := fun x => notB (dotK 22 x Ob.lam2)) (pos := false) hs hg
  rw [Nat.eq_of_beq_eq_true hc] at hcnt
  rw [hcnt, ← ncard_img o0_sorted _ (fun i hi => Finset.mem_range.1 (Finset.mem_filter.1 hi).1)]
  refine Set.ncard_le_ncard_of_injOn (fun x => toVecD 22 (w12Co2Rep 2) + x) ?_ ?_ (Set.toFinite _)
  · rintro x ⟨hx1, hx0⟩
    obtain ⟨i, hi, e⟩ := (mem_O0 _).1 hx0
    have hxe : x = toVecD 22 (fget Ob.P0 i 22) + toVecD 22 (w12Co2Rep 2) := by
      rw [e, add_comm (toVecD 22 (w12Co2Rep 2)), add_assoc, add_self_vec, add_zero]
    refine ⟨i, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, ?_, ?_⟩), e⟩
    · have hb : bil₀₂ (toVecD 22 (fget Ob.P0 i 22)) (toVecD 22 (w12Co2Rep 2)) = 0 := by
        have hp := polar_q₀₂ (toVecD 22 (fget Ob.P0 i 22)) (toVecD 22 (w12Co2Rep 2))
        rw [← hxe, q_orb (by norm_num) hx1, q_orb (by norm_num) (o0_sub i hi),
          (forms_reps 2 (by norm_num)).2] at hp
        rw [← hp]
        ring
      rw [ob_bil] at hb
      change notB (dotK 22 (fget Ob.P0 i 22) Ob.lam2) = true
      cases hdk : dotK 22 (fget Ob.P0 i 22) Ob.lam2
      · rfl
      · rw [hdk] at hb
        exact absurd hb (by decide)
    · refine iff_of_false ?_ Bool.false_ne_true
      rintro ⟨k, hk, ek⟩
      have ek' : fget Ob.PD2 k 22 = fget Ob.P0 i 22 := ek
      obtain ⟨g, hgfix, hgk⟩ := d2_mem k hk
      have hx1' : co2Act g (toVecD 22 (w12Co2Rep 2) + toVecD 22 Ob.urep) ∈ co2Orbit 1 := by
        rw [co2Act_add, hgfix, ← hgk, ek', add_comm, ← hxe]
        exact hx1
      have e44 := b_orb1 ((orb_act_iff 1 g _).1 hx1')
      rw [b3] at e44
      exact rel_parts.2.2.2.2.2.2.2.2 e44
  · intro a _ b _ h
    exact add_left_cancel h

theorem count2 :
    (co2Orbit 1).ncard * 1232 ≤ (co2Orbit 2).ncard * 28 := by
  exact co2_count z_low c2_hb

theorem ob_rM_apply (m : ℕ) (i j : Fin 22) :
    rowsMatrix 22 (unpackR 22 m) i j = if m.testBit (22 * i.val + j.val) then 1 else 0 := by
  have e : (unpackR 22 m)[i.val]?.getD 0 = m / 2 ^ (22 * i.val) % 2 ^ 22 := by
    simp only [unpackR, Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [rowsMatrix_apply, toVecD_apply, e, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [j.isLt, decide_true, Bool.true_and]
  rw [Nat.add_comm]

theorem ob_rM_xor (a b : ℕ) : rowsMatrix 22 (unpackR 22 (Nat.xor a b)) =
    rowsMatrix 22 (unpackR 22 a) + rowsMatrix 22 (unpackR 22 b) := by
  ext i j
  rw [Matrix.add_apply, ob_rM_apply, ob_rM_apply, ob_rM_apply]
  change (if (a ^^^ b).testBit _ = true then _ else _) = _
  rw [Nat.testBit_xor]
  cases a.testBit (22 * i.val + j.val) <;> cases b.testBit (22 * i.val + j.val) <;> decide

theorem ob_rM_trK (X : ℕ) :
    rowsMatrix 22 (unpackR 22 (trK 22 X)) = (rowsMatrix 22 (unpackR 22 X))ᵀ := by
  rw [← transposeRows_unpackR, rowsMatrix_transposeRows]

theorem hyp_rows (i j : Fin 22) : rowsMatrix 22 (unpackR 22 (hypF 11)) i j =
    if i.val < 11 ∧ j.val = i.val + 11 then 1 else 0 := by
  rw [ob_rM_apply, ob_hyp_bits i.val i.isLt j.val j.isLt]
  by_cases h : i.val < 11 ∧ j.val = i.val + 11 <;> simp [h]

theorem hyp_dot (z : Vec22) : z ⬝ᵥ (rowsMatrix 22 (unpackR 22 (hypF 11)) *ᵥ z) =
    ∑ i : Fin 11, z (Fin.castAdd 11 i) * z (Fin.natAdd 11 i) := by
  have hv : ∀ i : Fin 22, (rowsMatrix 22 (unpackR 22 (hypF 11)) *ᵥ z) i =
      if h : i.val < 11 then z ⟨i.val + 11, by omega⟩ else 0 := by
    intro i
    simp only [Matrix.mulVec, dotProduct, hyp_rows]
    by_cases h : i.val < 11
    · rw [dif_pos h, Finset.sum_eq_single ⟨i.val + 11, by omega⟩]
      · simp [h]
      · intro j _ hj
        rw [if_neg, zero_mul]
        rintro ⟨-, e⟩
        exact hj (Fin.ext e)
      · intro hn
        exact absurd (Finset.mem_univ _) hn
    · rw [dif_neg h]
      exact Finset.sum_eq_zero fun j _ => by rw [if_neg (fun h' => h h'.1), zero_mul]
  change ∑ i : Fin (11 + 11), z i * (rowsMatrix 22 (unpackR 22 (hypF 11)) *ᵥ z) i = _
  rw [Fin.sum_univ_add]
  have h1 : ∀ a : Fin 11, z (Fin.castAdd 11 a) *
      (rowsMatrix 22 (unpackR 22 (hypF 11)) *ᵥ z) (Fin.castAdd 11 a) =
        z (Fin.castAdd 11 a) * z (Fin.natAdd 11 a) := by
    intro a
    rw [hv, dif_pos (by simp)]
    exact congrArg (z (Fin.castAdd 11 a) * ·)
      (congrArg z (Fin.ext (by simp only [Fin.coe_castAdd, Fin.coe_natAdd]; omega)))
  have h2 : ∀ a : Fin 11, z (Fin.natAdd 11 a) *
      (rowsMatrix 22 (unpackR 22 (hypF 11)) *ᵥ z) (Fin.natAdd 11 a) = 0 := by
    intro a
    rw [hv, dif_neg (by simp), mul_zero]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

theorem hyp_MN : rowsMatrix 22 (unpackR 22 Ob.Pm) * rowsMatrix 22 (unpackR 22 Ob.Pmi) = 1 := by
  have h := hyp_ok
  rw [Bool.and_eq_true] at h
  rw [← mat_mulW, Nat.eq_of_beq_eq_true h.1, mat_idF]

theorem hyp_NM : rowsMatrix 22 (unpackR 22 Ob.Pmi) * rowsMatrix 22 (unpackR 22 Ob.Pm) = 1 :=
  (Matrix.mul_eq_one_comm_of_card_eq (Fin 22) (Fin 22) (ZMod 2) rfl).1 hyp_MN

theorem hyp_q (z : Vec22) : q₀₂ (rowsMatrix 22 (unpackR 22 Ob.Pm) *ᵥ z) =
    ∑ i : Fin 11, z (Fin.castAdd 11 i) * z (Fin.natAdd 11 i) := by
  have h := hyp_ok
  rw [Bool.and_eq_true] at h
  obtain ⟨hs, hd⟩ := altK_facts h.2
  have h0 := quad_alt _ hs hd z
  rw [ob_rM_xor, mat_mulW, mat_mulW, ob_rM_trK, mat_Q, Matrix.add_mulVec, dotProduct_add,
    hyp_dot] at h0
  have e1 : z ⬝ᵥ (((rowsMatrix 22 (unpackR 22 Ob.Pm))ᵀ * Qm22 * rowsMatrix 22 (unpackR 22 Ob.Pm))
      *ᵥ z) = q₀₂ (rowsMatrix 22 (unpackR 22 Ob.Pm) *ᵥ z) := by
    unfold q₀₂
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec z,
      Matrix.vecMul_transpose]
  rw [e1] at h0
  generalize q₀₂ (rowsMatrix 22 (unpackR 22 Ob.Pm) *ᵥ z) = a at h0 ⊢
  generalize ∑ i : Fin 11, z (Fin.castAdd 11 i) * z (Fin.natAdd 11 i) = b at h0 ⊢
  calc a = a + (b + b) := by rw [zmod2_add_self, add_zero]
    _ = (a + b) + b := by rw [add_assoc]
    _ = b := by rw [h0, zero_add]

theorem card_S_of (M N : Matrix (Fin 22) (Fin 22) (ZMod 2)) (hMN : M * N = 1) (hNM : N * M = 1)
    (hq : ∀ z : Vec22, q₀₂ (M *ᵥ z) = ∑ i : Fin 11, z (Fin.castAdd 11 i) * z (Fin.natAdd 11 i)) :
    {v : Vec22 | v ≠ 0 ∧ q₀₂ v = 0}.ncard = 2098175 := by
  have hl : Function.LeftInverse (fun v : Vec22 => (N *ᵥ v) ∘ (finSumFinEquiv (m := 11) (n := 11)))
      (fun u : Fin 11 ⊕ Fin 11 → ZMod 2 => M *ᵥ (u ∘ (finSumFinEquiv (m := 11) (n := 11)).symm)) := by
    intro u
    beta_reduce
    rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    funext a
    simp
  have hr : Function.RightInverse (fun v : Vec22 => (N *ᵥ v) ∘ (finSumFinEquiv (m := 11) (n := 11)))
      (fun u : Fin 11 ⊕ Fin 11 → ZMod 2 => M *ᵥ (u ∘ (finSumFinEquiv (m := 11) (n := 11)).symm)) := by
    intro v
    beta_reduce
    have e : ((N *ᵥ v) ∘ (finSumFinEquiv (m := 11) (n := 11))) ∘ (finSumFinEquiv (m := 11) (n := 11)).symm = N *ᵥ v := by
      funext a
      simp
    rw [e, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
  have hc := CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.card_quadPlus_nonzero_singular
    (K := ZMod 2) 11
  have h2 : (2 ^ 11 - 1) * (2 ^ (11 - 1) + 1) = 2098175 := by norm_num
  rw [Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card, h2] at hc
  rw [← Nat.card_coe_set_eq, ← hc]
  refine (Nat.card_congr ((Equiv.mk _ _ hl hr).subtypeEquiv fun u => ?_)).symm
  rw [Equiv.coe_fn_mk]
  change _ ↔ M *ᵥ (u ∘ (finSumFinEquiv (m := 11) (n := 11)).symm) ≠ 0 ∧ q₀₂ (M *ᵥ (u ∘ (finSumFinEquiv (m := 11) (n := 11)).symm)) = 0
  have h0 : M *ᵥ ((0 : Fin 11 ⊕ Fin 11 → ZMod 2) ∘ (finSumFinEquiv (m := 11) (n := 11)).symm) = 0 := by
    have e : ((0 : Fin 11 ⊕ Fin 11 → ZMod 2) ∘ (finSumFinEquiv (m := 11) (n := 11)).symm) = 0 := rfl
    rw [e, Matrix.mulVec_zero]
  have hne : M *ᵥ (u ∘ (finSumFinEquiv (m := 11) (n := 11)).symm) ≠ 0 ↔ u ≠ 0 := hl.injective.ne_iff' h0
  rw [hq, CFSG.LieType.Universal.Spin.quadPlus_apply, hne]
  simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd]

theorem card_S : {v : Vec22 | v ≠ 0 ∧ q₀₂ v = 0}.ncard = 2098175 :=
  card_S_of _ _ hyp_MN hyp_NM hyp_q

theorem orb_cover (v : Vec22) (hv : v ≠ 0) (hq : q₀₂ v = 0) :
    v ∈ co2Orbit 0 ∨ v ∈ co2Orbit 1 ∨ v ∈ co2Orbit 2 := by
  have hi : ∀ i < 3, co2Orbit i ⊆ {v : Vec22 | v ≠ 0 ∧ q₀₂ v = 0} := by
    rintro i hi _ ⟨g, rfl⟩
    have hg0 : co2Act g (toVecD 22 (w12Co2Rep i)) ≠ 0 := by
      intro h0
      apply (forms_reps i hi).1
      rw [← co2Act_inv_apply g (toVecD 22 (w12Co2Rep i)), h0, map_zero]
    exact ⟨hg0, q_orb hi ⟨g, rfl⟩⟩
  have hsub : co2Orbit 0 ∪ co2Orbit 1 ∪ co2Orbit 2 ⊆ {v : Vec22 | v ≠ 0 ∧ q₀₂ v = 0} :=
    Set.union_subset (Set.union_subset (hi 0 (by norm_num)) (hi 1 (by norm_num)))
      (hi 2 (by norm_num))
  have hcard : 2098175 ≤ (co2Orbit 0 ∪ co2Orbit 1 ∪ co2Orbit 2).ncard := by
    rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨orb_disj r2_not0, orb_disj r2_not1⟩),
      Set.ncard_union_eq (orb_disj r1_not0)]
    have h1 := count1
    have h2 := count2
    rw [n0_eq] at h1 ⊢
    linarith
  have he := Set.eq_of_subset_of_ncard_le hsub (by rw [card_S]; exact hcard)
  have hm : v ∈ {v : Vec22 | v ≠ 0 ∧ q₀₂ v = 0} := ⟨hv, hq⟩
  rw [← he] at hm
  rcases hm with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem span_top_of_mul {d : ℕ} (M N : Matrix (Fin d) (Fin d) (ZMod 2))
    (hMN : M * N = 1) (S : Set (Fin d → ZMod 2))
    (hrow : ∀ j : Fin d, N j ∈ Submodule.span (ZMod 2) S) :
    Submodule.span (ZMod 2) S = ⊤ := by
  have hsingle : ∀ i : Fin d, (Pi.single i 1 : Fin d → ZMod 2) ∈ Submodule.span (ZMod 2) S := by
    intro i
    have e : (Pi.single i 1 : Fin d → ZMod 2) = ∑ j, M i j • N j := by
      funext k
      have h := congrFun (congrFun hMN i) k
      rw [Matrix.mul_apply] at h
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h, Matrix.one_apply, Pi.single_apply]
      by_cases hik : i = k
      · subst hik
        simp
      · rw [if_neg hik, if_neg (Ne.symm hik)]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hrow j)
  rw [Submodule.eq_top_iff']
  intro x
  have hx : x = ∑ i, x i • (Pi.single i 1 : Fin d → ZMod 2) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsingle i)

theorem ob_unpack_getD (X : Nat) (i : Fin 22) : (unpackR 22 X)[i.val]?.getD 0 = rowF 22 X i.val := by
  have e : (unpackR 22 X)[i.val]? = some (rowF 22 X i.val) := by
    simp [unpackR, rowF_eq, i.isLt]
  rw [e, Option.getD_some]

theorem orb_span : Submodule.span (ZMod 2) (co2Orbit 0) = ⊤ := by
  have h := span_ok
  simp only [Bool.and_eq_true] at h
  have hMN : rowsMatrix 22 (unpackR 22 (packL 22 (ptsL 22 Ob.P0 Ob.bidx))) *
      rowsMatrix 22 (unpackR 22 Ob.Bi) = 1 := by
    rw [← mat_mulW, Nat.eq_of_beq_eq_true h.2, mat_idF]
  have hNM := (Matrix.mul_eq_one_comm_of_card_eq (Fin 22) (Fin 22) (ZMod 2) rfl).1 hMN
  refine span_top_of_mul _ _ hNM (co2Orbit 0) fun j => ?_
  obtain ⟨hlt, hrow⟩ := ob_span_rows j.val j.isLt
  have e : rowsMatrix 22 (unpackR 22 (packL 22 (ptsL 22 Ob.P0 Ob.bidx))) j =
      toVecD 22 (fget Ob.P0 (getL 0 Ob.bidx j.val) 22) := by
    funext c
    rw [rowsMatrix_apply, ob_unpack_getD, hrow]
  rw [e]
  exact Submodule.subset_span (o0_sub _ hlt)

end CertificateChecks.KernelCo2W11

end
