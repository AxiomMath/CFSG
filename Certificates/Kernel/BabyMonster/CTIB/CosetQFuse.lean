module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQOrb
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB

set_option exponentiation.threshold 1024

variable {G : Array ℕ} {AP k Bs T : ℕ}

theorem land_pow (x k : ℕ) : Nat.land x (Nat.sub (Nat.shiftLeft 1 k) 1) = x % 2 ^ k := by
  rw [shl_eq, Nat.shiftLeft_eq, Nat.one_mul, sub_eq, land_eq, Nat.and_two_pow_sub_one_eq_mod]

@[expose] noncomputable def ptIdxC (LO A k Bs T VT PT u : ℕ) : ℕ :=
  if xorFields T (u % 2 ^ 22) >>> (22 - k) = 0 ∧ vInv VT (xorFields T (u % 2 ^ 22) >>> k) then
    (if vSpl VT (xorFields T (u % 2 ^ 22) >>> k) = 0 then vEnt0 VT (xorFields T (u % 2 ^ 22) >>> k)
    else if conjK LO A (xorFields Bs (((xorFields T (u % 2 ^ 22) ^^^
          xorFields T (repOf PT (vEnt0 VT (xorFields T (u % 2 ^ 22) >>> k)) % 2 ^ 22)) % 2 ^ k)
          <<< (22 - k))) (repOf PT (vEnt0 VT (xorFields T (u % 2 ^ 22) >>> k))) = u
      then vEnt0 VT (xorFields T (u % 2 ^ 22) >>> k) else vEnt1 VT (xorFields T (u % 2 ^ 22) >>> k))
  else 1024

theorem ptIdxK_eq (LO A k Bs T VT PT u : ℕ) :
    ptIdxK LO A k Bs T VT PT u = ptIdxC LO A k Bs T VT PT u := by
  unfold ptIdxK ptIdxC vEnt0 vEnt1 vSpl vInv
  beta_reduce
  simp only [land_mod, land_pow]
  simp only [brec_eq, andB_eq, Bool.and_eq_true, beq_true, shr_eq, sub_eq, xor_eq, shl_eq]

theorem labOfK_eq (LO A k Bs T VT PT u : ℕ) : labOfK LO A k Bs T VT PT u =
    if ptIdxK LO A k Bs T VT PT u = 1024 then 8 else labOf PT (ptIdxK LO A k Bs T VT PT u) := by
  unfold labOfK
  simp only [brec_eq, beq_true]

theorem labOf_lt (PT p : ℕ) : labOf PT p < 8 := lt_of_le_of_lt Nat.and_le_right (by decide)

theorem closOK_spec {LO A Bs VT PT : ℕ} {Gs Ds : List ℕ} {off q t : ℕ} (ht : t < 15)
    (h : closOK LO A k Bs T VT PT Gs Ds off (q * 15 + t) = true) :
    ptIdxK LO A k Bs T VT PT (mulQ LO (nthN Ds (off + t)) (autQ LO (nthN Gs (off + t))
      (repOf PT q))) ≠ 1024 ∧
    labOf PT (ptIdxK LO A k Bs T VT PT (mulQ LO (nthN Ds (off + t)) (autQ LO (nthN Gs (off + t))
      (repOf PT q)))) = labOf PT q := by
  unfold closOK at h
  have e1 : Nat.div (q * 15 + t) 15 = q := by
    change (q * 15 + t) / 15 = q
    omega
  have e2 : Nat.add off (Nat.mod (q * 15 + t) 15) = off + t := by
    change off + (q * 15 + t) % 15 = off + t
    omega
  rw [e1, e2, beq_true, labOfK_eq] at h
  by_cases h0 : ptIdxK LO A k Bs T VT PT (mulQ LO (nthN Ds (off + t)) (autQ LO (nthN Gs (off + t))
      (repOf PT q))) = 1024
  · rw [ite_eq_left h0] at h
    exact absurd h (Nat.ne_of_gt (labOf_lt PT q))
  · rw [ite_eq_right h0] at h
    exact ⟨h0, h⟩

@[expose] noncomputable def trPar (TR q : ℕ) : ℕ := Nat.sub (Nat.land (fld32 TR q) 1023) 1

@[expose] noncomputable def trGen (TR q : ℕ) : ℕ := Nat.land (Nat.shiftRight (fld32 TR q) 10) 15

@[expose] noncomputable def trDep (TR q : ℕ) : ℕ := Nat.shiftRight (fld32 TR q) 14

theorem trOK_spec {LO A Bs VT PT TR RT npts : ℕ} {Gs Ds : List ℕ} {off q : ℕ}
    (h : trOK LO A k Bs T VT PT TR RT npts Gs Ds off q = true) :
    (fld32 TR q = 0 → ∀ q' < q, labOf PT q' ≠ labOf PT q) ∧
    (fld32 TR q ≠ 0 → trPar TR q < npts ∧ trGen TR q < 15 ∧ trDep TR (trPar TR q) < trDep TR q ∧
      ptIdxK LO A k Bs T VT PT (mulQ LO (nthN Ds (off + trGen TR q))
        (autQ LO (nthN Gs (off + trGen TR q)) (repOf PT (trPar TR q)))) = q) := by
  unfold trOK at h
  beta_reduce at h
  rw [brec_eq] at h
  by_cases he : fld32 TR q = 0
  · rw [ite_eq_left (beq_true.2 he), andB_true, allLt_true] at h
    refine ⟨fun _ q' hq' e => ?_, fun h' => absurd he h'⟩
    have h2 := h.2 q' hq'
    rw [notB_true, e, Nat.beq_refl] at h2
    exact absurd h2 (by decide)
  · rw [ite_eq_right (fun h' => he (beq_true.1 h'))] at h
    simp only [andB_true, blt_true, beq_true] at h
    exact ⟨fun h' => absurd h' he, fun _ => h⟩

theorem dOK_spec {LO A GP d : ℕ} (h : dOK LO A GP d = true) : d < 2 ^ 23 ∧
    ∀ i < 22, mulQ LO d (autQ LO GP (fld32 A i)) = mulQ LO (autQ LO A (fld32 GP i)) d := by
  unfold dOK at h
  rw [andB_true, blt_true, allLt_true] at h
  exact ⟨h.1, fun i hi => beq_true.1 (h.2 i hi)⟩

theorem incOK_mono {PT n : ℕ} (h : incOK PT n = true) {p q : ℕ} (hpq : p ≤ q) (hq : q < n) :
    repOf PT p ≤ repOf PT q := by
  unfold incOK at h
  rw [allLt_true] at h
  induction q with
  | zero => rw [Nat.le_zero.1 hpq]
  | succ q ih =>
    rcases Nat.lt_or_eq_of_le hpq with h1 | h1
    · have h2 := blt_true.1 (h q (by change q < n - 1; omega))
      exact le_trans (ih (by omega) (by omega)) (Nat.le_of_lt h2)
    · rw [h1]

theorem incOK_inj {PT n : ℕ} (h : incOK PT n = true) {p q : ℕ} (hp : p < n) (hq : q < n)
    (he : repOf PT p = repOf PT q) : p = q := by
  have hs : ∀ a b, a < b → b < n → repOf PT a < repOf PT b := fun a b hab hb => by
    unfold incOK at h
    rw [allLt_true] at h
    have h2 := blt_true.1 (h a (by change a < n - 1; omega))
    exact lt_of_lt_of_le h2 (incOK_mono (by unfold incOK; rw [allLt_true]; exact h) hab hb)
  rcases Nat.lt_trichotomy p q with h1 | h1 | h1
  · exact absurd he (Nat.ne_of_lt (hs p q h1 hq))
  · exact h1
  · exact absurd he.symm (Nat.ne_of_lt (hs q p h1 hp))

theorem cjQ_inv (φ : QC G →* QC G) (e n : QC G) : cjQ φ e⁻¹ (cjQ φ e n) = n := by
  rw [← cjQ_mul, mul_inv_cancel, cjQ_one]

theorem delta_rel (hS : Setup G AP k Bs T) {GP d : ℕ} (hG : SymG G)
    (hr : relOK (loOf G) GP = true) (hd : dOK (loOf G) AP GP d = true) (y : QC G) :
    mkQ d (dOK_spec hd).1 * homOf G (arrOf GP) (relOK_spec G hG hr).2 (phiS hS y) =
      phiS hS (homOf G (arrOf GP) (relOK_spec G hG hr).2 y) * mkQ d (dOK_spec hd).1 := by
  set β := homOf G (arrOf GP) (relOK_spec G hG hr).2
  set D : QC G := mkQ d (dOK_spec hd).1
  have hwfG : ∀ i < 22, (arrOf GP).getD i 0 < 2 ^ 23 := fun i hi => by
    rw [arrOf_getD _ hi]
    exact (relOK_spec G hG hr).1 i hi
  let ψ : QC G →* QC G :=
    { toFun := fun y => D⁻¹ * phiS hS (β y) * D
      map_one' := by simp
      map_mul' := fun a b => by simp only [map_mul, mul_assoc, mul_inv_cancel_left] }
  have key : ∀ y, β (phiS hS y) = ψ y := by
    refine hom_ext' (φ := β.comp (phiS hS)) (ψ := ψ) ?_ (fun i hi => ?_)
    · change β (phiS hS xQ) = D⁻¹ * phiS hS (β xQ) * D
      rw [phiS_x hS, hom_x, phiS_x hS, mul_assoc, xQ_comm D, ← mul_assoc, inv_mul_cancel, one_mul]
    · change β (phiS hS (eK i hi)) = D⁻¹ * phiS hS (β (eK i hi)) * D
      have e1 : D * β (phiS hS (eK i hi)) = phiS hS (β (eK i hi)) * D := by
        refine QC.ext' ?_
        rw [QC.mul_val, QC.mul_val]
        have h2 := (dOK_spec hd).2 i hi
        rw [mulQ_loOf G hG, mulQ_loOf G hG, autQ_loOf G hG, autQ_loOf G hG] at h2
        have ea : (phiS hS (eK i hi)).1 = fld32 AP i := by
          rw [phiS, homOf_val]
          change autApply G (arrOf AP) (2 ^ i) = _
          rw [autApply_two_pow G _ hi (wfA hS i hi), arrOf_getD _ hi]
        have eb : (β (eK i hi)).1 = fld32 GP i := by
          rw [homOf_val]
          change autApply G (arrOf GP) (2 ^ i) = _
          rw [autApply_two_pow G _ hi (hwfG i hi), arrOf_getD _ hi]
        rw [homOf_val, ea, phiS, homOf_val, eb, mkQ_val]
        exact h2
      rw [mul_assoc, ← e1, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [key y]
  change D * (D⁻¹ * phiS hS (β y) * D) = _
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]

theorem fuse_cj (hS : Setup G AP k Bs T) {GP d : ℕ} (hG : SymG G)
    (hr : relOK (loOf G) GP = true) (hd : dOK (loOf G) AP GP d = true) (e n : QC G) :
    mkQ d (dOK_spec hd).1 * homOf G (arrOf GP) (relOK_spec G hG hr).2 (cjQ (phiS hS) e n) =
      cjQ (phiS hS) (homOf G (arrOf GP) (relOK_spec G hG hr).2 e)
        (mkQ d (dOK_spec hd).1 * homOf G (arrOf GP) (relOK_spec G hG hr).2 n) := by
  have h := delta_rel hS hG hr hd e⁻¹
  simp only [cjQ, map_mul, map_inv] at h ⊢
  rw [← mul_assoc, ← mul_assoc, h]
  simp only [mul_assoc]

structure RankOK (G : Array ℕ) (AP k Bs T w VT PT TR RT npts : ℕ) (Gs Ds : List ℕ) (off : ℕ) :
    Prop where
  symm : SymG G
  setup : setupOK (loOf G) AP k Bs T = true
  hk : k ≤ 11
  hw : w = 0 ∨ w = 2 ^ 22
  v : ∀ j < 2 ^ (22 - 2 * k), vOK (loOf G) AP w k Bs T VT PT npts j = true
  pt : ∀ p < npts, ptOK (loOf G) AP w k Bs T PT p = true
  inc : incOK PT npts = true
  clos : ∀ q < npts * 15, closOK (loOf G) AP k Bs T VT PT Gs Ds off q = true
  tr : ∀ q < npts, trOK (loOf G) AP k Bs T VT PT TR RT npts Gs Ds off q = true
  d : ∀ t < 15, dOK (loOf G) AP (nthN Gs (off + t)) (nthN Ds (off + t)) = true
  rel : ∀ t < 15, relOK (loOf G) (nthN Gs (off + t)) = true

variable {w VT PT TR RT npts : ℕ} {Gs Ds : List ℕ} {off : ℕ}

theorem rep_least (R : RankOK G AP k Bs T w VT PT TR RT npts Gs Ds off) {q : ℕ} (hq : q < npts)
    (e : QC G) : repOf PT q ≤ (cjQ (phiS (setup_of R.symm R.setup)) e (repQ PT q)).1 := by
  obtain ⟨S, hS1, -, hS3⟩ := qorb_facts R.symm (setup_of R.symm R.setup) R.hk R.hw (R.pt q hq)
  exact (hS3 _ ((hS1 _).2 ((reach_qconj _ (repQ PT q) _).2 ⟨e, rfl⟩))).2

theorem orbit_inter (R : RankOK G AP k Bs T w VT PT TR RT npts Gs Ds off) {q q' : ℕ}
    (hq : q < npts) (hq' : q' < npts) {e e' : QC G}
    (h : cjQ (phiS (setup_of R.symm R.setup)) e (repQ PT q) =
      cjQ (phiS (setup_of R.symm R.setup)) e' (repQ PT q')) : q = q' := by
  set φ := phiS (setup_of R.symm R.setup)
  have h1 : repQ (G := G) PT q = cjQ φ (e' * e⁻¹) (repQ PT q') := by
    rw [cjQ_mul, ← h, cjQ_inv]
  have h2 : repQ (G := G) PT q' = cjQ φ (e * e'⁻¹) (repQ PT q) := by
    rw [cjQ_mul, h, cjQ_inv]
  have l1 := rep_least R hq' (e' * e⁻¹)
  have l2 := rep_least R hq (e * e'⁻¹)
  rw [← h1, repQ_val] at l1
  rw [← h2, repQ_val] at l2
  exact incOK_inj R.inc hq hq' (Nat.le_antisymm l2 l1)

theorem vSpl_le (VT j : ℕ) : vSpl VT j ≤ 1 := Nat.and_le_right

theorem pt_target (R : RankOK G AP k Bs T w VT PT TR RT npts Gs Ds off) {u : QC G}
    (h : ptIdxK (loOf G) AP k Bs T VT PT u.1 ≠ 1024) :
    ptIdxK (loOf G) AP k Bs T VT PT u.1 < npts ∧
      ∃ e, u = cjQ (phiS (setup_of R.symm R.setup)) e
        (repQ PT (ptIdxK (loOf G) AP k Bs T VT PT u.1)) := by
  have hS : Setup G AP k Bs T := setup_of R.symm R.setup
  have hk := R.hk
  rw [ptIdxK_eq] at h ⊢
  unfold ptIdxC at h ⊢
  have hu : u.1 % 2 ^ 22 = piQ u := rfl
  by_cases hc : xorFields T (u.1 % 2 ^ 22) >>> (22 - k) = 0 ∧
      vInv VT (xorFields T (u.1 % 2 ^ 22) >>> k)
  · rw [ite_eq_left hc]
    have hTl : xorFields T (u.1 % 2 ^ 22) < 2 ^ (22 - k) := lt_iff_shr_zero.2 hc.1
    have hj : xorFields T (u.1 % 2 ^ 22) >>> k < 2 ^ (22 - 2 * k) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add,
        (by omega : 22 - 2 * k + k = 22 - k)]
      exact hTl
    obtain ⟨hv1, -⟩ := vOK_spec (R.v _ hj)
    obtain ⟨hp0, hvix0, hsp0, hs1⟩ := hv1 hc.2
    have hm22 : ∀ x, x % 2 ^ 22 < 2 ^ 22 := fun x => Nat.mod_lt _ (Nat.two_pow_pos 22)
    have hvec : ∀ p, vixOf k T PT p = xorFields T (u.1 % 2 ^ 22) >>> k →
        xorFields T ((u.1 % 2 ^ 22) ^^^ repOf PT p % 2 ^ 22) < 2 ^ k := fun p hp => by
      unfold vixOf at hp
      rw [shr_eq, land_mod] at hp
      rw [xorFields_xor T (hm22 _) (hm22 _)]
      exact xor_lt_iff.2 hp.symm
    have hsplitw : ∀ p, p < npts → splitOf PT p = 1 →
        vixOf k T PT p = xorFields T (u.1 % 2 ^ 22) >>> k →
        piQ (cjQ (phiS hS) (eIm hS (xorFields T ((u.1 % 2 ^ 22) ^^^ repOf PT p % 2 ^ 22)))
          (repQ PT p)) = piQ u := fun p _ _ hp => by
      rw [piQ_split hS (by omega) _ (hvec p hp), hS.bt _ (Nat.xor_lt_two_pow (hm22 _) (hm22 _)),
        piQ, repQ_val, Nat.xor_comm (u.1 % 2 ^ 22), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      rfl
    by_cases hs : vSpl VT (xorFields T (u.1 % 2 ^ 22) >>> k) = 0
    · rw [ite_eq_left hs]
      refine ⟨hp0, ?_⟩
      have hns : splitOf PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)) ≠ 1 := by
        rw [hsp0, hs]
        decide
      obtain ⟨-, -, -, hfull⟩ := ptOK_spec (R.pt _ hp0)
      obtain ⟨hwit, hwx, -, -⟩ := hfull hns
      have hfx := wit_of_spec R.symm hS hwit hwx
      obtain ⟨e, he⟩ := (orbit_full hS (by omega) hfx u.1).2 ⟨u.2, by
        rw [repQ_val, xor_mod]
        exact hvec _ hvix0⟩
      exact ⟨e, QC.ext' he⟩
    · rw [ite_eq_right hs]
      have hs' : vSpl VT (xorFields T (u.1 % 2 ^ 22) >>> k) = 1 := by
        have := vSpl_le VT (xorFields T (u.1 % 2 ^ 22) >>> k)
        omega
      obtain ⟨hp1, hvix1, hsp1, hne⟩ := hs1 hs'
      have hsp0' : splitOf PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)) = 1 := by
        rw [hsp0, hs']
      have hc0 := hvec _ hvix0
      have e0 : conjK (loOf G) AP (xorFields Bs (((xorFields T (u.1 % 2 ^ 22) ^^^
          xorFields T (repOf PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)) % 2 ^ 22)) % 2 ^ k)
          <<< (22 - k))) (repOf PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k))) =
          (cjQ (phiS hS) (eIm hS (xorFields T ((u.1 % 2 ^ 22) ^^^
            repOf PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)) % 2 ^ 22)))
            (repQ PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)))).1 := by
        rw [← xorFields_xor T (hm22 _) (hm22 _), Nat.mod_eq_of_lt hc0, ← eIm_val hS (by omega) hc0]
        exact conjK_eq R.symm hS.rel (eIm hS (xorFields T (u.1 % 2 ^ 22 ^^^
          repOf PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)) % 2 ^ 22)))
          (repQ PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)))
      rw [e0]
      have hw0 := hsplitw _ hp0 hsp0' hvix0
      by_cases ht : (cjQ (phiS hS) (eIm hS (xorFields T ((u.1 % 2 ^ 22) ^^^
          repOf PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)) % 2 ^ 22)))
          (repQ PT (vEnt0 VT (xorFields T (u.1 % 2 ^ 22) >>> k)))).1 = u.1
      · rw [ite_eq_left ht]
        exact ⟨hp0, _, (QC.ext' ht).symm⟩
      · rw [ite_eq_right ht]
        refine ⟨hp1, ?_⟩
        have hw1 := hsplitw _ hp1 hsp1 hvix1
        rcases eq_or_x hw1.symm with h1 | h1
        · exact ⟨_, h1⟩
        · exfalso
          rcases eq_or_x hw0.symm with h2 | h2
          · have h4 := congrArg (fun z : QC G => z.1) h2
            exact ht h4.symm
          · have h3 := mul_right_cancel (h1.symm.trans h2)
            exact hne (orbit_inter R hp0 hp1 h3.symm)
  · rw [ite_eq_right hc] at h
    exact absurd rfl h

theorem reach_trans {act act' : ℕ → ℕ → ℕ} {ngen ngen' root x m : ℕ}
    (hsub : ∀ i < ngen', ∃ i' < ngen, ∀ n, act' i n = act i' n)
    (hx : Reach act ngen root x) (h : Reach act' ngen' x m) : Reach act ngen root m := by
  induction h with
  | root => exact hx
  | step i hi _ ih =>
    obtain ⟨i', hi', he⟩ := hsub i hi
    rw [he]
    exact Reach.step i' hi' ih

theorem fuse_val {d : ℕ} {A : Array ℕ} (hA : RelOK G A) (hd : d < 2 ^ 23) (n : QC G) :
    fuse G A d n.1 = (mkQ d hd * homOf G A hA n).1 := by
  unfold fuse
  rw [QC.mul_val, homOf_val, mkQ_val]

theorem kfuse (hG : SymG G) (GP d r : ℕ) :
    mulQ (loOf G) d (autQ (loOf G) GP r) = fuse G (arrOf GP) d r := by
  unfold fuse
  rw [mulQ_loOf G hG, autQ_loOf G hG]

theorem forb_facts (R : RankOK G AP k Bs T w VT PT TR RT npts Gs Ds off) (act : ℕ → ℕ → ℕ)
    (hact1 : ∀ i < 22, ∀ n, act i n = qconj G (arrOf AP) i n)
    (hact2 : ∀ t < 15, ∀ n,
      act (22 + t) n = fuse G (arrOf (nthN Gs (off + t))) (nthN Ds (off + t)) n)
    {p : ℕ} (hp : p < npts) (hmin : ∀ q < p, labOf PT q ≠ labOf PT p) :
    ∃ S : Finset ℕ, (∀ m, m ∈ S ↔ Reach act 37 (repOf PT p) m) ∧
      S.card = ((Finset.range npts).filter (fun q => labOf PT q = labOf PT p)).sum
        (sizeOf k PT) ∧
      (∀ m ∈ S, (m < 2 ^ 23 ∧ isInv G (arrOf AP) w m = true) ∧ repOf PT p ≤ m) ∧
      ∀ q < npts, (repOf PT q ∈ S ↔ labOf PT q = labOf PT p) := by
  have hS : Setup G AP k Bs T := setup_of R.symm R.setup
  have hO : ∀ q < npts, ∃ S : Finset ℕ,
      (∀ m, m ∈ S ↔ ∃ e : QC G, m = (cjQ (phiS hS) e (repQ PT q)).1) ∧
      S.card = sizeOf k PT q ∧ ∀ m ∈ S, (m < 2 ^ 23 ∧ isInv G (arrOf AP) w m = true) := by
    intro q hq
    obtain ⟨S, h1, h2, h3⟩ := qorb_facts R.symm hS R.hk R.hw (R.pt q hq)
    exact ⟨S, fun m => (h1 m).trans (reach_qconj hS (repQ PT q) m), h2, fun m hm => (h3 m hm).1⟩
  choose! O hOmem hOcard hOval using hO
  have memS : ∀ m, m ∈ ((Finset.range npts).filter (fun q => labOf PT q = labOf PT p)).biUnion O ↔
      ∃ q < npts, labOf PT q = labOf PT p ∧ ∃ e : QC G, m = (cjQ (phiS hS) e (repQ PT q)).1 := by
    intro m
    rw [Finset.mem_biUnion]
    constructor
    · rintro ⟨q, hq, hm⟩
      rw [Finset.mem_filter, Finset.mem_range] at hq
      exact ⟨q, hq.1, hq.2, (hOmem q hq.1 m).1 hm⟩
    · rintro ⟨q, hq, hl, he⟩
      exact ⟨q, Finset.mem_filter.2 ⟨Finset.mem_range.2 hq, hl⟩, (hOmem q hq m).2 he⟩
  have hsub : ∀ i < 22, ∃ i' < 37, ∀ n, qconj G (arrOf AP) i n = act i' n :=
    fun i hi => ⟨i, by omega, fun n => (hact1 i hi n).symm⟩
  have fstep : ∀ q < npts, ∀ t < 15, ∃ hd : nthN Ds (off + t) < 2 ^ 23,
      ∃ hr : RelOK G (arrOf (nthN Gs (off + t))),
      (mkQ (nthN Ds (off + t)) hd * homOf G (arrOf (nthN Gs (off + t))) hr (repQ PT q)).1 =
        mulQ (loOf G) (nthN Ds (off + t)) (autQ (loOf G) (nthN Gs (off + t)) (repOf PT q)) :=
    fun q _ t ht => ⟨(dOK_spec (R.d t ht)).1, (relOK_spec G R.symm (R.rel t ht)).2, by
      rw [kfuse R.symm]
      exact (fuse_val (relOK_spec G R.symm (R.rel t ht)).2 (dOK_spec (R.d t ht)).1
        (repQ PT q)).symm⟩
  have reach_rep : ∀ dep, ∀ q < npts, labOf PT q = labOf PT p → trDep TR q = dep →
      Reach act 37 (repOf PT p) (repOf PT q) := by
    intro dep
    induction dep using Nat.strong_induction_on with
    | _ dep ih =>
      intro q hq hl hdq
      obtain ⟨hroot, hnon⟩ := trOK_spec (R.tr q hq)
      by_cases h0 : fld32 TR q = 0
      · have hqp : q = p := by
          rcases Nat.lt_trichotomy q p with h | h | h
          · exact absurd hl (hmin q h)
          · exact h
          · exact absurd hl.symm (hroot h0 p h)
        rw [hqp]
        exact Reach.root
      · obtain ⟨hpar, hgen, hdep, hidx⟩ := hnon h0
        obtain ⟨hne, hlab⟩ := closOK_spec hgen (R.clos (trPar TR q * 15 + trGen TR q) (by omega))
        rw [hidx] at hlab
        have hrp := ih (trDep TR (trPar TR q)) (by rw [← hdq]; exact hdep) (trPar TR q) hpar
          (hlab.symm.trans hl) rfl
        obtain ⟨hd, hr, hu⟩ := fstep _ hpar _ hgen
        have hst := Reach.step (act := act) (22 + trGen TR q) (by omega) hrp
        rw [hact2 _ hgen, ← kfuse R.symm, ← hu] at hst
        rw [← hu] at hidx hne
        obtain ⟨-, e, he⟩ := pt_target R hne
        rw [hidx] at he
        have hq' : repOf PT q = (cjQ (phiS hS) e⁻¹ (mkQ (nthN Ds (off + trGen TR q)) hd *
            homOf G (arrOf (nthN Gs (off + trGen TR q))) hr (repQ PT (trPar TR q)))).1 := by
          rw [he, cjQ_inv]
          rfl
        rw [hq']
        exact reach_trans hsub hst ((reach_qconj hS (mkQ (nthN Ds (off + trGen TR q)) hd *
          homOf G (arrOf (nthN Gs (off + trGen TR q))) hr (repQ PT (trPar TR q))) _).2 ⟨_, rfl⟩)
  refine ⟨((Finset.range npts).filter (fun q => labOf PT q = labOf PT p)).biUnion O,
    fun m => ?_, ?_, fun m hm => ?_, fun q hq => ?_⟩
  · rw [memS]
    constructor
    · rintro ⟨q, hq, hl, e, rfl⟩
      exact reach_trans hsub (reach_rep _ q hq hl rfl) ((reach_qconj hS (repQ PT q) _).2 ⟨e, rfl⟩)
    · intro h
      induction h with
      | root => exact ⟨p, hp, rfl, 1, by rw [cjQ_one]; rfl⟩
      | step i hi _ ih =>
        obtain ⟨q, hq, hl, e, rfl⟩ := ih
        by_cases hi22 : i < 22
        · refine ⟨q, hq, hl, e * eK i hi22, ?_⟩
          rw [hact1 i hi22, cjQ_mul]
          exact qconj_eq hS.rel (wfA hS) hi22 _
        · obtain ⟨t, rfl⟩ : ∃ t, i = 22 + t := ⟨i - 22, by omega⟩
          have ht : t < 15 := by omega
          obtain ⟨hd, hr, hu⟩ := fstep q hq t ht
          obtain ⟨hne, hlab⟩ := closOK_spec ht (R.clos (q * 15 + t) (by omega))
          rw [← hu] at hne hlab
          obtain ⟨hq', e', he'⟩ := pt_target R hne
          refine ⟨_, hq', hlab.trans hl, e' * homOf G (arrOf (nthN Gs (off + t))) hr e, ?_⟩
          rw [hact2 t ht, fuse_val hr hd, fuse_cj hS R.symm (R.rel t ht) (R.d t ht) e
            (repQ PT q), cjQ_mul, ← he']
  · rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl fun q hq => ?_
      exact hOcard q (Finset.mem_range.1 (Finset.mem_filter.1 hq).1)
    · intro q hq q' hq' hne
      rw [Function.onFun, Finset.disjoint_left]
      intro m h1 h2
      have hq1 := Finset.mem_range.1 (Finset.mem_filter.1 hq).1
      have hq2 := Finset.mem_range.1 (Finset.mem_filter.1 hq').1
      obtain ⟨e, he⟩ := (hOmem q hq1 m).1 h1
      obtain ⟨e', he'⟩ := (hOmem q' hq2 m).1 h2
      exact hne (orbit_inter R hq1 hq2 (QC.ext' (he.symm.trans he')))
  · obtain ⟨q, hq, hl, e, he⟩ := (memS m).1 hm
    refine ⟨hOval q hq m ((hOmem q hq m).2 ⟨e, he⟩), ?_⟩
    have hpq : p ≤ q := by
      by_contra h
      exact hmin q (by omega) hl
    rw [he]
    exact le_trans (incOK_mono R.inc hpq hq) (rep_least R hq e)
  · rw [memS]
    constructor
    · rintro ⟨q', hq', hl, e, he⟩
      have := orbit_inter R hq hq' (e := 1) (e' := e) (QC.ext' (by rw [cjQ_one]; exact he))
      rw [this]
      exact hl
    · intro hl
      exact ⟨q, hq, hl, 1, by rw [cjQ_one]; rfl⟩

end CertificateChecks.KernelBM.CTIB.CosetQ

end
