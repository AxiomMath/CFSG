module

public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Certificates.Data.CFSGNative.Solomon.Co1T13
public import Certificates.Kernel.Co1T13K.Chk
public import Certificates.Kernel.Co1T13K.Cnt0
public import Certificates.Kernel.Co1T13K.Cnt1
public import Certificates.Kernel.Co1T13K.Span
public import Certificates.Certificate13504Base
public import Certificates.Kernel.Co1FiveL.Glue
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.Certificates.Kernel.Co1Seven.CenSound
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Sporadic.Co1Block.TwoBTri

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1T13K

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT CFSG.KC.Co1BBound
  CFSG.KC.Co1T13K CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Co1Block CertificateChecks.KernelSporSch.Co1Packed CertificateChecks.KernelCo1B
open CertificateChecks.KernelCo1B.Bound17591 (XB memK_of_mem mem_of_memK filter_length
  cntTab_blocks)
open CertificateChecks.KernelCo1FiveL (colA toVecD_colA colA_lt toVecD_vmF_trK)
open Matrix

local notation "U" => CFSG.KS.Raw.unpack 24 24
local notation "M24" => Matrix (Fin 24) (Fin 24) (ZMod 2)

theorem andB_eq3 (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq3 (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

theorem mulVec_inj (g : GL24) {x y : Fin 24 → ZMod 2} (h : (g : M24) *ᵥ x = (g : M24) *ᵥ y) :
    x = y := by
  have e := congrArg (fun z => ((g⁻¹ : GL24) : M24) *ᵥ z) h
  simpa [Matrix.mulVec_mulVec] using e

theorem getL_get : ∀ (L : List ℕ) (i : ℕ) (h : i < L.length), getL 0 L i = L[i]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: L, i + 1, h => getL_get L i (by simpa using h)

theorem inL_iff (x : ℕ) : ∀ l : List ℕ, inL x l = true ↔ x ∈ l
  | [] => by
    change false = true ↔ _
    simp
  | y :: l => by
    change Bool.rec (motive := fun _ => Bool) (inL x l) true (Nat.beq x y) = true ↔ x ∈ y :: l
    rw [List.mem_cons, ← inL_iff x l]
    cases h : Nat.beq x y
    · change inL x l = true ↔ _
      have : x ≠ y := Nat.ne_of_beq_eq_false h
      simp [this]
    · change true = true ↔ _
      have : x = y := Nat.eq_of_beq_eq_true h
      simp [this]

theorem nodupK_sound : ∀ l : List ℕ, nodupK l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    change CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (inL x l)) (nodupK l) = true at h
    rw [andB_eq3, Bool.and_eq_true, notB_eq3, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodupK_sound l h.2⟩
    rw [← inL_iff] at hm
    rw [hm] at h
    exact absurd h.1 (by decide)

theorem orbsK_length (YT : List ℕ) : ∀ R : List ℕ, (orbsK YT R).length = 13 * R.length
  | [] => rfl
  | r :: R => by
    have e : orbsK YT (r :: R) = orbK YT r ++ orbsK YT R := List.flatMap_cons
    rw [e, List.length_append, orbsK_length YT R, List.length_cons]
    simp [orbK]
    ring

theorem mem_orbsK {YT R : List ℕ} {v : ℕ} (h : v ∈ orbsK YT R) :
    ∃ r ∈ R, ∃ t < 13, v = vmF 24 (getL 0 YT t) r := by
  unfold orbsK at h
  obtain ⟨r, hr, hv⟩ := List.mem_flatMap.1 h
  unfold orbK at hv
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hv
  exact ⟨r, hr, t, List.mem_range.1 ht, rfl⟩

theorem selK_lt {f : ℕ → ℕ} (hf : ∀ k, f k < 2 ^ 24) (a : ℕ) : ∀ n, selK f a n < 2 ^ 24
  | 0 => Nat.two_pow_pos 24
  | n + 1 => by
    change Bool.rec (motive := fun _ => Nat) (selK f a n) (Nat.xor (f n) (selK f a n))
      (CFSG.KLie.CT.bit a n) < 2 ^ 24
    cases CFSG.KLie.CT.bit a n
    · exact selK_lt hf a n
    · exact Nat.xor_lt_two_pow (hf n) (selK_lt hf a n)

theorem selK_map {f f' : ℕ → ℕ} {a : ℕ} (A : M24) : ∀ n,
    (∀ k < n, toVecD 24 (f' k) = A *ᵥ toVecD 24 (f k)) →
    toVecD 24 (selK f' a n) = A *ᵥ toVecD 24 (selK f a n)
  | 0, _ => by
    change toVecD 24 0 = A *ᵥ toVecD 24 0
    rw [toVecD_zero, Matrix.mulVec_zero]
  | n + 1, h => by
    change toVecD 24 (Bool.rec (motive := fun _ => Nat) (selK f' a n)
        (Nat.xor (f' n) (selK f' a n)) (CFSG.KLie.CT.bit a n)) =
      A *ᵥ toVecD 24 (Bool.rec (motive := fun _ => Nat) (selK f a n)
        (Nat.xor (f n) (selK f a n)) (CFSG.KLie.CT.bit a n))
    have ih := selK_map (a := a) A n (fun k hk => h k (by omega))
    cases CFSG.KLie.CT.bit a n
    · exact ih
    · change toVecD 24 (f' n ^^^ selK f' a n) = A *ᵥ toVecD 24 (f n ^^^ selK f a n)
      rw [toVecD_xor, toVecD_xor, Matrix.mulVec_add, h n (by omega), ih]

theorem pvK_eq (YT : List ℕ) (p v : ℕ) :
    pvK YT p v = selK (fun t => vmF 24 (getL 0 YT t) v) p 12 := rfl

theorem base_eq : [Native.aR, Native.bR] =
    (List.range 2).map fun i => U (getL 0 CFSG.KD.Co1T13K.M i) := by
  have h := ch13504base
  simp only [Bool.and_eq_true] at h
  rw [aR_u, bR_u, ← Nat.eq_of_beq_eq_true h.1, ← Nat.eq_of_beq_eq_true h.2]
  rfl

theorem dag_eq : Native.dag [Native.aR, Native.bR]
    (Solomon.Co1T13.dagWords13.map Native.decWord) =
    ((List.range 4).map fun i => U (getL 0 CFSG.KD.Co1T13K.M i),
      (List.range 4).map fun i => U (getL 0 CFSG.KD.Co1T13K.MI i), true) :=
  dagWK_sound base_eq ch13504dag

theorem kyt : (∀ t < 13, getL 0 CFSG.KD.Co1T13K.YT t =
      trK 24 (powWK (getL 0 CFSG.KD.Co1T13K.M 3) t)) ∧
    powWK (getL 0 CFSG.KD.Co1T13K.M 3) 13 = idM := by
  have h := ch13504yt
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  refine ⟨fun t ht => ?_, h.1.2⟩
  have := MatL.allN_iff.1 h.1.1.2 t ht
  exact Nat.eq_of_beq_eq_true this

section Rep


theorem rep_y : MRep (U (getL 0 CFSG.KD.Co1T13K.M 3)) Certificates.y13Co1 := by
  have hb : List.Forall₂ MRep [Native.aR, Native.bR] [A₁, A₂] :=
    List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂ List.Forall₂.nil)
  have hflag : (Native.dag [Native.aR, Native.bR]
      (Solomon.Co1T13.dagWords13.map Native.decWord)).2.2 = true := by
    rw [dag_eq]
  have h := getD_rep (dag_rep hb _ hflag) MRep.one 3
  rw [dag_eq] at h
  have e : ((List.range 4).map fun i => U (getL 0 CFSG.KD.Co1T13K.M i)).getD 3 Native.one =
      U (getL 0 CFSG.KD.Co1T13K.M 3) := rfl
  rw [e] at h
  exact h

theorem rep_pow (t : ℕ) :
    MRep (U (powWK (getL 0 CFSG.KD.Co1T13K.M 3) t)) (Certificates.y13Co1 ^ t) := by
  rw [unpack_powWK]
  exact rep_y.pow t

theorem act_yt {t : ℕ} (ht : t < 13) (v : ℕ) :
    toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT t) v) =
      ((Certificates.y13Co1 ^ t : GL24) : M24) *ᵥ toVecD 24 v := by
  rw [kyt.1 t ht]
  exact toVecD_vmF_trK (rep_pow t) v

theorem y13_pow : Certificates.y13Co1 ^ 13 = 1 := by
  have h := rep_pow 13
  rw [kyt.2, MatL.unpack_idM] at h
  exact h.eq MRep.one

theorem y13_ne_one : Certificates.y13Co1 ≠ 1 := by
  intro h1
  have h := act_yt (t := 1) (by omega) 1
  rw [pow_one, h1, Units.val_one, Matrix.one_mulVec] at h
  have e := toVecD_injective (CFSG.KC.F2W.vmF_lt 24 _ _) (by norm_num) h
  have hm := ch13504move
  rw [Bool.not_eq_true', e] at hm
  exact absurd hm (by decide)

end Rep

theorem toVecD_two_pow (i : Fin 24) : toVecD 24 (2 ^ (i : ℕ)) = Pi.single i 1 := by
  funext j
  rw [toVecD_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e.symm)
    simp [h, h']

section Main


theorem colA_mem (g : ↥GA) {v : ℕ} (hv : v ∈ certVecs.toList) : colA g v ∈ certVecs.toList := by
  obtain ⟨-, w, hw, hwv⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.hX_GA g v hv
  have e : colA g v = w := by
    refine toVecD_injective (colA_lt _ _)
      (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.hX_GA g w hw).1 ?_
    rw [toVecD_colA, hwv, CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.μG_apply]
  rw [e]
  exact hw

theorem memK_colA (g : ↥GA) {v : ℕ} (hv : memK XB v = true) : memK XB (colA g v) = true :=
  memK_of_mem (colA_mem g (mem_of_memK hv))

theorem comm_t {a y : GL24} (hay : a * y = y * a) (t : ℕ) :
    (a : M24) * ((y ^ t : GL24) : M24) = ((y ^ t : GL24) : M24) * (a : M24) := by
  have h : ∀ t : ℕ, a * y ^ t = y ^ t * a := by
    intro t
    induction t with
    | zero => rw [pow_zero, one_mul, mul_one]
    | succ t ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hay, mul_assoc]
  have e := congrArg (fun z : GL24 => (z : M24)) (h t)
  simpa only [Units.val_mul] using e

variable {g : ↥GA} {y : GL24} (hgy : (g : GL24) * y = y * g)
  (hact : ∀ t < 13, ∀ v, toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT t) v) =
    ((y ^ t : GL24) : M24) *ᵥ toVecD 24 v)

include hgy hact in
theorem vm_colA {t : ℕ} (ht : t < 13) (v : ℕ) :
    toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT t) (colA g v)) =
      ((g : GL24) : M24) *ᵥ toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT t) v) := by
  rw [hact t ht, toVecD_colA, hact t ht, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    comm_t hgy t]

include hgy hact in
theorem pvK_colA (p v : ℕ) :
    pvK CFSG.KD.Co1T13K.YT p (colA g v) = colA g (pvK CFSG.KD.Co1T13K.YT p v) := by
  rw [pvK_eq, pvK_eq]
  refine toVecD_injective (selK_lt (fun _ => CFSG.KC.F2W.vmF_lt 24 _ _) _ _) (colA_lt _ _) ?_
  rw [toVecD_colA]
  exact selK_map (a := p) _ 12 fun k hk => vm_colA hgy hact (by omega) v

include hgy hact in
theorem inSK_colA {p q v : ℕ} (h : inSK XB CFSG.KD.Co1T13K.YT p q v = true) :
    inSK XB CFSG.KD.Co1T13K.YT p q (colA g v) = true := by
  unfold inSK at h ⊢
  rw [andB_eq3, Bool.and_eq_true] at h ⊢
  rw [pvK_colA hgy hact, pvK_colA hgy hact]
  exact ⟨memK_colA g h.1, memK_colA g h.2⟩

theorem exists_fixed {S : Finset ℕ} (f : ℕ → ℕ) (hf : ∀ v ∈ S, f v ∈ S) (hinj : Set.InjOn f S)
    (h5 : ∀ v ∈ S, f^[5] v = v) (hcard : S.card % 5 ≠ 0) : ∃ v ∈ S, f v = v := by
  classical
  by_contra hno'
  have hno : ∀ v ∈ S, f v ≠ v := fun v hv h => hno' ⟨v, hv, h⟩
  let φ : S → S := fun x => ⟨f x, hf x x.2⟩
  have φinj : Function.Injective φ := fun x y h =>
    Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h))
  let σ : Equiv.Perm S := Equiv.ofBijective φ (Finite.injective_iff_bijective.1 φinj)
  have hit : ∀ n (x : S), ((σ ^ n) x).val = f^[n] x.val := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply', ← ih]
      rfl
  have hσ : σ ^ 5 ^ 1 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_one, hit]
    exact h5 x x.2
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := σ) hσ
  have hc0 : σ.supportᶜ = ∅ := by
    rw [Finset.compl_eq_empty_iff]
    ext x
    simp only [Finset.mem_univ, iff_true, Equiv.Perm.mem_support]
    intro hx
    exact hno x.1 x.2 (congrArg Subtype.val hx)
  rw [hc0, Finset.card_empty, Fintype.card_coe] at h
  unfold Nat.ModEq at h
  omega

theorem set_eq {p q : ℕ} {R C : List ℕ} (hR : R.length = 12)
    (hset : setOK XB CFSG.KD.Co1T13K.YT p q R = true)
    (hcnt : ∀ n < 9, cntTabK (inSK XB CFSG.KD.Co1T13K.YT p q) CV.F (13 * n) 13 = getL 0 C n)
    (hC : ((List.range 9).map fun n => getL 0 C n).sum = 156) :
    (∀ v ∈ orbsK CFSG.KD.Co1T13K.YT R,
      v ∈ certVecs.toList ∧ inSK XB CFSG.KD.Co1T13K.YT p q v = true) ∧
    (orbsK CFSG.KD.Co1T13K.YT R).toFinset.card = 156 ∧
    ∀ v ∈ certVecs.toList, inSK XB CFSG.KD.Co1T13K.YT p q v = true →
      v ∈ orbsK CFSG.KD.Co1T13K.YT R := by
  classical
  unfold setOK at hset
  rw [andB_eq3, Bool.and_eq_true, List.all_eq_true] at hset
  have hin : ∀ v ∈ orbsK CFSG.KD.Co1T13K.YT R,
      v ∈ certVecs.toList ∧ inSK XB CFSG.KD.Co1T13K.YT p q v = true := by
    intro v hv
    have := hset.1 v hv
    rw [andB_eq3, Bool.and_eq_true] at this
    exact ⟨mem_of_memK this.1, this.2⟩
  have hnd := nodupK_sound _ hset.2
  have hcard : (orbsK CFSG.KD.Co1T13K.YT R).toFinset.card = 156 := by
    rw [List.toFinset_card_of_nodup hnd, orbsK_length, hR]
  refine ⟨hin, hcard, ?_⟩
  set F := certVecs.toList.filter (inSK XB CFSG.KD.Co1T13K.YT p q) with hF
  have hlen : F.length = 156 := by
    rw [hF, filter_length]
    have h117 : (117 : ℕ) = 13 * 9 := rfl
    rw [h117, cntTab_blocks, List.map_congr_left fun n hn => hcnt n (List.mem_range.1 hn), hC]
  have hsub : (orbsK CFSG.KD.Co1T13K.YT R).toFinset ⊆ F.toFinset := by
    intro v hv
    rw [List.mem_toFinset] at hv ⊢
    exact List.mem_filter.2 ⟨(hin v hv).1, (hin v hv).2⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [hcard, ← hlen]
    exact List.toFinset_card_le F)
  intro v hv hp
  have : v ∈ F.toFinset := List.mem_toFinset.2 (List.mem_filter.2 ⟨hv, hp⟩)
  rw [← heq, List.mem_toFinset] at this
  exact this

include hgy hact in
theorem fixes_rep {p q : ℕ} {R C : List ℕ} (hR : R.length = 12)
    (hset : setOK XB CFSG.KD.Co1T13K.YT p q R = true)
    (hcnt : ∀ n < 9, cntTabK (inSK XB CFSG.KD.Co1T13K.YT p q) CV.F (13 * n) 13 = getL 0 C n)
    (hC : ((List.range 9).map fun n => getL 0 C n).sum = 156) (h5 : g ^ 5 = 1) :
    ∃ i < 12, ∀ k < 13, ((g : GL24) : M24) *ᵥ
      toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) (getL 0 R i)) =
      toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) (getL 0 R i)) := by
  classical
  obtain ⟨hin, hcard, hall⟩ := set_eq hR hset hcnt hC
  set S := (orbsK CFSG.KD.Co1T13K.YT R).toFinset with hS
  have hlt : ∀ v ∈ S, v < 2 ^ 24 := fun v hv =>
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.hX_GA g v
      (hin v (List.mem_toFinset.1 hv)).1).1
  have hmap : ∀ v ∈ S, colA g v ∈ S := by
    intro v hv
    have hv' := hin v (List.mem_toFinset.1 hv)
    exact List.mem_toFinset.2 (hall _ (colA_mem g hv'.1) (inSK_colA hgy hact hv'.2))
  have hinj : Set.InjOn (colA g) S := by
    intro v hv w hw h
    refine toVecD_injective (hlt v hv) (hlt w hw) (mulVec_inj (g : GL24) ?_)
    have e := congrArg (toVecD 24) h
    rwa [toVecD_colA, toVecD_colA] at e
  have hiter : ∀ n v, toVecD 24 ((colA g)^[n] v) = (((g ^ n : ↥GA) : GL24) : M24) *ᵥ toVecD 24 v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', toVecD_colA, ih, pow_succ', Subgroup.coe_mul,
        Units.val_mul, Matrix.mulVec_mulVec]
  have h5' : ∀ v ∈ S, (colA g)^[5] v = v := by
    intro v hv
    refine toVecD_injective ?_ (hlt v hv) ?_
    · rw [Function.iterate_succ_apply']
      exact colA_lt _ _
    · rw [hiter, h5]
      simp
  obtain ⟨a, ha, hfix⟩ := exists_fixed (colA g) hmap hinj h5' (by rw [hcard]; decide)
  obtain ⟨r, hr, t, ht, rfl⟩ := mem_orbsK (List.mem_toFinset.1 ha)
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  refine ⟨i, by omega, ?_⟩
  rw [getL_get R i hi]
  have hfr : ((g : GL24) : M24) *ᵥ toVecD 24 R[i] = toVecD 24 R[i] := by
    have e := congrArg (toVecD 24) hfix
    rw [toVecD_colA, hact t ht, Matrix.mulVec_mulVec, comm_t hgy t, ← Matrix.mulVec_mulVec] at e
    exact mulVec_inj _ e
  intro k hk
  rw [hact k hk, Matrix.mulVec_mulVec, comm_t hgy k, ← Matrix.mulVec_mulVec, hfr]

end Main

theorem cnt0 : ∀ n < 9, cntTabK (inSK XB CFSG.KD.Co1T13K.YT 139 131) CV.F (13 * n) 13 =
    getL 0 C0 n := by
  intro n hn
  have h : ch13504a n = true := by
    interval_cases n
    exacts [ch13504a0, ch13504a1, ch13504a2, ch13504a3, ch13504a4, ch13504a5, ch13504a6,
      ch13504a7, ch13504a8]
  exact Nat.eq_of_beq_eq_true h

theorem cnt1 : ∀ n < 9, cntTabK (inSK XB CFSG.KD.Co1T13K.YT 157 455) CV.F (13 * n) 13 =
    getL 0 C1 n := by
  intro n hn
  have h : ch13504b n = true := by
    interval_cases n
    exacts [ch13504b0, ch13504b1, ch13504b2, ch13504b3, ch13504b4, ch13504b5, ch13504b6,
      ch13504b7, ch13504b8]
  exact Nat.eq_of_beq_eq_true h

theorem wK_fixed {A : M24} {r s : ℕ}
    (hr : ∀ k < 13, A *ᵥ toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) r) =
      toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) r))
    (hs : ∀ k < 13, A *ᵥ toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) s) =
      toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) s)) (k : ℕ) (hk : k < 24) :
    toVecD 24 (CFSG.KC.Co1T13K.wK CFSG.KD.Co1T13K.YT r s k) =
      A *ᵥ toVecD 24 (CFSG.KC.Co1T13K.wK CFSG.KD.Co1T13K.YT r s k) := by
  unfold CFSG.KC.Co1T13K.wK
  cases h : Nat.blt k 12
  · change toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT (Nat.sub k 12)) s) = _
    exact (hs _ (by change k - 12 < 13; omega)).symm
  · change toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) r) = _
    have : k < 12 := Eq.mp Nat.blt_eq h
    exact (hr k (by omega)).symm

theorem eq_one_of_fixed {A : M24} {i j : ℕ} (hi : i < 12) (hj : j < 12)
    (hr : ∀ k < 13, A *ᵥ toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k)
      (getL 0 CFSG.KD.Co1T13K.R0 i)) =
      toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) (getL 0 CFSG.KD.Co1T13K.R0 i)))
    (hs : ∀ k < 13, A *ᵥ toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k)
      (getL 0 CFSG.KD.Co1T13K.R1 j)) =
      toVecD 24 (vmF 24 (getL 0 CFSG.KD.Co1T13K.YT k) (getL 0 CFSG.KD.Co1T13K.R1 j))) :
    A = 1 := by
  have h := MatL.allN_iff.1 (MatL.allN_iff.1 ch13504span i hi) j hj
  refine Matrix.ext_of_mulVec_single fun m => ?_
  have hm := Nat.eq_of_beq_eq_true (MatL.allN_iff.1 h m m.2)
  have e := selK_map (a := rowF 24 (getL 0 CFSG.KD.Co1T13K.NT (Nat.add (Nat.mul 12 i) j)) m) A 24
    (wK_fixed hr hs)
  have h2 : Nat.shiftLeft 1 (m : ℕ) = 2 ^ (m : ℕ) := Nat.one_shiftLeft _
  rw [hm, h2, toVecD_two_pow m] at e
  rw [Matrix.one_mulVec]
  exact e.symm

open Certificates in
open CFSG.Sporadic.Co1Schreier in
theorem c13504 : y13Co1 ^ 13 = 1 ∧ y13Co1 ≠ 1 ∧
    ∀ c ∈ GA, c * y13Co1 = y13Co1 * c → c ^ 5 = 1 → c = 1 := by
  refine ⟨y13_pow, y13_ne_one, fun c hc hcy h5 => ?_⟩
  set g : ↥GA := ⟨c, hc⟩ with hg
  have hgy : (g : GL24) * Certificates.y13Co1 = Certificates.y13Co1 * g := hcy
  have hg5 : g ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h5)
  have h0 := ch13504set0
  have h1 := ch13504set1
  simp only [Bool.and_eq_true, Nat.beq_eq] at h0 h1
  have hact := fun t (ht : t < 13) v => act_yt ht v
  obtain ⟨i, hi, hr⟩ := fixes_rep hgy hact h0.1 h0.2 cnt0 (by decide +kernel) hg5
  obtain ⟨j, hj, hs⟩ := fixes_rep hgy hact h1.1 h1.2 cnt1 (by decide +kernel) hg5
  have hA := eq_one_of_fixed hi hj hr hs
  exact Units.ext hA

end CertificateChecks.KernelCo1T13K

end
