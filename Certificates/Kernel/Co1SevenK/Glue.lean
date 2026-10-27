module

public import Certificates.Kernel.Co1SevenK.SylGlue
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenBase
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1PowBound
public import CFSG.Certificates.Kernel.Co1BSpinSound
public import CFSG.Certificates.Kernel.Co1BTrSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1BSpin
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block CFSG.Open
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S Timmesfeld.Co1Seven
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F (μG μG_apply μG_injective)

local notation "U" => unpack 24 24

theorem cs_of {TL : List Nat} {K : Nat} (hl : TL.length = 7)
    (h : ∀ s < 7, eqK (getL 0 TL s) (trK 24 (powWK K s)) = true) :
    colsOf (powList (unpackR 24 K) 7) = (TL.map (unpackR 24)).toArray := by
  have hp : ∀ e, transposeRows 24 (pow (unpackR 24 K) e) = unpackR 24 (trK 24 (powWK K e)) :=
    fun e => by rw [pow_unpack', CFSG.KC.F2W.transposeRows_unpackR]
  rw [colsOf, powList, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have hi : i < 7 := by simpa using h1
  have e := beq_of_eqK (h i hi)
  rw [CFSG.KC.Co1B.getL_eq, List.getElem?_eq_getElem (by rw [hl]; exact hi),
    Option.getD_some] at e
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, hp, e]

theorem valid_mul (A B : Nat) : CFSG.Sporadic.Co1.InvNative.validRows (mul (U A) (U B)) = true := by
  rw [mul_unpackW]
  exact validRows_U _

theorem eq_one_of_rep {X : Rows} (hX : CFSG.Sporadic.Co1.InvNative.validRows X = true) {x : GL24}
    (h : MRep X x) (h1 : x = 1) : X = one :=
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.rows_eq_of_mrep hX
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.validRows_one (h1 ▸ h) MRep.one

theorem hgg_pk {GM : Nat → Nat} {ng : Nat} {gg : ℕ → ↥GA}
    (h : ∀ l < ng, MRep (U (GM l)) (gg l : GL24)) :
    ∀ l < (gensArr ng GM).size, μG (gg l) = rowsMatrix 24 (gensArr ng GM)[l]! := by
  intro l hl
  have hl' : l < ng := by simpa [gensArr] using hl
  rw [getElem!_pos _ l hl, μG_apply]
  simp only [gensArr, Array.getElem_ofFn]
  exact (h l hl').symm

theorem finite_GA : Finite ↥GA :=
  Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)

section Tree


theorem cen_tree {g : ↥GA} {GM : Nat → Nat} {ng cap N : Nat} {P PAR LAB W S : Nat → Nat}
    (hT : gtPinK GM ng cap N P PAR LAB W S = true) {gg : ℕ → ↥GA}
    (hrep : ∀ l < ng, MRep (U (GM l)) (gg l : GL24)) (hcomm : ∀ l < ng, gg l * g = g * gg l)
    (hle : Nat.card (Subgroup.centralizer ({g} : Set ↥GA)) ≤ N) :
    Nat.card (Subgroup.centralizer ({g} : Set ↥GA)) = N ∧
    ∃ f : ℕ → ↥GA, (∀ i < N, MRep (U (P i)) (f i : GL24) ∧
      f i ∈ Subgroup.centralizer ({g} : Set ↥GA)) ∧
      ∀ c ∈ Subgroup.centralizer ({g} : Set ↥GA), ∃ i < N, c = f i := by
  have : Finite ↥GA := finite_GA
  obtain ⟨-, hok⟩ := gtBFS_of_K hT
  have hsz : (bfsTree N P PAR LAB).pts.size = N := by simp [bfsTree]
  obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq μG μG_injective hok gg (hgg_pk hrep)
  have hcard := prodTree_card μG μG_injective hok gg (hgg_pk hrep)
  have hsub : Subgroup.closure (gg '' {l | l < (gensArr ng GM).size}) ≤
      Subgroup.centralizer ({g} : Set ↥GA) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < ng := by simpa [gensArr] using hl
    exact (mem_Cen (g := g)).2 (hcomm l hl')
  have hEq := Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, hsz]; exact hle)
  have hpt : ∀ i < N, (bfsTree N P PAR LAB).pts[i]! = U (P i) := by
    intro i hi
    rw [getElem!_pos _ i (by rw [hsz]; exact hi)]
    simp [bfsTree]
  refine ⟨by rw [← hEq, hcard, hsz], f, fun i hi => ⟨?_, ?_⟩, fun c hc => ?_⟩
  · have := hf i (by rw [hsz]; exact hi)
    rw [hpt i hi, μG_apply] at this
    exact this.symm
  · rw [← hEq]
    have : f i ∈ (Subgroup.closure (gg '' {l | l < (gensArr ng GM).size}) : Set ↥GA) := by
      rw [heq]
      exact ⟨i, by rw [hsz]; exact hi, rfl⟩
    exact this
  · rw [← hEq] at hc
    have hc' : c ∈ (Subgroup.closure (gg '' {l | l < (gensArr ng GM).size}) : Set ↥GA) := hc
    rw [heq] at hc'
    obtain ⟨i, hi, rfl⟩ := hc'
    exact ⟨i, by rw [← hsz]; exact hi, rfl⟩

end Tree

section Closure

variable {g : ↥GA} {N : Nat} {P : Nat → Nat} {f : ℕ → ↥GA}

theorem tgt_of_rep {x : Nat} {w : ↥GA} (hw : MRep (U x) (w : GL24)) (hp : (orderOf w).Prime)
    (hq : orderOf w ∈ qsList) : tgtK x = true := by
  have hpow : w ^ orderOf w = 1 := pow_orderOf_eq_one w
  have hcoe : (w : GL24) ^ orderOf w = 1 := by rw [← Subgroup.coe_pow, hpow, Subgroup.coe_one]
  refine tgtK_of ?_ ?_
  · intro h
    rw [h] at hw
    have hw1 : w = 1 := Subtype.ext (by simpa using hw.eq MRep.one)
    rw [hw1, orderOf_one] at hp
    exact Nat.not_prime_one hp
  · simp only [qsList, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h <;> rw [h] at hcoe
    · left
      refine eq_one_of_rep (valid_mul _ _) (hw.mul hw) ?_
      rw [← hcoe]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    · right; left
      have hv : CFSG.Sporadic.Co1.InvNative.validRows (mul (mul (U x) (U x)) (U x)) = true := by
        rw [mul_unpackW]
        exact valid_mul _ _
      refine eq_one_of_rep hv ((hw.mul hw).mul hw) ?_
      rw [← hcoe]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    · right; right
      have hv : CFSG.Sporadic.Co1.InvNative.validRows
          (mul (mul (mul (U x) (U x)) (mul (U x) (U x))) (U x)) = true := by
        rw [mul_unpackW, mul_unpackW]
        exact valid_mul _ _
      refine eq_one_of_rep hv (((hw.mul hw).mul (hw.mul hw)).mul hw) ?_
      rw [← hcoe]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem bot_tree {R C W : Nat → Nat}
    (hf : ∀ i < N, MRep (U (P i)) (f i : GL24) ∧ f i ∈ Subgroup.centralizer ({g} : Set ↥GA))
    (hall : ∀ c ∈ Subgroup.centralizer ({g} : Set ↥GA), ∃ i < N, c = f i)
    (hcard : Nat.card (Subgroup.centralizer ({g} : Set ↥GA)) = N)
    (hq : ∀ q : ℕ, q.Prime → q ∣ N → q ≠ 7 → q ∈ qsList) (hcl : closK P N R C W = true) :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({g} : Set ↥GA)) = ⊥ := by
  have : Finite ↥GA := finite_GA
  refine gLAPPrimeCoreOf_eq_bot_of_closure (by norm_num) ?_
  intro w hw hwp hw7
  have hqN : orderOf w ∣ N := by
    rw [← hcard]
    have := orderOf_dvd_natCard (⟨w, hw⟩ : ↥(Subgroup.centralizer ({g} : Set ↥GA)))
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨k, hk, rfl⟩ := hall w hw
  have hrk := (hf k hk).1
  have ht := tgt_of_rep hrk hwp (hq _ hwp hqN hw7)
  obtain ⟨r, c, hr, hc, hm, hwit⟩ := closK_sound hcl hk ht
  have hrr := (hf r hr).1
  have hrc := (hf c hc).1
  refine ⟨f c, (hf c hc).2, f r, (hf r hr).2, ?_, ?_⟩
  · have r1 := hrk.mul hrc
    have r2 := hrc.mul hrr
    rw [hm] at r1
    exact Subtype.ext (r1.eq r2)
  · obtain ⟨a, ai, b, bi, ha, hai, hb, hbi, hia, hib, hy1, hy7⟩ := wit7K_sound hwit
    have hra := (hf a ha).1
    have hrb := (hf b hb).1
    have hrai := hra.inv hia
    have hrbi := hrb.inv hib
    refine ⟨f a, (hf a ha).2, f b, (hf b hb).2, ?_⟩
    have hY : MRep (witY (U (P r)) (U (P a)) (U (P ai)) (U (P b)) (U (P bi)))
        (((f r * (f a * f r * (f a)⁻¹) * (f b * f r * (f b)⁻¹) : ↥GA)) : GL24) :=
      (hrr.mul ((hra.mul hrr).mul hrai)).mul ((hrb.mul hrr).mul hrbi)
    have hv : CFSG.Sporadic.Co1.InvNative.validRows
        (witY (U (P r)) (U (P a)) (U (P ai)) (U (P b)) (U (P bi))) = true := by
      simp only [witY, mul_unpackW]
      exact validRows_U _
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hord : orderOf (f r * (f a * f r * (f a)⁻¹) * (f b * f r * (f b)⁻¹)) = 7 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        have := hY.pow 7
        rw [hy7] at this
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact this.eq MRep.one
      · intro h
        rw [h] at hY
        exact hy1 (eq_one_of_rep hv hY rfl)
    rw [hord]

theorem cent_tree {z : ↥GA} {Z : Nat}
    (hf : ∀ i < N, MRep (U (P i)) (f i : GL24) ∧ f i ∈ Subgroup.centralizer ({g} : Set ↥GA))
    (hall : ∀ c ∈ Subgroup.centralizer ({g} : Set ↥GA), ∃ i < N, c = f i)
    (hz : MRep (U Z) (z : GL24)) (hc : centK P N Z = true) :
    ∀ c ∈ Subgroup.centralizer ({g} : Set ↥GA), c * z = z * c → c ^ 7 = 1 := by
  intro c hcm hcz
  obtain ⟨i, hi, rfl⟩ := hall c hcm
  have hri := (hf i hi).1
  have hcomm : mul (U (P i)) (U Z) = mul (U Z) (U (P i)) := by
    have r1 := hri.mul hz
    have r2 := hz.mul hri
    have e : (f i : GL24) * z = z * f i := by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcz]
    rw [e] at r1
    exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F.rows_eq_of_mrep (valid_mul _ _)
      (valid_mul _ _) r1 r2
  have h7 := centK_sound hc i hi hcomm
  have := hri.pow 7
  rw [h7] at this
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact this.eq MRep.one

end Closure

theorem rep_dag {k : ℕ} (hk : k < D.N) :
    MRep (U (D.M k)) ((gE k : ↥GA) : GL24) := by
  have h := rep_gE (sylowOK_parts sylowOK_K).1 k
  rwa [rowAt_eq, if_pos hk] at h

theorem comm_of_K {G : Nat → Nat} {ng X : Nat} (h : commGK G ng X = true) {gg : ℕ → ↥GA}
    {x : ↥GA} (hrep : ∀ l < ng, MRep (U (G l)) (gg l : GL24)) (hx : MRep (U X) (x : GL24)) :
    ∀ l < ng, gg l * x = x * gg l := by
  intro l hl
  have r1 := (hrep l hl).mul hx
  have r2 := hx.mul (hrep l hl)
  rw [commGK_sound h l hl] at r1
  exact Subtype.ext (r1.eq r2)

end CertificateChecks.KernelCo1SevenK

end
