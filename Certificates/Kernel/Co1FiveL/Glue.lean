module

public import Certificates.Kernel.Co1SevenK.Glue
public import Certificates.Kernel.Co1B.C17591
public import CFSG.Certificates.Kernel.Co1LeafQSound
public import CFSG.Certificates.Kernel.Co1ClosPSound
public import CFSG.Certificates.Kernel.Co1FiveKSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1Three
public import Certificates.Data.Kernel.Co1FiveL
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.B.TwoA.Par3.Main
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2BData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1EndData
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Basic
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1B CFSG.KC.Co1F2
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.KC.Co1ClosP CFSG.KC.Co1LeafP CFSG.KC.Co1FiveL CFSG.KC.Co1BBound
open Matrix
open CertificateChecks.KernelCo1SevenK (valid_mul eq_one_of_rep hgg_pk comm_of_K
  validRows_U)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F (μG μG_apply μG_injective Cen mem_Cen)
open CertificateChecks.KernelCo1B.Bound17591 (XB memK_of_mem mem_of_memK)

local notation "U" => unpack 24 24
local notation "M24" => Matrix (Fin 24) (Fin 24) (ZMod 2)

theorem gLAPPrimeCoreOf_eq_bot_of_closureM {p : ℕ} {S : Type*} [Group S] [Finite S]
    (hp : p.Prime) {C : Subgroup S} (m : ℕ)
    (h : ∀ w ∈ C, (orderOf w).Prime → orderOf w ≠ p →
      ∃ c ∈ C, ∃ r ∈ C, w * c = c * r ∧ ∃ a ∈ C, ∃ b ∈ C,
        p ∣ orderOf (r * (a * r * a⁻¹) * (b * r * b⁻¹) ^ m)) :
    GLAPPrimeCoreOf p C = ⊥ := by
  by_contra hL
  set R := GLAPPrimeCoreOf p C with hRdef
  have hRC : R ≤ C := GLAPPrimeCoreOf_le C
  have hcop : Nat.Coprime p (Nat.card R) := coprime_card_GLAPPrimeCoreOf hp C
  have hRne : Nat.card R ≠ 1 := fun h1 => hL (Subgroup.card_eq_one.1 h1)
  obtain ⟨q, hq, hqR⟩ := Nat.exists_prime_and_dvd hRne
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) q hqR
  set w : S := (x : S) with hw
  have hwo : orderOf w = q := by rw [hw, Subgroup.orderOf_coe, hx]
  have hwR : w ∈ R := x.2
  have hqp : q ≠ p := by
    rintro rfl
    exact (hp.coprime_iff_not_dvd.1 hcop) hqR
  obtain ⟨c, hc, r, hrC, hwc, a, ha, b, hb, hdvd⟩ :=
    h w (hRC hwR) (hwo ▸ hq) (hwo ▸ hqp)
  have hrR : r ∈ R := by
    have h1 : c⁻¹ * w * c⁻¹⁻¹ ∈ R := GLAPPrimeCoreOf_conj_mem c⁻¹ (C.inv_mem hc) w hwR
    have h2 : c⁻¹ * w * c⁻¹⁻¹ = r := by
      rw [inv_inv, mul_assoc, hwc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [← h2]
    exact h1
  have h1 : a * r * a⁻¹ ∈ R := GLAPPrimeCoreOf_conj_mem a ha r hrR
  have h2 : b * r * b⁻¹ ∈ R := GLAPPrimeCoreOf_conj_mem b hb r hrR
  have hy : r * (a * r * a⁻¹) * (b * r * b⁻¹) ^ m ∈ R :=
    R.mul_mem (R.mul_mem hrR h1) (R.pow_mem h2 m)
  have h3 : orderOf (⟨_, hy⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h3
  exact (hp.coprime_iff_not_dvd.1 hcop) (hdvd.trans h3)

@[expose] noncomputable def encV (w : Vec24) : ℕ :=
  ofBits 24 fun j => if h : j < 24 then decide (w ⟨j, h⟩ = 1) else false

theorem encV_lt (w : Vec24) : encV w < 2 ^ 24 := ofBits_lt 24 _

theorem toVecD_encV (w : Vec24) : toVecD 24 (encV w) = w := by
  funext j
  rw [encV, toVecD_ofBits]
  simp only [j.isLt, dite_true]
  have hz : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hz (w j) with h | h <;> simp [h]

@[expose] noncomputable def colA (c : ↥GA) (x : ℕ) : ℕ :=
  encV ((((c : GL24) : M24)) *ᵥ toVecD 24 x)

theorem toVecD_colA (c : ↥GA) (x : ℕ) :
    toVecD 24 (colA c x) = ((c : GL24) : M24) *ᵥ toVecD 24 x := toVecD_encV _

theorem colA_lt (c : ↥GA) (x : ℕ) : colA c x < 2 ^ 24 := encV_lt _

theorem toVecD_vmF_trK {M : ℕ} {g : GL24} (h : MRep (U M) g) (v : ℕ) :
    toVecD 24 (CFSG.KC.M1F2.vmF 24 (trK 24 M) v) = (g : M24) *ᵥ toVecD 24 v := by
  rw [h.mulVec v, act, ← unpackR_eq_unpack M,
    CFSG.KC.F2W.transposeRows_unpackR, CFSG.KC.F2W.vecMulN_unpackR]

theorem rep_betaK {AT : List ℕ} {a b : ℕ} {g1 g2 : GL24}
    (h1 : MRep (U (CFSG.KC.Co1F2.getL 0 AT a)) g1) (h2 : MRep (U (CFSG.KC.Co1F2.getL 0 AT b)) g2)
    (s : ℕ) : MRep (U (betaK AT a b s)) (g1 ^ (s / 5) * g2 ^ (s % 5)) := by
  have e := (h1.pow (s / 5)).mul (h2.pow (s % 5))
  rwa [CFSG.KC.Co1FiveK.pow_unpack, CFSG.KC.Co1FiveK.pow_unpack, mul_unpackW] at e

section Equi


theorem memK_colA {c : ↥GA} {x : ℕ} (hx : memK XB x = true) : memK XB (colA c x) = true := by
  obtain ⟨y, hy, hxy⟩ := Co1T.xL_maps c x (mem_of_memK hx)
  have e : colA c x = y := by
    rw [colA, hxy]
    exact toVecD_injective (encV_lt _) (Co1T.xL_lt y hy) (toVecD_encV _)
  rw [e]
  exact memK_of_mem hy

theorem equi_colA {AT BT : List ℕ} {a b : ℕ} {g1 g2 : ↥GA} (hB : btK AT a b BT = true)
    (h1 : MRep (U (CFSG.KC.Co1F2.getL 0 AT a)) (g1 : GL24))
    (h2 : MRep (U (CFSG.KC.Co1F2.getL 0 AT b)) (g2 : GL24)) {c : ↥GA} (hc : c ∈ Cen g1 g2) :
    Equi XB BT (colA c) := by
  obtain ⟨hc1, hc2⟩ := mem_Cen.1 hc
  unfold btK at hB
  obtain ⟨hlen, hall⟩ := andB_true hB
  rw [lenL_eq] at hlen
  have hlen' : BT.length = 25 := Nat.eq_of_beq_eq_true hlen
  refine ⟨fun x _ => colA_lt c x, fun x y _ _ => ?_, fun s hs x _ => ?_, fun x hx => ?_⟩
  · apply toVecD_injective (colA_lt _ _) (Nat.xor_lt_two_pow (colA_lt _ _) (colA_lt _ _))
    rw [toVecD_xor, toVecD_colA, toVecD_colA, toVecD_colA, toVecD_xor, Matrix.mulVec_add]
  · rw [hlen'] at hs
    have hs' : BT.getD s 0 = trK 24 (betaK AT a b s) := by
      have := Nat.eq_of_beq_eq_true (CFSG.KC.Co1BSpin.allN_true' hall s hs)
      rwa [getL_eq, ← List.getD_eq_getElem?_getD] at this
    rw [hs']
    have hβ := rep_betaK h1 h2 s
    apply toVecD_injective (colA_lt _ _) (CFSG.KC.F2W.vmF_lt 24 _ _)
    rw [toVecD_colA, toVecD_vmF_trK hβ, toVecD_vmF_trK hβ, toVecD_colA, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    have e1 : (c : GL24) * g1 = g1 * c := by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hc1]
    have e2 : (c : GL24) * g2 = g2 * c := by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hc2]
    have e : (c : GL24) * ((g1 : GL24) ^ (s / 5) * (g2 : GL24) ^ (s % 5)) =
        ((g1 : GL24) ^ (s / 5) * (g2 : GL24) ^ (s % 5)) * c :=
      Co1F.commGL_mul (Co1F.commGL_pow e1 _) (Co1F.commGL_pow e2 _)
    rw [← Units.val_mul, ← Units.val_mul, e]
  · apply Bool.eq_iff_iff.2
    refine ⟨fun h => ?_, memK_colA⟩
    obtain ⟨y, hy, hxy⟩ := Co1T.xL_maps c⁻¹ _ (mem_of_memK h)
    rw [toVecD_colA, Matrix.mulVec_mulVec, Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec] at hxy
    rw [toVecD_injective hx (Co1T.xL_lt y hy) hxy]
    exact memK_of_mem hy

theorem card_le_of_leaf {AT BT : List ℕ} {a b : ℕ} {g1 g2 : ↥GA} {Es : List (List ℕ)}
    {Ms Us : List ℕ} {Ts IMS CLs : List (List (List ℕ))} {SL : List ℕ} {UIT N : ℕ}
    (hL : CFSG.KC.Co1LeafQ.leafQK XB BT Es Ms Us Ts IMS CLs SL UIT N = true)
    (hB : btK AT a b BT = true)
    (h1 : MRep (U (CFSG.KC.Co1F2.getL 0 AT a)) (g1 : GL24))
    (h2 : MRep (U (CFSG.KC.Co1F2.getL 0 AT b)) (g2 : GL24)) :
    Nat.card (Cen g1 g2) ≤ N := by
  classical
  have : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  have : Fintype ↥(Cen g1 g2) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  refine CFSG.KC.Co1LeafQ.card_le_of_leafQK hL (fun c : ↥(Cen g1 g2) => colA c)
    (fun c => equi_colA hB h1 h2 c.2) fun c c' h => ?_
  have hM : (((c : ↥GA) : GL24) : M24) = (((c' : ↥GA) : GL24) : M24) := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    have e := congrArg (toVecD 24) (h (encV (Pi.single i 1)) (encV_lt _))
    rwa [toVecD_colA, toVecD_colA, toVecD_encV] at e
  exact Subtype.ext (Subtype.ext (Units.ext hM))

end Equi

section Tree


theorem cen_tree2 {g1 g2 : ↥GA} {GM : Nat → Nat} {ng cap N : Nat} {P PAR LAB W S : Nat → Nat}
    (hT : gtPinK GM ng cap N P PAR LAB W S = true) {gg : ℕ → ↥GA}
    (hrep : ∀ l < ng, MRep (U (GM l)) (gg l : GL24))
    (hc1 : ∀ l < ng, gg l * g1 = g1 * gg l) (hc2 : ∀ l < ng, gg l * g2 = g2 * gg l)
    (hle : Nat.card (Cen g1 g2) ≤ N) :
    Nat.card (Cen g1 g2) = N ∧ ∃ f : ℕ → ↥GA, (∀ i < N, MRep (U (P i)) (f i : GL24) ∧
      f i ∈ Cen g1 g2) ∧ ∀ c ∈ Cen g1 g2, ∃ i < N, c = f i := by
  have : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  obtain ⟨-, hok⟩ := gtBFS_of_K hT
  have hsz : (bfsTree N P PAR LAB).pts.size = N := by simp [bfsTree]
  obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq μG μG_injective hok gg (hgg_pk hrep)
  have hcard := prodTree_card μG μG_injective hok gg (hgg_pk hrep)
  have hsub : Subgroup.closure (gg '' {l | l < (gensArr ng GM).size}) ≤ Cen g1 g2 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < ng := by simpa [gensArr] using hl
    exact mem_Cen.2 ⟨hc1 l hl', hc2 l hl'⟩
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

theorem rep_foldl_pow {X : Rows} {w : GL24} (h : MRep X w) :
    ∀ es : List ℕ, MRep (es.foldl pow X) (w ^ es.prod)
  | [] => by simpa using h
  | e :: es => by
    rw [List.foldl_cons, List.prod_cons, pow_mul]
    exact rep_foldl_pow (h.pow e) es

theorem tgtPK_of_rep {x : Nat} {w : ↥GA} (hw : MRep (U x) (w : GL24)) (h1 : w ≠ 1)
    {es : List ℕ} (he : w ^ es.prod = 1) : tgtPK x es = true := by
  refine tgtPK_of ?_ ?_
  · intro h
    rw [h] at hw
    exact h1 (Subtype.ext (by simpa using hw.eq MRep.one))
  · have hv : CFSG.Sporadic.Co1.InvNative.validRows (es.foldl pow (U x)) = true := by
      rw [← unpack_powLK]
      exact validRows_U _
    refine eq_one_of_rep hv (rep_foldl_pow hw es) ?_
    rw [← Subgroup.coe_pow, he, Subgroup.coe_one]

theorem bot_tree5 {g1 g2 : ↥GA} {N m : ℕ} {es : List ℕ}
    {P R C W : Nat → Nat} {f : ℕ → ↥GA}
    (hf : ∀ i < N, MRep (U (P i)) (f i : GL24) ∧ f i ∈ Cen g1 g2)
    (hall : ∀ c ∈ Cen g1 g2, ∃ i < N, c = f i)
    (hcard : Nat.card (Cen g1 g2) = 5 ^ 3 * es.prod) (hcl : closPK P N es 5 m R C W = true) :
    GLAPPrimeCoreOf 5 (Cen g1 g2) = ⊥ := by
  have : Finite ↥GA := CFSG.Sporadic.Co1Schreier.finite_GA
  refine gLAPPrimeCoreOf_eq_bot_of_closureM Nat.prime_five m ?_
  intro w hw hwp hw5
  have hqN : orderOf w ∣ 5 ^ 3 * es.prod := by
    rw [← hcard]
    have := orderOf_dvd_natCard (⟨w, hw⟩ : ↥(Cen g1 g2))
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (orderOf w) (5 ^ 3) :=
    Nat.Coprime.pow_right 3 ((Nat.coprime_primes hwp Nat.prime_five).2 hw5)
  have hpow : w ^ es.prod = 1 := orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_left hqN)
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hwp
    exact Nat.not_prime_one hwp
  obtain ⟨k, hk, rfl⟩ := hall w hw
  have hrk := (hf k hk).1
  obtain ⟨r, c, hr, hc, hm, hwit⟩ := closPK_sound hcl hk (tgtPK_of_rep hrk hw1 hpow)
  have hrr := (hf r hr).1
  have hrc := (hf c hc).1
  refine ⟨f c, (hf c hc).2, f r, (hf r hr).2, ?_, ?_⟩
  · have r1 := hrk.mul hrc
    have r2 := hrc.mul hrr
    rw [hm] at r1
    exact Subtype.ext (r1.eq r2)
  · obtain ⟨a, ai, b, bi, ha, hai, hb, hbi, hia, hib, hy1, hy5⟩ := witPK_sound hwit
    have hra := (hf a ha).1
    have hrb := (hf b hb).1
    have hrai := hra.inv hia
    have hrbi := hrb.inv hib
    refine ⟨f a, (hf a ha).2, f b, (hf b hb).2, ?_⟩
    have hY : MRep (witYP (U (P r)) (U (P a)) (U (P ai)) (U (P b)) (U (P bi)) m)
        (((f r * (f a * f r * (f a)⁻¹) * (f b * f r * (f b)⁻¹) ^ m : ↥GA)) : GL24) :=
      (hrr.mul ((hra.mul hrr).mul hrai)).mul (((hrb.mul hrr).mul hrbi).pow m)
    have hv : CFSG.Sporadic.Co1.InvNative.validRows
        (witYP (U (P r)) (U (P a)) (U (P ai)) (U (P b)) (U (P bi)) m) = true := by
      simp only [witYP, mul_unpackW, ← unpack_powWK]
      exact validRows_U _
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hord : orderOf (f r * (f a * f r * (f a)⁻¹) * (f b * f r * (f b)⁻¹) ^ m) = 5 := by
      refine orderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        have := hY.pow 5
        rw [hy5] at this
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact this.eq MRep.one
      · intro h
        rw [h] at hY
        exact hy1 (eq_one_of_rep hv hY rfl)
    rw [hord]

end CertificateChecks.KernelCo1FiveL

end
