
module

public import Certificates.Kernel.Co1ThreeK.GlueQ
public import Certificates.Kernel.Co1ThreeK.SplitD
public import CFSG.Certificates.Kernel.Co1Three.SplitSound
import all CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1Leaf CFSG.KLie.CT
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance Timmesfeld.Co1Leaf
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (wG eltG SplitData root Good
  mem_expVecs_iff)

theorem matK_eltWK_go : ∀ {As : List Nat} {fs : List ↥GA},
    List.Forall₂ (fun A (f : ↥GA) => matK A = ιK f) As fs → ∀ (e : List Nat) (acc : Nat)
      (g : ↥GA), matK acc = ιK g →
      matK (List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
        (fun a _ ih e acc => CFSG.KC.Loop.strictN
          (mulWK acc (powWK a (List.headD e (nat_lit 0)))) fun x => ih (List.tail e) x) As e acc) =
        ιK ((fs.zip e).foldl (fun acc fb => acc * fb.1 ^ fb.2) g)
  | _, _, List.Forall₂.nil, _, _, _, h => by simpa using h
  | _, _, List.Forall₂.cons (a := A) (b := f) hA hrest, e, acc, g, h => by
    dsimp only
    rw [strictN_loop]
    rcases e with _ | ⟨x, e⟩
    · have := matK_eltWK_go hrest [] (mulWK acc (powWK A 0)) (g * f ^ 0)
        (by rw [matK_mulWK, matK_powWK, h, map_mul, map_pow, hA])
      simpa using this
    · rw [List.zip_cons_cons, List.foldl_cons]
      exact matK_eltWK_go hrest e _ _ (by rw [matK_mulWK, matK_powWK, h, map_mul, map_pow, hA]; rfl)

theorem matK_eltWK {As : List Nat} {fs : List ↥GA}
    (h : List.Forall₂ (fun A (f : ↥GA) => matK A = ιK f) As fs) (e : List Nat) :
    matK (eltWK As e) = ιK (eltG fs e) := by
  unfold eltWK
  exact matK_eltWK_go h e oneK 1 (by rw [matK_oneK, map_one])

theorem exists_of_forall₂ {R : Nat → ↥GA → Prop} {F : List Nat} {fs : List ↥GA}
    (h : List.Forall₂ R F fs) {x : ↥GA} (hx : x ∈ fs) : ∃ A ∈ F, R A x := by
  induction h with
  | nil => simp at hx
  | cons hab _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx'
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨A, hA, h⟩ := ih hx'
      exact ⟨A, List.mem_cons_of_mem _ hA, h⟩

theorem eltG_two (g0 g1 : ↥GA) (x0 x1 : ℕ) : eltG [g0, g1] [x0, x1] = g0 ^ x0 * g1 ^ x1 := by
  simp only [eltG, List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
    one_mul]

theorem two_of_length {l : List ℕ} (h : l.length = 2) : ∃ x0 x1, l = [x0, x1] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, l⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at h <;>
    first | omega | exact ⟨_, _, rfl⟩

theorem splitData_of_planeK {F : List Nat} {X Y : Nat}
    {fsF : List ↥GA} {g0 g1 : ↥GA} (h : planeK F X Y = true) (hX : matK X = ιK g0)
    (hY : matK Y = ιK g1) (hF : List.Forall₂ (fun A (f : ↥GA) => matK A = ιK f) F fsF) :
    SplitData [unpackR 24 X, unpackR 24 Y] [g0, g1] ∧
      ∀ x ∈ fsF, ∀ y ∈ [g0, g1], x * y = y * x := by
  obtain ⟨hXY, hX3, hY3, hFc, hd⟩ := planeK_sound h
  rw [hX, hY] at hXY hd
  rw [hX] at hX3
  rw [hY] at hY3
  have hc01 : g0 * g1 = g1 * g0 := ιK_injective (by rw [map_mul, map_mul, hXY])
  have hrep : Co1T.RowsRep [unpackR 24 X, unpackR 24 Y] [g0, g1] := by
    unfold Co1T.RowsRep
    exact List.Forall₂.cons ((mRep_iff _ _).2 hX) (List.Forall₂.cons ((mRep_iff _ _).2 hY)
      List.Forall₂.nil)
  refine ⟨⟨hrep, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro R hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with hR | hR <;>
    · rw [hR, CFSG.KS.SporSch.M24.unpackR_eq_unpack]
      exact CFSG.KS.SporSch.M24.StabL.wf_unpack' _
  · intro f hf f' hf'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf hf'
    rcases hf with rfl | rfl <;> rcases hf' with rfl | rfl
    · rfl
    · exact hc01
    · exact hc01.symm
    · rfl
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ιK_injective (by rw [map_pow, hX3, map_one])
    · exact ιK_injective (by rw [map_pow, hY3, map_one])
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) (expVecs_nodupK 3 2)
    have e : eltG [g0, g1] x = eltG [g0, g1] y := by
      have h1 := Co1T.mrep_eltR hrep x
      have h2 := Co1T.mrep_eltR hrep y
      rw [hxy] at h1
      exact Subtype.ext (h1.eq h2)
    obtain ⟨hlx, hx3⟩ := mem_expVecs_iff.1 hx
    obtain ⟨hly, hy3⟩ := mem_expVecs_iff.1 hy
    obtain ⟨x0, x1, rfl⟩ := two_of_length hlx
    obtain ⟨y0, y1, rfl⟩ := two_of_length hly
    have hx0 := hx3 x0 (by simp)
    have hx1 := hx3 x1 (by simp)
    have hy0 := hy3 y0 (by simp)
    have hy1 := hy3 y1 (by simp)
    rw [eltG_two, eltG_two] at e
    have e2 := congrArg ιK e
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow] at e2
    have hu := hd (x0 + 3 * x1) (by omega) (y0 + 3 * y1) (by omega)
    have r1 : (x0 + 3 * x1) % 3 = x0 := by omega
    have r2 : (x0 + 3 * x1) / 3 = x1 := by omega
    have r3 : (y0 + 3 * y1) % 3 = y0 := by omega
    have r4 : (y0 + 3 * y1) / 3 = y1 := by omega
    rw [r1, r2, r3, r4] at hu
    have := hu e2
    simp only [List.cons.injEq, and_true]
    omega
  · intro x hx y hy
    obtain ⟨A, hA, hAx⟩ := exists_of_forall₂ hF hx
    obtain ⟨h0, h1⟩ := hFc A hA
    rw [hAx] at h0 h1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy
    · rw [hy]
      refine ιK_injective ?_
      rw [map_mul, map_mul, ← hX]
      exact h0
    · rw [hy]
      refine ιK_injective ?_
      rw [map_mul, map_mul, ← hY]
      exact h1

theorem good_of_splitData {A : List Native.Rows}
    {fsF fsA : List ↥GA} (hS : SplitData A fsA) (hcomm : ∀ x ∈ fsF, ∀ y ∈ fsA, x * y = y * x)
    (hk : 0 < fsA.length)
    (hkids : ∀ f ∈ normVecs 3 fsA.length, Good (fsF ++ (kerBasis 3 f).map (eltG fsA))) :
    Good fsF := by
  have := Co1T.finite_GA
  have hTC : hS.T ≤ Subgroup.centralizer {x | x ∈ fsF} := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have ha : hS.φ a = eltG fsA (Co1T.vecList (Multiplicative.toAdd a)) := by
      rw [← hS.φ_apply, ofAdd_toAdd]
    rw [ha]
    exact Co1T.comm_eltG (fun g hg => hcomm f hf g hg) _
  refine Co1T.gLAPPrimeCoreOf_eq_bot_of_hyperplanes Nat.prime_three hS.T_elemAbelian hTC
    (hS.T_ne_bot hk) fun B hBT hidx => ?_
  obtain ⟨fl, hfl, hB⟩ := @Co1T.exists_normVec_eq_closure ↥GA (Subgroup.toGroup GA) fsA.length
    (Co1T.fnOf fsA) hS.fn_comm hS.fn_cube hS.φ_injective B hBT hidx
  have e : Subgroup.centralizer (B : Set ↥GA) =
      Subgroup.centralizer {x | x ∈ (kerBasis 3 fl).map (eltG fsA)} := by
    rw [hB, Subgroup.centralizer_closure, Co1T.set_kerBasis_eq hfl]
  rw [e, Co1T.centralizer_append]
  exact hkids fl hfl

@[expose] noncomputable def gD (k : Nat) : ↥GA := wG (PW.getD k [])

theorem normVecs_two : normVecs 3 2 = [[0, 1], [1, 0], [1, 1], [1, 2]] := by decide

theorem kerBasis_DV {a : Nat} (ha : a < 4) :
    kerBasis 3 ((normVecs 3 2).getD a []) = [LD.DV.getD a []] := by
  interval_cases a <;> rfl

theorem planeD_eq : Co1T.Data.planeD.map wG = [gD 0, gD 1] := rfl

theorem planesD_eq {a : Nat} (ha : a < 4) :
    (Co1T.Data.planesD.getD a []).map wG = [gD (2 + 2 * a), gD (3 + 2 * a)] := by
  interval_cases a <;> rfl

section Planes

theorem matK_PD {k : Nat} (hk : k < 10) : matK (PD k) = ιK (gD k) := by
  have h := kPD
  simp only [Bool.and_eq_true] at h
  have hk' := CFSG.KS.SporSch.M24.MatL.allN_iff.1 h.2 k hk
  simp only [Bool.and_eq_true] at hk'
  rw [Nat.eq_of_beq_eq_true hk'.2, matK_wordWK hk'.1]
  rfl

theorem dSplitK : SplitData [unpackR 24 (PD 0), unpackR 24 (PD 1)] (Co1T.Data.planeD.map wG) ∧
    ∀ x ∈ [root 2], ∀ y ∈ Co1T.Data.planeD.map wG, x * y = y * x := by
  rw [planeD_eq]
  exact splitData_of_planeK kSplitD (matK_PD (by norm_num)) (matK_PD (by norm_num))
    (List.Forall₂.cons (matK_RM (by norm_num)) List.Forall₂.nil)

theorem cSplitK {a : Nat} (ha : a < 4) :
    SplitData [unpackR 24 (PD (2 + 2 * a)), unpackR 24 (PD (3 + 2 * a))]
        ((Co1T.Data.planesD.getD a []).map wG) ∧
      ∀ x ∈ [root 2] ++ (kerBasis 3 ((normVecs 3 2).getD a [])).map
          (eltG (Co1T.Data.planeD.map wG)),
        ∀ y ∈ (Co1T.Data.planesD.getD a []).map wG, x * y = y * x := by
  rw [planesD_eq ha, kerBasis_DV ha, planeD_eq]
  have h := allN_eq_true.1 kSplitC a ha
  refine splitData_of_planeK h (matK_PD (by omega)) (matK_PD (by omega))
    (List.Forall₂.cons (matK_RM (by norm_num)) (List.Forall₂.cons ?_ List.Forall₂.nil))
  exact matK_eltWK (List.Forall₂.cons (matK_PD (by norm_num))
    (List.Forall₂.cons (matK_PD (by norm_num)) List.Forall₂.nil)) _

end Planes

end CertificateChecks.KernelCo1ThreeK

end
