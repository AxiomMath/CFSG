
module

public import CFSG.Sporadic.HNOddCore.InvRow4bBase
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem mem_centralizer_of_comm {t g : JH} (h : g * t = t * g) :
    g ∈ Subgroup.centralizer {t} :=
  Subgroup.mem_centralizer_singleton_iff.2 h

theorem comm_of_mem_centralizer {t g : JH} (h : g ∈ Subgroup.centralizer {t}) :
    g * t = t * g := by
  have e := Subgroup.mem_centralizer_singleton_iff.1 h
  exact e

@[expose] def progRunG {G : Type*} [Group G] : (ℕ → G) → List (Bool × ℕ × ℕ × ℕ) → ℕ → G
  | regs, [] => regs
  | regs, (true, a, b, c) :: rest => progRunG (Function.update regs c (regs a * regs b)) rest
  | regs, (false, a, b, _) :: rest => progRunG (Function.update regs b (regs a)⁻¹) rest

theorem map_progRunG {G K : Type*} [Group G] [Group K] (φ : G →* K) :
    ∀ (regs : ℕ → G) (prog : List (Bool × ℕ × ℕ × ℕ)) (r : ℕ),
      φ (progRunG regs prog r) = progRunG (fun s => φ (regs s)) prog r
  | _, [], _ => rfl
  | regs, (true, a, b, c) :: rest, r => by
    rw [progRunG, progRunG, map_progRunG φ _ rest r]
    congr 1
    funext s
    by_cases hs : s = c
    · subst hs
      simp
    · simp [Function.update_of_ne hs]
  | regs, (false, a, b, d) :: rest, r => by
    rw [progRunG, progRunG, map_progRunG φ _ rest r]
    congr 1
    funext s
    by_cases hs : s = b
    · subst hs
      simp
    · simp [Function.update_of_ne hs]

theorem regsRep_inv_step {arr : Array (Array ℕ)} {perm : ℕ → Equiv.Perm X} (h : RegsRep arr perm)
    {a b : ℕ} (ha : a < 11) (hb : b < 11)
    (hi : pisInv hnsData.n arr[a]! (pinvCand hnsData.n arr[a]!) = true) :
    RegsRep (arr.set! b (pinvCand hnsData.n arr[a]!)) (Function.update perm b (perm a)⁻¹) := by
  obtain ⟨hs, hr⟩ := h
  refine ⟨by simp [hs], fun r hr' => ?_⟩
  by_cases hrb : r = b
  · subst hrb
    rw [Function.update_self, Array.getElem!_set!_self _ _ _ (by omega)]
    exact prep_inv_of_pisInv (hr a ha) hi
  · rw [Function.update_of_ne hrb, Array.getElem!_set!_ne _ _ _ _ (Ne.symm hrb)]
    exact hr r hr'

theorem progRun_snd_inv (n : Nat) (arr : Array (Array Nat)) (a b d : Nat)
    (rest : List (Bool × ℕ × ℕ × ℕ)) :
    (progRun n arr ((false, a, b, d) :: rest)).2 =
      (pisInv n arr[a]! (pinvCand n arr[a]!) &&
        (progRun n (arr.set! b (pinvCand n arr[a]!)) rest).2) := rfl

theorem progRun_fst_inv (n : Nat) (arr : Array (Array Nat)) (a b d : Nat)
    (rest : List (Bool × ℕ × ℕ × ℕ)) :
    (progRun n arr ((false, a, b, d) :: rest)).1 =
      (progRun n (arr.set! b (pinvCand n arr[a]!)) rest).1 := rfl

theorem regsRep_progRun : ∀ (prog : List (Bool × ℕ × ℕ × ℕ)) (arr : Array (Array ℕ))
    (perm : ℕ → Equiv.Perm X), (∀ t ∈ prog, t.2.1 < 11 ∧ t.2.2.1 < 11 ∧ t.2.2.2 < 11) →
    RegsRep arr perm → (progRun hnsData.n arr prog).2 = true →
    RegsRep (progRun hnsData.n arr prog).1 (progRunG perm prog)
  | [], _, _, _, h, _ => h
  | (true, a, b, c) :: rest, arr, perm, hp, h, hr => by
    have ht := hp (true, a, b, c) (List.mem_cons_self ..)
    exact regsRep_progRun rest _ _ (fun t ht' => hp t (List.mem_cons_of_mem _ ht'))
      (regsRep_step h ht.1 ht.2.1 ht.2.2) hr
  | (false, a, b, d) :: rest, arr, perm, hp, h, hr => by
    have ht := hp (false, a, b, d) (List.mem_cons_self ..)
    have hr' := (progRun_snd_inv hnsData.n arr a b d rest).symm.trans hr
    rw [Bool.and_eq_true] at hr'
    rw [progRun_fst_inv hnsData.n arr a b d rest]
    exact regsRep_progRun rest (arr.set! b (pinvCand hnsData.n arr[a]!))
      (Function.update perm b (perm a)⁻¹) (fun t ht' => hp t (List.mem_cons_of_mem _ ht'))
      (regsRep_inv_step h ht.1 ht.2.1 hr'.1) hr'.2

@[expose] def m2RegsJ : ℕ → JH := progRunG jRegs0 InvData.m2Prog

@[expose] def g6cJ : JH := seedWordJ InvData.m2ConjRoot * hWordJ InvData.m2ConjH

@[expose] def e6J (i : ℕ) : JH := g6cJ⁻¹ * (m2RegsJ i * g6cJ)

abbrev m2Run : Array (Array ℕ) × Bool :=
  progRun hnsData.n (initRegs hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta)) InvData.m2Prog

abbrev g6Tab : Array ℕ :=
  pcomp hnsData.n (seedWordArr hnsData.n (natTab (hnsData.orbit ()).alpha)
    (natTab (hnsData.orbit ()).beta) InvData.m2ConjRoot)
    (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) InvData.m2ConjH)

abbrev e6Tab (i : ℕ) : Array ℕ :=
  pcomp hnsData.n (pinvCand hnsData.n g6Tab) (pcomp hnsData.n m2Run.1[i]! g6Tab)

theorem m2Prog_bounds : ∀ t ∈ InvData.m2Prog, t.2.1 < 11 ∧ t.2.2.1 < 11 ∧ t.2.2.2 < 11 := by
  decide

theorem permJ_m2RegsJ (r : ℕ) : permJ (m2RegsJ r) = progRunG permRegs0 InvData.m2Prog r := by
  rw [m2RegsJ, map_progRunG]
  congr 1
  funext s
  simp only [jRegs0, permRegs0]
  split_ifs
  · exact permJ_aJ
  · exact permJ_bJ
  · exact map_one _

theorem prep_g6c :
    PRep hnsData.n g6Tab (permJ g6cJ) := by
  rw [g6cJ, map_mul]
  exact prep_pcomp (prep_seedWordArr _ (by decide)) (prep_hWord (by decide))

theorem prep_a0J :
    PRep hnsData.n (natTab (hnsData.orbit ()).alpha) (permJ aJ) := by
  rw [permJ_aJ]
  exact prep_a0

theorem x0_fix_t6 :
    jR aJ • x0 = x0 := by
  rw [jR_smul]
  exact (mem_HJ_iff_fix _).1 aJ_mem_HJ

@[expose] def c6G (j : ℕ) : JH := hWordJ InvData.c6Words[j]!

@[expose] def g6 (s : ℕ) : JH := if s < 10 then c6G s else e6J (s - 9)

theorem c6G_mem_HJ (j : ℕ) : c6G j ∈ HJ := hWordJ_mem _

theorem c6_spec :
    InvData.c6Words.size = InvData.c6Nat.size ∧ ∀ j < InvData.c6Words.size,
    plettersOK 17 InvData.c6Words[j]! = true ∧
      PRep 12 (natArr InvData.c6Nat[j]!) (natWord InvData.c6Words[j]!) :=
  natAllOK_spec nat_parts.2.2.2.2.2.2.1

theorem prep_nat6 : PRep 12 (natArr InvData.nat6) sig6 := by
  unfold PRep natArr InvData.nat6 sig6
  decide

theorem nat_t6 :
    PRep 12 (natArr InvData.nat6) (thetaJ ⟨aJ, aJ_mem_HJ⟩ : Perm (Fin 12)) := by
  rw [thetaJ_aJ]
  exact prep_nat6

theorem fix_jR_smul
    {t g : JH} (hg : g * t = t * g) {y : X} (hy : jR t • y = y) :
    jR t • (g • y) = g • y := by
  rw [← jR_smul g, ← mul_smul, ← map_mul, ← hg, map_mul, mul_smul, hy]

abbrev S6 : Subgroup JH := Subgroup.closure (Set.range fun s : Fin InvData.s6Perms.size => g6 s)

theorem orbit6_parts :
    InvData.o6Lists.size = 2 ∧ InvData.o6Lists.map Array.size = #[7700, 1100] ∧
    orbitOK InvData.f6Arr.size InvData.s6Perms InvData.o6Lists[0]! = true ∧
    orbitOK InvData.f6Arr.size InvData.s6Perms InvData.o6Lists[1]! = true := by
  have h := orbits_cert
  unfold orbitChecks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨beq_iff_eq.1 h6, beq_iff_eq.1 h7, h8, h9⟩

theorem o6_size
    {i : ℕ} (hi : i < 2) : (InvData.o6Lists[i]!).size = [7700, 1100][i]! := by
  have hs : (InvData.o6Lists.map Array.size)[i]! = (InvData.o6Lists[i]!).size := by
    rw [getElem!_pos _ i (by simp [orbit6_parts.1, hi]), Array.getElem_map,
      getElem!_pos InvData.o6Lists i (by rw [orbit6_parts.1]; exact hi)]
  rw [← hs, orbit6_parts.2.1]
  interval_cases i <;> rfl

theorem orbitCert6 {i : ℕ} (hi : i < 2) :
    orbitCertOK InvData.f6Arr.size InvData.s6Perms InvData.o6Lists[i]!
      (posArr InvData.f6Arr.size InvData.o6Lists[i]!)
      (orbitRecs InvData.s6Perms InvData.o6Lists[i]!
        (posArr InvData.f6Arr.size InvData.o6Lists[i]!)).1
      (orbitRecs InvData.s6Perms InvData.o6Lists[i]!
        (posArr InvData.f6Arr.size InvData.o6Lists[i]!)).2 = true := by
  have h : orbitOK InvData.f6Arr.size InvData.s6Perms InvData.o6Lists[i]! = true := by
    interval_cases i
    · exact orbit6_parts.2.2.1
    · exact orbit6_parts.2.2.2
  exact h

theorem thetaJ_comm_t6
    {h : JH} (hh : h ∈ HJ) (hc : h * aJ = aJ * h) :
    (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) * sig6 = sig6 * (thetaJ ⟨h, hh⟩ : Perm (Fin 12)) := by
  have e1 := thetaJ_mul h aJ hh aJ_mem_HJ
  have e2 := thetaJ_mul aJ h aJ_mem_HJ hh
  have e3 : (⟨h * aJ, mul_mem hh aJ_mem_HJ⟩ : HJ) = ⟨aJ * h, mul_mem aJ_mem_HJ hh⟩ :=
    Subtype.ext hc
  rw [← thetaJ_aJ, ← e1, ← e2, e3]

abbrev Z6 : Subgroup (Perm (Fin 12)) := Subgroup.centralizer {sig6} ⊓ alternatingGroup (Fin 12)

theorem card_CH_t6_le :
    Nat.card (Subgroup.centralizer {aJ} ⊓ HJ : Subgroup JH) ≤ 23040 := by
  rw [← card_altCentralizer_sig6]
  refine card_le_of_thetaJ (K := Subgroup.centralizer {aJ} ⊓ HJ) (Z := Z6) inf_le_right ?_
  intro g hg
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_centralizer_singleton_iff (g := sig6)).2 ?_,
    (thetaJ _).2⟩
  exact thetaJ_comm_t6 _ (comm_of_mem_centralizer (Subgroup.mem_inf.1 hg).1)

abbrev K6 : Subgroup JH := Subgroup.closure (Set.range fun s : Fin InvData.c6Nat.size => c6G s)

theorem K6_le_HJ : K6 ≤ HJ := closure_le_HJ fun s => c6G_mem_HJ s

theorem orbit_invariant_of_le
    {S C : Subgroup JH} (hSC : S ≤ C) (x : X) :
    ∀ g : S, ∀ y ∈ MulAction.orbit C x, g • y ∈ MulAction.orbit C x := by
  rintro ⟨g, hg⟩ y ⟨h, rfl⟩
  refine ⟨⟨g, hSC hg⟩ * h, ?_⟩
  show (⟨g, hSC hg⟩ * h) • x = (⟨g, hg⟩ : S) • (h • x)
  rw [mul_smul]
  rfl

end CFSG.Sporadic.HNOddCore
