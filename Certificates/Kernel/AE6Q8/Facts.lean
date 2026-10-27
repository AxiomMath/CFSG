module

public import Certificates.Kernel.AE6Q8.Roots
public import Certificates.Kernel.AE6Q8.Pairs
public import CFSG.Certificates.Kernel.SporSch.RootPairSound
public import Certificates.Kernel.AE6F.Final
public import CFSG.Quasithin.Recognition.CertChain
public import Certificates.Data.AE6ModelSmall
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase
public import CFSG.Sporadic.Schreier.J1CountCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Q8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx CFSG.KS.SporSch.CAll
open CFSG.KS.SporSch.RPair
open CFSG.KS.Raw.Orb (Gen)
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native Certificates.AE6Model

@[expose] noncomputable def SA : Array (Array Nat) := ((List.range 7).map fun j => unpack 360 9 (SC.S j)).toArray

@[expose] def baseL : List (Fin 360) := [0, 2, 4, 24, 8]

@[expose] def baseA : Array Nat := (baseL.map Fin.val).toArray

theorem SA_get {j : Nat} (hj : j < 7) : SA[j]! = unpack 360 9 (SC.S j) := by
  interval_cases j <;> rfl

theorem binds : Binds 360 9 SC.S 7 5 SC.BP SA baseA := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => SA_get hj, rfl,
    fun t ht => ?_⟩
  interval_cases t <;> decide

theorem rawOK : rawChainOK 360 (SA.extract 0 4) SA baseA
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 4 7 sDeriveK) 1 = true :=
  rawChainK_sound (NS := 15) (CH := 24) binds SC.head SC.hl (by norm_num) SC.hs

theorem extract_size : (SA.extract 0 4).size = 4 := by simp [SA]

theorem extract_get {i : Nat} (hi : i < 4) : (SA.extract 0 4)[i]! = SA[i]! := by
  interval_cases i <;> rfl

theorem card_le : Nat.card (Subgroup.closure (Set.range fun j : Fin 4 => permOfArr 360 SA[j.val]!)) ≤
    (rawOrbitSizes 360 SA baseA).prod := by
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 360) (O := SA.extract 0 4)
    (S := SA) (base := baseL) (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 4 7 sDeriveK)
    (chunks := 1) (by norm_num) (by decide) (by norm_num) (by rw [extract_size]; simp [SA])
    (fun i hi => (extract_get (extract_size ▸ hi)).symm) (by rw [extract_size]; exact rawOK)
  have e : {g | ∃ k < (SA.extract 0 4).size, permOfArr 360 (SA.extract 0 4)[k]! = g} =
      Set.range fun j : Fin 4 => permOfArr 360 SA[j.val]! := by
    ext g
    rw [extract_size]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, by rw [extract_get hk]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.val, j.isLt, by rw [extract_get j.isLt]⟩
  rw [e] at h
  exact h.le

theorem chainCK : ChainCK 360 9 SC.S SC.SI SC.LR SC.TR SC.TRI 7 4 5 SC.BP SA baseA sDeriveK :=
  ⟨binds, SC.head, SC.hl, card_le⟩

theorem gen_eq_AP : ∀ l < 4, SC.S l = CertificateChecks.KernelO8.AP.S (2 * l) := by
  intro l hl
  interval_cases l <;> decide

theorem gen_eq {l : Nat} (hl : l < 4) :
    permOfArr 360 SA[l]! = (curtisPerms ()).getD (2 * l) 1 := by
  have h1 := (Orb.prep_PS binds (perms chainCK) (j := l) (by omega)).1
  have h2 := CertificateChecks.KernelAE6F.prep_curtis (l := 2 * l) (by omega)
  rw [← gen_eq_AP l hl] at h2
  exact Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))

theorem gen_eq_S : Gen 360 SA 4 = Subgroup.closure {g | g ∈ sGens ()} := by
  unfold Gen
  congr 1
  ext g
  have hs : sGens () = [(curtisPerms ()).getD 0 1, (curtisPerms ()).getD 2 1,
      (curtisPerms ()).getD 4 1, (curtisPerms ()).getD 6 1] := rfl
  rw [Set.mem_setOf_eq, hs]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    rw [gen_eq j.isLt]
    rcases j with ⟨j, hj⟩
    interval_cases j <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨⟨0, by norm_num⟩, gen_eq (l := 0) (by norm_num)⟩
    · exact ⟨⟨1, by norm_num⟩, gen_eq (l := 1) (by norm_num)⟩
    · exact ⟨⟨2, by norm_num⟩, gen_eq (l := 2) (by norm_num)⟩
    · exact ⟨⟨3, by norm_num⟩, gen_eq (l := 3) (by norm_num)⟩

theorem CS_sum : SN.CS.sum = SK.K := by decide

theorem CS_len : rcnt (SC.LR 0) ≤ SN.CS.length * 64 := by decide

theorem card_inv :
    Nat.card {g : Equiv.Perm (Fin 360) // g ∈ Gen 360 SA 4 ∧ orderOf g = 2} = SK.K := by
  rw [← CS_sum]
  exact card_ord_eq_sum chainCK (by norm_num) CS_len SN.hc

theorem K_le : SK.K ≤ SK.nbk * 64 := by decide

theorem clsB : ∀ k < SK.K, clsGK 360 9 (mask 9) (360 * 9) SC.BP 5 SK.N 4 2 SC.S SC.SI SC.LR SC.TR
    SK.E SK.CL SK.O SK.IX SK.PA SK.LB SK.DP SK.K SK.ncl k = true := by
  intro k hk
  have hs : k / 64 < SK.nbk := by have := K_le; omega
  have := allBlk_spec (SK.hb (k / 64) hs) (k % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 64 * 64) (k % 64) = k := by
    change k / 64 * 64 + k % 64 = k
    omega
  rwa [e] at this

theorem clsF : ClsFacts 360 SA baseA 4 5 SK.N 2 SK.E SK.CL SK.O SK.K SK.ncl :=
  cls_facts chainCK SK.hN SK.hd clsB

theorem cover {g : Equiv.Perm (Fin 360)} (hg : g ∈ Gen 360 SA 4) (ho : orderOf g = 2) :
    ∃ k < SK.K, el 360 SA baseA 5 (SK.E k) = g :=
  cls_cover chainCK SK.hN clsF card_inv hg ho

abbrev GC : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure (Set.range fun l : Fin 8 => (curtisPerms ()).getD l.val 1)

@[expose] noncomputable def Xg (t : Nat) : Equiv.Perm (Fin 360) :=
  permOfArr 360 (unpack 360 9 (SR.X t))

theorem xperm {t : Nat} (ht : t < SR.nx) :
    SR.X t = wordK 360 9 (mask 9) (pidn 360 9) SR.GS SR.GSI (SR.XW t) ∧
      permOK 360 9 (mask 9) (360 * 9) (SR.X t) (SR.XI t) = true := by
  have := (Orb.allN_iff.1 kXHd) t ht
  obtain ⟨a, b⟩ := (CFSG.KS.SporSch.CIdx.bAnd_iff' _ _).1 this
  exact ⟨beq_iff.1 a, b⟩

theorem prepX {t : Nat} (ht : t < SR.nx) :
    Orb.PRep 360 9 (SR.X t) (Xg t) ∧ Orb.PRep 360 9 (SR.XI t) (Xg t)⁻¹ := by
  have hr := rep_permOfArr (Orb.isInvA_unpack (xperm ht).2)
  exact ⟨Orb.prep_of_rep hr.1, Orb.prep_of_rep hr.2⟩

theorem GS_eq : ∀ l < 8, SR.GS l = CertificateChecks.KernelO8.AP.S l := by
  intro l hl
  interval_cases l <;> decide

theorem GS_perm : allN 8 (fun l => permOK 360 9 (mask 9) (360 * 9) (SR.GS l) (SR.GSI l)) =
    true := by
  decide +kernel

theorem prepGS {l : Nat} (hl : l < 8) :
    Orb.PRep 360 9 (SR.GS l) ((curtisPerms ()).getD l 1) ∧
      Orb.PRep 360 9 (SR.GSI l) ((curtisPerms ()).getD l 1)⁻¹ := by
  have hr := rep_permOfArr (Orb.isInvA_unpack ((Orb.allN_iff.1 GS_perm) l hl))
  have h1 := Orb.prep_of_rep hr.1
  have h2 := CertificateChecks.KernelAE6F.prep_curtis hl
  rw [← GS_eq l hl] at h2
  have e : permOfArr 360 (unpack 360 9 (SR.GS l)) = (curtisPerms ()).getD l 1 :=
    Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))
  refine ⟨h2, ?_⟩
  rw [← e]
  exact Orb.prep_of_rep hr.2

theorem letters : ∀ t < SR.nx, lettersK 8 (SR.XW t) = true := by decide +kernel

theorem Xg_mem {t : Nat} (ht : t < SR.nx) : Xg t ∈ GC := by
  obtain ⟨hp, -⟩ := Orb.prep_wordK (n := 360) (w := 9) (by norm_num) (by norm_num)
    (gs := fun l => (curtisPerms ()).getD l 1) (j := 8) (fun h hh => (prepGS hh).1)
    (fun h hh => (prepGS hh).2) (SR.XW t) (letters t ht)
  rw [← (xperm ht).1] at hp
  have e : Xg t = Quiver.SchreierGraph.evalWord (fun h : Fin 8 => (curtisPerms ()).getD h 1)
      (toLetters 8 (SR.XW t)) := Equiv.ext fun x => Fin.ext (((prepX ht).1 x).symm.trans (hp x))
  rw [e]
  exact Quiver.SchreierGraph.evalWord_mem_closure _ _

theorem S_le_GC : Gen 360 SA 4 ≤ GC := by
  unfold Gen
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  change permOfArr 360 SA[j.val]! ∈ GC
  rw [gen_eq j.isLt]
  exact Subgroup.subset_closure ⟨⟨2 * j.val, by omega⟩, rfl⟩

@[expose] noncomputable def zK (w : List Nat) : Nat :=
  w.foldr (fun i acc => pcomp 360 9 (mask 9) (CertificateChecks.KernelO8.AP.S i) acc) (pidn 360 9)

theorem Z_eq : SK.Z = zK zWord := by decide +kernel

theorem prep_zK : ∀ w : List Nat, (∀ i ∈ w, i < 8) →
    Orb.PRep 360 9 (zK w) (aeWord (curtisPerms ()) w)
  | [], _ => by
    have := Orb.prep_pidn (n := 360) (w := 9) (by norm_num) (by norm_num)
    simpa [zK, aeWord] using this
  | i :: w, h => by
    have h1 := CertificateChecks.KernelAE6F.prep_curtis (h i (List.mem_cons_self ..))
    have h2 := prep_zK w fun j hj => h j (List.mem_cons_of_mem _ hj)
    have := Orb.prep_pcomp (by norm_num) h1 h2
    simpa [zK, aeWord, List.map_cons, List.prod_cons] using this

theorem el_zp : el 360 SA baseA 5 (SK.E SK.zp) = z0 () := by
  obtain ⟨-, -, -, -, -, h⟩ := clsGHdK_facts SK.hd
  have hz := prep_zK zWord (by decide)
  rw [← Z_eq] at hz
  refine Equiv.ext fun x => Fin.ext ?_
  rw [← apL_elemT chainCK, h x x.isLt, hz x]
  rfl

theorem sqB : ∀ j < SK.N, sqK 360 9 (mask 9) (360 * 9) SC.BP 5 SC.LR SC.TR SR.RL SR.RC SR.RI SR.KL
    SK.ncl SR.R j = true := by
  intro j hj
  have hN : SK.N = 4096 := rfl
  have hb : j / 512 < 8 := by omega
  have := allBlk_spec (kSq (j / 512) hb) (j % 512) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (j / 512 * 512) (j % 512) = j := by
    change j / 512 * 512 + j % 512 = j
    omega
  rwa [e] at this

theorem map_conj_map (K : Subgroup (Equiv.Perm (Fin 360))) (a b : Equiv.Perm (Fin 360)) :
    (K.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      K.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem q8_fact {r : Equiv.Perm (Fin 360)} (hr : r ∈ Gen 360 SA 4) (ho : orderOf r = 2)
    {x y : Equiv.Perm (Fin 360)} (hxx : x * x = r) (hyy : y * y = r) (hxy : x * y * x = y)
    (hcut : ∀ h ∈ GC, h * r = r * h → h⁻¹ * x * h ∈ Gen 360 SA 4 ∧ h⁻¹ * y * h ∈ Gen 360 SA 4) :
    (∃ c ∈ Gen 360 SA 4, r = c * z0 () * c⁻¹) ∨
      5 ≤ Set.ncard {J' | ∃ g ∈ GC, g * r = r * g ∧
        (Subgroup.closure {x, y}).map (MulAut.conj g).toMonoidHom = J'} := by
  obtain ⟨k, hk, hek⟩ := cover hr ho
  obtain ⟨hi, -, -⟩ := clsF.blk k hk
  obtain ⟨-, -, hH⟩ := rootHdK_facts kRootHd
  obtain ⟨-, hRP1, hRP2, -⟩ := hH (SK.CL k) hi
  obtain ⟨hRK, hRc⟩ := clsF.blk_cl (SK.CL k) hi (SR.RP (SK.CL k)) hRP1 hRP2
  obtain ⟨g, hg, hgr⟩ := clsF.conj k hk (SR.RP (SK.CL k)) hRK hRc.symm
  rw [hek] at hgr
  have hrepo : orderOf (el 360 SA baseA 5 (SK.E (SR.RP (SK.CL k)))) = 2 :=
    clsF.ord (SR.RP (SK.CL k)) hRK
  by_cases hz : SK.CL k = SR.zc
  · left
    have hzp : SR.RP (SK.CL k) = SK.zp := by rw [hz]; exact beq_iff.1 kZc
    rw [hzp, el_zp] at hgr
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
    rw [← hgr]
    group
  right
  set rep := el 360 SA baseA 5 (SK.E (SR.RP (SK.CL k))) with hrep
  have hgGC : g ∈ GC := S_le_GC hg
  have hrr : r = g⁻¹ * rep * g := by rw [← hgr]; group
  have hxx' : g * x * g⁻¹ * (g * x * g⁻¹) = rep := by rw [← hgr, ← hxx]; group
  have hyy' : g * y * g⁻¹ * (g * y * g⁻¹) = rep := by rw [← hgr, ← hyy]; group
  have hxy' : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹) = g * y * g⁻¹ := by
    calc g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹) = g * (x * y * x) * g⁻¹ := by group
      _ = g * y * g⁻¹ := by rw [hxy]
  have hcut' : ∀ h ∈ GC, h * rep = rep * h →
      h⁻¹ * (g * x * g⁻¹) * h ∈ Gen 360 SA 4 ∧ h⁻¹ * (g * y * g⁻¹) * h ∈ Gen 360 SA 4 := by
    intro h hh hc
    have hh' : g⁻¹ * h * g ∈ GC :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgGC) hh) hgGC
    have hc' : g⁻¹ * h * g * r = r * (g⁻¹ * h * g) := by
      rw [hrr]
      have e1 : g⁻¹ * h * g * (g⁻¹ * rep * g) = g⁻¹ * (h * rep) * g := by group
      have e2 : g⁻¹ * rep * g * (g⁻¹ * h * g) = g⁻¹ * (rep * h) * g := by group
      rw [e1, e2, hc]
    obtain ⟨h1, h2⟩ := hcut _ hh' hc'
    have e1 : h⁻¹ * (g * x * g⁻¹) * h = g * ((g⁻¹ * h * g)⁻¹ * x * (g⁻¹ * h * g)) * g⁻¹ := by
      group
    have e2 : h⁻¹ * (g * y * g⁻¹) * h = g * ((g⁻¹ * h * g)⁻¹ * y * (g⁻¹ * h * g)) * g⁻¹ := by
      group
    rw [e1, e2]
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg h1) (Subgroup.inv_mem _ hg),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg h2) (Subgroup.inv_mem _ hg)⟩
  have h1c := hcut' 1 (Subgroup.one_mem _) (by group)
  have hx'G : g * x * g⁻¹ ∈ Gen 360 SA 4 := by simpa using h1c.1
  have hy'G : g * y * g⁻¹ ∈ Gen 360 SA 4 := by simpa using h1c.2
  have hrt := Orb.allN_iff.1 kRoot
  obtain ⟨p, hp, hpc, hpx⟩ := root_complete chainCK SK.hN clsF kRootHd sqB hrt hi hx'G hxx'
  obtain ⟨q, hq, hqc, hqy⟩ := root_complete chainCK SK.hN clsF kRootHd sqB hrt hi hy'G hyy'
  have hkeep : ∀ p' < SR.R, SR.RC p' = SK.CL k →
      (∀ h ∈ GC, h * rep = rep * h → h⁻¹ * el 360 SA baseA 5 (SR.RL p') * h ∈ Gen 360 SA 4) →
      SR.CT p' = 0 := by
    intro p' hp' hpc' hin
    by_contra hct
    obtain ⟨t, ht, hcomm, hnot⟩ := cut_sound chainCK (fun t ht => prepX ht)
      (Orb.allN_iff.1 kClsX) (by rw [hpc']; exact hi) ((Orb.allN_iff.1 kCut) p' hp') hct
    rw [hpc'] at hcomm
    exact hnot (hin _ (Xg_mem ht) hcomm)
  have hcp := hkeep p hp hpc fun h hh hc => by rw [hpx]; exact (hcut' h hh hc).1
  have hcq := hkeep q hq hqc fun h hh hc => by rw [hqy]; exact (hcut' h hh hc).2
  obtain ⟨mm, hmm, hQC', ⟨k1, hk1, e1⟩, ⟨k2, hk2, e2⟩⟩ := pair_sound chainCK SK.hN hrt
    (Orb.allN_iff.1 kPair) hp hq hcp hcq (hqc.trans hpc.symm) (by rw [hpc]; exact hz)
    (by rw [hpx, hqy]; exact hxy')
  have hQC : SR.QC mm = SK.CL k := hQC'.trans hpc
  obtain ⟨-, -, hQ1, hQw, hBB, hABA, hconjs, hdist⟩ := sub_facts chainCK SK.hN
    (fun t ht => prepX ht) (Orb.allN_iff.1 kClsX) ((Orb.allN_iff.1 kSub) mm hmm)
  rw [hQC] at hQ1 hconjs hdist
  set A := el 360 SA baseA 5 (SR.QJ (8 * mm + 2))
  set B := el 360 SA baseA 5 (SR.QJ (8 * mm + 4))
  have hq1 : q8G A B 1 = A * A := by simp [q8G]
  have hAA : A * A = rep := by rw [← hq1, ← hQw 1 (by norm_num), hQ1]
  have hBB' : B * B = A * A := by rw [hBB, hQw 1 (by norm_num), hq1]
  have h4 : A * (A * (A * A)) = 1 := by
    rw [← mul_assoc, hAA, ← sq, ← hrepo, pow_orderOf_eq_one]
  have hA1 : A * A ≠ 1 := by
    rw [hAA]
    intro h
    rw [h, orderOf_one] at hrepo
    norm_num at hrepo
  have hx : ∃ k < 8, q8G A B k = g * x * g⁻¹ := ⟨k1, hk1, by rw [← hQw k1 hk1, e1, hpx]⟩
  have hy : ∃ k < 8, q8G A B k = g * y * g⁻¹ := ⟨k2, hk2, by rw [← hQw k2 hk2, e2, hqy]⟩
  have hJ := q8_pair_closure h4 hBB' hABA hA1 hx hy (hxx'.trans hAA.symm) hxy'
  have h5 := five_le_conj (G' := GC) (r := rep)
    (c := fun a => Xg (SR.CJ (SR.JO (SK.CL k) + a))) hJ (fun z hz => q8_closure h4 hBB' hABA hz)
    (fun a ha => Xg_mem (hconjs a ha).1) (fun a ha => (hconjs a ha).2)
    (fun a ha b hb hab => by
      obtain ⟨k, hk, hk'⟩ := hdist a ha b hb hab
      refine ⟨k, hk, fun k' hk'' => ?_⟩
      rw [← hQw k hk, ← hQw k' hk'']
      exact hk' k' hk'')
  have hcl : Subgroup.closure ({g * x * g⁻¹, g * y * g⁻¹} : Set (Equiv.Perm (Fin 360))) =
      (Subgroup.closure {x, y}).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  let φ : Subgroup (Equiv.Perm (Fin 360)) → Subgroup (Equiv.Perm (Fin 360)) :=
    fun J => J.map (MulAut.conj g⁻¹).toMonoidHom
  have hφ : Function.Injective φ :=
    Subgroup.map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
  have hsub : φ '' {J' | ∃ c ∈ GC, c * rep = rep * c ∧
      (Subgroup.closure {g * x * g⁻¹, g * y * g⁻¹}).map (MulAut.conj c).toMonoidHom = J'} ⊆
      {J' | ∃ c ∈ GC, c * r = r * c ∧
        (Subgroup.closure {x, y}).map (MulAut.conj c).toMonoidHom = J'} := by
    rintro _ ⟨_, ⟨c, hc, hcr, rfl⟩, rfl⟩
    refine ⟨g⁻¹ * c * g, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgGC) hc) hgGC,
      ?_, ?_⟩
    · rw [hrr]
      have e1 : g⁻¹ * c * g * (g⁻¹ * rep * g) = g⁻¹ * (c * rep) * g := by group
      have e2 : g⁻¹ * rep * g * (g⁻¹ * c * g) = g⁻¹ * (rep * c) * g := by group
      rw [e1, e2, hcr]
    · simp only [φ]
      rw [hcl, map_conj_map, map_conj_map]
      try simp only [mul_assoc]
  have hfin : {J' | ∃ c ∈ GC, c * r = r * c ∧
      (Subgroup.closure {x, y}).map (MulAut.conj c).toMonoidHom = J'}.Finite := by
    refine (Set.finite_univ.image fun c : Equiv.Perm (Fin 360) =>
      (Subgroup.closure {x, y}).map (MulAut.conj c).toMonoidHom).subset ?_
    rintro _ ⟨c, -, -, rfl⟩
    exact ⟨c, Set.mem_univ _, rfl⟩
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_image_of_injective _ hφ] at this
  omega

end CertificateChecks.KernelAE6Q8

end
