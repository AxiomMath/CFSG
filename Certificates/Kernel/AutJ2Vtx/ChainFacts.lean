module

public import Certificates.Kernel.AutJ2Vtx.Glue
public import Certificates.Kernel.AutJ2Vtx.Chains
public import CFSG.Certificates.Kernel.SporSch.ChainKElem
public import CFSG.Certificates.Kernel.KGC31PSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJC

open CFSG.Quasithin.F112R.St84.AutJ2Model CFSG.ComponentClassification.J2Cover
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.Certificates
open CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu CertificateChecks.KernelAJV CFSG.KS.MulH

theorem tabT_eq_tabP {X : Nat} : tabT (unpack 315 9 X) = CFSG.KC.Child3.tabP 315 9 X := by
  apply Array.ext (by simp [tabT, CFSG.KC.Child3.tabP, arrTable, unpack])
  intro i h1 h2
  simp [tabT, CFSG.KC.Child3.tabP, arrTable, unpack]

theorem img_tt {k : Nat} (hk : k < 22) :
    imageList (tp 315 (tt k)) = (unpack 315 9 (AJT k)).toList := by
  obtain ⟨c1, -, c3⟩ := inv_spec hk
  have hr := rep_tp (permOK_unpack c1 c3)
  nth_rewrite 1 [tabT_eq_tabP] at hr
  exact CFSG.KC.KGC31P.imageList_of_rep c1 hr

noncomputable abbrev gensOf (ks : List Nat) : List (Equiv.Perm (Fin 315)) :=
  ks.map fun k => tp 315 (tt k)

theorem genOf_eq (ks : List Nat) :
    genOf 315 (ks.map tt) = Subgroup.closure {g | g ∈ gensOf ks} := by
  unfold genOf
  congr 1
  ext g
  simp

theorem img_gens {ks : List Nat} (hks : ∀ k ∈ ks, k < 22) {S : Nat → Nat}
    (hS : ∀ j < ks.length, S j = AJT (ks.getD j 0)) :
    ∀ j < (gensOf ks).length, imageList ((gensOf ks).getD j 1) = (unpack 315 9 (S j)).toList := by
  intro j hj
  have hj' : j < ks.length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map, hS j hj', List.getD_eq_getElem _ _ hj']
  exact img_tt (hks _ (List.getElem_mem hj'))

theorem card_of_chain {ks : List Nat} {words : List (List Int)} {k : Nat}
    {bv : Vector (Fin 315) k} (hbs : bv.toList.Nodup) {PS PSI LR TR TRI : Nat → Nat}
    {kS BP : Nat} (hQ : ChainK 315 9 (gensOf ks) words bv PS PSI LR TR TRI kS BP 1 315) {m : Nat}
    (hm : Nat.beq (ordK LR k) m = true) : Nat.card (genOf 315 (ks.map tt)) = m := by
  rw [genOf_eq, ← certificate_originalSubgroup (by norm_num) _ words bv hbs,
    ← RawSchreierDatum.orderCertificate_eq_card _ (chainK_valid hQ (by norm_num) hbs),
    (chainK_check (by norm_num) hbs hQ).2, Nat.eq_of_beq_eq_true hm]

theorem kGS : (List.range 3).all (fun j => Nat.beq (AJS.S j) (AJT ([0, 1, 2].getD j 0))) = true := by
  decide +kernel

theorem kGW : (List.range 4).all (fun j => Nat.beq (AJW.S j) (AJT ([0, 1, 2, 6].getD j 0))) =
    true := by decide +kernel

theorem kGX1 : (List.range 4).all (fun j => Nat.beq (AJX1.S j) (AJT ([0, 1, 2, 7].getD j 0))) =
    true := by decide +kernel

theorem kGQ2 : (List.range 4).all (fun j => Nat.beq (AJQ2.S j) (AJT ([8, 9, 10, 11].getD j 0))) =
    true := by decide +kernel

theorem kGA : (List.range 4).all (fun j => Nat.beq (AJA.S j) (AJT ([21, 20, 18, 19].getD j 0))) =
    true := by decide +kernel

theorem kGQ1 : (List.range 4).all (fun j => Nat.beq (AJQ1.S j) (AJT ([14, 15, 16, 17].getD j 0))) =
    true := by decide +kernel

theorem hS_of {ks : List Nat} {S : Nat → Nat}
    (h : (List.range ks.length).all (fun j => Nat.beq (S j) (AJT (ks.getD j 0))) = true) :
    ∀ j < ks.length, S j = AJT (ks.getD j 0) := fun j hj =>
  Nat.eq_of_beq_eq_true (List.all_eq_true.1 h j (List.mem_range.2 hj))

theorem chS : ChainK 315 9 (gensOf [0, 1, 2]) wS (#v[1, 3] : Vector (Fin 315) 2)
    AJS.S AJS.SI AJS.LR AJS.TR AJS.TRI 5 AJS.BP 1 315 :=
  ⟨by norm_num, by norm_num, by norm_num, img_gens (ks := [0, 1, 2]) (by decide) (hS_of kGS),
    by decide, AJS.head, AJS.hl, by norm_num, AJS.hs⟩

theorem chW : ChainK 315 9 (gensOf [0, 1, 2, 6]) wW (#v[1, 2, 3] : Vector (Fin 315) 3)
    AJW.S AJW.SI AJW.LR AJW.TR AJW.TRI 7 AJW.BP 1 315 :=
  ⟨by norm_num, by norm_num, by norm_num, img_gens (ks := [0, 1, 2, 6]) (by decide) (hS_of kGW),
    by decide, AJW.head, AJW.hl, by norm_num, AJW.hs⟩

theorem chX1 : ChainK 315 9 (gensOf [0, 1, 2, 7]) wX1 (#v[0, 1, 3] : Vector (Fin 315) 3)
    AJX1.S AJX1.SI AJX1.LR AJX1.TR AJX1.TRI 7 AJX1.BP 1 315 :=
  ⟨by norm_num, by norm_num, by norm_num, img_gens (ks := [0, 1, 2, 7]) (by decide) (hS_of kGX1),
    by decide, AJX1.head, AJX1.hl, by norm_num, AJX1.hs⟩

theorem chQ2 : ChainK 315 9 (gensOf [8, 9, 10, 11]) wQ2 (#v[1] : Vector (Fin 315) 1)
    AJQ2.S AJQ2.SI AJQ2.LR AJQ2.TR AJQ2.TRI 4 AJQ2.BP 1 315 :=
  ⟨by norm_num, by norm_num, by norm_num,
    img_gens (ks := [8, 9, 10, 11]) (by decide) (hS_of kGQ2), by decide, AJQ2.head, AJQ2.hl,
    by norm_num, AJQ2.hs⟩

theorem chA : ChainK 315 9 (gensOf [21, 20, 18, 19]) wA (#v[0, 1] : Vector (Fin 315) 2)
    AJA.S AJA.SI AJA.LR AJA.TR AJA.TRI 5 AJA.BP 1 315 :=
  ⟨by norm_num, by norm_num, by norm_num,
    img_gens (ks := [21, 20, 18, 19]) (by decide) (hS_of kGA), by decide, AJA.head, AJA.hl,
    by norm_num, AJA.hs⟩

theorem chQ1 : ChainK 315 9 (gensOf [14, 15, 16, 17]) wQ1 (#v[1, 3] : Vector (Fin 315) 2)
    AJQ1.S AJQ1.SI AJQ1.LR AJQ1.TR AJQ1.TRI 6 AJQ1.BP 1 315 :=
  ⟨by norm_num, by norm_num, by norm_num,
    img_gens (ks := [14, 15, 16, 17]) (by decide) (hS_of kGQ1), by decide, AJQ1.head, AJQ1.hl,
    by norm_num, AJQ1.hs⟩

theorem card_S : Nat.card (genOf 315 ([0, 1, 2].map tt)) = 256 := card_of_chain (by decide) chS kNS

theorem card_W : Nat.card (genOf 315 ([0, 1, 2, 6].map tt)) = 3840 :=
  card_of_chain (by decide) chW kNW

theorem card_X1 : Nat.card (genOf 315 ([0, 1, 2, 7].map tt)) = 2304 :=
  card_of_chain (by decide) chX1 kNX1

theorem card_Q2 : Nat.card (genOf 315 ([8, 9, 10, 11].map tt)) = 32 :=
  card_of_chain (by decide) chQ2 kNQ2

theorem card_A : Nat.card (genOf 315 ([21, 20, 18, 19].map tt)) = 36 :=
  card_of_chain (by decide) chA kNA

theorem card_Q1 : Nat.card (genOf 315 ([14, 15, 16, 17].map tt)) = 64 :=
  card_of_chain (by decide) chQ1 kNQ1

end CertificateChecks.KernelAJC

end
