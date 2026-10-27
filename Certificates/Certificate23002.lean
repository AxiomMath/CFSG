module

public import Certificates.Data.GSThmBCatalog7CF24
import Certificates.Kernel.CF24Mat.Check
import CFSG.Certificates.Kernel.CF24MatSound
import CFSG.Certificates.Kernel.CosetJ.WordsTSound
import Certificates.Kernel.CosetJ.Suz
import all Certificates.Data.GSThmBCatalog7CF24
import all CFSG.Sporadic.Recognition.SuzMultiplierInputs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki

open CFSG.ComponentClassification.GSThmB.CF24

namespace CertificateChecks.KernelCF24M

open CFSG.F3.Native CFSG.KS.F3R CFSG.KS.F3L CFSG.KC.McLMult CFSG.KC.CF24M CFSG.KC.Enum
  CFSG.Sporadic.Recognition.SuzMultiplier CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Bridge.SuzGPL.Native

theorem hI : IdL 12 (idLane 12) := idL_of id12_ok

theorem hIc : Canon 12 (idLane 12) := by
  have h := id12_ok
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact canonL_spec h.1

theorem A_eq : cf24A = unlane 12 (laneOf AT.chars) := by
  unfold cf24A
  rw [AT.eq]
  exact rowsOf_seed seedA_ok

theorem B_eq : cf24B = unlane 12 (laneOf BT.chars) := by
  unfold cf24B
  rw [BT.eq]
  exact rowsOf_seed seedB_ok

theorem img_eq : imgWords () = IT.W.toArray := by
  have h := CFSG.KC.WordsT.wordsT_sound iw_ok
  rw [← IT.eq] at h
  exact h

theorem iw_len : IT.W.length = 7 := by decide +kernel

noncomputable abbrev LA : V := laneOf AT.chars
noncomputable abbrev LB : V := laneOf BT.chars
noncomputable abbrev LAi : V := powLane 12 (spreadE 12 12) (idLane 12) LA 3
noncomputable abbrev LBi : V := powLane 12 (spreadE 12 12) (idLane 12) LB 2

noncomputable abbrev Ys : List V := ysOf 12 (spreadE 12 12) (idLane 12) LA LAi LB LBi IT.W
noncomputable abbrev Yis : List V := yisOf 12 (spreadE 12 12) (idLane 12) LA LAi LB LBi IT.W

noncomputable abbrev Xs : List V := esOf 12 (spreadE 12 12) (idLane 12) Ys Yis
noncomputable abbrev Xis : List V := eisOf 12 (spreadE 12 12) (idLane 12) Ys Yis

theorem AB_eq (z : Int) : cf24AB z = unlane 12 (abL4 LA LAi LB LBi z) := by
  unfold cf24AB
  rw [abL4_eq]
  split_ifs
  · exact A_eq
  · rw [A_eq, powM_unlane (by norm_num) hI.eq]
  · exact B_eq
  · rw [B_eq, powM_unlane (by norm_num) hI.eq]

theorem wordM_eq (w : List Int) :
    cf24WordM w = unlane 12 (abK4 12 (spreadE 12 12) (idLane 12) LA LAi LB LBi w) :=
  abK4_unlane (by norm_num) hI cf24AB AB_eq w

theorem ysOf_getD (f : List Int → V) (L : List (List Int)) {k : Nat} (hk : k < L.length) :
    (List.rec (motive := fun _ => List V) [] (fun w _ ih => f w :: ih) L).getD k V.zero =
      f L[k] := by
  induction L generalizing k with
  | nil => exact absurd hk (Nat.not_lt_zero k)
  | cons w L ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih (Nat.lt_of_succ_lt_succ hk)

theorem img_get {k : Nat} (hk : k < 7) : (imgWords ())[k]! = IT.W[k]'(iw_len ▸ hk) := by
  rw [img_eq, getElem!_pos _ k (by simp [iw_len, hk]), List.getElem_toArray]

theorem Ys_get {k : Nat} (hk : k < 7) : cf24Ys[k]! = unlane 12 (at6 Ys k) := by
  unfold cf24Ys
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn, img_get hk,
    wordM_eq]
  unfold at6 Ys ysOf
  rw [ysOf_getD _ _ (iw_len ▸ hk)]

theorem Yis_get {k : Nat} (hk : k < 7) : cf24Yis[k]! = unlane 12 (at6 Yis k) := by
  unfold cf24Yis
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn, img_get hk,
    wordM_eq]
  unfold at6 Yis yisOf
  rw [ysOf_getD (fun w => abK4 12 (spreadE 12 12) (idLane 12) LA LAi LB LBi (invZ w)) _
    (iw_len ▸ hk)]

theorem gcS_eq : gcS = 7 := by decide

theorem evalY (w : List (Fin gcS × Bool)) :
    cf24EvalM (fun k => cf24Ys[k]!) (fun k => cf24Yis[k]!) w =
      unlane 12 (evalKn 12 (spreadE 12 12) (idLane 12) (at6 Ys) (at6 Yis) w) := by
  unfold cf24EvalM
  exact evalKn_unlane (by norm_num) hI (fun k hk => Ys_get (lt_of_lt_of_eq hk gcS_eq))
    (fun k hk => Yis_get (lt_of_lt_of_eq hk gcS_eq)) w

theorem finRange_getD {α : Type} (f : Fin gcS → α) (z : α) {i : Nat} (hi : i < gcS) :
    ((List.finRange gcS).map f).getD i z = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  simp [hi]

theorem Es_get {i : Nat} (hi : i < gcS) : cf24Es[i]! = unlane 12 (at6 Xs i) := by
  unfold cf24Es
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn, evalY]
  change _ = unlane 12 ((esOf 12 (spreadE 12 12) (idLane 12) Ys Yis).getD i V.zero)
  unfold esOf
  rw [finRange_getD _ _ hi]

theorem Eis_get {i : Nat} (hi : i < gcS) : cf24Eis[i]! = unlane 12 (at6 Xis i) := by
  unfold cf24Eis
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn, evalY]
  change _ = unlane 12 ((eisOf 12 (spreadE 12 12) (idLane 12) Ys Yis).getD i V.zero)
  unfold eisOf
  rw [finRange_getD _ _ hi]

theorem evalE (w : List (Fin gcS × Bool)) :
    cf24EvalM (fun i => cf24Es[i]!) (fun i => cf24Eis[i]!) w =
      unlane 12 (evalKn 12 (spreadE 12 12) (idLane 12) (at6 Xs) (at6 Xis) w) :=
  evalKn_unlane (by norm_num) hI (fun _ hk => Es_get hk) (fun _ hk => Eis_get hk) w

theorem mat_facts : matCheckK 12 (spreadE 12 12) (idLane 12) (at6 Xs) (at6 Xis) gcS coverL suzR3
    (suzW [6, 6]) cf24C = true := by
  have h := mat_ok
  unfold matAB withEs at h
  simp only [strictT_eq, strictV_eq, strictLs_eq] at h
  exact h

theorem cf24MatCheck_true : cf24MatCheck = true := by
  obtain ⟨hinv, hrel, hr3, ⟨hdC, hdN⟩, ⟨hcC, hcN⟩⟩ := matCheckK_spec mat_facts
  unfold cf24MatCheck cf24MatCheckOf
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨fun i hi => ?_, fun w hw => ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨hX, hXi, h1, h2⟩ := hinv i hi
    rw [mulL_eq] at h1 h2
    rw [Es_get hi, Eis_get hi, mul_unlane (by norm_num), mul_unlane (by norm_num), h1, h2]
    exact ⟨⟨⟨canonM_unlane 12 hX.wf, canonM_unlane 12 hXi.wf⟩, eqM_unlane_one hI⟩,
      eqM_unlane_one hI⟩
  · have hw' : w ∈ coverL := by
      unfold coverL
      rw [← CertificateChecks.KernelCosetJ.Suz.suzCover_eq]
      exact hw
    rw [evalE, hrel w hw']
    exact eqM_unlane_one hI
  · rw [evalE, hr3]
    exact eqM_unlane_one hI
  · rw [evalE]
    exact canonM_unlane 12 hdC.wf
  · rw [evalE]
    exact eqM_unlane_ne hI hIc hdC hdN
  · rw [evalE]
    exact canonM_unlane 12 hcC.wf
  · rw [evalE]
    exact eqM_unlane_ne hI hIc hcC hcN

end CertificateChecks.KernelCF24M

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GSThmB.CF24 in
theorem certificate23002 : cf24MatCheck = true :=
  KernelCF24M.cf24MatCheck_true

end Certificates
