module

public import Certificates.Kernel.Co3Tw.CentV
public import Certificates.Kernel.Co3Tw.PairsChk
public import Certificates.Kernel.Co3Tw.CcChk
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.F4Planes.Model
public import CFSG.RankThree.Asc83Table.E9
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.RankThree.Native.ChainCentralizerD

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Tw

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Certificates.Native CFSG.Certificates
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.B3S3K CFSG.KC.PermWit CFSG.KC.Co3Tw
  CFSG.KC.CentSrch CertificateChecks.KernelSpor

#kc_forall_chunks prAll (fun r => prR r = true) 58 CertificateChecks.KernelCo3Tw.ch431008pr_ 1

#kc_forall_chunks scAll (fun c => siftC c = true) 173 CertificateChecks.KernelCo3Tw.ch431008sc_ 1

@[expose] noncomputable def Tp (i : Nat) : Equiv.Perm (Fin 276) := ppK (EP.T i)

theorem N_eq : EP.N = 2187 := Nat.eq_of_beq_eq_true szP.2

theorem ppT {i : Nat} (hi : i < 2187) : PP 276 9 (EP.T i) :=
  PP_pts okP (fun k hk => pGk k hk) i (by rw [N_eq]; exact hi)

theorem pbT {i : Nat} (hi : i < 2187) : CFSG.KC.Misc.ArrEnum.permB 276 9 (EP.T i) = true :=
  CFSG.KC.Misc.ArrEnum.permB_of_pp (ppT hi)

theorem prepT {i : Nat} (hi : i < 2187) : Orb.PRep 276 9 (EP.T i) (Tp i) := prep_ppK (pbT hi)

theorem Tp_mem {i : Nat} (hi : i < 2187) : Tp i ∈ P := by
  have hs : i < (enumBfs 276 gsP co3ChainBaseArr.toList 3000).pts.size := by
    rw [enumP.2.1, N_eq]
    exact hi
  have hr : Rep 276 (enumBfs 276 gsP co3ChainBaseArr.toList 3000).pts[i]! (Tp i) := by
    rw [enumP.2.2 i (by rw [N_eq]; exact hi)]
    exact Orb.rep_unpack (prepT hi)
  exact enumOK_mem base_lt enumP.1 hs hr

theorem exists_Tp {x : Equiv.Perm (Fin 276)} (hx : x ∈ P) : ∃ i < 2187, Tp i = x := by
  obtain ⟨i, hi, he⟩ := ((enumOK_spec base_lt enumP.1).1 x).1 hx
  rw [enumP.2.1, N_eq] at hi
  refine ⟨i, hi, ?_⟩
  rw [← he, enumP.2.2 i (by rw [N_eq]; exact hi)]
  rfl

theorem Tp_inj {i j : Nat} (hi : i < 2187) (hj : j < 2187) (h : Tp i = Tp j) : i = j := by
  let f : Fin 2187 → P := fun a => ⟨Tp a, Tp_mem a.2⟩
  have hs : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, rfl⟩ := exists_Tp hx
    exact ⟨⟨i, hi⟩, rfl⟩
  have hb := hs.bijective_of_nat_card_le (by rw [card_P, Nat.card_eq_fintype_card, Fintype.card_fin])
  have e := hb.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h)
  exact congrArg Fin.val e

theorem prep_one : Orb.PRep 276 9 (pidn 276 9) 1 := Orb.prep_pidn (by norm_num) (by norm_num)

theorem ord3K_iff {p : Nat} (hp : PP 276 9 p) : ord3K p = true ↔ ppK p ^ 3 = 1 ∧ ppK p ≠ 1 := by
  have hpb := CFSG.KC.Misc.ArrEnum.permB_of_pp hp
  have hid : PP 276 9 (pidn 276 9) := PP.id szW
  have h3 := hp.mul (hp.mul hp)
  have e1 : Nat.beq (pcomp 276 9 (mask 9) p (pcomp 276 9 (mask 9) p p)) (pidn 276 9) = true ↔
      ppK p ^ 3 = 1 := by
    rw [← eqA_PP h3 hid, eqA_iff (Orb.rep_unpack (prep_mul (prep_ppK hpb)
      (prep_mul (prep_ppK hpb) (prep_ppK hpb)))) (Orb.rep_unpack prep_one), pow_three]
  have e2 : Nat.beq p (pidn 276 9) = true ↔ ppK p = 1 := by
    rw [← eqA_PP hp hid, eqA_iff (Orb.rep_unpack (prep_ppK hpb)) (Orb.rep_unpack prep_one)]
  unfold ord3K
  rw [Bool.and_eq_true, e1, Bool.not_eq_true', Bool.eq_false_iff, Ne, e2]

theorem cntO3_eq (N : Nat) (T : Nat → Nat) :
    cntO3 N T = ((List.range N).filter fun i => ord3K (T i)).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have e : cntO3 (N + 1) T = cntO3 N T + (if ord3K (T N) = true then 1 else 0) := by
      change Nat.add (cntO3 N T) (Bool.rec 0 1 (ord3K (T N))) = _
      cases ord3K (T N) <;> rfl
    rw [e, ih, List.range_succ, List.filter_append, List.length_append]
    by_cases h : ord3K (T N) = true <;> simp [h]

theorem sN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem lenK_eq : ∀ L : List Nat, CFSG.KC.Co3Tw.lenK L = L.length
  | [] => rfl
  | a :: L => by
    change strictN (CFSG.KC.Co3Tw.lenK L) Nat.succ = _
    rw [sN_eq, lenK_eq L]
    rfl

theorem cntR_eq (r : Nat) : ∀ L : List Nat,
    cntR r L = (L.filter fun d => Nat.beq (fld(d, 12, 4095)) r).length
  | [] => rfl
  | d :: L => by
    change strictN (cntR r L) (fun c => nIf(Nat.beq (fld(d, 12, 4095)) r, Nat.succ c, c)) = _
    rw [sN_eq, cntR_eq r L, List.filter_cons]
    cases Nat.beq (fld(d, 12, 4095)) r <;> rfl

theorem hTp : ∀ i < 2187, Orb.PRep 276 9 (EP.T i) (Tp i) ∧ Tp i ∈ co3P :=
  fun _ hi => ⟨prepT hi, P_le_co3P (Tp_mem hi)⟩

theorem hRP : ∀ r < 58, f12 PD.rp r < 2187 := by
  have h : allN 58 (fun r => Nat.blt (f12 PD.rp r) 2187) = true := by decide +kernel
  exact fun r hr => Nat.le_of_ble_eq_true (Orb.allN_iff.1 h r hr)

theorem cube_of_cubeB {p : Nat} {X : Equiv.Perm (Fin 276)} (hp : Orb.PRep 276 9 p X) (hX : X ∈ co3P)
    (h : cubeB 9 (mask 9) Co3C.BP 7 p = true) : X ^ 3 = 1 := by
  rw [pow_three]
  refine sepCo3.eq (co3P.mul_mem hX (co3P.mul_mem hX hX)) co3P.one_mem fun t ht hb => ?_
  have e := Nat.eq_of_beq_eq_true (baseT h ht)
  rw [prep_at hp hb, hp, hp] at e
  exact e

theorem idB_of_one {p : Nat} (hp : Orb.PRep 276 9 p 1) : idB 9 (mask 9) Co3C.BP 7 p = true := by
  refine Orb.allN_iff.2 fun t ht => ?_
  rw [sB_eq, Nat.beq_eq, prep_at hp (bp_lt t ht)]
  rfl

@[expose] noncomputable def Xr (r : Nat) : Equiv.Perm (Fin 276) := Tp (f12 PD.rp r)

theorem Xr_ord {r : Nat} (hr : r < 58) : Xr r ^ 3 = 1 ∧ Xr r ≠ 1 := by
  have h := Orb.allN_iff.1 ch431008o3 r hr
  rw [sB_eq, bA_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hp, hm⟩ := hTp _ (hRP r hr)
  refine ⟨cube_of_cubeB hp hm h.1, fun h1 => ?_⟩
  have hp1 : Orb.PRep 276 9 (EP.T (f12 PD.rp r)) 1 := by
    rw [← h1]
    exact hp
  rw [idB_of_one hp1] at h
  exact absurd h.2 (by decide)

theorem crFacts : List.Pairwise (· < ·) (PD.cr.map jOf) ∧ ∀ d ∈ PD.cr, 0 ≤ jOf d ∧ jOf d < 2187 ∧
    fld(d, 12, 4095) < 58 ∧ Nat.shiftRight d 24 < 2187 ∧
    Tp (Nat.shiftRight d 24) * Tp (jOf d) =
      Tp (f12 PD.rp (fld(d, 12, 4095))) * Tp (Nat.shiftRight d 24) := by
  have h := ch431008cr
  rw [bA_eq, Bool.and_eq_true] at h
  exact crChk_sound sepCo3 hTp hRP PD.cr 0 h.1

theorem cr_len : PD.cr.length = 890 := by
  have h := ch431008cr
  rw [bA_eq, Bool.and_eq_true] at h
  rw [← lenK_eq]
  exact Nat.eq_of_beq_eq_true h.2

theorem conj_of_rec {d : Nat} (hd : d ∈ PD.cr) :
    Tp (jOf d) = (Tp (Nat.shiftRight d 24))⁻¹ * Xr (fld(d, 12, 4095)) * Tp (Nat.shiftRight d 24) := by
  obtain ⟨-, -, -, -, he⟩ := crFacts.2 d hd
  rw [Xr, mul_assoc, ← he, ← mul_assoc, inv_mul_cancel, one_mul]

theorem conj_pow3 (a X : Equiv.Perm (Fin 276)) : (a⁻¹ * X * a) ^ 3 = a⁻¹ * X ^ 3 * a := by
  have h := conj_pow (a := a⁻¹) (b := X) (i := 3)
  rwa [inv_inv] at h

theorem ord3_rec {d : Nat} (hd : d ∈ PD.cr) : ord3K (EP.T (jOf d)) = true := by
  obtain ⟨-, hj, hr, -, -⟩ := crFacts.2 d hd
  rw [ord3K_iff (ppT hj)]
  change Tp (jOf d) ^ 3 = 1 ∧ Tp (jOf d) ≠ 1
  rw [conj_of_rec hd]
  obtain ⟨h3, h1⟩ := Xr_ord hr
  refine ⟨?_, fun h => h1 ?_⟩
  · rw [conj_pow3, h3, mul_one, inv_mul_cancel]
  · have := congrArg (fun z => Tp (Nat.shiftRight d 24) * z * (Tp (Nat.shiftRight d 24))⁻¹) h
    simpa [mul_assoc] using this

theorem cr_cover {i : Nat} (hi : i < 2187) (h3 : ord3K (EP.T i) = true) :
    ∃ d ∈ PD.cr, jOf d = i := by
  have hnd : (PD.cr.map jOf).Nodup := crFacts.1.imp (fun h => ne_of_lt h)
  set O := (List.range 2187).filter fun i => ord3K (EP.T i)
  have hO : O.length = 890 := by
    have h := Nat.eq_of_beq_eq_true o3P
    rw [cntO3_eq] at h
    exact h
  have hOn : O.Nodup := (List.nodup_range).filter _
  have hsub : (PD.cr.map jOf).toFinset ⊆ O.toFinset := by
    intro j hj
    rw [List.mem_toFinset, List.mem_map] at hj
    obtain ⟨d, hd, rfl⟩ := hj
    rw [List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨(crFacts.2 d hd).2.1, ord3_rec hd⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hOn, List.toFinset_card_of_nodup hnd, List.length_map, hO,
      cr_len])
  have hiO : i ∈ O.toFinset := by
    rw [List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨hi, h3⟩
  rw [← heq, List.mem_toFinset, List.mem_map] at hiO
  exact hiO

theorem prep_ppow {p : Nat} {g : Equiv.Perm (Fin 276)} (hg : Orb.PRep 276 9 p g) :
    ∀ e, Orb.PRep 276 9 (ppow 276 9 (mask 9) (pidn 276 9) p e) (g ^ e)
  | 0 => by
    rw [pow_zero]
    exact prep_one
  | e + 1 => by
    change Orb.PRep 276 9 (strictN (ppow 276 9 (mask 9) (pidn 276 9) p e)
      (fun q => pcomp 276 9 (mask 9) p q)) _
    rw [sN_eq, pow_succ']
    exact prep_mul hg (prep_ppow hg e)

@[expose] noncomputable def Dk (k d : Nat) : Equiv.Perm (Fin 276) :=
  ppK (xpK k) ^ ((d + 1) % 3) * ppK (ypK k) ^ ((d + 1) / 3)

noncomputable abbrev DK (k : Nat) : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure ({ppK (xpK k), ppK (ypK k)} : Set (Equiv.Perm (Fin 276)))

theorem Dk_mem_DK (k d : Nat) : Dk k d ∈ DK k :=
  (DK k).mul_mem ((DK k).pow_mem (Subgroup.subset_closure (Set.mem_insert _ _)) _)
    ((DK k).pow_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)

theorem dOK_k {k : Nat} (hk : k < 7) : dOK 276 9 (xpK k) (ypK k) (dpK k) = true := by
  interval_cases k
  · exact ch431008d0
  · exact ch431008d1
  · exact ch431008d2
  · exact ch431008d3
  · exact ch431008d4
  · exact ch431008d5
  · exact ch431008d6

theorem dOK_fields {X Y DP : Nat} {x y : Equiv.Perm (Fin 276)} (hx : Orb.PRep 276 9 X x)
    (hy : Orb.PRep 276 9 Y y) (h : dOK 276 9 X Y DP = true) :
    ∀ d < 8, Orb.PRep 276 9 (fNW 276 9 DP d) (x ^ ((d + 1) % 3) * y ^ ((d + 1) / 3)) := by
  intro d hd
  unfold dOK at h
  rw [bA_eq, bA_eq, bA_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  have e := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h.2.2 d hd)
  rw [show fNW 276 9 DP d = _ from e]
  exact prep_mul (prep_ppow hx _) (prep_ppow hy _)

theorem hD : ∀ k < 7, ∀ d < 8, Orb.PRep 276 9 (fNW 276 9 (dpK k) d) (Dk k d) ∧ Dk k d ∈ co3P :=
  fun k hk d hd => ⟨dOK_fields (prep_ppK (gk k hk).1) (prep_ppK (gk k hk).2) (dOK_k hk) d hd,
    co3P.mul_mem (co3P.pow_mem (ppK_mem (gk k hk).1 (sk k hk).1) _)
      (co3P.pow_mem (ppK_mem (gk k hk).2 (sk k hk).2) _)⟩

@[expose] noncomputable def CGp (c : Nat) : Equiv.Perm (Fin 276) := ppK (fNW 276 9 PD.cc c)

theorem hC : ∀ c < 173, Orb.PRep 276 9 (fNW 276 9 PD.cc c) (CGp c) ∧ CGp c ∈ co3P := by
  intro c hc
  have hp : CFSG.KC.Misc.ArrEnum.permB 276 9 (fNW 276 9 PD.cc c) = true :=
    Orb.allN_iff.1 ch431008cp c hc
  have hs : siftR 276 9 Co3C.LR Co3C.TRI Co3C.BP 7 (fNW 276 9 PD.cc c) = true := scAll c hc
  exact ⟨prep_ppK hp, ppK_mem hp hs⟩

theorem prFacts {r : Nat} (hr : r < 58) :
    List.Pairwise (· < ·) ((nthL PD.pr r).map jOf) ∧
      (∀ e ∈ nthL PD.pr r, 0 ≤ jOf e ∧ jOf e < 2187 ∧
        PairFact Tp CGp Dk 173 2187 (Xr r) (Tp (jOf e))) ∧
      (nthL PD.pr r).length * f12 PD.cn r = 2187 := by
  have h := prAll r hr
  unfold prR at h
  rw [sB_eq, bA_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hp, hm⟩ := hTp _ (hRP r hr)
  have hs := prChk_sound sepCo3 hTp hC hD hp hm (nthL PD.pr r) 0 h1
  refine ⟨hs.1, hs.2, ?_⟩
  rw [← lenK_eq]
  exact Nat.eq_of_beq_eq_true h2

@[expose] noncomputable def fP (j : Nat) : P := if h : j < 2187 then ⟨Tp j, Tp_mem h⟩ else 1

theorem fP_inj : Set.InjOn fP {j | j < 2187} := by
  intro i hi j hj h
  have h' := congrArg Subtype.val h
  simp only [fP, dif_pos (show i < 2187 from hi), dif_pos (show j < 2187 from hj)] at h'
  exact Tp_inj hi hj h'

theorem card_image_fP {L : List Nat} (hL : L.Nodup) (hlt : ∀ j ∈ L, j < 2187) :
    (L.toFinset.image fP).card = L.length := by
  rw [Finset.card_image_of_injOn (fun i hi j hj h => fP_inj (hlt i (List.mem_toFinset.1 hi))
    (hlt j (List.mem_toFinset.1 hj)) h), List.toFinset_card_of_nodup hL]

theorem pr_cover {r : Nat} (hr : r < 58) {y : Equiv.Perm (Fin 276)} (hy : y ∈ P)
    (hc : Xr r * y = y * Xr r) : ∃ e ∈ nthL PD.pr r, Tp (jOf e) = y := by
  classical
  obtain ⟨hpw, hmem, hlen⟩ := prFacts hr
  have hxr : Xr r ∈ P := Tp_mem (hRP r hr)
  set xr : P := ⟨Xr r, hxr⟩ with hxrdef
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [card_P]; norm_num)
  have : Fintype P := Fintype.ofFinite _
  have : Fintype ↑(MulAction.orbit (ConjAct P) xr) := Fintype.ofFinite _
  have : Fintype ↥(MulAction.stabilizer (ConjAct P) xr) := Fintype.ofFinite _
  have hOS : Nat.card (MulAction.orbit (ConjAct P) xr) *
      Nat.card (MulAction.stabilizer (ConjAct P) xr) = 2187 := by
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct P) xr
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    convert h using 1
    rw [ConjAct.card, ← Nat.card_eq_fintype_card, card_P]
  set S := (PD.cr.filter fun d => Nat.beq (fld(d, 12, 4095)) r).map jOf with hSdef
  have hSsub : ∀ j ∈ S, ∃ d ∈ PD.cr, jOf d = j ∧ fld(d, 12, 4095) = r := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hj
    rw [List.mem_filter] at hd
    exact ⟨d, hd.1, rfl, Nat.eq_of_beq_eq_true hd.2⟩
  have hSlt : ∀ j ∈ S, j < 2187 := fun j hj => by
    obtain ⟨d, hd, rfl, -⟩ := hSsub j hj
    exact (crFacts.2 d hd).2.1
  have hSnd : S.Nodup :=
    ((crFacts.1.imp (fun h => ne_of_lt h)).sublist (List.Sublist.map _ List.filter_sublist))
  have hSlen : S.length = f12 PD.cn r := by
    rw [hSdef, List.length_map, ← cntR_eq]
    exact Nat.eq_of_beq_eq_true (Orb.allN_iff.1 ch431008cn r hr)
  have horb : f12 PD.cn r ≤ Nat.card (MulAction.orbit (ConjAct P) xr) := by
    rw [← hSlen, ← card_image_fP hSnd hSlt, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro z hz
    rw [Finset.coe_image, Set.mem_image] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    obtain ⟨d, hd, rfl, hdr⟩ := hSsub j (List.mem_toFinset.1 hj)
    obtain ⟨-, hjl, -, htl, -⟩ := crFacts.2 d hd
    refine ⟨ConjAct.toConjAct (fP (Nat.shiftRight d 24))⁻¹, ?_⟩
    apply Subtype.ext
    dsimp only
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    simp only [fP, dif_pos htl, dif_pos hjl, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv,
      hxrdef]
    rw [conj_of_rec hd, hdr]
  set J := (nthL PD.pr r).map jOf with hJdef
  have hJlt : ∀ j ∈ J, j < 2187 := fun j hj => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hj
    exact (hmem e he).2.1
  have hJnd : J.Nodup := hpw.imp (fun h => ne_of_lt h)
  set F : Finset (ConjAct P) := (J.toFinset.image fP).image ConjAct.toConjAct with hF
  have hFc : F.card = J.length := by
    rw [hF, Finset.card_image_of_injective _ ConjAct.toConjAct.injective, card_image_fP hJnd hJlt]
  have hFs : (F : Set (ConjAct P)) ⊆ MulAction.stabilizer (ConjAct P) xr := by
    intro z hz
    rw [hF, Finset.coe_image, Set.mem_image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [Finset.mem_coe, Finset.mem_image] at hu
    obtain ⟨j, hj, rfl⟩ := hu
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hj)
    obtain ⟨-, hjl, hcomm, -⟩ := hmem e he
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct]
    apply Subtype.ext
    simp only [fP, dif_pos hjl, Subgroup.coe_mul, Subgroup.coe_inv, hxrdef]
    rw [← hcomm, mul_inv_cancel_right]
  have hstab : J.length ≤ Nat.card (MulAction.stabilizer (ConjAct P) xr) := by
    rw [← hFc, ← Set.ncard_coe_finset]
    exact (Set.ncard_le_ncard hFs (Set.toFinite _)).trans
      (Nat.card_coe_set_eq (MulAction.stabilizer (ConjAct P) xr : Set (ConjAct P))).symm.le
  have hJlen : J.length = (nthL PD.pr r).length := List.length_map _
  have hcn : 0 < f12 PD.cn r := by
    rcases Nat.eq_zero_or_pos (f12 PD.cn r) with h0 | h0
    · rw [h0, mul_zero] at hlen
      exact absurd hlen (by norm_num)
    · exact h0
  have heq : Nat.card (MulAction.stabilizer (ConjAct P) xr) = J.length := by
    by_contra hne
    have hgt : J.length + 1 ≤ Nat.card (MulAction.stabilizer (ConjAct P) xr) := by omega
    have h1 := Nat.mul_le_mul horb hgt
    rw [hOS, hJlen, mul_add, mul_one, mul_comm, hlen] at h1
    omega
  have hFeq : (F : Set (ConjAct P)) = MulAction.stabilizer (ConjAct P) xr :=
    Set.eq_of_subset_of_ncard_le hFs (by
      rw [Set.ncard_coe_finset, hFc, ← heq]
      exact (Nat.card_coe_set_eq _).le) (Set.toFinite _)
  have hyst : ConjAct.toConjAct (⟨y, hy⟩ : P) ∈ (F : Set (ConjAct P)) := by
    rw [hFeq, SetLike.mem_coe, MulAction.mem_stabilizer_iff, ConjAct.smul_def,
      ConjAct.ofConjAct_toConjAct]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxrdef]
    rw [← hc, mul_inv_cancel_right]
  rw [hF, Finset.coe_image, Set.mem_image] at hyst
  obtain ⟨u, hu, hu'⟩ := hyst
  rw [Finset.mem_coe, Finset.mem_image] at hu
  obtain ⟨j, hj, rfl⟩ := hu
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hj)
  refine ⟨e, he, ?_⟩
  have h2 := congrArg Subtype.val (ConjAct.toConjAct.injective hu')
  simpa only [fP, dif_pos (hmem e he).2.1] using h2

theorem pair_conj {x y : Equiv.Perm (Fin 276)} (hx : x ∈ P) (hy : y ∈ P) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x) :
    ∃ g ∈ co3P, ∃ k < 7, g * x * g⁻¹ ∈ DK k ∧ g * y * g⁻¹ ∈ DK k := by
  obtain ⟨i, hi, rfl⟩ := exists_Tp hx
  obtain ⟨d, hd, hdi⟩ := cr_cover hi ((ord3K_iff (ppT hi)).2 ⟨hx3, hx1⟩)
  obtain ⟨-, -, hr, ht, -⟩ := crFacts.2 d hd
  have hconj := conj_of_rec hd
  rw [hdi] at hconj
  set a := Tp (Nat.shiftRight d 24) with ha
  set r := fld(d, 12, 4095) with hrdef
  have haP : a ∈ P := Tp_mem ht
  have hXr : Xr r = MulAut.conj a (Tp i) := by
    rw [MulAut.conj_apply, hconj]
    group
  set y' := MulAut.conj a y with hy'
  have hy'P : y' ∈ P := by
    rw [hy', MulAut.conj_apply]
    exact P.mul_mem (P.mul_mem haP hy) (P.inv_mem haP)
  have hcomm : Xr r * y' = y' * Xr r := by
    rw [hXr, hy', ← map_mul, ← map_mul, hxy]
  obtain ⟨e, he, hey⟩ := pr_cover hr hy'P hcomm
  obtain ⟨-, -, -, hk⟩ := (prFacts hr).2.1 e he
  rw [hey] at hk
  have hinj := (MulAut.conj a).injective
  rcases hk with h0 | ⟨k, hk7, c, hc, p, hp, d1, -, d2, -, h1, h2⟩
  · exfalso
    rcases h0 with h0 | h0 | h0 | h0
    · rw [hy', ← map_one (MulAut.conj a)] at h0
      exact hyx (hinj h0 ▸ (Subgroup.zpowers (Tp i)).one_mem)
    · rw [hy', hXr] at h0
      exact hyx (hinj h0 ▸ Subgroup.mem_zpowers _)
    · rw [hy', hXr, ← map_mul] at h0
      exact hyx (hinj h0 ▸ (Subgroup.zpowers (Tp i)).mul_mem (Subgroup.mem_zpowers _)
        (Subgroup.mem_zpowers _))
    · exact h0 (by rw [hy', ← map_pow, hy3, map_one])
  · obtain ⟨-, hCm⟩ := hC c hc
    obtain ⟨-, hTm⟩ := hTp p hp
    have haC : a ∈ co3P := P_le_co3P haP
    set h := CGp c * Tp p with hh
    have hm : h ∈ co3P := co3P.mul_mem hCm hTm
    refine ⟨h * a, co3P.mul_mem hm haC, k, hk7, ?_, ?_⟩
    · have e1 : h * a * Tp i * (h * a)⁻¹ = h * Xr r * h⁻¹ := by
        rw [hXr, MulAut.conj_apply]
        group
      rw [e1, h1, mul_inv_cancel_right]
      exact Dk_mem_DK k d1
    · have e2 : h * a * y * (h * a)⁻¹ = h * y' * h⁻¹ := by
        rw [hy', MulAut.conj_apply]
        group
      rw [e2, h2, mul_inv_cancel_right]
      exact Dk_mem_DK k d2

theorem prep_eq_of_beq {p q : Nat} {g h : Equiv.Perm (Fin 276)} (hg : Orb.PRep 276 9 p g)
    (hh : Orb.PRep 276 9 q h) (e : Nat.beq p q = true) : g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hg
  exact prep_uniq hg hh

theorem card_DK_le {k : Nat} (hk : k < 7) : Nat.card (DK k) ≤ 9 := by
  have h := dOK_k hk
  unfold dOK at h
  rw [bA_eq, bA_eq, bA_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hx3, hy3⟩, hxy, -⟩ := h
  have px := prep_ppK (gk k hk).1
  have py := prep_ppK (gk k hk).2
  exact CFSG.KC.F4Planes.card_closure_pair_le (prep_eq_of_beq (prep_mul px py) (prep_mul py px) hxy)
    (prep_eq_of_beq (prep_ppow px 3) prep_one hx3) (prep_eq_of_beq (prep_ppow py 3) prep_one hy3)

theorem closed_of_le_P (E : Subgroup (Equiv.Perm (Fin 276))) (hEP : E ≤ P)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hc : Nat.card E = 9)
    (a : Equiv.Perm (Fin 276)) (ha : a ∈ co3P) (b : Equiv.Perm (Fin 276)) (hb : b ∈ co3P)
    (haE : a ∈ Subgroup.centralizer (E : Set (Equiv.Perm (Fin 276))))
    (hbE : b ∈ Subgroup.centralizer (E : Set (Equiv.Perm (Fin 276))))
    (ha3 : ∃ m, a ^ 3 ^ m = 1) (hb3 : ∃ m, b ^ 3 ^ m = 1) : ∃ m, (a * b) ^ 3 ^ m = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    by_contra hne
    simp only [not_exists, not_and, not_not] at hne
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hne
    rw [hbot, Subgroup.card_bot] at hc
    exact absurd hc (by norm_num)
  have hox : orderOf x = 3 := orderOf_eq_prime (h3 x hxE) hx1
  obtain ⟨y, hyE, hyx⟩ : ∃ y ∈ E, y ∉ Subgroup.zpowers x := by
    by_contra hne
    simp only [not_exists, not_and, not_not] at hne
    have hz : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hox]
    have : Finite (Subgroup.zpowers x) := Nat.finite_of_card_ne_zero (by rw [hz]; norm_num)
    have hle := Subgroup.card_le_of_le (H := E) (K := Subgroup.zpowers x) hne
    rw [hz, hc] at hle
    exact absurd hle (by norm_num)
  obtain ⟨g, hg, k, hk, hgx, hgy⟩ := pair_conj (hEP hxE) (hEP hyE) (h3 x hxE) hx1 (h3 y hyE)
    (hab x hxE y hyE) hyx
  set u := MulAut.conj g x with hu
  set v := MulAut.conj g y with hv
  rw [← MulAut.conj_apply] at hgx hgy
  have hvu : v ∉ Subgroup.zpowers u := by
    rintro ⟨z, hz⟩
    apply hyx
    refine ⟨z, (MulAut.conj g).injective ?_⟩
    rw [map_zpow]
    exact hz
  have h9 : Nat.card (Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 276)))) = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine (by rw [hu, ← map_pow, h3 x hxE, map_one])
      (by rw [hv, ← map_pow, h3 y hyE, map_one])
      (by
        change u * v = v * u
        rw [hu, hv, ← map_mul, ← map_mul, hab x hxE y hyE])
      (by
        rw [hu, Ne, ← map_one (MulAut.conj g)]
        exact fun h => hx1 ((MulAut.conj g).injective h))
      hvu
  have hle : Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 276))) ≤ DK k := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hgx
    · exact hgy
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [h9]; exact card_DK_le hk)
  have hcen : ∀ z ∈ co3P, z ∈ Subgroup.centralizer (E : Set (Equiv.Perm (Fin 276))) →
      MulAut.conj g z ∈ Cent k := by
    intro z hz hzE
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [MulAut.conj_apply]
      exact co3P.mul_mem (co3P.mul_mem hg hz) (co3P.inv_mem hg)
    · have hzc : Subgroup.closure ({u, v} : Set (Equiv.Perm (Fin 276))) ≤
          Subgroup.centralizer ({MulAut.conj g z} : Set (Equiv.Perm (Fin 276))) := by
        rw [Subgroup.closure_le]
        rintro w (rfl | rfl)
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
          rintro _ rfl
          rw [hu, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hzE x hxE]
        · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
          rintro _ rfl
          rw [hv, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hzE y hyE]
      rw [heq] at hzc
      rw [Subgroup.mem_centralizer_iff]
      rintro w hw
      have hwD : w ∈ DK k := by
        rcases hw with rfl | rfl
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      exact (Subgroup.mem_centralizer_iff.1 (hzc hwD) _ rfl).symm
  obtain ⟨m, hm⟩ := closed_cent hk (hcen a ha haE) (hcen b hb hbE) (by
      obtain ⟨m, hm⟩ := ha3
      exact ⟨m, by rw [← map_pow, hm, map_one]⟩)
    (by
      obtain ⟨m, hm⟩ := hb3
      exact ⟨m, by rw [← map_pow, hm, map_one]⟩)
  refine ⟨m, (MulAut.conj g).injective ?_⟩
  rw [map_pow, map_mul, hm, map_one]

end CertificateChecks.KernelCo3Tw

end
