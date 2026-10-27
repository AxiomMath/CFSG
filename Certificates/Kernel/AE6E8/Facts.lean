module

public import Certificates.Kernel.AE6E8.Chain376
public import Certificates.Kernel.AE6E8.Twins
public import CFSG.Certificates.Kernel.AE6E8Sound
public import Certificates.Kernel.AE6Tri.FactsT
public import Certificates.Kernel.AE6Tri.FactsQ
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SAE8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.RowsBasic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KC.AE6E8 CFSG.KD.AE6Tri
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT gen)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CertificateChecks.KernelAE6Tri (gP gRep coe_curtisGen prep_gen)
open Certificates.AE6CertB Certificates.AE6Model

theorem curtis_getD (l : Nat) : (curtisPerms ()).getD l 1 = gP l := by
  by_cases hl : l < 8
  · have h1 := CertificateChecks.KernelAE6F.prep_curtis hl
    have h2 := prep_gen hl
    rw [gP, if_pos hl]
    exact Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (h2 x))
  · rw [List.getD_eq_default _ _ (by simp [curtisPerms]; omega), gP, if_neg hl]

theorem aeWord_eq (w : List Nat) : aeWord (curtisPerms ()) w = wv gP w := by
  rw [aeWord, wv]
  congr 1
  exact List.map_congr_left fun i _ => curtis_getD i

@[expose] noncomputable def S16 : Array (Array Nat) :=
  ((List.range 19).map fun j => unpack 16 5 (E8.S j)).toArray

@[expose] def base16L : List (Fin 16) := [4, 0, 2, 6, 12, 10, 8]

@[expose] def base16A : Array Nat := (base16L.map Fin.val).toArray

theorem S16_get {j : Nat} (hj : j < 19) : S16[j]! = unpack 16 5 (E8.S j) := by
  interval_cases j <;> rfl

theorem binds16 : Binds 16 5 E8.S 19 7 E8.BP S16 base16A := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [S16], fun j hj => S16_get hj, rfl,
    fun t ht => ?_⟩
  interval_cases t <;> decide

theorem rawOK16 : rawChainOK 16 (S16.extract 0 7) S16 base16A
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 7 19 e8Derive) 1 = true :=
  rawChainK_sound (NS := 1) (CH := 16) binds16 E8.head E8.hl (by norm_num) E8.hs

theorem extract_size16 : (S16.extract 0 7).size = 7 := by simp [S16]

theorem extract_get16 {i : Nat} (hi : i < 7) : (S16.extract 0 7)[i]! = S16[i]! :=
  CFSG.EvenSmallLie.OmegaEight.extract_getElem! hi (by simp [S16])

theorem perms16 : allN 19 (fun j => permOK 16 5 (mask 5) (16 * 5) (E8.S j) (E8.SI j)) = true :=
  CertificateChecks.KernelAE6F.perm_head E8.head

theorem w16 : ∀ k : Fin 7, ∀ x : Fin 16, pg 5 (mask 5) (E8.S k.val) x.val = (wr16 (ae8Gen k) x).val := by
  decide +kernel

theorem prepW (k : Fin 7) : Orb.PRep 16 5 (E8.S k.val) (wr16 (ae8Gen k)) := fun x => w16 k x

theorem gen16 : ∀ k (hk : k < 7), permOfArr 16 S16[k]! = wr16 (ae8Gen ⟨k, hk⟩) := by
  intro k hk
  have h1 := (Orb.prep_PS binds16 perms16 (j := k) (by omega)).1
  exact Equiv.ext fun x => Fin.ext ((h1 x).symm.trans (prepW ⟨k, hk⟩ x))

theorem prod16 : (rawOrbitSizes 16 S16 base16A).prod = 2580480 := by
  rw [rawOrbitSizesK_sound binds16 perms16 E8.hl, ← Nat.eq_of_beq_eq_true kOrdE8]
  simp [List.range_succ]
  ring

theorem card16 : Nat.card (Subgroup.closure {g | g ∈ ae8Gens16 ()}) = 2580480 := by
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 16) (O := S16.extract 0 7)
    (S := S16) (base := base16L)
    (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 7 19 e8Derive)
    (chunks := 1) (by norm_num) (by decide) (by norm_num) (by rw [extract_size16]; simp [S16])
    (fun i hi => (extract_get16 (extract_size16 ▸ hi)).symm) (by rw [extract_size16]; exact rawOK16)
  have e : {g | ∃ k < (S16.extract 0 7).size, permOfArr 16 (S16.extract 0 7)[k]! = g} =
      {g | g ∈ ae8Gens16 ()} := by
    ext g
    simp only [Set.mem_setOf_eq, ae8Gens16, List.mem_map, List.mem_ofFn,
      CFSG.Sporadic.Schreier.tab_eq]
    rw [extract_size16]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, ⟨⟨k, hk⟩, rfl⟩, by rw [extract_get16 hk, gen16 k hk]⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k.val, k.isLt, by rw [extract_get16 k.isLt, gen16 k.val k.isLt]⟩
  rw [e] at h
  exact h.trans prod16

@[expose] noncomputable def SR : Array (Array Nat) :=
  ((List.range 13).map fun j => unpack 376 9 (GR.S j)).toArray

@[expose] def baseRL : List (Fin 376) := [16, 18, 17, 20, 40, 24, 0]

@[expose] def baseRA : Array Nat := (baseRL.map Fin.val).toArray

theorem SR_get {j : Nat} (hj : j < 13) : SR[j]! = unpack 376 9 (GR.S j) := by
  interval_cases j <;> rfl

theorem bindsR : Binds 376 9 GR.S 13 7 GR.BP SR baseRA := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SR], fun j hj => SR_get hj, rfl,
    fun t ht => ?_⟩
  interval_cases t <;> decide

theorem rawOKR : rawChainOK 376 (SR.extract 0 8) SR baseRA
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 8 13 grDeriveK) 1 = true :=
  rawChainK_sound (NS := 16) (CH := 24) bindsR GR.head GR.hl (by norm_num) GR.hs

theorem extract_sizeR : (SR.extract 0 8).size = 8 := by simp [SR]

theorem extract_getR {i : Nat} (hi : i < 8) : (SR.extract 0 8)[i]! = SR[i]! :=
  CFSG.EvenSmallLie.OmegaEight.extract_getElem! hi (by simp [SR])

theorem permsR : allN 13 (fun j => permOK 376 9 (mask 9) (376 * 9) (GR.S j) (GR.SI j)) = true :=
  CertificateChecks.KernelAE6F.perm_head GR.head

@[expose] noncomputable def aP (k : Nat) : Equiv.Perm (Fin 16) :=
  if h : k < 7 then wr16 (ae8Gen ⟨k, h⟩) else wr16 (CFSG.ClassicalInvolution.Q3.AE.Wr.allOnes 8)

@[expose] noncomputable def rP (k : Nat) : Equiv.Perm (Fin 376) := sumPerm (aP k) (gP (grL.getD k 0))

theorem piP_rep : ∀ x : Fin 16, pg 5 (mask 5) piP x.val =
    (wr16 (CFSG.ClassicalInvolution.Q3.AE.Wr.allOnes 8) x).val := by
  decide +kernel

theorem prepA : ∀ j < grL.length, Orb.PRep 16 5 (wSel E8.S j) (aP j) := by
  intro j hj
  by_cases h : j < 7
  · rw [wSel_lt _ h, aP, dif_pos h]
    exact prepW ⟨j, h⟩
  · rw [wSel_ge _ (by omega), aP, dif_neg h]
    exact piP_rep

theorem genR : ∀ k < 8, permOfArr 376 SR[k]! = rP k := by
  intro k hk
  have hS : ∀ j < grL.length, Orb.PRep 376 9 (GR.S j) (permOfArr 376 SR[j]!) := fun j hj =>
    (Orb.prep_PS bindsR permsR (j := j) (by simp [grL] at hj; omega)).1
  exact sumOK_sound gRep prepA hS kGensGR k (by simpa [grL] using hk)

theorem grL_getD : ∀ i : Fin 7, grL.getD i.val 0 = ae8Letter.getD i.val 0 := by decide

theorem gP_eight : gP 8 = 1 := by
  rw [gP, if_neg (by norm_num)]

theorem mem_grGens {g : Equiv.Perm (Fin 376)} : g ∈ grGens () ↔ ∃ k < 8, rP k = g := by
  have e1 : ∀ i : Fin 7, CFSG.Sporadic.Schreier.tab (sumPerm (wr16 (ae8Gen i))
      ((curtisPerms ()).getD (ae8Letter.getD i 0) 1)) = rP i.val := fun i => by
    rw [CFSG.Sporadic.Schreier.tab_eq, curtis_getD, rP, aP, dif_pos i.isLt, grL_getD i]
  have e2 : CFSG.Sporadic.Schreier.tab
      (sumPerm (wr16 (CFSG.ClassicalInvolution.Q3.AE.Wr.allOnes 8)) 1) = rP 7 := by
    rw [CFSG.Sporadic.Schreier.tab_eq, rP, aP, dif_neg (by norm_num)]
    have e : grL.getD 7 0 = 8 := rfl
    rw [e, gP_eight]
  change g ∈ (List.ofFn fun i : Fin 7 => CFSG.Sporadic.Schreier.tab (sumPerm (wr16 (ae8Gen i))
      ((curtisPerms ()).getD (ae8Letter.getD i 0) 1))) ++
      [CFSG.Sporadic.Schreier.tab (sumPerm (wr16 (CFSG.ClassicalInvolution.Q3.AE.Wr.allOnes 8)) 1)] ↔ _
  rw [List.mem_append, List.mem_ofFn, List.mem_singleton, e2]
  simp only [e1]
  constructor
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨i.val, by omega, rfl⟩
    · exact ⟨7, by norm_num, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    by_cases h : k < 7
    · exact Or.inl ⟨⟨k, h⟩, rfl⟩
    · have e : k = 7 := by omega
      exact Or.inr (by rw [e])

theorem prodR : (rawOrbitSizes 376 SR baseRA).prod = 2580480 := by
  rw [rawOrbitSizesK_sound bindsR permsR GR.hl, ← Nat.eq_of_beq_eq_true kOrdGR]
  simp [List.range_succ]
  ring

theorem cardGr : Nat.card (Subgroup.closure {g | g ∈ grGens ()}) = 2580480 := by
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := 376) (O := SR.extract 0 8)
    (S := SR) (base := baseRL)
    (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 8 13 grDeriveK)
    (chunks := 1) (by norm_num) (by decide) (by norm_num) (by rw [extract_sizeR]; simp [SR])
    (fun i hi => (extract_getR (extract_sizeR ▸ hi)).symm) (by rw [extract_sizeR]; exact rawOKR)
  have e : {g | ∃ k < (SR.extract 0 8).size, permOfArr 376 (SR.extract 0 8)[k]! = g} =
      {g | g ∈ grGens ()} := by
    ext g
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, mem_grGens, extract_sizeR]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [extract_getR hk, genR k hk]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, hk, by rw [extract_getR hk, genR k hk]⟩
  rw [e] at h
  exact h.trans prodR

@[expose] noncomputable def sumHom : Equiv.Perm (Fin 16) × Equiv.Perm (Fin 360) →* Equiv.Perm (Fin 376) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 16 ⊕ Fin 360 ≃ Fin 376)).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin 16) (Fin 360))

theorem sumHom_injective : Function.Injective sumHom :=
  (Equiv.permCongrHom _).injective.comp Equiv.Perm.sumCongrHom_injective

@[expose] noncomputable def pairSub : Subgroup (Equiv.Perm (Fin 16) × Equiv.Perm (Fin 360)) :=
  Subgroup.closure {p | ∃ k < 8, (aP k, gP (grL.getD k 0)) = p}

theorem card_pairSub : Nat.card pairSub = 2580480 := by
  have e : pairSub.map sumHom = Subgroup.closure {g | g ∈ grGens ()} := by
    rw [pairSub, MonoidHom.map_closure]
    congr 1
    ext g
    rw [Set.mem_image, Set.mem_setOf_eq, mem_grGens]
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  rw [← Subgroup.card_map_of_injective sumHom_injective, e, cardGr]

theorem v0Gens_eq : v0Gens () = ae8Letter.map gP := by
  simp only [v0Gens, curtis_getD]

theorem map_snd_pairSub :
    pairSub.map (MonoidHom.snd _ _) = Subgroup.closure {g | g ∈ v0Gens ()} := by
  rw [pairSub, MonoidHom.map_closure, v0Gens_eq]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    by_cases h : k < 7
    · apply Subgroup.subset_closure
      have e := grL_getD ⟨k, h⟩
      simp only [MonoidHom.coe_snd, Set.mem_setOf_eq, List.mem_map]
      have hk' : k < ae8Letter.length := by simp [ae8Letter]; omega
      exact ⟨ae8Letter.getD k 0, by rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem _,
        congrArg gP e.symm⟩
    · have e : k = 7 := by omega
      subst e
      have e2 : grL.getD 7 0 = 8 := rfl
      simp only [MonoidHom.coe_snd, e2, gP_eight]
      exact Subgroup.one_mem _
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi
    apply Subgroup.subset_closure
    have hk7 : k < 7 := by simpa [ae8Letter] using hk
    refine ⟨_, ⟨k, by omega, rfl⟩, ?_⟩
    simp only [MonoidHom.coe_snd]
    rw [grL_getD ⟨k, hk7⟩, List.getD_eq_getElem _ _ hk]

theorem one_lt_card_ker : 1 < Nat.card ↥((MonoidHom.snd (Equiv.Perm (Fin 16)) (Equiv.Perm (Fin 360))).ker ⊓ pairSub) := by
  rw [Subgroup.one_lt_card_iff_ne_bot]
  intro h
  have hm : (aP 7, gP (grL.getD 7 0)) ∈ (MonoidHom.snd (Equiv.Perm (Fin 16)) (Equiv.Perm (Fin 360))).ker ⊓ pairSub := by
    refine ⟨MonoidHom.mem_ker.2 ?_, Subgroup.subset_closure ⟨7, by norm_num, rfl⟩⟩
    change gP (grL.getD 7 0) = 1
    have e2 : grL.getD 7 0 = 8 := rfl
    rw [e2, gP_eight]
  rw [h, Subgroup.mem_bot, Prod.mk_eq_one] at hm
  have hne : aP 7 ≠ 1 := by
    rw [aP, dif_neg (by norm_num)]
    intro e
    have e3 := congrArg (fun f : Equiv.Perm (Fin 16) => (f 0).val) e
    revert e3
    decide +kernel
  exact hne hm.1

theorem card_v0Gens_le : Nat.card (Subgroup.closure {g | g ∈ v0Gens ()}) ≤ 1290240 := by
  have h := Subgroup.relIndex_mul_card (MonoidHom.snd (Equiv.Perm (Fin 16)) (Equiv.Perm (Fin 360))).ker pairSub
  rw [Subgroup.relIndex_ker, map_snd_pairSub, card_pairSub] at h
  have h2 := one_lt_card_ker
  have h3 : Nat.card (Subgroup.closure {g | g ∈ v0Gens ()}) * 2 ≤ 2580480 := by
    rw [← h]
    exact Nat.mul_le_mul_left _ h2
  omega

theorem vl0_eq : vl.getD 0 [] = ae8Letter := by decide

theorem ae8Letter_lt : ∀ l ∈ ae8Letter, l < 8 := by decide

theorem map_ae6ModelV0 : (ae6ModelV 0).map omegaT.subtype = Subgroup.closure {g | g ∈ v0Gens ()} := by
  rw [CertificateChecks.KernelAE6Tri.vertexV0, MonoidHom.map_closure, v0Gens_eq]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map, Finset.mem_coe]
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i.val, ?_, (coe_curtisGen i).symm⟩
    rw [← vl0_eq]
    exact (CertificateChecks.KernelAE6Tri.vl0_iff i).1 hi
  · rintro ⟨l, hl, rfl⟩
    have hl8 : l < 8 := ae8Letter_lt l hl
    refine ⟨_, ⟨⟨l, hl8⟩, ?_, rfl⟩, coe_curtisGen ⟨l, hl8⟩⟩
    rw [CertificateChecks.KernelAE6Tri.vl0_iff, vl0_eq]
    exact hl

theorem cardV0 : Nat.card (Subgroup.closure {g | g ∈ v0Gens ()}) = 1290240 := by
  refine le_antisymm card_v0Gens_le ?_
  rw [← map_ae6ModelV0, Subgroup.card_map_of_injective omegaT.subtype_injective]
  exact CertificateChecks.KernelAE6Tri.card_v0_ge

theorem k0_get0 : (k0Gens ()).getD 0 1 = wv gP (e8KW.getD 0 []) := by
  simp only [k0Gens, kWords, List.map_cons, List.getD_cons_zero]
  exact aeWord_eq _

theorem k0_get1 : (k0Gens ()).getD 1 1 = wv gP (e8KW.getD 1 []) := by
  simp only [k0Gens, kWords, List.map_cons, List.getD_cons_succ, List.getD_cons_zero]
  exact aeWord_eq _

theorem q8_of {x y : Equiv.Perm (Fin 360)} (h : x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ y * y = x * x ∧
    x * y * (x * y) = x * x ∧ y ≠ x ∧ y ≠ x * x * x) :
    CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Q8Rel x y := by
  obtain ⟨h0, h4, hyy, h1, -, -⟩ := h
  have h2' : x * (y * x * y) = x * x := by
    rw [← h1]
    simp only [mul_assoc]
  have h2 : y * x * y = x := mul_left_cancel h2'
  have h3 : y * x = x * y⁻¹ := eq_mul_inv_of_mul_eq h2
  have key : y⁻¹ * x * y * x = 1 := by
    calc y⁻¹ * x * y * x = y⁻¹ * x * (y * x) := by group
      _ = y⁻¹ * x * (x * y⁻¹) := by rw [h3]
      _ = y⁻¹ * (x * x) * y⁻¹ := by group
      _ = y⁻¹ * (y * y) * y⁻¹ := by rw [hyy]
      _ = 1 := by group
  refine ⟨?_, ?_, ?_, eq_inv_of_mul_eq_one_left key⟩
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]
    exact h4
  · rw [sq]
    exact h0
  · rw [sq, sq, hyy]

theorem kq8 : CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5.Q8Rel ((k0Gens ()).getD 0 1)
    ((k0Gens ()).getD 1 1) := by
  rw [k0_get0, k0_get1]
  exact q8_of (q8OK_sound gRep kQ8)

theorem diagRels (c : Fin 2) :
    ∀ r ∈ A6.curtisRels, A6.curtisEval (List.ofFn fun i => A6.curtisGen (ae6Diag c i)) r = 1 := by
  obtain ⟨e, he⟩ := CertificateChecks.KernelAE6Tri.gamma c
  intro r hr
  have ht : (fun i => A6.curtisGen (ae6Diag c i)) = fun i => e (A6.curtisGen i) :=
    funext fun i => (he i).symm
  have hh : FreeGroup.lift (fun i => e (A6.curtisGen i)) =
      e.toMonoidHom.comp (FreeGroup.lift A6.curtisGen) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  rw [A6.curtisEval_ofFn, ht, hh, MonoidHom.comp_apply, ← A6.curtisEval_ofFn,
    A6.curtisGen_rels r hr, map_one]

@[expose] noncomputable def dl (k i : Nat) : Equiv.Perm (Fin 360) := gP ((e8D.getD k []).getD i 8)

theorem gl_eight : gl RG 8 = pidn 360 9 := rfl

theorem dRep : ∀ k i, Orb.PRep 360 9 ((e8DG.getD k []).getD i (pidn 360 9)) (dl k i) := by
  intro k i
  have e : (e8DG.getD k []).getD i (pidn 360 9) = gl RG ((e8D.getD k []).getD i 8) := by
    rw [e8DG, ← gl_eight, ← List.map_nil (f := gl RG), List.getD_map, List.map_nil, List.getD_map]
  rw [e, dl]
  exact gRep _

theorem diagWord (c : Fin 2) (s : Fin 3) : ((ae6KWord s).map (ae6Diag c)).map Fin.val =
    (e8KW.getD s.val []).map fun i => (e8D.getD c.val []).getD i 8 := by
  revert c s
  decide

theorem twinWord (c : Fin 2) : (ae6TwinWord (ae6DiagTwin c)).map Fin.val = e8CW.getD c.val [] := by
  revert c
  decide

theorem take_kgw : e8KW.take 2 = kgw := by decide

theorem diagTwins (c : Fin 2) (s : Fin 3) :
    ae6Word ((ae6KWord s).map (ae6Diag c)) ∈ ae6Twin (ae6DiagTwin c) := by
  have h := kcOK_sound gRep dRep kTwin c.val (Nat.lt_of_lt_of_le c.isLt (by decide)) s.val
    (Nat.lt_of_lt_of_le s.isLt (by decide))
  rw [ae6Twin, CFSG.ClassicalInvolution.Generic.mem_conjSub_iff]
  apply CertificateChecks.KernelAE6Tri.mem_of_coe
  have hu : (((e8U.getD c.val []).getD s.val []).map fun i => wv gP ((e8KW.take 2).getD i [])).prod ∈
      ae6ModelK.map omegaT.subtype := by
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    rw [take_kgw]
    exact CertificateChecks.KernelAE6Tri.kgw_mem i
  have hw : ((ae6Word ((ae6KWord s).map (ae6Diag c)) : AE6Om) : Equiv.Perm (Fin 360)) =
      ((e8KW.getD s.val []).map (dl c.val)).prod := by
    rw [CertificateChecks.KernelAE6Tri.coe_ae6Word, diagWord, wv, List.map_map]
    rfl
  have hc : ((ae6Word (ae6TwinWord (ae6DiagTwin c)) : AE6Om) : Equiv.Perm (Fin 360)) =
      wv gP (e8CW.getD c.val []) := by
    rw [CertificateChecks.KernelAE6Tri.coe_ae6Word, twinWord]
  have e : (((ae6Word (ae6TwinWord (ae6DiagTwin c)))⁻¹ * ae6Word ((ae6KWord s).map (ae6Diag c)) *
      ae6Word (ae6TwinWord (ae6DiagTwin c)) : AE6Om) : Equiv.Perm (Fin 360)) =
      (((e8U.getD c.val []).getD s.val []).map fun i => wv gP ((e8KW.take 2).getD i [])).prod := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hw, hc, mul_assoc, h, ← mul_assoc,
      inv_mul_cancel, one_mul]
  rw [e]
  exact hu

end CertificateChecks.KernelAE6E8

end
