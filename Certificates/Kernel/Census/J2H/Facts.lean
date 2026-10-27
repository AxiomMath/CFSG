module

public import Certificates.Kernel.Census.J2H.Checks
public import Certificates.Kernel.Census.J2H.Count
public import CFSG.Certificates.Kernel.J2HSound
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBCertInputs
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCentralizers
public import CFSG.Sporadic.SmallOddCore.LocalSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2H

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.J2H CFSG.KC.Misc.ArrEnum
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.Kernel CFSG.ComponentClassification.HarrisLit.EndB
open CertificateChecks.KernelJ2Cover

noncomputable abbrev gC (h : ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 cent2AStrong[h]!

noncomputable abbrev gB (h : ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 cent2BStrong[h]!

theorem sgnProd_expandW_mem {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}
    {gs : ℕ → Equiv.Perm (Fin n)} (subs : List (List ℤ))
    (hs : ∀ i < subs.length, sgnProd gs (subs.getD i []) ∈ H) :
    ∀ w : List ℕ, (∀ l ∈ w, 1 ≤ l ∧ l ≤ subs.length) → sgnProd gs (expandW subs w) ∈ H
  | [], _ => H.one_mem
  | l :: w, hw => by
    have h1 := hw l List.mem_cons_self
    have e : expandW subs (l :: w) = subs.getD (l - 1) [] ++ expandW subs w := by
      simp [expandW]
    rw [e, sgnProd_append]
    exact H.mul_mem (hs _ (by omega))
      (sgnProd_expandW_mem subs hs w fun l' hl' => hw l' (List.mem_cons_of_mem l hl'))

theorem sgnProd_invW {n : ℕ} (gs : ℕ → Equiv.Perm (Fin n)) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0) → sgnProd gs (invW w) = (sgnProd gs w)⁻¹
  | [], _ => by simp [invW]
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have e : invW (l :: w) = invW w ++ [-l] := by simp [invW]
    rw [e, sgnProd_append, sgnProd_invW gs w fun l' hl' => hw l' (List.mem_cons_of_mem l hl')]
    simp only [sgnProd_cons, sgnProd_nil, mul_one, mul_inv_rev]
    congr 1
    by_cases hpos : 0 < l
    · rw [if_neg (by omega), if_pos hpos, neg_neg]
    · rw [if_pos (by omega), if_neg hpos, inv_inv]

theorem rep_c2A {j : ℕ} (hj : j < 5) : Rep 315 (unpack 315 9 (C2A.S j)) (gC j) := by
  rw [← c2A_binds.2.2.2.2.1 j hj]
  exact (rep_of_binds c2A_binds c2A_perm hj).1

theorem word_c2A {wd : List ℤ} {r : ℕ} (h : wA wd r = true) :
    Rep 315 (unpack 315 9 r) (sgnProd gC wd) :=
  word_rep c2A_binds c2A_perm h

theorem gC_mem {i : ℕ}
    (hi : i < 2) : gC i ∈ centralizerIn P permTwoA := by
  rw [centralizerIn_P_permTwoA.1, cent2AChain, ofArrays_originalSubgroup]
  exact subset_closure ⟨i, hi, rfl⟩

theorem gB_mem {i : ℕ}
    (hi : i < 2) : gB i ∈ centralizerIn P permA := by
  rw [centralizerIn_P_permA.1, cent2BChain, ofArrays_originalSubgroup]
  exact subset_closure ⟨i, hi, rfl⟩

theorem order_five {X : ℕ} {x : Equiv.Perm (Fin 315)} (hX : Rep 315 (unpack 315 9 X) x)
    (h5 : Rep 315 (unpack 315 9 (pidn 315 9)) (x * x * x * x * x))
    (hne : neK 315 9 (mask 9) (315 * 9) X (pidn 315 9) = true) : orderOf x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ fun h1 => ?_
  · have := h5.unique rep_pidn
    simpa [pow_succ, mul_assoc] using this
  · have he := neK_sound hne
    rw [(eqA_iff hX rep_pidn).2 h1] at he
    exact Bool.noConfusion he

theorem odd_gens :
    ∃ x y : Equiv.Perm (Fin 315), x ∈ centralizerIn P permTwoA ∧
      y ∈ centralizerIn P permTwoA ∧ orderOf x = 5 ∧ orderOf y = 5 ∧
      closure {x, y} = centralizerIn P permTwoA := by
  have hg : ∀ i < 2, gC i ∈ centralizerIn P permTwoA := fun i hi => gC_mem hi
  have hx := sgnProd_mem hg xW (by decide)
  have hy := sgnProd_mem hg yW (by decide)
  refine ⟨_, _, hx, hy, ?_, ?_, le_antisymm ?_ ?_⟩
  · refine order_five (word_c2A x_val) ?_ x_ne
    have := word_c2A x_pow
    simpa only [sgnProd_append, mul_assoc] using this
  · refine order_five (word_c2A y_val) ?_ y_ne
    have := word_c2A y_pow
    simpa only [sgnProd_append, mul_assoc] using this
  · rw [closure_le]
    rintro _ (rfl | rfl)
    · exact hx
    · exact hy
  · rw [centralizerIn_P_permTwoA.1, cent2AChain, ofArrays_originalSubgroup, closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hs : ∀ i < [xW, yW].length, sgnProd gC ([xW, yW].getD i []) ∈
        closure {sgnProd gC xW, sgnProd gC yW} := by
      intro i hi
      obtain rfl | rfl : i = 0 ∨ i = 1 := by simp at hi; omega
      · exact subset_closure (Set.mem_insert _ _)
      · exact subset_closure (Set.mem_insert_of_mem _ rfl)
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · have e := (word_c2A g1_xy).unique (rep_c2A (j := 0) (by norm_num))
      have h := sgnProd_expandW_mem _ hs g1W (by decide)
      rw [e] at h
      exact h
    · have e := (word_c2A g2_xy).unique (rep_c2A (j := 1) (by norm_num))
      have h := sgnProd_expandW_mem _ hs g2W (by decide)
      rw [e] at h
      exact h

theorem mem_centralizer_closure_iff {G : Type*} [Group G] {T : Set G} {x : G} :
    x ∈ centralizer (closure T : Set G) ↔ ∀ t ∈ T, x * t = t * x := by
  constructor
  · intro h t ht
    exact ((mem_centralizer_iff.1 h) t (subset_closure ht)).symm
  · intro h
    rw [mem_centralizer_iff]
    intro t ht
    have hle : closure T ≤ centralizer {x} := by
      rw [closure_le]
      intro s hs
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (h s hs).symm
    exact mem_centralizer_singleton_iff.1 (hle ht)

theorem card_inf_eq {G : Type*} [Group G] (H K : Subgroup G) (p : G → Prop)
    (hp : ∀ x, x ∈ K ↔ p x) : Nat.card ↥(H ⊓ K) = Nat.card {x : H // p x} :=
  Nat.card_congr
    { toFun := fun x => ⟨⟨x, (mem_inf.1 x.2).1⟩, (hp x).1 (mem_inf.1 x.2).2⟩
      invFun := fun x => ⟨x.1, mem_inf.2 ⟨x.1.2, (hp x.1).2 x.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem crT_chain' : rawChainOK 315 (crTStrong.extract 0 3) crTStrong
    (([0, 1, 2] : List (Fin 315)).map Fin.val).toArray crTWords 4 = true := by
  rw [crTBase_eq]
  exact crT_chain.1

theorem crT_binds' : Binds 315 9 CRT.S 7 3 CRT.BP crTStrong
    (([0, 1, 2] : List (Fin 315)).map Fin.val).toArray := by
  rw [crTBase_eq]
  exact crT_binds

theorem card_cent_crT
    {T : Set (Equiv.Perm (Fin 315))} {G : ℕ → ℕ} {g : ℕ → Equiv.Perm (Fin 315)}
    (hT : ∀ t, t ∈ T ↔ ∃ j < 4, t = g j)
    (hG : ∀ j < 4, canonK 315 9 (mask 9) (315 * 9) (G j) = true ∧
      Rep 315 (unpack 315 9 (G j)) (g j)) :
    Nat.card ↥(centralizerIn R permTwoA ⊓ centralizer (closure T : Set (Equiv.Perm (Fin 315)))) =
      CFSG.KC.J2Cover.prodCnt 315 9 3 CRT.LR CRT.TR (commAllK 4 G) := by
  rw [centralizerIn_R_permTwoA.1, card_inf_eq _ _ (fun x => ∀ j < 4, x * g j = g j * x)]
  · exact card_comm_eq crT_binds' crT_perm CRT.hl crT_chain' hG
  · intro x
    rw [mem_centralizer_closure_iff]
    constructor
    · intro h j hj
      exact h _ ((hT _).2 ⟨j, hj, rfl⟩)
    · intro h t ht
      obtain ⟨j, hj, rfl⟩ := (hT t).1 ht
      exact h j hj

@[expose] noncomputable def s0Chain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) s0Strong 4 (by decide) [0] (by decide)
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 4 4 noD)

theorem s0Base_eq : (([0] : List (Fin 315)).map Fin.val).toArray = s0Base := by decide

theorem s0_chain' : rawChainOK 315 (s0Strong.extract 0 4) s0Strong
    (([0] : List (Fin 315)).map Fin.val).toArray
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 4 4 noD) 4 = true := by
  rw [s0Base_eq]
  exact s0_chain.1

theorem rep_s0 {j : ℕ} (hj : j < 4) :
    Rep 315 (unpack 315 9 (S0C.S j)) (permOfArr 315 s0Strong[j]!) := by
  rw [← s0_binds.2.2.2.2.1 j hj]
  exact (rep_of_binds s0_binds s0_perm hj).1

theorem s0_zero : permOfArr 315 s0Strong[0]! = permTwoA := by
  rw [s0_binds.2.2.2.2.1 0 (by norm_num), ← arrBind_sound s0_z]
  rfl

theorem s0_gen_mem {j : ℕ}
    (hj : j < 4) : permOfArr 315 s0Strong[j]! ∈ centralizerIn P permTwoA := by
  have hg : ∀ i < 2, gC i ∈ centralizerIn P permTwoA := fun i hi => gC_mem hi
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rw [s0_zero]
    exact mem_centralizerIn.2 ⟨permTwoA_mem, rfl⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : i < 3 := by omega
    have e := (word_c2A (s0_words i hi)).unique (rep_s0 hj)
    rw [← e]
    refine sgnProd_mem hg _ ?_
    interval_cases i <;> decide

theorem s0_facts :
    ∃ S₀ : Subgroup (Equiv.Perm (Fin 315)), S₀ ≤ centralizerIn P permTwoA ∧
      Nat.card S₀ = 128 ∧ permTwoA ∈ S₀ ∧
      Nat.card ↥(centralizerIn R permTwoA ⊓
        centralizer (S₀ : Set (Equiv.Perm (Fin 315)))) = 2 := by
  refine ⟨s0Chain.originalSubgroup, ?_, ?_, ?_, ?_⟩
  · rw [s0Chain, ofArrays_originalSubgroup, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact s0_gen_mem hj
  · rw [s0Chain, ofArrays_card (by norm_num) s0_chain', s0Base_eq, s0_chain.2]
    rfl
  · rw [s0Chain, ofArrays_originalSubgroup, ← s0_zero]
    exact subset_closure ⟨0, by norm_num, rfl⟩
  · rw [s0Chain, ofArrays_originalSubgroup, card_cent_crT (G := S0C.S)
      (g := fun j => permOfArr 315 s0Strong[j]!) (fun t => ?_) (fun j hj => ⟨?_, rep_s0 hj⟩),
      s0_count]
    · simp only [Set.mem_setOf_eq]
      exact ⟨fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩, fun ⟨j, hj, h⟩ => ⟨j, hj, h.symm⟩⟩
    · exact CFSG.KS.PK.allN_iff.1 s0_canon j hj

@[expose] noncomputable def a5Chain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) a5Strong 2 (by decide) [0] (by decide)
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 2 noD)

theorem a5Base_eq : (([0] : List (Fin 315)).map Fin.val).toArray = a5Base := by decide

theorem a5_chain' : rawChainOK 315 (a5Strong.extract 0 2) a5Strong
    (([0] : List (Fin 315)).map Fin.val).toArray
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 2 noD) 4 = true := by
  rw [a5Base_eq]
  exact a5_chain.1

noncomputable abbrev gA (h : ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 a5Strong[h]!

theorem rep_a5 {j : ℕ} (hj : j < 2) : Rep 315 (unpack 315 9 (A5C.S j)) (gA j) := by
  rw [← a5_binds.2.2.2.2.1 j hj]
  exact (rep_of_binds a5_binds a5_perm hj).1

theorem gA_mem {j : ℕ} (hj : j < 2) : gA j ∈ a5Chain.originalSubgroup := by
  rw [a5Chain, ofArrays_originalSubgroup]
  exact subset_closure ⟨j, hj, rfl⟩

theorem a5_facts :
    ∃ G : Subgroup (Equiv.Perm (Fin 315)), G ≤ centralizerIn P permA ∧ Nat.card G = 60 ∧
      ⁅G, G⁆ = G := by
  refine ⟨a5Chain.originalSubgroup, ?_, ?_, ?_⟩
  · rw [a5Chain, ofArrays_originalSubgroup, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have e := (word_rep c2B_binds c2B_perm (a5_words j hj)).unique (rep_a5 hj)
    change gA j ∈ (centralizerIn P permA : Set _)
    rw [← e]
    refine sgnProd_mem (m := 2) (fun i hi => gB_mem hi) _ ?_
    interval_cases j <;> decide
  · rw [a5Chain, ofArrays_card (by norm_num) a5_chain', a5Base_eq, a5_chain.2]
    rfl
  · refine le_antisymm (Subgroup.commutator_le_self _) ?_
    conv_lhs => rw [a5Chain, ofArrays_originalSubgroup]
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have e := (word_rep a5_binds a5_perm (a5_comm j hj)).unique (rep_a5 hj)
    change gA j ∈ _
    rw [← e]
    have hmem : ∀ w : List ℕ, lettersOK 2 (posW w) = true →
        sgnProd gA (posW w) ∈ a5Chain.originalSubgroup :=
      fun w hw => sgnProd_mem (fun i hi => gA_mem hi) _ hw
    have hnz : ∀ w : List ℕ, (∀ l ∈ w, l ≠ 0) → ∀ l ∈ posW w, l ≠ 0 := by
      intro w hw l hl
      obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
      simpa using hw l' hl'
    interval_cases j
    · simp only [a5Comm, List.getD_cons_zero, sgnProd_append]
      rw [sgnProd_invW _ _ (hnz _ (by decide)), sgnProd_invW _ _ (hnz _ (by decide)),
        ← commutatorElement_def]
      exact commutator_mem_commutator (hmem _ (by decide)) (hmem _ (by decide))
    · simp only [a5Comm, List.getD_cons_succ, List.getD_cons_zero, sgnProd_append]
      rw [sgnProd_invW _ _ (hnz _ (by decide)), sgnProd_invW _ _ (hnz _ (by decide)),
        ← commutatorElement_def]
      exact commutator_mem_commutator (hmem _ (by decide)) (hmem _ (by decide))

theorem tp_eq {T : Table} {g : Equiv.Perm (Fin 315)} (h : CFSG.Sporadic.Th.Rep 315 T g) :
    tp 315 T = g :=
  CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (co2Rep_natArr_iff.2 h)

theorem rep_c2AGens {l : ℕ} (hl : 1 ≤ l ∧ l ≤ 2) :
    CFSG.Sporadic.Th.Rep 315 (c2AGens.getD (l - 1) (idT 315)) (gC (l - 1)) := by
  obtain rfl | rfl : l = 1 ∨ l = 2 := by omega
  · exact rep_arrTable (by norm_num) (rep_of_binds c2A_binds c2A_perm (j := 0) (by norm_num)).1
  · exact rep_arrTable (by norm_num) (rep_of_binds c2A_binds c2A_perm (j := 1) (by norm_num)).1

theorem rep_wordTbl_c2A : ∀ (w : List ℕ), (∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) → ∀ (acc : Table)
    (a : Equiv.Perm (Fin 315)), CFSG.Sporadic.Th.Rep 315 acc a →
    CFSG.Sporadic.Th.Rep 315 (w.foldl (fun acc l => compT 315 acc (c2AGens.getD (l - 1) (idT 315)))
      acc) (a * sgnProd gC (posW w))
  | [], _, acc, a, h => by simpa [posW] using h
  | l :: w, hw, acc, a, h => by
    rw [List.foldl_cons]
    have hl := hw l List.mem_cons_self
    have := rep_wordTbl_c2A w (fun l' hl' => hw l' (List.mem_cons_of_mem l hl')) _ _
      (CFSG.Sporadic.Th.Rep.compT h (rep_c2AGens hl))
    have e : posW (l :: w) = (l : ℤ) :: posW w := rfl
    rw [e, sgnProd_cons, if_pos (by omega)]
    simpa [mul_assoc] using this

theorem v_tp {i : ℕ} (hi : i < 4) :
    tp 315 (wordTbl 315 c2AGens (vWs.getD i [])) = permOfArr 315 vStrong[i]! := by
  have hw : ∀ l ∈ vWs.getD i [], 1 ≤ l ∧ l ≤ 2 := by
    interval_cases i <;> decide
  have h1 := rep_wordTbl_c2A _ hw (idT 315) 1 (CFSG.Sporadic.Th.Rep.idT (by norm_num))
  rw [one_mul] at h1
  have h2 : CFSG.Sporadic.Th.Rep 315 (wordTbl 315 c2AGens (vWs.getD i []))
      (sgnProd gC (posW (vWs.getD i []))) := h1
  rw [tp_eq h2]
  have e := word_c2A (v_words i hi)
  rw [← v_binds.2.2.2.2.1 i hi] at e
  exact e.unique (rep_of_binds v_binds v_perm hi).1

theorem v_facts :
    Nat.card ↥(centralizerIn R permTwoA ⊓ centralizer
      (genOf 315 (vWs.map (wordTbl 315 c2AGens)) : Set (Equiv.Perm (Fin 315)))) = 2 := by
  rw [genOf, card_cent_crT (G := VC.S) (g := fun j => permOfArr 315 vStrong[j]!) (fun t => ?_)
    (fun j hj => ⟨CFSG.KS.PK.allN_iff.1 v_canon j hj, ?_⟩), v_count]
  · constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_setOf_eq, List.mem_toArray, List.mem_map] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      simp only [vWs, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact ⟨0, by norm_num, v_tp (i := 0) (by norm_num)⟩
      · exact ⟨1, by norm_num, v_tp (i := 1) (by norm_num)⟩
      · exact ⟨2, by norm_num, v_tp (i := 2) (by norm_num)⟩
      · exact ⟨3, by norm_num, v_tp (i := 3) (by norm_num)⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨wordTbl 315 c2AGens (vWs.getD j []), ?_, v_tp hj⟩
      simp only [Set.mem_setOf_eq, List.mem_toArray, List.mem_map]
      refine ⟨vWs.getD j [], ?_, rfl⟩
      interval_cases j <;> simp [vWs]
  · rw [← v_binds.2.2.2.2.1 j hj]
    exact (rep_of_binds v_binds v_perm hj).1

end CertificateChecks.KernelJ2H
