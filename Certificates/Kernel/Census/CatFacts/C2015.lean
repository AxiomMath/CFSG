
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallArrChecks
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public meta import CFSG.GH74.KGroups.Checks3
public import Certificates.Data.Kernel.Census.CatFacts.C2015Scan
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound
import CFSG.Certificates.Kernel.Census.CatFacts.ArrPerm
import CFSG.Certificates.Kernel.Census.CatFacts.FixFive
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
import Certificates.Kernel.Census.CatFacts.C2015K
import Certificates.Kernel.Census.CatFacts.C2015W
import Certificates.Kernel.Census.CatFacts.C2015Fpf
import Certificates.Kernel.Census.CatFacts.C2015G0
import Certificates.Kernel.Census.CatFacts.C2015G1
import Certificates.Kernel.Census.CatFacts.C2015G2
import Certificates.Kernel.Census.CatFacts.C2015G3
import Certificates.Kernel.Census.CatFacts.C2015G4

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.CatFacts CFSG.Sporadic.Schreier CFSG.Certificates

local notation "P45" => Equiv.Perm (Fin 45)

theorem pkpW_powW {n : Nat} (u : List (VP n)) (k : Nat) : pkpW (powW u k) = pkpW u ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powW, pkpW_append, ih, pow_succ']

theorem pkp_prodW {n : Nat} (w : List (VP n)) : pkp (prodW w) = pkpW w := by
  induction w with
  | nil => exact pkp_oneV n
  | cons a w ih => rw [prodW, List.foldr_cons, ← prodW, pkp_mulV, ih, pkpW_cons]

theorem pkp_cubeV {n : Nat} (u : VP n) : pkp (cubeV u) = pkp u ^ 3 := by
  rw [cubeV, forceV_eq, pkp_mulV, pkp_mulV, pow_succ', pow_succ', pow_one]

theorem pkp_pow45 {n : Nat} (u : VP n) : pkp (pow45 u) = pkp u ^ 45 := by
  rw [pow45, forceV_eq, pkp_mulV, pkp_mulV, pkp_mulV, pkp_mulV, pkp_cubeV, pkp_cubeV,
    show 45 = 3 * 3 * 5 by rfl, pow_mul, pow_mul]
  generalize (pkp u ^ 3) ^ 3 = d
  rw [pow_succ', pow_succ', pow_succ', pow_succ', pow_one]

theorem pkp_pow405 {n : Nat} (u : VP n) : pkp (pow405 u) = pkp u ^ 405 := by
  rw [pow405, pkp_cubeV, pkp_cubeV, pkp_pow45, ← pow_mul, ← pow_mul]

theorem isOneW_single {n : Nat} (v : VP n) : isOneW [v] = decide (pkp v = 1) := by
  rw [isOneW_eq, pkpW_single]

theorem force15_eq {β : Sort _} (k : C15 → List (List (VP 45)) → β) :
    force15 k = k c15 (odd3W c15.tP) := by
  unfold force15
  simp only [forceLL_eq, forceLv_eq, forceV_eq]

theorem cnt2015_eq : cnt2015 = (((transL QA45).headD []).length,
    ((transL QP45).headD []).length,
    ((List.range 45).map fun j =>
      ((blockW (transL QA45) j).filter fun w => eqW (w ++ [codeV s045]) (codeV s045 :: w)).length).sum,
    ((List.range 45).map fun j =>
      ((blockW (transL QP45) j).filter fun w => eqW (w ++ [codeV s045]) (codeV s045 :: w)).length).sum) := by
  unfold cnt2015
  simp only [forceLL_eq, forceV_eq]
  rfl

theorem eqW_comm_eq (x s : List (VP 45)) :
    eqW (x ++ s) (s ++ x) = decide (pkpW x * pkpW s = pkpW s * pkpW x) := by
  rw [eqW_eq, pkpW_append, pkpW_append]

theorem pairWitness_of_pairW {C : List (List (VP 45))} {D : List P45}
    (hCD : ∀ x ∈ C, pkpW x ∈ D) (h : pairW C = true) : pairWitness D 405 = true := by
  unfold pairW at h
  unfold pairWitness
  rw [List.any_eq_true] at h ⊢
  obtain ⟨x₁, hx₁, h⟩ := h
  rw [List.any_eq_true] at h
  obtain ⟨x₂, hx₂, h⟩ := h
  refine ⟨pkpW x₁, hCD x₁ hx₁, ?_⟩
  rw [List.any_eq_true]
  refine ⟨pkpW x₂, hCD x₂ hx₂, ?_⟩
  rwa [isOneW_single, pkp_pow405, pkp_codeV, pkpW_append] at h

theorem mem_elemsT_P {x : List (VP 45)} (hx : x ∈ productsW c15.tP) : pkpW x ∈ elemsT QP45 := by
  rw [elemsT_eq_W]
  exact List.mem_map_of_mem hx

theorem fpf_of_five {x : P45} (hx : x ∈ elemsT QP45) (h5 : x ^ 5 = 1) (h1 : x ≠ 1) (j : Fin 45) :
    x j ≠ j := by
  have h := fpf2015K
  unfold fpf2015 at h
  rw [forceLL_eq, List.all_eq_true] at h
  rw [elemsT_eq_W, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have h2 := h w hw
  rw [isOneW_eq, isOneW_eq, pkpW_powW, h5] at h2
  simp only [decide_true, decide_eq_true_eq, h1, decide_false, Bool.not_false, Bool.and_true,
    Bool.not_true, Bool.false_or] at h2
  have h3 := (range_all_iff _).1 h2 j
  rw [imgW_eq, bne_iff_ne, ne_eq] at h3
  intro h4
  exact h3 (by rw [h4])

theorem not_comm_five {s : P45}
    (hs : (Finset.univ.filter fun j : Fin 45 => s j = j).card % 5 ≠ 0) :
    ((elemsT QP45).filter (fun x => decide (x ^ 5 = 1) && !decide (x = 1))).all
      (fun x => !(decide (x * s = s * x))) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hx
  rw [Bool.not_eq_true', decide_eq_false_iff_not]
  intro hc
  exact hs (fix_card_mod_five hx.2.1 (fpf_of_five hx.1 hx.2.1 hx.2.2) hc)

theorem conj_of_cj {s : List (VP 45)} (h : (c15.cj.any fun c => eqW c s) = true) :
    (admConj.any fun k => decide (k * s045 * k⁻¹ = pkpW s)) = true := by
  rw [List.any_eq_true] at h ⊢
  obtain ⟨c, hc, h⟩ := h
  have hc' : c ∈ admWords.map fun w => codesW gXYF w ++ codeV s045 :: invW (codesW gXYF w) := hc
  rw [List.mem_map] at hc'
  obtain ⟨w, hw, rfl⟩ := hc'
  refine ⟨tab (evalCodes [tab x45, tab y45, tab f45] w), List.mem_map_of_mem hw, ?_⟩
  rw [eqW_eq, decide_eq_true_eq, pkpW_append, pkpW_cons, pkpW_invW] at h
  have hg : pkpW (codesW gXYF w) = evalCodes [tab x45, tab y45, tab f45] w :=
    pkpW_codesW [tab x45, tab y45, tab f45] w
  rw [hg, pkp_codeV] at h
  rw [tab_eq, decide_eq_true_eq, ← h, mul_assoc]

theorem t15_sound {s : List (VP 45)} (h : t15 c15 (odd3W c15.tP) s = true) :
    (!(decide (pkpW s * pkpW s = 1)) || pairWitness (((elemsT QP45).filter
        fun x => decide (x ^ 9 = 1) || decide (x ^ 5 = 1)).filter
          fun x => decide (x * pkpW s = pkpW s * x)) 405) = true ∧
    (!(decide (pkpW s * pkpW s = 1)) || QP45.sift (pkpW s) 0 ||
      (admConj.any fun k => decide (k * s045 * k⁻¹ = pkpW s)) ||
      ((elemsT QP45).filter (fun x => decide (x ^ 5 = 1) && !decide (x = 1))).all
        fun x => !(decide (x * pkpW s = pkpW s * x))) = true := by
  unfold t15 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hss : isOneW (s ++ s) = decide (pkpW s * pkpW s = 1) := by rw [isOneW_eq, pkpW_append]
  rw [hss] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [Bool.or_eq_true] at h1 ⊢
    refine h1.imp id fun hp => pairWitness_of_pairW (fun x hx => ?_) hp
    rw [List.mem_filter] at hx ⊢
    obtain ⟨hx, hc⟩ := hx
    unfold odd3W at hx
    rw [List.mem_filter, Bool.and_eq_true, isOneW_eq, decide_eq_true_eq, pkpW_powW] at hx
    rw [eqW_comm_eq] at hc
    refine ⟨List.mem_filter.2 ⟨mem_elemsT_P hx.1, ?_⟩, hc⟩
    rw [Bool.or_eq_true, decide_eq_true_eq]
    left
    rw [show 9 = 3 * 3 by rfl, pow_mul, hx.2.1, one_pow]
  · have hs : siftW c15.lP s = QP45.sift (pkpW s) 0 := (sift_pkpW QP45 s 0).symm
    rw [hs] at h2
    simp only [Bool.or_eq_true] at h2 ⊢
    rcases h2 with ((h2 | h2) | h2) | h2
    · exact Or.inl (Or.inl (Or.inl h2))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr (conj_of_cj h2))
    · refine Or.inr (not_comm_five ?_)
      rw [bne_iff_ne] at h2
      exact h2

theorem blocks2015 {p : P45 → Bool}
    (h : ∀ w : List (VP 45), t15 c15 (odd3W c15.tP) w = true → p (pkpW w) = true) :
    (elemsT QA45).all p = true := by
  refine elemsT_all_of_blocks QA45 (by decide) p fun j hj => ?_
  have hn : ((transL QA45).headD []).length = 45 := by
    have := cnt2015K
    rw [cnt2015_eq] at this
    exact (Prod.mk.inj this).1
  rw [hn] at hj
  have hg : ∀ g < 5, grp2015 g = true := by
    intro g hg
    interval_cases g
    · exact grp20150
    · exact grp20151
    · exact grp20152
    · exact grp20153
    · exact grp20154
  have h1 := hg (j / 9) (by omega)
  unfold grp2015 at h1
  rw [force15_eq, List.all_eq_true] at h1
  have h2 := h1 (j % 9) (List.mem_range.2 (Nat.mod_lt _ (by omega)))
  rw [show 9 * (j / 9) + j % 9 = j by omega] at h2
  rw [List.all_eq_true] at h2 ⊢
  exact fun w hw => h w (h2 w hw)

theorem noNilp2015 : noNilpA 45 (enumA QA45) ((enumA QP45).filter oddTestA) 405 = true := by
  have hodd : (enumA QP45).filter oddTestA =
      ((elemsT QP45).filter fun x => decide (x ^ 9 = 1) || decide (x ^ 5 = 1)).map toA := by
    rw [enumA_eq]
    exact filter_toA_pow2 _ 9 5
  rw [hodd, enumA_eq, noNilpA_map]
  unfold noNilpCheck
  apply blocks2015
  intro w hw
  exact (t15_sound hw).1

theorem adm2015 : admCheckA (elemsTab QA45) QP45 five45A s045 admConj = true := by
  have h5 : five45A = ((elemsT QP45).filter
      fun x => decide (x ^ 5 = 1) && !decide (x = 1)).map toA := by
    unfold five45A
    rw [enumA_eq, filter_toA_pow]
  rw [elemsTab_eq, h5, admCheckA_map]
  unfold admCheck
  apply blocks2015
  intro w hw
  exact (t15_sound hw).2

theorem count2015 (Q : RawSchreierDatum 45) (hk : 1 ≤ Q.baseCount)
    (hn : ((transL Q).headD []).length = 45) :
    ((elemsT Q).filter fun g => decide (g * s045 = s045 * g)).length =
      ((List.range 45).map fun j =>
        ((blockW (transL Q) j).filter fun w => eqW (w ++ [codeV s045]) (codeV s045 :: w)).length).sum := by
  rw [elemsT_count_blocks Q hk, hn]
  congr 1
  apply List.map_congr_left
  intro j _
  congr 1
  apply List.filter_congr
  intro w _
  rw [eqW_eq, pkpW_append, pkpW_single, pkpW_cons, pkp_codeV]

theorem oddNormal2015 : oddNormalCheck (elemsT QL45) 45 = true := by
  have h := oddN2015K
  unfold oddNW at h
  rw [forceLL_eq] at h
  unfold oddNormalCheck
  rw [elemsT_eq_W, List.all_map]
  refine List.all_eq_true.2 fun x hx => ?_
  have h1 := List.all_eq_true.1 h x hx
  simp only [isOneW_eq, pkpW_single, pkp_pow45, pkp_prodW, pkpW_append, pkpW_invW] at h1
  simpa only [Function.comp_def, List.any_map] using h1

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.KGroups.Native CFSG.GH74.KGroups.NativeChecks in
theorem facts2015 : (noNilpA 45 (enumA QA45) ((enumA QP45).filter oddTestA) 405 = true)
    ∧ (admCheckA (elemsTab QA45) QP45 five45A s045 admConj = true)
    ∧ (QA45.sift s045 0 = true)
    ∧ (QL45.check = true ∧ QL45.orderCertificate = 360)
    ∧ (oddNormalCheck (elemsT QL45) 45 = true)
    ∧ (((elemsT QP45).filter (fun g => decide (g * s045 = s045 * g))).length = 720)
    ∧ (QP45.sift la1 0 = true ∧ QP45.sift lb1 0 = true ∧ QP45.sift lb2 0 = true ∧
      la1 * s045 = s045 * la1 ∧ lb1 * s045 = s045 * lb1 ∧ lb2 * s045 = s045 * lb2
    )
    ∧ (QQ45.check = true ∧ QQ45.orderCertificate = 32)
    ∧ ((elemsT QQ45).all (fun q => QQ45.sift (g045 * q * g045⁻¹) 0) = true ∧
      QQ45.sift g045 0 = false ∧ QQ45.sift (g045 * g045) 0 = true ∧ QP45.sift g045 0 = true ∧
      QP45.sift (s045 * (g045⁻¹ * s045 * g045)) 0 = true ∧
      (q0gens.all fun q => QA45.sift q 0 && decide (q * s045 = s045 * q)) = true
    )
    ∧ (((elemsT QA45).filter (fun g => decide (g * s045 = s045 * g))).length = 2 ^ 5 * 45) := by
  have hc := cnt2015K
  rw [cnt2015_eq] at hc
  simp only [Prod.mk.injEq] at hc
  obtain ⟨hA, hP, cA, cP⟩ := hc
  refine ⟨noNilp2015, adm2015, by rw [sift_eq_siftP]; exact s0452015K, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · exact ⟨check_certificate_of _ _ _ _ _ ql452015K.1,
      (orderCertificate_eq_orderV _).trans ql452015K.2⟩
  · exact oddNormal2015
  · rw [count2015 QP45 (by decide) hP]
    exact cP
  · simp only [sift_eq_siftP]
    exact la2015K
  · exact ⟨check_certificate_of _ _ _ _ _ qq452015K.1,
      (orderCertificate_eq_orderV _).trans qq452015K.2⟩
  · simp only [elemsT_eq_elemsV, sift_eq_siftP]
    exact g0452015K
  · rw [count2015 QA45 (by decide) hA]
    exact cA

end CertificateChecks.KernelCatFacts
