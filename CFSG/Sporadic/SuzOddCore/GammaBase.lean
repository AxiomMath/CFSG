module

public import CFSG.Sporadic.SuzOddCore.CertChain
public import CFSG.Sporadic.FischerOddCore.RefineSpec
public import CFSG.Sporadic.SuzOddCore.GammaStageInputs
public import CFSG.Sporadic.SuzOddCore.GraphPerms

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native

theorem rep_powArr {n : ℕ} {t : Array ℕ} {T : Equiv.Perm (Fin n)} (ht : Rep n t T) :
    ∀ k, Rep n (powArr n t k) (T ^ k)
  | 0 => by rw [pow_zero]; exact rep_idA
  | k + 1 => by rw [pow_succ']; exact rep_compA ht (rep_powArr ht k)

theorem rep_strongWord {w : List ℤ} (hw : lettersOK 10 w = true) :
    Rep 22880 (wordA 22880 certStrongArrs certStrongInvs w) (strongWord w) :=
  rep_wordA (fun _ hh => rep_certStrong (by omega)) (fun _ hh => rep_certStrongInv (by omega)) w hw

theorem rep_zArr :
    Rep 22880 zArr suzZ :=
  rep_powArr (rep_strongWord graphArrays_check.2.2.2.2.2.2.2.2.1) _

theorem mem_deltaOf
    (i : Fin 22880) : (i : ℕ) ∈ deltaOf zArr ↔ i ∈ suzDeltaΩ := by
  rw [deltaOf, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, beq_iff_eq,
    rep_zArr i]
  simp only [suzDeltaΩ, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, h0, hz⟩
    exact ⟨Fin.ext hz, fun h => h0 (by rw [h]; rfl)⟩
  · rintro ⟨hz, h0⟩
    exact ⟨i.2, fun h => h0 (Fin.ext h), by rw [hz]⟩

@[expose] def certGs (k : ℕ) : Equiv.Perm (Fin 22880) := if k = 0 then suzA0 else suzA1

theorem rep_certPair
    {k : ℕ} (hk : k < (#[certArr 0, certArr 1] : Array (Array ℕ)).size) :
    Rep 22880 (#[certArr 0, certArr 1] : Array (Array ℕ))[k]! (certGs k) := by
  have hk2 : k < 2 := hk
  interval_cases k
  · exact rep_suzA0
  · exact rep_suzA1

theorem suzP_eq_closure_gens :
    suzP = Subgroup.closure
      {g | ∃ k < (#[certArr 0, certArr 1] : Array (Array ℕ)).size, certGs k = g} := by
  rw [suzP]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.size_toArray,
    List.length_cons, List.length_nil]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · left; rfl
    · right; rfl

theorem suzP_exists_smul
    (x y : Fin 22880) : ∃ g ∈ suzP, g x = y := by
  have := suzP_isPreprimitive.toIsPretransitive
  obtain ⟨⟨g, hg⟩, h⟩ := MulAction.exists_smul_eq suzP x y
  exact ⟨g, hg, h⟩

theorem replicate_getElem! {i : ℕ} (hi : i < 22880) : (Array.replicate 22880 1)[i]! = 1 := by
  rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_replicate]

@[expose] def gammaWordPerm (w : List ℕ) : Equiv.Perm (Fin 22880) :=
  w.foldr (fun k U => certGs k * U) 1

theorem rep_certGs {k : ℕ} (hk : k < 2) :
    Rep 22880 (certArr k) (certGs k) := by
  interval_cases k
  · have e : certGs 0 = suzA0 := if_pos rfl
    rw [e]
    exact rep_suzA0
  · have e : certGs 1 = suzA1 := if_neg (by norm_num)
    rw [e]
    exact rep_suzA1

theorem rep_foldr_certArr :
    ∀ w : List ℕ, (∀ k ∈ w, k < 2) →
      Rep 22880 (w.foldr (fun k u => compA 22880 (certArr k) u) (idA 22880))
        (w.foldr (fun k U => certGs k * U) 1)
  | [], _ => by
    rw [List.foldr_nil, List.foldr_nil]
    exact rep_idA
  | k :: w, hw => by
    rw [List.foldr_cons, List.foldr_cons]
    exact rep_compA (rep_certGs (hw k List.mem_cons_self))
      (rep_foldr_certArr w fun j hj => hw j (List.mem_cons_of_mem _ hj))

theorem rep_gammaWordArr (w : List ℕ) (hw : ∀ k ∈ w, k < 2) :
    Rep 22880 (gammaWordArr w) (gammaWordPerm w) := by
  unfold gammaWordArr gammaWordPerm
  exact rep_foldr_certArr w hw

theorem gammaWordPerm_mem : ∀ w : List ℕ, gammaWordPerm w ∈ suzP
  | [] => suzP.one_mem
  | k :: w => by
    change certGs k * gammaWordPerm w ∈ suzP
    refine suzP.mul_mem ?_ (gammaWordPerm_mem w)
    unfold certGs
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem gammaWords_lt {s : ℕ} (hs : s < 4) : ∀ k ∈ gammaWords.getD s [], k < 2 := by
  interval_cases s <;> decide

theorem gammaBaseCol_map {c u e : Array ℕ} {σ : Equiv.Perm (Fin 22880)}
    (hc : ColMap 22880 c c σ)
    (hue : ∀ v : Fin 22880, e[u[((σ v : Fin 22880) : ℕ)]!]! = e[u[(v : ℕ)]!]!) :
    ColMap 22880 (gammaBaseCol c u e) (gammaBaseCol c u e) σ := by
  intro v
  rw [gammaBaseCol, getElem!_ofFn_nat _ (σ v).2, getElem!_ofFn_nat _ v.2]
  simp only
  rw [hc v, hue v]

end CFSG.Sporadic.SuzOddCore
