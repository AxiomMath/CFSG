
module

public import Certificates.Data.Kernel.Census.CatFacts.C2015Lit
import CFSG.Certificates.Kernel.Census.CatFacts.PkWordSound

public section

set_option maxHeartbeats 0

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.Certificates.Kernel.PkEnum

local notation "V45" => VP 45

@[expose] def pickW {n : Nat} : List (List (VP n)) → List Nat → Option (List (VP n))
  | [], [] => some []
  | T :: Ts, i :: is => T[i]?.bind fun t => (pickW Ts is).map (t :: ·)
  | _, _ => none

theorem pickW_mem {n : Nat} : ∀ (Ts : List (List (VP n))) (is : List Nat) (w : List (VP n)),
    pickW Ts is = some w → w ∈ productsW Ts
  | [], [], w, h => by
    simp only [pickW, Option.some.injEq] at h
    subst h
    simp [productsW]
  | [], _ :: _, _, h => by simp [pickW] at h
  | _ :: _, [], _, h => by simp [pickW] at h
  | T :: Ts, i :: is, w, h => by
    simp only [pickW, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, w', hw', rfl⟩ := h
    simp only [productsW, List.mem_flatMap, List.mem_map]
    exact ⟨t, List.mem_of_getElem? ht, w', pickW_mem Ts is w' hw', rfl⟩

@[expose] def t15W (C : C15) (a b : List Nat) (s : List V45) : Bool :=
  (match pickW C.tP a, pickW C.tP b with
    | some x₁, some x₂ =>
      (isOneW (powW x₁ 3) && !isOneW x₁) && eqW (x₁ ++ s) (s ++ x₁) &&
        ((isOneW (powW x₂ 3) && !isOneW x₂) && eqW (x₂ ++ s) (s ++ x₂)) &&
        !isOneW [pow405 (codeV (pkpW (x₁ ++ x₂)))]
    | _, _ => false) &&
  (siftW C.lP s || (C.cj.any fun c => eqW c s) ||
    (Finset.univ.filter fun j : Fin 45 => pkpW s j = j).card % 5 != 0)

@[expose] def scan2015W (C : C15) : List (List Nat × List Nat) → List (List V45) → Bool
  | _, [] => true
  | ws, s :: l => match isOneW (s ++ s), ws with
    | false, ws => scan2015W C ws l
    | true, [] => false
    | true, p :: ws => t15W C p.1 p.2 s && scan2015W C ws l

theorem t15_of_t15W {C : C15} {a b : List Nat} {s : List V45} (h : t15W C a b s = true) :
    t15 C (odd3W C.tP) s = true := by
  unfold t15W at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  split at h1
  · rename_i x₁ x₂ hx₁ hx₂
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨⟨⟨p1, p2⟩, p3⟩, ⟨p4, p5⟩, p6⟩, p7⟩ := h1
    have m1 : x₁ ∈ odd3W C.tP :=
      List.mem_filter.2 ⟨pickW_mem _ _ _ hx₁, Bool.and_eq_true _ _ ▸ ⟨p1, p2⟩⟩
    have m2 : x₂ ∈ odd3W C.tP :=
      List.mem_filter.2 ⟨pickW_mem _ _ _ hx₂, Bool.and_eq_true _ _ ▸ ⟨p4, p5⟩⟩
    have hpw : pairW ((odd3W C.tP).filter fun x => eqW (x ++ s) (s ++ x)) = true := by
      unfold pairW
      exact List.any_eq_true.2 ⟨x₁, List.mem_filter.2 ⟨m1, p3⟩,
        List.any_eq_true.2 ⟨x₂, List.mem_filter.2 ⟨m2, p6⟩, p7⟩⟩
    unfold t15
    rw [hpw, Bool.or_true, Bool.true_and]
    simp only [Bool.or_eq_true] at h2 ⊢
    rcases h2 with (h2 | h2) | h2
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inr h2)
    · exact Or.inr h2
  · exact absurd h1 Bool.false_ne_true

theorem scan2015W_sound (C : C15) : ∀ (ws : List (List Nat × List Nat)) (l : List (List V45)),
    scan2015W C ws l = true → l.all (t15 C (odd3W C.tP)) = true
  | _, [], _ => rfl
  | ws, s :: l, h => by
    rw [List.all_cons, Bool.and_eq_true]
    cases hs : isOneW (s ++ s)
    · simp only [scan2015W, hs] at h
      refine ⟨?_, scan2015W_sound C ws l h⟩
      unfold t15
      rw [hs]
      rfl
    · cases ws with
      | nil => simp [scan2015W, hs] at h
      | cons p ws =>
        simp only [scan2015W, hs, Bool.and_eq_true] at h
        exact ⟨t15_of_t15W h.1, scan2015W_sound C ws l h.2⟩

theorem all2015_take_drop {α : Type*} {p : α → Bool} {l : List α} (k : Nat)
    (h₁ : (l.take k).all p = true) (h₂ : (l.drop k).all p = true) : l.all p = true := by
  rw [← List.take_append_drop k l, List.all_append, h₁, h₂]
  rfl

deriving instance DecidableEq for StV

@[expose] def c2015L : C15 := ⟨lit2015A, lit2015P, lit2015L, lit2015S, lit2015C⟩

theorem lit2015A_eq : c15.tA = lit2015A := by
  decide +kernel

theorem lit2015L_eq : c15.lP = lit2015L := by
  decide +kernel

theorem transL_eq_levelsV {n : Nat} (Q : RawSchreierDatum n) :
    transL Q = (levelsV (strongV Q) Q.base 0).map fun e => transV e.2 := by
  unfold transL levelsV
  rw [List.drop_zero, List.map_map]
  rfl

theorem lit2015P_eq : c15.tP = lit2015P := by
  have h : c15.tP = c15.lP.map fun e => transV e.2 := transL_eq_levelsV _
  rw [h, lit2015L_eq]
  decide +kernel

theorem lit2015S_eq : c15.s0 = lit2015S := by
  decide +kernel

theorem lit2015C_eq : c15.cj = lit2015C := by
  decide +kernel

theorem grp2015_L (g : Nat) : grp2015 g = (List.range 9).all fun i =>
    (blockW c2015L.tA (9 * g + i)).all (t15 c2015L (odd3W c2015L.tP)) := by
  unfold grp2015 force15
  simp only [forceLL_eq, forceLv_eq, forceV_eq]
  rw [lit2015A_eq, lit2015P_eq, lit2015L_eq, lit2015S_eq, lit2015C_eq]
  rfl

end CFSG.Certificates.Kernel.CatFacts
