module

public import CFSG.Sporadic.SmallOddCore.J2LocalCheck
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.Schreier.PairChain
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public meta import CFSG.Sporadic.SmallOddCore.J2LocalCheck
public meta import CFSG.Sporadic.Schreier.PairJ2Check
public import Certificates.Certificate2233
public import Certificates.Certificate2234
public import CFSG.Sporadic.SmallOddCore.J2CentralizerDInputs
public import Certificates.Certificate2277
public import Certificates.Certificate2280

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Certificates
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem j2_C1Gens_perm : ∀ g ∈ j2C1Gens, permOK 315 g = true := by
  have := j2_DOK
  simp only [j2DOK, Bool.and_eq_true, List.all_eq_true] at this
  exact this.1.1.1.1.1.1.2

theorem j2_DGens_perm : ∀ g ∈ j2DGens, permOK 315 g = true := by
  have := j2_DOK
  simp only [j2DOK, Bool.and_eq_true, List.all_eq_true] at this
  exact this.1.1.1.1.1.2

theorem j2_countCD :
    countW (commW 315 (j2DGens.map natArr)) PairJ2.blocks [] = 12 :=
  Certificates.certificate2277

theorem commW_iff {n : ℕ} {gs : List (Array ℕ)} {ds : List (Equiv.Perm (Fin n))}
    (hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep n) gs ds) {w : List (Array ℕ)}
    {g : Equiv.Perm (Fin n)} (hw : RepW n w g) :
    commW n gs w = true ↔ ∀ d ∈ ds, g * d = d * g := by
  induction hgs with
  | nil => simp [commW]
  | @cons a d gs ds had _ ih =>
    rw [commW, List.all_cons, Bool.and_eq_true, ← commW, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    refine and_congr ?_ Iff.rfl
    rw [CFSG.Monster.B.Co2.allLt_iff]
    constructor
    · intro h
      ext x
      have := h x x.2
      rw [beq_iff_eq] at this
      have e1 : a[(x : ℕ)]! = (d x : ℕ) := had x
      rw [e1] at this
      have e2 := hw (d x)
      have e3 := hw x
      rw [e2, e3, had (g x)] at this
      simpa using this
    · intro h i hi
      rw [beq_iff_eq]
      have e1 : a[i]! = (d ⟨i, hi⟩ : ℕ) := had ⟨i, hi⟩
      rw [e1, hw (d ⟨i, hi⟩), show evR w i = (g ⟨i, hi⟩ : ℕ) from hw ⟨i, hi⟩, had (g ⟨i, hi⟩)]
      have := congrArg (fun f : Equiv.Perm (Fin n) => (f ⟨i, hi⟩ : ℕ)) h
      simpa using this

theorem j2_card_centralizer_D :
    Nat.card ↥(j2P ⊓ centralizer (genOf 315 j2DGens : Set (Equiv.Perm (Fin 315)))) = 12 := by
  classical
  have hDp := j2_DGens_perm
  have hgs : List.Forall₂ (CFSG.Monster.B.Co2.Rep 315) (j2DGens.map natArr)
      (j2DGens.map (tp 315)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun g hg =>
      co2Rep_natArr_iff.2 (rep_tp (hDp g hg))
  have hcount := card_eq_countW (f := commW 315 (j2DGens.map natArr))
    (Pr := fun g => ∀ d ∈ j2DGens.map (tp 315), g * d = d * g) j2ChainArrays (by norm_num)
    PairJ2.chain_check.1 j2_groups (fun w g hw _ => commW_iff hgs hw)
  rw [show blocksOf 315 (rawLevels 315 j2StrongArrs PairJ2.baseArr) PairJ2.groups =
    PairJ2.blocks from rfl, j2_countCD, ← j2P_eq_original] at hcount
  have hcent : ∀ y : Equiv.Perm (Fin 315),
      y ∈ centralizer (genOf 315 j2DGens : Set (Equiv.Perm (Fin 315))) ↔
        ∀ d ∈ j2DGens.map (tp 315), y * d = d * y := by
    intro y
    rw [centralizer_closure, mem_centralizer_iff]
    constructor
    · intro h d hd
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hd
      exact (h _ ⟨g, by simpa using hg, rfl⟩).symm
    · rintro h _ ⟨g, hg, rfl⟩
      exact (h _ (List.mem_map.mpr ⟨g, by simpa using hg, rfl⟩)).symm
  rw [← hcount]
  exact Nat.card_congr ⟨fun x => ⟨⟨x.1, (mem_inf.mp x.2).1⟩, (hcent _).1 (mem_inf.mp x.2).2⟩,
    fun x => ⟨x.1.1, mem_inf.mpr ⟨x.1.2, (hcent _).2 x.2⟩⟩, fun _ => rfl, fun _ => rfl⟩

end CFSG.Sporadic.SmallOddCore
