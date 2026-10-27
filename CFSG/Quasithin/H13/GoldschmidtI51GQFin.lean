module

public import CFSG.Quasithin.H13.Sp62S6Over
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.GoldschmidtI51GQFinK

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Quasithin.H13.A6 Equiv

@[expose] def InR (b : Bool) (σ : Perm (Fin 6)) : Prop := b = false ∨ Perm.sign σ = 1

instance (b : Bool) : DecidablePred (InR b) := fun σ => by unfold InR; infer_instance

@[expose] def InA (o : Bool) (σ : Perm (Fin 6)) : Prop := if o then InP1 σ else InP2 σ

@[expose] def InB (o : Bool) (σ : Perm (Fin 6)) : Prop := if o then InP2 σ else InP1 σ

instance (o : Bool) : DecidablePred (InA o) := fun σ => by unfold InA; infer_instance

instance (o : Bool) : DecidablePred (InB o) := fun σ => by unfold InB; infer_instance

@[expose] def nn (o : Bool) : Perm (Fin 6) :=
  if o then swap 0 4 * swap 1 5 else swap 0 2 * swap 4 5

@[expose] def ff (o : Bool) : Perm (Fin 6) :=
  if o then swap 3 4 * swap 0 1 else swap 1 2 * swap 3 4

@[expose] def sw (i j : ℕ) : Perm (Fin 6) := swap (Fin.ofNat 6 i) (Fin.ofNat 6 j)

@[expose] def pw (l : List (ℕ × ℕ)) : Perm (Fin 6) := (l.map fun p => sw p.1 p.2).prod

def LP1w : List (List (ℕ × ℕ)) :=
  [[],
   [(4,5)],
   [(2,3)],
   [(2,3),(4,5)],
   [(1,2)],
   [(1,2),(4,5)],
   [(1,2),(2,3)],
   [(1,2),(2,3),(4,5)],
   [(1,3),(3,2)],
   [(1,3),(3,2),(4,5)],
   [(1,3)],
   [(1,3),(4,5)],
   [(0,1)],
   [(0,1),(4,5)],
   [(0,1),(2,3)],
   [(0,1),(2,3),(4,5)],
   [(0,1),(1,2)],
   [(0,1),(1,2),(4,5)],
   [(0,1),(1,2),(2,3)],
   [(0,1),(1,2),(2,3),(4,5)],
   [(0,1),(1,3),(3,2)],
   [(0,1),(1,3),(3,2),(4,5)],
   [(0,1),(1,3)],
   [(0,1),(1,3),(4,5)],
   [(0,2),(2,1)],
   [(0,2),(2,1),(4,5)],
   [(0,2),(2,3),(3,1)],
   [(0,2),(2,3),(3,1),(4,5)],
   [(0,2)],
   [(0,2),(4,5)],
   [(0,2),(2,3)],
   [(0,2),(2,3),(4,5)],
   [(0,2),(1,3)],
   [(0,2),(1,3),(4,5)],
   [(0,2),(2,1),(1,3)],
   [(0,2),(2,1),(1,3),(4,5)],
   [(0,3),(3,2),(2,1)],
   [(0,3),(3,2),(2,1),(4,5)],
   [(0,3),(3,1)],
   [(0,3),(3,1),(4,5)],
   [(0,3),(3,2)],
   [(0,3),(3,2),(4,5)],
   [(0,3)],
   [(0,3),(4,5)],
   [(0,3),(3,1),(1,2)],
   [(0,3),(3,1),(1,2),(4,5)],
   [(0,3),(1,2)],
   [(0,3),(1,2),(4,5)]]

def LP2w : List (List (ℕ × ℕ)) :=
  [[],
   [(4,5)],
   [(2,3)],
   [(2,3),(4,5)],
   [(2,4),(3,5)],
   [(2,4),(4,3),(3,5)],
   [(2,5),(5,3),(3,4)],
   [(2,5),(3,4)],
   [(0,1)],
   [(0,1),(4,5)],
   [(0,1),(2,3)],
   [(0,1),(2,3),(4,5)],
   [(0,1),(2,4),(3,5)],
   [(0,1),(2,4),(4,3),(3,5)],
   [(0,1),(2,5),(5,3),(3,4)],
   [(0,1),(2,5),(3,4)],
   [(0,2),(1,3)],
   [(0,2),(1,3),(4,5)],
   [(0,2),(2,1),(1,3)],
   [(0,2),(2,1),(1,3),(4,5)],
   [(0,2),(2,4),(1,3),(3,5)],
   [(0,2),(2,4),(4,1),(1,3),(3,5)],
   [(0,2),(2,5),(5,1),(1,3),(3,4)],
   [(0,2),(2,5),(1,3),(3,4)],
   [(0,3),(3,1),(1,2)],
   [(0,3),(3,1),(1,2),(4,5)],
   [(0,3),(1,2)],
   [(0,3),(1,2),(4,5)],
   [(0,3),(3,5),(5,1),(1,2),(2,4)],
   [(0,3),(3,5),(1,2),(2,4)],
   [(0,3),(3,4),(1,2),(2,5)],
   [(0,3),(3,4),(4,1),(1,2),(2,5)],
   [(0,4),(4,2),(1,5),(5,3)],
   [(0,4),(4,3),(3,1),(1,5),(5,2)],
   [(0,4),(4,2),(2,1),(1,5),(5,3)],
   [(0,4),(4,3),(1,5),(5,2)],
   [(0,4),(1,5)],
   [(0,4),(4,1),(1,5)],
   [(0,4),(1,5),(2,3)],
   [(0,4),(4,1),(1,5),(2,3)],
   [(0,5),(5,3),(3,1),(1,4),(4,2)],
   [(0,5),(5,2),(1,4),(4,3)],
   [(0,5),(5,3),(1,4),(4,2)],
   [(0,5),(5,2),(2,1),(1,4),(4,3)],
   [(0,5),(5,1),(1,4)],
   [(0,5),(1,4)],
   [(0,5),(5,1),(1,4),(2,3)],
   [(0,5),(1,4),(2,3)]]

def LP1aw : List (List (ℕ × ℕ)) :=
  [[],
   [(2,3),(4,5)],
   [(1,2),(4,5)],
   [(1,2),(2,3)],
   [(1,3),(3,2)],
   [(1,3),(4,5)],
   [(0,1),(4,5)],
   [(0,1),(2,3)],
   [(0,1),(1,2)],
   [(0,1),(1,2),(2,3),(4,5)],
   [(0,1),(1,3),(3,2),(4,5)],
   [(0,1),(1,3)],
   [(0,2),(2,1)],
   [(0,2),(2,3),(3,1),(4,5)],
   [(0,2),(4,5)],
   [(0,2),(2,3)],
   [(0,2),(1,3)],
   [(0,2),(2,1),(1,3),(4,5)],
   [(0,3),(3,2),(2,1),(4,5)],
   [(0,3),(3,1)],
   [(0,3),(3,2)],
   [(0,3),(4,5)],
   [(0,3),(3,1),(1,2),(4,5)],
   [(0,3),(1,2)]]

def LP2aw : List (List (ℕ × ℕ)) :=
  [[],
   [(2,3),(4,5)],
   [(2,4),(3,5)],
   [(2,5),(3,4)],
   [(0,1),(4,5)],
   [(0,1),(2,3)],
   [(0,1),(2,4),(4,3),(3,5)],
   [(0,1),(2,5),(5,3),(3,4)],
   [(0,2),(1,3)],
   [(0,2),(2,1),(1,3),(4,5)],
   [(0,2),(2,4),(1,3),(3,5)],
   [(0,2),(2,5),(1,3),(3,4)],
   [(0,3),(3,1),(1,2),(4,5)],
   [(0,3),(1,2)],
   [(0,3),(3,5),(1,2),(2,4)],
   [(0,3),(3,4),(1,2),(2,5)],
   [(0,4),(4,2),(1,5),(5,3)],
   [(0,4),(4,3),(1,5),(5,2)],
   [(0,4),(1,5)],
   [(0,4),(4,1),(1,5),(2,3)],
   [(0,5),(5,2),(1,4),(4,3)],
   [(0,5),(5,3),(1,4),(4,2)],
   [(0,5),(1,4)],
   [(0,5),(5,1),(1,4),(2,3)]]

def LS1w : List (List (ℕ × ℕ)) :=
  [[],
   [(3,4),(4,5)],
   [(3,5),(5,4)],
   [(2,3),(3,4)],
   [(2,3),(3,5)],
   [(2,4),(3,5)],
   [(1,2),(2,3),(3,4),(4,5)],
   [(1,2),(2,3),(3,5),(5,4)],
   [(1,2),(2,4),(4,3),(3,5)],
   [(1,3),(3,5),(5,2),(2,4)],
   [(0,1),(1,2),(2,3),(3,4)],
   [(0,1),(1,2),(2,3),(3,5)],
   [(0,1),(1,2),(2,4),(3,5)],
   [(0,1),(1,3),(3,5),(2,4)],
   [(0,2),(2,4),(1,3),(3,5)]]

def LS2w : List (List (ℕ × ℕ)) :=
  [[],
   [(3,4),(4,5)],
   [(3,5),(5,4)],
   [(1,2),(4,5)],
   [(1,2),(3,4)],
   [(1,2),(3,5)],
   [(1,3),(3,2)],
   [(1,3),(3,4),(4,5),(5,2)],
   [(1,3),(3,5),(5,4),(4,2)],
   [(1,4),(4,5),(5,3),(3,2)],
   [(1,4),(4,2)],
   [(1,4),(4,3),(3,5),(5,2)],
   [(1,5),(5,4),(4,3),(3,2)],
   [(1,5),(5,2)],
   [(1,5),(5,3),(3,4),(4,2)]]

@[expose] def LP1 : List (Perm (Fin 6)) := LP1w.map pw
@[expose] def LP2 : List (Perm (Fin 6)) := LP2w.map pw
@[expose] def LP1a : List (Perm (Fin 6)) := LP1aw.map pw
@[expose] def LP2a : List (Perm (Fin 6)) := LP2aw.map pw
@[expose] def LS1 : List (Perm (Fin 6)) := LS1w.map pw
@[expose] def LS2 : List (Perm (Fin 6)) := LS2w.map pw

@[expose] def LA (b o : Bool) : List (Perm (Fin 6)) :=
  if o then (if b then LP1a else LP1) else (if b then LP2a else LP2)

@[expose] def LB (b o : Bool) : List (Perm (Fin 6)) := LA b !o

@[expose] def LS (o : Bool) : List (Perm (Fin 6)) := if o then LS1 else LS2

theorem fin_sound : ∀ b o : Bool, (∀ a ∈ LA b o, InR b a ∧ InA o a) ∧
    (∀ c ∈ LB b o, InR b c ∧ InB o c) ∧ (∀ s ∈ LS o, InR true s) := fun b o =>
  ⟨I51K.all_of (t := fun c => I51K.rK b c && I51K.aK o c) (I51K.rA_iff b o)
      (by cases b <;> cases o <;> decide +kernel) (I51K.sound_check b o).1,
    I51K.all_of (t := fun c => I51K.rK b c && I51K.bK o c) (I51K.rB_iff b o)
      (by cases b <;> cases o <;> decide +kernel) (I51K.sound_check b o).2.1,
    I51K.all_of (t := I51K.rK true) (I51K.rK_iff true) (by cases o <;> decide +kernel)
      (I51K.sound_check b o).2.2⟩

theorem fin_nn : ∀ o : Bool, InB o (nn o) ∧ ¬ InA o (nn o) ∧ Perm.sign (nn o) = 1 ∧
    Perm.sign (ff o) = 1 := by
  decide +kernel

theorem fin_ff : ∀ o : Bool, ¬ InA o (ff o) ∧
    ∀ a : Perm (Fin 6), InA o a → ¬ InA o ((a * nn o)⁻¹ * ff o) := fun o =>
  ⟨fun h => absurd ((I51K.aK_iff o _).1 h) (by cases o <;> decide +kernel),
    I51K.ff_of o (fun σ => I51K.aK_iff o σ) (by cases o <;> decide +kernel)
      (by cases o <;> decide +kernel)⟩

theorem fin_cover : ∀ b o : Bool, ∀ σ : Perm (Fin 6), InR b σ → InA o σ ∨
    (∃ a ∈ LA b o, InA o ((a * nn o)⁻¹ * σ)) ∨ (∃ a ∈ LA b o, InA o ((a * ff o)⁻¹ * σ)) :=
  fun b o => I51K.cover_of b o (fun σ => I51K.rK_iff b σ) (fun σ => I51K.aK_iff o σ)
    (by cases b <;> cases o <;> decide +kernel) (by cases o <;> decide +kernel)
    (by cases o <;> decide +kernel)

theorem fin_BsubA : ∀ b o : Bool, ∀ σ : Perm (Fin 6), InR b σ → InB o σ → InA o σ ∨
    ∃ a ∈ LA b o, InA o ((a * nn o)⁻¹ * σ) :=
  fun b o => I51K.bsub_of b o (fun σ => I51K.rK_iff b σ) (fun σ => I51K.aK_iff o σ)
    (fun σ => I51K.bK_iff o σ) (by cases b <;> cases o <;> decide +kernel)
    (by cases o <;> decide +kernel)

theorem fin_gq3 : ∀ b o : Bool, ∀ a ∈ LA b o, ∃ c ∈ LB b o,
    (InA o (c⁻¹ * a * ff o) ∨ ∃ a' ∈ LA b o, InA o ((a' * nn o)⁻¹ * (c⁻¹ * a * ff o))) :=
  fun b o => I51K.gq3_of b o (fun σ => I51K.aK_iff o σ)
    (by cases b <;> cases o <;> decide +kernel) (by cases b <;> cases o <;> decide +kernel)
    (by cases o <;> decide +kernel) (by cases o <;> decide +kernel)

theorem fin_core : ∀ b o : Bool, ∀ n : Perm (Fin 6), InR b n →
    (∀ s ∈ LS o, InA o (s⁻¹ * n * s)) → n = 1 :=
  fun b o => I51K.core_of b o (fun σ => I51K.rK_iff b σ) (fun σ => I51K.aK_iff o σ)
    (by cases o <;> decide +kernel) (by decide +kernel)

theorem fin_card : ∀ b o : Bool,
    Fintype.card {σ : Perm (Fin 6) // InR b σ} =
        15 * Fintype.card {σ : Perm (Fin 6) // InR b σ ∧ InA o σ} ∧
    Fintype.card {σ : Perm (Fin 6) // InR b σ} =
      15 * Fintype.card {σ : Perm (Fin 6) // InR b σ ∧ InB o σ} := by
  intro b o
  rw [I51K.card_eq (fun σ => InR b σ) (I51K.rK b) (fun σ => I51K.rK_iff b σ),
    I51K.card_eq (fun σ => InR b σ ∧ InA o σ) (fun c => I51K.rK b c && I51K.aK o c)
      (I51K.rA_iff b o),
    I51K.card_eq (fun σ => InR b σ ∧ InB o σ) (fun c => I51K.rK b c && I51K.bK o c)
      (I51K.rB_iff b o)]
  exact ⟨(I51K.counts b o).1, (I51K.counts b o).2.1⟩

theorem fin_far_idx : ∀ b o : Bool,
    Fintype.card {σ : Perm (Fin 6) // InR b σ ∧ InA o σ ∧ InA o ((ff o)⁻¹ * σ * ff o)} * 8 =
      Fintype.card {σ : Perm (Fin 6) // InR b σ ∧ InA o σ} := by
  intro b o
  rw [I51K.card_eq (fun σ => InR b σ ∧ InA o σ ∧ InA o ((ff o)⁻¹ * σ * ff o))
      (fun c => I51K.rK b c &&
        (I51K.aK o c && I51K.aK o (CFSG.Permutation.FinPack.mulK 6
          (CFSG.Permutation.FinPack.mulK 6 (I51K.FC o) c) (I51K.FC o))))
      (I51K.rAC_iff b o (f := ff o) (F := I51K.FC o) (by cases o <;> decide +kernel)
        (by cases o <;> decide +kernel)),
    I51K.card_eq (fun σ => InR b σ ∧ InA o σ) (fun c => I51K.rK b c && I51K.aK o c)
      (I51K.rA_iff b o)]
  exact (I51K.counts b o).2.2.1

theorem fin_near_idx : ∀ b o : Bool,
    Fintype.card {σ : Perm (Fin 6) // InR b σ ∧ InA o σ ∧ InA o ((nn o)⁻¹ * σ * nn o)} * 6 =
      Fintype.card {σ : Perm (Fin 6) // InR b σ ∧ InA o σ} := by
  intro b o
  rw [I51K.card_eq (fun σ => InR b σ ∧ InA o σ ∧ InA o ((nn o)⁻¹ * σ * nn o))
      (fun c => I51K.rK b c &&
        (I51K.aK o c && I51K.aK o (CFSG.Permutation.FinPack.mulK 6
          (CFSG.Permutation.FinPack.mulK 6 (I51K.NC o) c) (I51K.NC o))))
      (I51K.rAC_iff b o (f := nn o) (F := I51K.NC o) (by cases o <;> decide +kernel)
        (by cases o <;> decide +kernel)),
    I51K.card_eq (fun σ => InR b σ ∧ InA o σ) (fun c => I51K.rK b c && I51K.aK o c)
      (I51K.rA_iff b o)]
  exact (I51K.counts b o).2.2.2

theorem fin_LA_complete : ∀ b o : Bool, ∀ σ : Perm (Fin 6), InR b σ → InA o σ → σ ∈ LA b o :=
  fun b o => I51K.mem_of I51K.memA_walk b o (fun σ => I51K.rK_iff b σ)
    (fun σ => I51K.aK_iff o σ) (by cases b <;> cases o <;> decide +kernel)

end CFSG.Quasithin.H13.I51
