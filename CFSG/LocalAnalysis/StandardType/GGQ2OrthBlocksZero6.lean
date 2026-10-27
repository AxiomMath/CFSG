module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthAmbient
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthAmbientSmall
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksGroup
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksComp
public import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.ClassicalInvolution.Models.SymplecticPairs Matrix
open CFSG.Open (StatedSp)
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K]
variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)

@[expose] def emb (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    Fin (S.card + δ.val) → Fin (t + δ.val) :=
  Fin.addCases (fun i => Fin.castAdd δ.val (S.orderEmbOfFin rfl i))
    (fun j => Fin.natAdd t j)

theorem emb_castAdd {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)} (i : Fin S.card) :
    emb t δ S (Fin.castAdd δ.val i) = Fin.castAdd δ.val (S.orderEmbOfFin rfl i) :=
  Fin.addCases_left i

theorem emb_natAdd {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)} (j : Fin δ.val) :
    emb t δ S (Fin.natAdd S.card j) = Fin.natAdd t j :=
  Fin.addCases_right j

theorem emb_injective (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    Function.Injective (emb t δ S) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [emb_castAdd, emb_castAdd] at hij
      have h := Fin.castAdd_injective _ _ hij
      have h' := (S.orderEmbOfFin rfl).injective h
      rw [h']
    | right j =>
      rw [emb_castAdd, emb_natAdd] at hij
      have hv := congrArg Fin.val hij
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have h1 := (S.orderEmbOfFin rfl i).isLt
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [emb_natAdd, emb_castAdd] at hij
      have hv := congrArg Fin.val hij
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have h1 := (S.orderEmbOfFin rfl j).isLt
      omega
    | right j =>
      rw [emb_natAdd, emb_natAdd] at hij
      have h := Fin.natAdd_injective _ _ hij
      rw [h]

theorem mem_liftSupport_iff {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)}
    (j : Fin (t + δ.val)) :
    j ∈ liftSupport t δ S ↔ ∃ i : Fin (S.card + δ.val), emb t δ S i = j := by
  classical
  constructor
  · intro hj
    rw [liftSupport, Finset.mem_union] at hj
    rcases hj with hj | hj
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      have hri : Set.range (S.orderEmbOfFin rfl) = ((S : Finset (Fin t)) : Set (Fin t)) :=
        Finset.range_orderEmbOfFin S rfl
      have hmem : i ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [hri]
        exact hi
      obtain ⟨k, rfl⟩ := hmem
      exact ⟨Fin.castAdd δ.val k, emb_castAdd k⟩
    · obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp hj
      exact ⟨Fin.natAdd S.card k, emb_natAdd k⟩
  · rintro ⟨i, rfl⟩
    induction i using Fin.addCases with
    | left i =>
      rw [emb_castAdd, liftSupport, Finset.mem_union]
      left
      exact Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem S rfl i)
    | right j =>
      rw [emb_natAdd, liftSupport, Finset.mem_union]
      right
      exact Finset.mem_map_of_mem _ (Finset.mem_univ j)

theorem image_emb_univ {t : ℕ} {δ : Fin 2} (S : Finset (Fin t)) :
    Finset.univ.image (emb t δ S) = liftSupport t δ S := by
  classical
  ext j
  rw [Finset.mem_image, mem_liftSupport_iff]
  simp only [Finset.mem_univ, true_and]

theorem emb_plane_lt_iff {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)}
    (k : Fin (S.card + δ.val)) : (emb t δ S k : ℕ) < t ↔ (k : ℕ) < S.card := by
  induction k using Fin.addCases with
  | left i =>
    rw [emb_castAdd]
    have h1 := (S.orderEmbOfFin rfl i).isLt
    have h2 := i.isLt
    rw [Fin.val_castAdd, Fin.val_castAdd]
    exact ⟨fun _ => h2, fun _ => h1⟩
  | right j =>
    rw [emb_natAdd]
    have h := j.isLt
    rw [Fin.val_natAdd, Fin.val_natAdd]
    constructor <;> omega

theorem planeQ_lift (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {w : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K}
    (hw : ∀ z : Fin (t + δ.val) ⊕ Fin (t + δ.val),
      (Sum.elim id id z : Fin (t + δ.val)) ∉ liftSupport t δ S → w z = 0) :
    planeQ (K := K) t δ w = planeQ (K := K) S.card δ
      (fun z => w (Sum.map (emb t δ S) (emb t δ S) z)) := by
  classical
  have hterm : ∀ j : Fin (t + δ.val),
      (w (Sum.inl j) * w (Sum.inr j) +
        if (j : ℕ) < t then w (Sum.inl j) ^ 2 + w (Sum.inr j) ^ 2 else 0) =
      (if j ∈ liftSupport t δ S then
        (w (Sum.inl j) * w (Sum.inr j) +
          if (j : ℕ) < t then w (Sum.inl j) ^ 2 + w (Sum.inr j) ^ 2 else 0) else 0) := by
    intro j
    by_cases hj : j ∈ liftSupport t δ S
    · rw [if_pos hj]
    · rw [if_neg hj, hw (Sum.inl j) (by simpa using hj), hw (Sum.inr j) (by simpa using hj)]
      simp
  calc planeQ (K := K) t δ w
      = ∑ j : Fin (t + δ.val),
          (w (Sum.inl j) * w (Sum.inr j) +
            if (j : ℕ) < t then w (Sum.inl j) ^ 2 + w (Sum.inr j) ^ 2 else 0) := rfl
    _ = ∑ j : Fin (t + δ.val),
          (if j ∈ liftSupport t δ S then
            (w (Sum.inl j) * w (Sum.inr j) +
              if (j : ℕ) < t then w (Sum.inl j) ^ 2 + w (Sum.inr j) ^ 2 else 0) else 0) :=
        Finset.sum_congr rfl fun j _ => hterm j
    _ = ∑ j ∈ liftSupport t δ S,
          (w (Sum.inl j) * w (Sum.inr j) +
            if (j : ℕ) < t then w (Sum.inl j) ^ 2 + w (Sum.inr j) ^ 2 else 0) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = ∑ j ∈ Finset.univ.image (emb t δ S),
          (w (Sum.inl j) * w (Sum.inr j) +
            if (j : ℕ) < t then w (Sum.inl j) ^ 2 + w (Sum.inr j) ^ 2 else 0) := by
        rw [image_emb_univ]
    _ = ∑ k : Fin (S.card + δ.val),
          (w (Sum.inl (emb t δ S k)) * w (Sum.inr (emb t δ S k)) +
            if (emb t δ S k : ℕ) < t then
              w (Sum.inl (emb t δ S k)) ^ 2 + w (Sum.inr (emb t δ S k)) ^ 2 else 0) :=
        Finset.sum_image fun a _ b _ hab => emb_injective t δ S hab
    _ = ∑ k : Fin (S.card + δ.val),
          ((w (Sum.map (emb t δ S) (emb t δ S) (Sum.inl k))) *
              (w (Sum.map (emb t δ S) (emb t δ S) (Sum.inr k))) +
            if (k : ℕ) < S.card then
              (w (Sum.map (emb t δ S) (emb t δ S) (Sum.inl k))) ^ 2 +
                (w (Sum.map (emb t δ S) (emb t δ S) (Sum.inr k))) ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Sum.map_inl, Sum.map_inr]
        have hlt := emb_plane_lt_iff (δ := δ) (S := S) k
        by_cases hk : (k : ℕ) < S.card
        · rw [if_pos (hlt.2 hk), if_pos hk]
        · rw [if_neg (fun h => hk (hlt.1 h)), if_neg hk]
    _ = planeQ (K := K) S.card δ
          (fun z => w (Sum.map (emb t δ S) (emb t δ S) z)) := rfl

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
