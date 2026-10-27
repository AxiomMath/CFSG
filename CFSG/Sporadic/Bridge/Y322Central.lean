module

public import CFSG.Sporadic.Bridge.Y443Split
public import CFSG.YGroups.Y322Central
import all CFSG.Sporadic.Bridge.Y322Words

public section

namespace CFSG.Sporadic.Bridge.Y322

open CFSG.Certificates CFSG.Certificates.CosetEnumeration CFSG.YGroups

@[expose] def node (c : ℕ) : Fin 8 := ⟨c % 8, Nat.mod_lt _ (by norm_num)⟩

@[expose] def positive (w : List ℕ) : List (Fin 8 × Bool) := w.map fun c => (node c, true)

theorem yRels_letters : ∀ w ∈ yRels 3 2 2, ∀ c ∈ w, c < 8 := by decide +kernel

theorem positive_mem_words : ∀ w ∈ yRels 3 2 2, positive w ∈ words := by decide +kernel

theorem positive_wordF1 : positive y322WordF1 = f1Word := by decide +kernel

theorem positive_wordF2 : positive y322WordF2 = f2Word := by decide +kernel

theorem wordF1_letters : ∀ c ∈ y322WordF1, c < 8 := by decide +kernel

theorem wordF2_letters : ∀ c ∈ y322WordF2, c < 8 := by decide +kernel

variable {G : Type} [Group G] (s : Fin 8 → G)

theorem signedProd_positive (w : List ℕ) :
    signedProd s (positive w) = (w.map fun c => s (node c)).prod := by
  simp [signedProd, positive, Function.comp_def]

theorem lift_wordFG (f : Fin (ngen 3 2 2) → G) (w : List ℕ) :
    FreeGroup.lift f (wordFG (ngen 3 2 2) w) =
      (w.map fun c => if h : c < ngen 3 2 2 then f ⟨c, h⟩ else 1).prod := by
  simp only [wordFG, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  by_cases h : c < ngen 3 2 2 <;> simp [h]

theorem lift_relator (hs : ∀ w ∈ words, signedProd s w = 1) :
    ∀ r ∈ yRelSet 3 2 2, FreeGroup.lift (fun c : Fin (ngen 3 2 2) => s (node c.val)) r = 1 := by
  rintro r ⟨w, hw, rfl⟩
  rw [lift_wordFG, ← hs _ (positive_mem_words w hw), signedProd_positive]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  have h : c < ngen 3 2 2 := yRels_letters w hw c hc
  simp [h]

noncomputable def hom (hs : ∀ w ∈ words, signedProd s w = 1) : YGroup 3 2 2 →* G :=
  PresentedGroup.toGroup (lift_relator s hs)

theorem hom_yGen (hs : ∀ w ∈ words, signedProd s w = 1) {c : ℕ} (hc : c < 8) :
    hom s hs (yGen 3 2 2 c) = s (node c) := by
  rw [yGen_of_lt (show c < ngen 3 2 2 from hc), hom, PresentedGroup.toGroup.of]

theorem hom_evalWord (hs : ∀ w ∈ words, signedProd s w = 1) {w : List ℕ} (hw : ∀ c ∈ w, c < 8) :
    hom s hs (evalWord (yGen 3 2 2) w) = signedProd s (positive w) := by
  rw [signedProd_positive, evalWord, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun c hc => hom_yGen s hs (hw c hc)

theorem hom_F1 (hs : ∀ w ∈ words, signedProd s w = 1) :
    hom s hs y322F1 = signedProd s f1Word := by
  rw [← positive_wordF1, y322F1, hom_evalWord s hs wordF1_letters]

theorem hom_F2 (hs : ∀ w ∈ words, signedProd s w = 1) :
    hom s hs y322F2 = signedProd s f2Word := by
  rw [← positive_wordF2, y322F2, hom_evalWord s hs wordF2_letters]

theorem centralWord :
    CentralWord := by
  intro G _ s hs
  refine ⟨?_, ?_, fun i => ?_⟩
  · rw [← hom_F1 s hs, ← hom_F2 s hs, y322F1_eq_F2]
  · rw [← hom_F1 s hs, ← map_pow, pow_two, y322F1_mul_self, map_one]
  · have hi : node i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    have h := congrArg (hom s hs) (y322F1_comm_yGen (show i.val < 8 from i.isLt))
    rw [map_mul, map_mul, hom_yGen s hs i.isLt, hi, hom_F1 s hs] at h
    exact h

end CFSG.Sporadic.Bridge.Y322

namespace CFSG.Sporadic.Bridge.Y443

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Carrier .M ≃* TauCeti.SporadicName.M.Group) :=
  nonempty_mulEquiv_of_centralWord Y322.centralWord

end CFSG.Sporadic.Bridge.Y443
