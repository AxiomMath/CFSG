module

public import Certificates.Certificate7107
public import CFSG.Monster.B.Classical.PlaneIncidence
import all CFSG.Fischer.F4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Check

public section

namespace CFSG.Quasithin.H13

open CFSG.M23Pair CFSG.Fischer CFSG.Monster.B.Classical.Plane
open CFSG.QuasithinUnique.Vol2Native.L239
open scoped Matrix

theorem hepL_mem (a : Fin 21) : hepL a ∈ M23Insp.data.H :=
  Certificates.certificate7107.1 a

theorem length_heptThrough : heptThrough.length = 21 :=
  Certificates.certificate7107.2.1

theorem sbar_apply_21 :
    ((sbar : ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) 21 = 22 :=
  Certificates.certificate7107.2.2.1.1

theorem sbar_apply_22 :
    ((sbar : ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) 22 = 21 :=
  Certificates.certificate7107.2.2.1.2

theorem lamInv_sbar_lam (i : Fin 21) :
    lamInv (((sbar : ↥CFSG.Blueprint.NativeSporadic.M23) : Equiv.Perm (Fin 23)) (lam i)) =
      normIdx (A0 *ᵥ frobVec (Ω i)) :=
  Certificates.certificate7107.2.2.2.1 i

theorem lam_ne_21 : ∀ i : Fin 21, lam i ≠ 21 := by decide

theorem lam_ne_22 : ∀ i : Fin 21, lam i ≠ 22 := by decide

theorem lamInv_lam : ∀ i : Fin 21, lamInv (lam i) = i := by decide

theorem lam_lamInv : ∀ x : Fin 23, x ≠ 21 → x ≠ 22 → lam (lamInv x) = x := by decide

theorem lam_injective : Function.Injective lam := fun i j h => by
  rw [← lamInv_lam i, h, lamInv_lam]

theorem det_A0 : A0.det = 1 := by decide

theorem lam_mem_hepL_iff {a p : Fin 21} : lam p ∈ hepL a ↔ p ∈ projLine a := by
  rw [hepL, Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨q, hq, hqp⟩ | h | h)
    · exact lam_injective hqp ▸ hq
    · exact absurd h (lam_ne_21 p)
    · exact absurd h (lam_ne_22 p)
  · intro hp
    exact Or.inl ⟨p, hp, rfl⟩

theorem mem_hepL_21 (a : Fin 21) : (21 : Fin 23) ∈ hepL a :=
  Finset.mem_union_right _ (Finset.mem_insert_self _ _)

theorem mem_hepL_22 (a : Fin 21) : (22 : Fin 23) ∈ hepL a :=
  Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem hepL_injective : Function.Injective hepL := by
  intro a b h
  apply projLine_injective
  ext p
  rw [← lam_mem_hepL_iff, ← lam_mem_hepL_iff, h]

theorem eq_hepL_of_mem
    {B : Finset (Fin 23)} (hB : B ∈ M23Insp.data.H) (h21 : (21 : Fin 23) ∈ B)
    (h22 : (22 : Fin 23) ∈ B) : ∃ a : Fin 21, B = hepL a := by
  classical
  have hnd : heptThrough.Nodup := M23Insp.chk_H_nodup.filter _
  have hmem : ∀ C, C ∈ heptThrough ↔ C ∈ M23Insp.data.H ∧ (21 : Fin 23) ∈ C ∧
      (22 : Fin 23) ∈ C := by
    intro C
    rw [heptThrough, List.mem_filter, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  have hsub : Finset.univ.image hepL ⊆ heptThrough.toFinset := by
    intro C hC
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hC
    rw [List.mem_toFinset, hmem]
    exact ⟨hepL_mem a, mem_hepL_21 a, mem_hepL_22 a⟩
  have heq : Finset.univ.image hepL = heptThrough.toFinset := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [List.toFinset_card_of_nodup hnd, length_heptThrough,
      Finset.card_image_of_injective _ hepL_injective, Finset.card_univ, Fintype.card_fin]
  have hBF : B ∈ heptThrough.toFinset := by
    rw [List.mem_toFinset, hmem]
    exact ⟨hB, h21, h22⟩
  rw [← heq] at hBF
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hBF
  exact ⟨a, ha.symm⟩

end CFSG.Quasithin.H13
