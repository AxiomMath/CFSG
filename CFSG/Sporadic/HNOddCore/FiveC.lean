module

public import CFSG.Sporadic.HNOddCore.FiveB
public import CFSG.Sporadic.HNOddCore.OddB
public import Certificates.Certificate2085
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv Equiv.Perm
open CFSG.ComponentClassification.SymmetricLocal

abbrev Hi5 : Fin 12 → Prop := fun i => ¬ i.val < 5

abbrev A7P : Subgroup (Perm (Fin 12)) :=
  (alternatingGroup {i : Fin 12 // Hi5 i}).map Perm.ofSubtype

@[expose] def a7Hom :
    AH →* A7P :=
  (thetaHom.comp AH.subtype).codRestrict A7P fun h => by
    rw [MonoidHom.comp_apply, thetaHom_apply]
    have hf := (mem_alt5 _).1 h.2
    refine (mem_map_ofSubtype_alternatingGroup_iff (p := Hi5)).2 ⟨fun x hx => ?_, ?_⟩
    · exact hf x (not_not.1 hx)
    · exact Equiv.Perm.mem_alternatingGroup.1 (thetaJ _).2

theorem a7Hom_val
    (h : AH) :
    ((a7Hom h : A7P) : Perm (Fin 12)) = (thetaJ (h : HJ) : Perm (Fin 12)) := rfl

theorem a7Hom_bijective :
    Function.Bijective a7Hom := by
  constructor
  · intro a b hab
    have e1 : (thetaJ (a : HJ) : Perm (Fin 12)) = thetaJ (b : HJ) := by
      rw [← a7Hom_val, ← a7Hom_val, hab]
    exact Subtype.ext (thetaJ.injective (Subtype.ext e1))
  · rintro ⟨σ, hσ⟩
    obtain ⟨hfix, hsign⟩ := (mem_map_ofSubtype_alternatingGroup_iff (p := Hi5)).1 hσ
    obtain ⟨h, hθ⟩ : ∃ h : HJ, (thetaJ h : Perm (Fin 12)) = σ :=
      ⟨thetaJ.symm ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩,
        by rw [MulEquiv.apply_symm_apply]⟩
    have hmem : h ∈ AH := by
      show thetaJ h ∈ alt5
      rw [mem_alt5]
      intro i hi
      rw [hθ]
      exact hfix i (not_not.2 hi)
    refine ⟨⟨h, hmem⟩, Subtype.ext ?_⟩
    rw [a7Hom_val]
    exact hθ

theorem card_Hi5 : Nat.card {i : Fin 12 // Hi5 i} = 7 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

theorem card_A7P : Nat.card A7P = 2520 := by
  have : Nontrivial {i : Fin 12 // Hi5 i} :=
    ⟨⟨⟨5, by decide⟩, ⟨6, by decide⟩, by decide⟩⟩
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (alternatingGroup {i : Fin 12 // Hi5 i})
    Perm.ofSubtype Perm.ofSubtype_injective).toEquiv, nat_card_alternatingGroup, card_Hi5]
  rfl

theorem card_AH :
    Nat.card AH = 2520 := by
  rw [Nat.card_congr (Equiv.ofBijective a7Hom a7Hom_bijective), card_A7P]

theorem A7P_simple : IsSimpleGroup A7P :=
  (Subgroup.equivMapOfInjective (alternatingGroup {i : Fin 12 // Hi5 i}) Perm.ofSubtype
    Perm.ofSubtype_injective).isSimpleGroup_congr.1
    (alternatingGroup.isSimpleGroup (by rw [card_Hi5]; norm_num))

theorem AH_simple :
    IsSimpleGroup AH :=
  sub_isSimpleGroup_of_bijective a7Hom a7Hom_bijective A7P_simple

abbrev B5 : Subgroup HJ :=
  Subgroup.closure (Set.range fun j : Fin 5 => (⟨aGenJ j, aGenJ_mem j⟩ : HJ))

theorem natImgs_a_size :
    (natImgs natStrongArr FAData.aWords).size = 5 := by
  simp [natImgs, aWords_size]

theorem permOfArr_natImg
    {j : ℕ} (hj : j < 5) :
    Monster.B.Co2.permOfArr 12 (natImgs natStrongArr FAData.aWords)[j]! =
      (thetaJ ⟨aGenJ j, aGenJ_mem j⟩ : Perm (Fin 12)) := by
  rw [natImgs, map_getElem! _ _ (by rw [aWords_size]; exact hj),
    permOfArr_eq_of_prep (prep_natWord (aWords_letters hj))]
  exact (thetaJ_hWord _).symm

theorem B5_map :
    B5.map thetaHom = arrGen 12 (natImgs natStrongArr FAData.aWords) := by
  rw [MonoidHom.map_closure, arrGen]
  congr 1
  ext σ
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by rw [natImgs_a_size]; exact j.2, by rw [permOfArr_natImg j.2]; rfl⟩
  · rintro ⟨k, hk, rfl⟩
    rw [natImgs_a_size] at hk
    exact ⟨_, ⟨⟨k, hk⟩, rfl⟩, by rw [permOfArr_natImg hk]; rfl⟩

theorem card_B5 :
    Nat.card B5 = 2520 := by
  have h := five_small_parts.1
  unfold natChainOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← Subgroup.card_map_of_injective thetaHom_injective, B5_map,
    card_arrGen_of_chainCheck (by norm_num) (by decide) h.2]
  rfl

theorem B5_eq :
    B5 = AH := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_AH, card_B5])
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact aGenJ_mem_AH j.2

abbrev AJ :
    Subgroup JH := AH.map HJ.subtype

theorem AJ_eq :

    AJ = Subgroup.closure (Set.range fun j : Fin 5 => aGenJ j) := by
  rw [AJ, ← B5_eq, MonoidHom.map_closure, ← Set.range_comp]
  rfl

theorem AJ_le_HJ :
    AJ ≤ HJ := Subgroup.map_subtype_le _

theorem card_AJ :
    Nat.card AJ = 2520 := by
  rw [Subgroup.card_map_of_injective HJ.subtype_injective, card_AH]

theorem IJ_eq :
    IJ = Subgroup.closure (Set.range fun k : Fin 6 => iGen k) := by
  apply le_antisymm
  · rw [IJ, Subgroup.closure_le]
    rintro x (hx | hx)
    · have hle : AJ ≤ Subgroup.closure (Set.range fun k : Fin 6 => iGen k) := by
        rw [AJ_eq, Subgroup.closure_le]
        rintro _ ⟨j, rfl⟩
        exact Subgroup.subset_closure ⟨⟨j, by omega⟩, ite_eq_left j.2⟩
      exact hle hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.subset_closure ⟨5, ite_eq_right (by norm_num)⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    unfold iGen
    dsimp only
    split_ifs with h
    · refine Subgroup.subset_closure (Or.inl ?_)
      have hmem : aGenJ k ∈ AJ := by
        rw [AJ_eq]
        exact Subgroup.subset_closure ⟨⟨k, h⟩, rfl⟩
      exact hmem
    · exact Subgroup.subset_closure (Or.inr rfl)

end CFSG.Sporadic.HNOddCore
