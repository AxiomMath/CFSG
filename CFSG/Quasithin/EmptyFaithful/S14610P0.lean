module

public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S146E3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem i1Of1469_le_yOfL22_sup (T M I : Subgroup G) : i1Of1469 T M I ≤ yOfL22 T M ⊔ T :=
  sup_le (((oTwoUpper_le _).trans inf_le_left).trans le_sup_left) (inf_le_left.trans le_sup_right)

omit [Finite G] in
theorem i1Of1469_le (T M I : Subgroup G) : i1Of1469 T M I ≤ I :=
  sup_le ((oTwoUpper_le _).trans inf_le_right) inf_le_right

theorem Setting146.pCoreOf_yOfL22_sup_le_mcOf (S : Setting146 G T M) :
    pCoreOf 2 (yOfL22 T M ⊔ T) ≤ mcOf T := by
  have hOC : pCoreOf 2 (yOfL22 T M ⊔ T) ≤ Subgroup.centralizer (VZ T M : Set G) := by
    rw [← S.hyp1281.centralizer]; exact inf_le_right
  exact hOC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ _)))

theorem Setting146.not_lI_le_mcOf (S : Setting146 G T M) {I : Subgroup G}
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    ¬ lI T M I ≤ mcOf T := by
  intro h
  apply S.not_yOfL22_le_mcOf
  have hTG : T ≤ mcOf T := le_centralizer_quasithinOmegaOneCenter T
  have h2 : yOfL22 T M ⊔ T ≤ mcOf T := by
    rw [hLT]
    exact sup_le (sup_le h (inf_le_left.trans hTG)) S.pCoreOf_yOfL22_sup_le_mcOf
  exact le_sup_left.trans h2

private noncomputable def i1Hom (T M I : Subgroup G)
    (φ : OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3)) :
    ↥(i1Of1469 T M I) →* Equiv.Perm (Fin 3) :=
  (Der6A.piS3 φ).comp (Subgroup.inclusion (i1Of1469_le_yOfL22_sup T M I))

omit [Finite G] in
private theorem i1Hom_surjective (T M I : Subgroup G)
    (φ : OTwoQuot (yOfL22 T M ⊔ T) ≃* Equiv.Perm (Fin 3))
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    Function.Surjective (i1Hom T M I φ) := by
  intro σ
  obtain ⟨y, hy⟩ := Der6A.piS3_surjective φ σ
  have hXO : i1Of1469 T M I ≤ Subgroup.normalizer (pCoreOf 2 (yOfL22 T M ⊔ T) : Set G) :=
    (i1Of1469_le_yOfL22_sup T M I).trans (le_normalizer_pCoreOf 2 _)
  have hyLT : (y : G) ∈ ((i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) : Subgroup G) : Set G) :=
    hLT ▸ y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXO] at hyLT
  obtain ⟨a, ha, b, hb, hab⟩ := hyLT
  have hLTa : a ∈ yOfL22 T M ⊔ T := i1Of1469_le_yOfL22_sup T M I ha
  have hLTb : b ∈ yOfL22 T M ⊔ T := pCoreOf_le 2 _ hb
  refine ⟨⟨a, ha⟩, ?_⟩
  have e : y = ⟨a, hLTa⟩ * ⟨b, hLTb⟩ := Subtype.ext hab.symm
  have hb1 : Der6A.piS3 φ ⟨b, hLTb⟩ = 1 := (Der6A.piS3_eq_one_iff φ hLTb).mpr hb
  rw [← hy, e, map_mul, hb1, mul_one]
  rfl

theorem Setting146.i1_oTwoQuot (S : Setting146 G T M) {I : Subgroup G}
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    Nonempty (OTwoQuot (i1Of1469 T M I) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨φ⟩ := S.hyp1281.sThree
  refine nonempty_oTwoQuot_equiv_perm_three (i1Of1469 T M I) (i1Hom T M I φ)
    (i1Hom_surjective T M I φ hLT) fun x hx => ?_
  have hxLT : (x : G) ∈ yOfL22 T M ⊔ T := i1Of1469_le_yOfL22_sup T M I x.2
  have hxO : (x : G) ∈ pCoreOf 2 (yOfL22 T M ⊔ T) :=
    (Der6A.piS3_eq_one_iff φ hxLT).mp hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 (yOfL22 T M ⊔ T)))
    ⟨x, hxO⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (x : G) ^ 2 ^ k = 1 := by
    have := pow_orderOf_eq_one (⟨x, hxO⟩ : pCoreOf 2 (yOfL22 T M ⊔ T))
    rw [hk] at this
    exact congrArg Subtype.val this
  simpa using h1

theorem Setting146.pCoreOf_i1_eq (S : Setting146 G T M) {I : Subgroup G}
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hsyl : IsSylowTwoOf (T ⊓ I) I) :
    pCoreOf 2 (i1Of1469 T M I) = i1Of1469 T M I ⊓ pCoreOf 2 (yOfL22 T M ⊔ T) ∧
      pCoreOf 2 (i1Of1469 T M I) = pCoreOf 2 (yOfL22 T M ⊔ T) ⊓ (T ⊓ I) := by
  obtain ⟨φ⟩ := S.hyp1281.sThree
  have hXLT : i1Of1469 T M I ≤ yOfL22 T M ⊔ T := i1Of1469_le_yOfL22_sup T M I
  have hTI1 : T ⊓ I ≤ i1Of1469 T M I := le_sup_right
  have hsyl1 : IsSylowTwoOf (T ⊓ I) (i1Of1469 T M I) :=
    B6.isSylowTwoOf_mono hsyl hTI1 (i1Of1469_le T M I)
  have h1 : pCoreOf 2 (i1Of1469 T M I) = i1Of1469 T M I ⊓ pCoreOf 2 (yOfL22 T M ⊔ T) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hxX : x ∈ i1Of1469 T M I := pCoreOf_le 2 _ hx
      refine ⟨hxX, ?_⟩
      have hN : ((pCoreOf 2 (i1Of1469 T M I)).subgroupOf (i1Of1469 T M I)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
          (le_normalizer_pCoreOf 2 _)
      have hNp : IsPGroup 2 ((pCoreOf 2 (i1Of1469 T M I)).subgroupOf (i1Of1469 T M I)) :=
        (pCoreOf_isPGroup 2 (i1Of1469 T M I)).of_equiv
          (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 _)).symm
      have hs := i1Hom_surjective T M I φ hLT
      have hmapn := Subgroup.Normal.map hN (i1Hom T M I φ) hs
      have hmapp := hNp.map (i1Hom T M I φ)
      have hle := le_pCore 2 hmapn hmapp
      rw [F6.pCore_perm_three_eq_bot, le_bot_iff] at hle
      have h1 : i1Hom T M I φ ⟨x, hxX⟩ ∈
          ((pCoreOf 2 (i1Of1469 T M I)).subgroupOf (i1Of1469 T M I)).map (i1Hom T M I φ) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
      rw [hle, Subgroup.mem_bot] at h1
      exact (Der6A.piS3_eq_one_iff φ (hXLT hxX)).mp h1
    · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        le_normalizer_pCoreOf 2 _ (hXLT hg)⟩
  refine ⟨h1, ?_⟩
  have hle : i1Of1469 T M I ⊓ pCoreOf 2 (yOfL22 T M ⊔ T) ≤ T ⊓ I :=
    h1 ▸ B6.pCoreOf_two_le_of_isSylowTwoOf hsyl1
  rw [h1]
  exact le_antisymm (le_inf inf_le_right hle) (le_inf (inf_le_right.trans hTI1) inf_le_left)

end CFSG.Quasithin
