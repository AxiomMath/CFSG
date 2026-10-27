module

public import CFSG.Quasithin.EmptyFaithful.S1469One
public import CFSG.Quasithin.EmptyFaithful.S1469Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

structure Ctx1469 (T M H : Subgroup G) (u : G) (I : Subgroup G) : Prop where
  setting : Setting146 G T M
  hH : IsHTM T M H
  hu : IsInvU T M H u
  hI : IsIMin T M u I
  hrank : 4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G))
  hT : 2 ^ 11 < Nat.card T
  hTI : 2 ^ 9 < Nat.card (T ⊓ I : Subgroup G)
  minPar : MinParabolic I (T ⊓ I) (I ⊓ mcOf T)
  cgs_le : cgsIn I (T ⊓ I) ≤ I ⊓ mcOf T
  not_conclusion :
    ¬ (yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))

@[expose] def Main1469 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H : Subgroup G) (u : G) (I : Subgroup G),
    Ctx1469 T M H u I → False

variable {T M : Subgroup G}

omit [Finite G] in
theorem lI_mono {I J : Subgroup G} (hJI : J ≤ I) : lI T M J ≤ lI T M I :=
  oTwoUpper_mono (inf_le_inf_left _ hJI)

omit [Finite G] in
theorem conclusion1469_of_le {I J : Subgroup G} (hJI : J ≤ I) (hTJ : T ⊓ J = T ⊓ I)
    (hc : yOfL22 T M ⊔ T = (lI T M J ⊔ (T ⊓ J)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :
    yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) := by
  refine le_antisymm ?_ ?_
  · calc yOfL22 T M ⊔ T = (lI T M J ⊔ (T ⊓ J)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) := hc
      _ ≤ (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T) :=
        sup_le_sup_right (sup_le_sup (lI_mono hJI) hTJ.le) _
  · refine sup_le (sup_le ?_ ?_) (pCoreOf_le 2 _)
    · exact ((oTwoUpper_le _).trans inf_le_left).trans le_sup_left
    · exact inf_le_left.trans le_sup_right

theorem Setting146.exists_ctx1469 (h3 : Stage1466Three) (h1 : Stage1463One) (h2 : Stage1463Two)
    (h4 : Stage1463Four) (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) {u : G}
    (hu : IsInvU T M H u) {I : Subgroup G} (hI : IsIStar T M u I)
    (hbig : 2 ^ 11 < Nat.card T)
    (hrank : 4 ≤ mIdx (conjClosure (VZ T M) H) (Subgroup.centralizer (pCoreOf 2 H : Set G)))
    (hnot : ¬ (yOfL22 T M ⊔ T = (lI T M I ⊔ (T ⊓ I)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))) :
    ∃ J : Subgroup G, Ctx1469 T M H u J := by
  obtain ⟨J, hJ, hJI⟩ := exists_isIMin_le hI
  have hTJ : T ⊓ J = T ⊓ I := tI_eq_of_le hI hJ.1 hJI
  have hnotJ : ¬ (yOfL22 T M ⊔ T = (lI T M J ⊔ (T ⊓ J)) ⊔ pCoreOf 2 (yOfL22 T M ⊔ T)) :=
    fun hc => hnot (conclusion1469_of_le hJI hTJ hc)
  have hidx := (h1 G T M S H hH u hu).2.1
  have hN0 := h2 G T M S H hH u hu
  have hNu := (h4 G T M S H hH u hu).1
  obtain ⟨hsyl, hcases⟩ := isIStar_sylow_cases S hu hidx hN0 hNu hJ.1
  have h4' := stage1466_four_of h3 G T M H u S hH hu J hJ.1
  have h5' := stage1466_five_of h3 h1 h2 h4 G T M H u S hH hu J hJ
  exact ⟨J, S, hH, hu, hJ, hrank, hbig, S.card_tI_gt hH hu hcases hbig,
    ⟨hsyl, tI_not_normal hJ.1 hcases hN0 hNu, h5'.resolve_right fun hc => hnotJ hc.2⟩,
    h4'.resolve_right fun hc => hnotJ hc.2, hnotJ⟩

theorem stage1469W_of_main (h3 : Stage1466Three) (h1 : Stage1463One) (h2 : Stage1463Two)
    (h4 : Stage1463Four) (hmain : Main1469) : Stage1469W := by
  intro G _ _ T M H u S hH hu I hI hbig hrank
  by_contra hnot
  obtain ⟨J, hJ⟩ := S.exists_ctx1469 h3 h1 h2 h4 hH hu hI hbig hrank hnot
  exact hmain G T M H u J hJ

theorem stage1469_of_main (h3 : Stage1466Three) (h1 : Stage1463One) (h2 : Stage1463Two)
    (h4 : Stage1463Four) (hmain : Main1469) : Stage1469 :=
  stage1469_of_W (stage1469W_of_main h3 h1 h2 h4 hmain)

theorem stage1469W_of_main' (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three)
    (h4 : Stage1463Four) (hmain : Main1469) : Stage1469W :=
  stage1469W_of_main (stage1466_three_of h3) h1 h2 h4 hmain

theorem stage1469_of_main' (h1 : Stage1463One) (h2 : Stage1463Two) (h3 : Stage1463Three)
    (h4 : Stage1463Four) (hmain : Main1469) : Stage1469 :=
  stage1469_of_W (stage1469W_of_main' h1 h2 h3 h4 hmain)

end CFSG.Quasithin
