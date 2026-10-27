module

public import CFSG.Quasithin.EmptyFaithful.S1421QA15Big
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Odd
public import CFSG.Quasithin.EmptyFaithful.S1421QA21Quot
public import CFSG.Quasithin.EmptyFaithful.S1421QA21Lie

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.QA21

@[expose] def Core3BigBorel : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Core3IsLieBig X →
    ∀ U : Subgroup X, IsSylowTwoOf U ⊤ → ∃ P : Fin 2 → Subgroup X, BorelPkg X U P

theorem core3BigParabolic_of_borel (hB : Core3BigBorel) : Core3BigParabolic := by
  intro G _ _ T M H K1 L M₁ c hq hbig _ y hy
  set S := S1421.sOf T K1 with hS
  set Y := yOfL22 T M with hY
  have hSG : S ≤ S1421.g0Of T M H K1 :=
    (le_sup_right : S ≤ Y ⊔ S).trans (S1421.yOfL22_sup_sOf_le_g0Of T M H K1)
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := hSG.trans c.g0Of_le_normalizer
  have hSK : S ≤ Subgroup.normalizer (K1 : Set G) := inf_le_right
  have hsyl : IsSylowTwoOf (S ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (S1421.isSylowTwoOf_g0 c.inM c.sylow) c.le_g0Of
      c.g0Of_le_normalizer
  have hDle : (Y ⊔ S) ⊓ L ≤ Y ⊔ T :=
    inf_le_left.trans (sup_le_sup_left S1421.sOf_le_T _)
  have hD : Group.IsSolvable ↥((Y ⊔ S) ⊓ L) := by
    have := S1421.isSolvable_yOfL22_sup c.st
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hDle)
      (Subgroup.inclusion_injective hDle)
  have hK1ns : ¬ Group.IsSolvable ↥K1 := not_isSolvable_of_mem_cComp c.st.notation_.cComp_mem
  have hcen : CFSG.pCore 2 ↥L ≤ Subgroup.center ↥L :=
    S1421.normal_isPGroup_le_center_of_isQuasisimple hq _ (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  obtain ⟨P, hPL, hK1P, hDP, hSLP, hSN⟩ := exists_parabolic_of_quotient hq hcen c.lt_L hK1ns hSL hSK
    hsyl inf_le_right (le_inf (inf_le_left.trans le_sup_right) inf_le_right) hD
    (fun U hU => hB _ hbig U hU)
  exact ⟨P, hPL, hK1P, hDP ⟨(le_sup_left : Y ≤ Y ⊔ S) hy.1, hy.2⟩, hSLP, hSN⟩

theorem core3BigBorel_holds :
    Core3BigBorel :=
  fun _ _ _ h _ hU => borelPkg_of_isLieBig h hU

theorem core3BigParabolic_holds :
    Core3BigParabolic :=
  core3BigParabolic_of_borel core3BigBorel_holds

end CFSG.Quasithin
