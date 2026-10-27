module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclG
public import CFSG.Quasithin.Vol2.Ch11SecA11Comp

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Mem

variable {G : Type} [Group G] [Finite G] {Y : Type} [Group Y] [Finite Y]
  {L SL : Subgroup G} {ρ : ↥L →* Y} {U : Subgroup Y} {P : Fin 2 → Subgroup Y}

theorem levUp_not_isSolvable (h : RkData L SL ρ U P) (j : Fin 2) :
    ¬ Group.IsSolvable ↥(levUp L ρ (P j)) := by
  intro hs
  let e : ↥(lev ρ (P j)) ≃* ↥(levUp L ρ (P j)) :=
    (lev ρ (P j)).equivMapOfInjective L.subtype L.subtype_injective
  have h1 : Group.IsSolvable ↥(lev ρ (P j)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact h.pkg.not_isSolvable_perfectCore j
    (Group.isSolvable_of_surjective (levHom_surjective h.surj _))

theorem inf_levUp_ne_bot (h : RkData L SL ρ U P) (hch : CharTwo L) (j : Fin 2) :
    pCoreOf 2 L ⊓ levUp L ρ (P j) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact inf_ne_bot_of_levi (levUp_le _) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    ((levUp_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    ((pCoreOf_le_parUp h j).trans (parUp_le_normalizer_levUp _)) hch (levUp_not_isSolvable h j)

theorem levUp_mem_lFamilyOf {G₁ S : Subgroup G} (hSG : IsSylowTwoOf S G₁) (hLG : L ≤ G₁)
    (h : RkData L SL ρ U P) (hch : CharTwo L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (j : Fin 2) (hSP : S ≤ Subgroup.normalizer (parUp L ρ (P j) : Set G)) :
    levUp L ρ (P j) ∈ lFamilyOf G₁ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := levUp L ρ (P j) with hA
  have hAG : A ≤ G₁ := (levUp_le _).trans hLG
  have hSA : S ≤ Subgroup.normalizer (A : Set G) := by
    rw [hA, ← perfectCore_parUp]
    exact hSP.trans (normalizer_le_normalizer_perfectCore _)
  have hSsyl : IsSylowTwoOf S (A ⊔ S) := A4.isSylowTwoOf_mono hSG le_sup_right (sup_le hAG hSG.1)
  have hAn : (A.subgroupOf (A ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hSA)
  obtain ⟨n, hn, -, hq⟩ := levUp_modO2 h j
  have hne : A ≠ ⊥ := by
    intro hb
    apply levUp_not_isSolvable h j
    rw [← hA, hb]
    infer_instance
  have hcc : A ∈ cComp (A ⊔ S) :=
    Vol2.Ch11.SecA.mem_cComp_of_quasisimple hne (levUp_perfect _) hq
      (A3.subnormal_of_normal le_sup_left hAn)
  refine ⟨hAG, hSsyl.2.1, hcc, hSsyl.2.2, ?_⟩
  have hSQ : S ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    hSL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hAQ : A ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    (levUp_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hN : A ⊔ S ≤ Subgroup.normalizer ((pCoreOf 2 L ⊓ A : Subgroup G) : Set G) :=
    sup_le (le_normalizer_inf hAQ Subgroup.le_normalizer) (le_normalizer_inf hSQ hSA)
  have h2 : IsPGroup 2 ↥(pCoreOf 2 L ⊓ A) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left
  have h3 : pCoreOf 2 L ⊓ A ≤ pCoreOf 2 (A ⊔ S) :=
    le_pCoreOf_of_le_normalizer (inf_le_right.trans le_sup_left) hN h2
  intro hb
  exact inf_levUp_ne_bot h hch j (le_bot_iff.1 (hb ▸ h3))

end Mem

end CFSG.Quasithin.Rk2
