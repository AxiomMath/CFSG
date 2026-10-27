module

public import CFSG.Quasithin.Background.Harris.R1.J2VertTab
public import CFSG.Quasithin.Background.Harris.R1.J2VertHom
public import CFSG.Quasithin.Background.Harris.R1.J2VertPres
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import Certificates.Certificate300202

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.ComponentClassification.J2Cover CFSG.CosetTable CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

@[expose] noncomputable def baseP : Fin 3 → Equiv.Perm (Fin 315)
  | 0 => permA
  | 1 => permB
  | 2 => permU

@[expose] def rBase : Array (Array ℕ) := #[autStrong[0]!, autStrong[1]!, outerArr]

theorem rep_baseP (k : Fin 3) :
    Rep 315 (rBase.getD k.val (idA 315)) (baseP k) := by
  fin_cases k
  · exact rep_strong (j := 0) (by norm_num)
  · exact rep_strong (j := 1) (by norm_num)
  · exact rep_permU

@[expose] noncomputable def rGen (i : Fin 8) : Equiv.Perm (Fin 315) :=
  ((rWord i).map baseP).prod

theorem baseP_mem_R (k : Fin 3) : baseP k ∈ R := by
  fin_cases k
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact permU_mem_R

theorem rGen_mem_R (i : Fin 8) : rGen i ∈ R :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact baseP_mem_R k

theorem rGenArrs_getD (i : Fin 8) :
    (rGenArrs 315 rBase).getD i.val (idA 315) = evalW 315 rBase (rWord i) := by
  have hi : i.val < (List.range 8).length := by simp
  simp [rGenArrs, rWord, Array.getD_eq_getD_getElem?]

theorem rep_rGen (i : Fin 8) :
    Rep 315 ((rGenArrs 315 rBase).getD i.val (idA 315)) (rGen i) := by
  rw [rGenArrs_getD]
  exact rep_evalW rep_baseP (rWord i)

theorem rGenArrs_size : (rGenArrs 315 rBase).size = 8 := by simp [rGenArrs]

theorem rGen_relCheck :
    relCheck 315 (rGenArrs 315 #[autStrong[0]!, autStrong[1]!, outerArr]) (vRels true) = true :=
  Certificates.certificate300202.1

theorem rGen_tabLower :
    tabLower 315 (rGenArrs 315 #[autStrong[0]!, autStrong[1]!, outerArr]) tabR 3840 = true :=
  Certificates.certificate300202.2

theorem rGen_rels :
    ∀ r ∈ vRels true, (r.map fun p => if p.2 then rGen p.1 else (rGen p.1)⁻¹).prod = 1 :=
  prod_eq_one_of_relCheck rep_rGen rGen_relCheck

@[expose] noncomputable def rHom :
    PG 8 (vRels true) →* Equiv.Perm (Fin 315) :=
  pgHom rGen_rels

theorem range_rHom_eq :
    rHom.range = Subgroup.closure (Set.range rGen) :=
  range_pgHom rGen_rels

theorem range_rHom_le_R :
    rHom.range ≤ R := by
  rw [range_rHom_eq, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact rGen_mem_R i

theorem le_card_closure_rGen :
    3840 ≤ Nat.card (Subgroup.closure (Set.range rGen)) := by
  refine le_card_of_tabLower (gs := rGenArrs 315 rBase) (pl := tabR)
    (good_of_getD (k := 8) rGenArrs_size fun i hi => ?_)
    rGen_tabLower
  have := rep_rGen ⟨i, hi⟩
  refine ⟨?_, rGen ⟨i, hi⟩, Subgroup.subset_closure ⟨_, rfl⟩, this⟩
  rw [rGenArrs_getD ⟨i, hi⟩]
  exact size_evalW _ _

theorem rHom_injective :
    Function.Injective rHom :=
  pgHom_injective rGen_rels (card_PG_le true).1 (card_PG_le true).2 le_card_closure_rGen

end CFSG.Quasithin.Background.Harris.R1.J2Vert
