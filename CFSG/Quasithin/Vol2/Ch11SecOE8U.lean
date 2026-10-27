module

public import CFSG.Quasithin.Vol2.Ch11SecOE8T
public import CFSG.Quasithin.Vol2.Ch11SecOE7P
public import CFSG.Quasithin.Vol2.Ch11SecOE7A
public import CFSG.Quasithin.Vol2.Ch11SecOE8S

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3 CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_psl3_of_twisted {T : Subgroup G}
    (h : AlmostSimple (CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hLT : CFSG.generalizedFitting G ⊔ T = ⊤) {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (e : ↥(CFSG.generalizedFitting G) ≃* projectiveSL 3 K)
    (htw : E2.IsDiagramNontrivial T (CFSG.generalizedFitting G)
      (T ⊓ CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ n := by
  set L := CFSG.generalizedFitting G with hLdef
  have hLn : L.Normal := h.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e', he'⟩ := L3T.exists_equiv_map_eq_U hT e
  set U := (T ⊓ L).subgroupOf L with hUdef
  have hUe : (projUnitriangular 3 K).map e'.symm.toMonoidHom = U := by
    rw [← he', Subgroup.map_map]
    convert Subgroup.map_id U
    ext x
    simp
  have pkg := (Rk2.rank2Pkg_proj3 hK hn).map e'.symm
  rw [show (unitriangular 3 K).map (proj 3 K) = projUnitriangular 3 K from rfl, hUe] at pkg
  set D := Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) with hD
  have hTD : T ≤ D := SecE3.le_normalizer_inf
  have hDs : Group.IsSolvable ↥D := by
    set P01 := (fun j : Fin 2 => ((Q3 K j).map (proj 3 K)).map e'.symm.toMonoidHom) 0 ⊓
      (fun j : Fin 2 => ((Q3 K j).map (proj 3 K)).map e'.symm.toMonoidHom) 1 with hP01
    have hP01s : Group.IsSolvable ↥P01 := pkg.res.2.2.2.1
    have hle : D ⊓ L ≤ P01.map L.subtype := by
      intro x hx
      obtain ⟨hxN, hxL⟩ := Subgroup.mem_inf.mp hx
      have hxU : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer (U : Set ↥L) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [hUdef, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact Subgroup.mem_normalizer_iff.mp hxN y
      exact ⟨⟨x, hxL⟩, ⟨pkg.norm 0 hxU, pkg.norm 1 hxU⟩, rfl⟩
    have hims : Group.IsSolvable ↥(P01.map L.subtype) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (P01.equivMapOfInjective L.subtype L.subtype_injective).symm.toMonoidHom)
        (MulEquiv.injective _)
    exact isSolvable_of_inf h.two
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
  have hDE : E1.InEFor n D T := by
    have h1 : E1.InE 1 D :=
      (E1.nParam_le_iff Nat.one_pos).mp (by simpa using E1.solvable_nParam_le_one hDs)
    exact (h1 T (B6.isSylowTwoOf_mono hT hTD le_top)).mono (by omega)
  have htop : ∀ X Y : Subgroup G, X ≤ L → ¬ Group.IsSolvable ↥X → D ⊔ (X ⊔ Y) = ⊤ := by
    intro X Y hXL hXs
    refine eq_top_of_not_isSolvable_of_isDiagramNontrivial hT hLT pkg.res pkg.norm htw
      (hTD.trans le_sup_left) fun hs => hXs ?_
    have hXle : X ≤ (D ⊔ (X ⊔ Y)) ⊓ L := le_inf (le_sup_left.trans le_sup_right) hXL
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXle)
  have hInE := inEFor_top_of_conj_sup hT hTD hDE
    (fun A _ hA1 hc => SecE3.isE_top_of_card_le h hT hA1 hc) fun A hAT hA hc => ?_
  · exact (E1.nParam_le_iff (by omega)).mpr ((E1.inE_iff_inEFor hT).mpr hInE)
  refine ⟨1, by rwa [A1b.conjSub_one], ?_⟩
  rw [A1b.conjSub_one]
  by_cases hsemi : ∀ t ∈ T, (∀ a ∈ A, t * a = a * t) →
      L3T.actHom e' t ∈ semilinearAutGroup 3 K
  · obtain ⟨X, hXL, hXs, hE⟩ := L3T.member_of_semilinear h hT hn hK e' he' hAT hA hc hsemi
    exact ⟨_, hE, htop X _ hXL hXs⟩
  · push Not at hsemi
    obtain ⟨t, htT, htA, htE⟩ := hsemi
    obtain ⟨L₀, hL₀L, hL₀s, hE⟩ := L3T.member_of_twisted h hT hn hK e' he' hAT hA hc htT htA htE
    exact ⟨_, hE, htop L₀ _ hL₀L hL₀s⟩

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
