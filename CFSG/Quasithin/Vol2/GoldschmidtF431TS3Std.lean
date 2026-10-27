module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TS3Assemble
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.NF
open scoped commutatorElement

section Orient

structure StdOrient3 (C : Type) [Group C] (P P' : Subgroup C) (z t : C) : Prop where
  cz : Subgroup.centralizer ({z} : Set C) ≤ P
  ct : Subgroup.centralizer ({t} : Set C) ≤ P'
  nz : ¬ Subgroup.centralizer ({z} : Set C) ≤ P'
  nt : ¬ Subgroup.centralizer ({t} : Set C) ≤ P
  Zperf : z ∈ centerOf (perfectCore P)
  F1 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ({z} : Set C))
  F2 : 3 ∣ Nat.card ↥⁅Subgroup.centralizer ({t} : Set C), Subgroup.centralizer ({t} : Set C)⁆

variable {D C : Type} [Group D] [Group C] (ε : D ≃* C)

theorem orientD3_of_std3 {P P' : Subgroup C} {z t : C} (S : StdOrient3 C P P' z t)
    {Q Q' : Subgroup D} (hQP : Q.map ε.toMonoidHom = P) (hQP' : Q'.map ε.toMonoidHom = P') :
    OrientD3 Q Q' (ε.symm z) (ε.symm t) where
  cz := (centralizer_le_transport ε hQP z).mpr S.cz
  ct := (centralizer_le_transport ε hQP' t).mpr S.ct
  nz h := S.nz ((centralizer_le_transport ε hQP' z).mp h)
  nt h := S.nt ((centralizer_le_transport ε hQP t).mp h)
  Zperf := by
    have hperf : perfectCore P = (perfectCore Q).map ε.toMonoidHom := by
      rw [← hQP]
      exact perfectCore_map_of_injective ε.toMonoidHom ε.injective Q
    have hcenter : centerOf (perfectCore P) = (centerOf (perfectCore Q)).map ε.toMonoidHom := by
      rw [hperf]
      exact centerOf_map_of_injective ε.toMonoidHom ε.injective _
    have h1 := S.Zperf
    rw [hcenter] at h1
    exact (mem_symm_iff_of_map_eq ε rfl).mpr h1
  F1 := by
    have h := map_centralizer_singleton ε (ε.symm z)
    rw [MulEquiv.apply_symm_apply] at h
    have hc : Nat.card ↥(Subgroup.centralizer ({ε.symm z} : Set D)) =
        Nat.card ↥(Subgroup.centralizer ({z} : Set C)) := by
      rw [← Subgroup.card_map_of_injective (f := ε.toMonoidHom) ε.injective, h]
    rw [hc]
    exact S.F1
  F2 := by
    have h := map_centralizer_singleton ε (ε.symm t)
    rw [MulEquiv.apply_symm_apply] at h
    have hc : Nat.card ↥⁅Subgroup.centralizer ({ε.symm t} : Set D),
        Subgroup.centralizer ({ε.symm t} : Set D)⁆ =
        Nat.card ↥⁅Subgroup.centralizer ({t} : Set C), Subgroup.centralizer ({t} : Set C)⁆ := by
      rw [← Subgroup.card_map_of_injective (f := ε.toMonoidHom) ε.injective,
        Subgroup.map_commutator, h]
    rw [hc]
    exact S.F2

include ε in
theorem commutator_aut_mem_range_of_equiv
    (hF3 : ∀ x y : MulAut C, ⁅x, y⁆ ∈ (MulAut.conj : C →* MulAut C).range) :
    ∀ x y : MulAut D, ⁅x, y⁆ ∈ (MulAut.conj : D →* MulAut D).range := by
  intro x y
  obtain ⟨c, hc⟩ := hF3 (MulAut.congr ε x) (MulAut.congr ε y)
  refine ⟨ε.symm c, ?_⟩
  apply (MulAut.congr ε).injective
  rw [congr_conj ε, MulEquiv.apply_symm_apply, hc, map_commutatorElement]

end Orient

section Final

variable {D C : Type} [Group D] [Group C] [Finite D] {G : Type} [Group G] [Finite G]
  {M1 M2 : Subgroup G} (E : LieExt D M1 M2) (ε : D ≃* C)

theorem f431Local_of_std3 {U P P' : Subgroup C} {z t : C} {V L : Subgroup C}
    (S1 : StdTwo C U P P' z t) (S2 : StdLoc C U z t V L) (S3 : StdOrient3 C P P' z t)
    {Q Q' : Subgroup D} (hQ : (Q = E.P1 ∧ Q' = E.P2) ∨ (Q = E.P2 ∧ Q' = E.P1))
    (hQP : Q.map ε.toMonoidHom = P) (hQP' : Q'.map ε.toMonoidHom = P')
    (hU : E.TD.map ε.toMonoidHom = U) (hcen : Subgroup.center D = ⊥)
    (hgen : (MulAut.conj : D →* MulAut D).range ≤ E.K)
    (hodd : ¬ 2 ∣ (iK E.toLieAmalgamExt hgen).range.index)
    (hF3 : ∀ x y : MulAut C, ⁅x, y⁆ ∈ (MulAut.conj : C →* MulAut C).range)
    (hag : ∀ E' : Subgroup ↥E.K, IsAGMember (E.TD.map (iK E.toLieAmalgamExt hgen)) E' →
      Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb1 ∨ Subgroup.normalizer (E' : Set ↥E.K) ≤ E.Mb2)
    (hyp1 : ∀ w ∈ centerOf (perfectCore M1), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M1)
    (hyp2 : ∀ w ∈ centerOf (perfectCore M2), orderOf w = 2 →
      Subgroup.centralizer ({w} : Set G) ≤ M2) :
    ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
        ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
      (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
        Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2) := by
  refine f431Local_of_dlevel3 E hcen hgen hodd
    (twoClassD_of_std E.toLieAmalgamExt ε S1 hQ hQP hQP' hU)
    (locD_of_std E.toLieAmalgamExt ε S2 hU) (commutator_aut_mem_range_of_equiv ε hF3) hag hyp1
    hyp2 ?_
  rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (orientD3_of_std3 ε S3 hQP hQP')
  · exact Or.inr (orientD3_of_std3 ε S3 hQP hQP')

end Final

end CFSG.Quasithin.H13.F431.Lift
