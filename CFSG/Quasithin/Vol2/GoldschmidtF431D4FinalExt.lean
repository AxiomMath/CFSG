module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4FinalCent
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4ExtInn
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4Clause
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4D3Glue

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.Quasithin.H13.F431
  CFSG.Quasithin.H13.F431.U42.Am

section ZeroData

variable
  {G : Type} [Group G] [Finite G]
  {M1 M2 : Subgroup G}

theorem d4_zeroData (hs : IsSimpleGroup D) (E : LieExt D M1 M2) (hP1 : E.P1 = d4H)
    (hZ : Function.Injective (MulAut.conj : D →* MulAut D))
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index) {z : G}
    (hzr : z ∈ twoPrimeResidual M1)
    (hzc : z ∈ Subgroup.centralizer (twoPrimeResidual M1 : Set G)) (hz2 : z ^ 2 = 1)
    (hz : z ≠ 1) :
    ((E.phi1 ⟨z, twoPrimeResidual_le M1 hzr⟩ : ↥E.N1) : MulAut D) = MulAut.conj d4z := by
  obtain ⟨n, hn, hn1, -, -, hnc⟩ := E.exists_zero_data_inn hZ hodd hzr hzc hz2 hz
  have hnz : n = d4z := eq_d4z_of_comm_U hs (by rw [hP1]; exact d4U_le_d4B.trans inf_le_left) hn1
    hnc
  rw [hn, hnz]

end ZeroData

section TopIso

variable {G : Type} [Group G] {M1 M2 : Subgroup G}

@[expose] noncomputable def isoOfTop (E : LieExt D M1 M2) (hM : E.Mbar = ⊤) (hP1 : E.P1 = d4H)
    (hP2 : E.P2 = d4N) :
    (RankTwoAmalgam.ofSubgroups (autStab d4H) (autStab d4N)).Iso
      (RankTwoAmalgam.ofSubgroups M1 M2) :=
  isoTrans (ofSubgroupsCongr (by rw [hM, hP1, top_inf_eq]) (by rw [hM, hP2, top_inf_eq]))
    (isoSymm E.iso)

theorem isoOfTop_V1 (E : LieExt D M1 M2) (hM : E.Mbar = ⊤) (hP1 : E.P1 = d4H)
    (hP2 : E.P2 = d4N) {m : ↥M1} (a : ↥(autStab d4H))
    (h : ((E.phi1 m : ↥E.N1) : MulAut D) = (a : MulAut D)) :
    d4IsoV1 (isoOfTop E hM hP1 hP2) a = m := by
  apply E.iso.φ1.injective
  exact (E.iso.φ1.apply_symm_apply _).trans (Subtype.ext h.symm)

@[expose] def D3ClauseVacuous : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G)
    (e : (RankTwoAmalgam.ofSubgroups (autStab d4H) (autStab d4N)).Iso
      (RankTwoAmalgam.ofSubgroups M₁ M₂)),
    ((d4IsoV1 e d3ZH : ↥M₁) : G) = z → Subgroup.centralizer ({z} : Set G) ≤ M₁ →
      IsSimpleGroup G → False

end TopIso

section Cases

variable
  {G : Type} [Group G] [Finite G] {M1 M2 : Subgroup G}

theorem clause_of_iso (hF424 : D4F424) (hNF : D4NonFusion d4ZH d4TH)
    (hLoc : D4LocalCent d4ZH d4TH) {A B : Subgroup D} (hA : A = d4H) (hB : B = d4N)
    (e : (RankTwoAmalgam.ofSubgroups A B).Iso (RankTwoAmalgam.ofSubgroups M1 M2)) (hz : d4z ∈ A)
    {z : G} (hez : ((d4IsoV1 e ⟨d4z, hz⟩ : ↥M1) : G) = z)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ M1) : Nonempty (G ≃* D) := by
  subst hA hB
  exact d4_clause_of_inputs hF424 hNF hLoc G M1 M2 z e hez hcent

theorem d4_case_inn (hs : IsSimpleGroup D) (hF424 : D4F424) (hNF : D4NonFusion d4ZH d4TH)
    (hLoc : D4LocalCent d4ZH d4TH) (E : LieExt D M1 M2)
    (hM : E.Mbar = (MulAut.conj : D →* MulAut D).range) (hP1 : E.P1 = d4H) (hP2 : E.P2 = d4N)
    (hZ : Function.Injective (MulAut.conj : D →* MulAut D))
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index) {z : G}
    (hzr : z ∈ twoPrimeResidual M1)
    (hzc : z ∈ Subgroup.centralizer (twoPrimeResidual M1 : Set G)) (hz2 : z ^ 2 = 1)
    (hz : z ≠ 1) (hcent : Subgroup.centralizer ({z} : Set G) ≤ M1) : Nonempty (G ≃* D) := by
  have hSelf1 : ∀ g : D, (∀ x, x ∈ E.P1 ↔ g * x * g⁻¹ ∈ E.P1) → g ∈ E.P1 := by
    rw [hP1]
    exact d4_hHH hs
  have hSelf2 : ∀ g : D, (∀ x, x ∈ E.P2 ↔ g * x * g⁻¹ ∈ E.P2) → g ∈ E.P2 := by
    rw [hP2]
    exact d4_hNN hs
  obtain ⟨e, he⟩ := E.exists_innIso hM hZ hSelf1 hSelf2
  have hdz : d4z ∈ E.P1 := by
    rw [hP1]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have key := he ⟨z, twoPrimeResidual_le M1 hzr⟩ d4z hdz
    (d4_zeroData hs E hP1 hZ hodd hzr hzc hz2 hz)
  exact clause_of_iso hF424 hNF hLoc hP1 hP2 e hdz key hcent

theorem d4_case_top (hs : IsSimpleGroup D) (hD3 : D3ClauseVacuous) (hG : IsSimpleGroup G)
    (E : LieExt D M1 M2) (hM : E.Mbar = ⊤) (hP1 : E.P1 = d4H) (hP2 : E.P2 = d4N)
    (hZ : Function.Injective (MulAut.conj : D →* MulAut D))
    (hodd : ¬ 2 ∣ (MulAut.conj : D →* MulAut D).range.index) {z : G}
    (hzr : z ∈ twoPrimeResidual M1)
    (hzc : z ∈ Subgroup.centralizer (twoPrimeResidual M1 : Set G)) (hz2 : z ^ 2 = 1)
    (hz : z ≠ 1) (hcent : Subgroup.centralizer ({z} : Set G) ≤ M1) : False :=
  hD3 G M1 M2 z (isoOfTop E hM hP1 hP2)
    (congrArg Subtype.val (isoOfTop_V1 E hM hP1 hP2 (m := ⟨z, twoPrimeResidual_le M1 hzr⟩) d3ZH
      ((d4_zeroData hs E hP1 hZ hodd hzr hzc hz2 hz).trans d3ZH_val.symm))) hcent hG

end Cases

end CFSG.Quasithin.D4Hex
