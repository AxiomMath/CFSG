module

public import CFSG.Quasithin.Background.RonanD38Top
public import CFSG.Quasithin.Background.SmithD39TwoSzHolds

public section

namespace CFSG.Quasithin.RonanD38

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

theorem d38_main :
    ∀ (W : Type) [CommGroup W] [Finite W] (M Mp T L : Subgroup (MulAut W)) (V : Subgroup W),
      D3Std M Mp T L V → ∀ n : ℕ, CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 n →
        qhatOf (autSub (Mp ⊔ T) (orbSup T V)) = ((2 : ℚ) : WithTop ℚ) ∧
        (∀ A : Subgroup (MulAut W), A ≤ T →
          autSub A (orbSup T V) ∈ QhatStar (autSub T (orbSup T V)) → A ≤ stabSub V) ∧
        ((Mp = L ∧ orbSup T V = V ∧ BinaryNaturalSz L V (V ⊓ fixV L) n) ∨
          (∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut W)) ∧ Mp = L ⊔ conjAutSub t L ∧
            ((BinaryNaturalSz L V (V ⊓ fixV L) n ∧
                IsSumMod (orbSup T V ⊓ fixV Mp) V (V.map t.toMonoidHom) (orbSup T V) ∧
                V = commSub (orbSup T V) L ∧ V ≤ fixV (conjAutSub t L) ∧
                fixV (conjAutSub t L) ⊓ orbSup T V = V ⊔ (orbSup T V ⊓ fixV Mp)) ∨
              (BinaryNaturalSz (conjAutSub t L) V (V ⊓ fixV (conjAutSub t L)) n ∧
                IsSumMod (orbSup T V ⊓ fixV Mp) V (V.map t⁻¹.toMonoidHom) (orbSup T V) ∧
                V = commSub (orbSup T V) (conjAutSub t L) ∧
                V ≤ fixV (conjAutSub t⁻¹ (conjAutSub t L)) ∧
                fixV (conjAutSub t⁻¹ (conjAutSub t L)) ⊓ orbSup T V =
                  V ⊔ (orbSup T V ⊓ fixV Mp))))) := by
  intro W _ _ M Mp T L V hD n hsz
  have h38 := Vol2.Ch10.SecA.a38ForSQTKCat_proved
  have h35 := H13.d35_proved
  have h36 := SmithD39Two.d36c_holds
  have h37 := d37_holds
  have hB45 := asB45_holds
  have hA21 := asA21SQTKSection
  have hF := Vol2.Ch10.SecA.facts10_1_holds
  have hcases := H13.d38_mp_cases h38 hD.hyp
  have hcen := H13.d38_center_eq_bot hD.hyp hcases hsz
  have hszL : CFSG.Blueprint.SuzukiModel ↥L 2 n := H13.suzukiModel_congr
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm hsz
  have hLs : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_2b2_simplicity ↥L 2 n hszL).2
  have hR := d38_restrict hD
  have htopR := d38_restrict_orbSup T V
  have hszR := d38_restrict_suzuki hD hLs hcen hszL
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [← d38_restrict_qhatOf hD]
    exact SmithD39Two.d38Top_holds _ _ _ _ _ _ hR htopR hszR
  ·
    intro A hAT hQ
    by_cases hVY : V = orbSup T V
    · have h1 : A ≤ stabSub (orbSup T V) := hAT.trans (le_stabSub_orbSup T V)
      rwa [← hVY] at h1
    · have hVne : V.subgroupOf (orbSup T V) ≠ ⊤ := fun h =>
        hVY (le_antisymm (le_orbSup T V) (Subgroup.subgroupOf_eq_top.mp h))
      obtain ⟨r, -, hr2, ⟨⟨hA2, hrA⟩, hA3⟩, -⟩ := hQ
      have hle := d38_qstar_top h38 h35 h36 hB45 hA21 hF hR htopR hVne hszR
        (autSub_mono hAT (orbSup T V)) hA2.isElemAbelian2 hA3 (hrA.trans hr2)
      exact d38_restrict_stabSub (hAT.trans (le_stabSub_orbSup T V)) (le_orbSup T V) hle
  · rcases hcases with hMp | ⟨t, htT, htn, hMp⟩
    · obtain ⟨hVT, hBN⟩ := d38_eq_case h35 hB45 hA21 hF hD hMp hLs hszL
      exact Or.inl ⟨hMp, hVT, hBN⟩
    · refine Or.inr ⟨t, htT, htn, hMp, ?_⟩
      have hlt := d38_lt_of_pair h37 hD htT htn hMp hszL
      rcases h36 W M Mp T L V hD hlt t htT htn hMp with hc | hc
      · exact Or.inl (d38_pair hB45 hA21 hF hD htT htn hMp hszL hc)
      ·
        have hMp' : Mp = conjAutSub t L ⊔ conjAutSub t⁻¹ (conjAutSub t L) := by
          rw [conjAutSub_inv_conjAutSub, sup_comm]
          exact hMp
        have hstd' : D3Std M Mp T (conjAutSub t L) V := ⟨hD.hyp.conj htT, hD.qhat, hD.irrT⟩
        let e := Subgroup.equivMapOfInjective L (MulAut.conj t).toMonoidHom
          (MulAut.conj t).injective
        have hsz' : CFSG.Blueprint.SuzukiModel ↥(conjAutSub t L) 2 n :=
          H13.suzukiModel_congr e.symm hszL
        exact Or.inr (d38_pair hB45 hA21 hF hstd' (T.inv_mem htT)
          (not_mem_normalizer_conjAutSub htn) hMp' hsz' hc)

end CFSG.Quasithin.RonanD38
