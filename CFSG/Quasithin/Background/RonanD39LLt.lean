module

public import CFSG.Quasithin.Background.SmithD321Main
public import CFSG.Quasithin.Background.SmithD321CaseI
public import CFSG.Quasithin.Background.SmithD39TwoSzHolds
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DiscList

public section

namespace CFSG.Quasithin.RonanD39

private theorem ne_bot_of_d3Std {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M Mp T L V) : V ≠ ⊥ := by
  rintro rfl
  obtain ⟨-, -, hlt, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  exact not_lt_bot hlt

private theorem caseII_concl (h36 : D36c) {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M Mp T L V)
    (hVc : V = commSub V L) (hlt : commSub V L < commSub (orbSup T V) L) {t : MulAut W}
    (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) :
    V < orbSup T V ∧ D36cConcl Mp T L V t ∧ commSub (orbSup T V) L ≠ V := by
  have hVT : V < orbSup T V :=
    lt_of_le_of_ne (le_orbSup T V) fun h => hlt.ne (congrArg (fun X => commSub X L) h)
  refine ⟨hVT, ?_, fun h => hlt.ne' (h.trans hVc)⟩
  rcases h36 W M Mp T L V hD hVT t htT htn hMp with hc | hc
  · exact hc
  · refine absurd (hVc.trans (commSub_eq_bot_iff.2 fun v hv => mem_fixV.2 fun g hg => ?_))
      (ne_bot_of_d3Std hD)
    exact hc.1 v hv g (by rwa [conjAutSub_inv_conjAutSub])

private theorem three_dvd_card (h36 : D36c) (h37 : D37) {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hB : SmithD321.D321Base M Mp T L V t)
    (hcase : V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L)) :
    3 ∣ Nat.card ↥L := by
  rcases hcase with hVT | ⟨hVc, hlt⟩
  · exact hB.three_dvd_of_d37 h37 hVT
  · obtain ⟨-, hc, hne⟩ := caseII_concl h36 hB.hD hVc hlt hB.htT hB.htn hB.hMp
    exact hB.three_dvd_of_caseIIb hc hne

theorem d39_llt_of (h36 : D36c) (h37 : D37) (hL38 : D3L38)
    (h38 : D38Top) (hA23 : A23SQTKListFact) (hSzF : H13.SimpleThreePrimeSuzukiFact)
    (h56 : AsB56) {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (hcase : V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L))
    {t : MulAut W} (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) :
    orbSup T V = ⊤ ∧ ∀ A ∈ QhatStar M, A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ := by
  have hB := SmithD321.d321Base_of hL38 hD htT htn hMp
  have h3L := three_dvd_card h36 h37 hB hcase
  have hAC : ∀ A ∈ QhatStar M, A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ := by
    intro A hA
    obtain ⟨r, hr, hr2, -⟩ := QhatStar_spec hA
    exact SmithD321.inf_cent_eq_bot h38 hA23 hSzF hD hr hr2 hA
      (fun _ hp hp5 => hB.commutator_pCoreOf_eq_bot hr hA hp hp5)
      (fun _ hx hx3 => hB.eq_one_of_pow_prime Nat.prime_three (by norm_num) h3L hx hx3)
  refine ⟨?_, hAC⟩
  by_contra htop
  obtain ⟨A, r, hS⟩ := hB.exists_sit hqM htop
  rcases hcase with hVT | ⟨hVc, hlt⟩
  · exact SmithD321.caseI_false h56 h37 hS hVT (hAC A hS.hAQ)
  · obtain ⟨-, hc, hne⟩ := caseII_concl h36 hD hVc hlt htT htn hMp
    exact SmithD321.caseIIb_false hS hc hne (hAC A hS.hAQ)

theorem d39_llt
    {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    (hD : D3Std M Mp T L V) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (hcase : V = orbSup T V ∨ (V = commSub V L ∧ commSub V L < commSub (orbSup T V) L))
    {t : MulAut W} (htT : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) :
    orbSup T V = ⊤ ∧ ∀ A ∈ QhatStar M, A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) = ⊥ :=
  d39_llt_of SmithD39Two.d36c_holds d37_holds (d3L38_of_a38 d3A38_holds)
    SmithD39Two.d38Top_holds a23SQTKListFact H13.simpleThreePrimeSuzukiFact asB56_holds hD hqM
    hcase htT htn hMp

end CFSG.Quasithin.RonanD39
