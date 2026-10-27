module

public import CFSG.Quasithin.Background.SmithD321CaseI
public import CFSG.Quasithin.Background.SmithD321Count
public import CFSG.Quasithin.Background.SmithD321Main

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
  CFSG.Quasithin.SmithD391 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open

variable {W : Type} [CommGroup W] [Finite W]

theorem sit_le_normalizer_L (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (h36 : D36c) (h37 : D37) (hB56 : AsB56) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} (hS : D321Sit M Mp T L V t A r)
    (h3L : 3 ∣ Nat.card ↥L) : A ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hAC := hS.inf_cent_eq_bot_of_three_dvd h38 hA23 hSzF h3L
  have hlt : V < orbSup T V := by
    rcases (le_orbSup T V).eq_or_lt with hVT | hlt
    · exact (caseI_false hB56 h37 hS hVT hAC).elim
    · exact hlt
  rcases h36 W M Mp T L V hS.hD hlt t hS.htT hS.htn hS.hMp with hc | hc
  · exact le_normalizer_of_count hA21 hB42 h9 hS hc.1 hAC
  · have h1 := le_normalizer_of_count hA21 hB42 h9 hS.swap hc.1 hAC
    have h2 := le_normalizer_Lt hS.swap h1
    rwa [conjAutSub_inv_conjAutSub] at h2

theorem mem_normalizer_of_Lt {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} (hB : D321Base M Mp T L V t) {g : MulAut W} (hg : g ∈ M)
    (hgLt : g ∈ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W))) :
    g ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
  by_contra hgL
  have h1 := (hB.conj_swap hg hgL).2
  rw [mem_normalizer_iff_conjAutSub.1 hgLt] at h1
  exact hB.Lt_ne h1

theorem qhatStar_le_normalizer_of_d321 (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (h36 : D36c) (h37 : D37) (hB56 : AsB56) (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} (hB : D321Base M Mp T L V t) (htop : orbSup T V ≠ ⊤)
    (h3L : 3 ∣ Nat.card ↥L) {A₁ : Subgroup (MulAut W)} (hA₁ : A₁ ∈ QhatStar M) :
    A₁ ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  obtain ⟨r, hr, hr2, -, -⟩ := QhatStar_spec hA₁
  have hA₁2 : IsPGroup 2 ↥A₁ := by
    obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA₁
    exact hA2.isElemAbelian2.isPGroup
  obtain ⟨x, hx, hA₁x⟩ := F7.isSylowTwoOf_exists_conj_le hB.hD.hyp.sylow (QhatStar_le hA₁) hA₁2
  set A := conjBy x⁻¹ A₁ with hAdef
  have hAQ : A ∈ QhatStar M := conjBy_mem_QhatStar hA₁ (M.inv_mem hx)
  have hAT : A ≤ T := by
    intro y hy
    rw [mem_conjBy_iff, inv_inv] at hy
    have := hA₁x hy
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  obtain ⟨r', hr', -, ⟨⟨-, hAr'⟩, -⟩, -⟩ := QhatStar_spec hAQ
  have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
  rw [hrr] at hAr'
  have hS : D321Sit M Mp T L V t A r := ⟨hB, hr, hr2, htop, hAQ, hAT, hAr'⟩
  have hAL := sit_le_normalizer_L hA21 hB42 h9 h36 h37 hB56 h38 hA23 hSzF hS h3L
  intro a ha
  have haM : a ∈ M := QhatStar_le hA₁ ha
  have hya : x⁻¹ * a * x ∈ A := by
    rw [hAdef, mem_conjBy_iff, inv_inv]
    simpa [mul_assoc] using ha
  have h1 := mem_normalizer_iff_conjAutSub.1 (hAL hya)
  rw [conjAutSub_mul, conjAutSub_mul] at h1
  have h2 := congrArg (conjAutSub x) h1
  have hxx : ∀ Z : Subgroup (MulAut W), conjAutSub x (conjAutSub x⁻¹ Z) = Z := fun Z => by
    simpa using conjAutSub_inv_conjAutSub Z x⁻¹
  rw [hxx] at h2
  have ha' : a ∈ Subgroup.normalizer ((conjAutSub x L : Subgroup (MulAut W)) :
      Set (MulAut W)) := mem_normalizer_iff_conjAutSub.2 h2
  rcases hB.conj_cases hx with h | h
  · rwa [h] at ha'
  · rw [h] at ha'
    exact mem_normalizer_of_Lt hB haM ha'

end CFSG.Quasithin.H13.T326
