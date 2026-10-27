module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

theorem kq_le_kq_of_le216 {X G : Subgroup (MulAut V)} (h : G ≤ X) (k : ℕ) : kq X k ≤ kq G k := by
  by_cases htop : kq G k = ⊤
  · rw [htop]
    exact le_top
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨A, hA, hAk, hAa⟩ := (kq_eq_coe_iff.mp ha.symm).1
    rw [← ha]
    exact kq_le_iff.mpr ⟨A, ⟨hA.1.trans h, hA.2⟩, hAk, hAa.le⟩

omit [Finite V] in
theorem kRle_eq_of_le216 {X G : Subgroup (MulAut V)} (h : G ≤ X) (k : ℕ) (r : ℚ) :
    kRle G k r = {A | A ∈ kRle X k r ∧ A ≤ G} := by
  ext A
  constructor
  · rintro ⟨⟨hA, hr⟩, hAk⟩
    exact ⟨⟨⟨⟨hA.1.trans h, hA.2⟩, hr⟩, hAk⟩, hA.1⟩
  · rintro ⟨⟨⟨hA, hr⟩, hAk⟩, hAG⟩
    exact ⟨⟨⟨hAG, hA.2⟩, hr⟩, hAk⟩

theorem qhatOf_eq_of_le216 {X G : Subgroup (MulAut V)} {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) (hAG : A ≤ G) (hG : G ≤ X) :
    qhatOf G = (r : WithTop ℚ) := by
  obtain ⟨r', hr', -, ⟨⟨hA2, hAr⟩, hAk⟩, -⟩ := QhatStar_spec hA
  have hrr : r' = r := by
    have : (r' : WithTop ℚ) = r := hr'.symm.trans hr
    exact_mod_cast this
  subst hrr
  refine le_antisymm ?_ (hr ▸ kq_le_kq_of_le216 hG 3)
  exact kq_le_iff.mpr ⟨A, ⟨hAG, hA2.2⟩, hAk, hAr.le⟩

theorem QhatStar_of_le216 {X G : Subgroup (MulAut V)} {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {A₀ : Subgroup (MulAut V)} (hA₀ : A₀ ∈ QhatStar X) (hA₀G : A₀ ≤ G)
    (hG : G ≤ X) : QhatStar G = {A | A ∈ QhatStar X ∧ A ≤ G} := by
  have hrG := qhatOf_eq_of_le216 hr hA₀ hA₀G hG
  ext A
  constructor
  · rintro ⟨r'', hr'', -, hAk, hmin⟩
    have hrr : r'' = r := by
      have : (r'' : WithTop ℚ) = r := hr''.symm.trans hrG
      exact_mod_cast this
    subst hrr
    rw [kRle_eq_of_le216 hG] at hAk hmin
    exact ⟨⟨r'', hr, hr2, hAk.1, fun B hB hBA => hmin B ⟨hB, hBA.trans hAk.2⟩ hBA⟩, hAk.2⟩
  · rintro ⟨⟨r'', hr'', -, hAk, hmin⟩, hAG⟩
    have hrr : r'' = r := by
      have : (r'' : WithTop ℚ) = r := hr''.symm.trans hr
      exact_mod_cast this
    subst hrr
    refine ⟨r'', hrG, hr2, ?_, fun B hB hBA => hmin B ?_ hBA⟩
    · rw [kRle_eq_of_le216 hG]
      exact ⟨hAk, hAG⟩
    · rw [kRle_eq_of_le216 hG] at hB
      exact hB.1

theorem Jhat_eq_of_gen216 {X G : Subgroup (MulAut V)} {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {Q : Set (Subgroup (MulAut V))} (hQ : Q ⊆ QhatStar X) (hQne : Q.Nonempty)
    (hG : G = ⨆ A ∈ Q, A) : Jhat G = G := by
  have hGX : G ≤ X := by
    rw [hG]
    refine iSup₂_le fun A hA => ?_
    obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec (hQ hA)
    exact hA2.le
  obtain ⟨A₀, hA₀⟩ := hQne
  have hA₀G : A₀ ≤ G := hG ▸ le_iSup₂ (f := fun A (_ : A ∈ Q) => A) A₀ hA₀
  have hset := QhatStar_of_le216 hr hr2 (hQ hA₀) hA₀G hGX
  apply le_antisymm (Jhat_le G)
  rw [hG]
  refine iSup₂_le fun A hA => ?_
  have hAG : A ≤ G := hG ▸ le_iSup₂ (f := fun A (_ : A ∈ Q) => A) A hA
  have hmem : A ∈ QhatStar G := by
    rw [hset]
    exact ⟨hQ hA, hAG⟩
  exact le_Jhat hmem |>.trans (by rw [← hG])

theorem le_of_mem_QhatStar216 {X A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) : A ≤ X := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  exact hA2.le

theorem ne_bot_of_mem_QhatStar216 {X A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) : A ≠ ⊥ := by
  obtain ⟨r', -, -, ⟨⟨hA2, -⟩, -⟩, -⟩ := QhatStar_spec hA
  exact hA2.ne_bot


end CFSG.Quasithin
