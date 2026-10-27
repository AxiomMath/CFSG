module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case1
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146SwapB
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aF
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case1B
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case1D

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

open CFSG.Quasithin.F146Field.Case1 in
theorem case1_core_shape {T M H K : Subgroup G}
    (hStar : IsHStar T M H) (hmin : MinParabolic H T (H ⊓ M)) (hK : K ∈ cComp H)
    (hHK : H = K ⊔ T)
    (hker : kerIn (H ⊓ M) H = pCoreOf 2 H) {t : G} (ht : t ∈ T) (hne : cjSub t K ≠ K)
    (horb : ∀ s ∈ T, cjSub s K = K ∨ cjSub s K = cjSub t K)
    (hM : H ⊓ M = ((H ⊓ M) ⊓ K) ⊔ cjSub t ((H ⊓ M) ⊓ K) ⊔ T)
    {m : ℕ} (_hm : 2 ≤ m)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    (hBQ : ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K)) :
    Notation1428 T M H K ∧ Shape1428 T H K := by
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  have hTH : T ≤ H := hmin.isSylow.1
  have hTM : T ≤ H ⊓ M := hmin.le
  have hK' : cjSub t K ∈ cComp H := cjSub_mem_cComp_of_mem hK (hTH ht)
  have hΩ := oTwoUpper_eq_sup hK hT2 hHK ht horb
  have hsyl := isSylowTwoOf_inf_cComp hmin.isSylow hK hHK
  have hsyl' : IsSylowTwoOf (T ⊓ cjSub t K) (cjSub t K) :=
    isSylowTwoOf_inf_cComp hmin.isSylow hK' (eq_sup_cjSub hK hHK ht)
  have hbor := inf_eq_inf_normalizer hmin hK hHK hker hB
  have hbor1 : ∀ x ∈ K, x ∈ H ⊓ M →
      x ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := fun x hx hxM =>
    (hbor.le ⟨hx, hxM⟩).2
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hC : K ⊓ cjSub t K ≤ T :=
    (inf_cjSub_le_pCoreOf hmin hK hHK hker ht hne horb).trans hQT
  have hKK' : K ≤ Subgroup.normalizer (cjSub t K : Set G) := le_normalizer_of_mem_cComp hK' hK
  have hK'K : cjSub t K ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_mem_cComp hK hK'
  have hΩN : T ≤ Subgroup.normalizer ((oTwoUpper H : Subgroup G) : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper H)
  have hlt : K < oTwoUpper H := by
    refine lt_of_le_of_ne (le_oTwoUpper hK) ?_
    intro h
    apply hne
    have h1 := mem_normalizer_iff_cjSub_eq.mp (le_normalizer_oTwoUpper H (hTH ht))
    rw [h]
    exact h1
  have hN : Notation1428 T M H K := by
    refine ⟨le_oTwoUpper hK, inf_le_right.trans (oTwoUpper_le_normalizer hK hT2 hHK),
      P134.pCoreOf_le_normalizer_of_mem_cComp hK, hsyl, hBQ, ?_, ?_, ?_, ?_, ?_⟩
    · refine cComp_mem_of_le hK le_sup_left (sup_le (le_of_mem_cComp hK) ?_)
      exact (inf_le_left : T ⊓ Subgroup.normalizer (K : Set G) ≤ T).trans hTH
    · intro hKM
      apply hStar.2.1
      rw [hHK]
      exact sup_le hKM (hTM.trans inf_le_right)
    · exact Or.inr ⟨hlt, relIndex_normalizer_eq_two ht hne horb⟩
    · intro x hx
      have hxM₀ : x ∈ H ⊓ M := ⟨oTwoUpper_le H hx.2, hx.1⟩
      have key : H ⊓ M ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
        rw [hΩ]
        calc H ⊓ M = ((H ⊓ M) ⊓ K) ⊔ cjSub t ((H ⊓ M) ⊓ K) ⊔ T := hM
          _ ≤ _ := by
            refine sup_le (sup_le ?_ ?_) ?_
            · intro y hy
              exact mem_normalizer_inf_sup hKK' hK'K hT2 hC hsyl hy.2 (hbor1 y hy.2 hy.1)
            · intro y hy
              have hyK' : y ∈ cjSub t K := cjSub_mono inf_le_right hy
              have hyM : y ∈ H ⊓ M := by
                have h1 : t⁻¹ * y * t ∈ (H ⊓ M) ⊓ K := mem_cjSub.mp hy
                have h2 := (H ⊓ M).mul_mem ((H ⊓ M).mul_mem (hTM ht) h1.1)
                  ((H ⊓ M).inv_mem (hTM ht))
                have h3 : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
                rwa [h3] at h2
              have hN := borel_property_cjSub hTM ht hbor1 hyK' hyM
              have hC' : cjSub t K ⊓ K ≤ T := by rw [inf_comm]; exact hC
              have := mem_normalizer_inf_sup hK'K hKK' hT2 hC' hsyl' hyK' hN
              rwa [sup_comm] at this
            · intro s hs
              refine A4.mem_normalizer_of_conj_mem fun z hz => ?_
              refine ⟨T.mul_mem (T.mul_mem hs hz.1) (T.inv_mem hs), ?_⟩
              rw [← hΩ]
              exact (Subgroup.mem_normalizer_iff.mp (hΩN hs) z).mp (hΩ ▸ hz.2)
      exact key hxM₀
    · intro x hx
      exact (hbor.ge hx).2.2
  exact ⟨hN, ⟨Or.inr (Or.inl ⟨hK, hlt⟩)⟩⟩

theorem case1_shape (h38 : Vol2Native.A38ForSQTKCat) {T M H K : Subgroup G}
    (hStar : IsHStar T M H) (hmin : MinParabolic H T (H ⊓ M)) (hsq : SQTKGroup ↥H)
    (hK : K ∈ cComp H) (hHK : H = K ⊔ T) (hker : kerIn (H ⊓ M) H = pCoreOf 2 H)
    {t : G} (ht : t ∈ T) (hne : cjSub t K ≠ K)
    (hM : H ⊓ M = ((H ⊓ M) ⊓ K) ⊔ cjSub t ((H ⊓ M) ⊓ K) ⊔ T)
    {m : ℕ} (hm : 2 ≤ m)
    (hty : IsPSL 2 2 m ↥(E2.star (H ⊓ M) H K) ∨ IsSz m ↥(E2.star (H ⊓ M) H K))
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    ∃ K1 : Subgroup G, Notation1428 T M H K1 ∧ Shape1428 T H K1 := by
  obtain ⟨e⟩ := case1_equiv hmin hK hHK hker
  exact ⟨K, case1_core_shape hStar hmin hK hHK hker ht hne
    (case1_orbit h38 hsq hmin.isSylow hK ht hne) hM hm hB
    ⟨m, hm, isBenderQuot_of_equiv e hty⟩⟩

theorem case2a_core_shape {T M H K : Subgroup G}
    (hStar : IsHStar T M H) (hmin : MinParabolic H T (H ⊓ M)) (hK : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hker : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K)))
    (hBQ : ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K)) :
    Notation1428 T M H K ∧ Shape1428 T H K := by
  have c : Case2a.Setting T M H K := ⟨hmin, hK, hHK, hTK, hker⟩
  have hN : Notation1428 T M H K := by
    refine ⟨c.oTwoUpper_eq.ge, inf_le_left.trans hTK, c.pCore_le_normalizer, c.sylow_inf, hBQ,
      c.cComp_mem, c.not_le_M hStar.2.1, Or.inl ⟨c.oTwoUpper_eq.symm, hTK⟩, ?_,
      Case2a.borel_le c hB⟩
    rw [c.oTwoUpper_eq]
    exact Case2a.borel_inf c hB
  refine ⟨hN, ⟨Or.inl ⟨c.oTwoUpper_eq.symm, ?_⟩⟩⟩
  rw [c.oTwoUpper_eq]
  exact hK

theorem case2a_shape {T M H K : Subgroup G}
    (hStar : IsHStar T M H) (hmin : MinParabolic H T (H ⊓ M)) (hK : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hker : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    {m : ℕ} (hBen : E2.IsBenderOf m ↥(E2.star (H ⊓ M) H K))
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    ∃ K1 : Subgroup G, Notation1428 T M H K1 ∧ Shape1428 T H K1 :=
  ⟨K, case2a_core_shape hStar hmin hK hHK hTK hker hB
    ⟨m, hBen.1, case2a_bq hmin hK hHK hTK hker hBen⟩⟩

end CFSG.Quasithin.F146Field
