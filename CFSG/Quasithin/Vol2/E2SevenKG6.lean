module

public import CFSG.Quasithin.Vol2.E2SevenKG
public import CFSG.Quasithin.Vol2.Ch3E213MP5I
public import CFSG.Quasithin.Vol2.Ch3E213MP5J
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Quasithin.Background.E1Invariance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open Matrix CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section SL2

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem isPSL_two_two_of_equiv_sl2_char {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n)
    (hk : Nat.card k = 2 ^ n) (e : Y ≃* SL(2, k)) : IsPSL 2 2 n Y := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, k, inferInstance, inferInstance, hk,
    ⟨e.trans ((CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := k)).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 k))⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    omega

omit [Finite k] [CharP k 2] in
theorem normalizer_sl2UpperUnipotentSubgroup :
    Subgroup.normalizer (sl2UpperUnipotentSubgroup k : Set SL(2, k)) = sl2Borel k := by
  apply le_antisymm
  · intro A hA
    have h1 : A * sl2UpperUnipotent 1 * A⁻¹ ∈ sl2UpperUnipotentSubgroup k :=
      (Subgroup.mem_normalizer_iff.mp hA _).mp
        ((mem_sl2UpperUnipotentSubgroup_iff _).mpr ⟨1, rfl⟩)
    obtain ⟨y, hy⟩ := (mem_sl2UpperUnipotentSubgroup_iff _).mp h1
    have hinv : (A⁻¹ : SL(2, k)).val = !![A.val 1 1, -A.val 0 1; -A.val 1 0, A.val 0 0] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    have h3 : (A * sl2UpperUnipotent 1 * A⁻¹ : SL(2, k)).val 1 0 = -(A.val 1 0) ^ 2 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hinv]
      simp [sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have h2 : (A * sl2UpperUnipotent 1 * A⁻¹ : SL(2, k)).val 1 0 = 0 := by
      rw [hy]
      simp [sl2UpperUnipotent]
    rw [h3] at h2
    rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
    simpa using h2
  · intro A hA
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hA' : A⁻¹ ∈ sl2Borel k := (sl2Borel k).inv_mem hA
    constructor
    · intro hz
      obtain ⟨x, rfl⟩ := (mem_sl2UpperUnipotentSubgroup_iff _).mp hz
      rw [sl2Borel_conj_upperUnipotent hA x]
      exact (mem_sl2UpperUnipotentSubgroup_iff _).mpr ⟨_, rfl⟩
    · intro hz
      obtain ⟨y, hy⟩ := (mem_sl2UpperUnipotentSubgroup_iff _).mp hz
      have h1 : z = A⁻¹ * sl2UpperUnipotent y * A⁻¹⁻¹ := by
        rw [← hy]
        group
      rw [h1, sl2Borel_conj_upperUnipotent hA' y]
      exact (mem_sl2UpperUnipotentSubgroup_iff _).mpr ⟨_, rfl⟩

omit [Finite k] [CharP k 2] in
theorem card_sl2UpperUnipotentSubgroup :
    Nat.card (sl2UpperUnipotentSubgroup k) = Nat.card k := by
  rw [sl2UpperUnipotentSubgroup,
    ← Nat.card_congr (MonoidHom.ofInjective (sl2UpperUnipotentHom_injective (K := k))).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

theorem isSylowTwoOf_sl2UpperUnipotentSubgroup {n : ℕ} (hn : 1 ≤ n) (hk : Nat.card k = 2 ^ n) :
    IsSylowTwoOf (sl2UpperUnipotentSubgroup k) (⊤ : Subgroup SL(2, k)) := by
  refine ⟨le_top, ?_, ?_⟩
  · rintro ⟨g, hg⟩
    obtain ⟨x, rfl⟩ := (mem_sl2UpperUnipotentSubgroup_iff _).mp hg
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, sl2UpperUnipotent_mul, CharTwo.add_self_eq_zero,
      sl2UpperUnipotent_zero, Subgroup.coe_one]
  · have h1 := (sl2UpperUnipotentSubgroup k).card_mul_index
    rw [sl2_card_formula, card_sl2UpperUnipotentSubgroup, hk] at h1
    have h2 : (sl2UpperUnipotentSubgroup k).index = (2 ^ n) ^ 2 - 1 :=
      Nat.eq_of_mul_eq_mul_left (by positivity) h1
    have e : ((sl2UpperUnipotentSubgroup k).subgroupOf ⊤).index =
        (sl2UpperUnipotentSubgroup k).index := Subgroup.relIndex_top_right _
    rw [e, h2]
    have h3 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
    have h4 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    omega

end SL2

section Transport

variable {G : Type} [Group G]

private theorem mem_normalizer_subgroupOf_iff' {X U : Subgroup G} (hUX : U ≤ X) (y : ↥X) :
    y ∈ Subgroup.normalizer ((U.subgroupOf X : Subgroup ↥X) : Set ↥X) ↔
      (y : G) ∈ Subgroup.normalizer (U : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hUX, Subgroup.mem_subgroupOf]

private theorem mem_normalizer_map_subtype_iff {X : Subgroup G} (P : Subgroup ↥X) (y : ↥X) :
    (y : G) ∈ Subgroup.normalizer ((P.map X.subtype : Subgroup G) : Set G) ↔
      y ∈ Subgroup.normalizer (P : Set ↥X) := by
  have hP : (P.map X.subtype).subgroupOf X = P :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective P
  rw [← mem_normalizer_subgroupOf_iff' (Subgroup.map_subtype_le P), hP]

theorem isMaxParabolic2_map_subtype {X K : Subgroup G} (hKX : K ≤ X) {P : Subgroup ↥X}
    (hP : IsMaxParabolic2 (K.subgroupOf X) P) : IsMaxParabolic2 K (P.map X.subtype) := by
  obtain ⟨⟨hPK, S, hS, hSP⟩, hne, hmax⟩ := hP
  have hKmap : (K.subgroupOf X).map X.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKX
  have hSK : S ≤ K.subgroupOf X := hS.1
  have hS' : IsSylowTwoOf (S.map X.subtype) K := by
    have h := (E1.isSylowIn_map_of_injective (p := 2) X.subtype_injective (P := S)
      (H := K.subgroupOf X)).mpr hS
    rwa [hKmap] at h
  have hN : K ⊓ Subgroup.normalizer ((S.map X.subtype : Subgroup G) : Set G) ≤ P.map X.subtype := by
    rintro g ⟨hgK, hgN⟩
    refine ⟨⟨g, hKX hgK⟩, hSP ⟨Subgroup.mem_subgroupOf.mpr hgK, ?_⟩, rfl⟩
    exact (mem_normalizer_map_subtype_iff S ⟨g, hKX hgK⟩).mp hgN
  refine ⟨⟨?_, S.map X.subtype, hS', hN⟩, ?_, ?_⟩
  · rw [← hKmap]
    exact Subgroup.map_mono hPK
  · intro h
    apply hne
    apply Subgroup.map_injective X.subtype_injective
    rw [h, hKmap]
  · intro Q hQ hQne hPQ
    obtain ⟨hQK, R, hR, hRQ⟩ := hQ
    have hQX : Q ≤ X := hQK.trans hKX
    have hRK : R ≤ K := hR.1
    have hQ' : IsParabolic2 (K.subgroupOf X) (Q.subgroupOf X) := by
      refine ⟨Subgroup.subgroupOf_mono _ hQK, R.subgroupOf X, ?_, ?_⟩
      · exact (E1.isSylowIn_subgroupOf_iff (p := 2) (hRK.trans hKX) hKX).mpr hR
      · intro y hy
        obtain ⟨hyK, hyN⟩ := Subgroup.mem_inf.mp hy
        rw [Subgroup.mem_subgroupOf] at hyK ⊢
        exact hRQ ⟨hyK, (mem_normalizer_subgroupOf_iff' (hRK.trans hKX) y).mp hyN⟩
    have hQne' : Q.subgroupOf X ≠ K.subgroupOf X := by
      intro h
      apply hQne
      rw [← Subgroup.map_subgroupOf_eq_of_le hQX, h, hKmap]
    have hPQ' : P ≤ Q.subgroupOf X := fun y hy => Subgroup.mem_subgroupOf.mpr (hPQ ⟨y, hy, rfl⟩)
    have := hmax _ hQ' hQne' hPQ'
    rw [← Subgroup.map_subgroupOf_eq_of_le hQX, this]

end Transport

theorem kgL3Even_holds : KGL3Even := by
  intro G _ _ X T M K V n hP _ hKX hXN hC _ hn hK hdiag hMK hVO hVab hTV hV4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hMmax, hTM⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hMX : M ≤ X := hMmax.1.le
  have hTX : T ≤ X := hP.isSylow.1
  have hTsylM : IsSylowTwoOf T M := isSylowTwoOf_mono hP.isSylow hTM hMX
  have hO2T : pCoreOf 2 M ≤ T := A4.le_of_normal_of_isSylowTwoOf hTsylM
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hVT : V ≤ T := hVO.trans hO2T
  have hK'n : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  have hS : IsSylowTwoOf (T.subgroupOf X) ⊤ := Setup.X6.isSylowTwoOf_subgroupOf_top hP.isSylow
  have hCA : ∀ a : ↥X, (∀ x ∈ K.subgroupOf X, a * x = x * a) → a = 1 := by
    intro a ha
    have h1 : (a : G) ∈ X ⊓ Subgroup.centralizer (K : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨a.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := ha ⟨y, hKX hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
      exact (congrArg Subtype.val this).symm
    rw [hC, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hPSL : IsPSL 3 2 n ↥(K.subgroupOf X) :=
    CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKX).symm hK
  have hSK : (T ⊓ K).subgroupOf X = T.subgroupOf X ⊓ K.subgroupOf X := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hdiag' : ∀ P : Subgroup ↥X, IsMaxParabolic2 (K.subgroupOf X) P →
      K.subgroupOf X ⊓ Subgroup.normalizer
        ((T.subgroupOf X ⊓ K.subgroupOf X : Subgroup ↥X) : Set ↥X) ≤ P →
        ¬ T.subgroupOf X ≤ Subgroup.normalizer (P : Set ↥X) := by
    intro P hPmax hPB hSP
    refine hdiag (P.map X.subtype) (isMaxParabolic2_map_subtype hKX hPmax) ?_ ?_
    · rintro g ⟨hgK, hgN⟩
      refine ⟨⟨g, hKX hgK⟩, hPB ⟨Subgroup.mem_subgroupOf.mpr hgK, ?_⟩, rfl⟩
      rw [← hSK]
      exact (mem_normalizer_subgroupOf_iff' (inf_le_right.trans hKX) ⟨g, hKX hgK⟩).mpr hgN
    · intro t ht
      exact (mem_normalizer_map_subtype_iff P ⟨t, hTX ht⟩).mpr
        (hSP (Subgroup.mem_subgroupOf.mpr ht))
  have hBorel : ∃ S₀ : Subgroup ↥X, IsSylowTwoOf S₀ (K.subgroupOf X) ∧
      M.subgroupOf X ⊓ K.subgroupOf X =
        K.subgroupOf X ⊓ Subgroup.normalizer (S₀ : Set ↥X) := by
    refine ⟨(T ⊓ K).subgroupOf X, ?_, ?_⟩
    · exact (E1.isSylowIn_subgroupOf_iff (p := 2) (inf_le_right.trans hKX) hKX).mpr
        (A4.isSylowTwoOf_inf_normal hP.isSylow hKX hXN)
    · ext y
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      rw [mem_normalizer_subgroupOf_iff' (inf_le_right.trans hKX)]
      have h := SetLike.ext_iff.mp hMK (y : G)
      simp only [Subgroup.mem_inf] at h
      exact h
  have hSB : T.subgroupOf X ≤ M.subgroupOf X := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hTM (Subgroup.mem_subgroupOf.mp hy))
  have hES : V.subgroupOf X ≤ T.subgroupOf X := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (hVT (Subgroup.mem_subgroupOf.mp hy))
  have hSE : T.subgroupOf X ≤ Subgroup.normalizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
    fun s hs => (mem_normalizer_subgroupOf_iff' (hVT.trans hTX) s).mpr
      (hTV (Subgroup.mem_subgroupOf.mp hs))
  have hE2 : ∀ x ∈ V.subgroupOf X, x * x = 1 := by
    intro x hx
    apply Subtype.ext
    have := hVab.2 _ (Subgroup.mem_subgroupOf.mp hx)
    simpa [sq] using this
  obtain ⟨k, _, _, _, θ, hk, hθS, hθB, hEZ⟩ :=
    Ch3E213M.P5.model_of_setting hS hCA hPSL hdiag' hBorel hSB hES hSE hE2
  obtain ⟨φ, hφ⟩ : ∃ φ : SL(2, k) →* G, φ = X.subtype.comp (Ch3E213M.P5.cornerA θ) := ⟨_, rfl⟩
  have hφinj : Function.Injective φ := by
    rw [hφ]
    exact X.subtype_injective.comp (Ch3E213M.P5.cornerA_injective θ)
  have hmapX : ∀ Y : Subgroup SL(2, k),
      Y.map φ = (Y.map (Ch3E213M.P5.cornerA θ)).map X.subtype :=
    fun Y => by rw [hφ, ← Subgroup.map_map]
  have hrange : φ.range = (Ch3E213M.P5.cornerA θ).range.map X.subtype := by
    rw [hφ, MonoidHom.range_comp]
  have hTL : T ⊓ φ.range = (sl2UpperUnipotentSubgroup k).map φ := by
    have h1 := Ch3E213M.P5.inf_range_cornerA_S θ hθS
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rw [Subgroup.map_inf _ _ _ X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hTX] at h2
    rw [hmapX, ← h2, hrange]
  have hML : M ⊓ φ.range = (sl2Borel k).map φ := by
    have h1 := Ch3E213M.P5.inf_range_cornerA_B θ hθB
    have h2 := congrArg (Subgroup.map X.subtype) h1
    rw [Subgroup.map_inf _ _ _ X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hMX] at h2
    rw [hmapX, ← h2, hrange]
  have hVL : V ≤ (sl2UpperUnipotentSubgroup k).map φ := by
    intro v hv
    have h1 := hEZ (Subgroup.mem_subgroupOf.mpr hv :
      (⟨v, (hVT.trans hTX) hv⟩ : ↥X) ∈ V.subgroupOf X)
    rw [← Ch3E213M.P5.map_sl2UpperUnipotent, ← Ch3E213M.P5.map_cornerA] at h1
    rw [hmapX]
    exact ⟨⟨v, (hVT.trans hTX) hv⟩, h1, rfl⟩
  have hcardU : Nat.card ((sl2UpperUnipotentSubgroup k).map φ) = 2 ^ n := by
    rw [Subgroup.card_map_of_injective hφinj, card_sl2UpperUnipotentSubgroup, hk]
  have hn2 : 2 ≤ n := by
    have h1 : Nat.card V ≤ Nat.card ((sl2UpperUnipotentSubgroup k).map φ) :=
      Subgroup.card_le_of_le hVL
    rw [hcardU] at h1
    by_contra h
    have h2 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  refine ⟨hn2, φ.range, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hrange]
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.mem_subgroupOf.mp ((Ch3E213M.P5.range_cornerA_le θ) hg)
  ·
    exact isPSL_two_two_of_equiv_sl2_char hn2 hk (MonoidHom.ofInjective hφinj).symm
  ·
    rw [hTL, MonoidHom.range_eq_map]
    exact (E1.isSylowIn_map_of_injective (p := 2) hφinj).mpr
      (isSylowTwoOf_sl2UpperUnipotentSubgroup (by omega) hk)
  ·
    rw [hTL]
    exact hVL
  ·
    rw [hTL]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hVL hv
    obtain ⟨x, rfl⟩ := (mem_sl2UpperUnipotentSubgroup_iff _).mp ha
    obtain ⟨y, rfl⟩ := (mem_sl2UpperUnipotentSubgroup_iff _).mp hb
    rw [← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]
  ·
    rw [hML, hTL, ← normalizer_sl2UpperUnipotentSubgroup (k := k)]
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      replace hy : y ∈ Subgroup.normalizer ((sl2UpperUnipotentSubgroup k : Subgroup SL(2, k)) :
        Set SL(2, k)) := hy
      refine Subgroup.mem_inf.mpr ⟨⟨y, rfl⟩, ?_⟩
      rw [Subgroup.mem_normalizer_iff] at hy ⊢
      intro z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨y * w * y⁻¹, (hy w).mp hw, by simp⟩
      · rintro ⟨w, hw, hwz⟩
        refine ⟨y⁻¹ * w * y, (hy _).mpr (by simpa [mul_assoc] using hw), ?_⟩
        rw [map_mul, map_mul, map_inv, hwz]
        group
    · rintro ⟨⟨y, rfl⟩, hy⟩
      replace hy : φ y ∈ Subgroup.normalizer
        (((sl2UpperUnipotentSubgroup k).map φ : Subgroup G) : Set G) := hy
      refine ⟨y, ?_, rfl⟩
      show y ∈ Subgroup.normalizer ((sl2UpperUnipotentSubgroup k : Subgroup SL(2, k)) :
        Set SL(2, k))
      rw [Subgroup.mem_normalizer_iff] at hy ⊢
      intro z
      have h := hy (φ z)
      constructor
      · intro hz
        obtain ⟨w, hw, hwz⟩ := h.mp ⟨z, hz, rfl⟩
        have : w = y * z * y⁻¹ := hφinj (by rw [hwz, map_mul, map_mul, map_inv])
        rw [← this]
        exact hw
      · intro hz
        have h1 : φ (y * z * y⁻¹) ∈ (sl2UpperUnipotentSubgroup k).map φ := ⟨_, hz, rfl⟩
        rw [map_mul, map_mul, map_inv] at h1
        obtain ⟨w, hw, hwz⟩ := h.mpr h1
        rw [hφinj hwz] at hw
        exact hw

end E2

end CFSG.Quasithin
