module

public import CFSG.Quasithin.Background.BlueprintB2Reduced
public import CFSG.Quasithin.Background.BlueprintB2Frattini
public import CFSG.Quasithin.Background.A4Defs
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.Quasithin

open CFSG CFSG.Quasithin.BlueprintB2

variable {G : Type*} [Group G]

namespace BlueprintB2

theorem pCore_eq_open_pCore (p : ℕ) (E : Type*) [Group E] :
    CFSG.pCore p E = CFSG.Open.pCore p E := (CFSG.Open.pCore_eq_pCore p E).symm

theorem isElemAbelian_iff_isElementaryAbelian (p : ℕ) {A : Subgroup G} :
    CFSG.Open.IsElemAbelian p A ↔ IsElementaryAbelian p A :=
  (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p A).symm

theorem subgroupOf_map_subtype_self {S : Subgroup G} (A : Subgroup S) :
    (A.map S.subtype).subgroupOf S = A :=
  Subgroup.comap_map_eq_self_of_injective S.subtype_injective A

theorem map_subtype_le_self {S : Subgroup G} (A : Subgroup S) : A.map S.subtype ≤ S := by
  rintro _ ⟨a, -, rfl⟩
  exact a.2

theorem pRank_eq_open_pRank [Finite G] (p : ℕ) (H : Subgroup G) :
    CFSG.pRank p H = CFSG.Open.pRank p H := CFSG.SectionRank.pRank_coe_eq_openPRank p H

theorem isMaxElemAbelian_iff_mem_elemThompsonFamily [Finite G] {S A : Subgroup G} :
    IsMaxElemAbelian S A ↔ A ≤ S ∧ A.subgroupOf S ∈ elemThompsonFamily S 2 := by
  rw [mem_elemThompsonFamily_iff]
  constructor
  · rintro ⟨hAS, hA, hmax⟩
    refine ⟨hAS, isElementaryAbelian_subgroupOf
      ((isElemAbelian_iff_isElementaryAbelian 2).mp hA), fun B' hB' => ?_⟩
    rw [card_subgroupOf_eq hAS]
    have := hmax (B'.map S.subtype) (map_subtype_le_self B')
      ((isElemAbelian_iff_isElementaryAbelian 2).mpr (isElementaryAbelian_map hB' _))
    rwa [Subgroup.card_map_of_injective S.subtype_injective] at this
  · rintro ⟨hAS, hA', hmax'⟩
    refine ⟨hAS, ?_, fun B hBS hB => ?_⟩
    · have := isElementaryAbelian_map hA' S.subtype
      rw [Subgroup.map_subgroupOf_eq_of_le hAS] at this
      exact (isElemAbelian_iff_isElementaryAbelian 2).mpr this
    · have := hmax' (B.subgroupOf S)
        (isElementaryAbelian_subgroupOf ((isElemAbelian_iff_isElementaryAbelian 2).mp hB))
      rwa [card_subgroupOf_eq hAS, card_subgroupOf_eq hBS] at this

end BlueprintB2

theorem elemThompson_map_subtype_eq_thompsonJ [Finite G] (S : Subgroup G) :
    (elemThompson S 2).map S.subtype = thompsonJ S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A' hA' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hA : IsMaxElemAbelian S (A'.map S.subtype) := by
      rw [BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily,
        BlueprintB2.subgroupOf_map_subtype_self]
      exact ⟨BlueprintB2.map_subtype_le_self A', hA'⟩
    exact le_iSup₂_of_le (A'.map S.subtype) hA le_rfl
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨hAS, hA'⟩ := BlueprintB2.isMaxElemAbelian_iff_mem_elemThompsonFamily.mp hA
    calc A = (A.subgroupOf S).map S.subtype := (Subgroup.map_subgroupOf_eq_of_le hAS).symm
      _ ≤ _ := Subgroup.map_mono (BlueprintB2.le_elemThompson hA')

namespace BlueprintB2

theorem omegaOneCenterOf_eq_centerTorsion (K : Subgroup G) :
    omegaOneCenterOf K = centerTorsion 2 K := by
  have hset : {x : G | x ∈ centerOf K ∧ x ^ 2 = 1} = (centerTorsion 2 K : Set G) := by
    ext z
    rw [SetLike.mem_coe, mem_centerTorsion_iff]
    simp only [Set.mem_ofPred_eq, centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe]
    tauto
  unfold omegaOneCenterOf omegaOneOf
  rw [hset, Subgroup.closure_eq]

theorem map_centerTorsion {E E' : Type*} [Group E] [Group E'] (f : E →* E')
    (hf : Function.Injective f) (p : ℕ) (K : Subgroup E) :
    (centerTorsion p K).map f = centerTorsion p (K.map f) := by
  ext z
  rw [mem_centerTorsion_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyK, hyc, hyp⟩ := mem_centerTorsion_iff.mp hy
    refine ⟨Subgroup.mem_map_of_mem f hyK, ?_, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      rw [← map_mul, ← map_mul, hyc k hk]
    · rw [← map_pow, hyp, map_one]
  · rintro ⟨⟨y, hyK, rfl⟩, hc, hp⟩
    refine ⟨y, mem_centerTorsion_iff.mpr ⟨hyK, fun k hk => ?_, ?_⟩, rfl⟩
    · apply hf
      rw [map_mul, map_mul]
      exact hc (f k) (Subgroup.mem_map_of_mem f hk)
    · apply hf
      rw [map_pow, hp, map_one]

theorem map_subtype_centralizer (S : Subgroup G) (T : Subgroup S) :
    (Subgroup.centralizer (T : Set S)).map S.subtype =
      S ⊓ Subgroup.centralizer ((T.map S.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy t ht)
  · rintro ⟨hxS, hx⟩
    refine ⟨⟨x, hxS⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
    intro t ht
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx (t : G) ⟨t, ht, rfl⟩)

end BlueprintB2

theorem elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf [Finite G] (S : Subgroup G) :
    (elemThompsonCenterTorsion S 2).map S.subtype = omegaOneCenterOf (thompsonJ S) := by
  rw [BlueprintB2.omegaOneCenterOf_eq_centerTorsion, ← elemThompson_map_subtype_eq_thompsonJ,
    elemThompsonCenterTorsion_eq_centerTorsion,
    BlueprintB2.map_centerTorsion S.subtype S.subtype_injective]

theorem elemBaumann_map_subtype_eq_baum [Finite G] (S : Subgroup G) :
    (elemBaumann S 2).map S.subtype = baum S := by
  unfold elemBaumann baum
  rw [BlueprintB2.map_subtype_centralizer,
    ← elemThompsonCenterTorsion_map_subtype_eq_omegaOneCenterOf]

theorem isPrimeReduced_iff_open_pCore {E : Type*} [Group E] (p : ℕ) (V : Subgroup E) :
    IsPrimeReduced p V ↔
      ∃ _ : V.Normal, CFSG.IsElementaryAbelian p V ∧
        CFSG.Open.pCore p (E ⧸ Subgroup.centralizer (V : Set E)) = ⊥ := by
  unfold IsPrimeReduced
  refine exists_congr fun hN => and_congr_right fun _ => ?_
  try with_reducible rfl

namespace BlueprintB2

theorem mem_centralizer_subgroupOf_iff {H V : Subgroup G} (hVH : V ≤ H) (y : H) :
    y ∈ Subgroup.centralizer ((V.subgroupOf H : Subgroup H) : Set H) ↔
      (y : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    exact congrArg Subtype.val (h ⟨v, hVH hv⟩ (Subgroup.mem_subgroupOf.mpr hv))
  · intro h v hv
    exact Subtype.ext (h (v : G) (Subgroup.mem_subgroupOf.mp hv))

theorem normal_subgroupOf_iff_le_normalizer {H D : Subgroup G} (hDH : D ≤ H) :
    (D.subgroupOf H).Normal ↔ H ≤ Subgroup.normalizer (D : Set G) := by
  rw [Subgroup.normal_subgroupOf_iff hDH]
  constructor
  · intro h k hk
    rw [Subgroup.mem_normalizer_iff]
    intro d
    refine ⟨fun hd => h d k hd hk, fun hd => ?_⟩
    have := h _ k⁻¹ hd (H.inv_mem hk)
    simpa [mul_assoc] using this
  · intro h d k hd hk
    exact (Subgroup.mem_normalizer_iff.mp (h hk) d).mp hd

end BlueprintB2

theorem isTwoReducedIn_iff_isPrimeReduced_subgroupOf {H V : Subgroup G} :
    IsTwoReducedIn H V ↔ V ≤ H ∧ IsPrimeReduced 2 (V.subgroupOf H) := by
  constructor
  · rintro ⟨hVH, hHN, hVe, hD⟩
    refine ⟨hVH, (isPrimeReduced_iff_forall 2).mpr
      ⟨(BlueprintB2.normal_subgroupOf_iff_le_normalizer hVH).mpr hHN,
        BlueprintB2.isElementaryAbelian_subgroupOf
          ((BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mp hVe), ?_⟩⟩
    intro D' hD' hDp
    have hDH : D'.map H.subtype ≤ H := BlueprintB2.map_subtype_le_self D'
    have hnorm : H ≤ Subgroup.normalizer ((D'.map H.subtype : Subgroup G) : Set G) := by
      rw [← BlueprintB2.normal_subgroupOf_iff_le_normalizer hDH,
        BlueprintB2.subgroupOf_map_subtype_self]
      exact hD'
    have hle : D'.map H.subtype ≤ Subgroup.centralizer (V : Set G) := by
      refine hD _ hDH hnorm ?_
      rintro _ ⟨d, hd, rfl⟩
      obtain ⟨k, hk⟩ := hDp d hd
      exact ⟨k, (BlueprintB2.mem_centralizer_subgroupOf_iff hVH _).mp hk⟩
    intro d hd
    exact (BlueprintB2.mem_centralizer_subgroupOf_iff hVH d).mpr (hle ⟨d, hd, rfl⟩)
  · rintro ⟨hVH, hred⟩
    obtain ⟨hN, hVe, hD'⟩ := (isPrimeReduced_iff_forall 2).mp hred
    refine ⟨hVH, (BlueprintB2.normal_subgroupOf_iff_le_normalizer hVH).mp hN, ?_, ?_⟩
    · have := isElementaryAbelian_map hVe H.subtype
      rw [Subgroup.map_subgroupOf_eq_of_le hVH] at this
      exact (BlueprintB2.isElemAbelian_iff_isElementaryAbelian 2).mpr this
    · intro D hDH hHD hDp
      have hDn : (D.subgroupOf H).Normal :=
        (BlueprintB2.normal_subgroupOf_iff_le_normalizer hDH).mpr hHD
      have hle := hD' (D.subgroupOf H) hDn fun d hd => by
        obtain ⟨k, hk⟩ := hDp (d : G) (Subgroup.mem_subgroupOf.mp hd)
        exact ⟨k, (BlueprintB2.mem_centralizer_subgroupOf_iff hVH (d ^ 2 ^ k)).mpr hk⟩
      intro d hd
      exact (BlueprintB2.mem_centralizer_subgroupOf_iff hVH ⟨d, hDH hd⟩).mp
        (hle (Subgroup.mem_subgroupOf.mpr hd))

theorem primeReducedAggregate_map_subtype_eq_twoReducedJoin (H : Subgroup G) :
    (primeReducedAggregate H 2).map H.subtype = twoReducedJoin H := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun V' hV' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hV : IsTwoReducedIn H (V'.map H.subtype) := by
      rw [isTwoReducedIn_iff_isPrimeReduced_subgroupOf, BlueprintB2.subgroupOf_map_subtype_self]
      exact ⟨BlueprintB2.map_subtype_le_self V', hV'⟩
    exact le_iSup₂_of_le (V'.map H.subtype) hV le_rfl
  · refine iSup₂_le fun V hV => ?_
    obtain ⟨hVH, hred⟩ := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hV
    calc V = (V.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hVH).symm
      _ ≤ _ := Subgroup.map_mono (le_primeReducedAggregate hred)

namespace BlueprintB2

theorem conjAct_eq_conjNormal (V : Subgroup G) [V.Normal] (g : Subgroup.normalizer (V : Set G)) :
    conjAct V g = MulAut.conjNormal (H := V) (g : G) :=
  MulEquiv.ext fun _ => Subtype.ext rfl

end BlueprintB2

theorem autOn_eq_map_conjNormal (V L : Subgroup G) [V.Normal] :
    autOn L V = L.map (MulAut.conjNormal (H := V)) := by
  ext φ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(g : G), Subgroup.mem_subgroupOf.mp hg, (BlueprintB2.conjAct_eq_conjNormal V g).symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, (Subgroup.normalizer_eq_top_iff.mpr inferInstance :
        Subgroup.normalizer (V : Set G) = ⊤) ▸ Subgroup.mem_top g⟩,
      Subgroup.mem_subgroupOf.mpr hg, BlueprintB2.conjAct_eq_conjNormal V _⟩

theorem pPrimeGen_two_eq_oTwoUpper (X : Subgroup G) :
    BlueprintB2.pPrimeGen 2 X = oTwoUpper X := by
  unfold BlueprintB2.pPrimeGen oTwoUpper
  congr 1
  ext x
  simp [Nat.coprime_two_right]

end CFSG.Quasithin
