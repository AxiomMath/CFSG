module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GH74.SmallRanks.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma s16c1_conjSubgroup_coe_mul (A B U : Subgroup G) (k : G)
    (h : (A : Set G) = (B : Set G) * (U : Set G)) :
    (conjSubgroup A k : Set G) = (conjSubgroup B k : Set G) * (conjSubgroup U k : Set G) := by
  change (A.map (MulAut.conj k⁻¹).toMonoidHom : Set G) =
    (B.map (MulAut.conj k⁻¹).toMonoidHom : Set G) *
      (U.map (MulAut.conj k⁻¹).toMonoidHom : Set G)
  simp only [Subgroup.coe_map, h, Set.image_mul]

private lemma s16c1_conjSubgroup_sup (A B : Subgroup G) (k : G) :
    conjSubgroup A k ⊔ conjSubgroup B k = conjSubgroup (A ⊔ B) k :=
  (Subgroup.map_sup A B (MulAut.conj k⁻¹).toMonoidHom).symm

private lemma s16c1_sup_conj (A B : Subgroup G) (k : G) (hA : conjSubgroup A k = A) :
    A ⊔ conjSubgroup B k = conjSubgroup (A ⊔ B) k := by
  rw [← s16c1_conjSubgroup_sup A B k, hA]

private lemma s16c1_conjSubgroup_injective (k : G) :
    Function.Injective fun A : Subgroup G => conjSubgroup A k := by
  intro A B h
  have := congrArg (fun X : Subgroup G => conjSubgroup X k⁻¹) h
  simpa only [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] using this

theorem s16c1_normal_conj {L K : Subgroup G} (h : (K.subgroupOf L).Normal) (k : G) :
    ((conjSubgroup K k).subgroupOf (conjSubgroup L k)).Normal := by
  refine ⟨fun x hx l => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [mem_conjSubgroup_iff] at hx ⊢
  have hxl : k * (x : G) * k⁻¹ ∈ L := mem_conjSubgroup_iff.mp x.2
  have hll : k * (l : G) * k⁻¹ ∈ L := mem_conjSubgroup_iff.mp l.2
  have hres := h.conj_mem (⟨k * (x : G) * k⁻¹, hxl⟩ : L)
    (by simpa [Subgroup.mem_subgroupOf] using hx) (⟨k * (l : G) * k⁻¹, hll⟩ : L)
  rw [Subgroup.mem_subgroupOf] at hres
  convert hres using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
  group

private lemma s16c1_quotShape_map {L K : Subgroup G} (k : G) [(K.subgroupOf L).Normal]
    [((K.map (MulAut.conj k⁻¹).toMonoidHom).subgroupOf
      (L.map (MulAut.conj k⁻¹).toMonoidHom)).Normal] {d : ℕ}
    (h : QuotShape L K d) :
    QuotShape (L.map (MulAut.conj k⁻¹).toMonoidHom)
      (K.map (MulAut.conj k⁻¹).toMonoidHom) d := by
  let eL : ↥L ≃* ↥(L.map (MulAut.conj k⁻¹).toMonoidHom) :=
    MulEquiv.subgroupMap (MulAut.conj k⁻¹) L
  have he : (K.subgroupOf L).map (eL : ↥L →* ↥(L.map (MulAut.conj k⁻¹).toMonoidHom)) =
      (K.map (MulAut.conj k⁻¹).toMonoidHom).subgroupOf
        (L.map (MulAut.conj k⁻¹).toMonoidHom) := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_map]
      exact ⟨x, hx, (MulEquiv.coe_subgroupMap_apply (MulAut.conj k⁻¹) L x).symm⟩
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨eL.symm y, ?_, eL.apply_symm_apply y⟩
      rw [Subgroup.mem_subgroupOf]
      have hmem : k * (y : G) * k⁻¹ ∈ K := by
        rw [← hby]
        have hfb : (MulEquiv.toMonoidHom (MulAut.conj k⁻¹)) b = k⁻¹ * b * k := by
          rw [show (MulEquiv.toMonoidHom (MulAut.conj k⁻¹)) b = (MulAut.conj k⁻¹) b from rfl,
            MulAut.conj_apply, inv_inv]
        rw [hfb]
        convert hb using 1
        group
      convert hmem using 1
      rw [show ((eL.symm y : ↥L) : G) = (MulAut.conj k⁻¹).symm (y : G) from rfl,
        MulAut.conj_symm_apply, inv_inv]
  let e : (↥L ⧸ K.subgroupOf L) ≃*
      (↥(L.map (MulAut.conj k⁻¹).toMonoidHom) ⧸
        (K.map (MulAut.conj k⁻¹).toMonoidHom).subgroupOf
          (L.map (MulAut.conj k⁻¹).toMonoidHom)) :=
    QuotientGroup.congr (K.subgroupOf L)
      ((K.map (MulAut.conj k⁻¹).toMonoidHom).subgroupOf
        (L.map (MulAut.conj k⁻¹).toMonoidHom)) eL he
  obtain ⟨hshape, hrank⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hshape with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨m, hm, he'⟩
    · exact Or.inl ⟨r, CFSG.Blueprint.LieModel.of_mulEquiv e hr⟩
    · exact Or.inr (Or.inl ⟨r, CFSG.Blueprint.LieModel.of_mulEquiv e hr⟩)
    · rcases he' with ⟨e'⟩
      exact Or.inr (Or.inr ⟨m, hm, ⟨e.symm.trans e'⟩⟩)
  · rw [← CFSG.GH74.twoRank_eq_of_mulEquiv e]
    exact hrank

theorem s16c1_quotShape_conj {L K : Subgroup G} (k : G) [(K.subgroupOf L).Normal]
    [((conjSubgroup K k).subgroupOf (conjSubgroup L k)).Normal] {d : ℕ}
    (h : QuotShape L K d) : QuotShape (conjSubgroup L k) (conjSubgroup K k) d :=
  @s16c1_quotShape_map G _ _ L K k inferInstance
    (show ((K.map (MulAut.conj k⁻¹).toMonoidHom).subgroupOf
        (L.map (MulAut.conj k⁻¹).toMonoidHom)).Normal from
      (inferInstance : ((conjSubgroup K k).subgroupOf (conjSubgroup L k)).Normal)) d h

theorem s16c1_inCalO_mul {n : ℕ} {M V₀ V : Subgroup G} {g k : G} (hk : k ∈ M)
    (hkV : k ∈ normalizer (V : Set G)) (hkV₀ : k ∈ normalizer (V₀ : Set G))
    (hO : InCalO n M V₀ V g) : InCalO n M V₀ V (g * k) := by
  obtain ⟨⟨hF1, hF2, hF3⟩, ⟨hD1, hD2, hD3⟩⟩ := hO
  have hVk : conjSubgroup V k = V := conjSubgroup_eq_iff_mem_normalizer.mpr hkV
  have hV₀k : conjSubgroup V₀ k = V₀ := conjSubgroup_eq_iff_mem_normalizer.mpr hkV₀
  have hMk : conjSubgroup M k = M :=
    conjSubgroup_eq_iff_mem_normalizer.mpr ((Subgroup.le_normalizer (H := M)) hk)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [← conjSubgroup_conjSubgroup V g k, ← hMk]
    exact fun hle => hF1 ((E3.conjSubgroup_le_conjSubgroup_iff k).mp hle)
  · rw [← conjSubgroup_conjSubgroup M g k, ← hVk, E3.mQuot_conjSubgroup]
    exact hF2
  · intro hne hbot
    have h : V₀ ⊓ conjSubgroup M (g * k) = conjSubgroup (V₀ ⊓ conjSubgroup M g) k := by
      rw [← conjSubgroup_conjSubgroup M g k]
      simp only [E3.conjSubgroup_inf, hV₀k]
    exact hF3 hne (conjSubgroup_eq_bot_iff.mp (by rw [← h]; exact hbot))
  · rw [← conjSubgroup_conjSubgroup M g k, ← hVk]
    exact fun hle => hD1 ((E3.conjSubgroup_le_conjSubgroup_iff k).mp hle)
  · rw [← conjSubgroup_conjSubgroup V g k, ← hMk, E3.mQuot_conjSubgroup]
    exact hD2
  · intro hne hbot
    have h : conjSubgroup V₀ (g * k) ⊓ M = conjSubgroup (conjSubgroup V₀ g ⊓ M) k := by
      rw [← conjSubgroup_conjSubgroup V₀ g k]
      simp only [E3.conjSubgroup_inf, hMk]
    exact hD3 hne (conjSubgroup_eq_bot_iff.mp (by rw [← h]; exact hbot))

theorem s16c1_inCalOStar_mul {n : ℕ} {M V₀ V : Subgroup G} {g k : G} (hk : k ∈ M)
    (hkV : k ∈ normalizer (V : Set G)) (hkV₀ : k ∈ normalizer (V₀ : Set G))
    (hO : InCalOStar n M V₀ V g) : InCalOStar n M V₀ V (g * k) := by
  obtain ⟨hInCalO, K, hKnorm, hKset, hQuot, hconj, hcomm, hcentral, hne⟩ := hO
  have hVk : conjSubgroup V k = V := conjSubgroup_eq_iff_mem_normalizer.mpr hkV
  have hV₀k : conjSubgroup V₀ k = V₀ := conjSubgroup_eq_iff_mem_normalizer.mpr hkV₀
  have hMk : conjSubgroup M k = M :=
    conjSubgroup_eq_iff_mem_normalizer.mpr ((Subgroup.le_normalizer (H := M)) hk)
  have hVg : conjSubgroup V (g * k) = conjSubgroup (conjSubgroup V g) k :=
    (conjSubgroup_conjSubgroup V g k).symm
  have hMg : conjSubgroup M (g * k) = conjSubgroup (conjSubgroup M g) k :=
    (conjSubgroup_conjSubgroup M g k).symm
  have hV₀g : conjSubgroup V₀ (g * k) = conjSubgroup (conjSubgroup V₀ g) k :=
    (conjSubgroup_conjSubgroup V₀ g k).symm
  have hL : V ⊔ conjSubgroup V (g * k) = conjSubgroup (V ⊔ conjSubgroup V g) k := by
    rw [hVg]
    exact s16c1_sup_conj V (conjSubgroup V g) k hVk
  have hB : (conjSubgroup V (g * k) ⊓ M : Subgroup G) =
      conjSubgroup (conjSubgroup V g ⊓ M) k := by
    simp only [hVg, E3.conjSubgroup_inf, hMk]
  have hU : (V ⊓ conjSubgroup M (g * k) : Subgroup G) =
      conjSubgroup (V ⊓ conjSubgroup M g) k := by
    simp only [hMg, E3.conjSubgroup_inf, hVk]
  have hmQuot : E3.mQuot V (conjSubgroup M (g * k)) = E3.mQuot V (conjSubgroup M g) := by
    rw [hMg]
    conv_lhs => rw [← hVk]
    rw [E3.mQuot_conjSubgroup]
  have hRHS : (V ⊓ conjSubgroup V (g * k)) ⊔ V₀ =
      conjSubgroup ((V ⊓ conjSubgroup V g) ⊔ V₀) k := by
    calc (V ⊓ conjSubgroup V (g * k)) ⊔ V₀
        = (conjSubgroup V k ⊓ conjSubgroup (conjSubgroup V g) k) ⊔ conjSubgroup V₀ k := by
            simp only [hVg, hVk, hV₀k]
      _ = conjSubgroup (V ⊓ conjSubgroup V g) k ⊔ conjSubgroup V₀ k := by
            simp only [← E3.conjSubgroup_inf]
      _ = conjSubgroup ((V ⊓ conjSubgroup V g) ⊔ V₀) k := s16c1_conjSubgroup_sup _ _ k
  refine ⟨s16c1_inCalO_mul hk hkV hkV₀ hInCalO, conjSubgroup K k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL]
    exact s16c1_normal_conj hKnorm k
  · rw [hB, hU]
    exact s16c1_conjSubgroup_coe_mul K (conjSubgroup V g ⊓ M) (V ⊓ conjSubgroup M g) k hKset
  · have hqs := @s16c1_quotShape_conj G _ _ (V ⊔ conjSubgroup V g) K k hKnorm
        (s16c1_normal_conj hKnorm k) (E3.mQuot V (conjSubgroup M g)) hQuot
    simpa only [hL, hmQuot] using hqs
  · obtain ⟨l, hl, hgl⟩ := hconj
    have hVkinv : conjSubgroup V k⁻¹ = V := by
      have h := conjSubgroup_conjSubgroup V k k⁻¹
      rw [hVk, mul_inv_cancel, conjSubgroup_one] at h
      exact h
    have hkl : conjSubgroup V (k⁻¹ * l) = conjSubgroup V l := by
      rw [← conjSubgroup_conjSubgroup V k⁻¹ l, hVkinv]
    have hl' : k⁻¹ * l * k ∈ V ⊔ conjSubgroup V (g * k) := by
      rw [hL, mem_conjSubgroup_iff]
      convert hl using 1
      group
    refine ⟨k⁻¹ * l * k, hl', ?_⟩
    have hR : conjSubgroup V (k⁻¹ * l * k) = conjSubgroup (conjSubgroup V l) k := by
      rw [show k⁻¹ * l * k = (k⁻¹ * l) * k from by group,
        ← conjSubgroup_conjSubgroup V (k⁻¹ * l) k, hkl]
    rw [hVg, hgl, hR]
  · rw [hV₀g, show V = conjSubgroup V k from hVk.symm, ← E3.conjSubgroup_commutator]
    calc conjSubgroup ⁅conjSubgroup V₀ g, V⁆ k
        ≤ conjSubgroup V₀ k := E3.conjSubgroup_mono_left k hcomm
      _ = V₀ := hV₀k
  · have hLHS : V ⊓ centralizer ↑(conjSubgroup V (g * k) ⊓ M) =
        conjSubgroup (V ⊓ centralizer ↑(conjSubgroup V g ⊓ M)) k := by
      calc V ⊓ centralizer ↑(conjSubgroup V (g * k) ⊓ M)
          = conjSubgroup V k ⊓ centralizer ↑(conjSubgroup (conjSubgroup V g ⊓ M) k) := by
              rw [hVk, hB]
        _ = conjSubgroup V k ⊓ conjSubgroup (centralizer ↑(conjSubgroup V g ⊓ M)) k := by
              rw [← E3.conjSubgroup_centralizer]
        _ = conjSubgroup (V ⊓ centralizer ↑(conjSubgroup V g ⊓ M)) k := by
              rw [← E3.conjSubgroup_inf]
    rw [hLHS, hcentral, ← hRHS]
  · intro h
    apply hne
    have hthis := congrArg (fun X : Subgroup G => conjSubgroup X k⁻¹) h
    rw [hRHS, hU] at hthis
    simpa only [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] using hthis

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
