module

public import CFSG.RankThree.PartTwo.Sec15.Item153Claims
import CFSG.RankThree.PartTwo.Sec15.Item153TwinProofTools
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item134Residual

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof153Twin2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Cores

variable {H : Type*} [Group H] [Finite H]

theorem map_pPrimeCore_le_of_isSubnormal' {p : ℕ} [Fact p.Prime] {Z : Subgroup H}
    (hZ : Z.IsSubnormal) : (CFSG.pPrimeCore p Z).map Z.subtype ≤ CFSG.pPrimeCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ Subgroup.normalizer (X : Set H) →
      (CFSG.pPrimeCore p X).map X.subtype ≤ (CFSG.pPrimeCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (CFSG.pPrimeCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((CFSG.pPrimeCore p X).map X.subtype).subgroupOf Y ≤ CFSG.pPrimeCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        obtain ⟨x, hx, hxl⟩ := hl
        have hyN : (y : H) ∈ Subgroup.normalizer (X : Set H) := hYN y.2
        let φ := Subgroup.normalizerMonoidHom X ⟨(y : H), hyN⟩
        have hfix : (CFSG.pPrimeCore p X).map φ.toMonoidHom = CFSG.pPrimeCore p X :=
          (Subgroup.characteristic_iff_map_eq.mp inferInstance) φ
        refine ⟨φ x, ?_, ?_⟩
        · rw [← hfix]
          exact Subgroup.mem_map_of_mem _ hx
        · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hxl]
          rfl
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv,
          Subgroup.card_map_of_injective X.subtype_injective]
        exact CFSG.pPrimeCore_coprime_card
    calc (CFSG.pPrimeCore p X).map X.subtype
        = (((CFSG.pPrimeCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (CFSG.pPrimeCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hZ with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => ?_⟩, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hl
      let φ := Subgroup.normalizerMonoidHom (⊤ : Subgroup H) ⟨g, by
        rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top g⟩
      have hfix : (CFSG.pPrimeCore p (⊤ : Subgroup H)).map φ.toMonoidHom =
          CFSG.pPrimeCore p _ :=
        (Subgroup.characteristic_iff_map_eq.mp inferInstance) φ
      refine ⟨φ x, ?_, ?_⟩
      · rw [← hfix]
        exact Subgroup.mem_map_of_mem _ hx
      · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]
    · rw [Subgroup.card_map_of_injective (⊤ : Subgroup H).subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

theorem nonempty_quot_equiv_map {N : Subgroup H} [N.Normal] (hN : N = CFSG.pPrimeCore 3 H)
    {Z : Subgroup H} (hZ : Z.IsSubnormal) :
    Nonempty (↥Z ⧸ CFSG.pPrimeCore 3 ↥Z ≃* ↥(Z.map (QuotientGroup.mk' N))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  subst hN
  set f : ↥Z →* H ⧸ CFSG.pPrimeCore 3 H :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)).comp Z.subtype with hf
  have hker : f.ker = CFSG.pPrimeCore 3 ↥Z := by
    have hk : f.ker = (CFSG.pPrimeCore 3 H).comap Z.subtype := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [hk]
    refine le_antisymm ?_ ?_
    · apply le_sSup
      refine ⟨Subgroup.Normal.comap inferInstance _, ?_⟩
      have hle : ((CFSG.pPrimeCore 3 H).comap Z.subtype).map Z.subtype ≤
          CFSG.pPrimeCore 3 H := Subgroup.map_comap_le _ _
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective Z.subtype_injective] at hdvd
      exact Nat.Coprime.coprime_dvd_right hdvd CFSG.pPrimeCore_coprime_card
    · rw [← Subgroup.map_le_iff_le_comap]
      exact map_pPrimeCore_le_of_isSubnormal' hZ
  have hrange : f.range = Z.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))⟩

end Cores

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ker148_eq_pPrimeCore {A M : Subgroup G} (hAM : A ≤ M) :
    ker148 A M = CFSG.pPrimeCore 3 ↥(M ⊔ A) := by
  have h : pPrimeCoreOf 3 M = pPrimeCoreOf 3 (M ⊔ A) := by rw [sup_eq_left.mpr hAM]
  change (pPrimeCoreOf 3 M).subgroupOf (M ⊔ A) = _
  rw [h]
  change ((CFSG.pPrimeCore 3 ↥(M ⊔ A)).map (M ⊔ A).subtype).comap (M ⊔ A).subtype = _
  exact Subgroup.comap_map_eq_self_of_injective (M ⊔ A).subtype_injective _

omit [Finite G] in
theorem subgroupOf_mem_thetaComponents {K K' : Subgroup G} (hKK' : K = K') {Z : Subgroup G}
    (hZ : Z ∈ thetaComponentsIn K) :
    Z ≤ K' ∧ Z.subgroupOf K' ∈ thetaComponents 3 ↥K' := by
  subst hKK'
  obtain ⟨Z', hZ', rfl⟩ := hZ
  refine ⟨Subgroup.map_subtype_le _, ?_⟩
  change (Z'.map K.subtype).comap K.subtype ∈ _
  rwa [Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

theorem exists_pair_of_twin {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) (h152 : Item152 A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    (hMY : ¬ M ≤ Subgroup.normalizer (Y : Set G)) (hAN : A ≤ Subgroup.normalizer (M : Set G)) :
    letI := ker148_normal hAN
    ∃ U V : Subgroup ↥(img148 A M (deltaZero A (lB A) M)),
      U.IsSubnormal ∧ V.IsSubnormal ∧ Group.IsPerfect U ∧ Group.IsPerfect V ∧ U ≠ ⊥ ∧ V ≠ ⊥ ∧
      ⁅U, V⁆ = ⊥ ∧ Nat.card U = Nat.card V ∧
      Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* ↥U) := by
  let := ker148_normal hAN
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hMA : M = M ⊔ A := (sup_eq_left.mpr hAM).symm
  set π := QuotientGroup.mk' (ker148 A M) with hπ
  obtain ⟨t, htM, htN⟩ := Set.not_subset.mp hMY
  set Yt := Y.map (MulAut.conj t).toMonoidHom with hYt
  have hYYt : Y ≠ Yt := fun he => htN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  obtain ⟨Y', hY', hYY'⟩ := mem_thetaComponentsIn_of_item152 h h152 hY hM
  change Y'.map M.subtype = Y at hYY'
  set σ : ↥M ≃* ↥M := MulAut.conj (⟨t, htM⟩ : M) with hσ
  have hYtθ : Yt ∈ thetaComponentsIn M := by
    refine ⟨Y'.map σ.toMonoidHom, map_mulEquiv_mem_thetaComponents Nat.prime_three σ hY', ?_⟩
    change (Y'.map σ.toMonoidHom).map M.subtype = Y.map (MulAut.conj t).toMonoidHom
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hYθ : Y ∈ thetaComponentsIn M := ⟨Y', hY', hYY'⟩
  obtain ⟨hYH, hY₁⟩ := subgroupOf_mem_thetaComponents hMA hYθ
  obtain ⟨hYtH, hY₂⟩ := subgroupOf_mem_thetaComponents hMA hYtθ
  have hker := ker148_eq_pPrimeCore hAM
  have hθker : aschbacherSolvableCore 3 ↥(M ⊔ A) ≤ ker148 A M := by
    rw [hker]
    obtain ⟨-, hθc, hθ3, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥(M ⊔ A)) Nat.prime_three
    have : (aschbacherSolvableCore 3 ↥(M ⊔ A)).Normal := Subgroup.normal_of_characteristic _
    exact le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3⟩
  set Y₁ := Y.subgroupOf (M ⊔ A) with hY₁def
  set Y₂ := Yt.subgroupOf (M ⊔ A) with hY₂def
  have hne : Y₁ ≠ Y₂ := by
    intro he
    apply hYYt
    rw [hY₁def, hY₂def, Subgroup.subgroupOf_inj, inf_eq_left.mpr hYH,
      inf_eq_left.mpr hYtH] at he
    exact he
  have hc := commutator_le_of_mem_thetaComponents hY₁ hY₂ hne
  set Yb₁ := Y₁.map π with hYb₁
  set Yb₂ := Y₂.map π with hYb₂
  have hsn₁ : Yb₁.IsSubnormal := hY₁.2.1.map (QuotientGroup.mk'_surjective _)
  have hsn₂ : Yb₂.IsSubnormal := hY₂.2.1.map (QuotientGroup.mk'_surjective _)
  have : Group.IsPerfect ↥Y₁ := hY₁.1
  have : Group.IsPerfect ↥Y₂ := hY₂.1
  have hp₁ : Group.IsPerfect ↥Yb₁ := Group.IsPerfect.map π
  have hp₂ : Group.IsPerfect ↥Yb₂ := Group.IsPerfect.map π
  have hcomm : ⁅Yb₁, Yb₂⁆ = ⊥ := by
    rw [hYb₁, hYb₂, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hπ,
      QuotientGroup.ker_mk']
    exact hc.trans hθker
  have hne₁ : Yb₁ ≠ ⊥ := by
    intro h0
    rw [hYb₁, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk', hker] at h0
    obtain ⟨x, hxY, hx3, y, -, hxy⟩ :=
      Proof153Twin.hasNonCentralThree_of_mem_scriptY4 hY.prop.1
    have hxO : (⟨x, hYH hxY⟩ : ↥(M ⊔ A)) ∈ CFSG.pPrimeCore 3 ↥(M ⊔ A) :=
      h0 (Subgroup.mem_subgroupOf.mpr hxY)
    have hx1 : (⟨x, hYH hxY⟩ : ↥(M ⊔ A)) = 1 := by
      refine Sec13.eq_one_of_pow_three_pow_of_not_dvd
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card) hxO
        (k := 1) ?_
      apply Subtype.ext
      simpa using hx3
    have hx : x = 1 := congrArg Subtype.val hx1
    apply hxy
    rw [hx, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _
  have htH : t ∈ M ⊔ A := (le_sup_left : M ≤ M ⊔ A) htM
  set t' : ↥(M ⊔ A) := ⟨t, htH⟩ with ht'
  have hY₂eq : Y₂ = Y₁.map (MulAut.conj t').toMonoidHom := by
    ext x
    rw [hY₂def, Subgroup.mem_subgroupOf, hYt]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨y, hYH hy⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
      apply Subtype.ext
      simpa [MulAut.conj_apply, ht'] using hyx
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, by simp [MulAut.conj_apply, ht']⟩
  have hYb₂eq : Yb₂ = Yb₁.map (MulAut.conj (π t')).toMonoidHom := by
    rw [hYb₂, hYb₁, hY₂eq, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hcard : Nat.card Yb₁ = Nat.card Yb₂ := by
    rw [hYb₂eq]
    exact (Subgroup.card_map_of_injective (MulAut.conj (π t')).injective).symm
  have hne₂ : Yb₂ ≠ ⊥ := by
    intro h0
    apply hne₁
    refine Subgroup.eq_bot_of_card_eq _ ?_
    rw [hcard, h0, Subgroup.card_bot]
  have hMY' : M ∈ scriptY A := hM2.1
  obtain ⟨heq149, -, -⟩ := h149 M hMY'
  have hX0Δ : oPrimeResidualOf 3 (delta A (lB A) M) ≤ deltaZero A (lB A) M := by
    rw [heq149]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  have hYX0 : Y ≤ oPrimeResidualOf 3 (delta A (lB A) M) :=
    le_oPrimeResidualOf_delta hY.prop.1 hYM
  have hMX0 := normalizer_le_normalizer_oPrimeResidualOf_delta h149 hMY'
  have hYtX0 : Yt ≤ oPrimeResidualOf 3 (delta A (lB A) M) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMX0 htM) y).mp (hYX0 hy)
  set D := img148 A M (deltaZero A (lB A) M) with hD
  have hle₁ : Yb₁ ≤ D := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr ((hYX0.trans hX0Δ) (Subgroup.mem_subgroupOf.mp hx))
  have hle₂ : Yb₂ ≤ D := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr ((hYtX0.trans hX0Δ) (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨Yb₁.subgroupOf D, Yb₂.subgroupOf D, hsn₁.subgroupOf, hsn₂.subgroupOf,
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle₁).symm.toMonoidHom)
      (MulEquiv.surjective _),
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle₂).symm.toMonoidHom)
      (MulEquiv.surjective _), ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact hne₁ (disjoint_self.mp (h0.mono_right hle₁))
  · intro h0
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact hne₂ (disjoint_self.mp (h0.mono_right hle₂))
  · refine (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp ?_
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle₁, inf_eq_left.mpr hle₂]
    exact hcomm
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv]
    exact hcard
  · obtain ⟨e₂⟩ := nonempty_quot_equiv_map hker hY₁.2.1
    set e : ↥Y ≃* ↥Y₁ := (Subgroup.subgroupOfEquivOfLe hYH).symm with he
    exact ⟨(QuotientGroup.congr (CFSG.pPrimeCore 3 ↥Y) (CFSG.pPrimeCore 3 ↥Y₁) e
      (CFSG.pPrimeCore_map_iso 3 e)).trans (e₂.trans (Subgroup.subgroupOfEquivOfLe hle₁).symm)⟩

end CFSG.RankThree.PartTwo.Sec15.Proof153Twin2
