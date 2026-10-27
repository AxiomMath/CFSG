module

public import CFSG.RankThree.PartTwo.Sec15.Ronan153BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Gagen153Case7
import CFSG.RankThree.PartTwo.Sec15.Ronan152SixHelpers
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan153Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec15.Proof153Twin2

variable {G : Type} [Group G] [Finite G]

theorem exists_pair_of_twin_big {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h149 : Item149 A (lB A)) (h152 : Item152Big A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y) {M : Subgroup G}
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
  obtain ⟨Y', hY', hYY'⟩ := Ronan152Six.mem_thetaComponentsIn_of_big h h152 hY hYb hM
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

theorem twinTypesAt_of_big
    (h148 : Item148R) (h149 : Sec16.Item149S14) {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) (h152 : Item152Big A (lB A)) {Y : Subgroup G}
    (hY : Y ∈ scriptY0Star A (lB A)) (hYb : Big152 Y) : TwinTypesAt A Y := by
  intro hE M hM hMY
  have h := hR.toSec14Std
  obtain ⟨hYM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hAN : A ≤ Subgroup.normalizer (M : Set G) := hM2.1.2
  let := ker148_normal hAN
  obtain ⟨U, V, hU, hV, hUp, hVp, hU1, hV1, hUV, hcard, ⟨eY⟩⟩ :=
    exists_pair_of_twin_big h (h149 G A c L h) h152 hY hYb hM hMY hAN
  refine types_of_quot_equiv hY.prop.1 hE eY ?_
  have hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA10s : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA5Z : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hid : ∀ (X : Type) [Group X], (MonoidHom.id X).ker ≤ Subgroup.center X := fun X _ => by
    rw [MonoidHom.ker_id]
    exact bot_le
  rcases (h148 G A c L hR M hM2.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7'
  ·
    exfalso
    have hD : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
    apply hU1
    rw [eq_bot_iff]
    intro x _
    have hx : (x : ↥(M ⊔ A) ⧸ ker148 A M) ∈ (⊥ : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)) := by
      rw [← hD]
      exact x.2
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp hx))
  ·
    exfalso
    obtain ⟨c', -, -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    · exact false_of_mulEquiv_quasisimple (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1) φ
        hU hUp hVp hU1 hV1 hUV
    · exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · rcases hε with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p f)
        exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
        exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · exact false_of_isTripleCover h6 hU hUp hVp hU1 hV1 hUV
    · exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, htypes⟩ := h3
    rcases htypes with hON | ⟨U₀, V₀, hU₀, hV₀, hsup, hcomm, -, hU6, hV6⟩ |
        ⟨U₀, V₀, hU₀, hV₀, hinf, hsup, hU6, ⟨eV⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨_, ⟨φ⟩⟩
    · exfalso
      have := CFSG.Sporadic.ON.isSimpleGroup_ON
      exact false_of_isTripleCover hON hU hUp hVp hU1 hV1 hUV
    ·
      right
      obtain ⟨hψ₁, hk₁⟩ := tripleCover_cover hU6.2.some
      obtain ⟨hψ₂, hk₂⟩ := tripleCover_cover hV6.2.some
      rcases le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ (φ₁ := MonoidHom.id ↥U₀)
          Function.surjective_id hψ₂ hk₂ (φ₂ := MonoidHom.id ↥V₀) Function.surjective_id hU hUp
          hVp hU1 hV1 hUV with ⟨hUU, -⟩ | ⟨hUV₀, -⟩
      · exact exists_surjective_of_le_tripleCover hU6 hU hUp hU1 hUU
      · exact exists_surjective_of_le_tripleCover hV6 hU hUp hU1 hUV₀
    ·
      exfalso
      have hcomm : ⁅U₀, V₀⁆ = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact Subgroup.commutator_le_inf U₀ V₀
      obtain ⟨hψ₁, hk₁⟩ := tripleCover_cover hU6.2.some
      have h360 : ∀ {W : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}, W.IsSubnormal →
          Group.IsPerfect W → W ≠ ⊥ → W ≤ U₀ → 360 ∣ Nat.card W := by
        intro W hW hWp hW1 hWU
        obtain ⟨g, hg, -, -⟩ := exists_surjective_of_le_tripleCover hU6 hW hWp hW1 hWU
        have := Subgroup.card_dvd_of_surjective hg
        rwa [card_alternatingGroup_six] at this
      have h60 : ∀ {W : Subgroup ↥(img148 A M (deltaZero A (lB A) M))}, W.IsSubnormal →
          Group.IsPerfect W → W ≠ ⊥ → W ≤ V₀ → Nat.card W = 60 := by
        intro W hW hWp hW1 hWV
        rw [eq_of_le_simple_factor hA5Z eV hW hWp hW1 hWV, Nat.card_congr eV.toEquiv,
          card_alternatingGroup_five]
      rcases le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ (φ₁ := MonoidHom.id ↥U₀)
          Function.surjective_id (ψ₂ := MonoidHom.id (alternatingGroup (Fin 5)))
          Function.surjective_id (hid _) (φ₂ := eV.symm.toMonoidHom) eV.symm.surjective hU hUp
          hVp hU1 hV1 hUV with ⟨hUU, hVV⟩ | ⟨hUV₀, hVU⟩
      · have h1 := h360 hU hUp hU1 hUU
        rw [hcard, h60 hV hVp hV1 hVV] at h1
        norm_num at h1
      · have h1 := h360 hV hVp hV1 hVU
        rw [← hcard, h60 hU hUp hU1 hUV₀] at h1
        norm_num at h1
    ·
      left
      obtain ⟨hU', hV', hUp', hVp', hU1', hV1', hUV', -, -⟩ :=
        pair_map φ hU hV hUp hVp hU1 hV1 hUV
      rcases pair_prod hA5Z hA5Z hU' hV' hUp' hVp' hU1' hV1' hUV' with
        ⟨⟨ψ⟩, -⟩ | ⟨⟨ψ⟩, -⟩
      · exact ⟨(U.equivMapOfInjective φ.toMonoidHom φ.injective).trans ψ⟩
      · exact ⟨(U.equivMapOfInjective φ.toMonoidHom φ.injective).trans ψ⟩
    ·
      exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
    ·
      have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
      exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact (false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV).elim
  ·
    exfalso
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 (3 * n))
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · have h2 : 2 ^ (3 * n) ≠ 2 := by
        intro h22
        have := Nat.pow_right_injective (le_refl 2) (h22.trans (pow_one 2).symm)
        omega
      have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) h2
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    exfalso
    obtain ⟨⟨φ⟩, -⟩ := h6
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    have hJZ : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥ := sporadicModels131.2.2.2
    obtain ⟨hU', hV', hUp', hVp', hU1', hV1', hUV', hcU, hcV⟩ :=
      pair_map φ hU hV hUp hVp hU1 hV1 hUV
    rcases pair_prod hA5Z hJZ hU' hV' hUp' hVp' hU1' hV1' hUV' with
      ⟨⟨ψ₁⟩, ⟨ψ₂⟩⟩ | ⟨⟨ψ₁⟩, ⟨ψ₂⟩⟩
    · have h1 := Nat.card_congr ψ₁.toEquiv
      have h2 := Nat.card_congr ψ₂.toEquiv
      rw [hcU, hcard, ← hcV, h2, card_alternatingGroup_five, CFSG.Sporadic.J2.card_J2] at h1
      norm_num at h1
    · have h1 := Nat.card_congr ψ₁.toEquiv
      have h2 := Nat.card_congr ψ₂.toEquiv
      rw [hcU, hcard, ← hcV, h2, card_alternatingGroup_five, CFSG.Sporadic.J2.card_J2] at h1
      norm_num at h1
  ·
    exact (claim153TwinCase7_of_item148R h148 G A c L hR Y hY hE M hM hMY hAN h7').elim

end CFSG.RankThree.PartTwo.Sec15.Ronan153Big
