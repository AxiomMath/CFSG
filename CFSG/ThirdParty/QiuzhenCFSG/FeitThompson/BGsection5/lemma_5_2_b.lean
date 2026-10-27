module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.lemma_5_2_a

namespace CFSG
end CFSG
open CFSG

/-! # Lemma 5.2(b) from BG Section 5 -/

section

open scoped commutatorElement

public theorem CFSG.lemma_5_2_b
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {E : Subgroup R} (hE : E ∈ elementaryAbelianSubgroupsOfRank p 2 R)
    (hEmax : E ∈ maximalElementaryAbelianSubgroups p R) :
    Nat.card (Ω₁Z p R) = p ∧ Ω₁Z₂ p R ∈ elementaryAbelianSubgroupsOfRank p 2 R := by
  classical
  rcases hE with ⟨hEcard, hEelem⟩
  rcases hEmax with ⟨_hEelem', hEmax'⟩
  letI : IsElementaryAbelian p E := hEelem
  let Z : Subgroup R := Ω₁Z p R
  let W : Subgroup R := Ω₁Z₂ p R
  have hZelem : IsElementaryAbelian p Z := by
    let Ωc : Subgroup (Subgroup.center R) := omega₁ (G := Subgroup.center R) (p := p)
    have hΩcelem : IsElementaryAbelian p Ωc := by
      letI : IsMulCommutative (Subgroup.center R) := inferInstance
      simpa [Ωc] using omega1_isElementaryAbelian_of_commutative (p := p) (Subgroup.center R)
    letI : IsElementaryAbelian p Ωc := hΩcelem
    refine
      { toIsMulCommutative := by
          refine IsMulCommutative.of_comm ?_
          intro x y
          apply Subtype.ext
          have hxcenter : (x : R) ∈ Subgroup.center R := by
            rcases Subgroup.mem_map.mp x.2 with ⟨x', _hx', hx⟩
            rw [← hx]
            exact x'.2
          exact (Subgroup.mem_center_iff.mp hxcenter (y : R)).symm
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    rcases Subgroup.mem_map.mp x.2 with ⟨y, hy, hyx⟩
    let yΩ : Ωc := ⟨y, hy⟩
    have hypow : yΩ ^ p = 1 := by
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p Ωc) yΩ
    have hx_eq : ((x : Z) : R) = ((yΩ : Ωc) : Subgroup.center R) := by
      simpa [yΩ] using hyx.symm
    simpa [hx_eq] using congrArg (fun z : Ωc => (((z : Ωc) : Subgroup.center R) : R)) hypow
  have hZcentE : Z ≤ Subgroup.centralizer (E : Set R) := by
    calc
      Z ≤ Subgroup.center R := by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
        exact y.property
      _ ≤ Subgroup.centralizer (E : Set R) := Subgroup.center_le_centralizer (E : Set R)
  have hZ_le_center : Z ≤ Subgroup.center R := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
    exact y.property
  have hEcentZ : E ≤ Subgroup.centralizer (Z : Set R) := by
    exact (Subgroup.le_centralizer_iff).mp hZcentE
  have hZEelem : IsElementaryAbelian p ↥(Z ⊔ E : Subgroup R) := by
    letI : IsElementaryAbelian p Z := hZelem
    exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := Z) (C := E) hEcentZ
  have hEZ_eq : E = Z ⊔ E := by
    exact hEmax' (Z ⊔ E : Subgroup R) le_sup_right hZEelem
  have hZ_le_E : Z ≤ E := by
    intro z hz
    have hzsup : z ∈ Z ⊔ E := Subgroup.mem_sup_left hz
    simpa [← hEZ_eq] using hzsup
  have hR_not_cyclic : ¬ IsCyclic R := by
    intro hcyc
    letI : IsCyclic R := hcyc
    have hgen_le_one : generatorRank R ≤ 1 := generatorRank_le_one_of_isCyclic (G := R) (by infer_instance)
    have hprimeRank_le_one :
        ∀ q : ℕ, Nat.Prime q → primeRank q R ≤ 1 := by
      intro q hq
      rw [primeRank]
      refine csSup_le ?_ ?_
      · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := R), inferInstance, zero_le⟩
      intro n hn
      rcases hn with ⟨A, _hApA, hAcomm, hnA⟩
      letI : IsMulCommutative A := hAcomm
      have hAle : generatorRank A ≤ 1 := by
        haveI : IsCyclic A := isCyclic_of_injective A.subtype A.subtype_injective
        exact generatorRank_le_one_of_isCyclic (G := A) (by infer_instance)
      exact hnA.trans hAle
    have hgroupRank_le_one : groupRank R ≤ 1 := by
      rw [groupRank]
      refine csSup_le ?_ ?_
      · exact ⟨0, p, Fact.out, zero_le⟩
      intro n hn
      rcases hn with ⟨q, hq, hnq⟩
      exact hnq.trans (hprimeRank_le_one q hq)
    exact (by decide : ¬ 3 ≤ (1 : ℕ)) (le_trans hR hgroupRank_le_one)
  have hR_nontrivial : Nontrivial R := by
    refine not_subsingleton_iff_nontrivial.mp ?_
    intro hsub
    letI : Subsingleton R := hsub
    exact hR_not_cyclic (inferInstance : IsCyclic R)
  have hZ_nontrivial : Nontrivial (Subgroup.center R) := hpR.center_nontrivial
  have hcenter_card_gt_one : 1 < Nat.card (Subgroup.center R) := by
    exact Finite.one_lt_card
  have hpdvd_center : p ∣ Nat.card (Subgroup.center R) := by
    have hcenter_p : IsPGroup p (Subgroup.center R) := hpR.to_subgroup (Subgroup.center R)
    rcases (IsPGroup.nontrivial_iff_card (p := p) (G := Subgroup.center R) (hG := hcenter_p)).1 hZ_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p (Nat.ne_of_gt hn)
  have hZ_ne_bot : Z ≠ ⊥ := by
    simpa [Z, Ω₁Z] using omega₁_map_subtype_ne_bot (M := Subgroup.center R) (p := p) hpdvd_center
  have hZpow : ∀ z : Z, (z : R) ^ p = 1 := by
    intro z
    exact congrArg Subtype.val <|
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p Z) z
  have hErank : E ∈ elementaryAbelianSubgroupsOfRank p 2 R := ⟨hEcard, hEelem⟩
  have hEmaximal : E ∈ maximalElementaryAbelianSubgroups p R := ⟨hEelem, hEmax'⟩
  have hZcard_eq_p : Nat.card Z = p := by
    have hZp : IsPGroup p Z := IsElementaryAbelian.isPGroup p Z
    rcases hZp.exists_card_eq with ⟨k, hk⟩
    have hk_ne_zero : k ≠ 0 := by
      intro hk0
      apply hZ_ne_bot
      apply (Subgroup.card_eq_one (H := Z)).1
      simpa [hk0] using hk
    have hk_le_two : k ≤ 2 := by
      have hcard_le : Nat.card Z ≤ Nat.card E := Subgroup.card_le_of_le hZ_le_E
      rw [hk, hEcard] at hcard_le
      exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_le
    have hk_ne_two : k ≠ 2 := by
      intro hk2
      have hZcard_eq : Nat.card Z = p ^ 2 := by simpa [hk2] using hk
      have hZ_eq_E : Z = E := Subgroup.eq_of_le_of_card_ge hZ_le_E (by rw [hZcard_eq, hEcard])
      have hE_le_T : E ≤ CΩ₁Z₂ p R := by
        intro e he
        rw [CΩ₁Z₂, Subgroup.mem_centralizer_iff]
        intro w hw
        have heZ : e ∈ Z := by simpa [hZ_eq_E] using he
        have hecent : e ∈ Subgroup.center R := by
          rcases Subgroup.mem_map.mp heZ with ⟨y, hy, rfl⟩
          exact y.property
        exact (Subgroup.mem_center_iff.mp hecent) w
      exact (lemma_5_2_a (p := p) hpodd (R := R) hpR hR (hE := hErank) (hEmax := hEmaximal))
        hE_le_T
    have hk_one : k = 1 := by omega
    simpa [hk_one] using hk
  have hW_noncyclic_raw :
      ¬ IsCyclic (omega₁ (G := ↥(Subgroup.upperCentralSeries R 2)) (p := p)) := by
    haveI : Fact (IsPGroup p R) := ⟨hpR⟩
    exact (lemma_4_5_c (R := R) (p := p) hpodd hR_not_cyclic).1
  have hW_noncyclic : ¬ IsCyclic W := by
    intro hWcyc
    let Ωsub : Subgroup (Subgroup.upperCentralSeries R 2) :=
      omega₁ (G := ↥(Subgroup.upperCentralSeries R 2)) (p := p)
    have hmapcyc : IsCyclic (Ωsub.map (Subgroup.upperCentralSeries R 2).subtype) := by
      rcases (Subgroup.isCyclic_iff_exists_zpowers_eq_top W).mp hWcyc with ⟨g, hg⟩
      apply (Subgroup.isCyclic_iff_exists_zpowers_eq_top
        (Ωsub.map (Subgroup.upperCentralSeries R 2).subtype)).mpr
      exact ⟨g, by simpa [W, Ω₁Z₂, z2OmegaCandidate, Ωsub] using hg⟩
    letI : IsCyclic (Ωsub.map (Subgroup.upperCentralSeries R 2).subtype) := hmapcyc
    let e : Ωsub ≃* Ωsub.map (Subgroup.upperCentralSeries R 2).subtype :=
      Subgroup.equivMapOfInjective Ωsub (Subgroup.upperCentralSeries R 2).subtype
        (Subgroup.upperCentralSeries R 2).subtype_injective
    have hΩcyc : IsCyclic Ωsub := isCyclic_of_injective e.toMonoidHom e.injective
    exact hW_noncyclic_raw (by simpa [Ωsub] using hΩcyc)
  have hWexp_dvd : Monoid.exponent ↥W ∣ p := by
    simpa [W, Ω₁Z₂] using z2OmegaCandidate_exponent_dvd_p_of_odd (G := R) (p := p) hpodd
  have hWpow : ∀ w : W, (w : R) ^ p = 1 := by
    intro w
    exact congrArg Subtype.val <|
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hWexp_dvd w
  have hcomm_mem_Z {w r : R} (hw : w ∈ W) : ⁅w, r⁆ ∈ Z := by
    have hwZ2 : w ∈ Subgroup.upperCentralSeries R 2 := by
      simpa [W, Ω₁Z₂] using z2OmegaCandidate_le_upperCentralSeries_two (G := R) (p := p) hw
    have hwpow : w ^ p = 1 := hWpow ⟨w, hw⟩
    simpa [Z, Ω₁Z] using
      commutator_mem_omega₁_center_of_mem_upperCentralSeries_two_of_pow_eq_one
        (G := R) (p := p) (x := w) (g := r) hwZ2 hwpow
  have hWcard : Nat.card W = p ^ 2 := by
    have hWp : IsPGroup p W := hpR.to_subgroup W
    have hW_nontrivial : Nontrivial W := not_subsingleton_iff_nontrivial.mp fun hsub =>
      letI : Subsingleton W := hsub
      hW_noncyclic (inferInstance : IsCyclic W)
    let C : Subgroup R := W ⊓ Subgroup.centralizer (E : Set R)
    have hC_le_W : C ≤ W := inf_le_left
    have hC_le_centE : C ≤ Subgroup.centralizer (E : Set R) := inf_le_right
    have hC_le_E : C ≤ E := by
      intro c hc
      have hczpow_centE : Subgroup.zpowers c ≤ Subgroup.centralizer (E : Set R) :=
        (Subgroup.zpowers_le).2 hc.2
      have hczpow_elem : IsElementaryAbelian p (Subgroup.zpowers c) :=
        isElementaryAbelian_zpowers_of_pow_eq_one (p := p) (x := c) (hWpow ⟨c, hc.1⟩)
      letI : IsElementaryAbelian p (Subgroup.zpowers c) := hczpow_elem
      have hsup_elem : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers c : Subgroup R) := by
        exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := E)
          (C := Subgroup.zpowers c) hczpow_centE
      have hsup_eq : E ⊔ Subgroup.zpowers c = E :=
        (hEmax' (E ⊔ Subgroup.zpowers c) le_sup_left hsup_elem).symm
      have hc_sup : c ∈ E ⊔ Subgroup.zpowers c := by
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
      simpa [hsup_eq] using hc_sup
    have hCelem : IsElementaryAbelian p C := isElementaryAbelian_of_le (p := p) hC_le_E
    letI : IsElementaryAbelian p C := hCelem
    have hZ_le_W : Z ≤ W := by
      intro z hz
      have hzcent : z ∈ Subgroup.center R := hZ_le_center hz
      let z₂ : Subgroup.upperCentralSeries R 2 := ⟨z,
        Subgroup.upperCentralSeries_mono (G := R) (show 1 ≤ 2 by decide)
          (by simpa [Subgroup.upperCentralSeries_one] using hzcent)⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨z₂, ?_, rfl⟩
      rw [omega₁, omega]
      refine Subgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq, pow_one]
      apply Subtype.ext
      exact hZpow ⟨z, hz⟩
    have hZ_le_C : Z ≤ C := by
      intro z hz
      exact ⟨hZ_le_W hz, hZcentE hz⟩
    have hC_ne_E : C ≠ E := by
      intro hCE
      have hE_le_W : E ≤ W := by
        intro e he
        exact (show e ∈ C by simpa [hCE] using he).1
      have hE_norm : E.Normal := by
        have hnorm_top : Subgroup.normalizer (E : Set R) = ⊤ := by
          apply top_unique
          intro r _hr
          rw [Subgroup.mem_normalizer_iff]
          intro e
          constructor
          · intro he
            have hcommE : ⁅e, r⁆ ∈ E := hZ_le_E (hcomm_mem_Z (hE_le_W he))
            have hconj : r * e * r⁻¹ = ⁅e, r⁆⁻¹ * e := by
              simp [commutatorElement_def, mul_assoc]
            have hconjE : ⁅e, r⁆⁻¹ * e ∈ E := E.mul_mem (E.inv_mem hcommE) he
            rw [hconj]
            exact hconjE
          · intro he
            have hcommE : ⁅r * e * r⁻¹, r⁻¹⁆ ∈ E := hZ_le_E (hcomm_mem_Z (hE_le_W he))
            have hback : e = ⁅r * e * r⁻¹, r⁻¹⁆⁻¹ * (r * e * r⁻¹) := by
              simp [commutatorElement_def, mul_assoc]
            have hbackE : ⁅r * e * r⁻¹, r⁻¹⁆⁻¹ * (r * e * r⁻¹) ∈ E :=
              E.mul_mem (E.inv_mem hcommE) he
            rw [hback]
            exact hbackE
        exact (Subgroup.normalizer_eq_top_iff).mp hnorm_top
      letI : E.Normal := hE_norm
      obtain ⟨B, _hBnorm, hBelem, hBcard, hEB⟩ :=
        exists_normal_elementaryAbelian_card_p3_containing_rank_two_normal
          (p := p) hpodd hpR hR hErank
      have hE_eq_B : E = B := hEmax' B hEB hBelem
      have hpow_eq : p ^ 2 = p ^ 3 := by
        calc
          p ^ 2 = Nat.card E := hEcard.symm
          _ = Nat.card B := by rw [hE_eq_B]
          _ = p ^ 3 := hBcard
      exact (ne_of_lt ((Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).2
        (by decide : 2 < 3))) hpow_eq
    have hC_eq_Z : C = Z := by
      rcases (IsElementaryAbelian.isPGroup p C).exists_card_eq with ⟨k, hk⟩
      have hk_le_two : k ≤ 2 := by
        have hcard_le : Nat.card C ≤ Nat.card E := Subgroup.card_le_of_le hC_le_E
        rw [hk, hEcard] at hcard_le
        exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_le
      have hk_ge_one : 1 ≤ k := by
        have hcard_ge : Nat.card Z ≤ Nat.card C := Subgroup.card_le_of_le hZ_le_C
        rw [hZcard_eq_p, hk] at hcard_ge
        have hcard_ge' : p ^ 1 ≤ p ^ k := by simpa using hcard_ge
        exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_ge'
      have hk_ne_two : k ≠ 2 := by
        intro hk2
        have hCcard_eq : Nat.card C = p ^ 2 := by simpa [hk2] using hk
        have hC_eq_E : C = E := Subgroup.eq_of_le_of_card_ge hC_le_E (by rw [hCcard_eq, hEcard])
        exact hC_ne_E hC_eq_E
      have hk_one : k = 1 := by
        omega
      have hcard_le : Nat.card C ≤ Nat.card Z := by
        rw [hk, hZcard_eq_p]
        simp [hk_one]
      exact (Subgroup.eq_of_le_of_card_ge hZ_le_C hcard_le).symm
    let Csub : Subgroup W := C.subgroupOf W
    have hW_le_normE : W ≤ Subgroup.normalizer (E : Set R) := by
      intro w hw
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he
        have hcommE : ⁅w, e⁆ ∈ E := hZ_le_E (hcomm_mem_Z hw)
        simpa [commutatorElement_def, mul_assoc] using E.mul_mem hcommE he
      · intro he
        have hwinv : w⁻¹ ∈ W := W.inv_mem hw
        have hcommE : ⁅w⁻¹, w * e * w⁻¹⁆ ∈ E := hZ_le_E (hcomm_mem_Z hwinv)
        simpa [commutatorElement_def, mul_assoc] using E.mul_mem hcommE he
    let φ : W →* MulAut E :=
      (Subgroup.normalizerMonoidHom (H := E)).comp (Subgroup.inclusion hW_le_normE)
    have hker : φ.ker = Csub := by
      ext w
      constructor
      · intro hwker
        change (w : R) ∈ C
        refine ⟨w.2, ?_⟩
        show (w : R) ∈ Subgroup.centralizer (E : Set R)
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        let eE : E := ⟨e, he⟩
        have hfix : φ w eE = eE := by
          simpa using congrArg (fun f : MulAut E => f eE) hwker
        have hconj : (w : R) * e * (w : R)⁻¹ = e := by
          simpa [φ] using congrArg Subtype.val hfix
        have hmul : (w : R) * e = e * (w : R) := by
          simpa [mul_assoc] using congrArg (fun t : R => t * (w : R)) hconj
        exact hmul.symm
      · intro hwC
        change φ w = 1
        ext e
        have hwcent : (w : R) ∈ Subgroup.centralizer (E : Set R) := hwC.2
        have hmul : ((e : E) : R) * (w : R) = (w : R) * ((e : E) : R) :=
          (Subgroup.mem_centralizer_iff.mp hwcent) ((e : E) : R) e.2
        have hconj : (w : R) * ((e : E) : R) * (w : R)⁻¹ = ((e : E) : R) := by
          calc
            (w : R) * ((e : E) : R) * (w : R)⁻¹ = ((e : E) : R) * (w : R) * (w : R)⁻¹ := by
              rw [hmul.symm]
            _ = ((e : E) : R) := by simp [mul_assoc]
        simpa [φ] using hconj
    have hQp : IsPGroup p (W ⧸ φ.ker) := hWp.to_quotient (φ.ker)
    haveI : Fact (IsPGroup p (W ⧸ φ.ker)) := ⟨hQp⟩
    have hQodd : Odd (Nat.card (W ⧸ φ.ker)) := by
      rcases hQp.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact (show Odd p from (Fact.out : Nat.Prime p).odd_of_ne_two hpodd).pow
    have hQle : Nat.card (W ⧸ Csub) ≤ p := by
      simpa [hker] using
        quotient_centralizer_card_le_p_of_elementaryAbelian_rank_two
          (p := p) (E := E) (Q := W ⧸ φ.ker) hEcard hQodd
          (i := QuotientGroup.kerLift φ) (hi := QuotientGroup.kerLift_injective (φ := φ))
    haveI : Csub.Normal := by
      rw [← hker]
      infer_instance
    have hCsub_ne_top : Csub ≠ ⊤ := by
      intro hCsub_top
      have hW_le_C : W ≤ C := by
        intro w hw
        have hwsub : (⟨w, hw⟩ : W) ∈ Csub := by simp [hCsub_top]
        exact hwsub
      have hC_eq_W : C = W := le_antisymm hC_le_W hW_le_C
      have hW_eq_Z : W = Z := by rw [← hC_eq_W, hC_eq_Z]
      have hWcyc : IsCyclic W := by
        rw [hW_eq_Z]
        exact isCyclic_of_prime_card hZcard_eq_p
      exact hW_noncyclic hWcyc
    have hQ_nontrivial : Nontrivial (W ⧸ Csub) := by
      exact (QuotientGroup.nontrivial_iff (G := W) (N := Csub)).2 hCsub_ne_top
    have hQcard_eq_p : Nat.card (W ⧸ Csub) = p := by
      have hQp' : IsPGroup p (W ⧸ Csub) := hWp.to_quotient Csub
      rcases hQp'.exists_card_eq with ⟨k, hk⟩
      have hk_ne_zero : k ≠ 0 := by
        intro hk0
        have hcard_one : Nat.card (W ⧸ Csub) = 1 := by simpa [hk0] using hk
        haveI : Nontrivial (W ⧸ Csub) := hQ_nontrivial
        have hcard_ne_one : Nat.card (W ⧸ Csub) ≠ 1 := Nat.ne_of_gt Finite.one_lt_card
        exact hcard_ne_one hcard_one
      have hk_le_one : k ≤ 1 := by
        rw [hk] at hQle
        have hpow : p ^ k ≤ p ^ 1 := by simpa using hQle
        exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hpow
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne_zero
      have hk_one : k = 1 := by omega
      simpa [hk_one] using hk
    have hCsub_card : Nat.card Csub = Nat.card C := by
      exact natCard_subgroupOf_eq C W hC_le_W
    have hCsub_card_eq_p : Nat.card Csub = p := by
      rw [hCsub_card, hC_eq_Z, hZcard_eq_p]
    calc
      Nat.card W = Nat.card (W ⧸ Csub) * Nat.card Csub := by
        simpa using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := Csub))
      _ = p * p := by rw [hQcard_eq_p, hCsub_card_eq_p]
      _ = p ^ 2 := by rw [pow_two]
  have hWcomm : ∀ a b : W, a * b = b * a := by
    have hWp : IsPGroup p W := hpR.to_subgroup W
    letI : CommGroup W := IsPGroup.commGroupOfCardEqPrimeSq (p := p) (G := W) hWcard
    intro a b
    exact mul_comm a b
  have hWelem : IsElementaryAbelian p W := by
    refine
      { toIsMulCommutative := { is_comm := ⟨hWcomm⟩ }
        exponent_dvd_p := hWexp_dvd }
  exact ⟨hZcard_eq_p, hWcard, hWelem⟩

end
