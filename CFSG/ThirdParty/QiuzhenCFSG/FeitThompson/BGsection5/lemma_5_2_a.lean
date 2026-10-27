module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.lemma_5_1_b

namespace CFSG
end CFSG
open CFSG

/-! # Lemma 5.2(a) from BG Section 5 -/

section

public theorem CFSG.lemma_5_2_a
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {R : Type*} [Group R] [Finite R] (hpR : IsPGroup p R) (hR : 3 ≤ groupRank R)
    {E : Subgroup R} (hE : E ∈ elementaryAbelianSubgroupsOfRank p 2 R)
    (hEmax : E ∈ maximalElementaryAbelianSubgroups p R) :
    ¬ E ≤ CΩ₁Z₂ p R := by
  classical
  intro hET
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
  have hZ_le_center : Z ≤ Subgroup.center R := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
    exact y.property
  have hZcentE : Z ≤ Subgroup.centralizer (E : Set R) := by
    exact hZ_le_center.trans (Subgroup.center_le_centralizer (E : Set R))
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
  have hWexp_dvd : Monoid.exponent ↥W ∣ p := by
    simpa [W, Ω₁Z₂] using z2OmegaCandidate_exponent_dvd_p_of_odd (G := R) (p := p) hpodd
  have hWpow : ∀ w : W, (w : R) ^ p = 1 := by
    intro w
    exact congrArg Subtype.val <|
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hWexp_dvd w
  have hW_le_E : W ≤ E := by
    have hWcentE : W ≤ Subgroup.centralizer (E : Set R) := by
      exact (Subgroup.le_centralizer_iff).mp (by simpa [W, CΩ₁Z₂] using hET)
    intro w hw
    have hwcentE : Subgroup.zpowers (w : R) ≤ Subgroup.centralizer (E : Set R) := by
      exact (Subgroup.zpowers_le).2 (hWcentE hw)
    have hwzpowElem : IsElementaryAbelian p (Subgroup.zpowers (w : R)) :=
      isElementaryAbelian_zpowers_of_pow_eq_one (p := p) (x := (w : R)) (hWpow ⟨w, hw⟩)
    letI : IsElementaryAbelian p (Subgroup.zpowers (w : R)) := hwzpowElem
    have hsupElem : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers (w : R) : Subgroup R) := by
      exact isElementaryAbelian_sup_of_le_centralizer' (p := p) (E := E)
        (C := Subgroup.zpowers (w : R)) hwcentE
    have hsupEq : E ⊔ Subgroup.zpowers (w : R) = E :=
      (hEmax' (E ⊔ Subgroup.zpowers (w : R) : Subgroup R) le_sup_left hsupElem).symm
    have hw_in_sup : (w : R) ∈ E ⊔ Subgroup.zpowers (w : R) := by
      exact Subgroup.mem_sup_right <| Subgroup.mem_zpowers (w : R)
    have hw_in_E : (w : R) ∈ E := by
      simpa [hsupEq] using hw_in_sup
    exact hw_in_E
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
  have hWcard : Nat.card W = p ^ 2 := by
    have hWp : IsPGroup p W := hpR.to_subgroup W
    rcases hWp.exists_card_eq with ⟨k, hk⟩
    have hk_le_two : k ≤ 2 := by
      have hcard_le : Nat.card W ≤ Nat.card E := Subgroup.card_le_of_le hW_le_E
      rw [hk, hEcard] at hcard_le
      exact (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).mp hcard_le
    have hk_ne_zero : k ≠ 0 := by
      intro hk0
      have hcard_one : Nat.card W = 1 := by simpa [hk0] using hk
      haveI : Subsingleton W := (Nat.card_eq_one_iff_unique.mp hcard_one).1
      exact hW_noncyclic (inferInstance : IsCyclic W)
    have hk_ne_one : k ≠ 1 := by
      intro hk1
      have hcard_p : Nat.card W = p := by simpa [hk1] using hk
      exact hW_noncyclic (isCyclic_of_prime_card (α := W) hcard_p)
    have hk_two : k = 2 := by omega
    simpa [hk_two] using hk
  have hW_eq_E : W = E := by
    exact Subgroup.eq_of_le_of_card_ge hW_le_E (by rw [hEcard, hWcard])
  have hEnorm : E.Normal := by
    have hWchar : W.Characteristic := by
      simpa [W, Ω₁Z₂] using z2OmegaCandidate_characteristic (G := R) (p := p)
    have hEchar : E.Characteristic := by
      rw [← hW_eq_E]
      exact hWchar
    letI : E.Characteristic := hEchar
    infer_instance
  have hE_rank : E ∈ elementaryAbelianSubgroupsOfRank p 2 R := ⟨hEcard, hEelem⟩
  letI : E.Normal := hEnorm
  obtain ⟨B, _hBnorm, hBelem, hBcard, hEB⟩ :=
    exists_normal_elementaryAbelian_card_p3_containing_rank_two_normal
      (p := p) hpodd hpR hR hE_rank
  have hE_eq_B : E = B := hEmax' B hEB hBelem
  have hpow_eq : p ^ 2 = p ^ 3 := by
    calc
      p ^ 2 = Nat.card E := hEcard.symm
      _ = Nat.card B := by rw [hE_eq_B]
      _ = p ^ 3 := hBcard
  exact (ne_of_lt ((Nat.pow_lt_pow_iff_right (Nat.Prime.one_lt (Fact.out : Nat.Prime p))).2
    (by decide : 2 < 3))) hpow_eq

end
