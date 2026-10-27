module

public import CFSG.RankThree.PartOne.SEITZ2.SzOuter
public import CFSG.RankThree.PartOne.SEITZ9.SzTorus
public import CFSG.RankThree.PartOne.SEITZ10.SzCase2
public import CFSG.RankThree.PartOne.SEITZ9.SzModule

public section

namespace CFSG.RankThree.PartOne.SEITZ10

open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne.SEITZ2 CFSG.RankThree.PartOne.SEITZ9
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open CFSG.RankThree.PartOne.KE (fixField)
open CFSG.RankThree.PartOne.CTP (fixedSubgroup)

theorem subfieldPairSz_holds :
    SubfieldPairSz := by
  intro a ha K _ _ hK σ p hp hp5 hσ hne g hg
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfinG : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨b, m, hab, hbp, hk⟩ := card_fixField_suzuki hp hp5 hK hσ
  obtain ⟨e⟩ := KE.fixed_szFieldAut_equiv hK hk hab
  rw [← fixedSubgroup_eq_eqLocus] at e
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  ·
    right
    subst hb0
    have hk2 : Nat.card (fixField σ) = 2 := by simpa using hk
    have h20 : Nat.card (fixedSubgroup (szFieldAut a K σ)) = 20 := by
      rw [Nat.card_congr e.toEquiv]
      exact (suzuki_two_normal_five_complement_core_trivial hk2).1
    intro hdvd
    rw [h20] at hdvd
    have hle : p ≤ 20 := Nat.le_of_dvd (by norm_num) hdvd
    have hp5' : p = 5 := by
      interval_cases p <;> omega
    subst hp5'
    have ha2 : a = 2 := by omega
    exact hne ha2 rfl
  · left
    set R := fixedSubgroup (szFieldAut a K σ) with hR
    set k : Subfield K := fixField σ with hkdef
    set Rg : Subgroup (suzukiGroup a K) := R.map (MulAut.conj g).toMonoidHom with hRg
    set H : Subgroup (suzukiGroup a K) := Subgroup.closure ((R : Set (suzukiGroup a K)) ∪
      (Rg : Set (suzukiGroup a K))) with hH
    have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
    have hRgH : Rg ≤ H := fun x hx => Subgroup.subset_closure (Or.inr hx)
    have hσk : ∀ c ∈ k, σ c = c := fun c hc => hc
    have hUk : ∀ u ∈ k, ∀ v ∈ k, suzukiSElt a K u v ∈ H := fun u hu v hv =>
      hRH (suzukiSElt_mem_fixed σ (hσk u hu) (hσk v hv))
    have hTk : ∀ l : Kˣ, (l : K) ∈ k → suzukiDElt a K l ∈ H := fun l hl =>
      hRH (suzukiDElt_mem_fixed σ (hσk _ hl))
    have hW : suzukiWElt a K ∈ H := hRH (suzukiWElt_mem_fixed σ)
    have hKk : Nat.card K = Nat.card k ^ p := by
      rw [hK, hk, ← pow_mul]
      congr 1
      omega
    by_cases hcase : ∀ g' : suzukiB a K, (g' : suzukiGroup a K) ∈ H →
        ((torusPart hK g' : Kˣ) : K) ∈ k
    · exfalso
      obtain ⟨N, hNn, hNo, hNcard⟩ := bender_case2 hK hk hb1 hUk hW hcase
      have hsimple : IsSimpleGroup (suzukiGroup b k) := (suzuki_simple hb1 hk).2.2
      have hRsimple : IsSimpleGroup ↥R := e.isSimpleGroup
      have hcardR : Nat.card R = Nat.card k ^ 2 * (Nat.card k ^ 2 + 1) * (Nat.card k - 1) := by
        rw [Nat.card_congr e.toEquiv, suzuki_order hk, hk]
        exact mul_right_comm _ _ _
      have hR2 : 2 ∣ Nat.card R := by
        have hmem : suzukiSElt a K 0 1 ∈ R :=
          suzukiSElt_mem_fixed σ (σ.map_zero) (σ.map_one)
        have hdvd := Subgroup.orderOf_dvd_natCard R hmem
        rw [CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK one_ne_zero] at hdvd
        exact hdvd
      set R' : Subgroup ↥H := R.subgroupOf H with hR'
      have eR : ↥R' ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRH
      have : IsSimpleGroup ↥R' := eR.isSimpleGroup
      have hR'card : Nat.card R' = Nat.card R := Nat.card_congr eR.toEquiv
      have hR'N : R' ≤ N :=
        le_of_isSimpleGroup_of_odd_index N hNo R'
          (even_iff_two_dvd.2 (hR'card ▸ hR2))
      have hNR' : R' = N := Subgroup.eq_of_le_of_card_ge hR'N (by rw [hNcard, hR'card, hcardR])
      have eRg : ↥Rg ≃* ↥R := (R.equivMapOfInjective _ (MulAut.conj g).injective).symm
      set Rg' : Subgroup ↥H := Rg.subgroupOf H with hRg'
      have eRg' : ↥Rg' ≃* ↥R := (Subgroup.subgroupOfEquivOfLe hRgH).trans eRg
      have : IsSimpleGroup ↥Rg' := eRg'.isSimpleGroup
      have hRg'card : Nat.card Rg' = Nat.card R := Nat.card_congr eRg'.toEquiv
      have hRg'N : Rg' ≤ N :=
        le_of_isSimpleGroup_of_odd_index N hNo Rg'
          (even_iff_two_dvd.2 (hRg'card ▸ hR2))
      have hRgR : Rg ≤ R := by
        intro x hx
        have h1 : (⟨x, hRgH hx⟩ : ↥H) ∈ Rg' := hx
        have h2 : (⟨x, hRgH hx⟩ : ↥H) ∈ R' := hNR' ▸ hRg'N h1
        exact h2
      have hRgcard : Nat.card Rg = Nat.card R := Nat.card_congr eRg.toEquiv
      exact hg (Subgroup.eq_of_le_of_card_ge hRgR hRgcard.ge)
    · obtain ⟨g', hg'H, hg'k⟩ : ∃ g' : suzukiB a K, (g' : suzukiGroup a K) ∈ H ∧
          ((torusPart hK g' : Kˣ) : K) ∉ k := by
        by_contra hcon
        exact hcase fun g' hg' => by_contra fun hk' => hcon ⟨g', hg', hk'⟩
      obtain ⟨u, v, hgg⟩ := torusPart_spec hK g'
      exact suzuki_eq_top_of_irrational_torus hK hp hKk H hUk hTk hW hg'k (hgg ▸ hg'H)

end CFSG.RankThree.PartOne.SEITZ10
