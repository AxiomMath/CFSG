module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKFacts
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.KFacts.K72FixL2
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourSelfCentralizer
public import CFSG.GroupTheory.DihedralSubgroups
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.GorensteinWalter

theorem outer_case_false {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    (e : X ≃* PSL2 K) {q₀ : ℕ} (hq₀ : 4 ≤ q₀) (hK : Nat.card K = q₀ ^ 3) {β : MulAut X}
    (hβ3 : β ^ 3 = 1) (hout : ¬ IsInnerAut β) (hN : InnThetaNoncyclic β) : False := by
  obtain ⟨hcen, hqs, -, -⟩ := fixedPoints_facts_of_mulEquiv_psl2 e hq₀ hK hβ3 hout
  obtain ⟨W, V, hWs, -, hWle, hWcomm, hWnorm, hVW, -, hVnc⟩ := hN
  set C : Subgroup X := β.toMonoidHom.eqLocus (MonoidHom.id X) with hC
  have hCfix : ∀ c : X, c ∈ C ↔ β c = c := fun c => Iff.rfl
  have hcenX : Subgroup.center X = ⊥ := center_eq_bot_of_mulEquiv e (psl2_center_eq_bot K)
  have hconj_inj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut X => φ g) hx
      simp only [map_one, MulAut.conj_apply, MulAut.one_apply] at h
      have h' : x * g * x⁻¹ = g := h
      rw [mul_inv_eq_iff_eq_mul] at h'
      exact h'.symm
    rw [hcenX, Subgroup.mem_bot] at hxc
    exact hxc
  set R : Subgroup X := W.comap (MulAut.conj : X →* MulAut X) with hR
  have hRC : ∀ r ∈ R, r ∈ C := by
    intro r hr
    have hr' : MulAut.conj r ∈ W := hr
    have h1 : MulAut.conj (β r) = MulAut.conj r := by
      calc MulAut.conj (β r) = β * MulAut.conj r * β⁻¹ := (mul_mulAutConj_mul_inv β r).symm
        _ = MulAut.conj r * β * β⁻¹ := by rw [hWcomm _ hr']
        _ = MulAut.conj r := by rw [mul_inv_cancel_right]
    exact (hCfix r).mpr (hconj_inj h1)
  have hRnorm : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    intro c hc r hr
    have hc' : β c = c := (hCfix c).mp hc
    have hr' : MulAut.conj r ∈ W := hr
    have h := hWnorm c hc' _ hr'
    show MulAut.conj (c * r * c⁻¹) ∈ W
    simpa only [map_mul, map_inv] using h
  have hNnorm : (R.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hRnorm (g : X) g.2 _ hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hnt : Nontrivial C := by
    obtain ⟨a, b, hab⟩ := hqs.2.2
    haveI : Nontrivial (C ⧸ Subgroup.center C) :=
      nontrivial_of_ne a b (fun h => hab (by rw [h]))
    exact (QuotientGroup.mk'_surjective (Subgroup.center C)).nontrivial
  haveI : Group.IsPerfect C := hqs.1
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hNnorm with htop | hle
  ·
    have hmem : ∀ c : C, MulAut.conj (c : X) ∈ W := by
      intro c
      have hc : c ∈ R.subgroupOf C := by rw [htop]; exact Subgroup.mem_top c
      exact (Subgroup.mem_subgroupOf.mp hc)
    let φ : C →* W :=
      ((MulAut.conj : X →* MulAut X).comp C.subtype).codRestrict W (fun c => hmem c)
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply hconj_inj
      exact congrArg Subtype.val hab
    haveI := hWs
    have hsolv : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective (f := φ) hφ
    exact Group.IsPerfect.not_isSolvable C hsolv
  ·
    have hV1 : ∀ v ∈ V, v = 1 := by
      intro v hv
      obtain ⟨r, hr⟩ := (MonoidHom.mem_range).mp (hWle (hVW hv))
      have hrR : r ∈ R := by
        have hr' : MulAut.conj r ∈ W := by rw [hr]; exact hVW hv
        exact hr'
      have hrC : r ∈ C := hRC r hrR
      have hz : (⟨r, hrC⟩ : C) ∈ Subgroup.center C := by
        apply hle
        exact (Subgroup.mem_subgroupOf).mpr hrR
      rw [hcen, Subgroup.mem_bot] at hz
      have hr1 : r = 1 := congrArg Subtype.val hz
      rw [← hr, hr1, map_one]
    apply hVnc
    haveI : Subsingleton V :=
      ⟨fun a b => Subtype.ext ((hV1 _ a.2).trans (hV1 _ b.2).symm)⟩
    exact isCyclic_of_subsingleton

theorem conj_injective_of_mulEquiv {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (e : X ≃* PSL2 K) : Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut X => φ g) hx
    simp only [map_one, MulAut.conj_apply, MulAut.one_apply] at h
    have h' : x * g * x⁻¹ = g := h
    rw [mul_inv_eq_iff_eq_mul] at h'
    exact h'.symm
  rw [center_eq_bot_of_mulEquiv e (psl2_center_eq_bot K), Subgroup.mem_bot] at hxc
  exact hxc

theorem psl2_noncyclic_two_not_centralize_three
    (K : Type) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (x : PSL2 K) (hx : orderOf x = 3)
    (V : Subgroup (PSL2 K)) (hV2 : IsPGroup 2 V) (hVnc : ¬ IsCyclic V)
    (hVc : ∀ v ∈ V, Commute x v) : False := by
  obtain ⟨P, hVP⟩ := IsPGroup.exists_le_sylow hV2
  obtain ⟨m, -, ⟨eP⟩⟩ := psl2_odd_hasDihedralSylowTwo_model K hK P
  let Q : Subgroup P := V.subgroupOf P
  let eQ : Q ≃* V := Subgroup.subgroupOfEquivOfLe hVP
  let QD : Subgroup (DihedralGroup (2 ^ m)) := Q.map eP.toMonoidHom
  let eQD : Q ≃* QD := Subgroup.equivMapOfInjective Q eP.toMonoidHom eP.injective
  have hQDnc : ¬ IsCyclic QD := fun hc => hVnc ((eQ.symm.trans eQD).isCyclic.mpr hc)
  obtain ⟨k, hk1, -, ⟨eD⟩⟩ := noncyclic_subgroup_dihedral_two_pow QD hQDnc
  obtain ⟨K4, hK4V, hK4⟩ :=
    exists_kleinFour_le_of_dihedral_subgroup_mulEquiv V hk1 (eQ.symm.trans (eQD.trans eD))
  have hKc : K4 ≤ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (PSL2 K)) :
      Set (PSL2 K)) := by
    intro k0 hk0
    rw [Subgroup.mem_centralizer_iff]
    rintro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (hVc k0 (hK4V hk0)) j).eq
  have hAne : Subgroup.zpowers x ≠ ⊥ := by
    intro h
    rw [Subgroup.zpowers_eq_bot] at h
    rw [h, orderOf_one] at hx
    norm_num at hx
  have hAodd : Odd (Nat.card (Subgroup.zpowers x)) := by
    rw [Nat.card_zpowers, hx]
    exact ⟨1, by norm_num⟩
  exact psl2_no_kleinFour_centralizes_odd_cyclic K hK (Subgroup.zpowers x) K4
    (Subgroup.isCyclic_zpowers x) hAne hAodd hK4 hKc

theorem inner_case_false
    {X : Type} [Group X] [Finite X] {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (e : X ≃* PSL2 K) {x : X} (hx : orderOf x = 3)
    {β : MulAut X} (hβ : β = MulAut.conj x) (hN : InnThetaNoncyclic β) : False := by
  obtain ⟨W, V, -, -, hWle, hWcomm, -, hVW, hV2, hVnc⟩ := hN
  have hconj_inj : Function.Injective (MulAut.conj : X →* MulAut X) :=
    conj_injective_of_mulEquiv e
  have hVrange : V ≤ (MulAut.conj : X →* MulAut X).range := le_trans hVW hWle
  have hmap : (V.comap (MulAut.conj : X →* MulAut X)).map (MulAut.conj : X →* MulAut X) = V :=
    Subgroup.map_comap_eq_self hVrange
  let eV : (V.comap (MulAut.conj : X →* MulAut X)) ≃* V :=
    (Subgroup.equivMapOfInjective _ (MulAut.conj : X →* MulAut X) hconj_inj).trans
      (MulEquiv.subgroupCongr hmap)
  let V₁ : Subgroup (PSL2 K) := (V.comap (MulAut.conj : X →* MulAut X)).map e.toMonoidHom
  let eV₁ : (V.comap (MulAut.conj : X →* MulAut X)) ≃* V₁ :=
    Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  let E : V ≃* V₁ := eV.symm.trans eV₁
  have hV₁2 : IsPGroup 2 V₁ := IsPGroup.of_injective hV2 E.symm.toMonoidHom E.symm.injective
  have hV₁nc : ¬ IsCyclic V₁ := fun h => hVnc (E.isCyclic.mpr h)
  have hcent : ∀ v ∈ V₁, Commute (e x) v := by
    intro v hv
    obtain ⟨v₀, hv₀, rfl⟩ := Subgroup.mem_map.mp hv
    have hv₀' : MulAut.conj v₀ ∈ V := hv₀
    have h1 := hWcomm _ (hVW hv₀')
    rw [hβ, ← map_mul, ← map_mul] at h1
    have hxv : x * v₀ = v₀ * x := hconj_inj h1
    exact (show Commute x v₀ from hxv).map e
  have hex : orderOf (e x) = 3 :=
    (orderOf_injective e.toMonoidHom e.injective x).trans hx
  exact psl2_noncyclic_two_not_centralize_three K hK (e x) hex V₁ hV₁2 hV₁nc hcent

theorem kLTwoCentralizer_holds :
    KLTwoCentralizer := by
  intro p f hpf hp2 hf X _ _ hne β hβ3 hN
  obtain ⟨eX⟩ := hne
  have hp : p.Prime := hpf.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hK : IsOddPrimePower (Nat.card (GaloisField p f)) := ⟨p, f, hp, hpodd, hf, hcard⟩
  let e : X ≃* PSL2 (GaloisField p f) := eX.trans (projSLEquivPSL (GaloisField p f))
  have hβ3' : β ^ 3 = 1 := by rw [← hβ3]; exact pow_orderOf_eq_one β
  by_cases hin : β ∈ (MulAut.conj : X →* MulAut X).range
  · exfalso
    obtain ⟨x, hxβ⟩ := hin
    have hx : orderOf x = 3 := by
      rw [← hxβ, orderOf_injective _ (conj_injective_of_mulEquiv e)] at hβ3
      exact hβ3
    exact inner_case_false hK e hx hxβ.symm hN
  · have hout : ¬ IsInnerAut β := hin
    have hout' : ¬ IsInnerAut (MulAut.congr e β) := fun h => hout ((isInnerAut_congr e β).mp h)
    have hα3 : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ3', map_one]
    have hfield := isField_of_pow_three_of_not_inner hα3 hout'
    obtain ⟨σ, hσ, -⟩ := exists_fixed_iff_of_isField hfield hα3
    haveI : Finite (GaloisField p f ≃+* GaloisField p f) :=
      Nat.finite_of_card_ne_zero (by rw [card_ringAut_eq hp hf hcard]; omega)
    have h3f : 3 ∣ f := by
      have h1 := orderOf_dvd_natCard σ
      rw [card_ringAut_eq hp hf hcard, hσ] at h1
      exact h1
    obtain ⟨k, hk⟩ := h3f
    have hKq : Nat.card (GaloisField p f) = (p ^ k) ^ 3 := by
      rw [hcard, hk, ← pow_mul, mul_comm]
    have hk1 : 1 ≤ k := by omega
    by_cases h4 : 4 ≤ p ^ k
    · exact (outer_case_false e h4 hKq hβ3' hout hN).elim
    · have hpk : p ≤ p ^ k := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk1
      have hp2' : 2 ≤ p := hp.two_le
      have hp3 : p = 3 := by omega
      subst hp3
      have hk3 : k = 1 := by
        by_contra hne1
        have h9 : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h9' : (9 : ℕ) ≤ 3 ^ k := h9
        omega
      exact ⟨rfl, by omega, hin⟩

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof

end
