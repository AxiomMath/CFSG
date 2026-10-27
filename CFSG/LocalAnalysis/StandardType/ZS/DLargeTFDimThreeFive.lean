module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Main
import CFSG.LocalAnalysis.StandardType.ZS.H3Recognition
import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTableDegThree
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsMonomial
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsOrthGeom
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
import CFSG.GroupTheory.SteinbergBKNormalPSubgroupTrivial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

private theorem eq_one_of_dvd_ten_of_modEq {p n : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hn : n ∣ 10) (hmod : n ≡ 1 [MOD p]) : n = 1 := by
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hn (by norm_num)
  have hdvd : p ∣ n - 1 := hmod.symm.dvd'
  by_cases hn1 : n = 1
  · exact hn1
  · exfalso
    have hn2 : 2 ≤ n := by omega
    have hnle : n ≤ 10 := Nat.le_of_dvd (by norm_num) hn
    have hp_le : p ≤ 9 := by
      have h1 : p ≤ n - 1 := Nat.le_of_dvd (by omega) hdvd
      omega
    have hp_eq : p = 7 := by
      have h1 : p ≠ 8 := by rintro rfl; norm_num at hp
      have h2 : p ≠ 9 := by rintro rfl; norm_num at hp
      omega
    have hn8 : n = 8 := by
      have h : 7 ∣ n - 1 := by rwa [hp_eq] at hdvd
      obtain ⟨k, hk⟩ := h
      have hk1 : k = 1 := by omega
      omega
    rw [hn8] at hn
    norm_num at hn

private theorem card_sylow_eq_one_of_card_eq {J : Type*} [Group J] [Finite J] {p : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (hcardJ : Nat.card J = 10 * p) : Nat.card (Sylow p J) = 1 := by
  let P : Sylow p J := default
  have : Finite (Sylow p J) :=
    Finite.of_injective (fun Q : Sylow p J => (Q : Subgroup J)) (fun _ _ h => Sylow.ext h)
  have hn_dvd : Nat.card (Sylow p J) ∣ 10 * p := by
    have h1 : Nat.card (Sylow p J) ∣ P.index := Sylow.card_dvd_index P
    have h2 : P.index ∣ Nat.card J := Subgroup.index_dvd_card (P : Subgroup J)
    rw [hcardJ] at h2
    exact h1.trans h2
  have hp_not_dvd : ¬ p ∣ Nat.card (Sylow p J) := not_dvd_card_sylow (p := p) (G := J)
  have hcop : Nat.Coprime (Nat.card (Sylow p J)) p :=
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hp_not_dvd).symm
  have h10 : Nat.card (Sylow p J) ∣ 10 := (hcop.dvd_mul_right).mp hn_dvd
  exact eq_one_of_dvd_ten_of_modEq Fact.out hp7 h10
    (card_sylow_modEq_one (p := p) (G := J))

private theorem card_eq_ten_mul_of_dvd {n p : ℕ} (hpprime : p.Prime) (hp7 : 7 ≤ p)
    (hnpos : 0 < n) (hn : n ≤ 120) (h2 : 2 ∣ n) (h5 : 5 ∣ n) (hp : p ∣ n) : n = 10 * p := by
  have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hpprime).mpr (by omega)
  have h5p : Nat.Coprime 5 p := (Nat.coprime_primes Nat.prime_five hpprime).mpr (by omega)
  have h10 : 10 ∣ n := by
    have hcop25 : Nat.Coprime 2 5 :=
      (Nat.coprime_primes Nat.prime_two Nat.prime_five).mpr (by norm_num)
    have h25 : 2 * 5 ∣ n := hcop25.mul_dvd_of_dvd_of_dvd h2 h5
    rwa [show 2 * 5 = 10 by norm_num] at h25
  have h10p : 10 * p ∣ n := by
    have hcop : Nat.Coprime 10 p := (Nat.coprime_mul_iff_left).mpr ⟨h2p, h5p⟩
    exact hcop.mul_dvd_of_dvd_of_dvd h10 hp
  obtain ⟨k, hk⟩ := h10p
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk
      exact absurd hk (ne_of_gt hnpos)
    · exact h0
  have hk1 : k = 1 := by
    have hle : (10 * p) * k ≤ 120 := by rw [← hk]; exact hn
    have hp70 : 70 ≤ 10 * p := by omega
    have h70k : 70 * k ≤ 120 := (Nat.mul_le_mul_right k hp70).trans hle
    omega
  rw [hk1, mul_one] at hk
  exact hk

private theorem false_of_normal_p_subgroup {J : Type*} [Group J] [Finite J] {p : ℕ}
    [Fact p.Prime] (hp7 : 7 ≤ p) (hcardJ : Nat.card J = 10 * p)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V] [Nontrivial V]
    (ρ : J →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hirr : ∀ W : Submodule (ZMod p) V,
      (∀ g : J, ∀ w ∈ W, (ρ g : V →ₗ[ZMod p] V) w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hinj : ∀ x : J, ρ x = 1 → x = 1) (hpdiv : p ∣ Nat.card J) : False := by
  have hSylow := card_sylow_eq_one_of_card_eq hp7 hcardJ
  have : Subsingleton (Sylow p J) :=
    (Finite.card_le_one_iff_subsingleton).mp (by omega)
  let P : Sylow p J := default
  have : P.Normal := Sylow.normal_of_subsingleton P
  have hPne : (P : Subgroup J) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hpdiv
  have hex : ∃ z ∈ (P : Subgroup J), z ≠ 1 := by
    by_contra h
    push Not at h
    exact hPne ((Subgroup.eq_bot_iff_forall (P : Subgroup J)).mpr h)
  obtain ⟨z, hzP, hzne⟩ := hex
  exact hzne (hinj z (CFSG.GroupTheory.SteinbergBK.normal_p_subgroup_irreducible_trivial
    (p := p) (G := J) (P := (P : Subgroup J)) P.isPGroup' ρ hirr z hzP))

private theorem dvd_card_of_isOrthType [Module.Finite (ZMod p) V] (hp7 : 7 ≤ p)
    (h3 : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hJ : IsOrthType p J) (hd : DMax p J 5) :
    2 ∣ Nat.card J ∧ 5 ∣ Nat.card J ∧ p ∣ Nat.card J := by
  obtain ⟨g, hgJ, hgord⟩ :=
    TableFacts.exists_orderOf_eq_of_isOrthType (p := p) (by omega : 5 ≤ p)
      (by omega : 3 ≤ Module.finrank (ZMod p) V) hJ
  obtain ⟨x, hxJ, y, hyJ, hxr, hyr, hxy5⟩ := hd.2
  have hx2 : orderOf x = 2 := by
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxr.1)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (IsRefl.ne_one hxr)
    · exact h
  refine ⟨?_, ?_, ?_⟩
  · have := J.orderOf_dvd_natCard hxJ
    rwa [hx2] at this
  · have := J.orderOf_dvd_natCard (J.mul_mem hxJ hyJ)
    rwa [hxy5] at this
  · have := J.orderOf_dvd_natCard hgJ
    rwa [hgord] at this

theorem false_of_isOrthType_of_dMax_five_of_card_le [Module.Finite (ZMod p) V]
    (hp7 : 7 ≤ p) (h3 : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hA : AbsIrred p J) (hJ : IsOrthType p J) (hd : DMax p J 5)
    (hcard : Nat.card J ≤ 120) : False := by
  have hpprime : Nat.Prime p := Fact.out
  have : Finite V := Module.finite_of_finite (ZMod p)
  let : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V)) LinearEquiv.coe_injective
  let : Finite J := Subtype.finite
  obtain ⟨h2, h5, hpdiv⟩ := dvd_card_of_isOrthType (p := p) hp7 h3 hJ hd
  have hcard_eq : Nat.card J = 10 * p :=
    card_eq_ten_mul_of_dvd hpprime hp7 (Finite.card_pos (α := J)) hcard h2 h5 hpdiv
  let ρ : J →* LinearMap.GeneralLinearGroup (ZMod p) V :=
    { toFun := fun g => LinearMap.GeneralLinearGroup.ofLinearEquiv (g : V ≃ₗ[ZMod p] V)
      map_one' := Units.ext rfl
      map_mul' := by
        intro a b
        simp [LinearMap.GeneralLinearGroup.ofLinearEquiv_mul] }
  have hinj : ∀ x : J, ρ x = 1 → x = 1 := by
    intro z hz
    have hzlin : (ρ z : V →ₗ[ZMod p] V) = 1 := by
      have := congrArg (fun y : LinearMap.GeneralLinearGroup (ZMod p) V =>
        (y : V →ₗ[ZMod p] V)) hz
      simpa using this
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have := congrFun (congrArg DFunLike.coe hzlin) v
    simpa [ρ, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv] using this
  have hirr : ∀ W : Submodule (ZMod p) V,
      (∀ g : J, ∀ w ∈ W, (ρ g : V →ₗ[ZMod p] V) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    exact hA.1 W (fun a ha w hw => by
      have := hW ⟨a, ha⟩ w hw
      simpa [ρ, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv] using this)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [h3]; norm_num)
  exact false_of_normal_p_subgroup hp7 hcard_eq ρ hirr hinj hpdiv

theorem false_of_isImprimitiveOnV_of_dMax_five_of_card_le [Module.Finite (ZMod p) V]
    (hp : p ≠ 2) (h3 : Module.finrank (ZMod p) V = 3) {J : Subgroup (V ≃ₗ[ZMod p] V)}
    (hR : ReflGen p J) (hA : AbsIrred p J) (himp : Quasithin.SimsG4.IsImprimitiveOnV J)
    (hd : DMax p J 5) (hcard : Nat.card J ≤ 120) : False := by
  obtain ⟨f, i₀, i₁, ζ, hi, hJ⟩ :=
    exists_basis_eq_gmmn_or_g2mmn hp h3 (le_refl 3) hR hA himp
  obtain ⟨x, hxJ, y, hyJ, hxr, hyr, hxy5⟩ := hd.2
  rcases hJ with hJ | hJ
  · rw [hJ] at hxJ hyJ hcard
    have h5dvd : 5 ∣ orderOf ζ := by
      rcases TableFacts.orderOf_mul_le_three_or_dvd_of_mem_gmmn hp f hi ζ hxJ hyJ hxr hyr with
        hle | hdvd
      · rw [hxy5] at hle
        omega
      · rwa [hxy5] at hdvd
    have h5le : 5 ≤ orderOf ζ := Nat.le_of_dvd (orderOf_pos ζ) h5dvd
    rw [card_gmmn (p := p) (n := 3) (by norm_num) f hi ζ] at hcard
    norm_num at hcard
    have h25 : 25 ≤ orderOf ζ ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ orderOf ζ ^ 2 := Nat.pow_le_pow_left h5le 2
    nlinarith
  · rw [hJ] at hxJ hyJ hcard
    have h5lcm : 5 ∣ Nat.lcm 2 (orderOf ζ) := by
      rcases TableFacts.orderOf_mul_le_four_or_dvd_of_mem_g2mmn hp f hi ζ hxJ hyJ hxr hyr with
        hle | hdvd
      · rw [hxy5] at hle
        omega
      · rwa [hxy5] at hdvd
    have h5dvd : 5 ∣ orderOf ζ := by
      have h2m : Nat.lcm 2 (orderOf ζ) ∣ 2 * orderOf ζ := Nat.lcm_dvd_mul 2 (orderOf ζ)
      have h5' : 5 ∣ 2 * orderOf ζ := h5lcm.trans h2m
      rcases (Nat.prime_five.dvd_mul).mp h5' with h | h
      · norm_num at h
      · exact h
    have h10dvd : 10 ∣ Nat.lcm 2 (orderOf ζ) :=
      (Nat.coprime_primes Nat.prime_two Nat.prime_five).mpr (by norm_num) |>.mul_dvd_of_dvd_of_dvd
        (Nat.dvd_lcm_left 2 (orderOf ζ)) h5lcm
    have h10le : 10 ≤ Nat.lcm 2 (orderOf ζ) :=
      Nat.le_of_dvd (Nat.lcm_pos (by norm_num) (orderOf_pos ζ)) h10dvd
    rw [card_g2mmn (p := p) hp (n := 3) (by norm_num) f hi ζ] at hcard
    norm_num at hcard
    have h100 : 100 ≤ Nat.lcm 2 (orderOf ζ) ^ 2 := by
      calc 100 = 10 ^ 2 := by norm_num
        _ ≤ Nat.lcm 2 (orderOf ζ) ^ 2 := Nat.pow_le_pow_left h10le 2
    nlinarith

private theorem seven_le_of_prime_of_five_lt {p : ℕ} (hpprime : p.Prime) (hp5 : 5 < p) : 7 ≤ p := by
  by_contra h
  have hp6 : p ≤ 6 := by omega
  interval_cases p; norm_num at hpprime

private theorem false_of_J34 {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {F : Subgroup (W ≃ₗ[ZMod p] W)} (hdY : DMax p (movedGroup F) 5)
    (h : DimThree.ExcData p .J34 (movedGroup F)) : False := by
  have hd4 : DMax p (movedGroup F) 4 := by
    have := h.2.2.2.2.1
    simpa [ExcRow.dmax] using this
  obtain ⟨x, hx, y, hy, hxr, hyr, hxy5⟩ := hdY.2
  have := hd4.1 x hx y hy hxr hyr
  omega

private theorem false_of_J35 {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    {F : Subgroup (W ≃ₗ[ZMod p] W)} (hcardY : Nat.card (movedGroup F) ≤ 120)
    (h : DimThree.ExcData p .J35 (movedGroup F)) : False := by
  have h2160 : Nat.card (movedGroup F) = 2160 := by
    have := h.2.2.1
    simpa [ExcRow.ord] using this
  omega

private theorem h3_model {W : Type} [AddCommGroup W] [Module (ZMod p) W]
    [Module.Finite (ZMod p) W] {F : Subgroup (W ≃ₗ[ZMod p] W)} (hp5 : 5 < p)
    (hW : Module.finrank (ZMod p) W = 4) (hSplit : SplitSupport F 3)
    (hframe : H3Frame p (movedGroup F)) (hcard : Nat.card (movedGroup F) = 120) :
    ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W), α ^ 2 = α + 1 ∧
      F = basisClosure f (h3Mats α) := by
  have hcardF : Nat.card F = 120 := by
    rw [← card_movedGroup_of_splitSupport hSplit]
    exact hcard
  have hFrameF : H3Frame p F := H3Frame.of_movedGroup hSplit hframe
  exact exists_basis_eq_h3Mats_of_h3Frame (by omega : p ≠ 2) (by omega : p ≠ 5) hW hSplit
    hcardF hFrameF

theorem tfDimThreeFive_holds :
    TFDimThreeFive p := by
  intro W _ _ _ F hp5 hW hR hTF hSplit hd hcard
  have hp7 : 7 ≤ p := seven_le_of_prime_of_five_lt (Fact.out : Nat.Prime p) hp5
  let V := HardMathSupport.Kantor79.commutatorSpace F
  let Y := movedGroup F
  let : Module.Finite (ZMod p) V := Module.Finite.of_injective V.subtype V.subtype_injective
  have h3V : Module.finrank (ZMod p) V = 3 := hSplit.2.1
  have hRY : ReflGen p Y := reflGen_movedGroup hR
  have hIY : AbsIrred p Y := absIrred_of_reflGen hRY (irred_movedGroup_of_splitSupport hSplit)
  have htfY : QTwoLin.TransvectionFree Y := transvectionFree_movedGroup hSplit hTF
  have hdY : DMax p Y 5 := (dmax_movedGroup_iff hSplit 5).mpr hd
  have hcardY : Nat.card Y ≤ 120 := by
    change Nat.card (movedGroup F) ≤ 120
    rw [card_movedGroup_of_splitSupport hSplit]
    exact hcard
  by_cases hprim : Quasithin.SimsG4.IsImprimitiveOnV Y
  · exact (false_of_isImprimitiveOnV_of_dMax_five_of_card_le (p := p) (by omega) h3V hRY
      hIY hprim hdY hcardY).elim
  · rcases DimThree.rows_of_finrank_eq_three (p := p) (by omega) h3V hRY hIY hprim with
      hSL | hOrth | hH3 | hJ34 | hJ35
    · exact (not_transvectionFree_of_mem_iff_det (by rw [h3V]; norm_num) hSL htfY).elim
    · exact (false_of_isOrthType_of_dMax_five_of_card_le hp7 h3V hIY hOrth hdY hcardY).elim
    · exact h3_model hp5 hW hSplit hH3.2.2.2 (by
        simpa [Y, ExcRow.ord] using hH3.1.2.2.1)
    · exact (false_of_J34 hdY hJ34.1).elim
    · exact (false_of_J35 hcardY hJ35.1).elim

end CFSG.StandardType.ZS

end
