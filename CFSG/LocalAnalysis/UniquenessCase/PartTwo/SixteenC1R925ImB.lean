module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Fit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem r925_mem_of_map_mem {Γ : Type} [Group Γ] [Finite Γ] {Z : Subgroup Γ} [Z.Normal]
    (hJ : ∀ x ∈ CFSG.pPrimeCore 3 Γ, ¬ 3 ∣ orderOf x) {y : Γ} {k : ℕ} (hy : y ^ 3 ^ k = 1)
    (hyZ : toModO3p Γ y ∈ Z.map (toModO3p Γ)) : y ∈ Z := by
  obtain ⟨z, hzZ, hzy⟩ := Subgroup.mem_map.mp hyZ
  let j : Γ := z⁻¹ * y
  have hjJ : j ∈ CFSG.pPrimeCore 3 Γ := by
    have h1 : toModO3p Γ j = 1 := by
      dsimp only [j]
      rw [map_mul, map_inv, hzy, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 Γ) j).mp h1
  have hjcop : Nat.Coprime (orderOf j) 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr (hJ j hjJ)
  let c : Γ ⧸ Z := QuotientGroup.mk' Z y
  have hcj : c = QuotientGroup.mk' Z j := by
    have hy_eq : y = z * j := by dsimp only [j]; group
    dsimp only [c]
    rw [hy_eq, map_mul]
    have hz1 : QuotientGroup.mk' Z z = 1 := (QuotientGroup.eq_one_iff (N := Z) z).mpr hzZ
    rw [hz1, one_mul]
  have hc_dvd_j : orderOf c ∣ orderOf j := by
    rw [hcj]
    exact orderOf_map_dvd (QuotientGroup.mk' Z) j
  have hc_cop3 : Nat.Coprime (orderOf c) 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr fun h3 => hJ j hjJ (h3.trans hc_dvd_j)
  have hc_dvd_pow : orderOf c ∣ 3 ^ k :=
    (orderOf_map_dvd (QuotientGroup.mk' Z) y).trans (orderOf_dvd_of_pow_eq_one hy)
  have hc1 : orderOf c = 1 :=
    Nat.Coprime.eq_one_of_dvd (hc_cop3.pow_right k) hc_dvd_pow
  exact (QuotientGroup.eq_one_iff (N := Z) y).mp (show QuotientGroup.mk' Z y = 1 from
    orderOf_eq_one_iff.mp hc1)

theorem r925_centralizes_of_centralizes_fstar {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ}
    [J.Normal] (hJ : ∀ x ∈ J, ¬ 3 ∣ orderOf x) {D : Subgroup Γ} (hD : Nat.card D = 3)
    (hDF : D ≤ centralizer (Fstar J : Set Γ)) : D ≤ centralizer (J : Set Γ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hNchar : (genFittingFStar ↥J).Characteristic :=
    CFSG.ComponentClassification.GeneralizedFitting.characteristic ↥J
  have hnormalizes : J ≤ Subgroup.normalizer (Fstar J : Set Γ) := by
    have h := Subgroup.le_normalizer_map (H := genFittingFStar ↥J) J.subtype
    have htop : Subgroup.normalizer (genFittingFStar ↥J : Set ↥J) = ⊤ :=
      Subgroup.normalizer_eq_top (genFittingFStar ↥J)
    have hmap : (⊤ : Subgroup ↥J).map J.subtype = J := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [htop, hmap] at h
    exact h
  have hFJle : ⁅Fstar J, J⁆ ≤ Fstar J := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hnormalizes
  have hDFbot : ⁅D, Fstar J⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDF
  have hFDbot : ⁅Fstar J, D⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hDFbot
  have h1 : ⁅⁅D, Fstar J⁆, J⁆ = ⊥ := by
    rw [hDFbot, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅Fstar J, J⁆, D⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅⁅Fstar J, J⁆, D⁆ ≤ ⁅Fstar J, D⁆ := Subgroup.commutator_mono hFJle le_rfl
      _ = ⊥ := hFDbot
  have h3 : ⁅⁅J, D⁆, Fstar J⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hJDcent : ⁅J, D⁆ ≤ centralizer (Fstar J : Set Γ) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  have hJDfit : ⁅J, D⁆ ≤ r925FittingIn J :=
    (le_inf hJDcent (Subgroup.commutator_le_left J D)).trans
      (r925_centralizer_fstar_le_fitting J)
  have hfit_le : r925FittingIn J ≤ Fstar J := by
    rw [r925_fstar_eq_sup]; exact le_sup_left
  have hFitD : ⁅r925FittingIn J, D⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅r925FittingIn J, D⁆ ≤ ⁅Fstar J, D⁆ := Subgroup.commutator_mono hfit_le le_rfl
      _ = ⊥ := hFDbot
  have hdouble : ⁅⁅J, D⁆, D⁆ = ⊥ := by
    rw [eq_bot_iff]
    calc ⁅⁅J, D⁆, D⁆ ≤ ⁅r925FittingIn J, D⁆ := Subgroup.commutator_mono hJDfit le_rfl
      _ = ⊥ := hFitD
  have hJ3 : ¬ 3 ∣ Nat.card J := by
    intro h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
    exact hJ (x : Γ) x.2 (by rw [Subgroup.orderOf_coe, hx])
  have hcop : Nat.Coprime (Nat.card D) (Nat.card J) := by
    rw [hD]
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr hJ3
  have hnormJ : D ≤ Subgroup.normalizer (J : Set Γ) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcomm : ⁅J, D⁆ = ⊥ :=
    CFSG.GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot J D
      hnormJ hcop hdouble
  rw [Subgroup.commutator_comm] at hcomm
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

theorem r925_im_centralizer_le {Γ : Type} [Group Γ] [Finite Γ] {Y K M : Subgroup Γ}
    (h : R925Ctx Γ Y K M) (hnot : ¬ CFSG.pPrimeCore 3 Γ ≤ M) :
    centralizer (Fstar (CFSG.pPrimeCore 3 Γ) : Set Γ) ≤ CFSG.pPrimeCore 3 Γ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J : Subgroup Γ := CFSG.pPrimeCore 3 Γ with hJdef
  set Z₀ : Subgroup Γ := centralizer (Fstar J : Set Γ) with hZdef
  haveI hJchar : J.Characteristic := CFSG.pPrimeCore_characteristic
  haveI hNchar : (genFittingFStar ↥J).Characteristic :=
    CFSG.ComponentClassification.GeneralizedFitting.characteristic ↥J
  haveI hFchar : (Fstar J).Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic (H := J)
      (K := genFittingFStar ↥J)
  haveI hZ₀c : Z₀.Characteristic := by
    rw [hZdef]
    exact Subgroup.characteristic_centralizer
  haveI hZ₀n : Z₀.Normal := inferInstance
  have hJnot : ¬ J ≤ M := hnot
  by_contra hle
  have hZ₀map_ne : Z₀.map (toModO3p Γ) ≠ ⊥ := by
    intro hbot
    apply hle
    intro z hz
    have hzmap : toModO3p Γ z ∈ Z₀.map (toModO3p Γ) := Subgroup.mem_map_of_mem _ hz
    rw [hbot, Subgroup.mem_bot] at hzmap
    rw [hJdef]
    exact (QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 Γ) z).mp hzmap
  haveI hKbN : (K.map (toModO3p Γ)).Normal :=
    h.normal_k.map _ (QuotientGroup.mk'_surjective _)
  haveI hZmapN : (Z₀.map (toModO3p Γ)).Normal :=
    hZ₀n.map _ (QuotientGroup.mk'_surjective _)
  have hKbar_le : K.map (toModO3p Γ) ≤ Z₀.map (toModO3p Γ) :=
    r925_le_of_normal (r925_kbar_simple h) (r925_kbar_centralizer h) hZ₀map_ne
  obtain ⟨D, hDY, hD3⟩ := h.y_cover.exists_subgroup_card_three
  have hDleK : D ≤ K := hDY.trans h.y_le_k
  have hDZ : D ≤ Z₀ := by
    intro d hd
    have hdmap : toModO3p Γ d ∈ Z₀.map (toModO3p Γ) :=
      hKbar_le (Subgroup.mem_map_of_mem _ (hDleK hd))
    have hd3 : d ^ 3 ^ 1 = 1 := by
      have h : orderOf d ∣ 3 := by
        rw [← hD3]
        exact Subgroup.orderOf_dvd_natCard D hd
      simpa using orderOf_dvd_iff_pow_eq_one.mp h
    exact r925_mem_of_map_mem r925_pPrimeCore_orderOf hd3 hdmap
  have hDcentJ : D ≤ centralizer (J : Set Γ) :=
    r925_centralizes_of_centralizes_fstar (J := J)
      (fun x hx => r925_pPrimeCore_orderOf x (by rwa [hJdef] at hx)) hD3 hDZ
  have hJcentD : J ≤ centralizer (D : Set Γ) := Subgroup.le_centralizer_iff.mpr hDcentJ
  have hJM : J ≤ M :=
    (hJcentD.trans (Subgroup.centralizer_le_normalizer (D : Set Γ))).trans
      (h.m_normalizer D (hDY.trans h.y_le) hD3)
  exact hJnot hJM

theorem r925_im_Y_inf_centralizer (hKSch : UCK.KSch) {Γ : Type} [Group Γ] [Finite Γ]
    {Y K M : Subgroup Γ} (h : R925Ctx Γ Y K M)
    (hZ : centralizer (Fstar (CFSG.pPrimeCore 3 Γ) : Set Γ) ≤ CFSG.pPrimeCore 3 Γ) :
    Y ⊓ centralizer (r925PCoreGe5 Γ : Set Γ) = ⊥ := by
  set C : Subgroup Γ := centralizer (r925PCoreGe5 Γ : Set Γ) with hCdef
  set X : Subgroup Γ := Y ⊓ C with hXdef
  haveI hPchar : (r925PCoreGe5 Γ).Characteristic := by
    rw [r925PCoreGe5]
    infer_instance
  haveI hCchar : C.Characteristic := by
    rw [hCdef]
    exact Subgroup.characteristic_centralizer
  haveI hCn : C.Normal := inferInstance
  haveI hXn : (X.subgroupOf Y).Normal := by
    rw [hXdef, Subgroup.inf_subgroupOf_left]
    infer_instance
  have hfit_le : r925FittingIn (CFSG.pPrimeCore 3 Γ) ≤ r925PCoreGe5 Γ :=
    r925_fitting_le_pCoreGe5 h.o2_eq_bot
  have hYlayer : Y ≤ centralizer (r925LayerIn (CFSG.pPrimeCore 3 Γ) : Set Γ) :=
    r925_layer_centralized hKSch h.kgroup
      (fun q hq h5 => h.rank_gt_three q hq (by omega)) h.y_cover.1 h.y_cover.isThreeGen
  have hXsub : X.subgroupOf Y = ⊥ := by
    refine IsPerfA5Cover.eq_bot_of_odd h.y_cover (X.subgroupOf Y) ?_
    intro x hx
    have hxX : (x : Γ) ∈ X := Subgroup.mem_subgroupOf.mp hx
    have hxC : (x : Γ) ∈ C := (Subgroup.mem_inf.mp hxX).2
    have hxY : (x : Γ) ∈ Y := (Subgroup.mem_inf.mp hxX).1
    have hyFit : (x : Γ) ∈ centralizer (r925FittingIn (CFSG.pPrimeCore 3 Γ) : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp hxC z (hfit_le hz)
    have hyLayer : (x : Γ) ∈ centralizer (r925LayerIn (CFSG.pPrimeCore 3 Γ) : Set Γ) :=
      hYlayer hxY
    have hyFstar : (x : Γ) ∈ centralizer (Fstar (CFSG.pPrimeCore 3 Γ) : Set Γ) := by
      rw [r925_fstar_eq_sup (CFSG.pPrimeCore 3 Γ), Subgroup.sup_eq_closure,
        Subgroup.centralizer_closure]
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases hz with hzA | hzB
      · exact Subgroup.mem_centralizer_iff.mp hyFit z hzA
      · exact Subgroup.mem_centralizer_iff.mp hyLayer z hzB
    have hyJ : (x : Γ) ∈ CFSG.pPrimeCore 3 Γ := hZ hyFstar
    have hyFitting : (x : Γ) ∈ r925FittingIn (CFSG.pPrimeCore 3 Γ) :=
      r925_centralizer_fstar_le_fitting (CFSG.pPrimeCore 3 Γ) ⟨hyFstar, hyJ⟩
    have hyPCore : (x : Γ) ∈ r925PCoreGe5 Γ := hfit_le hyFitting
    have hcop6 : Nat.Coprime (orderOf (x : Γ)) 6 := r925_pCoreGe5_orderOf (x : Γ) hyPCore
    have hcop2 : Nat.Coprime (orderOf (x : Γ)) 2 :=
      hcop6.coprime_dvd_right (by norm_num : (2 : ℕ) ∣ 6)
    have h2not : ¬ 2 ∣ orderOf (x : Γ) := by
      rw [Nat.coprime_comm] at hcop2
      exact (Nat.prime_two.coprime_iff_not_dvd).mp hcop2
    rw [← Subgroup.orderOf_coe x]
    exact Nat.not_even_iff_odd.mp fun he => h2not (even_iff_two_dvd.mp he)
  have hXle : X ≤ Y := by rw [hXdef]; exact inf_le_left
  have hXbot : X = ⊥ := by
    have h := congrArg (Subgroup.map Y.subtype) hXsub
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXle, Subgroup.map_bot] at h
  exact hXbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
