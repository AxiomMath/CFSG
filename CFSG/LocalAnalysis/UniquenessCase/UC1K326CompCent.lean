module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompUniq
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Crit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

private theorem pCore_le_centralizer_of_isComponentOf {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤) :
    CFSG.pCore 3 G ≤ Subgroup.centralizer (L : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsNilpotent (CFSG.pCore 3 G) :=
    (CFSG.pCore_isPGroup (p := 3) (G := G)).isNilpotent
  have h := CFSG.ComponentClassification.LocalComponents.commutes_with_solvable_subnormal L
    (CFSG.pCore 3 G) hL (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (CFSG.pCore_normal (p := 3) (G := G)).isSubnormal)
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact h

private theorem zOf_normal {L : Subgroup G} (hLn : L.Normal) : (zOf L).Normal := by
  haveI : L.Normal := hLn
  exact ConjAct.normal_of_characteristic_of_normal

private theorem zOf_le_pCore {L : Subgroup G} (hLn : L.Normal)
    (hz : Nat.card (Subgroup.center ↥L) = 3) :
    zOf L ≤ CFSG.pCore 3 G := by
  have hcard : Nat.card (zOf L) = 3 := by
    rw [zOf, Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective, hz]
  have hZp : IsPGroup 3 (zOf L) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  change zOf L ≤ sSup {K : Subgroup G | K.Normal ∧ IsPGroup 3 K}
  exact le_sSup ⟨zOf_normal hLn, hZp⟩

private theorem pCore_ne_bot_of_component {L : Subgroup G} (hLn : L.Normal)
    (hz : Nat.card (Subgroup.center ↥L) = 3) : CFSG.pCore 3 G ≠ ⊥ := by
  intro hbot
  have hle : zOf L ≤ (⊥ : Subgroup G) := (zOf_le_pCore hLn hz).trans (le_of_eq hbot)
  have hzbot : zOf L = ⊥ := le_bot_iff.mp hle
  have hcard : Nat.card (zOf L) = 3 := by
    rw [zOf, Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective, hz]
  rw [hzbot, Subgroup.card_bot] at hcard
  norm_num at hcard

private theorem comp_coprime_mem_centralizer_pCore (h : Hyp326 G n P) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤)
    (hu : ∀ L' : Subgroup G, CFSG.Open.IsComponentOf L' ⊤ → L' = L)
    (hz : Nat.card (Subgroup.center ↥L) = 3)
    {c : G} (hc : c ∈ Subgroup.centralizer (L : Set G))
    (hc_cop : Nat.Coprime (orderOf c) 3) :
    c ∈ Subgroup.centralizer (CFSG.pCore 3 G : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLn : L.Normal :=
    comp_normal (fun L₁ L₂ h₁ h₂ => (hu L₁ h₁).trans (hu L₂ h₂).symm) hL
  have hQ : CFSG.pCore 3 G ≠ ⊥ := pCore_ne_bot_of_component hLn hz
  obtain ⟨D, hDQ, hDn, hDexp, hDcop⟩ := exists_exp3_normal_coprime (G := G) hQ
  have hQleC : CFSG.pCore 3 G ≤ Subgroup.centralizer (L : Set G) :=
    pCore_le_centralizer_of_isComponentOf hL
  obtain ⟨e⟩ := h.wr
  have hcentD : c ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    let y : G := ⁅x, c⁆
    have hxC : x ∈ Subgroup.centralizer (L : Set G) := hQleC (hDQ hx)
    have hyC : y ∈ Subgroup.centralizer (L : Set G) := by
      have h1 := (Subgroup.centralizer (L : Set G)).mul_mem
        ((Subgroup.centralizer (L : Set G)).mul_mem
          ((Subgroup.centralizer (L : Set G)).mul_mem hxC hc)
          ((Subgroup.centralizer (L : Set G)).inv_mem hxC))
        ((Subgroup.centralizer (L : Set G)).inv_mem hc)
      simpa [y, commutatorElement_def] using h1
    have hyD : y ∈ D := by
      have h1 : c * x⁻¹ * c⁻¹ ∈ D := hDn.conj_mem x⁻¹ (D.inv_mem hx) c
      have h2 : x * (c * x⁻¹ * c⁻¹) ∈ D := D.mul_mem hx h1
      simpa [y, commutatorElement_def, mul_assoc] using h2
    have hyP : y ∈ P := pCore_le_sylow h.sylow (hDQ hyD)
    have hy3 : y ^ 3 = 1 := hDexp y hyD
    have hTnorm : ((P ⊓ L).subgroupOf P).Normal := by
      rw [Subgroup.inf_subgroupOf_left L P]
      exact hLn.subgroupOf P
    have hnab : ¬ IsMulCommutative ↥(P ⊓ L) :=
      not_isMulCommutative_of_isSylowOf (L := L) (T := P ⊓ L) hL.2.2 hz
        (h.sylow.inf_of_le_normalizer (N := L) le_top
          (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hLn).symm))
    have hnab' : ¬ IsMulCommutative ↥((P ⊓ L).subgroupOf P) := by
      intro hcomm
      exact hnab (IsMulCommutative.of_comm (fun a b => by
        let φ := Subgroup.subgroupOfEquivOfLe (inf_le_left : P ⊓ L ≤ P)
        have h1 : φ.symm a * φ.symm b = φ.symm b * φ.symm a :=
          hcomm.is_comm.comm _ _
        calc a * b = φ (φ.symm a) * φ (φ.symm b) := by simp
          _ = φ (φ.symm a * φ.symm b) := (φ.map_mul _ _).symm
          _ = φ (φ.symm b * φ.symm a) := by rw [h1]
          _ = φ (φ.symm b) * φ (φ.symm a) := φ.map_mul _ _
          _ = b * a := by simp))
    have hycentT : y ∈ Subgroup.centralizer (((P ⊓ L : Subgroup G) : Set G)) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right) hyC
    have hy' : (⟨y, hyP⟩ : ↥P) ∈
        Subgroup.centralizer (((P ⊓ L).subgroupOf P : Subgroup ↥P) : Set ↥P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hzz
      apply Subtype.ext
      have hzz' : (z : G) ∈ (P ⊓ L : Subgroup G) := hzz
      exact Subgroup.mem_centralizer_iff.mp hycentT (z : G) hzz'
    have hmem : (⟨y, hyP⟩ : ↥P) ∈ Subgroup.center ↥P :=
      zwr_centralizer_nonabelian_normal h.one_le e hTnorm hnab' hy'
    have hyP3 : (⟨y, hyP⟩ : ↥P) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hy3
    have hyZ : y ∈ Subgroup.center G := h.central ⟨y, hyP⟩ hmem hyP3
    have hyc : Commute y c :=
      (commute_iff_eq y c).mpr (Subgroup.mem_center_iff.mp hyZ c).symm
    have hxc : x * c * x⁻¹ = y * c := by
      simp only [y, commutatorElement_def]
      group
    have hconj : ∀ m : ℕ, x * c ^ m * x⁻¹ = (x * c * x⁻¹) ^ m := by
      intro m
      simpa [MulAut.conj_apply] using (map_pow (MulAut.conj x) c m)
    have hpow : ∀ m : ℕ, x * c ^ m * x⁻¹ = y ^ m * c ^ m := by
      intro m
      rw [hconj m, hxc, hyc.mul_pow m]
    have hy_m : y ^ orderOf c = 1 := by
      have hh := hpow (orderOf c)
      rw [pow_orderOf_eq_one, mul_one, mul_one, mul_inv_cancel] at hh
      exact hh.symm
    have hy1 : y = 1 :=
      (pow_eq_one_iff_of_coprime (a := y) hc_cop).mp ⟨hy_m, hy3⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp hy1
  exact hDcop c hc_cop hcentD

private theorem comp_coprime_mem_pCore (h : Hyp326 G n P) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤)
    (hu : ∀ L' : Subgroup G, CFSG.Open.IsComponentOf L' ⊤ → L' = L)
    (hz : Nat.card (Subgroup.center ↥L) = 3)
    {c : G} (hc : c ∈ Subgroup.centralizer (L : Set G))
    (hc_cop : Nat.Coprime (orderOf c) 3) :
    c ∈ CFSG.pCore 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLn : L.Normal :=
    comp_normal (fun L₁ L₂ h₁ h₂ => (hu L₁ h₁).trans (hu L₂ h₂).symm) hL
  have hcQ : c ∈ Subgroup.centralizer (CFSG.pCore 3 G : Set G) :=
    comp_coprime_mem_centralizer_pCore h hL hu hz hc hc_cop
  have hQleC : CFSG.pCore 3 G ≤ Subgroup.centralizer (L : Set G) :=
    pCore_le_centralizer_of_isComponentOf hL
  have hFstar : CFSG.Open.genFittingFStar G = CFSG.pCore 3 G ⊔ L := by
    rw [CFSG.Open.genFittingFStar.eq_sup, genFittingFitting_eq_pCore h.core]
    congr 1
    rw [CFSG.Open.genFittingLayer.eq_sSup]
    refine le_antisymm (sSup_le ?_) (le_sSup hL)
    intro L' hL'
    rw [hu L' hL']
  have hc_cent_sup : c ∈ Subgroup.centralizer
      (((CFSG.pCore 3 G ⊔ L : Subgroup G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hzsup
    change z ∈ (CFSG.pCore 3 G ⊔ L : Subgroup G) at hzsup
    rw [Subgroup.mem_sup_of_normal_left] at hzsup
    obtain ⟨q, hq, l, hl, hql⟩ := hzsup
    rw [← hql]
    have hq' : q * c = c * q := Subgroup.mem_centralizer_iff.mp hcQ q hq
    have hl' : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
    calc (q * l) * c = q * (l * c) := by rw [mul_assoc]
      _ = q * (c * l) := by rw [hl']
      _ = (q * c) * l := by rw [mul_assoc]
      _ = (c * q) * l := by rw [hq']
      _ = c * (q * l) := by rw [mul_assoc]
  have hcQL : c ∈ (CFSG.pCore 3 G ⊔ L : Subgroup G) := by
    have h := CFSG.Adapters.generalized_fitting_self_centralizing G
    rw [hFstar] at h
    exact h hc_cent_sup
  rw [Subgroup.mem_sup_of_normal_left] at hcQL
  obtain ⟨q, hq, l, hl, hql⟩ := hcQL
  have hlC : l ∈ Subgroup.centralizer (L : Set G) := by
    have hl_eq : l = q⁻¹ * c := by
      rw [← hql]
      group
    rw [hl_eq]
    exact (Subgroup.centralizer (L : Set G)).mul_mem
      ((Subgroup.centralizer (L : Set G)).inv_mem (hQleC hq)) hc
  have hlz : l ∈ zOf L := by
    refine Subgroup.mem_map.mpr ⟨⟨l, hl⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hlC m.1 m.2
  have hlQ : l ∈ CFSG.pCore 3 G := zOf_le_pCore hLn hz hlz
  rw [← hql]
  exact (CFSG.pCore 3 G).mul_mem hq hlQ

theorem comp_centralizer_le_pCore (h : Hyp326 G n P) {L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L ⊤)
    (hu : ∀ L' : Subgroup G, CFSG.Open.IsComponentOf L' ⊤ → L' = L)
    (hz : Nat.card (Subgroup.center ↥L) = 3) :
    Subgroup.centralizer (L : Set G) ≤ CFSG.pCore 3 G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLn : L.Normal :=
    comp_normal (fun L₁ L₂ h₁ h₂ => (hu L₁ h₁).trans (hu L₂ h₂).symm) hL
  haveI : L.Normal := hLn
  have hCp : IsPGroup 3 (Subgroup.centralizer (L : Set G)) := by
    intro g
    have hn0 : orderOf (g : G) ≠ 0 := (orderOf_pos (g : G)).ne'
    let k : ℕ := ordProj[3] (orderOf (g : G))
    have hk_dvd : k ∣ orderOf (g : G) := Nat.ordProj_dvd (orderOf (g : G)) 3
    have hk_ne : k ≠ 0 := (Nat.ordProj_pos (orderOf (g : G)) 3).ne'
    have hc_cop : Nat.Coprime (orderOf ((g : G) ^ k)) 3 := by
      rw [orderOf_pow_of_dvd hk_ne hk_dvd]
      exact (Nat.coprime_ordCompl (p := 3) (by norm_num) hn0).symm
    have hgmem : (g : G) ^ k ∈ Subgroup.centralizer (L : Set G) := (g ^ k).2
    have hQmem : (g : G) ^ k ∈ CFSG.pCore 3 G :=
      comp_coprime_mem_pCore h hL hu hz hgmem hc_cop
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 3) (G := G) ⟨(g : G) ^ k, hQmem⟩
    have hm' : ((g : G) ^ k) ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hord1 : orderOf ((g : G) ^ k) = 1 := by
      have hdvd : orderOf ((g : G) ^ k) ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
      have hc3 : Nat.Coprime (orderOf ((g : G) ^ k)) (3 ^ m) := hc_cop.pow_right m
      have hdvd1 : orderOf ((g : G) ^ k) ∣ 1 := by
        rw [← hc3.gcd_eq_one]
        exact Nat.dvd_gcd (dvd_refl _) hdvd
      exact Nat.dvd_one.mp hdvd1
    have hk1 : (g : G) ^ k = 1 := orderOf_eq_one_iff.mp hord1
    refine ⟨(orderOf (g : G)).factorization 3, Subtype.ext ?_⟩
    simpa [k] using hk1
  have hCnormal : (Subgroup.centralizer (L : Set G)).Normal := Subgroup.normal_centralizer
  exact le_sSup ⟨hCnormal, hCp⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
