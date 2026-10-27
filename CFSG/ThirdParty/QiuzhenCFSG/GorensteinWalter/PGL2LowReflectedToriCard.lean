module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2LowDihedralOvergroupCard
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeNormalIndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorusFixedSylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicIndexTwoSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Two reflected odd tori in odd `PGL₂`

The low-two-part torus and a derived-subgroup conjugate associated to the
opposite outer involution generate, together with the inner reflector, a
subgroup of the derived `PSL₂` whose order is divisible by four.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

public structure PGL2LowReflectedToriData
    (K : Type u) [Field K] [Finite K]
    (P : Sylow 2 (PGL2 K)) {m : ℕ}
    (eP : P ≃* DihedralGroup (2 ^ m)) where
  U : Subgroup (PGL2 K)
  s : PGL2 K
  t : PGL2 K
  k : PGL2 K
  g : PGL2 K
  R : Subgroup (PGL2 K)
  Rstar : Subgroup (PGL2 K)
  U_cyclic : IsCyclic U
  U_half_odd : Odd (Nat.card U / 2)
  U_card : Nat.card U = Nat.card K - 1 ∨ Nat.card U = Nat.card K + 1
  s_involution : IsInvolution (s : PGL2 K)
  t_involution : IsInvolution (t : PGL2 K)
  t_commutes_s : Commute t s
  s_mem_U : s ∈ U
  s_not_mem_commutator : s ∉ commutator (PGL2 K)
  t_mem_commutator : t ∈ commutator (PGL2 K)
  t_not_mem_U : t ∉ U
  t_inverts_U : ∀ x : PGL2 K, x ∈ U → t * x * t⁻¹ = x⁻¹
  w : PGL2 K
  t_eq_w_or_ws : t = w ∨ t = w * s
  w_not_mem_U : w ∉ U
  w_involution : w * w = 1
  w_inverts_U : ∀ x : PGL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹
  centralizer_eq :
    Subgroup.centralizer ({s} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w
  k_mem_commutator : k ∈ commutator (PGL2 K)
  k_conj_s : k * s * k⁻¹ = t * s
  R_eq : R = U ⊓ commutator (PGL2 K)
  Rstar_eq : Rstar = R.map (MulAut.conj k).toMonoidHom
  R_card_odd : Odd (Nat.card R)
  R_card_gt_one : 1 < Nat.card R
  R_le_centralizer_s : R ≤ Subgroup.centralizer ({s} : Set (PGL2 K))
  Rstar_le_centralizer_ts :
    Rstar ≤ Subgroup.centralizer ({t * s} : Set (PGL2 K))
  R_le_commutator : R ≤ commutator (PGL2 K)
  Rstar_le_commutator : Rstar ≤ commutator (PGL2 K)
  conj_s_mem_P : g * s * g⁻¹ ∈ (P : Subgroup (PGL2 K))
  conj_t_eq_central :
    g * t * g⁻¹ =
      (eP.symm (DihedralGroup.r
        (2 ^ (m - 1) : ZMod (2 ^ m))) : PGL2 K)
  four_dvd_card : 4 ∣ Nat.card (↥((R ⊔ Subgroup.zpowers t) ⊔ Rstar))

/-- The two reflected odd tori used in the component branch of
Gorenstein--Walter Theorem 2.6 generate an inner subgroup of order divisible
by four. -/
public theorem pgl2_low_reflected_tori_card_four
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (P : Sylow 2 (PGL2 K)) {m : ℕ}
    (eP : P ≃* DihedralGroup (2 ^ m)) :
    Nonempty (PGL2LowReflectedToriData K P eP) := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  rcases hK with ⟨r, f, hr, hrodd, hf, hKcard⟩
  let : Fact r.Prime := ⟨hr⟩
  have hK' : IsOddPrimePower (Nat.card K) :=
    ⟨r, f, hr, hrodd, hf, hKcard⟩
  have hqOdd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hrodd.pow
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hJindex : J.index = 2 := by
    dsimp [J]
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK' hcard]
    exact pgl2_psl2Range_index_eq_two K hK'
  obtain ⟨U, s, t, w, hUcyc, hUodd, hUorder, hsU, hsJ, hsne, hssq,
      htJ, htU, htsq, htinv, htrel, hwU, hwsq, hwinv, hcent⟩ :=
    pgl2_low_two_part_torus_reflection_data K hK' hcard
  have hsI : IsInvolution s :=
    ⟨hsne, by simpa [pow_two] using hssq⟩
  have htne : t ≠ 1 := by
    intro ht
    apply htU
    rw [ht]
    exact U.one_mem
  have htI : IsInvolution t :=
    ⟨htne, by simpa [pow_two] using htsq⟩
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hssq
  have htscomm : Commute t s := by
    show t * s = s * t
    calc
      t * s = (t * s * t⁻¹) * t := by group
      _ = s⁻¹ * t := by rw [htinv s hsU]
      _ = s * t := by rw [hsinv]
  have htsne : t ≠ s := by
    intro h
    apply htU
    rw [h]
    exact hsU
  let b : PGL2 K := t * s
  have hbne : b ≠ 1 := by
    intro hb
    apply htsne
    calc
      t = t * 1 := by simp
      _ = t * (s * s) := by rw [hssq]
      _ = (t * s) * s := by group
      _ = 1 * s := by simpa [b] using congrArg (fun x => x * s) hb
      _ = s := by simp
  have hbsq : b * b = 1 := by
    dsimp [b]
    calc
      (t * s) * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [htscomm.eq.symm]
      _ = (t * t) * (s * s) := by group
      _ = 1 := by rw [htsq, hssq]; simp
  have hbI : IsInvolution b :=
    ⟨hbne, by simpa [pow_two] using hbsq⟩
  have hbJ : b ∉ J := by
    intro hbmem
    have hiff := (J.mul_mem_iff_of_index_two hJindex).mp hbmem
    exact hsJ (hiff.mp htJ)
  have hconj : IsConj s b :=
    pgl2_outer_involutions_conjugate K hK' hcard hsI hbI hsJ hbJ
  obtain ⟨g, hgs⟩ := isConj_iff.mp hconj
  obtain ⟨k, hkJ, hks⟩ :
      ∃ k : PGL2 K, k ∈ J ∧ k * s * k⁻¹ = b := by
    by_cases hgJ : g ∈ J
    · exact ⟨g, hgJ, hgs⟩
    · refine ⟨b * g, ?_, ?_⟩
      · exact (J.mul_mem_iff_of_index_two hJindex).mpr
          (iff_of_false hbJ hgJ)
      · calc
          (b * g) * s * (b * g)⁻¹ = b * (g * s * g⁻¹) * b⁻¹ := by
            group
          _ = b * b * b⁻¹ := by rw [hgs]
          _ = b := by group
  let R : Subgroup (PGL2 K) := U ⊓ J
  have hUtwo : Nat.card U = 2 * (Nat.card U / 2) := by
    rcases hUorder with hsub | hadd
    · rw [hsub]
      rcases hqOdd with ⟨a, ha⟩
      omega
    · rw [hadd]
      rcases hqOdd with ⟨a, ha⟩
      omega
  obtain ⟨D, hDeq, hDJ, hRDindex, hDcard, hDdih⟩ :=
    exists_dihedral_subgroup_le_index_two_of_reflected_cyclic
      J U hJindex hUcyc (Nat.card U / 2) hUtwo
        (fun hUJ => hsJ (hUJ hsU)) t htJ htU htsq htinv
  have hRleD : R ≤ D := by
    rw [hDeq]
    exact le_sup_left
  let RD : Subgroup D := R.subgroupOf D
  have hRDcard : Nat.card RD = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleD)
  have hRcard : Nat.card R = Nat.card U / 2 := by
    have hmul := RD.index_mul_card
    rw [show RD.index = 2 by simpa [RD, R] using hRDindex,
      hRDcard, hDcard, hUtwo] at hmul
    omega
  have hRodd : Odd (Nat.card R) := by
    rw [hRcard]
    exact hUodd
  have hRgt : 1 < Nat.card R := by
    have hhalfpos : 0 < Nat.card U / 2 := by
      have hUpos : 0 < Nat.card U := Nat.card_pos
      rw [hUtwo] at hUpos
      omega
    have hhalfne : Nat.card U / 2 ≠ 1 := by
      intro hone
      have hUcardTwo : Nat.card U = 2 := by rw [hUtwo, hone]
      rcases hUorder with hsub | hadd
      · rw [hUcardTwo] at hsub
        omega
      · rw [hUcardTwo] at hadd
        omega
    rw [hRcard]
    omega
  let Rstar : Subgroup (PGL2 K) :=
    R.map (MulAut.conj k).toMonoidHom
  have hRstarJ : Rstar ≤ J := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyR, rfl⟩
    exact (inferInstance : J.Normal).conj_mem y hyR.2 k
  have hRstarcard : Nat.card Rstar = Nat.card R := by
    dsimp [Rstar]
    exact Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hRstarodd : Odd (Nat.card Rstar) := by
    rw [hRstarcard]
    exact hRodd
  have hRstarne : Rstar ≠ ⊥ := by
    intro hbot
    have hcardOne : Nat.card Rstar = 1 := by rw [hbot]; simp
    rw [hRstarcard] at hcardOne
    omega
  let : IsCyclic U := hUcyc
  let : CommGroup U := IsCyclic.commGroup
  have hRcent : R ≤
      Subgroup.centralizer ({s} : Set (PGL2 K)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (mul_comm (⟨x, hx.1⟩ : U) (⟨s, hsU⟩ : U))
  have hRstarcent : Rstar ≤
      Subgroup.centralizer ({b} : Set (PGL2 K)) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyR, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hks]
    have hys : y * s = s * y :=
      congrArg Subtype.val
        (mul_comm (⟨y, hyR.1⟩ : U) (⟨s, hsU⟩ : U))
    calc
      (k * y * k⁻¹) * (k * s * k⁻¹) = k * (y * s) * k⁻¹ := by group
      _ = k * (s * y) * k⁻¹ := by rw [hys]
      _ = (k * s * k⁻¹) * (k * y * k⁻¹) := by group
  let M : Subgroup (PGL2 K) := D ⊔ Rstar
  have hMleJ : M ≤ J := sup_le hDJ hRstarJ
  have hMneD : M ≠ D := by
    intro hMD
    have hRstarD : Rstar ≤ D := by
      intro x hx
      have hxM : x ∈ M := (le_sup_right : Rstar ≤ M) hx
      rwa [hMD] at hxM
    let RstarD : Subgroup D := Rstar.subgroupOf D
    have hRstarDodd : Odd (Nat.card RstarD) := by
      rw [show Nat.card RstarD = Nat.card Rstar by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRstarD)]
      exact hRstarodd
    have hRDnormal : RD.Normal :=
      Subgroup.normal_of_index_eq_two (by simpa [RD, R] using hRDindex)
    have hRstarDRD : RstarD ≤ RD :=
      odd_card_subgroup_le_normal_index_two RD RstarD hRDnormal
        (by simpa [RD, R] using hRDindex) hRstarDodd
    have hRstarR : Rstar ≤ R := by
      intro x hx
      let xD : D := ⟨x, hRstarD hx⟩
      have hxRstarD : xD ∈ RstarD := hx
      exact hRstarDRD hxRstarD
    have hRstarbot : Rstar = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxR : x ∈ R := hRstarR hx
      have hxs : x * s = s * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hRcent hxR)
      have hxb : x * b = b * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (hRstarcent hx)
      have hxt : x * t = t * x := by
        dsimp [b] at hxb
        calc
          x * t = (x * (t * s)) * s⁻¹ := by group
          _ = ((t * s) * x) * s⁻¹ := by rw [hxb]
          _ = t * (s * x * s⁻¹) := by group
          _ = t * x := by rw [hxs.symm]; group
      have htconj : t * x * t⁻¹ = x := by
        calc
          t * x * t⁻¹ = x * t * t⁻¹ := by rw [← hxt]
          _ = x := by simp
      have hxeqinv : x = x⁻¹ := by
        exact htconj.symm.trans (htinv x hxR.1)
      have hxsq : x ^ 2 = 1 := by
        calc
          x ^ 2 = x * x := pow_two x
          _ = x * x⁻¹ := congrArg (fun z => x * z) hxeqinv
          _ = 1 := mul_inv_cancel x
      have hxsubsq : (⟨x, hx⟩ : Rstar) ^ 2 = 1 :=
        Subtype.ext hxsq
      have hxsubone : (⟨x, hx⟩ : Rstar) = 1 :=
        eq_one_of_sq_eq_one_of_coprime_two
          hRstarodd.coprime_two_left hxsubsq
      exact congrArg Subtype.val hxsubone
    exact hRstarne hRstarbot
  let eJ : J ≃* PSL2 K :=
    (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
      K hK' hcard (MulEquiv.refl (PGL2 K))).some
  let DJ : Subgroup J := D.subgroupOf J
  let MJ : Subgroup J := M.subgroupOf J
  let D0 : Subgroup (PSL2 K) := DJ.map eJ.toMonoidHom
  let M0 : Subgroup (PSL2 K) := MJ.map eJ.toMonoidHom
  have hDJMJ : DJ ≤ MJ := by
    intro x hx
    exact (le_sup_left : D ≤ M) hx
  have hD0M0 : D0 ≤ M0 := Subgroup.map_mono hDJMJ
  let eDJ : DJ ≃* D0 :=
    Subgroup.equivMapOfInjective DJ eJ.toMonoidHom eJ.injective
  let eD : D ≃* D0 :=
    (Subgroup.subgroupOfEquivOfLe hDJ).symm.trans eDJ
  let eMJ : MJ ≃* M0 :=
    Subgroup.equivMapOfInjective MJ eJ.toMonoidHom eJ.injective
  let eM : M ≃* M0 :=
    (Subgroup.subgroupOfEquivOfLe hMleJ).symm.trans eMJ
  have hD0card : Nat.card D0 = 2 * (Nat.card U / 2) := by
    calc
      Nat.card D0 = Nat.card D := Nat.card_congr eD.toEquiv.symm
      _ = Nat.card U := hDcard
      _ = 2 * (Nat.card U / 2) := hUtwo
  have hD0order : Nat.card D0 = Nat.card K - 1 ∨
      Nat.card D0 = Nat.card K + 1 := by
    rw [show Nat.card D0 = Nat.card U by
      calc
        Nat.card D0 = Nat.card D := Nat.card_congr eD.toEquiv.symm
        _ = Nat.card U := hDcard]
    exact hUorder
  have hD0dih : Nonempty
      (D0 ≃* DihedralGroup (Nat.card U / 2)) :=
    ⟨eD.symm.trans hDdih.some⟩
  have hfourM : 4 ∣ Nat.card M := by
    rcases psl2_low_dihedral_overgroup_eq_or_four_dvd_card
        hKcard hrodd hcard hUodd D0 M0 hD0card hD0order hD0dih hD0M0 with
      hM0D0 | hfour
    · exfalso
      apply hMneD
      apply le_antisymm
      · intro x hxM
        let xJ : J := ⟨x, hMleJ hxM⟩
        have hxM0 : eJ xJ ∈ M0 :=
          Subgroup.mem_map.mpr ⟨xJ, hxM, rfl⟩
        rw [hM0D0] at hxM0
        rcases Subgroup.mem_map.mp hxM0 with ⟨dJ, hdD, hdx⟩
        have hxd : xJ = dJ := eJ.injective hdx.symm
        change (xJ : PGL2 K) ∈ D
        rw [hxd]
        exact hdD
      · exact le_sup_left
    · have hM0card : Nat.card M0 = Nat.card M :=
        (Nat.card_congr eM.toEquiv).symm
      rwa [hM0card] at hfour
  let A : Subgroup (PGL2 K) := Subgroup.zpowers s
  let B : Subgroup (PGL2 K) := Subgroup.zpowers t
  have hAp : IsPGroup 2 A := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime hsI.2 hsI.1]
    norm_num
  have hBp : IsPGroup 2 B := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime htI.2 htI.1]
    norm_num
  have htNormA : t ∈ Subgroup.normalizer (A : Set (PGL2 K)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    have htinverse : t⁻¹ = t :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using htI.2)
    change Subgroup.zpowers (t * s * t⁻¹) = Subgroup.zpowers s
    rw [htinverse]
    have htsq : t * t = 1 := by simpa [pow_two] using htI.2
    have hconj : t * s * t = s := by
      calc
        t * s * t = s * (t * t) := by rw [htscomm.eq]; group
        _ = s := by rw [htsq, mul_one]
    rw [hconj]
  have hBnormA : B ≤ Subgroup.normalizer (A : Set (PGL2 K)) :=
    Subgroup.zpowers_le.mpr htNormA
  let V : Subgroup (PGL2 K) := A ⊔ B
  have hVp : IsPGroup 2 V :=
    IsPGroup.to_sup_of_normal_left' hAp hBp hBnormA
  obtain ⟨Q, hVQ⟩ := IsPGroup.exists_le_sylow hVp
  have hsQ : s ∈ (Q : Subgroup (PGL2 K)) :=
    hVQ ((le_sup_left : A ≤ V) (Subgroup.mem_zpowers s))
  have htQ : t ∈ (Q : Subgroup (PGL2 K)) :=
    hVQ ((le_sup_right : B ≤ V) (Subgroup.mem_zpowers t))
  obtain ⟨a, ha⟩ :=
    @MulAction.IsPretransitive.exists_smul_eq (PGL2 K)
      (Sylow 2 (PGL2 K)) inferInstance inferInstance Q P
  have hsP : a * s * a⁻¹ ∈ (P : Subgroup (PGL2 K)) := by
    have hmem : a * s * a⁻¹ ∈
        ((a • Q : Sylow 2 (PGL2 K)) : Subgroup (PGL2 K)) := by
      change (MulAut.conj a) s ∈
        (Q : Subgroup (PGL2 K)).map (MulAut.conj a).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨s, hsQ, rfl⟩
    rwa [ha] at hmem
  have htP : a * t * a⁻¹ ∈ (P : Subgroup (PGL2 K)) := by
    have hmem : a * t * a⁻¹ ∈
        ((a • Q : Sylow 2 (PGL2 K)) : Subgroup (PGL2 K)) := by
      change (MulAut.conj a) t ∈
        (Q : Subgroup (PGL2 K)).map (MulAut.conj a).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨t, htQ, rfl⟩
    rwa [ha] at hmem
  let HP : Subgroup P := J.subgroupOf (P : Subgroup (PGL2 K))
  have hHPindex : HP.index = 2 := by
    have : J.Normal := by dsimp [J]; infer_instance
    have hdvd : HP.index ∣ 2 := by
      change J.relIndex (P : Subgroup (PGL2 K)) ∣ 2
      simpa [hJindex] using
        (Subgroup.relIndex_dvd_index_of_normal
          (H := J) (K := (P : Subgroup (PGL2 K))))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hone | htwo
    · exfalso
      have htop : HP = ⊤ := Subgroup.index_eq_one.mp hone
      have hsPH : (⟨a * s * a⁻¹, hsP⟩ : P) ∈ HP := by
        rw [htop]
        trivial
      apply hsJ
      have hsconjJ : a * s * a⁻¹ ∈ J := hsPH
      have hback : a⁻¹ * (a * s * a⁻¹) * (a⁻¹)⁻¹ ∈ J :=
        (inferInstance : J.Normal).conj_mem
          (a * s * a⁻¹) hsconjJ a⁻¹
      have hcancel : a⁻¹ * (a * s * a⁻¹) * (a⁻¹)⁻¹ = s := by
        group
      rw [hcancel] at hback
      simpa [J] using hback
    · exact htwo
  let sP : P := ⟨a * s * a⁻¹, hsP⟩
  let tP : P := ⟨a * t * a⁻¹, htP⟩
  have htPH : tP ∈ HP := by
    change a * t * a⁻¹ ∈ J
    exact (inferInstance : J.Normal).conj_mem t htJ a
  have hsPH : sP ∉ HP := by
    intro hs
    apply hsJ
    have hsconjJ : a * s * a⁻¹ ∈ J := hs
    have hback : a⁻¹ * (a * s * a⁻¹) * (a⁻¹)⁻¹ ∈ J :=
      (inferInstance : J.Normal).conj_mem
        (a * s * a⁻¹) hsconjJ a⁻¹
    have hcancel : a⁻¹ * (a * s * a⁻¹) * (a⁻¹)⁻¹ = s := by
      group
    rw [hcancel] at hback
    simpa [J] using hback
  have htPne : tP ≠ 1 := by
    intro h
    apply htI.1
    have hval : a * t * a⁻¹ = 1 := congrArg Subtype.val h
    calc
      t = a⁻¹ * (a * t * a⁻¹) * a := by group
      _ = 1 := by rw [hval]; simp
  have hsPne : sP ≠ 1 := by
    intro h
    apply hsI.1
    have hval : a * s * a⁻¹ = 1 := congrArg Subtype.val h
    calc
      s = a⁻¹ * (a * s * a⁻¹) * a := by group
      _ = 1 := by rw [hval]; simp
  have htPsq : tP * tP = 1 := by
    apply Subtype.ext
    change (a * t * a⁻¹) * (a * t * a⁻¹) = 1
    calc
      (a * t * a⁻¹) * (a * t * a⁻¹) = a * (t * t) * a⁻¹ := by group
      _ = 1 := by
        rw [show t * t = 1 by simpa [pow_two] using htI.2]
        simp
  have hsPsq : sP * sP = 1 := by
    apply Subtype.ext
    change (a * s * a⁻¹) * (a * s * a⁻¹) = 1
    calc
      (a * s * a⁻¹) * (a * s * a⁻¹) = a * (s * s) * a⁻¹ := by group
      _ = 1 := by
        rw [show s * s = 1 by simpa [pow_two] using hsI.2]
        simp
  have hcommP : Commute tP sP := by
    show tP * sP = sP * tP
    apply Subtype.ext
    simpa [tP, sP] using congrArg (MulAut.conj a) htscomm.eq
  have hm : 2 ≤ m := pgl2_dihedral_sylow_parameter_ge_two K hK' P eP
  have htPcentral : tP = eP.symm (DihedralGroup.r
      (2 ^ (m - 1) : ZMod (2 ^ m))) :=
    eq_central_involution_of_mem_indexTwo_of_commuting_involution_not_mem
      hm eP HP hHPindex tP sP htPH hsPH htPne hsPne htPsq hsPsq hcommP
  refine ⟨⟨U, s, t, k, a, R, Rstar, hUcyc, hUodd, hUorder, hsI, htI,
    htscomm, hsU, hsJ, htJ, htU, htinv, w, htrel, hwU, hwsq, hwinv, hcent,
    hkJ, ?_, rfl, rfl, hRodd, hRgt,
    hRcent, ?_, inf_le_right, hRstarJ, hsP, ?_, ?_⟩⟩
  · simpa [b] using hks
  · simpa [b] using hRstarcent
  · exact congrArg Subtype.val htPcentral
  · simpa [M, hDeq, R, sup_assoc] using hfourM

end CFSG.GorensteinWalter
