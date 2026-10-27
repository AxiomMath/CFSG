module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
import CFSG.Quasithin.EmptyFaithful.E22PL2SevbS4
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.Walter.Defs
public import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.Quasithin.E22L2

open scoped MatrixGroups
open CFSG.GorensteinWalter CFSG.Walter

theorem e22pl2sevb_comap_centralizer {Γ Λ : Type*} [Group Γ] [Group Λ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (w : Λ) :
    (Subgroup.centralizer ({φ w} : Set Γ)).comap φ = Subgroup.centralizer ({w} : Set Λ) := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact hφ.eq_iff

theorem e22pl2sevb_exists_mem_centralizer_not_mem_range {Γ Λ : Type*} [Group Γ] [Group Λ]
    (φ : Λ →* Γ) (hφ : Function.Injective φ) (hN : φ.range.Normal) (hidx : φ.range.index = 2)
    {w : Λ} (hw : orderOf w = 2) (hconj : ∀ x : Λ, orderOf x = 2 → IsConj x w) :
    ∃ d : Γ, d ∈ Subgroup.centralizer ({φ w} : Set Γ) ∧ d ∉ φ.range := by
  classical
  set z : Γ := φ w with hzdef
  have hz2 : orderOf z = 2 := by rw [hzdef, orderOf_injective φ hφ w, hw]
  obtain ⟨g, hg⟩ : ∃ g : Γ, g ∉ φ.range := by
    by_contra hcon
    have htop : φ.range = ⊤ := eq_top_iff.mpr fun x _ => by_contra fun hx => hcon ⟨x, hx⟩
    rw [htop, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨w₂, hw₂⟩ : g * z * g⁻¹ ∈ φ.range := hN.conj_mem z ⟨w, rfl⟩ g
  have hw₂ord : orderOf w₂ = 2 := by
    rw [← orderOf_injective φ hφ w₂, hw₂]
    have := MulEquiv.orderOf_eq (MulAut.conj g) z
    rwa [MulAut.conj_apply, hz2] at this
  obtain ⟨l, hl⟩ := isConj_iff.mp (hconj w₂ hw₂ord)
  have hhz : (φ l * g) * z * (φ l * g)⁻¹ = z := by
    calc (φ l * g) * z * (φ l * g)⁻¹ = φ l * (g * z * g⁻¹) * (φ l)⁻¹ := by group
      _ = φ l * φ w₂ * (φ l)⁻¹ := by rw [hw₂]
      _ = φ (l * w₂ * l⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = z := by rw [hl]
  refine ⟨φ l * g, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc (φ l * g) * z = ((φ l * g) * z * (φ l * g)⁻¹) * (φ l * g) := by group
      _ = z * (φ l * g) := by rw [hhz]
  · intro hh'
    apply hg
    have : (φ l)⁻¹ * (φ l * g) ∈ φ.range :=
      φ.range.mul_mem (φ.range.inv_mem ⟨l, rfl⟩) hh'
    simpa using this

theorem e22pl2sevb_card_centralizer {Γ Λ : Type*} [Group Γ] [Group Λ] [Finite Γ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (hN : φ.range.Normal) (hidx : φ.range.index = 2)
    {w : Λ} (hw : orderOf w = 2) (hconj : ∀ x : Λ, orderOf x = 2 → IsConj x w) :
    Nat.card (Subgroup.centralizer ({φ w} : Set Γ)) =
      2 * Nat.card (Subgroup.centralizer ({w} : Set Λ)) := by
  classical
  set D := Subgroup.centralizer ({φ w} : Set Γ) with hD
  obtain ⟨d, hdD, hdR⟩ := e22pl2sevb_exists_mem_centralizer_not_mem_range φ hφ hN hidx hw hconj
  have hrel : φ.range.relIndex D = 2 := by
    have h1 : φ.range.relIndex D ∣ φ.range.index := by
      have := hN
      exact Subgroup.relIndex_dvd_index_of_normal φ.range D
    rw [hidx] at h1
    have h2 : φ.range.relIndex D ≠ 1 := fun h => hdR ((Subgroup.relIndex_eq_one.mp h) hdD)
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd h h2
    · exact h
  have hmap : φ.range ⊓ D = (Subgroup.centralizer ({w} : Set Λ)).map φ := by
    rw [← e22pl2sevb_comap_centralizer φ hφ w, Subgroup.map_comap_eq, inf_comm]
  have h := Subgroup.relIndex_mul_card (H := φ.range) (K := D)
  rw [hrel, hmap, Subgroup.card_map_of_injective hφ] at h
  exact h.symm

theorem e22pl2sevb_le_centralizer_of_comap_eq {Γ Λ : Type*} [Group Γ] [Group Λ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (hN : φ.range.Normal) {w : Λ} (hw : orderOf w = 2)
    (hZ : (Subgroup.center (Subgroup.centralizer ({w} : Set Λ))).map
        (Subgroup.centralizer ({w} : Set Λ)).subtype = Subgroup.zpowers w)
    {Y : Subgroup Γ} (hDY : Subgroup.centralizer ({φ w} : Set Γ) ≤ Y)
    (hM : Y.comap φ = Subgroup.centralizer ({w} : Set Λ)) :
    Y ≤ Subgroup.centralizer ({φ w} : Set Γ) := by
  classical
  set z : Γ := φ w with hzdef
  set C := Subgroup.centralizer ({w} : Set Λ) with hC
  set D := Subgroup.centralizer ({z} : Set Γ) with hD
  have hz2 : orderOf z = 2 := by rw [hzdef, orderOf_injective φ hφ w, hw]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hDC : D.comap φ = C := e22pl2sevb_comap_centralizer φ hφ w
  intro y hy
  obtain ⟨w', hw'⟩ : y * z * y⁻¹ ∈ φ.range := hN.conj_mem z ⟨w, rfl⟩ y
  have hcomm : ∀ c ∈ C, c * w' = w' * c := by
    intro c hc
    obtain ⟨c', hc'⟩ : y⁻¹ * φ c * y ∈ φ.range := by
      have := hN.conj_mem (φ c) ⟨c, rfl⟩ y⁻¹
      simpa using this
    have hcD : φ c ∈ D := by rw [← hDC] at hc; exact hc
    have hcY : y⁻¹ * φ c * y ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) (hDY hcD)) hy
    have hc'C : c' ∈ C := by
      rw [← hM]
      show φ c' ∈ Y
      rw [hc']
      exact hcY
    have h3 : φ c' * z = z * φ c' := by
      rw [hzdef, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hc'C]
    have h4 : φ c = y * φ c' * y⁻¹ := by rw [hc']; group
    have h5 : φ c * (y * z * y⁻¹) = (y * z * y⁻¹) * φ c := by
      rw [h4]
      calc y * φ c' * y⁻¹ * (y * z * y⁻¹) = y * (φ c' * z) * y⁻¹ := by group
        _ = y * (z * φ c') * y⁻¹ := by rw [h3]
        _ = (y * z * y⁻¹) * (y * φ c' * y⁻¹) := by group
    apply hφ
    rw [map_mul, map_mul, hw']
    exact h5
  have hwC : w ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hw'C : w' ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hcomm w hwC).symm
  have hw'Z : (⟨w', hw'C⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (hcomm c c.2)
  have hw'mem : w' ∈ Subgroup.zpowers w := by
    rw [← hZ]
    exact ⟨⟨w', hw'C⟩, hw'Z, rfl⟩
  have hw'ne : w' ≠ 1 := fun h => by
    rw [h, map_one] at hw'
    exact hz1 (by simpa using hw'.symm)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw'mem
  have hk2 : w ^ (k % 2) = w' := by
    have := zpow_mod_orderOf w k
    rwa [hw, hk, Nat.cast_ofNat] at this
  have hw'w : w' = w := by
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero] at hk2
      exact absurd hk2.symm hw'ne
    · rw [h, zpow_one] at hk2
      exact hk2.symm
  have hyz : y * z * y⁻¹ = z := by rw [← hw', hw'w]
  rw [hD, Subgroup.mem_centralizer_singleton_iff]
  calc y * z = (y * z * y⁻¹) * y := by group
    _ = z * y := by rw [hyz]

theorem e22pl2sevb_eq_top_of_comap_top {Γ Λ : Type*} [Group Γ] [Group Λ] (φ : Λ →* Γ)
    (hidx : φ.range.index = 2) {Y : Subgroup Γ} (hM : Y.comap φ = ⊤) {d : Γ} (hd : d ∈ Y)
    (hdR : d ∉ φ.range) : Y = ⊤ := by
  have hRY : φ.range ≤ Y := by
    rintro _ ⟨x, rfl⟩
    have : x ∈ Y.comap φ := by rw [hM]; trivial
    exact this
  rw [eq_top_iff]
  intro x _
  by_cases hx : x ∈ φ.range
  · exact hRY hx
  · have hxh : x * d⁻¹ ∈ φ.range := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false hx (fun h' => hdR (by simpa using φ.range.inv_mem h'))
    have := Y.mul_mem (hRY hxh) hd
    rwa [inv_mul_cancel_right] at this

theorem e22pl2sevb_le_normalizer_inf {Γ : Type*} [Group Γ] (Y R : Subgroup Γ) (hR : R.Normal) :
    Y ≤ Subgroup.normalizer ((Y ⊓ R : Subgroup Γ) : Set Γ) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨hY, hR'⟩
    exact ⟨Y.mul_mem (Y.mul_mem hd hY) (Y.inv_mem hd), hR.conj_mem h hR' d⟩
  · rintro ⟨hY, hR'⟩
    have h1 : h = d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [h1]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem hd) hY) (Y.inv_mem (Y.inv_mem hd))
    · rw [h1]
      exact hR.conj_mem _ hR' d⁻¹

theorem e22pl2sevb_overgroup_trichotomy {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 7) {z : CFSG.GorensteinWalter.PSL2 K} (hz : orderOf z = 2)
    {M : Subgroup (CFSG.GorensteinWalter.PSL2 K)}
    (hCM : Subgroup.centralizer ({z} : Set (CFSG.GorensteinWalter.PSL2 K)) ≤ M) :
    M = Subgroup.centralizer ({z} : Set (CFSG.GorensteinWalter.PSL2 K)) ∨ M = ⊤ ∨
      Nonempty (↥M ≃* Equiv.Perm (Fin 4)) := by
  classical
  set C := Subgroup.centralizer ({z} : Set PSL(2, K)) with hC
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK1 : Nat.card K = 7 ^ 1 := by rw [pow_one]; exact hK
  have hodd7 : Odd 7 := by decide
  have hodd : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK1 hodd7 one_pos
  obtain ⟨hcC, ⟨e⟩⟩ : Nat.card C = 8 ∧ Nonempty (C ≃* DihedralGroup 4) := by
    obtain ⟨-, h3⟩ := psl2_centralizer_involution K hK1 hodd7 one_pos hz
    obtain ⟨h, he⟩ := h3 (by norm_num)
    exact ⟨by rw [h]; norm_num, by simpa using he⟩
  have hCnc : ¬ ∀ a b : C, a * b = b * a := by
    intro hcomm
    have : IsMulCommutative (DihedralGroup 4) := ⟨⟨fun x y => e.symm.injective (by
      rw [map_mul, map_mul]; exact hcomm _ _)⟩⟩
    rcases DihedralGroup.commutative_iff.mp this with h | h <;> omega
  have hdvd : 8 ∣ Nat.card M := hcC ▸ Subgroup.card_dvd_of_le hCM
  have hpos : 0 < Nat.card M := Nat.card_pos
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK1 M with
    hEl | ⟨k, -, -, hcyc⟩ | ⟨k, hk, hMk, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, s, -, hs, N, D, hN, hNel, hNcard, -, hDcard, hdisj, hsup⟩ | ⟨m, hm, hmf, ⟨eP⟩⟩ |
      ⟨m, hm, hmf, -⟩
  ·
    exfalso
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 7 M).exists_card_eq
    rw [hk] at hdvd
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 8 7))
      hdvd
    omega
  ·
    exfalso
    refine hCnc fun (a b : C) => ?_
    have h := congrArg (fun x : M => (x : PSL(2, K)))
      (mul_comm' (⟨a, hCM a.2⟩ : M) ⟨b, hCM b.2⟩)
    exact Subtype.ext h
  ·
    left
    have hk4 : k ≤ 4 := by
      rw [hK] at hk
      norm_num at hk
      rcases hk with hk | hk
      · exact (Nat.le_of_dvd (by norm_num) hk).trans (by norm_num)
      · exact Nat.le_of_dvd (by norm_num) hk
    rw [hMk] at hdvd hpos
    have hk4' : k = 4 := by omega
    exact (Subgroup.eq_of_le_of_card_ge hCM (by rw [hMk, hcC]; omega)).symm
  ·
    exfalso
    have h12 : Nat.card M = 12 := by
      rw [Nat.card_congr eA4.toEquiv, Nat.card_eq_fintype_card]
      rfl
    omega
  ·
    exact Or.inr (Or.inr ⟨eS4⟩)
  ·
    exfalso
    have h60 : Nat.card M = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl
    omega
  ·
    exfalso
    have hcompl : N.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hMcard : Nat.card M = 7 ^ m * s := by
      rw [← hcompl.card_mul_card, hNcard, hDcard]
    rw [hMcard] at hdvd
    have hds : 8 ∣ s :=
      (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 8 7)).dvd_of_dvd_mul_left hdvd
    rw [pow_one] at hs
    norm_num at hs
    have := Nat.le_of_dvd (by norm_num) (dvd_trans hds hs)
    omega
  ·
    right
    left
    have hm1 : m = 1 := Nat.dvd_one.mp hmf
    subst hm1
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr eP.toEquiv,
      psl2_card_formula _ (isOddPrimePower_of_card (GaloisField.card 7 1 hm) hodd7 one_pos),
      GaloisField.card 7 1 hm, psl2_card_formula K hodd, hK, pow_one]
  ·
    exfalso
    have := Nat.le_of_dvd one_pos hmf
    omega

theorem pgl2_centralizer_inner_involution_isCoatom_seven
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 7) {z : CFSG.GorensteinWalter.PGL2 K} (hz : orderOf z = 2)
    (hzJ : z ∈ commutator (CFSG.GorensteinWalter.PGL2 K)) :
    IsCoatom (Subgroup.centralizer ({z} : Set (CFSG.GorensteinWalter.PGL2 K))) := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK1 : Nat.card K = 7 ^ 1 := by rw [pow_one]; exact hK
  have hodd7 : Odd 7 := by decide
  have hodd : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK1 hodd7 one_pos
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three K hodd (by omega)
  obtain ⟨w, rfl⟩ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range := hcomm ▸ hzJ
  have hφ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K)
  have hw : orderOf w = 2 := by rw [← orderOf_injective _ hφ w]; exact hz
  have hN : (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.Normal := by
    rw [← hcomm]
    infer_instance
  have hidx := pgl2_psl2Range_index_eq_two K hodd
  have hconj : ∀ x : PSL(2, K), orderOf x = 2 → IsConj x w :=
    fun x hx => psl2_isConj_of_orderOf_eq_two K hK1 hodd7 one_pos hx hw
  have hZ := psl2_center_centralizer_involution K hK1 hodd7 one_pos (by omega) hw
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set φ := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) with hφdef
  have hcC : Nat.card (Subgroup.centralizer ({w} : Set PSL(2, K))) = 8 := by
    obtain ⟨-, h3⟩ := psl2_centralizer_involution K hK1 hodd7 one_pos hw
    rw [(h3 (by norm_num)).1]
    norm_num
  have hD16 : Nat.card (Subgroup.centralizer ({φ w} : Set (PGL2 K))) = 16 := by
    rw [e22pl2sevb_card_centralizer φ hφ hN hidx hw hconj, hcC]
  refine ⟨fun htop => ?_, fun Y hDY => ?_⟩
  ·
    rw [htop, Subgroup.card_top, pgl2_card_formula K, hK] at hD16
    omega
  · have hCM : Subgroup.centralizer ({w} : Set PSL(2, K)) ≤ Y.comap φ :=
      e22pl2sevb_comap_centralizer φ hφ w ▸ Subgroup.comap_mono hDY.le
    rcases e22pl2sevb_overgroup_trichotomy hK hw hCM with hM | hM | he
    ·
      exact absurd (e22pl2sevb_le_centralizer_of_comap_eq φ hφ hN hw hZ hDY.le hM)
        (not_le_of_gt hDY)
    ·
      obtain ⟨d, hdD, hdR⟩ := e22pl2sevb_exists_mem_centralizer_not_mem_range φ hφ hN hidx hw hconj
      exact e22pl2sevb_eq_top_of_comap_top φ hidx hM (hDY.le hdD) hdR
    ·
      exfalso
      obtain ⟨e⟩ := he
      have hMeq : (Y.comap φ).map φ = Y ⊓ φ.range := by
        rw [Subgroup.map_comap_eq, inf_comm]
      have hnorm : Y ≤ Subgroup.normalizer
          (((Y.comap φ).map φ : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
        rw [hMeq]
        exact e22pl2sevb_le_normalizer_inf Y φ.range hN
      exact e22pl2sevb_false_of_perm_four
        ((Subgroup.equivMapOfInjective (Y.comap φ) φ hφ).symm.trans e)
        (hDY.le.trans hnorm)
        (fun V hV => pgl2_kleinFour_centralizer_eq_self K hodd V hV) hD16

end CFSG.Quasithin.E22L2
