module

public import CFSG.Walter.PSL2Facts.OddMaximal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.Walter.Defs

public section

namespace CFSG.Quasithin.E22L2

open scoped MatrixGroups
open CFSG.GorensteinWalter CFSG.Walter

theorem e22pd_card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem e22pd_dvd_twentyfour {a : ℕ} (ha : 16 ≤ a) (hlt : a < 24) (hd : a ∣ 24) : False := by
  obtain ⟨j, hj⟩ := hd
  rcases j with _ | _ | j
  · omega
  · omega
  · nlinarith [Nat.zero_le (a * j)]

theorem psl2_centralizer_involution_isCoatom_pm_one {p : ℕ}
    [Fact p.Prime] {K : Type} [Field K] [Finite K] (hK : Nat.card K = p)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp17 : 17 ≤ p)
    {z : CFSG.GorensteinWalter.PSL2 K} (hz : orderOf z = 2) :
    IsCoatom (Subgroup.centralizer ({z} : Set (CFSG.GorensteinWalter.PSL2 K))) := by
  classical
  set C := Subgroup.centralizer ({z} : Set PSL(2, K)) with hC
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hp2 : p ≠ 2 := by omega
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  have hodd : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK1 hpodd one_pos
  obtain ⟨n, hnlo, hnhi, hn8, hcn, ⟨e⟩⟩ : ∃ n : ℕ, (p - 1) / 2 ≤ n ∧ n ≤ (p + 1) / 2 ∧ 8 ≤ n ∧
      Nat.card C = 2 * n ∧ Nonempty (C ≃* DihedralGroup n) := by
    obtain ⟨h1, h3⟩ := psl2_centralizer_involution K hK1 hpodd one_pos hz
    rw [pow_one] at h1 h3
    have hq4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hq4 with hq4 | hq4
    · obtain ⟨hc, he⟩ := h1 hq4
      exact ⟨(p - 1) / 2, le_rfl, by omega, by omega, by rw [hc]; omega, he⟩
    · obtain ⟨hc, he⟩ := h3 hq4
      exact ⟨(p + 1) / 2, by omega, le_rfl, by omega, by rw [hc]; omega, he⟩
  have hCnc : ¬ ∀ a b : C, a * b = b * a := by
    intro hcomm
    have : IsMulCommutative (DihedralGroup n) := ⟨⟨fun x y => e.symm.injective (by
      rw [map_mul, map_mul]; exact hcomm _ _)⟩⟩
    rcases DihedralGroup.commutative_iff.mp this with h | h <;> omega
  have hcop : Nat.Coprime (2 * n) p := by
    rw [← hcn]
    obtain ⟨h1, h3⟩ := psl2_centralizer_involution K hK1 hpodd one_pos hz
    rw [pow_one] at h1 h3
    have hq4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    rcases hq4 with hq4 | hq4
    · rw [(h1 hq4).1] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · rw [(h3 hq4).1] at hdvd
      have := (Nat.dvd_add_right (dvd_refl p)).mp hdvd
      have := Nat.le_of_dvd (by omega) this
      omega
  refine ⟨?_, fun H hCH => ?_⟩
  ·
    intro htop
    have hzZ : z ∈ Subgroup.center PSL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.eq_top_iff' C).mp htop g)
    rw [psl2_center_eq_bot, Subgroup.mem_bot] at hzZ
    rw [hzZ, orderOf_one] at hz
    omega
  have hle : C ≤ H := hCH.le
  have hdvd : 2 * n ∣ Nat.card H := hcn ▸ Subgroup.card_dvd_of_le hle
  have hlt : 2 * n < Nat.card H := by
    rcases (Nat.le_of_dvd Nat.card_pos hdvd).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [hcn, h])) hCH.ne
  have hgcd : Nat.gcd (p - 1) 2 = 2 := Nat.gcd_eq_right (by omega)
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK1 H with
    hEl | ⟨k, -, -, hcyc⟩ | ⟨k, hk, hHk, -⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, s, -, hs, N, D, hN, hNel, hNcard, -, hDcard, hdisj, hsup⟩ | ⟨m, hm, hmf, ⟨eP⟩⟩ |
      ⟨m, hm, hmf, -⟩
  ·
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    rw [hk] at hdvd
    have h2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (dvd_trans (dvd_mul_right 2 n) hdvd)
    exact (hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp h2).symm).elim
  ·
    refine absurd (fun (a b : C) => ?_) hCnc
    have h := congrArg (fun x : H => (x : PSL(2, K))) (mul_comm' (⟨a, hle a.2⟩ : H) ⟨b, hle b.2⟩)
    exact Subtype.ext h
  ·
    rw [hK, hgcd] at hk
    have hkle : k ≤ (p + 1) / 2 := by
      rcases hk with hk | hk
      · exact (Nat.le_of_dvd (by omega) hk).trans (by omega)
      · exact Nat.le_of_dvd (by omega) hk
    rw [hHk] at hdvd hlt
    obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_left two_pos hdvd
    have hj2 : 2 ≤ j := by
      rcases j with _ | _ | j
      · omega
      · omega
      · omega
    have : 2 * n ≤ k := by
      calc 2 * n = n * 2 := by ring
        _ ≤ n * j := Nat.mul_le_mul_left n hj2
        _ = k := hj.symm
    omega
  ·
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr eA4.toEquiv, Nat.card_eq_fintype_card]
      rfl
    omega
  ·
    have h24 : Nat.card H = 24 := by
      rw [Nat.card_congr eS4.toEquiv]
      exact e22pd_card_perm_four
    rw [h24] at hdvd hlt
    exact (e22pd_dvd_twentyfour (by omega) hlt hdvd).elim
  ·
    let x : C := e.symm (DihedralGroup.r 1)
    have hx : orderOf x = n := by rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hy : orderOf (eA5 ⟨x, hle x.2⟩) = n := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx]
    rcases alternatingGroup_five_pow_eq_one (eA5 ⟨x, hle x.2⟩) with h | h | h <;>
    · have := Nat.le_of_dvd (by norm_num) (hy ▸ orderOf_dvd_of_pow_eq_one h)
      omega
  ·
    have hcompl : N.IsComplement' D := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    have hHcard : Nat.card H = p ^ m * s := by
      rw [← hcompl.card_mul_card, hNcard, hDcard]
    rw [hHcard] at hdvd
    have hds : 2 * n ∣ s := (Nat.Coprime.pow_right m hcop).dvd_of_dvd_mul_left hdvd
    rw [pow_one, hgcd] at hs
    have := Nat.le_of_dvd (by omega) (dvd_trans hds hs)
    omega
  ·
    have hm1 : m = 1 := Nat.dvd_one.mp hmf
    subst hm1
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr eP.toEquiv,
      psl2_card_formula _ (isOddPrimePower_of_card (GaloisField.card p 1 hm) hpodd one_pos),
      GaloisField.card p 1 hm, psl2_card_formula K hodd, hK, pow_one]
  ·
    have := Nat.le_of_dvd one_pos hmf
    omega

theorem e22pd_isCoatom_centralizer_of_index_two {Γ Λ : Type*} [Group Γ] [Group Λ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (hN : φ.range.Normal) (hidx : φ.range.index = 2)
    {w : Λ} (hw : orderOf w = 2) (hconj : ∀ x : Λ, orderOf x = 2 → IsConj x w)
    (hmax : IsCoatom (Subgroup.centralizer ({w} : Set Λ)))
    (hZ : (Subgroup.center (Subgroup.centralizer ({w} : Set Λ))).map
        (Subgroup.centralizer ({w} : Set Λ)).subtype = Subgroup.zpowers w) :
    IsCoatom (Subgroup.centralizer ({φ w} : Set Γ)) := by
  classical
  set z : Γ := φ w with hzdef
  set C := Subgroup.centralizer ({w} : Set Λ) with hC
  set D := Subgroup.centralizer ({z} : Set Γ) with hD
  have hz2 : orderOf z = 2 := by rw [hzdef, orderOf_injective φ hφ w, hw]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hDC : D.comap φ = C := by
    ext x
    rw [Subgroup.mem_comap, hD, hC, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, hzdef, ← map_mul, ← map_mul]
    exact hφ.eq_iff
  refine ⟨fun hDtop => hmax.1 (by rw [← hDC, hDtop, Subgroup.comap_top]), fun Y hDY => ?_⟩
  have hCM : C ≤ Y.comap φ := hDC ▸ Subgroup.comap_mono hDY.le
  rcases hmax.le_iff.mp hCM with hM | hM
  ·
    have hRY : φ.range ≤ Y := by
      rintro _ ⟨x, rfl⟩
      have : x ∈ Y.comap φ := by rw [hM]; trivial
      exact this
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
    have hhD : φ l * g ∈ D := by
      rw [hD, Subgroup.mem_centralizer_singleton_iff]
      calc (φ l * g) * z = ((φ l * g) * z * (φ l * g)⁻¹) * (φ l * g) := by group
        _ = z * (φ l * g) := by rw [hhz]
    have hhR : φ l * g ∉ φ.range := by
      intro hh'
      apply hg
      have : (φ l)⁻¹ * (φ l * g) ∈ φ.range :=
        φ.range.mul_mem (φ.range.inv_mem ⟨l, rfl⟩) hh'
      simpa using this
    rw [eq_top_iff]
    intro x _
    by_cases hx : x ∈ φ.range
    · exact hRY hx
    · have hxh : x * (φ l * g)⁻¹ ∈ φ.range := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx]
        exact iff_of_false hx (fun h' => hhR (by simpa using φ.range.inv_mem h'))
      have := Y.mul_mem (hRY hxh) (hDY.le hhD)
      rwa [inv_mul_cancel_right] at this
  ·
    exfalso
    refine hDY.not_ge fun y hy => ?_
    obtain ⟨w', hw'⟩ : y * z * y⁻¹ ∈ φ.range := hN.conj_mem z ⟨w, rfl⟩ y
    have hcomm : ∀ c ∈ C, c * w' = w' * c := by
      intro c hc
      obtain ⟨c', hc'⟩ : y⁻¹ * φ c * y ∈ φ.range := by
        have := hN.conj_mem (φ c) ⟨c, rfl⟩ y⁻¹
        simpa using this
      have hcD : φ c ∈ D := by rw [← hDC] at hc; exact hc
      have hcY : y⁻¹ * φ c * y ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) (hDY.le hcD)) hy
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

theorem pgl2_centralizer_inner_involution_isCoatom {p : ℕ}
    [Fact p.Prime] {K : Type} [Field K] [Finite K] (hK : Nat.card K = p)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) (hp17 : 17 ≤ p)
    {z : CFSG.GorensteinWalter.PGL2 K} (hz : orderOf z = 2)
    (hzJ : z ∈ commutator (CFSG.GorensteinWalter.PGL2 K)) :
    IsCoatom (Subgroup.centralizer ({z} : Set (CFSG.GorensteinWalter.PGL2 K))) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  have hodd : IsOddPrimePower (Nat.card K) := isOddPrimePower_of_card hK1 hpodd one_pos
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three K hodd (by omega)
  obtain ⟨w, rfl⟩ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range := hcomm ▸ hzJ
  have hφ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K)
  have hw : orderOf w = 2 := by rw [← orderOf_injective _ hφ w]; exact hz
  have hN : (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.Normal := by
    rw [← hcomm]
    infer_instance
  exact e22pd_isCoatom_centralizer_of_index_two _ hφ hN (pgl2_psl2Range_index_eq_two K hodd) hw
    (fun x hx => psl2_isConj_of_orderOf_eq_two K hK1 hpodd one_pos hx hw)
    (psl2_centralizer_involution_isCoatom_pm_one hK hp8 hp17 hw)
    (psl2_center_centralizer_involution K hK1 hpodd one_pos (by omega) hw)

theorem e22pd_isSolvable_centralizer_of_index_two {Γ Λ : Type*} [Group Γ] [Group Λ] (φ : Λ →* Γ)
    (hφ : Function.Injective φ) (hN : φ.range.Normal) (hidx : φ.range.index = 2) {w : Λ}
    (hsolv : Group.IsSolvable (Subgroup.centralizer ({w} : Set Λ))) :
    Group.IsSolvable (Subgroup.centralizer ({φ w} : Set Γ)) := by
  classical
  set C := Subgroup.centralizer ({w} : Set Λ) with hC
  set D := Subgroup.centralizer ({φ w} : Set Γ) with hD
  have hCD : ∀ x : C, φ (x : Λ) ∈ D := by
    intro x
    rw [hD, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp x.2]
  let f : C →* D := (φ.comp C.subtype).codRestrict D hCD
  have := hN
  let g : D →* Γ ⧸ φ.range := (QuotientGroup.mk' φ.range).comp D.subtype
  have hQ : Nat.card (Γ ⧸ φ.range) = 2 := hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (Γ ⧸ φ.range) := isCyclic_of_prime_card hQ
  let : CommGroup (Γ ⧸ φ.range) := IsCyclic.commGroup
  refine Group.isSolvable_of_ker_le_range f g fun d hd => ?_
  have hd' : (d : Γ) ∈ φ.range := (QuotientGroup.eq_one_iff (d : Γ)).mp (MonoidHom.mem_ker.mp hd)
  obtain ⟨x, hx⟩ := hd'
  have hxC : x ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    apply hφ
    rw [map_mul, map_mul, hx]
    exact Subgroup.mem_centralizer_singleton_iff.mp d.2
  exact ⟨⟨x, hxC⟩, Subtype.ext hx⟩

theorem pgl2_centralizer_inner_involution_isSolvable {K : Type} [Field K] [Finite K]
    (hK : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    {z : CFSG.GorensteinWalter.PGL2 K} (hz : orderOf z = 2)
    (hzJ : z ∈ commutator (CFSG.GorensteinWalter.PGL2 K)) :
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set (CFSG.GorensteinWalter.PGL2 K))) := by
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  obtain ⟨w, rfl⟩ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range := hcomm ▸ hzJ
  have hφ := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K)
  have hw : orderOf w = 2 := by rw [← orderOf_injective _ hφ w]; exact hz
  have hN : (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.Normal := by
    rw [← hcomm]
    infer_instance
  refine e22pd_isSolvable_centralizer_of_index_two _ hφ hN (pgl2_psl2Range_index_eq_two K hK) ?_
  obtain ⟨p, f, hp, hpodd, hf, hKpf⟩ := hK
  have : Fact p.Prime := ⟨hp⟩
  have h3 : 3 < p ^ f := hKpf ▸ hcard
  have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.mp hpodd.pow
  obtain ⟨h1, h3'⟩ := psl2_centralizer_involution K hKpf hpodd hf hw
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h | h
  · obtain ⟨-, ⟨e⟩⟩ := h1 h
    have : NeZero ((p ^ f - 1) / 2) := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup ((p ^ f - 1) / 2)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  · obtain ⟨-, ⟨e⟩⟩ := h3' h
    have : NeZero ((p ^ f + 1) / 2) := ⟨by omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup ((p ^ f + 1) / 2)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end CFSG.Quasithin.E22L2
