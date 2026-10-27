module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL2OddSylow
import CFSG.Quasithin.Vol2.Ch3Sec3L2qFacts
import CFSG.Quasithin.Vol2.Ch11SecJDick1
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups Pointwise

private theorem uc22s2112r34_inv_sl2_conj_inv_of_commute
    {F : Type*} [Field F] {s a c : SL(2, F)}
    (ha : ∀ k : F, (a : Matrix (Fin 2) (Fin 2) F) ≠ k • (1 : Matrix (Fin 2) (Fin 2) F))
    (hsa : s * a * s⁻¹ = a⁻¹) (hca : c * a = a * c) :
    s * c * s⁻¹ = c⁻¹ := by
  have hca' : (c : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) =
      (a : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) hca
  obtain ⟨α, β, hc⟩ := CFSG.Quasithin.Vol2.Ch11.SecJ.exists_eq_of_commute ha hca'
  have hinv_eq : ∀ x : SL(2, F),
      ((x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (x : Matrix (Fin 2) (Fin 2) F).trace • (1 : Matrix (Fin 2) (Fin 2) F) -
          (x : Matrix (Fin 2) (Fin 2) F) := by
    intro x
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.trace_fin_two]
  have hs_mul : (s : Matrix (Fin 2) (Fin 2) F) *
      ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hconj : (s : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) *
      ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      ((a⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    simpa [Matrix.SpecialLinearGroup.coe_mul, mul_assoc] using
      congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) hsa
  have htrace : (c : Matrix (Fin 2) (Fin 2) F).trace =
      2 * α + β * (a : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [hc]
    simp [Matrix.trace_fin_two]
    ring
  have hleft : ((s * c * s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      α • (1 : Matrix (Fin 2) (Fin 2) F) + β • ((a⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    calc
      ((s * c * s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
          = (s : Matrix (Fin 2) (Fin 2) F) *
              (α • (1 : Matrix (Fin 2) (Fin 2) F) + β • (a : Matrix (Fin 2) (Fin 2) F)) *
              ((s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
              simp [hc, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
      _ = α • (1 : Matrix (Fin 2) (Fin 2) F) +
            β • ((a⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
              rw [mul_add, add_mul]
              simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
              rw [hs_mul, hconj]
  apply Subtype.ext
  rw [hinv_eq]
  calc
    ((s * c * s⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)
        = α • (1 : Matrix (Fin 2) (Fin 2) F) +
            β • ((a⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := hleft
    _ = α • (1 : Matrix (Fin 2) (Fin 2) F) +
          β • ((a : Matrix (Fin 2) (Fin 2) F).trace • (1 : Matrix (Fin 2) (Fin 2) F) -
            (a : Matrix (Fin 2) (Fin 2) F)) := by rw [hinv_eq]
    _ = (c : Matrix (Fin 2) (Fin 2) F).trace • (1 : Matrix (Fin 2) (Fin 2) F) -
          (c : Matrix (Fin 2) (Fin 2) F) := by
          rw [htrace, hc]
          module

private theorem uc22s2112r34_inv_exists_odd_lift
    {F : Type*} [Field F] [Finite F] {X : Type*} [Group X]
    (φ : SL(2, F) →* X) (hker : φ.ker ≤ Subgroup.center SL(2, F))
    {r : X} (hr : r ∈ φ.range) (hrodd : Odd (orderOf r)) (hr1 : r ≠ 1) :
    ∃ g : SL(2, F), φ g = r ∧ g ^ orderOf r = 1 ∧ Odd (orderOf g) ∧
      g ∉ Subgroup.center SL(2, F) := by
  classical
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hr
  let m := orderOf (φ g)
  have hrodd' : Odd m := hrodd
  have hgm_ker : g ^ m ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have hcenter_sq : ∀ z : SL(2, F), z ∈ Subgroup.center SL(2, F) → z ^ 2 = 1 := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    rw [Fintype.card_fin] at hc
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hzc, ← map_pow, hc, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hgm_sq : (g ^ m) ^ 2 = 1 := hcenter_sq _ (hker hgm_ker)
  have hg2m : g ^ (2 * m) = 1 := by
    rw [Nat.mul_comm 2 m, pow_mul]
    exact hgm_sq
  obtain ⟨k, hk⟩ := hrodd'
  have hrodd'' : Odd m := ⟨k, hk⟩
  have hk' : m + 1 = 2 * (k + 1) := by omega
  have harith : (m + 1) * m = 2 * m * (k + 1) := by
    rw [hk']
    ring
  have hpow : (g ^ (m + 1)) ^ m = 1 := by
    rw [← pow_mul, harith, pow_mul, hg2m, one_pow]
  have hφg : φ (g ^ (m + 1)) = φ g := by
    rw [map_pow, pow_succ, pow_orderOf_eq_one, one_mul]
  refine ⟨g ^ (m + 1), hφg, hpow, ?_, ?_⟩
  · exact Odd.of_dvd_nat hrodd'' (orderOf_dvd_of_pow_eq_one hpow)
  · intro hgcenter
    apply hr1
    have hg2 : (g ^ (m + 1)) ^ 2 = 1 := hcenter_sq _ hgcenter
    have hr2 : (φ g) ^ 2 = 1 := by
      rw [← hφg, ← map_pow, hg2, map_one]
    have hdvd : orderOf (φ g) ∣ 2 := orderOf_dvd_of_pow_eq_one hr2
    have hcop : Nat.Coprime (orderOf (φ g)) 2 :=
      (Nat.coprime_two_left.mpr hrodd'').symm
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

private theorem uc22s2112r34_inv_mul_eq_one_of_mem_center_sl2
    {F : Type*} [Field F] {d r : SL(2, F)} {m : ℕ}
    (hm : Odd m) (hr : r ^ m = 1) (hd : d ^ m = 1)
    (hc : d * r ∈ Subgroup.center SL(2, F)) :
    d * r = 1 := by
  have hcenter_sq : (d * r) ^ 2 = 1 := by
    obtain ⟨c, hc', hzc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
    rw [Fintype.card_fin] at hc'
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hzc, ← map_pow, hc', map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hcomm : Commute d r := by
    have h := Subgroup.mem_center_iff.mp hc r
    have h' : r * d = d * r := mul_right_cancel (by simpa [mul_assoc] using h)
    exact h'.symm
  have hpow : (d * r) ^ m = 1 := by
    rw [hcomm.mul_pow, hd, hr, mul_one]
  have hdvd : orderOf (d * r) ∣ Nat.gcd 2 m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcenter_sq) (orderOf_dvd_of_pow_eq_one hpow)
  have hgcd : Nat.gcd 2 m = 1 := (Nat.coprime_two_left.mpr hm).gcd_eq_one
  rw [hgcd] at hdvd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

theorem uc22s2112r34_exists_inv_centralizer_sl2 {X : Type} [Group X] [Finite X] {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (φ : SL(2, GaloisField p e) →* X)
    (hker : φ.ker ≤ center SL(2, GaloisField p e)) {Q R : Subgroup X}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q φ.range) (hRK : R ≤ φ.range)
    (hRQ : (R : Set X) * (Q : Set X) = (Q : Set X) * (R : Set X)) (hR1 : R ≠ ⊥)
    (hRc : Nat.Coprime (Nat.card R) (6 * p)) :
    ∃ t ∈ Q, ∀ y ∈ φ.range ⊓ centralizer (R : Set X), t * y * t⁻¹ = y⁻¹ := by
  classical
  let F := GaloisField p e
  let S := SL(2, F)
  let PSL := PSL(2, F)
  let π : S →* PSL := QuotientGroup.mk' (Subgroup.center S)
  have hπker : π.ker = Subgroup.center S := QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let K : Subgroup X := φ.range
  let H : Subgroup X := R ⊔ Q
  let H₀ : Subgroup S := H.comap φ
  let Q₀ : Subgroup S := Q.comap φ
  let Hbar : Subgroup PSL := H₀.map π
  let Qbar : Subgroup PSL := Q₀.map π
  have hQleK : Q ≤ K := hQ.le
  have hRH : R ≤ H := le_sup_left
  have hQH : Q ≤ H := le_sup_right
  have hHK : H ≤ K := sup_le hRK hQleK
  have hQ₀leH₀ : Q₀ ≤ H₀ := by
    intro x hx
    exact Subgroup.mem_comap.mpr (hQH (Subgroup.mem_comap.mp hx))
  have hQbarLeHbar : Qbar ≤ Hbar := Subgroup.map_mono hQ₀leH₀
  have hU : (H : Set X) = (R : Set X) * (Q : Set X) :=
    CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hRQ
  obtain ⟨nQ, hnQ⟩ := hQ.isPGroup.exists_card_eq
  have hR2 : Nat.Coprime (Nat.card R) 2 :=
    Nat.Coprime.of_dvd_right (show 2 ∣ 6 * p by omega) hRc
  have hRQcop : Nat.Coprime (Nat.card R) (Nat.card Q) := by
    rw [hnQ]
    rcases Nat.eq_zero_or_pos nQ with rfl | hnQpos
    · simp
    · exact (Nat.coprime_pow_right_iff hnQpos (Nat.card R) 2).mpr hR2
  have hdisj : R ⊓ Q = ⊥ := Subgroup.inf_eq_bot_of_coprime hRQcop
  have hHcard : Nat.card H = Nat.card R * Nat.card Q :=
    CFSG.Quasithin.H23P4.card_eq_mul_of_coe_eq_mul (U := H) (H := R) (K := Q) hU hdisj
  have hcenter_le_two : Nat.card (Subgroup.center S) ≤ 2 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (i := (0 : Fin 2)) (R := F)).toEquiv]
    exact card_rootsOfUnity F 2
  have hkerle2 : Nat.card φ.ker ≤ 2 :=
    (Subgroup.card_le_of_le hker).trans hcenter_le_two
  have hkerdvd : Nat.card φ.ker ∣ 2 := by
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    have h12 : Nat.card φ.ker = 1 ∨ Nat.card φ.ker = 2 := by omega
    rcases h12 with h | h
    · rw [h]; norm_num
    · rw [h]
  have hker2 : IsPGroup 2 φ.ker :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hkerdvd)
  let ψ : H₀ →* H :=
    (φ.comp H₀.subtype).codRestrict H (fun x => Subgroup.mem_comap.mp x.2)
  have hψrange : ψ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro h
    obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (hHK h.2)
    refine ⟨⟨s, Subgroup.mem_comap.mpr (by rw [hs]; exact h.2)⟩, ?_⟩
    apply Subtype.ext
    exact hs
  have hψker : ψ.ker = φ.ker.subgroupOf H₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      apply Subtype.ext
      exact hx
  have hcardψker : Nat.card ψ.ker = Nat.card φ.ker := by
    rw [hψker]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (MonoidHom.ker_le_comap φ H)).toEquiv
  have hcardH0 : Nat.card H₀ = Nat.card H * Nat.card φ.ker := by
    have h := Subgroup.card_ker_mul_card_range ψ
    have htop : Nat.card (⊤ : Subgroup H) = Nat.card H :=
      Nat.card_congr (Subgroup.topEquiv (G := H)).toEquiv
    rw [hψrange, hcardψker] at h
    calc
      Nat.card H₀ = Nat.card φ.ker * Nat.card (⊤ : Subgroup H) := h.symm
      _ = Nat.card φ.ker * Nat.card H := by rw [htop]
      _ = Nat.card H * Nat.card φ.ker := mul_comm _ _
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardHbar_dvd : Nat.card Hbar ∣ Nat.card R * Nat.card Q * 2 := by
    have hmap : Nat.card Hbar ∣ Nat.card H * Nat.card φ.ker := by
      change Nat.card (H₀.map π) ∣ Nat.card H * Nat.card φ.ker
      rw [← hcardH0]
      exact Subgroup.card_map_dvd H₀ π
    have hmul : Nat.card H * Nat.card φ.ker ∣ Nat.card H * 2 :=
      Nat.mul_dvd_mul_left (Nat.card H) hkerdvd
    simpa [hHcard, mul_assoc] using hmap.trans hmul
  obtain ⟨QK, hQK⟩ := hQ.exists_sylow_eq_subgroupOf
  have hQKmap : (QK : Subgroup φ.range).map φ.range.subtype = Q := by
    rw [hQK, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQ.le]
  let φK : S →* φ.range := φ.rangeRestrict
  have hφKker : φK.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact Subtype.ext_iff
  have hker2K : IsPGroup 2 φK.ker := hφKker ▸ hker2
  have hQKle : (QK : Subgroup φ.range) ≤ φK.range := by
    have htop : φK.range = ⊤ :=
      MonoidHom.range_eq_top.mpr (by simpa [φK] using φ.rangeRestrict_surjective)
    rw [htop]
    exact le_top
  let Q₀Syl : Sylow 2 S := QK.comapOfKerIsPGroup φK hker2K hQKle
  have hQ₀Syl_coe : (Q₀Syl : Subgroup S) = Q.comap φ := by
    change (QK.comapOfKerIsPGroup φK hker2K hQKle : Subgroup S) = Q.comap φ
    rw [Sylow.coe_comapOfKerIsPGroup]
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    constructor
    · intro hx
      have hx' : φ.range.subtype (φK x) ∈ Q := by
        rw [← hQKmap]
        exact Subgroup.mem_map_of_mem φ.range.subtype hx
      exact hx'
    · intro hx
      have hx' : φ.range.subtype (φK x) ∈ Q := hx
      rw [← hQKmap] at hx'
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
      rwa [φ.range.subtype_injective hyx] at hy
  let QbarSyl : Sylow 2 PSL := @Sylow.mapSurjective 2 S _ _ PSL _ π hπsurj hfact Q₀Syl
  have hQbarSyl_coe : (QbarSyl : Subgroup PSL) = Qbar := by
    change (Sylow.mapSurjective (f := π) hπsurj Q₀Syl : Subgroup PSL) = Qbar
    rw [Sylow.coe_mapSurjective, hQ₀Syl_coe]
  have hQbar_card : Nat.card Qbar = 2 ^ (Nat.card PSL).factorization 2 := by
    rw [← hQbarSyl_coe]
    exact Sylow.card_eq_multiplicity QbarSyl
  have hQbar_nc : ¬ IsCyclic Qbar :=
    (CFSG.RankThree.PartTwo.Sec18.not_isCyclic_sylow_l2odd189 hp2 he hQbar_card).1
  have hpR : ¬ p ∣ Nat.card R := by
    have hcop : Nat.Coprime p (Nat.card R) :=
      (Nat.Coprime.of_dvd_right (dvd_mul_left p 6) hRc).symm
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop
  have h3R : ¬ 3 ∣ Nat.card R := by
    have hcop : Nat.Coprime 3 (Nat.card R) :=
      (Nat.Coprime.of_dvd_right (by omega : 3 ∣ 6 * p) hRc).symm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop
  have hp2' : ¬ p ∣ 2 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  have hpQ : ¬ p ∣ Nat.card Q := by
    rw [hnQ]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Fact.out h))
  have h3Q : ¬ 3 ∣ Nat.card Q := by
    rw [hnQ]
    exact fun h => (by norm_num : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hpProd : ¬ p ∣ Nat.card R * Nat.card Q * 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
      · exact hpR h
      · exact hpQ h
    · exact hp2' h
  have h3Prod : ¬ 3 ∣ Nat.card R * Nat.card Q * 2 := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
      · exact h3R h
      · exact h3Q h
    · exact (by norm_num : ¬ 3 ∣ 2) h
  have hpHbar : ¬ p ∣ Nat.card Hbar := fun h => hpProd (h.trans hcardHbar_dvd)
  have h3Hbar : ¬ 3 ∣ Nat.card Hbar := fun h => h3Prod (h.trans hcardHbar_dvd)
  have hFcard : Nat.card F = p ^ e := GaloisField.card p e (by omega)
  have hDih : ∃ z : ℕ, Nat.card Hbar = 2 * z ∧
      Nonempty (Hbar ≃* DihedralGroup z) := by
    rcases CFSG.Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part
      (F := F) (p := p) (f := e) hFcard Hbar hpHbar with
      ⟨z, -, hcard, hcyc⟩ | ⟨z, -, hcard, heD⟩ | ⟨-, heA4⟩ | ⟨-, heS4⟩ | ⟨-, heA5⟩
    · exfalso
      exact hQbar_nc (@Subgroup.isCyclic_of_le PSL _ Qbar Hbar hQbarLeHbar hcyc)
    · exact ⟨z, hcard, heD⟩
    · exfalso
      apply h3Hbar
      obtain ⟨eA4⟩ := heA4
      have hcardA4 : Nat.card Hbar = 12 := by
        rw [Nat.card_congr eA4.toEquiv, nat_card_alternatingGroup,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num [Nat.factorial]
      rw [hcardA4]
      norm_num
    · exfalso
      apply h3Hbar
      obtain ⟨eS4⟩ := heS4
      have hcardS4 : Nat.card Hbar = 24 := by
        rw [Nat.card_congr eS4.toEquiv, Nat.card_perm,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num [Nat.factorial]
      rw [hcardS4]
      norm_num
    · exfalso
      apply h3Hbar
      obtain ⟨eA5⟩ := heA5
      have hcardA5 : Nat.card Hbar = 60 := by
        rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        norm_num [Nat.factorial]
      rw [hcardA5]
      norm_num
  obtain ⟨z, hcardHbar, ⟨eD⟩⟩ := hDih
  have hzpos : 0 < z := by
    rcases Nat.eq_zero_or_pos z with hz | hz
    · rw [hz, mul_zero] at hcardHbar
      exact absurd hcardHbar (Nat.card_pos (α := Hbar)).ne'
    · exact hz
  have hzne : NeZero z := ⟨hzpos.ne'⟩
  obtain ⟨⟨r, hrR⟩, hr1sub⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR1
  have hr1 : r ≠ 1 := fun h => hr1sub (Subtype.ext h)
  have h2R : ¬ 2 ∣ Nat.card R := by
    have hcop : Nat.Coprime 2 (Nat.card R) :=
      (Nat.Coprime.of_dvd_right (by omega : 2 ∣ 6 * p) hRc).symm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop
  have h2ord : ¬ 2 ∣ orderOf r := fun h =>
    h2R (h.trans (Subgroup.orderOf_dvd_natCard R hrR))
  have hrodd : Odd (orderOf r) :=
    Nat.not_even_iff_odd.mp (fun he => h2ord (even_iff_two_dvd.mp he))
  have hrange : r ∈ φ.range := hRK hrR
  obtain ⟨rt, hφrt, hrtpow, hrtodd, hrtnc⟩ :=
    uc22s2112r34_inv_exists_odd_lift φ hker hrange hrodd hr1
  have hrtH₀ : rt ∈ H₀ := by
    rw [Subgroup.mem_comap, hφrt]
    exact hRH hrR
  have hpirtHbar : π rt ∈ Hbar := Subgroup.mem_map_of_mem π hrtH₀
  have hpirtne : π rt ≠ 1 := by
    intro h
    apply hrtnc
    have hmem : rt ∈ π.ker := MonoidHom.mem_ker.mpr h
    rwa [hπker] at hmem
  have hodd_pi : Odd (orderOf (π rt)) :=
    Odd.of_dvd_nat hrtodd (orderOf_map_dvd π rt)
  let prt : Hbar := ⟨π rt, hpirtHbar⟩
  have hodd_prt : Odd (orderOf (eD prt)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hodd_pi
  let QbarH : Subgroup Hbar := Qbar.subgroupOf Hbar
  have hQbarH_nc : ¬ IsCyclic QbarH := by
    intro h
    exact hQbar_nc ((MulEquiv.isCyclic
      (Subgroup.subgroupOfEquivOfLe hQbarLeHbar)).mp h)
  have hmapQbar_nc : ¬ IsCyclic (QbarH.map eD.toMonoidHom) := by
    intro h
    exact hQbarH_nc ((MulEquiv.isCyclic (eD.subgroupMap QbarH)).mpr h)
  obtain ⟨j, hj⟩ := @CFSG.Quasithin.H13.L2q.exists_sr_mem z hzne
    (QbarH.map eD.toMonoidHom) hmapQbar_nc
  let sbarH : Hbar := eD.symm (DihedralGroup.sr j)
  have hsbarH_mem : sbarH ∈ QbarH :=
    (Subgroup.mem_map_equiv (f := eD) (K := QbarH)).mp hj
  have hrot : eD prt ∈ TauCeti.dihedralRotations z := by
    rcases h : eD prt with i | i
    · exact TauCeti.r_mem_dihedralRotations i
    · exfalso
      have h2 : orderOf (eD prt) = 2 := by
        rw [h, DihedralGroup.orderOf_sr]
      rw [h2] at hodd_prt
      exact (by decide : ¬ Odd 2) hodd_prt
  have hconj : DihedralGroup.sr j * eD prt * (DihedralGroup.sr j)⁻¹ =
      (eD prt)⁻¹ :=
    TauCeti.conj_eq_inv_of_notMem_dihedralRotations
      (TauCeti.sr_notMem_dihedralRotations j) hrot
  have hsbarH_inv : sbarH * prt * sbarH⁻¹ = prt⁻¹ := by
    apply eD.injective
    simp only [map_mul, map_inv, sbarH, MulEquiv.apply_symm_apply]
    exact hconj
  have hsbar_inv : (sbarH : PSL) * π rt * (sbarH : PSL)⁻¹ = (π rt)⁻¹ := by
    simpa using congrArg (fun x : Hbar => (x : PSL)) hsbarH_inv
  have hsbar_mem : (sbarH : PSL) ∈ Qbar := Subgroup.mem_subgroupOf.mp hsbarH_mem
  obtain ⟨st, hstQ₀, hπst⟩ := Subgroup.mem_map.mp hsbar_mem
  have hd_center : st * rt * st⁻¹ * rt ∈ Subgroup.center S := by
    have hmem : st * rt * st⁻¹ * rt ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, hπst, hsbar_inv]
      group
    rwa [hπker] at hmem
  have hd_inv : st * rt * st⁻¹ = rt⁻¹ := by
    have hd_pow : (st * rt * st⁻¹) ^ orderOf r = 1 := by
      have hconj : st * rt * st⁻¹ = (MulAut.conj st) rt := by
        simp [MulAut.conj_apply]
      rw [hconj, ← map_pow, hrtpow, map_one]
    have hprod := uc22s2112r34_inv_mul_eq_one_of_mem_center_sl2
      hrodd hrtpow hd_pow hd_center
    exact eq_inv_of_mul_eq_one_left hprod
  have hscalar : ∀ k : F, (rt : Matrix (Fin 2) (Fin 2) F) ≠
      k • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro k hk
    apply hrtnc
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hk,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  refine ⟨φ st, ?_, ?_⟩
  · exact Subgroup.mem_comap.mp hstQ₀
  · intro y hy
    rcases Subgroup.mem_inf.mp hy with ⟨hyK, hyC⟩
    obtain ⟨c, hcφ⟩ := MonoidHom.mem_range.mp hyK
    have hyr : r * y = y * r := Subgroup.mem_centralizer_iff.mp hyC r hrR
    let u : S := c * rt * c⁻¹ * rt⁻¹
    have hu_ker : u ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : φ u = y * r * y⁻¹ * r⁻¹ := by
        simp [u, hcφ, hφrt, map_mul, map_inv]
      rw [h1, ← hyr]
      group
    have hu_center : u ∈ Subgroup.center S := hker hu_ker
    have hu_sq : u ^ 2 = 1 := by
      obtain ⟨a, ha, hua⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hu_center
      rw [Fintype.card_fin] at ha
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hua, ← map_pow, ha, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have hu_comm : Commute u rt := by
      have h := Subgroup.mem_center_iff.mp hu_center rt
      exact h.symm
    have hu_pow : u ^ orderOf r = u := by
      obtain ⟨k, hk⟩ := hrodd
      rw [hk, pow_succ, pow_mul, hu_sq, one_pow, one_mul]
    have hconj_pow : (c * rt * c⁻¹) ^ orderOf r = 1 := by
      have hconj : c * rt * c⁻¹ = (MulAut.conj c) rt := by
        simp [MulAut.conj_apply]
      rw [hconj, ← map_pow, hrtpow, map_one]
    have hu_eq_one : u = 1 := by
      have h1 : (u * rt) ^ orderOf r = u := by
        rw [hu_comm.mul_pow, hu_pow, hrtpow, mul_one]
      have h2 : u * rt = c * rt * c⁻¹ := by
        simp [u]
        group
      rw [h2, hconj_pow] at h1
      exact h1.symm
    have hc_comm : c * rt = rt * c := by
      have h1 : c * rt * c⁻¹ = rt := by
        have := congrArg (fun x => x * rt) hu_eq_one
        simpa [u, mul_assoc] using this
      calc
        c * rt = (c * rt * c⁻¹) * c := by group
        _ = rt * c := by rw [h1]
    have hsc_inv : st * c * st⁻¹ = c⁻¹ :=
      uc22s2112r34_inv_sl2_conj_inv_of_commute hscalar hd_inv hc_comm
    calc
      φ st * y * (φ st)⁻¹ = φ (st * c * st⁻¹) := by
        simp [hcφ, map_mul, map_inv]
      _ = φ c⁻¹ := by rw [hsc_inv]
      _ = y⁻¹ := by simp [hcφ]

end CFSG.LocalAnalysis.UniquenessCase.UC22
