module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
import CFSG.GH74.GLS.LU.Local.SL2Sylow
import CFSG.HardMathSupport.Solomon.Proving.PSL2CommutantAffine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups
open CFSG.Blueprint (LieModel)

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (Shape)


private theorem uc22s2112r34q35_factorization_two_mul_sq_sub_one {q : ℕ} (hodd : Odd q)
    (h8 : q % 8 = 3 ∨ q % 8 = 5) : (q * (q ^ 2 - 1)).factorization 2 = 3 := by
  have hq16 : q ^ 2 % 16 = 9 := by
    have h16 : q % 16 = 3 ∨ q % 16 = 11 ∨ q % 16 = 5 ∨ q % 16 = 13 := by omega
    rcases h16 with h16 | h16 | h16 | h16 <;> rw [Nat.pow_mod, h16]
  obtain ⟨k, hk⟩ : ∃ k, q ^ 2 = 16 * k + 9 :=
    ⟨q ^ 2 / 16, by have := Nat.div_add_mod (q ^ 2) 16; omega⟩
  have hq2m1 : q ^ 2 - 1 = 8 * (2 * k + 1) := by omega
  have h8fac : (Nat.factorization 8) 2 = 3 := by
    have h8' : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8', Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hfac2 : (q ^ 2 - 1).factorization 2 = 3 := by
    rw [hq2m1, Nat.factorization_mul (by norm_num) (by omega)]
    simp only [Finsupp.add_apply]
    have hoddk : Odd (2 * k + 1) := ⟨k, rfl⟩
    have hk2 : ¬ 2 ∣ 2 * k + 1 := fun hd =>
      (Nat.not_even_iff_odd.mpr hoddk) (even_iff_two_dvd.mpr hd)
    rw [Nat.factorization_eq_zero_of_not_dvd hk2, h8fac]
  have hqfac : q.factorization 2 = 0 := by
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    intro hd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  have hqne : q ≠ 0 := by omega
  have hqne' : q ^ 2 - 1 ≠ 0 := by
    have hq3 : 3 ≤ q := by omega
    have : 1 < q ^ 2 := by nlinarith
    omega
  rw [Nat.factorization_mul hqne hqne']
  simp only [Finsupp.add_apply, hqfac, hfac2, zero_add]

private theorem uc22s2112r34q35_dvd_six_of_dvd_twentyfour_of_dvd_two_mul_odd {d m : ℕ}
    (h24 : d ∣ 24) (h2m : d ∣ 2 * m) (hm : Odd m) : d ∣ 6 := by
  obtain ⟨r, hr⟩ := hm
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos h24 (by norm_num)
  have hdle : d ≤ 24 := Nat.le_of_dvd (by norm_num) h24
  obtain ⟨k, hk⟩ := h24
  obtain ⟨l, hl⟩ := h2m
  interval_cases d <;> omega

private theorem uc22s2112r34q35_dvd_three_of_dvd_six_of_odd {d : ℕ} (h6 : d ∣ 6)
    (hodd : Odd d) : d ∣ 3 := by
  have h : d ∣ 3 * 2 := by simpa [mul_comm] using h6
  exact (Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left h

private theorem uc22s2112r34q35_scalar_of_commute_sylow {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (P : Sylow 2 SL(2, F)) (M : Matrix (Fin 2) (Fin 2) F)
    (hM : ∀ X : ↥(P : Subgroup SL(2, F)),
      M * ((X : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        ((X : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * M) :
    ∃ c : F, M = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  classical
  by_contra hμ
  push Not at hμ
  have hnc : ¬ IsMulCommutative ↥(P : Subgroup SL(2, F)) :=
    CFSG.Semidihedral.OddFieldSL2.sylow_two_not_isMulCommutative (F := F) hodd P
  have hex : ∃ A B : ↥(P : Subgroup SL(2, F)), A * B ≠ B * A := by
    by_contra h
    push Not at h
    exact hnc (isMulCommutative_iff.mpr h)
  obtain ⟨A, B, hAB⟩ := hex
  have hAB' : (A : SL(2, F)) * (B : SL(2, F)) ≠ (B : SL(2, F)) * (A : SL(2, F)) := by
    intro h
    exact hAB (Subtype.ext h)
  have hcomm := CFSG.HardMathSupport.Solomon.Proving.PSL2Even.mul_comm_of_commute_nonscalar
    M (A : Matrix (Fin 2) (Fin 2) F) (B : Matrix (Fin 2) (Fin 2) F) hμ
    (hM A).symm (hM B).symm
  exact hAB' (Subtype.ext hcomm)

theorem uc22s2112r34q35_card_normalizer_sylow_two_sl2 {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) (Q : Sylow 2 SL(2, F)) :
    Nat.card (normalizer ((Q : Subgroup SL(2, F)) : Set SL(2, F))) = 24 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card F) := by
    rw [Nat.odd_iff]
    omega
  set Psub : Subgroup SL(2, F) := (Q : Subgroup SL(2, F)) with hPsub
  have hPcard : Nat.card Psub = 8 := by
    rw [hPsub, Sylow.card_eq_multiplicity,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F,
      uc22s2112r34q35_factorization_two_mul_sq_sub_one hodd hF]
    norm_num
  obtain ⟨f, hf⟩ := CFSG.Semidihedral.OddFieldSL2.exists_quaternion_embedding_in_sylow F hodd Q
  have hbij : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card (f : QuaternionGroup 2 → ↥Psub)]
    refine ⟨hf, ?_⟩
    rw [show Nat.card (QuaternionGroup 2) = 8 by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card], hPcard]
  let φ : ↥Psub ≃* QuaternionGroup 2 := (MulEquiv.ofBijective f hbij).symm
  have hker : Nat.card ↥(Psub.normalizerMonoidHom.ker) ≤ 2 := by
    have h := CFSG.GH74.GLS.LU.Local.SL2.ker_normalizerMonoidHom_card_le hodd Q
    rwa [← hPsub] at h
  have hAut : Nat.card (MulAut ↥Psub) ≤ 24 := by
    rw [Nat.card_congr (MulAut.congr φ).toEquiv]
    exact CFSG.GH74.GLS.LU.Local.SL2.card_mulAut_q8_le
  have hrange : Nat.card ↥(Psub.normalizerMonoidHom.range) ≤ 24 :=
    (Subgroup.card_le_card_group (H := Psub.normalizerMonoidHom.range)).trans hAut
  change Nat.card (normalizer (Psub : Set SL(2, F))) = 24
  set N : Subgroup SL(2, F) := normalizer (Psub : Set SL(2, F)) with hN
  have hprod : Nat.card ↥(Psub.normalizerMonoidHom.ker) *
      Nat.card ↥(Psub.normalizerMonoidHom.range) = Nat.card N := by
    rw [hN, ← Subgroup.card_mul_index Psub.normalizerMonoidHom.ker, Subgroup.index_ker]
  have hNle : Nat.card N ≤ 48 := by
    rw [← hprod]
    exact (Nat.mul_le_mul hker hrange).trans (by norm_num)
  have h8 : 8 ∣ Nat.card N := by
    rw [hN]
    have h := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := Psub))
    rwa [hPcard] at h
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have h3 : 3 ∣ Nat.card N := by
    obtain ⟨g, hgN, hgord⟩ := CFSG.GH74.GLS.LU.Local.SL2.q8_normalizer h2 Q φ
    have h := Subgroup.orderOf_dvd_natCard N (by rwa [hN])
    rwa [hgord] at h
  have h24 : 24 ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3
  have hPN : Psub ≤ N := by
    rw [hN]
    exact Subgroup.le_normalizer
  have hrel : Psub.relIndex N ∣ Psub.index := Subgroup.relIndex_dvd_index_of_le hPN
  have hrelnd : ¬ 2 ∣ Psub.relIndex N := fun h => Q.not_dvd_index (h.trans hrel)
  obtain ⟨c, hc⟩ := h24
  have hc2 : c ≤ 2 := by
    rw [hc] at hNle
    have := Nat.card_pos (α := ↥N)
    omega
  have hcpos : 0 < c := by
    rw [hc] at hNle
    have := Nat.card_pos (α := ↥N)
    omega
  interval_cases c
  · simpa using hc
  · exfalso
    have hrel6 : Psub.relIndex N = 6 := by
      have h := Subgroup.relIndex_mul_card (H := Psub) (K := N)
      rw [inf_eq_left.mpr hPN, hc, hPcard] at h
      omega
    exact hrelnd (by rw [hrel6]; norm_num)

private theorem uc22s2112r34q35_mem_sup_or_mul_t_mem {Y : Type} [Group Y] {F₁ F₂ : Type}
    [Field F₁] [Field F₂] (S : Shape Y F₁ F₂) (y : Y) :
    y ∈ S.I₁ ⊔ S.I₂ ∨ y * S.t ∈ S.I₁ ⊔ S.I₂ := by
  have : S.I₁.Normal := S.normal₁
  have : S.I₂.Normal := S.normal₂
  have : (S.I₁ ⊔ S.I₂).Normal := Subgroup.sup_normal S.I₁ S.I₂
  have htop : y ∈ S.I₁ ⊔ S.I₂ ⊔ Subgroup.zpowers S.t := by
    rw [S.gen]
    exact Subgroup.mem_top y
  rw [Subgroup.mem_sup_of_normal_left] at htop
  obtain ⟨l, hl, k, hk, hlk⟩ := htop
  rcases CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_zpowers_of_sq S.t_sq hk with hk1 | hkt
  · left
    rw [hk1, mul_one] at hlk
    rwa [← hlk]
  · right
    rw [← hlk, hkt, mul_assoc, S.t_sq, mul_one]
    exact hl

private theorem uc22s2112r34q35_t_mem_normalizer_sup {Y : Type} [Group Y] {F₁ F₂ : Type}
    [Field F₁] [Field F₂] (S : Shape Y F₁ F₂) :
    S.t ∈ Subgroup.normalizer ((S.I₁ ⊔ S.I₂ : Subgroup Y) : Set Y) := by
  have hconj : ∀ x ∈ S.I₁ ⊔ S.I₂, S.t * x * S.t⁻¹ ∈ S.I₁ ⊔ S.I₂ := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_sup_of_commute S.comm hx
    rw [show S.t * (a * b) * S.t⁻¹ = (S.t * a * S.t⁻¹) * (S.t * b * S.t⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (S.act₁.conj_mem ha))
      (Subgroup.mem_sup_right (S.act₂.conj_mem hb))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj x
  · intro hx
    have h := hconj (S.t * x * S.t⁻¹) hx
    have e : S.t * (S.t * x * S.t⁻¹) * S.t⁻¹ = x := by
      calc S.t * (S.t * x * S.t⁻¹) * S.t⁻¹ =
          (S.t * S.t) * x * (S.t * S.t)⁻¹ := by group
        _ = x := by rw [S.t_sq]; group
    rwa [e] at h

private theorem uc22s2112r34q35_conjSLAut_eq_of_act₁ {Y : Type} [Group Y] {F₁ F₂ : Type}
    [Field F₁] [Field F₂] (S : Shape Y F₁ F₂) {w : Y} (hw : w ∈ S.I₁) :
    S.e₁ ⟨S.t * w * S.t⁻¹, S.act₁.conj_mem hw⟩ =
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.conjSLAut S.g₁ (S.e₁ ⟨w, hw⟩) := by
  obtain ⟨y, hy, hey⟩ := S.act₁ ⟨w, hw⟩
  have hy' : y = ⟨S.t * w * S.t⁻¹, S.act₁.conj_mem hw⟩ := Subtype.ext hy
  rw [hy'] at hey
  apply Subtype.ext
  rw [CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.conjSLAut_coe]
  exact hey

private theorem uc22s2112r34q35_exists_sylow_sl2 {Y : Type} [Group Y] [Finite Y]
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (S : Shape Y F₁ F₂) (Q : Sylow 2 Y) :
    ∃ P : Sylow 2 SL(2, F₁),
      (P : Subgroup SL(2, F₁)) =
        (((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁).map S.e₁.toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQtop : CFSG.ABGLocalTools.IsSylowOf 2 (Q : Subgroup Y) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [Sylow.card_eq_multiplicity, Subgroup.card_top]
  have hI : ⊤ ≤ Subgroup.normalizer (S.I₁ : Set Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr S.normal₁]
  have hQ₁ : CFSG.ABGLocalTools.IsSylowOf 2 ((Q : Subgroup Y) ⊓ S.I₁) S.I₁ :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hQtop le_top hI
  have hcard : Nat.card ↥((Q : Subgroup Y) ⊓ S.I₁) =
      2 ^ (Nat.card SL(2, F₁)).factorization 2 := by
    rw [hQ₁.card_eq, Nat.card_congr S.e₁.toEquiv]
  let H : Subgroup SL(2, F₁) :=
    (((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁).map S.e₁.toMonoidHom
  have hHcard : Nat.card ↥H = 2 ^ (Nat.card SL(2, F₁)).factorization 2 := by
    rw [Subgroup.card_map_of_injective S.e₁.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ₁.le).toEquiv, hcard]
  exact ⟨Sylow.ofCard H hHcard, Sylow.coe_ofCard H hHcard⟩

private theorem uc22s2112r34q35_mem_center_of_scalar {F : Type} [Field F]
    {E : SL(2, F)} {c : F} (hc : (E : Matrix (Fin 2) (Fin 2) F) =
      c • (1 : Matrix (Fin 2) (Fin 2) F)) :
    E ∈ Subgroup.center SL(2, F) := by
  rw [Subgroup.mem_center_iff]
  intro B
  apply Subtype.ext
  have hm : (B : Matrix (Fin 2) (Fin 2) F) * (E : Matrix (Fin 2) (Fin 2) F) =
      (E : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F) := by
    rw [hc]
    simp
  simpa only [Matrix.SpecialLinearGroup.coe_mul] using hm

private theorem uc22s2112r34q35_mem_I₁_eq_one_or_z {Y : Type} [Group Y] [Finite Y]
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (S : Shape Y F₁ F₂) (hodd : Odd (Nat.card F₁)) (Q : Sylow 2 Y) {a : Y}
    (ha : a ∈ S.I₁) (hcomm : ∀ w ∈ (Q : Subgroup Y) ⊓ S.I₁, a * w = w * a) :
    a = 1 ∨ a = S.z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := uc22s2112r34q35_exists_sylow_sl2 S Q
  have hM : ∀ X : ↥(P : Subgroup SL(2, F₁)),
      (S.e₁ ⟨a, ha⟩ : Matrix (Fin 2) (Fin 2) F₁) *
          ((X : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) =
        ((X : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
          (S.e₁ ⟨a, ha⟩ : Matrix (Fin 2) (Fin 2) F₁) := by
    intro X
    have hXmem : (X : SL(2, F₁)) ∈
        (((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁).map S.e₁.toMonoidHom := by
      rw [← hP]
      exact X.2
    obtain ⟨w, hw, hXw⟩ := hXmem
    have hwQ : ((w : Y)) ∈ (Q : Subgroup Y) ⊓ S.I₁ := Subgroup.mem_subgroupOf.mp hw
    have hcommw : (⟨a, ha⟩ : ↥S.I₁) * w = w * ⟨a, ha⟩ :=
      Subtype.ext (hcomm (w : Y) hwQ)
    have hEW : S.e₁ ⟨a, ha⟩ * S.e₁ w = S.e₁ w * S.e₁ ⟨a, ha⟩ := by
      simpa using congrArg S.e₁ hcommw
    have hmat : ((S.e₁ ⟨a, ha⟩ : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
        ((S.e₁ w : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) =
        ((S.e₁ w : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
          ((S.e₁ ⟨a, ha⟩ : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using
        congrArg (fun A : SL(2, F₁) => (A : Matrix (Fin 2) (Fin 2) F₁)) hEW
    rw [show X = S.e₁ w from hXw.symm]
    exact hmat
  obtain ⟨c, hc⟩ := uc22s2112r34q35_scalar_of_commute_sylow hodd P
    ((S.e₁ ⟨a, ha⟩ : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) hM
  have hcent : S.e₁ ⟨a, ha⟩ ∈ Subgroup.center SL(2, F₁) :=
    uc22s2112r34q35_mem_center_of_scalar hc
  rcases CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.eq_one_or_neg_one_of_mem_center hcent with h | h
  · left
    have h1 : (⟨a, ha⟩ : ↥S.I₁) = 1 := S.e₁.injective (by rw [h, map_one])
    exact congrArg Subtype.val h1
  · right
    have h1 : (⟨a, ha⟩ : ↥S.I₁) = ⟨S.z, S.z_mem₁⟩ :=
      S.e₁.injective (by rw [h, S.e₁_z])
    exact congrArg Subtype.val h1

private theorem uc22s2112r34q35_orderOf_dvd_six_of_mem_I₁ {Y : Type} [Group Y] [Finite Y]
    {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (S : Shape Y F₁ F₂) (hF : Odd (Nat.card F₁))
    (Q : Sylow 2 Y) {y u v : Y} (hy : y ∈ Subgroup.normalizer ((Q : Subgroup Y) : Set Y))
    (hoddY : Odd (orderOf y)) (hy_eq : y = u * v) (hu : u ∈ S.I₁) (hv : v ∈ S.I₂)
    (hdvd : orderOf u ∣ 2 * orderOf y) : orderOf u ∣ 6 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := uc22s2112r34q35_exists_sylow_sl2 S Q
  have huN : u ∈ Subgroup.normalizer (((Q : Subgroup Y) ⊓ S.I₁ : Subgroup Y) : Set Y) := by
    have hconj_u : ∀ w ∈ (Q : Subgroup Y) ⊓ S.I₁,
        u * w * u⁻¹ ∈ (Q : Subgroup Y) ⊓ S.I₁ := by
      intro w hw
      have hyw : y * w * y⁻¹ ∈ (Q : Subgroup Y) ⊓ S.I₁ :=
        ⟨(Subgroup.mem_normalizer_iff.mp hy w).mp hw.1,
          by simpa using S.normal₁.conj_mem w hw.2 y⟩
      have hconj : u * w * u⁻¹ = y * w * y⁻¹ := by
        have hvw : v * w = w * v := (S.comm w hw.2 v hv).symm
        calc u * w * u⁻¹ = u * (v * w * v⁻¹) * u⁻¹ := by rw [hvw]; group
          _ = (u * v) * w * (u * v)⁻¹ := by group
          _ = y * w * y⁻¹ := by rw [← hy_eq]
      rwa [hconj]
    have hconj_u_inv : ∀ w ∈ (Q : Subgroup Y) ⊓ S.I₁,
        u⁻¹ * w * u ∈ (Q : Subgroup Y) ⊓ S.I₁ := by
      intro w hw
      have hmemQ : y⁻¹ * w * y ∈ (Q : Subgroup Y) :=
        (Subgroup.mem_normalizer_iff''.mp hy w).mp hw.1
      have hmemI : y⁻¹ * w * y ∈ S.I₁ := by
        simpa using S.normal₁.conj_mem w hw.2 y⁻¹
      have hmem : y⁻¹ * w * y ∈ (Q : Subgroup Y) ⊓ S.I₁ := ⟨hmemQ, hmemI⟩
      have hvw : v * (y⁻¹ * w * y) = (y⁻¹ * w * y) * v :=
        (S.comm (y⁻¹ * w * y) hmemI v hv).symm
      have huy : u⁻¹ = v * y⁻¹ := by rw [hy_eq]; group
      have huy' : u = (v * y⁻¹)⁻¹ := by rw [← huy]; simp
      have hconj : u⁻¹ * w * u = y⁻¹ * w * y := by
        rw [huy, huy']
        calc (v * y⁻¹) * w * (v * y⁻¹)⁻¹ = v * (y⁻¹ * w * y) * v⁻¹ := by group
          _ = y⁻¹ * w * y := by rw [hvw]; group
      rwa [hconj]
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact hconj_u w
    · intro hw
      have := hconj_u_inv (u * w * u⁻¹) hw
      rwa [show u⁻¹ * (u * w * u⁻¹) * u = w by group] at this
  have huNsub : (⟨u, hu⟩ : ↥S.I₁) ∈ Subgroup.normalizer
      ((((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁ : Subgroup ↥S.I₁) : Set ↥S.I₁) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using
      (Subgroup.mem_normalizer_iff.mp huN (w : Y))
  let g : SL(2, F₁) := S.e₁ ⟨u, hu⟩
  have hgord : orderOf g = orderOf u := by
    dsimp [g]
    exact (MulEquiv.orderOf_eq S.e₁ ⟨u, hu⟩).trans (Subgroup.orderOf_coe ⟨u, hu⟩).symm
  have hmem : g ∈ Subgroup.normalizer
      ((((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁).map S.e₁.toMonoidHom :
        Set (SL(2, F₁))) := by
    change S.e₁ ⟨u, hu⟩ ∈ Subgroup.normalizer
      ((((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁).map S.e₁.toMonoidHom :
        Set (SL(2, F₁)))
    have hmap := Subgroup.map_equiv_normalizer_eq
      (((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁) S.e₁
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ huNsub
  by_cases hq3 : Nat.card F₁ % 8 = 3 ∨ Nat.card F₁ % 8 = 5
  · have h24 : orderOf u ∣ 24 := by
      have hd := Subgroup.orderOf_dvd_natCard (Subgroup.normalizer
        ((((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁).map S.e₁.toMonoidHom :
          Set (SL(2, F₁)))) hmem
      rw [← hP, uc22s2112r34q35_card_normalizer_sylow_two_sl2 hq3 P] at hd
      rwa [hgord] at hd
    exact uc22s2112r34q35_dvd_six_of_dvd_twentyfour_of_dvd_two_mul_odd h24 hdvd hoddY
  · have hq8 : Nat.card F₁ % 8 = 1 ∨ Nat.card F₁ % 8 = 7 := by
      have h2 : Nat.card F₁ % 2 = 1 := Nat.odd_iff.mp hF
      omega
    obtain ⟨n, hn3, ⟨φ⟩⟩ :=
      CFSG.Semidihedral.OddFieldSL2.sylow_two_quaternion F₁ hF P
    have hPcard : Nat.card ↥(P : Subgroup SL(2, F₁)) = 2 ^ n := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card]
      let : NeZero (2 ^ (n - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
      rw [QuaternionGroup.card]
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    have hPfac : Nat.card ↥(P : Subgroup SL(2, F₁)) =
        2 ^ (Nat.card SL(2, F₁)).factorization 2 := by
      rw [Sylow.card_eq_multiplicity]
    have hn_fac : n = (Nat.card SL(2, F₁)).factorization 2 :=
      Nat.pow_right_injective (by norm_num) (hPcard.symm.trans hPfac)
    have h16 : 16 ∣ Nat.card SL(2, F₁) := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
      have hq16 : Nat.card F₁ ^ 2 % 16 = 1 := by
        have h16cases : Nat.card F₁ % 16 = 1 ∨ Nat.card F₁ % 16 = 7 ∨
            Nat.card F₁ % 16 = 9 ∨ Nat.card F₁ % 16 = 15 := by omega
        rcases h16cases with h | h | h | h <;> norm_num [Nat.pow_mod, h]
      obtain ⟨k, hk⟩ : ∃ k, Nat.card F₁ ^ 2 = 16 * k + 1 :=
        ⟨Nat.card F₁ ^ 2 / 16,
          by have := Nat.div_add_mod (Nat.card F₁ ^ 2) 16; omega⟩
      have hdvd16 : 16 ∣ Nat.card F₁ ^ 2 - 1 := ⟨k, by omega⟩
      exact dvd_mul_of_dvd_right hdvd16 (Nat.card F₁)
    have hfac4 : 4 ≤ (Nat.card SL(2, F₁)).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (Nat.card_pos (α := SL(2, F₁))).ne').mp h16
    have hn4 : 4 ≤ n := by omega
    have hj2 : 2 ≤ n - 2 := by omega
    obtain ⟨a, b, hbodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos u).ne'
    have hdvd2a : 2 ^ a ∣ orderOf u := by
      rw [hord]; exact dvd_mul_right _ _
    let w : SL(2, F₁) := g ^ (2 ^ a)
    have horder_w : orderOf w = b := by
      dsimp [w]
      rw [orderOf_pow_of_dvd (pow_ne_zero a (by norm_num))
        (by rw [hgord, hord]; exact dvd_mul_right _ _),
        hgord, hord, Nat.mul_div_cancel_left b (pow_pos (by norm_num) a)]
    have hwodd : Odd (orderOf w) := by rw [horder_w]; exact hbodd
    have hwN : w ∈ Subgroup.normalizer
        ((P : Subgroup SL(2, F₁)) : Set (SL(2, F₁))) := by
      dsimp [w]
      change g ^ 2 ^ a ∈ Subgroup.normalizer
        (((P : Subgroup SL(2, F₁))) : Set (SL(2, F₁)))
      have hPset : ((P : Subgroup SL(2, F₁)) : Set (SL(2, F₁))) =
          (((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁).map S.e₁.toMonoidHom :=
        congrArg (fun H : Subgroup SL(2, F₁) => (H : Set (SL(2, F₁)))) hP
      rw [hPset]
      exact Subgroup.pow_mem _ hmem _
    have hαodd : Odd (orderOf (MulAut.conj w)) :=
      Odd.of_dvd_nat hwodd
        (orderOf_map_dvd (MulAut.conj : SL(2, F₁) →* MulAut (SL(2, F₁))) w)
    have hQ : ∀ x, x ∈ (P : Subgroup SL(2, F₁)) ↔
        MulAut.conj w x ∈ (P : Subgroup SL(2, F₁)) := by
      intro x
      simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hwN x)
    have hcentP := CFSG.GH74.GLS.LU.Local.SL2.aut_sylow_odd_large P hj2 φ
      (MulAut.conj w) hαodd hQ
    have hcomm : ∀ X : ↥(P : Subgroup SL(2, F₁)),
        ((w : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
            ((X : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) =
          ((X : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
            ((w : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) := by
      intro X
      have h1 : w * (X : SL(2, F₁)) = (X : SL(2, F₁)) * w := by
        have h2 := hcentP X X.2
        have h3 : w * (X : SL(2, F₁)) * w⁻¹ = X := by
          simpa [MulAut.conj_apply] using h2
        calc w * (X : SL(2, F₁)) = (w * (X : SL(2, F₁)) * w⁻¹) * w := by group
          _ = (X : SL(2, F₁)) * w := by rw [h3]
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using
        congrArg (fun A : SL(2, F₁) => (A : Matrix (Fin 2) (Fin 2) F₁)) h1
    obtain ⟨c, hc⟩ := uc22s2112r34q35_scalar_of_commute_sylow hF P
      (((w : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁)) hcomm
    have hcent := uc22s2112r34q35_mem_center_of_scalar hc
    have hg1_or := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.eq_one_or_neg_one_of_mem_center hcent
    have hw1 : w = 1 := by
      rcases hg1_or with h | h
      · exact h
      · exfalso
        have hordneg : orderOf (-1 : SL(2, F₁)) = 2 := by
          rw [show (-1 : SL(2, F₁)) =
            CFSG.Semidihedral.OddFieldSL2.minusIdentity F₁ from rfl]
          exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf F₁
            (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F₁ hF)
        rw [h, hordneg] at hwodd
        obtain ⟨k, hk⟩ := hwodd
        omega
    have hgpow : g ^ (2 ^ a) = 1 := by simpa [w] using hw1
    have hdvd_pow : orderOf u ∣ 2 ^ a := by
      have h := orderOf_dvd_of_pow_eq_one hgpow
      rwa [hgord] at h
    have hcop : Nat.Coprime (orderOf u) (orderOf y) :=
      Nat.Coprime.coprime_dvd_left hdvd_pow
        (Nat.Coprime.pow_left a (Nat.coprime_two_right.mpr hoddY).symm)
    have h2 : orderOf u ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_right hcop hdvd
    exact h2.trans (by norm_num)

section Shape

variable {Y : Type} [Group Y] [Finite Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
  [Finite F₂]

theorem uc22s2112r34q35_shape_eq_of_central (S : Shape Y F₁ F₂) (h₁ : Odd (Nat.card F₁))
    (h₂ : Odd (Nat.card F₂)) (Q : Sylow 2 Y) {c : Y}
    (hc : ∀ y ∈ (Q : Subgroup Y), c * y = y * c) : c = 1 ∨ c = S.z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup Y := S.I₁ ⊔ S.I₂
  by_cases hcL : c ∈ L
  · obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_sup_of_commute S.comm hcL
    have ha_eq : a = 1 ∨ a = S.z := by
      refine uc22s2112r34q35_mem_I₁_eq_one_or_z S h₁ Q ha ?_
      intro w hw
      have hcw : c * w = w * c := hc w hw.1
      have hbw : b * w = w * b := (S.comm w hw.2 b hb).symm
      have hconj : a * w * a⁻¹ = w := by
        calc a * w * a⁻¹ = a * (b * w * b⁻¹) * a⁻¹ := by rw [hbw]; group
          _ = (a * b) * w * (a * b)⁻¹ := by group
          _ = c * w * c⁻¹ := by rw [hab]
          _ = w := by rw [hcw]; group
      calc a * w = (a * w * a⁻¹) * a := by group
        _ = w * a := by rw [hconj]
    have hb_eq : b = 1 ∨ b = S.z := by
      have hb' : b ∈ S.swap.I₁ := hb
      have h := uc22s2112r34q35_mem_I₁_eq_one_or_z S.swap h₂ Q hb' ?_
      · simpa [Shape.swap] using h
      · intro w hw
        have hcw : c * w = w * c := hc w hw.1
        have haw : a * w = w * a := S.comm a ha w hw.2
        have hcwa : a * (b * w * b⁻¹) * a⁻¹ = w := by
          calc a * (b * w * b⁻¹) * a⁻¹ = (a * b) * w * (a * b)⁻¹ := by group
            _ = c * w * c⁻¹ := by rw [hab]
            _ = w := by rw [hcw]; group
        have hconj : b * w * b⁻¹ = w := by
          calc b * w * b⁻¹ = a⁻¹ * (a * (b * w * b⁻¹) * a⁻¹) * a := by group
            _ = a⁻¹ * w * a := by rw [hcwa]
            _ = w := by
              rw [show a⁻¹ * w * a = a⁻¹ * (w * a) by group, ← haw]
              group
        calc b * w = (b * w * b⁻¹) * b := by group
          _ = w * b := by rw [hconj]
    have hceq : c = a * b := hab.symm
    rcases ha_eq with rfl | rfl <;> rcases hb_eq with rfl | rfl
    · left; simpa using hceq
    · right; simpa using hceq
    · right; simpa using hceq
    · left; simpa [S.z_sq] using hceq
  · exfalso
    have hctL : c * S.t ∈ L := by
      rcases uc22s2112r34q35_mem_sup_or_mul_t_mem S c with h | h
      · exact absurd h hcL
      · exact h
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_sup_of_commute S.comm hctL
    have hceq : c = a * b * S.t := by
      calc c = c * (S.t * S.t) := by rw [S.t_sq, mul_one]
        _ = (c * S.t) * S.t := by group
        _ = (a * b) * S.t := by rw [hab]
    obtain ⟨P, hP⟩ := uc22s2112r34q35_exists_sylow_sl2 S Q
    have hM : ∀ X : ↥(P : Subgroup SL(2, F₁)),
        ((S.e₁ ⟨a, ha⟩ : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
            (S.g₁ : Matrix (Fin 2) (Fin 2) F₁) *
            ((X : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) =
          ((X : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
            (((S.e₁ ⟨a, ha⟩ : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
              (S.g₁ : Matrix (Fin 2) (Fin 2) F₁)) := by
      intro X
      have hXmem : (X : SL(2, F₁)) ∈
          (((Q : Subgroup Y) ⊓ S.I₁).subgroupOf S.I₁).map S.e₁.toMonoidHom := by
        rw [← hP]
        exact X.2
      obtain ⟨w, hw, hXw⟩ := hXmem
      have hwQ : ((w : Y)) ∈ (Q : Subgroup Y) ⊓ S.I₁ := Subgroup.mem_subgroupOf.mp hw
      have hcw : c * (w : Y) = (w : Y) * c := hc (w : Y) hwQ.1
      have hconj : c * (w : Y) * c⁻¹ =
          a * (S.t * (w : Y) * S.t⁻¹) * a⁻¹ := by
        rw [hceq]
        have hbw : b * (S.t * (w : Y) * S.t⁻¹) = (S.t * (w : Y) * S.t⁻¹) * b :=
          (S.comm (S.t * (w : Y) * S.t⁻¹) (S.act₁.conj_mem w.2) b hb).symm
        calc (a * b * S.t) * (w : Y) * (a * b * S.t)⁻¹ =
            a * (b * (S.t * (w : Y) * S.t⁻¹) * b⁻¹) * a⁻¹ := by group
          _ = a * (S.t * (w : Y) * S.t⁻¹) * a⁻¹ := by rw [hbw]; group
      have hfix : c * (w : Y) * c⁻¹ = (w : Y) := by rw [hcw]; group
      have hcwa : a * (S.t * (w : Y) * S.t⁻¹) * a⁻¹ = (w : Y) := by
        rw [← hconj, hfix]
      have hEW : S.e₁ w = S.e₁ ⟨a, ha⟩ *
          CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.conjSLAut S.g₁ (S.e₁ w) * (S.e₁ ⟨a, ha⟩)⁻¹ := by
        have hmem : a * (S.t * (w : Y) * S.t⁻¹) * a⁻¹ ∈ S.I₁ :=
          S.I₁.mul_mem (S.I₁.mul_mem ha (S.act₁.conj_mem w.2)) (S.I₁.inv_mem ha)
        have hsub : (⟨a * (S.t * (w : Y) * S.t⁻¹) * a⁻¹, hmem⟩ : ↥S.I₁) = w :=
          Subtype.ext hcwa
        have h1 : (⟨a * (S.t * (w : Y) * S.t⁻¹) * a⁻¹, hmem⟩ : ↥S.I₁) =
            ⟨a, ha⟩ * ⟨S.t * (w : Y) * S.t⁻¹, S.act₁.conj_mem w.2⟩ * ⟨a, ha⟩⁻¹ := by
          apply Subtype.ext
          simp
        calc S.e₁ w = S.e₁ ⟨a * (S.t * (w : Y) * S.t⁻¹) * a⁻¹, hmem⟩ := by rw [hsub]
          _ = S.e₁ ⟨a, ha⟩ * S.e₁ ⟨S.t * (w : Y) * S.t⁻¹, S.act₁.conj_mem w.2⟩ *
              (S.e₁ ⟨a, ha⟩)⁻¹ := by rw [h1, map_mul, map_mul, map_inv]
          _ = S.e₁ ⟨a, ha⟩ *
              CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.conjSLAut S.g₁ (S.e₁ w) *
              (S.e₁ ⟨a, ha⟩)⁻¹ := by
            rw [uc22s2112r34q35_conjSLAut_eq_of_act₁ S w.2]
      have h'' : Matrix.SpecialLinearGroup.toGL (S.e₁ w) =
          Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩) *
            (S.g₁ * Matrix.SpecialLinearGroup.toGL (S.e₁ w) * S.g₁⁻¹) *
            (Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩))⁻¹ := by
        have h' := congrArg Matrix.SpecialLinearGroup.toGL hEW
        simpa only [map_mul, map_inv,
          CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.toGL_conjSLAut] using h'
      have hGL : Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩) * S.g₁ *
          Matrix.SpecialLinearGroup.toGL (S.e₁ w) =
          Matrix.SpecialLinearGroup.toGL (S.e₁ w) *
            (Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩) * S.g₁) := by
        have hR : Matrix.SpecialLinearGroup.toGL (S.e₁ w) *
            (Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩) * S.g₁) =
            Matrix.SpecialLinearGroup.toGL (S.e₁ ⟨a, ha⟩) * S.g₁ *
              Matrix.SpecialLinearGroup.toGL (S.e₁ w) := by
          conv_lhs => rw [h'']
          group
        exact hR.symm
      have hMat := congrArg (fun u : GL (Fin 2) F₁ =>
        (u : Matrix (Fin 2) (Fin 2) F₁)) hGL
      rw [show X = S.e₁ w from hXw.symm]
      simpa [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hMat
    obtain ⟨μ, hμ⟩ := uc22s2112r34q35_scalar_of_commute_sylow h₁ P
      (((S.e₁ ⟨a, ha⟩ : SL(2, F₁)) : Matrix (Fin 2) (Fin 2) F₁) *
        (S.g₁ : Matrix (Fin 2) (Fin 2) F₁)) hM
    have hdetM : (Matrix.det (((S.e₁ ⟨a, ha⟩ : SL(2, F₁)) :
        Matrix (Fin 2) (Fin 2) F₁) * (S.g₁ : Matrix (Fin 2) (Fin 2) F₁)) : F₁) =
        μ * μ := by
      rw [hμ, Matrix.det_smul, Matrix.det_one, Fintype.card_fin]
      ring
    have hdetg : (Matrix.det (((S.e₁ ⟨a, ha⟩ : SL(2, F₁)) :
        Matrix (Fin 2) (Fin 2) F₁) * (S.g₁ : Matrix (Fin 2) (Fin 2) F₁)) : F₁) =
        ((S.g₁ : Matrix (Fin 2) (Fin 2) F₁)).det := by
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul]
    exact S.ns₁ ⟨μ, by
      rw [Matrix.GeneralLinearGroup.val_det_apply, ← hdetg]
      exact hdetM⟩

theorem uc22s2112r34q35_shape_orderOf_dvd_three_of_odd (S : Shape Y F₁ F₂)
    (h₁ : Odd (Nat.card F₁)) (h₂ : Odd (Nat.card F₂)) (Q : Sylow 2 Y) {y : Y}
    (hy : y ∈ normalizer ((Q : Subgroup Y) : Set Y)) (hodd : Odd (orderOf y)) :
    orderOf y ∣ 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L : Subgroup Y := S.I₁ ⊔ S.I₂
  have htN : S.t ∈ Subgroup.normalizer (L : Set Y) :=
    uc22s2112r34q35_t_mem_normalizer_sup S
  have hy2 : y * y ∈ L := by
    rcases uc22s2112r34q35_mem_sup_or_mul_t_mem S y with hyL | hytL
    · exact L.mul_mem hyL hyL
    · have hconj : S.t * (y * S.t) * S.t⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp htN (y * S.t)).mp hytL
      have htinv : S.t⁻¹ = S.t := (eq_inv_of_mul_eq_one_right S.t_sq).symm
      have hconj' : S.t * (y * S.t) * S.t ∈ L := by simpa [htinv] using hconj
      have hy_eq : y * y = (y * S.t) * (S.t * (y * S.t) * S.t) := by
        rw [show (y * S.t) * (S.t * (y * S.t) * S.t) =
            y * (S.t * S.t) * (y * (S.t * S.t)) by group, S.t_sq]
        simp
      rw [hy_eq]
      exact L.mul_mem hytL hconj'
  have hyL : y ∈ L := by
    obtain ⟨k, hk⟩ := hodd
    have hy_eq_pow : y = (y * y) ^ (k + 1) := by
      have hy_pow : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
      calc y = y ^ (2 * k + 1) * y := by rw [hy_pow, one_mul]
        _ = y ^ (2 * k + 2) := by
            conv_rhs => rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ]
        _ = (y * y) ^ (k + 1) := by
            rw [← pow_two, ← pow_mul]
            ring_nf
    rw [hy_eq_pow]
    exact L.pow_mem hy2 (k + 1)
  obtain ⟨a, ha, b, hb, hab⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_sup_of_commute S.comm hyL
  have hcomm_ab : Commute a b := S.comm a ha b hb
  have hy_pow : y ^ orderOf y = 1 := pow_orderOf_eq_one y
  have hab_pow : (a * b) ^ orderOf y = 1 := by rw [hab]; exact hy_pow
  have hpow : a ^ orderOf y * b ^ orderOf y = 1 := by
    rw [← hcomm_ab.mul_pow]
    exact hab_pow
  have ham_eq : a ^ orderOf y = (b ^ orderOf y)⁻¹ :=
    eq_inv_of_mul_eq_one_left hpow
  have hbm_eq : b ^ orderOf y = (a ^ orderOf y)⁻¹ :=
    eq_inv_of_mul_eq_one_right hpow
  have ham : a ^ orderOf y ∈ S.I₁ ⊓ S.I₂ := by
    refine ⟨S.I₁.pow_mem ha _, ?_⟩
    rw [ham_eq]
    exact S.I₂.inv_mem (S.I₂.pow_mem hb _)
  have hbm : b ^ orderOf y ∈ S.I₁ ⊓ S.I₂ := by
    refine ⟨?_, S.I₂.pow_mem hb _⟩
    rw [hbm_eq]
    exact S.I₁.inv_mem (S.I₁.pow_mem ha _)
  have ham' : a ^ orderOf y = 1 ∨ a ^ orderOf y = S.z := by
    have hmemZ : a ^ orderOf y ∈ Subgroup.zpowers S.z := by
      rw [← S.inter]
      exact ham
    exact CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_zpowers_of_sq S.z_sq hmemZ
  have hbm' : b ^ orderOf y = 1 ∨ b ^ orderOf y = S.z := by
    have hmemZ : b ^ orderOf y ∈ Subgroup.zpowers S.z := by
      rw [← S.inter]
      exact hbm
    exact CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.mem_zpowers_of_sq S.z_sq hmemZ
  have hdvd_a : orderOf a ∣ 2 * orderOf y := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have h2m : a ^ (2 * orderOf y) = (a ^ orderOf y) ^ 2 := by
      rw [show 2 * orderOf y = orderOf y * 2 by ring, pow_mul]
    rw [h2m]
    rcases ham' with h | h
    · rw [h, one_pow]
    · rw [h, pow_two, S.z_sq]
  have hdvd_b : orderOf b ∣ 2 * orderOf y := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have h2m : b ^ (2 * orderOf y) = (b ^ orderOf y) ^ 2 := by
      rw [show 2 * orderOf y = orderOf y * 2 by ring, pow_mul]
    rw [h2m]
    rcases hbm' with h | h
    · rw [h, one_pow]
    · rw [h, pow_two, S.z_sq]
  have ha6 : orderOf a ∣ 6 :=
    uc22s2112r34q35_orderOf_dvd_six_of_mem_I₁ S h₁ Q hy hodd hab.symm ha hb hdvd_a
  have hb6 : orderOf b ∣ 6 := by
    have hba : y = b * a := by rw [← hab]; exact hcomm_ab
    exact uc22s2112r34q35_orderOf_dvd_six_of_mem_I₁ S.swap h₂ Q hy hodd hba hb ha hdvd_b
  have ha6' : a ^ 6 = 1 := by
    obtain ⟨k, hk⟩ := ha6
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  have hb6' : b ^ 6 = 1 := by
    obtain ⟨k, hk⟩ := hb6
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  have hy6 : y ^ 6 = 1 := by
    rw [← hab, hcomm_ab.mul_pow, ha6', hb6', mul_one]
  exact uc22s2112r34q35_dvd_three_of_dvd_six_of_odd
    (orderOf_dvd_of_pow_eq_one hy6) hodd

end Shape

theorem uc22s2112r34q35_orderOf_dvd_three_of_shape_of_odd {X : Type} [Group X] [Finite X]
    (hsh : ∀ z : X, orderOf z = 2 → ∃ (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂)
      (_ : Finite F₁) (_ : Finite F₂) (S : Shape ↥(centralizer ({z} : Set X)) F₁ F₂),
      Odd (Nat.card F₁) ∧ Odd (Nat.card F₂) ∧ (S.z : X) = z)
    (h2 : 2 ∣ Nat.card X) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) (hodd : Odd (orderOf x)) :
    orderOf x ∣ 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPne : (P : Subgroup X) ≠ ⊥ := P.ne_bot_of_dvd_card h2
  obtain ⟨zP, hzPcenter, hzPord⟩ :
      ∃ z : ↥(P : Subgroup X), z ∈ Subgroup.center ↥(P : Subgroup X) ∧ orderOf z = 2 := by
    have hPnt : Nontrivial ↥(P : Subgroup X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hPne
    let : Nontrivial ↥(P : Subgroup X) := hPnt
    have hcenter : Nontrivial ↥(Subgroup.center ↥(P : Subgroup X)) :=
      IsPGroup.center_nontrivial P.isPGroup'
    have hcentP : IsPGroup 2 (Subgroup.center ↥(P : Subgroup X)) :=
      P.isPGroup'.to_subgroup (Subgroup.center ↥(P : Subgroup X))
    have hcard : 2 ∣ Nat.card ↥(Subgroup.center ↥(P : Subgroup X)) := by
      rcases hcentP.card_eq_or_dvd with h | h
      · exfalso
        have h1 : 1 < Nat.card ↥(Subgroup.center ↥(P : Subgroup X)) :=
          (Finite.one_lt_card_iff_nontrivial
            (α := ↥(Subgroup.center ↥(P : Subgroup X)))).mpr hcenter
        omega
      · exact h
    obtain ⟨z, hz⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(P : Subgroup X))) 2 hcard
    exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩
  let zX : X := (zP : X)
  have hzXord : orderOf zX = 2 := (Subgroup.orderOf_coe zP).trans hzPord
  obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hoddF₁, hoddF₂, hSz⟩ := hsh zX hzXord
  let : Field F₁ := hF₁
  let : Field F₂ := hF₂
  let : Finite F₁ := hFin₁
  let : Finite F₂ := hFin₂
  let C : Subgroup X := Subgroup.centralizer ({zX} : Set X)
  have hPC : (P : Subgroup X) ≤ C := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzPcenter ⟨p, hp⟩)
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup X) ⊤ := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [Sylow.card_eq_multiplicity, Subgroup.card_top]
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup X) C :=
    CFSG.ABGLocalTools.IsSylowOf.of_le hPtop hPC le_top
  obtain ⟨Q, hQ⟩ := hPsyl.exists_sylow_eq_subgroupOf
  have hxzP : x * zX * x⁻¹ ∈ (P : Subgroup X) :=
    (Subgroup.mem_normalizer_iff.mp hx zX).mp zP.2
  let cP : ↥(P : Subgroup X) := ⟨x * zX * x⁻¹, hxzP⟩
  have hcZ : cP ∈ Subgroup.center ↥(P : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro p
    apply Subtype.ext
    have hpP : (p : X) ∈ (P : Subgroup X) := p.2
    have hxp : x⁻¹ * (p : X) * x ∈ (P : Subgroup X) :=
      (Subgroup.mem_normalizer_iff''.mp hx (p : X)).mp hpP
    have hcent : (x⁻¹ * (p : X) * x) * zX = zX * (x⁻¹ * (p : X) * x) := by
      simpa using congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzPcenter ⟨x⁻¹ * (p : X) * x, hxp⟩)
    have hcP : (cP : X) = x * zX * x⁻¹ := rfl
    have hcent' : zX * (x⁻¹ * (p : X) * x) = (x⁻¹ * (p : X) * x) * zX := hcent.symm
    calc (p : X) * (cP : X) = x * ((x⁻¹ * (p : X) * x) * zX) * x⁻¹ := by
          rw [hcP]; group
      _ = x * (zX * (x⁻¹ * (p : X) * x)) * x⁻¹ := by rw [hcent']
      _ = (cP : X) * (p : X) := by rw [hcP]; group
  have hcC : x * zX * x⁻¹ ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [cP] using
      (Subgroup.mem_center_iff.mp hcZ (⟨zX, zP.2⟩ : ↥(P : Subgroup X))).symm
  let c : ↥C := ⟨x * zX * x⁻¹, hcC⟩
  have hccomm : ∀ y ∈ (Q : Subgroup ↥C), c * y = y * c := by
    intro y hy
    apply Subtype.ext
    have hyP : (y : X) ∈ (P : Subgroup X) := by
      rw [hQ, Subgroup.mem_subgroupOf] at hy
      exact hy
    simpa [c, cP] using
      (Subgroup.mem_center_iff.mp hcZ (⟨(y : X), hyP⟩ : ↥(P : Subgroup X))).symm
  have hcz : c = 1 ∨ c = S.z :=
    uc22s2112r34q35_shape_eq_of_central S hoddF₁ hoddF₂ Q hccomm
  have hcne : c ≠ 1 := by
    intro hc1
    have hord : orderOf c = 2 := by
      rw [(Subgroup.orderOf_coe c).symm]
      have h1 : orderOf (c : X) = 2 := by
        have hconj : orderOf (x * zX * x⁻¹) = orderOf zX := by
          simpa [MulAut.conj_apply] using
            (MulEquiv.orderOf_eq (MulAut.conj x) zX)
        rw [show (c : X) = x * zX * x⁻¹ from rfl, hconj, hzXord]
      exact h1
    rw [hc1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hcSz : c = S.z := by
    rcases hcz with h | h
    · exact absurd h hcne
    · exact h
  have hxz : x * zX * x⁻¹ = zX := by
    have hval := congrArg Subtype.val hcSz
    rw [show (c : X) = x * zX * x⁻¹ from rfl, hSz] at hval
    exact hval
  have hxC : x ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * zX = (x * zX * x⁻¹) * x := by group
      _ = zX * x := by rw [hxz]
  let xc : ↥C := ⟨x, hxC⟩
  have hxcN : xc ∈ Subgroup.normalizer ((Q : Subgroup ↥C) : Set ↥C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyP : (y : X) ∈ (P : Subgroup X) := by
        rw [hQ, Subgroup.mem_subgroupOf] at hy
        exact hy
      have hconjP : x * (y : X) * x⁻¹ ∈ (P : Subgroup X) :=
        (Subgroup.mem_normalizer_iff.mp hx (y : X)).mp hyP
      rw [hQ, Subgroup.mem_subgroupOf]
      simpa [xc] using hconjP
    · intro hy
      have hyP : ((xc * y * xc⁻¹ : ↥C) : X) ∈ (P : Subgroup X) := by
        rw [hQ, Subgroup.mem_subgroupOf] at hy
        exact hy
      have hxinv : x⁻¹ ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) :=
        Subgroup.inv_mem _ hx
      have hmemP : x⁻¹ * ((xc * y * xc⁻¹ : ↥C) : X) * x ∈ (P : Subgroup X) := by
        simpa using (Subgroup.mem_normalizer_iff.mp hxinv
          ((xc * y * xc⁻¹ : ↥C) : X)).mp hyP
      rw [hQ, Subgroup.mem_subgroupOf]
      have hy_eq : (y : X) = x⁻¹ * ((xc * y * xc⁻¹ : ↥C) : X) * x := by
        simp [xc]
        group
      rw [hy_eq]
      exact hmemP
  have hodd' : Odd (orderOf xc) := by
    rw [← Subgroup.orderOf_coe xc]
    exact hodd
  have hdvd := uc22s2112r34q35_shape_orderOf_dvd_three_of_odd S hoddF₁ hoddF₂ Q hxcN hodd'
  rwa [← Subgroup.orderOf_coe xc] at hdvd

section G2


theorem uc22s2112r34q35_normSylow_G2_of_odd {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : LieModel X .G2 0 p f)
    (P : Sylow 2 X) {x : X} (hx : x ∈ normalizer ((P : Subgroup X) : Set X))
    (hodd : Odd (orderOf x)) : orderOf x ∣ 3 := by
  classical
  refine uc22s2112r34q35_orderOf_dvd_three_of_shape_of_odd ?_ ?_ P hx hodd
  · intro z hz
    obtain ⟨F, hF, hFin, S, hcard, hSz⟩ :=
      CFSG.GH74.GLS.IVK.GHInv.exists_shape_G2 hp hp2 hX z hz
    refine ⟨F, F, hF, hF, hFin, hFin, S, ?_, ?_, hSz⟩
    · rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
    · rw [hcard]; exact (hp.odd_of_ne_two hp2).pow
  · obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_of_lieModel hX
    have hoddF : Odd (Nat.card F) :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.odd_card_of_model hp hp2 hcard
    have hchar : ringChar F ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hoddF
    have hz₀ : orderOf (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.z₀ F) = 2 :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.orderOf_z₀ hchar
    have hpre : orderOf (φ.symm (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.z₀ F)) = 2 := by
      rw [(φ.symm).orderOf_eq, hz₀]
    simpa [hpre] using orderOf_dvd_natCard (φ.symm (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.z₀ F))

end G2

section D4


theorem uc22s2112r34q35_normSylow_D4_of_odd {X : Type} [Group X] [Finite X] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : LieModel X .trialityD4 0 p f)
    (P : Sylow 2 X) {x : X} (hx : x ∈ normalizer ((P : Subgroup X) : Set X))
    (hodd : Odd (orderOf x)) : orderOf x ∣ 3 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  refine uc22s2112r34q35_orderOf_dvd_three_of_shape_of_odd ?_ ?_ P hx hodd
  · intro z hz
    obtain ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, hcard₁, hcard₂, hSz⟩ :=
      CFSG.GH74.GLS.IVK.GHInv.exists_shape_D4 hp hp2 hX z hz
    refine ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, S, ?_, ?_, hSz⟩
    · rw [hcard₁]; exact ((hp.odd_of_ne_two hp2).pow).pow
    · rw [hcard₂]; exact (hp.odd_of_ne_two hp2).pow
  · have hf := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.one_le_of_lieModel_D4 hX
    obtain ⟨φ⟩ := CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.exists_equiv_concrete hp2 hX
    have hD : CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.D4Data
        (GaloisField p (3 * f)) (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.sig0 p f) (p ^ f) :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.d4Data_sig0 hp2 hf
    have hord : orderOf (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.τL hD.sigma3) = 2 :=
      CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.orderOf_tauL hD.sigma3 hD.neg_one
    have hpre : orderOf (φ.symm (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.τL hD.sigma3)) = 2 := by
      rw [(φ.symm).orderOf_eq, hord]
    simpa [hpre] using
      orderOf_dvd_natCard (φ.symm (CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab.τL hD.sigma3))

end D4

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
