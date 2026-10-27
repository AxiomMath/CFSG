module

public import CFSG.Open.SignalizerFunctorDefs
import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.Walter.PSL2Facts.Even
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinearTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L264

open CFSG CFSG.GorensteinWalter CFSG.Open
open BenderSuzuki.MatrixGroups
open CFSG.Glauberman.Dickson CFSG.Glauberman.Dickson.MaxUp
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)

theorem not_two_dvd_sq_sub_one_of_even {s : ℕ} (hs : 2 ∣ s) (hs1 : 1 ≤ s) : ¬ 2 ∣ s ^ 2 - 1 := by
  obtain ⟨c, rfl⟩ := hs
  have h1 : (2 * c) ^ 2 = 4 * c ^ 2 := by ring
  have hc : 1 ≤ c := by omega
  have h2 : 1 ≤ c ^ 2 := Nat.one_le_pow _ _ hc
  rw [h1]
  generalize c ^ 2 = u at *
  omega

theorem isCoatom_of_mulEquiv_psl2_subfield {F : Type} [Field F]
    [Finite F] {f m r : ℕ} (hF : Nat.card F = 2 ^ f) (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : f = m * r) (hm2 : 2 ≤ m) {H : Subgroup (PSL2MatrixGroup F)}
    (e : H ≃* PSL2MatrixGroup (GaloisField 2 m)) : IsCoatom H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hm0 : m ≠ 0 := by omega
  have hf0 : f ≠ 0 := by rw [hf]; exact Nat.mul_ne_zero hm0 hr.ne_zero
  set s := 2 ^ m with hs
  have hs4 : 4 ≤ s := calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hseven : 2 ∣ s := dvd_pow_self 2 hm0
  have hq : 2 ^ f = s ^ r := by rw [hf, pow_mul]
  have hs2 : 16 ≤ s ^ 2 := by nlinarith
  have hodd : ¬ 2 ∣ s ^ 2 - 1 := not_two_dvd_sq_sub_one_of_even hseven (by omega)
  have hcop : Nat.Coprime (s ^ 2 - 1) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  have hcardH : Nat.card H = s * (s ^ 2 - 1) :=
    (Nat.card_congr e.toEquiv).trans (CFSG.Walter.psl2_even_card hm0)
  have hcardG : Nat.card (PSL2MatrixGroup F) = s ^ r * ((s ^ r) ^ 2 - 1) := by
    have hfe := CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 f (Nat.pos_of_ne_zero hf0) hF
    have e2 := CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv hfe (Fin 2)
    rw [Nat.card_congr e2.toEquiv, CFSG.Walter.psl2_even_card hf0, hq]
  have hNge : 60 ≤ s * (s ^ 2 - 1) := calc 60 = 4 * 15 := by norm_num
    _ ≤ s * (s ^ 2 - 1) := Nat.mul_le_mul hs4 (by omega)
  have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0] at hc
        have : 0 < 2 ^ f := by positivity
        omega
      · exact h0
    rw [hc, show 2 * c - 1 = 2 * (c - 1) + 1 by omega]
    simp
  apply coatom_of_forall
  · apply ne_top_of_card_lt
    rw [hcardH, hcardG]
    have hsq : s < s ^ r := calc s = s ^ 1 := (pow_one s).symm
      _ < s ^ r := Nat.pow_lt_pow_right (by omega) (by omega)
    have h1 : s ^ 2 - 1 < (s ^ r) ^ 2 - 1 := by
      have : s ^ 2 < (s ^ r) ^ 2 := Nat.pow_lt_pow_left hsq (by norm_num)
      omega
    exact Nat.mul_lt_mul'' hsq h1
  intro K hHK hK
  have hHKc : Nat.card H < Nat.card K := Subgroup.card_lt_of_lt hHK
  have hHKd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK.le
  have htd : s ^ 2 - 1 ∣ Nat.card K := by
    rw [hcardH] at hHKd
    exact (dvd_mul_left (s ^ 2 - 1) s).trans hHKd
  have hsd : s ∣ Nat.card K := by
    rw [hcardH] at hHKd
    exact (dvd_mul_right s (s ^ 2 - 1)).trans hHKd
  rw [hcardH] at hHKc
  obtain ⟨c2, hc2⟩ : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
  have hc21 : 1 ≤ c2 := by
    have : 0 < 2 ^ f := by positivity
    omega
  rcases dickson_psl2_subgroup_list hF K with
    ⟨m', -, hmc, hel⟩ | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz2, hz, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨h16, ⟨eS4⟩⟩ |
      ⟨h5, ⟨eA5⟩⟩ | ⟨m', t, -, -, -, htq, E, C, hE, hEel, hEcard, hCcyc, hCcard, hdisj, hsup, -⟩ |
      ⟨m', hm'f, ⟨eP⟩⟩ | ⟨m', hm'f, ⟨eG⟩⟩
  ·
    rw [hmc] at htd
    have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m' hcop) htd
    omega
  ·
    rw [hgcd, Nat.div_one, Nat.div_one] at hz
    rw [hcard] at hsd
    have h2z : 2 ∣ z := hseven.trans hsd
    rcases hz with hz | hz
    · have := h2z.trans hz
      rw [hc2] at this
      omega
    · have := h2z.trans hz
      rw [hc2] at this
      omega
  ·
    rw [hgcd, Nat.div_one, Nat.div_one] at hz
    have hKc : Nat.card K = 2 * z := by
      rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
    have hzodd : ¬ 2 ∣ z := by
      intro h2z
      rcases hz with hz | hz
      · have := h2z.trans hz
        rw [hc2] at this
        omega
      · have := h2z.trans hz
        rw [hc2] at this
        omega
    rw [hKc] at hsd
    have hcz : Nat.Coprime s z :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hzodd)
    have hs2' : s ∣ 2 := hcz.dvd_of_dvd_mul_right hsd
    have := Nat.le_of_dvd (by norm_num) hs2'
    omega
  ·
    have h12 : Nat.card K = 12 := by
      rw [Nat.card_congr eA4.toEquiv, card_alternatingFour']
    rw [h12] at hHKc
    omega
  ·
    have h24 : Nat.card K = 24 := by
      rw [Nat.card_congr eS4.toEquiv, card_permFour]
    rw [h24] at hHKc
    omega
  ·
    have h60 : Nat.card K = 60 := by
      rw [Nat.card_congr eA5.toEquiv, card_alternatingFive']
    rw [h60] at hHKc
    omega
  ·
    rw [hgcd, Nat.div_one] at htq
    have hKc : Nat.card K = 2 ^ m' * t := by
      have hcomp : E.IsComplement' C := by
        apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
        rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]
      rw [← hEcard, ← hCcard, hcomp.card_mul_card]
    rw [hKc] at htd
    have h1 : s ^ 2 - 1 ∣ t :=
      (Nat.Coprime.pow_right m' hcop).dvd_of_dvd_mul_left htd
    have h2 : 2 ^ (2 * m) - 1 ∣ 2 ^ f - 1 := by
      have : s ^ 2 = 2 ^ (2 * m) := by rw [hs, ← pow_mul, mul_comm]
      rw [← this]
      exact h1.trans htq
    have h3 := h826_exponent_dvd_of_pow_sub_one_dvd (le_refl 2) h2
    rw [hf] at h3
    have h4 : 2 ∣ r := by
      rw [show 2 * m = m * 2 by ring] at h3
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp h3
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h4).symm
  ·
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      exact hf0 (zero_dvd_iff.mp hm'f)
    have hKc : Nat.card K = 2 ^ m' * ((2 ^ m') ^ 2 - 1) :=
      (Nat.card_congr eP.toEquiv).trans (CFSG.Walter.psl2_even_card hm'0)
    rw [hKc] at htd
    have h1 : s ^ 2 - 1 ∣ (2 ^ m') ^ 2 - 1 :=
      (Nat.Coprime.pow_right m' hcop).dvd_of_dvd_mul_left htd
    have h2 : 2 ^ (2 * m) - 1 ∣ 2 ^ (2 * m') - 1 := by
      have e1 : s ^ 2 = 2 ^ (2 * m) := by rw [hs, ← pow_mul, mul_comm]
      have e2 : (2 ^ m') ^ 2 = 2 ^ (2 * m') := by rw [← pow_mul, mul_comm]
      rw [← e1, ← e2]
      exact h1
    have h3 := h826_exponent_dvd_of_pow_sub_one_dvd (le_refl 2) h2
    have hmd : m ∣ m' := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h3
    obtain ⟨j, rfl⟩ := hmd
    have hjr : j ∣ r := by
      rw [hf] at hm'f
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp hm'f
    rcases (Nat.dvd_prime hr).mp hjr with rfl | rfl
    · rw [hKc, mul_one, ← hs] at hHKc
      exact lt_irrefl _ hHKc
    · apply hK
      apply Subgroup.eq_top_of_card_eq
      rw [hKc, hcardG, ← hf, hq]
  ·
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      exact hf0 (zero_dvd_iff.mp (by simpa using hm'f))
    have hKc : Nat.card K = 2 ^ m' * ((2 ^ m') ^ 2 - 1) := by
      rw [Nat.card_congr eG.toEquiv, card_pgl2_galoisField hm'0, ← pow_mul, mul_comm m' 2]
    rw [hKc] at htd
    have h1 : s ^ 2 - 1 ∣ (2 ^ m') ^ 2 - 1 :=
      (Nat.Coprime.pow_right m' hcop).dvd_of_dvd_mul_left htd
    have h2 : 2 ^ (2 * m) - 1 ∣ 2 ^ (2 * m') - 1 := by
      have e1 : s ^ 2 = 2 ^ (2 * m) := by rw [hs, ← pow_mul, mul_comm]
      have e2 : (2 ^ m') ^ 2 = 2 ^ (2 * m') := by rw [← pow_mul, mul_comm]
      rw [← e1, ← e2]
      exact h1
    have h3 := h826_exponent_dvd_of_pow_sub_one_dvd (le_refl 2) h2
    have hmd : m ∣ m' := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h3
    obtain ⟨j, rfl⟩ := hmd
    have h2j : 2 * j ∣ r := by
      rw [hf, show 2 * (m * j) = m * (2 * j) by ring] at hm'f
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm0)).mp hm'f
    have h4 : 2 ∣ r := (dvd_mul_right 2 j).trans h2j
    exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h4).symm

theorem card_gf64 : Nat.card (GaloisField 2 6) = 2 ^ 6 :=
  GaloisField.card 2 6 (by norm_num)

theorem card_psl2_gf64 : Nat.card (PSL2 (GaloisField 2 6)) = 262080 := by
  rw [CFSG.Walter.psl2_even_card (by norm_num : (6 : ℕ) ≠ 0)]
  norm_num

theorem isCyclic_sylow_three (R : Sylow 3 (PSL2 (GaloisField 2 6))) :
    IsCyclic (R : Subgroup (PSL2 (GaloisField 2 6))) :=
  psl2_sylow_isCyclic_of_coprime_field_card (GaloisField 2 6) card_gf64
    (by rw [card_gf64]; norm_num) 3 (by norm_num) (by rw [card_gf64]; norm_num) R

theorem card_le_three_of_pow_three {P : Subgroup (PSL2 (GaloisField 2 6))}
    (hP : ∀ x ∈ P, x ^ 3 = 1) : Nat.card P ≤ 3 := by
  have hexp : Monoid.exponent P ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hP x x.2)
  have hPp : IsPGroup 3 P := IsPGroup.of_exponent_dvd_pow (n := 1) (by rwa [pow_one])
  obtain ⟨R, hR⟩ := hPp.exists_le_sylow
  have : IsCyclic (R : Subgroup (PSL2 (GaloisField 2 6))) := isCyclic_sylow_three R
  have : IsCyclic P := Subgroup.isCyclic_of_le hR
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

theorem exists_sylow_commute {t : PSL2 (GaloisField 2 6)} (ht : t ^ 3 = 1) :
    ∃ R : Subgroup (PSL2 (GaloisField 2 6)), 9 ∣ Nat.card R ∧ ∀ r ∈ R, r * t = t * r := by
  have hp : IsPGroup 3 (Subgroup.zpowers t) := IsPGroup.of_exponent_dvd_pow (n := 1) (by
    rw [IsCyclic.exponent_eq_card, Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one ht)
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  have : IsCyclic (R : Subgroup (PSL2 (GaloisField 2 6))) := isCyclic_sylow_three R
  refine ⟨R, R.pow_dvd_card_of_pow_dvd_card (n := 2) (by rw [card_psl2_gf64]; norm_num),
    fun r hr => ?_⟩
  have htR : t ∈ (R : Subgroup (PSL2 (GaloisField 2 6))) := hR (Subgroup.mem_zpowers t)
  exact congrArg Subtype.val
    ((IsCyclic.isMulCommutative (α := (R : Subgroup (PSL2 (GaloisField 2 6))))).is_comm.comm
      ⟨r, hr⟩ ⟨t, htR⟩)

theorem conj_injective_psl2 (K : Type) [Field K] [Finite K] :
    Function.Injective (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
  have hxc : x ∈ Subgroup.center (PSL2 K) := Subgroup.mem_center_iff.mpr fun y => by
    have h := DFunLike.congr_fun hx y
    rw [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rwa [psl2_center_eq_bot, Subgroup.mem_bot] at hxc

theorem card_le_three_of_le_range_pglAction {E : Subgroup (MulAut (PSL2 (GaloisField 2 6)))}
    (hE : ∀ α ∈ E, α ^ 3 = 1) (hle : E ≤ (pglAction (GaloisField 2 6)).range) :
    Nat.card E ≤ 3 := by
  have hinj := conj_injective_psl2 (GaloisField 2 6)
  have hinn : E ≤ (MulAut.conj : PSL2 (GaloisField 2 6) →* _).range := fun α hα =>
    CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_mem_inndiag_of_pow_three (hle hα) (hE α hα)
  have hPmap : (E.comap (MulAut.conj : PSL2 (GaloisField 2 6) →* _)).map MulAut.conj = E :=
    Subgroup.map_comap_eq_self hinn
  have hP3 : ∀ x ∈ E.comap (MulAut.conj : PSL2 (GaloisField 2 6) →* _), x ^ 3 = 1 :=
    fun x hx => hinj (by rw [map_pow, map_one]; exact hE _ hx)
  rw [← hPmap, Subgroup.card_map_of_injective hinj]
  exact card_le_three_of_pow_three hP3

theorem card_map_rightHom_le_three {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut (PSL2 K))} (hE : ∀ α ∈ E, α ^ 3 = 1) :
    Nat.card (E.map (SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom)) ≤
      3 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hK⟩ := FiniteField.card' K
  have := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K
    (by rw [Nat.card_eq_fintype_card, hK])).2
  have hexp : Monoid.exponent (E.map (SemidirectProduct.rightHom.comp
      (semilinearEquivAut K).symm.toMonoidHom)) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      obtain ⟨α, hα, hx⟩ := x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hx, ← map_pow, hE α hα, map_one]
      rfl
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

theorem isCoatom_and_card_fixed
    {φ : MulAut (PSL2 (GaloisField 2 6))} (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (pglAction (GaloisField 2 6)).range) :
    IsCoatom (signalizerFixedSubgroup φ) ∧ Nat.card (signalizerFixedSubgroup φ) = 60 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hφ1 : φ ≠ 1 := fun h => hφ (h ▸ Subgroup.one_mem _)
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨σ, hσ, g, hg⟩ :=
    CFSG.RankThree.PartTwo.KFacts.linear_two_prime_order_field_descent Nat.prime_three φ hord hφ
  set π := pglAction (GaloisField 2 6) g
  have hfix : signalizerFixedSubgroup φ =
      (signalizerFixedSubgroup (psl2FieldAut (GaloisField 2 6) σ)).map π.toMonoidHom := by
    ext x
    constructor
    · intro hx
      have hx' : φ x = x := hx
      rw [hg, MulAut.mul_apply, MulAut.mul_apply] at hx'
      refine ⟨π⁻¹ x, ?_, ?_⟩
      · change psl2FieldAut (GaloisField 2 6) σ (π⁻¹ x) = π⁻¹ x
        have h := congrArg (fun y => π⁻¹ y) hx'
        simpa only [MulAut.inv_apply_self] using h
      · change π (π⁻¹ x) = x
        exact MulAut.apply_inv_self _ π x
    · rintro ⟨y, hy, rfl⟩
      have hy' : psl2FieldAut (GaloisField 2 6) σ y = y := hy
      change φ (π y) = π y
      rw [hg, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hy']
  obtain ⟨e1⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut
    (by decide : Odd 3) hσ
  have hcard4 : Nat.card (fixedSubfield (GaloisField 2 6) σ) = 2 ^ 2 := by
    rw [(CFSG.RankThree.LinearTwo.card_fixedSubfield Nat.prime_two (by norm_num) card_gf64 σ).2,
      hσ]
  let eF := CFSG.ClassicalModels.finiteFieldEquivGaloisField
    (fixedSubfield (GaloisField 2 6) σ) 2 2 (by norm_num) hcard4
  let e3 : signalizerFixedSubgroup φ ≃* PSL2MatrixGroup (GaloisField 2 2) :=
    (MulEquiv.subgroupCongr hfix).trans
      ((Subgroup.equivMapOfInjective _ π.toMonoidHom π.injective).symm.trans
        (e1.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2))))
  refine ⟨isCoatom_of_mulEquiv_psl2_subfield card_gf64 Nat.prime_three (by norm_num)
    (by norm_num) le_rfl e3, ?_⟩
  rw [Nat.card_congr e3.toEquiv, CFSG.Walter.psl2_even_card (by norm_num : (2 : ℕ) ≠ 0)]
  norm_num

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L264
