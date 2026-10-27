module

public import CFSG.LocalAnalysis.OddStandard.ONanB2D8
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.PSLTwoNine

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81H

open CFSG.RankThree.PartTwo.Sec21.FF79 Subgroup
open CFSG.OddStandard.ONanRec.B2 (CentD8 eq_of_central_d8 exists_psl2_of_centD8)

variable {X : Type} [Group X] [Finite X]

theorem exists_sylow_three_eq_zpowers {b : X} (hb : orderOf b = 3)
    (hC : Cen b = Subgroup.zpowers b) : ∃ P : Sylow 3 X, (P : Subgroup X) = Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb]
  have hbp : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num)
  obtain ⟨P, hP⟩ := hbp.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hP⟩
  have hbP : b ∈ (P : Subgroup X) := hP (Subgroup.mem_zpowers b)
  have hb1 : b ≠ 1 := by
    rintro rfl
    simp at hb
  haveI : Nontrivial (P : Subgroup X) := ⟨⟨⟨b, hbP⟩, 1, fun h => hb1 (congrArg Subtype.val h)⟩⟩
  haveI := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (P : Subgroup X))
  have hzc : ∀ p : (P : Subgroup X), p * (z : (P : Subgroup X)) = (z : (P : Subgroup X)) * p :=
    fun p => Subgroup.mem_center_iff.1 z.2 p
  set z' : X := ((z : (P : Subgroup X)) : X) with hz'
  have hz'c : ∀ p ∈ (P : Subgroup X), p * z' = z' * p := fun p hp =>
    congrArg Subtype.val (hzc ⟨p, hp⟩)
  have hz'b : z' ∈ Subgroup.zpowers b := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    exact (hz'c b hbP).symm
  have hz'1 : z' ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz'b
  have hz'3 : z' ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hb,
      pow_orderOf_eq_one, one_zpow]
  have hz'ord : orderOf z' = 3 := by
    have hd : orderOf z' ∣ 3 := orderOf_dvd_of_pow_eq_one hz'3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz'1
    · exact h
  have heq : Subgroup.zpowers z' = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz'b) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hz'ord, hb]
  have hbz : b ∈ Subgroup.zpowers z' := heq ▸ Subgroup.mem_zpowers b
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hbz
  intro p hp
  rw [← hC, Subgroup.mem_centralizer_singleton_iff, ← hm]
  exact Commute.zpow_right (hz'c p hp) m

theorem not_nine_dvd_card {b : X} (hb : orderOf b = 3) (hC : Cen b = Subgroup.zpowers b) :
    ¬ 9 ∣ Nat.card X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_sylow_three_eq_zpowers hb hC
  have h1 : Nat.card (P : Subgroup X) = 3 := by rw [hP, Nat.card_zpowers, hb]
  have h2 := P.card_eq_multiplicity
  have h3 : (Nat.card X).factorization 3 = 1 := by
    have : 3 ^ (Nat.card X).factorization 3 = 3 ^ 1 := by rw [← h2, h1]; norm_num
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this
  intro h9
  have : 3 ^ 2 ∣ Nat.card X := by norm_num; exact h9
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').1 this
  omega

theorem exists_mem_normalizer_of_lt_pGroup {p : ℕ} [Fact p.Prime] {P V : Subgroup X}
    (hP : IsPGroup p P) (hlt : V < P) : ∃ l ∈ P, l ∉ V ∧ l ∈ Subgroup.normalizer (V : Set X) := by
  set VP : Subgroup P := V.subgroupOf P with hVP
  have hne : VP < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    obtain ⟨x, hxP, hxV⟩ := SetLike.exists_of_lt hlt
    have hx : (⟨x, hxP⟩ : P) ∈ VP := h ▸ Subgroup.mem_top _
    exact hxV (Subgroup.mem_subgroupOf.mp hx)
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hlt' := Group.normalizerCondition_of_isNilpotent (G := P) VP hne
  obtain ⟨y, hyN, hyV⟩ := SetLike.exists_of_lt hlt'
  refine ⟨y, y.2, fun h => hyV (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    have hvP : v ∈ P := hlt.le hv
    have h := (Subgroup.mem_normalizer_iff.mp hyN ⟨v, hvP⟩).mp (Subgroup.mem_subgroupOf.mpr hv)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  · intro hv
    have hvP : (y : X) * v * (y : X)⁻¹ ∈ P := hlt.le hv
    have hvP' : v ∈ P := by
      have := P.mul_mem (P.inv_mem y.2) (P.mul_mem hvP y.2)
      simpa [mul_assoc] using this
    have h := (Subgroup.mem_normalizer_iff.mp hyN ⟨v, hvP'⟩).mpr
    have h2 : (y * ⟨v, hvP'⟩ * y⁻¹ : P) ∈ VP := Subgroup.mem_subgroupOf.mpr (by simpa using hv)
    exact Subgroup.mem_subgroupOf.mp (h h2)

theorem exists_sylow_two_eq_cen {t : X} (ht : orderOf t = 2) (e : Cen t ≃* DihedralGroup 4) :
    ∃ D : Sylow 2 X, (D : Subgroup X) = Cen t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 (Cen t) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]; norm_num)
  obtain ⟨D, hD⟩ := hV2.exists_le_sylow
  refine ⟨D, le_antisymm ?_ hD⟩
  by_contra hle
  have hlt : Cen t < (D : Subgroup X) := lt_of_le_of_ne hD fun h => hle (h ▸ le_rfl)
  obtain ⟨x, hxD, hxV, hxN⟩ := exists_mem_normalizer_of_lt_pGroup D.isPGroup' hlt
  have ht1 : t ≠ 1 := fun h => by simp [h] at ht
  have htV : t ∈ Cen t := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxt : x * t * x⁻¹ ∈ Cen t := (Subgroup.mem_normalizer_iff.1 hxN t).1 htV
  have hcomm : ∀ q ∈ Cen t, q * (x * t * x⁻¹) = (x * t * x⁻¹) * q := by
    intro q hq
    have hq' : x⁻¹ * q * x ∈ Cen t := by
      have := (Subgroup.mem_normalizer_iff.1 hxN (x⁻¹ * q * x)).2
        (by rw [show x * (x⁻¹ * q * x) * x⁻¹ = q by group]; exact hq)
      exact this
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hq'
    calc q * (x * t * x⁻¹) = x * ((x⁻¹ * q * x) * t) * x⁻¹ := by group
      _ = x * (t * (x⁻¹ * q * x)) * x⁻¹ := by rw [hc]
      _ = (x * t * x⁻¹) * q := by group
  have hx1 : x * t * x⁻¹ ≠ 1 := fun h => ht1 (by
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have htc : ∀ q ∈ Cen t, q * t = t * q := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.1 hq
  have heq := eq_of_central_d8 e hxt htV hcomm htc hx1 ht1
  apply hxV
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x * t = x * t * x⁻¹ * x := by group
    _ = t * x := by rw [heq]

theorem mem_commutator_of_cen_dihedral {t : X} (ht : orderOf t = 2)
    (e : Cen t ≃* DihedralGroup 4) : t ∈ commutator X := by
  have htV : t ∈ Cen t := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have ht1 : t ≠ 1 := fun h => by simp [h] at ht
  have hcen : ∀ w : DihedralGroup 4, w * e ⟨t, htV⟩ = e ⟨t, htV⟩ * w := by
    intro w
    obtain ⟨q, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 q.2)
  have het : e ⟨t, htV⟩ = DihedralGroup.r 2 := by
    rcases (CFSG.OddStandard.ONanRec.B2.d8_center_iff _).1 hcen with h1 | h2
    · exact absurd (congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))) ht1
    · exact h2
  have hd8 : (DihedralGroup.r 1 * DihedralGroup.sr 0 * (DihedralGroup.r 1)⁻¹ *
      (DihedralGroup.sr 0)⁻¹ : DihedralGroup 4) = DihedralGroup.r 2 := by decide
  have hcomm : (⟨t, htV⟩ : Cen t) = e.symm (DihedralGroup.r 1) * e.symm (DihedralGroup.sr 0) *
      (e.symm (DihedralGroup.r 1))⁻¹ * (e.symm (DihedralGroup.sr 0))⁻¹ := by
    apply e.injective
    rw [het]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hd8.symm
  have h1 : t = ((e.symm (DihedralGroup.r 1) : Cen t) : X) *
      ((e.symm (DihedralGroup.sr 0) : Cen t) : X) *
      ((e.symm (DihedralGroup.r 1) : Cen t) : X)⁻¹ *
      ((e.symm (DihedralGroup.sr 0) : Cen t) : X)⁻¹ := by
    have := congrArg Subtype.val hcomm
    simpa using this
  have hmem := commutator_mem_commutator
    (Subgroup.mem_top ((e.symm (DihedralGroup.r 1) : Cen t) : X))
    (Subgroup.mem_top ((e.symm (DihedralGroup.sr 0) : Cen t) : X))
  rw [commutatorElement_def] at hmem
  rw [h1]
  exact hmem

theorem mem_zpowers_or_mul_mem_of_mem_normalizer {b t g : X} (hb : orderOf b = 3)
    (hC : Cen b = Subgroup.zpowers b) (hinv : t * b * t⁻¹ = b⁻¹)
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers b : Set X)) :
    g ∈ Subgroup.zpowers b ∨ t * g ∈ Subgroup.zpowers b := by
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := fun h => by simp [h] at hb
  have hgb : g * b * g⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.1 hg b).1 (Subgroup.mem_zpowers b)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgb
  have hk' : b ^ (k % 3) = g * b * g⁻¹ := by
    have := zpow_mod_orderOf b k
    rw [hb] at this
    rw [← hk]
    exact_mod_cast this
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hk'
    apply hb1
    have : g * b * g⁻¹ = 1 := hk'.symm
    calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  · left
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    rw [h1, zpow_one] at hk'
    calc g * b = g * b * g⁻¹ * g := by group
      _ = b * g := by rw [← hk']
  · right
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    rw [h2] at hk'
    have hb2 : b ^ (2 : ℤ) = b⁻¹ := by
      rw [zpow_two]
      calc b * b = b⁻¹ * (b * b * b) := by group
        _ = b⁻¹ := by rw [← pow_three', hb3]; group
    rw [hb2] at hk'
    have hgbinv : g * b * g⁻¹ = b⁻¹ := hk'.symm
    have : t * g * b * (t * g)⁻¹ = b := by
      calc t * g * b * (t * g)⁻¹ = t * (g * b * g⁻¹) * t⁻¹ := by group
        _ = t * b⁻¹ * t⁻¹ := by rw [hgbinv]
        _ = (t * b * t⁻¹)⁻¹ := by group
        _ = b := by rw [hinv, inv_inv]
    calc t * g * b = t * g * b * (t * g)⁻¹ * (t * g) := by group
      _ = b * (t * g) := by rw [this]

theorem index_ne_two {b t : X} (hb : orderOf b = 3) (hC : Cen b = Subgroup.zpowers b)
    (hinv : t * b * t⁻¹ = b⁻¹) (htc : t ∈ commutator X) (N : Subgroup X) [N.Normal] :
    N.index ≠ 2 := by
  intro h2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_sylow_three_eq_zpowers hb hC
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hbN : b ∈ N := by
    have h4 : b = b ^ 2 * b ^ 2 := by
      calc b = b ^ 3 * b := by rw [hb3, one_mul]
        _ = b ^ 2 * b ^ 2 := by group
    rw [h4]
    exact Subgroup.mul_self_mem_of_index_two h2 _
  have hcN : commutator X ≤ N := by
    refine Subgroup.commutator_le.2 fun g _ h _ => ?_
    rw [commutatorElement_def]
    have e1 : g * h ∈ N ↔ g⁻¹ * h⁻¹ ∈ N := by
      rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.mul_mem_iff_of_index_two h2,
        Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
    have := (Subgroup.mul_mem_iff_of_index_two h2 (a := g * h) (b := g⁻¹ * h⁻¹)).2 e1
    simpa [mul_assoc] using this
  have htN : t ∈ N := hcN htc
  have hPN : (P : Subgroup X) ≤ N := by
    rw [hP]
    exact Subgroup.zpowers_le.2 hbN
  have hF := Sylow.normalizer_sup_eq_top' P hPN
  have hNorm : Subgroup.normalizer (P : Set X) ≤ N := by
    intro g hg
    have hg' : g ∈ Subgroup.normalizer (Subgroup.zpowers b : Set X) := by
      rw [← hP]
      exact hg
    have hzN : Subgroup.zpowers b ≤ N := Subgroup.zpowers_le.2 hbN
    rcases mem_zpowers_or_mul_mem_of_mem_normalizer hb hC hinv hg' with h | h
    · exact hzN h
    · have := N.mul_mem (N.inv_mem htN) (hzN h)
      simpa using this
  have htop : N = ⊤ := by
    rw [eq_top_iff, ← hF]
    exact sup_le hNorm le_rfl
  rw [htop, Subgroup.index_top] at h2
  omega

theorem isConj_of_no_index_two {D : Sylow 2 X} (e : (D : Subgroup X) ≃* DihedralGroup 4)
    (hno : ∀ N : Subgroup X, N.Normal → N.index ≠ 2) {u v : X} (hu : orderOf u = 2)
    (hv : orderOf v = 2) : IsConj u v := by
  by_contra h
  obtain ⟨N, hN, hi⟩ :=
    CFSG.GorensteinWalter.TwoClassFusion.exists_normal_index_two_of_not_isConj D (m := 2)
      (by norm_num) e hu hv h
  exact hno N hN hi

theorem map_cen_conj (c u : X) :
    (Cen u).map (MulAut.conj c).toMonoidHom = Cen (c * u * c⁻¹) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    calc c * x * c⁻¹ * (c * u * c⁻¹) = c * (x * u) * c⁻¹ := by group
      _ = c * (u * x) * c⁻¹ := by rw [hx]
      _ = c * u * c⁻¹ * (c * x * c⁻¹) := by group
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, by group⟩
    calc c⁻¹ * y * c * u = c⁻¹ * (y * (c * u * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * u * c⁻¹) * y) * c := by rw [hy]
      _ = u * (c⁻¹ * y * c) := by group

theorem nonempty_cen_equiv_of_isConj {u v : X} (h : IsConj u v) : Nonempty (Cen u ≃* Cen v) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  subst hc
  exact ⟨(MulEquiv.subgroupMap (MulAut.conj c) (Cen u)).trans
    (MulEquiv.subgroupCongr (map_cen_conj c u))⟩

theorem centD8_of_isConj {t : X} (e : Cen t ≃* DihedralGroup 4)
    (hconj : ∀ u : X, orderOf u = 2 → IsConj t u) : CentD8 X := by
  intro u hu
  obtain ⟨φ⟩ := nonempty_cen_equiv_of_isConj (hconj u hu)
  exact ⟨φ.symm.trans e⟩

section Certificates


theorem exists_psl2_seven {b t : X} (hb : orderOf b = 3) (hC : Cen b = Subgroup.zpowers b)
    (ht : orderOf t = 2) (hinv : t * b * t⁻¹ = b⁻¹) (e : Cen t ≃* DihedralGroup 4) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 7 ∧
      Nonempty (X ≃* CFSG.GorensteinWalter.PSL2 K) := by
  obtain ⟨D, hD⟩ := exists_sylow_two_eq_cen ht e
  let eD : (D : Subgroup X) ≃* DihedralGroup 4 := (MulEquiv.subgroupCongr hD).trans e
  have hno : ∀ N : Subgroup X, N.Normal → N.index ≠ 2 := fun N hN =>
    haveI := hN
    index_ne_two hb hC hinv (mem_commutator_of_cen_dihedral ht e) N
  have hconj : ∀ u : X, orderOf u = 2 → IsConj t u := fun u hu =>
    isConj_of_no_index_two eD hno ht hu
  obtain ⟨K, hF, hfin, hK, ⟨eX⟩⟩ := exists_psl2_of_centD8 (centD8_of_isConj e hconj) ⟨t, ht⟩
  refine ⟨K, hF, hfin, ?_, ⟨eX⟩⟩
  rcases hK with h7 | h9
  · exact h7
  · exfalso
    have hcard : Nat.card X = 360 := by
      rw [Nat.card_congr eX.toEquiv]
      exact CFSG.LocalAnalysis.EvenBN.Tits.card_psl2_nine h9
    exact not_nine_dvd_card hb hC (hcard ▸ by norm_num)

theorem nonempty_equiv_gl_three_two {b t : X} (hb : orderOf b = 3)
    (hC : Cen b = Subgroup.zpowers b) (ht : orderOf t = 2) (hinv : t * b * t⁻¹ = b⁻¹)
    (e : Cen t ≃* DihedralGroup 4) :
    Nonempty (X ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨K, hF, hfin, h7, ⟨eX⟩⟩ := exists_psl2_seven hb hC ht hinv e
  haveI : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = 7 := by rw [Fintype.card_eq_nat_card, h7]
  let eK : ZMod 7 ≃+* K := ZMod.ringEquivOfPrime K (by norm_num) hK
  let e7 : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    eX.trans (CFSG.GorensteinWalter.psl2RingEquiv eK).symm
  obtain ⟨g⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨e7.trans g.symm⟩

end Certificates

end CFSG.RankThree.PartTwo.Sec21.FF81H
