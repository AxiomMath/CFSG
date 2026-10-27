module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCentralizer
public import CFSG.RankThree.GF2n.Stroth80.Sec11A2Line
public import CFSG.RankThree.GF2n.Stroth80.Sec78ConjFrame
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem card_PSL2GF_two_pow (x : ℕ) (hx : 1 ≤ x) :
    Nat.card (CFSG.AGLEmbedding.PSL2GF 2 x) = 2 ^ x * ((2 ^ x) ^ 2 - 1) := by
  have hK : Nat.card (GaloisField 2 x) = 2 ^ x := GaloisField.card 2 x (by omega)
  have hgcd : Nat.gcd 2 (2 ^ x - 1) = 1 := by
    have heven : Even (2 ^ x) := by
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ x := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero x two_ne_zero)
    exact Nat.coprime_two_left.mpr (Nat.Even.sub_odd h1 heven odd_one)
  simp only [CFSG.AGLEmbedding.PSL2GF]
  rw [Nat.card_congr
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField 2 x)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := GaloisField 2 x)
      (n := 2) (by norm_num), hK, hgcd, Nat.div_one]
  norm_num

theorem card_dvd_of_isPGroup_subgroup_GL_two {K : Type} [Field K] [Finite K] {x : ℕ}
    (hx : 1 ≤ x) (hq : Nat.card K = 2 ^ x) (A : Subgroup (GL (Fin 2) K))
    (hA : IsPGroup 2 ↥A) : Nat.card ↥A ∣ Nat.card K := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hdvd : Nat.card ↥A ∣ Nat.card (GL (Fin 2) K) := Subgroup.card_subgroup_dvd_card A
  have hcardGL : Nat.card (GL (Fin 2) K) =
      (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
    have h := Matrix.card_GL_field (𝔽 := K) (n := 2)
    rw [Fin.prod_univ_two] at h
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
    rw [← Nat.card_eq_fintype_card] at h
    exact h
  have hodd1 : Odd (Nat.card K - 1) := by
    rw [hq]
    have heven : Even (2 ^ x) := by
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ x := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero x two_ne_zero)
    exact Nat.Even.sub_odd h1 heven odd_one
  have hodd2 : Odd (Nat.card K ^ 2 - 1) := by
    rw [hq]
    have heven : Even ((2 ^ x) ^ 2) := by
      rw [even_iff_two_dvd]
      exact (dvd_pow_self 2 (by omega : x ≠ 0)).trans (dvd_pow_self (2 ^ x) two_ne_zero)
    have h1 : 1 ≤ (2 ^ x) ^ 2 :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (pow_ne_zero x two_ne_zero))
    exact Nat.Even.sub_odd h1 heven odd_one
  have hcop1 : Nat.Coprime (2 ^ k) (Nat.card K ^ 2 - 1) :=
    (Nat.coprime_two_left.mpr hodd2).pow_left k
  have hcop2 : Nat.Coprime (2 ^ k) (Nat.card K - 1) :=
    (Nat.coprime_two_left.mpr hodd1).pow_left k
  rw [hk] at hdvd ⊢
  have hstep : 2 ^ k ∣ Nat.card K * (Nat.card K - 1) := by
    refine (hcop1.dvd_mul_left).mp ?_
    have h := hdvd
    rw [hcardGL] at h
    rwa [show Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) by
      rw [Nat.mul_sub_one, sq]] at h
  exact (hcop2.dvd_mul_right).mp hstep

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem nonempty_xbar_mulEquiv_psl2GF {x : ℕ}
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    Nonempty (Xbar M Q Z B ≃* CFSG.AGLEmbedding.PSL2GF 2 x) := by
  have hStated := hLm2.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags])
  simp only [CFSG.Open.StatedClassicalModel] at hStated
  obtain ⟨-, K, hKf, hKfin, hKcard, he⟩ := hStated
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨eK⟩ := he
  have hx0 : x ≠ 0 := by
    have h1 : 1 ≤ x := (hLm2.admissible).2.1
    omega
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (GaloisField 2 x) := Fintype.ofFinite _
  have hcard : Nat.card K = Nat.card (GaloisField 2 x) := by
    rw [hKcard, GaloisField.card 2 x hx0]
  have hcardF : Fintype.card K = Fintype.card (GaloisField 2 x) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  let iso : K ≃+* GaloisField 2 x := FiniteField.ringEquivOfCardEq hcardF
  have hquot : XbarMod M Q Z B ≃* Xbar M Q Z B :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact ⟨hquot.symm.trans (eK.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.GorensteinWalter.psl2RingEquiv iso)))⟩

theorem Xbar_ne_bot_of_lieModel (hc : Ctx M Q Z B) {x : ℕ} (hx : 1 ≤ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    Xbar M Q Z B ≠ ⊥ := by
  obtain ⟨e⟩ := nonempty_xbar_mulEquiv_psl2GF hLm2 hcenter
  have hcard : Nat.card (Xbar M Q Z B) = 2 ^ x * ((2 ^ x) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_PSL2GF_two_pow x hx]
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have h2 : 2 ≤ 2 ^ x := by
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hx
  have h3 : 3 ≤ (2 ^ x) ^ 2 - 1 := by
    have h4 : 4 ≤ (2 ^ x) ^ 2 := by
      have h5 : 2 * 2 ≤ 2 ^ x * 2 ^ x := Nat.mul_le_mul h2 h2
      simpa [pow_two] using h5
    omega
  have hgt : 1 < 2 ^ x * ((2 ^ x) ^ 2 - 1) := by
    calc 1 < 2 * 3 := by norm_num
      _ ≤ 2 ^ x * ((2 ^ x) ^ 2 - 1) := Nat.mul_le_mul h2 h3
  omega

theorem exists_isA2_of_lieModel (hc : Ctx M Q Z B) {x : ℕ} (hx : 1 ≤ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    ∃ a ∈ LB M Q B, IsA2 Q Z a := by
  classical
  have hXne := Xbar_ne_bot_of_lieModel hc hx hLm2 hcenter
  have hE : (Ebar M Q Z B).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hXne (by rw [Xbar, h, Subgroup.closure_empty])
  obtain ⟨τ, hτ⟩ := hE
  obtain ⟨⟨e, heτ, hAe⟩, y, hy⟩ := hτ
  rw [← heτ] at hy
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) y
  have hze : (QuotientGroup.mk' (Q.subgroupOf M)) (m * e * m⁻¹) ∈
      bar M Q (LB M Q B) := by
    rw [map_mul, map_mul, map_inv]
    exact hy
  obtain ⟨y', hy', hEq⟩ := Subgroup.mem_map.mp hze
  have hQm : ((y'⁻¹ * (m * e * m⁻¹) : ↥M) : G) ∈ Q := by
    have h1 : (QuotientGroup.mk' (Q.subgroupOf M)) (y'⁻¹ * (m * e * m⁻¹)) = 1 := by
      rw [map_mul, map_inv, hEq, inv_mul_cancel]
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hz : ((m * e * m⁻¹ : ↥M) : G) =
      (y' : G) * ((y'⁻¹ * (m * e * m⁻¹) : ↥M) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hzLB : ((m * e * m⁻¹ : ↥M) : G) ∈ LB M Q B := by
    rw [hz]
    exact (LB M Q B).mul_mem (Subgroup.mem_subgroupOf.mp hy') (Subgroup.mem_sup_left hQm)
  refine ⟨((m * e * m⁻¹ : ↥M) : G), hzLB, ?_⟩
  have hconj := sec7ctr_IsA2_conj (hc.conj_Q_eq m.2) (hc.conj_Z_eq m.2) hAe
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj

theorem card_inf_centralizer_Xbar_le (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) :
    Nat.card ↥(bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) ≤ Nat.card Z := by
  classical
  obtain ⟨K, hKf, hKfin, hKcard, f, hf⟩ :=
    stroth114_holds G M Q Z B hc n hw hn ha2
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hKq : Nat.card K = 2 ^ x := by rw [hKcard, hZ]
  have hCX₁ : bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ≤
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z) := by
    intro y hy
    exact ⟨hy.2, Subgroup.map_mono (f := QuotientGroup.mk' (Q.subgroupOf M))
      (fun z hz => hc.LB_le_H0 hz) hy.1⟩
  have hC2 : IsPGroup 2 ↥(bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) :=
    (hc.isPGroup_bar_LB).of_injective
      (Subgroup.inclusion (inf_le_left :
        bar M Q (LB M Q B) ⊓ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ≤
          bar M Q (LB M Q B)))
      (Subgroup.inclusion_injective (inf_le_left :
        bar M Q (LB M Q B) ⊓ Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ≤
          bar M Q (LB M Q B)))
  let g : ↥(bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) →* GL (Fin 2) K :=
    f.comp (Subgroup.inclusion hCX₁)
  have hg : Function.Injective g := hf.comp (Subgroup.inclusion_injective hCX₁)
  have hran2 : IsPGroup 2 ↥(g.range) :=
    hC2.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hdvd : Nat.card ↥(g.range) ∣ Nat.card Z := by
    rw [← hKcard]
    exact card_dvd_of_isPGroup_subgroup_GL_two hx hKq g.range hran2
  have hcard : Nat.card ↥(bar M Q (LB M Q B) ⊓
      Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) = Nat.card ↥(g.range) :=
    Nat.card_congr (Equiv.ofInjective g hg)
  rw [hcard]
  exact Nat.le_of_dvd Nat.card_pos hdvd

theorem card_quotient_inf_centralizer_le (hc : Ctx M Q Z B) {x : ℕ} (hx : 1 ≤ x)
    (he : Nonempty (Xbar M Q Z B ≃* CFSG.AGLEmbedding.PSL2GF 2 x)) :
    Nat.card (↥(bar M Q (LB M Q B)) ⧸
      (bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
          (bar M Q (LB M Q B))) ≤ 2 ^ x * x := by
  classical
  obtain ⟨e⟩ := he
  let f : ↥(bar M Q (LB M Q B)) →* MulAut (CFSG.AGLEmbedding.PSL2GF 2 x) :=
    (MulAut.congr e).toMonoidHom.comp (barLBConjAct hc)
  have hker : f.ker = (barLBConjAct hc).ker :=
    MonoidHom.ker_comp_of_injective (barLBConjAct hc) (MulAut.congr e).toMonoidHom
      (MulAut.congr e).injective
  have hcard : Nat.card (↥(bar M Q (LB M Q B)) ⧸
      (bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
          (bar M Q (LB M Q B))) = Nat.card ↥(f.range) := by
    rw [← barLBConjAct_ker hc, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h2f : IsPGroup 2 ↥(f.range) :=
    (hc.isPGroup_bar_LB).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hdvd : Nat.card ↥(f.range) ∣ 2 ^ x * x :=
    card_twoSubgroup_mulAut_psl2GF_two_dvd hx f.range h2f
  rw [hcard]
  exact Nat.le_of_dvd (Nat.mul_pos (pow_pos (by norm_num) x) (by omega)) hdvd

theorem card_bar_LB_le_sq_mul_x (hc : Ctx M Q Z B) {n x : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hx : 1 ≤ x) (hZ : Nat.card Z = 2 ^ x)
    (hLm2 : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .PSL 2 2 x)
    (hcenter : Subgroup.center ↥(Xbar M Q Z B) = ⊥) :
    Nat.card (bar M Q (LB M Q B)) ≤ (Nat.card Z) ^ 2 * x := by
  classical
  have he := nonempty_xbar_mulEquiv_psl2GF hLm2 hcenter
  have ha2 := exists_isA2_of_lieModel hc hx hLm2 hcenter
  have hC := card_inf_centralizer_Xbar_le hc hw hn hx hZ ha2
  have hQ := card_quotient_inf_centralizer_le hc hx he
  have hprod : Nat.card (bar M Q (LB M Q B)) =
      Nat.card (↥(bar M Q (LB M Q B)) ⧸
        (bar M Q (LB M Q B) ⊓
          Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
            (bar M Q (LB M Q B))) *
      Nat.card ↥(bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
          (bar M Q (LB M Q B)))
    rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  calc Nat.card (bar M Q (LB M Q B)) =
      Nat.card (↥(bar M Q (LB M Q B)) ⧸
        (bar M Q (LB M Q B) ⊓
          Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))).subgroupOf
            (bar M Q (LB M Q B))) *
      Nat.card ↥(bar M Q (LB M Q B) ⊓
        Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q))) := hprod
    _ ≤ (2 ^ x * x) * Nat.card Z := Nat.mul_le_mul hQ hC
    _ = (Nat.card Z) ^ 2 * x := by rw [hZ]; ring

end CFSG.RankThree.GF2n.Stroth80
