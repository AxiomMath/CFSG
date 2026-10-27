module

public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.RankThree.PartTwo.Sec8.Outer
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.KFacts.K73Lines
import CFSG.RankThree.Asc83Table.E9
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_E81_lifts {c a : G} (hcL : L ≤ Subgroup.centralizer {c})
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hca : c * a = a * c) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (ha3 : a ^ 3 = 1)
    (hout : ¬ IsInnerAut (thetaQuotMulAut L (compAction L ⟨a, ha⟩)))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    {y₁ y₂ : L ⧸ aschbacherSolvableCore 3 L}
    (hy₁ : y₁ ∈ Sec8.barCentralizer (Subgroup.zpowers a) L)
    (hy₂ : y₂ ∈ Sec8.barCentralizer (Subgroup.zpowers a) L) (hy₁3 : y₁ ^ 3 = 1)
    (hy₂3 : y₂ ^ 3 = 1) (hy : y₁ * y₂ = y₂ * y₁) (hy₁1 : y₁ ≠ 1)
    (hy₂₁ : y₂ ∉ Subgroup.zpowers y₁) :
    ∃ A₀ : Subgroup G,
      (∀ y ∈ Subgroup.closure ({y₁, y₂} : Set (L ⧸ aschbacherSolvableCore 3 L)),
        ∃ (x : G) (hxL : x ∈ L), QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ = y ∧
          x ∈ A₀) ∧ c ∈ A₀ ∧
        a ∈ A₀ ∧ CFSG.Assembly.IsElemAbelian 3 A₀ ∧ Nat.card A₀ = 81 ∧
        A₀ ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
        Late.sectionCentralizer A₀ L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcy y hy).symm)
  set τ : Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (thetaQuotMulAut L).comp (compAction L) with hτdef
  have hτc : τ ⟨c, hcN⟩ = 1 := thetaQuotMulAut_compAction_eq_one hcN hcy
  have hτa3 : τ ⟨a, ha⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [h1, map_one]
  have hmemN : ∀ i j : ℕ, c ^ i * a ^ j ∈ Subgroup.normalizer (L : Set G) := fun i j =>
    mul_mem (pow_mem hcN i) (pow_mem ha j)
  have hτij : ∀ i j : ℕ, τ ⟨c ^ i * a ^ j, hmemN i j⟩ = τ ⟨a, ha⟩ ^ j := by
    intro i j
    have h1 : (⟨c ^ i * a ^ j, hmemN i j⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨c, hcN⟩ ^ i * ⟨a, ha⟩ ^ j := Subtype.ext (by simp)
    rw [h1, map_mul, map_pow, map_pow, hτc, one_pow, one_mul]
  have hout' : ¬ IsInnerAut (τ ⟨a, ha⟩) := hout
  have hac : a ∉ Subgroup.zpowers c := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hout'
    have hk' : (⟨a, ha⟩ : Subgroup.normalizer (L : Set G)) = ⟨c, hcN⟩ ^ k :=
      Subtype.ext (by simp [hk])
    rw [hk', map_zpow, hτc, one_zpow]
    exact ⟨1, map_one _⟩
  set Ebar := Subgroup.closure ({y₁, y₂} : Set (L ⧸ aschbacherSolvableCore 3 L)) with hEbar
  have hEbar9 : Nat.card Ebar = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hy₁3 hy₂3 hy hy₁1 hy₂₁
  have hEbar3 : IsPGroup 3 Ebar := IsPGroup.of_card (n := 2) (by rw [hEbar9]; norm_num)
  have hEbarle : Ebar ≤ Sec8.barCentralizer (Subgroup.zpowers a) L := by
    rw [hEbar, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hy₁
    · exact hy₂
  obtain ⟨E, hEL, hEa, -, himE, hcardE, hinj⟩ :=
    exists_lift_of_le_barCentralizer ha ⟨1, by rw [pow_one]; exact ha3⟩ hEbar3 hEbarle
  have hE9 : Nat.card E = 9 := hcardE.trans hEbar9
  have hqE : ∀ e : L, (e : G) ∈ E →
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) e ∈ Ebar := fun e he => by
    rw [← himE]
    exact ⟨e, he, rfl⟩
  have hE3' : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    have heL := hEL he
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩ ^ 3 = 1 :=
      pow_three_eq_one_of_mem_closure_pair hy hy₁3 hy₂3 (hqE ⟨e, heL⟩ he)
    have h2 : (⟨e, heL⟩ : L) ^ 3 = 1 :=
      hinj _ (by simpa using E.pow_mem he 3) (by rw [map_pow, h1])
    simpa using congrArg Subtype.val h2
  have hEcomm : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e := by
    intro e he e' he'
    have heL := hEL he
    have he'L := hEL he'
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩ *
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e', he'L⟩ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e', he'L⟩ *
          QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩ :=
      commute_of_mem_closure_pair hy hy₁3 hy₂3 (hqE _ he) (hqE _ he')
    have h2 : (⟨e, heL⟩ : L) * ⟨e', he'L⟩ * (⟨e', he'L⟩ * ⟨e, heL⟩)⁻¹ = 1 := by
      refine hinj _ ?_ ?_
      · show e * e' * (e' * e)⁻¹ ∈ E
        exact E.mul_mem (E.mul_mem he he') (E.inv_mem (E.mul_mem he' he))
      · rw [map_mul, map_inv, map_mul, map_mul, h1, mul_inv_cancel]
    exact congrArg Subtype.val (mul_inv_eq_one.mp h2)
  have hlift : ∀ y ∈ Ebar, ∃ (x : G) (hxL : x ∈ L),
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩ = y ∧ x ∈ E := by
    intro y hy
    rw [← himE] at hy
    obtain ⟨x, hxE, rfl⟩ := hy
    exact ⟨x, x.2, rfl, hxE⟩
  set B := Subgroup.closure ({c, a} : Set G) with hB
  have hB9 : Nat.card B = 9 :=
    CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine hc3 ha3 hca hc1 hac
  have hBE : ∀ b ∈ B, ∀ e ∈ E, b * e = e * b := by
    intro b hb e he
    obtain ⟨i, j, -, -, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hb
    have hce : Commute c e := hcy e (hEL he)
    have hae : Commute a e := (Subgroup.mem_centralizer_singleton_iff.mp (hEa he)).symm
    exact ((hce.pow_left i).mul_left (hae.pow_left j)).eq
  have hEN : E ≤ Subgroup.normalizer (B : Set G) := fun e he =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => hBE b hb e he)
  have hdisj : Disjoint B E := by
    rw [Subgroup.disjoint_def]
    intro x hxB hxE
    obtain ⟨i, j, -, hj, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hxB
    have hxL := hEL hxE
    have hinner : IsInnerAut (τ ⟨a, ha⟩ ^ j) := by
      rw [← hτij i j]
      change IsInnerAut (thetaQuotMulAut L (compAction L ⟨_, hmemN i j⟩))
      rw [thetaQuotMulAut_compAction_of_mem hxL]
      exact ⟨_, rfl⟩
    have hj0 : j = 0 := by
      by_contra hj0
      exact hout' (isInnerAut_of_pow_of_pow_three hτa3 (Nat.one_le_iff_ne_zero.mpr hj0) hj hinner)
    subst hj0
    simp only [pow_zero, mul_one] at hxL hxE ⊢
    have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c ^ i, hxL⟩ ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) z
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact ((show Commute c l from hcy l l.2).pow_left i).eq.symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val (hinj ⟨c ^ i, hxL⟩ hxE hcen)
  set A₀ := B ⊔ E with hA₀
  have hA₀81 : Nat.card A₀ = 81 := by
    rw [hA₀, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B E hEN hdisj,
      hB9, hE9]
  have hdecomp : ∀ x ∈ A₀, ∃ e ∈ E, ∃ b ∈ B, e * b = x := by
    intro x hx
    rw [hA₀, sup_comm, ← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right E B hEN] at hx
    obtain ⟨e, he, b, hb, rfl⟩ := hx
    exact ⟨e, he, b, hb, rfl⟩
  have hcomm : ∀ x ∈ A₀, ∀ y ∈ A₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨e, he, b, hb, rfl⟩ := hdecomp x hx
    obtain ⟨e', he', b', hb', rfl⟩ := hdecomp y hy
    have h1 : Commute (e * b) (e' * b') := by
      apply Commute.mul_left
      · exact (show Commute e e' from hEcomm e he e' he').mul_right
          (show Commute e b' from (hBE b' hb' e he).symm)
      · exact (show Commute b e' from hBE b hb e' he').mul_right
          (show Commute b b' from commute_of_mem_closure_pair hca hc3 ha3 hb hb')
    exact h1.eq
  have hexp : ∀ x ∈ A₀, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, b, hb, rfl⟩ := hdecomp x hx
    have hc : Commute e b := (hBE b hb e he).symm
    rw [hc.mul_pow, hE3' e he, pow_three_eq_one_of_mem_closure_pair hca hc3 ha3 hb, one_mul]
  have hcA : c ∈ A₀ := (le_sup_left : B ≤ A₀) (Subgroup.subset_closure (by simp))
  have haA : a ∈ A₀ := (le_sup_left : B ≤ A₀) (Subgroup.subset_closure (by simp))
  refine ⟨A₀, fun y hy => ?_, hcA, haA,
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, hexp⟩, hA₀81, fun x hx =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
        hcomm z ((Subgroup.zpowers_le.mpr hcA) hz) x hx), ?_⟩
  · obtain ⟨x, hxL, hx, hxE⟩ := hlift y hy
    exact ⟨x, hxL, hx, (le_sup_right : E ≤ A₀) hxE⟩
  ext x
  rw [Late.sectionCentralizer]
  constructor
  · rintro ⟨hx, hxL⟩
    obtain ⟨e, he, b, hb, rfl⟩ := hdecomp x hx
    obtain ⟨i, j, -, hj, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hca hc3 ha3 hb
    have heL := hEL he
    have heN : e ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer heL
    have hxN : e * (c ^ i * a ^ j) ∈ Subgroup.normalizer (L : Set G) := mul_mem heN (hmemN i j)
    have h1 : τ ⟨e * (c ^ i * a ^ j), hxN⟩ = 1 :=
      thetaQuotMulAut_compAction_eq_one_of_forall hxN hxL
    have h2 : τ ⟨e * (c ^ i * a ^ j), hxN⟩ =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩) * τ ⟨a, ha⟩ ^ j := by
      have h3 : (⟨e * (c ^ i * a ^ j), hxN⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨e, heN⟩ * ⟨c ^ i * a ^ j, hmemN i j⟩ := rfl
      rw [h3, map_mul, hτij]
      congr 1
      exact thetaQuotMulAut_compAction_of_mem heL heN
    rw [h2] at h1
    have hinner : IsInnerAut (τ ⟨a, ha⟩ ^ j) :=
      ⟨(QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩)⁻¹, by
        rw [map_inv]
        exact (eq_inv_of_mul_eq_one_right h1).symm⟩
    have hj0 : j = 0 := by
      by_contra hj0
      exact hout' (isInnerAut_of_pow_of_pow_three hτa3 (Nat.one_le_iff_ne_zero.mpr hj0) hj hinner)
    subst hj0
    rw [pow_zero, mul_one] at h1
    have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩ ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      generalize QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨e, heL⟩ = u at h1 ⊢
      rw [Subgroup.mem_center_iff]
      intro z
      have h4 := congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore 3 L) => φ z) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h4
      calc z * u = u * z * u⁻¹ * u := by rw [h4]
        _ = u * z := by group
    rw [hZ, Subgroup.mem_bot] at hcen
    have he1 : e = 1 := congrArg Subtype.val (hinj ⟨e, heL⟩ he hcen)
    rw [he1, one_mul, pow_zero, mul_one]
    exact Subgroup.npow_mem_zpowers c i
  · intro hx
    refine ⟨(Subgroup.zpowers_le.mpr hcA) hx, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm' : c ^ k * y = y * c ^ k := ((show Commute c y from hcy y hy).zpow_left k).eq
    rw [hcomm', mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _


theorem nontrivial_projSL_two {m : ℕ} (hm : m ≠ 0) :
    Nontrivial (projSL 2 (GaloisField 2 m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := nonempty_sl2_mulEquiv_projSL (F := GaloisField 2 m) (GaloisField.card 2 m hm)
  have := nontrivial_sl2 (GaloisField 2 m)
  exact ι.injective.nontrivial

theorem ne_bot_of_mulEquiv {M T : Type*} [Group M] [Group T] [Nontrivial T] {H : Subgroup M}
    (ι : H ≃* T) : H ≠ ⊥ := by
  intro hH
  obtain ⟨t, ht⟩ := exists_ne (1 : T)
  apply ht
  obtain ⟨x, rfl⟩ := ι.surjective t
  have hx : x = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall H).mp hH x x.2)
  rw [hx, map_one]

theorem mulAut_congr_eq {M : Type*} [Group M] (φ α : MulAut M) :
    MulAut.congr φ α = φ * α * φ⁻¹ := by
  ext x
  rfl

theorem inducedAutHom_trans {M : Type*} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (φ : MulAut M) (x : Subgroup.normalizer (L : Set G)) :
    inducedAutHom L (e.trans φ) x = φ * inducedAutHom L e x * φ⁻¹ := by
  rw [inducedAutHom_apply, inducedAutHom_apply, congr_trans, mulAut_congr_eq]

theorem symm_mem_barCentralizer {M : Type*} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G)) {z : M}
    (hz : inducedAutHom L e ⟨a, ha⟩ z = z) :
    e.symm z ∈ Sec8.barCentralizer (Subgroup.zpowers a) L := by
  rw [mem_barCentralizer_zpowers_iff ha]
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  exact hz

theorem nonempty_imageModTheta_mulEquiv_of_conj {M : Type*} [Group M]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1) {z : M}
    (hdz : inducedAutHom L e ⟨d, hd⟩ = MulAut.conj z) :
    Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
      inSubgroup perfectResidual (Subgroup.centralizer ({z} : Set M))) :=
  nonempty_imageModTheta_perfectResidual_mulEquiv hd hd3 e _ fun w => by
    rw [Subgroup.mem_centralizer_singleton_iff, hdz, MulAut.conj_apply]
    constructor
    · intro h1
      rw [← h1, mul_inv_cancel_right]
    · intro h1
      calc w * z = z * w * z⁻¹ * z := by rw [h1]
        _ = z * w := by group

section Model


theorem exists_data83_of_model {A : Subgroup G} {c a : G} (h : Hyp81 G A c L a)
    {M : Type*} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (hZ : Subgroup.center M = ⊥) {z₁ z₂ : M}
    (hz₁ : inducedAutHom L e ⟨a, h.a_mem_normalizer⟩ z₁ = z₁)
    (hz₂ : inducedAutHom L e ⟨a, h.a_mem_normalizer⟩ z₂ = z₂)
    (hz₁3 : z₁ ^ 3 = 1) (hz₂3 : z₂ ^ 3 = 1) (hz : z₁ * z₂ = z₂ * z₁) (hz₁1 : z₁ ≠ 1)
    (hz₂₁ : z₂ ∉ Subgroup.zpowers z₁)
    (hne : inSubgroup perfectResidual (Subgroup.centralizer ({z₁} : Set M)) ≠ ⊥)
    {n : ℕ} (hn : Odd n)
    (hinner : ∀ d : G, d ∈ L →
      InducesStdKind L d .inner ∨ InducesStdKind L d .diagonal)
    (hcases : ∀ (A₀ : Subgroup G) (d : G), a ∈ A₀ → CFSG.Assembly.IsElemAbelian 3 A₀ →
      (∀ z ∈ Subgroup.closure ({z₁, z₂} : Set M), ∃ x ∈ A₀, ∃ hxL : x ∈ L,
        e (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩) = z) →
      Nonempty (Sec8.imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))
        ≃* inSubgroup perfectResidual (Subgroup.centralizer ({z₁} : Set M))) →
      Sec8.Cases83 L a A₀ d n) :
    ∃ (A₀ : Subgroup G) (d : G), Sec8.Data83 G c L a A₀ d n := by
  have ha := h.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hca : c * a = a * c :=
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
  have hout' := h.not_isInnerAut_induced
  have hcL : L ≤ Subgroup.centralizer {c} := by
    obtain ⟨L', -, rfl⟩ := h.mem_thetaComponentsAt
    exact Subgroup.map_subtype_le _
  have hZ' : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    Sec4.center_eq_bot_of_mulEquiv e hZ
  have hy₁ := symm_mem_barCentralizer e ha hz₁
  have hy₂ := symm_mem_barCentralizer e ha hz₂
  have hy₁3 : e.symm z₁ ^ 3 = 1 := by rw [← map_pow, hz₁3, map_one]
  have hy₂3 : e.symm z₂ ^ 3 = 1 := by rw [← map_pow, hz₂3, map_one]
  have hy : e.symm z₁ * e.symm z₂ = e.symm z₂ * e.symm z₁ := by rw [← map_mul, ← map_mul, hz]
  have hy₁1 : e.symm z₁ ≠ 1 := fun h1 => hz₁1 (by rw [← e.apply_symm_apply z₁, h1, map_one])
  have hy₂₁ : e.symm z₂ ∉ Subgroup.zpowers (e.symm z₁) := by
    rintro ⟨k, hk⟩
    apply hz₂₁
    refine ⟨k, ?_⟩
    apply e.symm.injective
    rw [map_zpow]
    exact hk
  obtain ⟨A₀, hlift, hcA, haA, hA₀, hcard, hnorm, hsec⟩ :=
    exists_E81_lifts hcL ha hca hc3 h.ne_one ha3 hout' hZ' hy₁ hy₂ hy₁3 hy₂3 hy hy₁1 hy₂₁
  have hlift' : ∀ z ∈ Subgroup.closure ({z₁, z₂} : Set M), ∃ x ∈ A₀, ∃ hxL : x ∈ L,
      e (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩) = z := by
    intro z hz'
    have hmem : e.symm z ∈ Subgroup.closure
        ({e.symm z₁, e.symm z₂} : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
      have h1 : (Subgroup.closure ({z₁, z₂} : Set M)).map e.symm.toMonoidHom =
          Subgroup.closure ({e.symm z₁, e.symm z₂} : Set (L ⧸ aschbacherSolvableCore 3 L)) := by
        rw [MonoidHom.map_closure, Set.image_pair]
        rfl
      rw [← h1]
      exact ⟨z, hz', rfl⟩
    obtain ⟨x, hxL, hx, hxA⟩ := hlift _ hmem
    exact ⟨x, hxA, hxL, by rw [hx, MulEquiv.apply_symm_apply]⟩
  obtain ⟨d, hdA, hdL, hdz⟩ := hlift' z₁ (Subgroup.subset_closure (by simp))
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hdL
  have hd3 : ∃ j : ℕ, d ^ 3 ^ j = 1 := ⟨1, by rw [pow_one]; exact hA₀.2 d hdA⟩
  have hdconj : inducedAutHom L e ⟨d, hdN⟩ = MulAut.conj z₁ := by
    rw [inducedAutHom_eq_conj_of_mem e hdL hdN, hdz]
  have hK := nonempty_imageModTheta_mulEquiv_of_conj e hdN hd3 hdconj
  have : Nontrivial (inSubgroup perfectResidual (Subgroup.centralizer ({z₁} : Set M))) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hKne : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≠ ⊥ :=
    ne_bot_of_imageModTheta_mulEquiv hK.some
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hz₁1
    rw [← hdz]
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨1, hdL⟩ = 1 := map_one _
    rw [h1, map_one]
  exact ⟨A₀, d, ⟨fun x hx => hnorm hx, hcA, haA, hA₀, hcard, hsec, hdA, hd1, hinner d hdL, hn,
    hKne, hcases A₀ d haA hA₀ hlift' hK⟩⟩

end Model

end CFSG.RankThree.PartTwo.Sec8.Item83Proof
