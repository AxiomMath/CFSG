module

public import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.KFacts.K72Moving
import CFSG.RankThree.PartTwo.KFacts.K73Lines
import CFSG.RankThree.Asc83Table.E9
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem eq_one_of_mem_aschbacherSolvableCore_of_pow {x : L}
    (hx : x ∈ aschbacherSolvableCore 3 L) {j : ℕ} (hxj : x ^ 3 ^ j = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hxj
  have h2 : orderOf x ∣ Nat.card (aschbacherSolvableCore 3 L) := by
    rw [show orderOf x = orderOf (⟨x, hx⟩ : aschbacherSolvableCore 3 L) from
      Subgroup.orderOf_coe ⟨x, hx⟩]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ j) (Nat.card (aschbacherSolvableCore 3 L)) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (not_three_dvd_card_aschbacherSolvableCore L))
  have h3 : orderOf x ∣ 1 := by
    rw [← Nat.Coprime.gcd_eq_one hcop]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem thetaQuotMulAut_compAction_of_mem {d : G} (hdL : d ∈ L)
    (hd : d ∈ Subgroup.normalizer (L : Set G)) :
    thetaQuotMulAut L (compAction L ⟨d, hd⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩) := by
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  rw [thetaQuotMulAut_mk, MulAut.conj_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

theorem inducedAutHom_eq_conj_of_mem {M : Type*} [Group M]
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {d : G} (hdL : d ∈ L)
    (hd : d ∈ Subgroup.normalizer (L : Set G)) :
    inducedAutHom L e ⟨d, hd⟩ =
      MulAut.conj (e (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩)) := by
  rw [inducedAutHom_apply, thetaQuotMulAut_compAction_of_mem hdL hd]
  ext m
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem exists_lift_of_le_barCentralizer {a : G} (ha : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : ∃ j : ℕ, a ^ 3 ^ j = 1) {Ebar : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (hE3 : IsPGroup 3 Ebar) (hEa : Ebar ≤ Sec8.barCentralizer (Subgroup.zpowers a) L) :
    ∃ E : Subgroup G, E ≤ L ∧ E ≤ Subgroup.centralizer {a} ∧ IsPGroup 3 E ∧
      Sec8.imageModTheta L E = Ebar ∧ Nat.card E = Nat.card Ebar ∧
      ∀ x : L, (x : G) ∈ E → QuotientGroup.mk' (aschbacherSolvableCore 3 L) x = 1 → x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set q := QuotientGroup.mk' θ with hq
  set P : Subgroup L := Ebar.comap q with hP
  set P' : Subgroup G := P.map L.subtype with hP'
  have hfix : ∀ b : G, ∀ hb : b ∈ Subgroup.normalizer (L : Set G), b ∈ Subgroup.zpowers a →
      ∀ y ∈ Ebar, thetaQuotMulAut L (compAction L ⟨b, hb⟩) y = y := by
    intro b hb hba y hy
    have hy' := hEa hy
    rw [Sec8.barCentralizer, FixedPoints.mem_subgroup] at hy'
    exact hy' ⟨_, mem_autThetaQuot_iff.mpr ⟨b, hb, hba, rfl⟩⟩
  have hconjP : ∀ b : G, ∀ hb : b ∈ Subgroup.normalizer (L : Set G), b ∈ Subgroup.zpowers a →
      ∀ g ∈ P', b * g * b⁻¹ ∈ P' := by
    rintro b hb hba _ ⟨l, hl, rfl⟩
    refine ⟨compAction L ⟨b, hb⟩ l, ?_, rfl⟩
    change q (compAction L ⟨b, hb⟩ l) ∈ Ebar
    have h1 : q (compAction L ⟨b, hb⟩ l) = thetaQuotMulAut L (compAction L ⟨b, hb⟩) (q l) :=
      (thetaQuotMulAut_mk _ l).symm
    rw [h1, hfix b hb hba _ hl]
    exact hl
  have haP' : a ∈ Subgroup.normalizer (P' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact hconjP a ha (Subgroup.mem_zpowers a) g
    · intro hg
      have h1 := hconjP a⁻¹ (inv_mem ha) (inv_mem (Subgroup.mem_zpowers a)) _ hg
      have e : a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g := by group
      rwa [e] at h1
  have hA3 : IsPGroup 3 (Subgroup.zpowers a) := by
    obtain ⟨j, hj⟩ := ha3
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hj)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨Q, hQ⟩ := exists_sylow_le_normalizer hA3 (Subgroup.zpowers_le.mpr haP')
  set E : Subgroup G := (Q : Subgroup P').map P'.subtype with hE
  have hEP' : E ≤ P' := Subgroup.map_subtype_le _
  have hP'L : P' ≤ L := Subgroup.map_subtype_le _
  have hEL : E ≤ L := hEP'.trans hP'L
  have hE3' : IsPGroup 3 E := Q.isPGroup'.map P'.subtype
  have hmemP : ∀ x : L, (x : G) ∈ E → x ∈ P := by
    intro x hx
    obtain ⟨l, hl, hlx⟩ := hEP' hx
    rwa [show l = x from Subtype.ext hlx] at hl
  have hinj : ∀ x : L, (x : G) ∈ E → q x = 1 → x = 1 := by
    intro x hx hqx
    have hxθ : x ∈ θ := by
      rw [hq, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hqx
      exact hqx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hE3') ⟨x, hx⟩
    have hxk : x ^ 3 ^ k = 1 := by
      have h1 : (⟨(x : G), hx⟩ : E) ^ 3 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
      exact Subtype.ext (by simpa using congrArg Subtype.val h1)
    exact eq_one_of_mem_aschbacherSolvableCore_of_pow hxθ hxk
  have hle : Sec8.imageModTheta L E ≤ Ebar := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmemP x hx
  have hθP : θ ≤ P := by
    intro x hx
    change q x ∈ Ebar
    have h1 : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact one_mem _
  have hcardP : Nat.card P = Nat.card θ * Nat.card Ebar := by
    have h1 := Subgroup.card_ker_mul_card_range (q.comp P.subtype)
    have hker : (q.comp P.subtype).ker = θ.subgroupOf P := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hrange : (q.comp P.subtype).range = Ebar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective θ) Ebar
    rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθP).toEquiv] at h1
    exact h1.symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE3
  have hθ3 : ¬ 3 ∣ Nat.card θ := not_three_dvd_card_aschbacherSolvableCore L
  have hθ0 : Nat.card θ ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card P').factorization 3 = k := by
    rw [hP', Subgroup.card_map_of_injective L.subtype_injective, hcardP, hk,
      Nat.factorization_mul hθ0 (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hθ3, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, zero_add]
  have hcardQ : Nat.card E = 3 ^ k := by
    rw [hE, Subgroup.card_map_of_injective P'.subtype_injective, Sylow.card_eq_multiplicity, hfac]
  have hcardIm : Nat.card (Sec8.imageModTheta L E) = Nat.card E := by
    set g := q.comp (E.subgroupOf L).subtype with hg
    have hker : g.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.mpr (Subtype.ext (hinj (x : L) x.2 hx))
    have h1 := Subgroup.card_ker_mul_card_range g
    rw [hker, Subgroup.card_bot, one_mul] at h1
    have hrange : g.range = Sec8.imageModTheta L E := by
      rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
      rfl
    rw [← hrange, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv]
  have himage : Sec8.imageModTheta L E = Ebar :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardIm, hcardQ, hk])
  refine ⟨E, hEL, fun e he => ?_, hE3', himage, by rw [← hcardIm, himage], hinj⟩
  ·
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he' : a * e * a⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hQ (Subgroup.mem_zpowers a)) e).mp he
    set x : L := ⟨e, hEL he⟩
    set x' : L := compAction L ⟨a, ha⟩ x
    have hx' : (x' : G) = a * e * a⁻¹ := rfl
    have hqx : q x' = q x := by
      have h1 : q x' = thetaQuotMulAut L (compAction L ⟨a, ha⟩) (q x) :=
        (thetaQuotMulAut_mk _ x).symm
      rw [h1, hfix a ha (Subgroup.mem_zpowers a) _ (hmemP x he)]
    have h1 : x'⁻¹ * x = 1 := by
      refine hinj _ ?_ (by rw [map_mul, map_inv, hqx, inv_mul_cancel])
      change (x' : G)⁻¹ * e ∈ E
      rw [hx']
      exact E.mul_mem (E.inv_mem he') he
    have h2 : (x' : G) = e := by
      have := congrArg Subtype.val (inv_mul_eq_one.mp h1)
      exact this
    rw [hx'] at h2
    calc e * a = a * e * a⁻¹ * a := by rw [h2]
      _ = a * e := by group

section E81

theorem thetaQuotMulAut_compAction_eq_one {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hbL : ∀ y ∈ L, b * y = y * b) : thetaQuotMulAut L (compAction L ⟨b, hb⟩) = 1 := by
  ext y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  rw [thetaQuotMulAut_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  change b * (l : G) * b⁻¹ = l
  rw [hbL l l.2, mul_inv_cancel_right]

theorem isInnerAut_of_pow_of_pow_three {M : Type*} [Group M] {τ : MulAut M} (h3 : τ ^ 3 = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j < 3) (hτ : IsInnerAut (τ ^ j)) : IsInnerAut τ := by
  interval_cases j
  · simpa using hτ
  · have h : τ = (τ ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, h3, one_mul, pow_one]
    rw [h]
    exact Subgroup.pow_mem _ hτ 2

theorem pow_three_eq_one_of_mem_closure_pair {M : Type*} [Group M] {x y : M}
    (hxy : x * y = y * x) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) {z : M}
    (hz : z ∈ Subgroup.closure ({x, y} : Set M)) : z ^ 3 = 1 := by
  obtain ⟨i, j, -, -, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hxy hx3 hy3 hz
  have hc : Commute (x ^ i) (y ^ j) := (show Commute x y from hxy).pow_pow i j
  rw [hc.mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul, hx3, hy3,
    one_pow, one_pow, one_mul]

theorem commute_of_mem_closure_pair {M : Type*} [Group M] {x y : M} (hxy : x * y = y * x)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) {z w : M} (hz : z ∈ Subgroup.closure ({x, y} : Set M))
    (hw : w ∈ Subgroup.closure ({x, y} : Set M)) : z * w = w * z := by
  obtain ⟨i, j, -, -, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hxy hx3 hy3 hz
  obtain ⟨k, l, -, -, rfl⟩ := exists_pow_mul_pow_of_mem_closure_pair hxy hx3 hy3 hw
  have hc : Commute x y := hxy
  have h1 : Commute (x ^ i * y ^ j) (x ^ k * y ^ l) := by
    apply Commute.mul_left
    · exact (Commute.pow_pow_self x i k).mul_right (hc.pow_pow i l)
    · exact (hc.symm.pow_pow j k).mul_right (Commute.pow_pow_self y j l)
  exact h1.eq

theorem thetaQuotMulAut_compAction_eq_one_of_forall {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (h : ∀ y ∈ L, x * y * x⁻¹ * y⁻¹ ∈ (aschbacherSolvableCore 3 L).map L.subtype) :
    thetaQuotMulAut L (compAction L ⟨x, hx⟩) = 1 := by
  ext z
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  rw [thetaQuotMulAut_mk, MulAut.one_apply]
  apply QuotientGroup.eq_iff_div_mem.mpr
  obtain ⟨t, ht, hte⟩ := h l l.2
  have : compAction L ⟨x, hx⟩ l / l = t := by
    apply Subtype.ext
    change x * (l : G) * x⁻¹ / l = L.subtype t
    rw [hte, div_eq_mul_inv]
  rw [this]
  exact ht

theorem exists_E81 {c a : G} (hcL : L ≤ Subgroup.centralizer {c})
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hca : c * a = a * c) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (ha3 : a ^ 3 = 1)
    (hout : ¬ IsInnerAut (thetaQuotMulAut L (compAction L ⟨a, ha⟩)))
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    {y₁ y₂ : L ⧸ aschbacherSolvableCore 3 L}
    (hy₁ : y₁ ∈ Sec8.barCentralizer (Subgroup.zpowers a) L)
    (hy₂ : y₂ ∈ Sec8.barCentralizer (Subgroup.zpowers a) L) (hy₁3 : y₁ ^ 3 = 1)
    (hy₂3 : y₂ ^ 3 = 1) (hy : y₁ * y₂ = y₂ * y₁) (hy₁1 : y₁ ≠ 1)
    (hy₂₁ : y₂ ∉ Subgroup.zpowers y₁) :
    ∃ (A₀ : Subgroup G) (d : G) (hdL : d ∈ L),
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨d, hdL⟩ = y₁ ∧ d ∈ A₀ ∧ c ∈ A₀ ∧
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
  have hy₁E : y₁ ∈ Sec8.imageModTheta L E := by
    rw [himE]
    exact Subgroup.subset_closure (by simp)
  obtain ⟨x₁, hx₁E, hx₁⟩ := hy₁E
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
  refine ⟨A₀, x₁, x₁.2, hx₁, (le_sup_right : E ≤ A₀) hx₁E, hcA, haA,
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, hexp⟩, hA₀81, fun x hx =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
        hcomm z ((Subgroup.zpowers_le.mpr hcA) hz) x hx), ?_⟩
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

end E81

end CFSG.RankThree.PartTwo.KFacts
