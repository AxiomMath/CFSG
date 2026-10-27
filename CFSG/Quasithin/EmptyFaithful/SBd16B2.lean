module

public import CFSG.Quasithin.EmptyFaithful.SBd14Mid

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement Pointwise

namespace SylowX

variable {G : Type} [Group G] [Finite G]

theorem mem_smul_sylow_iff {H : Type*} [Group H] {p : ℕ} (Q : Sylow p H) (h x : H) :
    x ∈ (h • Q : Sylow p H) ↔ h⁻¹ * x * h ∈ Q := by
  have : x ∈ ((h • Q : Sylow p H) : Subgroup H) ↔ x ∈ MulAut.conj h • (Q : Subgroup H) := by
    rw [Sylow.coe_subgroup_smul]
  rw [show (x ∈ (h • Q : Sylow p H)) ↔ x ∈ ((h • Q : Sylow p H) : Subgroup H) from Iff.rfl, this,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp
  exact Iff.rfl

omit [Finite G] in
theorem eq_one_of_isPGroup_two_three {A B : Subgroup G} (hA : IsPGroup 2 ↥A) (hB : IsPGroup 3 ↥B)
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) : x = 1 := by
  obtain ⟨j, hj⟩ := hA ⟨x, hxA⟩
  obtain ⟨i, hi⟩ := hB ⟨x, hxB⟩
  have hj' : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hi' : x ^ 3 ^ i = 1 := by simpa using congrArg Subtype.val hi
  have hcop : Nat.Coprime (2 ^ j) (3 ^ i) := Nat.Coprime.pow j i (by norm_num)
  have := pow_gcd_eq_one.2 ⟨hj', hi'⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

theorem isPGroup_zpowers_of_pow_three {H : Type*} [Group H] {z : H} (hz : z ^ 3 = 1) :
    IsPGroup 3 ↥(Subgroup.zpowers z) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hz)

omit [Finite G] in
theorem mem_map_subtype_iff {Y : Subgroup G} (P : Subgroup ↥Y) {z : G} (hz : z ∈ Y) :
    z ∈ P.map Y.subtype ↔ (⟨z, hz⟩ : ↥Y) ∈ P := by
  constructor
  · rintro ⟨x, hx, hxz⟩
    have : x = ⟨z, hz⟩ := Subtype.ext hxz
    exact this ▸ hx
  · intro h
    exact ⟨⟨z, hz⟩, h, rfl⟩

omit [Finite G] in
theorem mem_normalizer_of_forall_iff {Y X : Subgroup G} (hXY : X ≤ Y) {n : G}
    (hn : n ∈ Subgroup.normalizer (Y : Set G)) (h : ∀ z ∈ Y, z ∈ X ↔ n * z * n⁻¹ ∈ X) :
    n ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  by_cases hz : z ∈ Y
  · exact h z hz
  · have h1 : z ∉ X := fun hzX => hz (hXY hzX)
    have h2 : n * z * n⁻¹ ∉ X := fun hX =>
      hz ((Subgroup.mem_normalizer_iff.mp hn z).mpr (hXY hX))
    exact ⟨fun hzX => absurd hzX h1, fun hX => absurd hX h2⟩

theorem exists_conj_mem_sylow_three {H : Type*} [Group H] [Finite H] (P : Sylow 3 H) {z : H}
    (hz : z ^ 3 = 1) : ∃ h : H, h⁻¹ * z * h ∈ P := by
  obtain ⟨Q, hQ⟩ := (isPGroup_zpowers_of_pow_three hz).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P Q
  refine ⟨h, ?_⟩
  have hzQ : z ∈ Q := hQ (Subgroup.mem_zpowers z)
  rw [← hh] at hzQ
  exact (mem_smul_sylow_iff P h z).mp hzQ

theorem exists_mul_mem_normalizer_sylow {Y : Subgroup G} (P : Sylow 3 ↥Y) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ y ∈ Y, g * y ∈ Subgroup.normalizer (((P : Subgroup ↥Y).map Y.subtype : Subgroup G) : Set G) := by
  classical
  let φ : MulAut ↥Y := Y.normalizerMonoidHom ⟨g, hg⟩
  have hφ : ∀ x : ↥Y, ((φ x : ↥Y) : G) = g * (x : G) * g⁻¹ := fun x =>
    Y.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ x
  have hrange : φ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr φ.surjective
  let Q : Sylow 3 ↥Y := P.comapOfInjective φ.toMonoidHom φ.injective (by
    rw [hrange]
    exact le_top)
  have hQ : ∀ x : ↥Y, x ∈ Q ↔ φ x ∈ P := fun x => Iff.rfl
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq ↥Y Q P
  have key : ∀ x : ↥Y, x ∈ P ↔ φ (h⁻¹ * x * h) ∈ P := by
    intro x
    rw [← hQ, ← mem_smul_sylow_iff Q h x, hh]
  have hmY : g * ((h : ↥Y) : G)⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    Subgroup.mul_mem _ hg (inv_mem (Subgroup.le_normalizer h.2))
  refine ⟨(((h⁻¹ : ↥Y)) : G), (h⁻¹).2, ?_⟩
  show g * ((h : ↥Y) : G)⁻¹ ∈ _
  refine mem_normalizer_of_forall_iff (Subgroup.map_subtype_le _) hmY ?_
  intro z hz
  have hmz : g * ((h : ↥Y) : G)⁻¹ * z * (g * ((h : ↥Y) : G)⁻¹)⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp hmY z).mp hz
  rw [mem_map_subtype_iff _ hz, mem_map_subtype_iff _ hmz]
  have e1 : (⟨g * ((h : ↥Y) : G)⁻¹ * z * (g * ((h : ↥Y) : G)⁻¹)⁻¹, hmz⟩ : ↥Y) =
      φ (h⁻¹ * ⟨z, hz⟩ * h) := by
    apply Subtype.ext
    rw [hφ]
    simp only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e1]
  exact key ⟨z, hz⟩

theorem exists_mul_of_sylow_three {Y : Subgroup G}
    (e : OTwoQuot Y ≃* Multiplicative (Fin 2 → ZMod 3)) (P : Sylow 3 ↥Y) (y : ↥Y) :
    ∃ x ∈ (P : Subgroup ↥Y), ∃ o ∈ CFSG.Open.pCore 2 ↥Y, y = x * o := by
  classical
  have hnormY : (CFSG.Open.pCore 2 ↥Y).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  let π : ↥Y →* OTwoQuot Y := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥Y)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcard : Nat.card (OTwoQuot Y) = 3 ^ 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_multiplicative, ZMod.card]
  have h1 : ((P : Subgroup ↥Y).map π).index ∣ (P : Subgroup ↥Y).index :=
    Subgroup.index_map_dvd _ hπ
  have h2 : ((P : Subgroup ↥Y).map π).index ∣ 3 ^ 2 := by
    have := Subgroup.index_dvd_card ((P : Subgroup ↥Y).map π)
    rwa [hcard] at this
  have h3 : ¬ 3 ∣ ((P : Subgroup ↥Y).map π).index := fun h => P.not_dvd_index (h.trans h1)
  have h4 : ((P : Subgroup ↥Y).map π).index = 1 := by
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    interval_cases i
    · simpa using hi'
    · exact absurd (hi' ▸ dvd_refl 3) h3
    · exact absurd (hi' ▸ (by norm_num : 3 ∣ 3 ^ 2)) h3
  have h5 : (P : Subgroup ↥Y).map π = ⊤ := Subgroup.index_eq_one.mp h4
  have h6 : π y ∈ (P : Subgroup ↥Y).map π := by
    rw [h5]
    exact Subgroup.mem_top _
  obtain ⟨x, hxP, hxy⟩ := h6
  refine ⟨x, hxP, x⁻¹ * y, ?_, by group⟩
  have : (QuotientGroup.mk x : OTwoQuot Y) = QuotientGroup.mk y := hxy
  exact QuotientGroup.eq.mp this

theorem pow_three_eq_one_of_odd {Y : Subgroup G}
    (e : OTwoQuot Y ≃* Multiplicative (Fin 2 → ZMod 3)) {y : G} (hy : y ∈ Y)
    (hodd : Odd (orderOf y)) : y ^ 3 = 1 := by
  have hA3 : ∀ x : Multiplicative (Fin 2 → ZMod 3), x ^ 3 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize (Multiplicative.toAdd x) i = a
    revert a
    decide
  have hnormY : (CFSG.Open.pCore 2 ↥Y).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have h1 : (⟨y, hy⟩ : ↥Y) ^ 3 ∈ CFSG.Open.pCore 2 ↥Y := by
    have h2 : (QuotientGroup.mk ((⟨y, hy⟩ : ↥Y) ^ 3) : OTwoQuot Y) = 1 := by
      apply e.injective
      rw [map_one, QuotientGroup.mk_pow, map_pow]
      exact hA3 _
    exact (QuotientGroup.eq_one_iff _).mp h2
  have h2 : y ^ 3 ∈ pCoreOf 2 Y := ⟨(⟨y, hy⟩ : ↥Y) ^ 3, h1, rfl⟩
  obtain ⟨j, hj⟩ := pCoreOf_isPGroup 2 Y ⟨y ^ 3, h2⟩
  have hj' : (y ^ 3) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hodv1 : orderOf (y ^ 3) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have hodv2 : orderOf (y ^ 3) ∣ orderOf y := orderOf_pow_dvd 3
  have hcop : Nat.Coprime (2 ^ j) (orderOf y) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  have h3 : orderOf (y ^ 3) ∣ Nat.gcd (2 ^ j) (orderOf y) := Nat.dvd_gcd hodv1 hodv2
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

end SylowX

open SylowX

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

section Main

theorem RestHyp.centralizer_Q_X (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) {t' : G}
    (ht'T : t' ∈ T) (hc1 : B6.conjSub t' V₁ = V₂) {X : Subgroup G} {d : G}
    (hdD : d ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L))) (hd3 : d ^ 3 = 1)
    (hdN0 : d ∉ L ⊔ Subgroup.centralizer (L : Set G)) (hdX : d ∈ X)
    (hXV : X ⊓ Subgroup.centralizer (VZ T M : Set G) = ⊥) {y : G} (hyX : y ∈ X)
    (hyYL : y ∈ oTwoUpper (Yp ⊓ L)) (hodd : Odd (orderOf y))
    (hact : ¬ ∀ v ∈ V₂, y * v = v * y) :
    Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have D0 := r.ctx.hyp.decomp
  have hV₁ : V₁ = centerOf L := r.V₁_eq_center h113
  have hdYp : d ∈ Yp := r.D_le_Yp ht'T hdD
  have hdL : d ∈ Subgroup.normalizer (L : Set G) := r.Yp_le_L hdYp
  have hdQ : d ∈ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := r.Yp_le_Q hdYp
  have hdV : ∀ v ∈ V₂, d * v * d⁻¹ = v := fun v hv => by
    have := r.D_cV₂ hc1 d hdD v hv
    calc d * v * d⁻¹ = v * d * d⁻¹ := by rw [this]
      _ = v := by group
  have hd1 : d ≠ 1 := fun h => hdN0 (h ▸ Subgroup.one_mem _)
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdodd : Odd (orderOf d) := by
    rw [hdord]
    exact ⟨1, by norm_num⟩
  obtain ⟨hA, -⟩ := lie_outer r.ctx.c33.quasisimple r.ctx.c33.center_eq r.sylow r.hn2 hdL hdQ hd3
    hdN0 r.V₂_le_Q (fun v hv q hq => r.V₂_cQ v hv q hq) D0.card₂ (r.V₂_inf_Z h113) hdV
  rw [eq_bot_iff]
  rintro c ⟨hcQ, hcX⟩
  rw [Subgroup.mem_bot]
  have hXc : ∀ x ∈ X, x * c = c * x := Subgroup.mem_centralizer_iff.mp hcX
  have hcmem : c ∈ V₂ ⊔ centerOf L := by
    refine hA c hcQ ?_
    have h1 : ⁅c, d⁆ = 1 := by
      calc ⁅c, d⁆ = (c * d) * c⁻¹ * d⁻¹ := rfl
        _ = (d * c) * c⁻¹ * d⁻¹ := by rw [← hXc d hdX]
        _ = 1 := by group
    rw [h1]
    exact Subgroup.one_mem _
  have hcomm2 : ∀ a ∈ V₂, ∀ b ∈ centerOf L, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp hb.2 a ((r.V₂_le_Q ha).2)
  obtain ⟨v₂, hv₂, v₁, hv₁, hcv⟩ := mem_sup_of_commute' hcomm2 hcmem
  have hv₁V : v₁ ∈ V₁ := hV₁ ▸ hv₁
  have hyc : y * c * y⁻¹ = c := by
    calc y * c * y⁻¹ = c * y * y⁻¹ := by rw [hXc y hyX]
      _ = c := by group
  have hyv₁ : y * v₁ * y⁻¹ = v₁ := by
    calc y * v₁ * y⁻¹ = v₁ * y * y⁻¹ := by rw [r.h2 y hyYL v₁ hv₁V]
      _ = v₁ := by group
  have hv₂c : v₂ = c * v₁⁻¹ := by rw [hcv]; group
  have hyv₂ : y * v₂ * y⁻¹ = v₂ := by
    calc y * v₂ * y⁻¹ = (y * c * y⁻¹) * (y * v₁ * y⁻¹)⁻¹ := by rw [hv₂c]; group
      _ = c * v₁⁻¹ := by rw [hyc, hyv₁]
      _ = v₂ := hv₂c.symm
  have hv₂1 : v₂ = 1 := r.fpf₂ h113 hyYL hodd hact v₂ hv₂ hyv₂
  have hcv₁ : c = v₁ := by rw [hcv, hv₂1, one_mul]
  have hcV₁ : c ∈ V₁ := hcv₁ ▸ hv₁V
  by_contra hc1'
  have hdc : d * c * d⁻¹ = c := by
    calc d * c * d⁻¹ = c * d * d⁻¹ := by rw [hXc d hdX]
      _ = c := by group
  have hdN₁ : d ∈ Subgroup.normalizer (V₁ : Set G) := (r.Yp_le_V h113).1 hdYp
  have hall := SBd7.odd_fixes_of_card_four D0.card₁ (fun a ha => r.V_sq a (D0.le₁ ha)) hdN₁ hdodd
    hcV₁ hc1' hdc
  have hle : VZ T M ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [← D0.sup]
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc v * d = (d * v * d⁻¹) * d := by rw [hall v hv]
        _ = d * v := by group
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc v * d = (d * v * d⁻¹) * d := by rw [hdV v hv]
        _ = d * v := by group
  have hdC : d ∈ Subgroup.centralizer (VZ T M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
  have : d ∈ X ⊓ Subgroup.centralizer (VZ T M : Set G) := ⟨hdX, hdC⟩
  rw [hXV, Subgroup.mem_bot] at this
  exact hd1 this

theorem RestHyp.exists_sylow_X (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    ∃ X : Subgroup G, X ≤ Yp ∧ IsPGroup 3 ↥X ∧ ¬ 3 ∣ X.relIndex Yp ∧
      X ⊓ Subgroup.centralizer (VZ T M : Set G) = ⊥ ∧
      Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      (∀ g ∈ T, ∃ n ∈ T ⊓ Subgroup.normalizer (X : Set G),
        ∃ o ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G), g = n * o) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  obtain ⟨hO2, hE9⟩ := r.case1 h113
  obtain ⟨e⟩ := hE9
  obtain ⟨t', ht'T, -, hc1, hc2, -⟩ := exists_swap hyp D0
  obtain ⟨d, hdD, hd3, hdN0⟩ := r.exists_outer h113 ht'T hc2
  have hdYp : d ∈ Yp := r.D_le_Yp ht'T hdD
  have hdY3 : (⟨d, hdYp⟩ : ↥Yp) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  obtain ⟨P, hdP⟩ := (isPGroup_zpowers_of_pow_three hdY3).exists_le_sylow
  set X : Subgroup G := (P : Subgroup ↥Yp).map Yp.subtype with hX
  have hXY : X ≤ Yp := Subgroup.map_subtype_le _
  have hX3 : IsPGroup 3 ↥X := P.isPGroup'.map Yp.subtype
  have hXi : ¬ 3 ∣ X.relIndex Yp := by
    have hsub : X.subgroupOf Yp = (P : Subgroup ↥Yp) :=
      Subgroup.comap_map_eq_self_of_injective Yp.subtype_injective _
    show ¬ 3 ∣ (X.subgroupOf Yp).index
    rw [hsub]
    exact P.not_dvd_index
  have hdX : d ∈ X := ⟨⟨d, hdYp⟩, hdP (Subgroup.mem_zpowers _), rfl⟩
  have hXV : X ⊓ Subgroup.centralizer (VZ T M : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxC⟩
    rw [Subgroup.mem_bot]
    have hxO : x ∈ pCoreOf 2 Yp := by
      rw [hO2]
      exact ⟨hXY hxX, hxC⟩
    exact eq_one_of_isPGroup_two_three (pCoreOf_isPGroup 2 Yp) hX3 hxO hxX
  refine ⟨X, hXY, hX3, hXi, hXV, ?_, ?_⟩
  ·
    obtain ⟨y₂, hy₂, hodd₂, hact₂⟩ := r.exists_y₂
    have hy₂Yp : y₂ ∈ Yp := (oTwoUpper_le _ hy₂).1
    have hy₂3 : y₂ ^ 3 = 1 := pow_three_eq_one_of_odd e hy₂Yp hodd₂
    obtain ⟨h, hh⟩ := exists_conj_mem_sylow_three P
      (z := (⟨y₂, hy₂Yp⟩ : ↥Yp)) (Subtype.ext (by simpa using hy₂3))
    have hy'X : (h : G)⁻¹ * y₂ * h ∈ X := ⟨h⁻¹ * ⟨y₂, hy₂Yp⟩ * h, hh, rfl⟩
    have hhYp : (h : G)⁻¹ ∈ Yp := Yp.inv_mem h.2
    have hy'YL : (h : G)⁻¹ * y₂ * h ∈ oTwoUpper (Yp ⊓ L) := by
      have := (Subgroup.mem_normalizer_iff.mp (r.Yp_le_YL hhYp) y₂).mp hy₂
      simpa using this
    have hodd' : Odd (orderOf ((h : G)⁻¹ * y₂ * h)) := by
      have : (h : G)⁻¹ * y₂ * h = (MulAut.conj (h : G)⁻¹) y₂ := by
        simp
      rw [this, MulEquiv.orderOf_eq]
      exact hodd₂
    have hact' : ¬ ∀ v ∈ V₂, ((h : G)⁻¹ * y₂ * h) * v = v * ((h : G)⁻¹ * y₂ * h) := by
      intro hall
      apply hact₂
      intro v hv
      have hvV : (h : G)⁻¹ * v * h ∈ V₂ := by
        have := (Subgroup.mem_normalizer_iff.mp ((r.Yp_le_V h113).2 hhYp) v).mp hv
        simpa using this
      have h1 := hall _ hvV
      calc y₂ * v = (h : G) * (((h : G)⁻¹ * y₂ * h) * ((h : G)⁻¹ * v * h)) * (h : G)⁻¹ := by group
        _ = (h : G) * (((h : G)⁻¹ * v * h) * ((h : G)⁻¹ * y₂ * h)) * (h : G)⁻¹ := by rw [h1]
        _ = v * y₂ := by group
    exact r.centralizer_Q_X h113 ht'T hc1 hdD hd3 hdN0 hdX hXV hy'X hy'YL hodd' hact'
  ·
    have hT2 : IsPGroup 2 ↥T := hyp.qtfe.sylow.1
    have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 Yp : Set G) := fun g hg =>
      normalizer_le_normalizer_pCoreOf 2 Yp (r.T_le_Yp hg)
    have hOT : pCoreOf 2 Yp ≤ T := by
      have hsup : IsPGroup 2 ↥(T ⊔ pCoreOf 2 Yp) :=
        hT2.to_sup_of_normal_right' (pCoreOf_isPGroup 2 Yp) hTN
      let S : Sylow 2 G := hT2.toSylow hyp.qtfe.sylow.2
      have hST : T ⊔ pCoreOf 2 Yp = T := S.3 hsup (le_sup_left : (S : Subgroup G) ≤ T ⊔ pCoreOf 2 Yp)
      rw [← hST]
      exact le_sup_right
    intro g hgT
    obtain ⟨y, hyYp, hgy⟩ := exists_mul_mem_normalizer_sylow P (r.T_le_Yp hgT)
    obtain ⟨x, hxP, o, hoO, hyo⟩ := exists_mul_of_sylow_three e P ⟨(y : G)⁻¹, Yp.inv_mem hyYp⟩
    have hxX : (x : G) ∈ X := ⟨x, hxP, rfl⟩
    have hy : y = (o : G)⁻¹ * (x : G)⁻¹ := by
      have := congrArg (fun w : ↥Yp => (w : G)⁻¹) hyo
      simpa using this
    have hn : g * (o : G)⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
      have h1 : g * y * (x : G) ∈ Subgroup.normalizer (X : Set G) :=
        Subgroup.mul_mem _ hgy (Subgroup.le_normalizer hxX)
      have h2 : g * y * (x : G) = g * (o : G)⁻¹ := by rw [hy]; group
      rwa [h2] at h1
    have hoO' : (o : G) ∈ pCoreOf 2 Yp := ⟨o, hoO, rfl⟩
    have hoT : (o : G) ∈ T := hOT hoO'
    have hoC : (o : G) ∈ Subgroup.centralizer (VZ T M : Set G) := by
      rw [hO2] at hoO'
      exact hoO'.2
    exact ⟨g * (o : G)⁻¹, ⟨T.mul_mem hgT (T.inv_mem hoT), hn⟩, o, ⟨hoT, hoC⟩, by group⟩

end Main

end CFSG.Quasithin.SBd14
