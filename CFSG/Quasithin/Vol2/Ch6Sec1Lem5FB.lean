module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FA
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5EA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped MatrixGroups
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mul_self)

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem hall_ch615 (c : Cx615C G T M L V H n) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) : IsCyclic D ∧ Nat.card D = 2 ^ n - 1 := by
  classical
  have h := c.hyp
  obtain ⟨F, _, _, _, hF, ψ, Yc, hc⟩ := c.nat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hS := h.toHyp5_0_1.setting516 hD h.module
  have hCV : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
    rw [c.V_eq]; exact hS.centralizer_le
  have hLN := hc.le_normalizer
  have hDL : ∀ d ∈ D, d ∈ L := fun d hd => (Subgroup.mem_inf.mp (hD.1 hd)).1
  have hDN : ∀ d ∈ D, d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    fun d hd => (Subgroup.mem_inf.mp (hD.1 hd)).2
  have hDodd : ∀ d ∈ D, Odd (orderOf d) := fun d hd =>
    Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hd)
  let φ : ↥D →* F :=
    { toFun := fun d => (ψ (autHom hLN ⟨d, hDL d d.2⟩) : Matrix (Fin 2) (Fin 2) F) 0 0
      map_one' := by
        show (ψ (autHom hLN 1) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
        rw [map_one, map_one]
        simp
      map_mul' := fun a b => by
        have e : (autHom hLN ⟨((a * b : ↥D) : G), hDL _ (a * b).2⟩ : ↥(autOn L V)) =
            autHom hLN ⟨a, hDL a a.2⟩ * autHom hLN ⟨b, hDL b b.2⟩ := by
          rw [← map_mul]
          rfl
        simp only [e, map_mul]
        exact (upper_mul (hc.upper (hDL a a.2) (hDN a a.2))
          (hc.upper (hDL b b.2) (hDN b b.2))).2 }
  have hφ : ∀ d : ↥D, φ d = (ψ (autHom hLN ⟨d, hDL d d.2⟩) : Matrix (Fin 2) (Fin 2) F) 0 0 :=
    fun d => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro d hd
    rw [hφ] at hd
    have hu := eq_unipSL_of_upper_ch615 (hc.upper (hDL d d.2) (hDN d d.2)) hd
    have hsq : autHom hLN ⟨(d : G) ^ 2, L.pow_mem (hDL d d.2) 2⟩ = 1 := by
      apply ψ.injective
      have e : (autHom hLN ⟨(d : G) ^ 2, L.pow_mem (hDL d d.2) 2⟩ : ↥(autOn L V)) =
          autHom hLN ⟨d, hDL d d.2⟩ * autHom hLN ⟨d, hDL d d.2⟩ := by
        rw [← map_mul]
        congr 1
        exact Subtype.ext (pow_two _)
      rw [e, map_mul, hu, unipSL_mul_self, map_one]
    have hcen := mem_centralizer_of_autHom_eq_one hLN hsq
    have hT : (d : G) ^ 2 ∈ T := hCV ⟨Subgroup.mem_sup_left (L.pow_mem (hDL d d.2) 2), hcen⟩
    obtain ⟨k, hk⟩ := h.sylow.1 ⟨_, hT⟩
    have hk' : ((d : G) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd := hDodd d d.2
    have hd1 : orderOf (d : G) ∣ 2 * 2 ^ k := by
      rw [← pow_mul] at hk'
      exact orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf (d : G)) (2 * 2 ^ k) :=
      Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd)
        (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))
    have h1 : orderOf (d : G) = 1 := Nat.Coprime.eq_one_of_dvd hcop hd1
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  refine ⟨isCyclic_of_injective_ringHom φ hφinj, ?_⟩
  set φ' : ↥D →* Fˣ := φ.toHomUnits with hφ'
  have hbij : Function.Bijective φ' := by
    refine ⟨fun a b hab => hφinj (by simpa [hφ'] using congrArg Units.val hab), fun u => ?_⟩
    obtain ⟨δ, hδ, hδc⟩ := hc.exists_mem_D hCV c.toCx615.isSylowTwoOf_inf hD u.ne_zero
    exact ⟨⟨δ, hδ⟩, Units.ext (by rw [hφ', MonoidHom.coe_toHomUnits]; exact hδc)⟩
  rw [Nat.card_eq_of_bijective φ' hbij, Nat.card_units, hF]

theorem hall_inf_centralizer_ch615 (c : Cx615C G T M L V H n) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    D ⊓ Subgroup.centralizer (UX615 T L H : Set G) = ⊥ := by
  rw [eq_bot_iff]
  rintro d ⟨hdD, hdC⟩
  have hdT : d ∈ T := c.faithful ⟨Subgroup.mem_sup_left (hD.1 hdD), hdC⟩
  have hodd : Odd (orderOf d) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hdD)
  obtain ⟨k, hk⟩ := c.hyp.sylow.1 ⟨d, hdT⟩
  have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf d = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)) (orderOf_dvd_of_pow_eq_one hk')
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)

theorem hall_mul_ch615 (c : Cx615C G T M L V H n) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    (∀ t ∈ T, ∀ d ∈ D, ∃ d' ∈ D, ∃ t' ∈ T, t * d = d' * t') ∧
      ∀ d ∈ D, ∀ t ∈ T, ∃ t' ∈ T, ∃ d' ∈ D, d * t = t' * d' := by
  have h := c.hyp.toHyp5_0_1
  have key : ∀ t ∈ T, ∀ d ∈ D, ∃ d' ∈ D, ∃ t' ∈ T, t * d = d' * t' := by
    intro t ht d hd
    have hBT := Subgroup.coe_mul_of_right_le_normalizer_left (borelL T L) T
      h.T_le_normalizer_borel
    have hDS := Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L)
      (hD.1.trans inf_le_right)
    have h1 : t * d ∈ ((borelL T L ⊔ T : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left (hD.1 hd))
    rw [hBT] at h1
    obtain ⟨y, hy, s, hs, hys⟩ := h1
    have hy' : y ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
      rw [h.borelL_eq_sup hD]
      exact hy
    rw [hDS] at hy'
    obtain ⟨d', hd', r, hr, rfl⟩ := hy'
    refine ⟨d', hd', r * s, T.mul_mem hr.1 hs, ?_⟩
    rw [← hys]
    group
  refine ⟨key, fun d hd t ht => ?_⟩
  obtain ⟨d', hd', t', ht', he⟩ := key t⁻¹ (T.inv_mem ht) d⁻¹ (D.inv_mem hd)
  refine ⟨t'⁻¹, T.inv_mem ht', d'⁻¹, D.inv_mem hd', ?_⟩
  have := congrArg (·⁻¹) he
  simpa [mul_inv_rev] using this

theorem not_hall_normalizes_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)) :
    ¬ ∀ y ∈ autI hU D, ∀ k ∈ autI hU (oTwoUpper H), y * k * y⁻¹ ∈ autI hU (oTwoUpper H) := by
  intro hDK
  apply hN
  refine borelL_le_normalizer_of_autI_ch615 hU fun y hy k hk => ?_
  have h := c.hyp.toHyp5_0_1
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    c.hH.1.1.trans (le_normalizer_oTwoUpper H)
  have hDS := Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L) (hD.1.trans inf_le_right)
  obtain ⟨b, hb, rfl⟩ := (mem_autI hU).mp hy
  have hb' : (b : G) ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
    rw [h.borelL_eq_sup hD]
    exact hb
  rw [hDS] at hb'
  obtain ⟨d, hd, r, hr, hdr⟩ := hb'
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hdN : d ∈ Subgroup.normalizer (UX615 T L H : Set G) := hXN (Subgroup.mem_sup_left (hD.1 hd))
  have hrN : r ∈ Subgroup.normalizer (UX615 T L H : Set G) :=
    hXN (Subgroup.mem_sup_right (c.hH.1.1 hr.1))
  have e : b = ⟨d, hdN⟩ * ⟨r, hrN⟩ := Subtype.ext hdr.symm
  rw [e, map_mul]
  have h1 : convI hU ⟨r, hrN⟩ * k * (convI hU ⟨r, hrN⟩)⁻¹ ∈ autI hU (oTwoUpper H) :=
    C124.autI_conj_mem hU hTK _ (convI_mem_autI hU hr.1 hrN) _ hk
  have h2 := hDK _ (convI_mem_autI hU hd hdN) _ h1
  have e2 : convI hU ⟨d, hdN⟩ * convI hU ⟨r, hrN⟩ * k * (convI hU ⟨d, hdN⟩ * convI hU ⟨r, hrN⟩)⁻¹ =
      convI hU ⟨d, hdN⟩ * (convI hU ⟨r, hrN⟩ * k * (convI hU ⟨r, hrN⟩)⁻¹) *
        (convI hU ⟨d, hdN⟩)⁻¹ := by group
  rw [e2]
  exact h2

theorem autI_hall_mul_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    ∀ y ∈ autI hU T, ∀ δ ∈ autI hU D, ∃ δ' ∈ autI hU D, ∃ y' ∈ autI hU T, y * δ = δ' * y' := by
  intro y hy δ hδ
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  obtain ⟨t, ht, rfl⟩ := (mem_autI hU).mp hy
  obtain ⟨d, hd, rfl⟩ := (mem_autI hU).mp hδ
  obtain ⟨d', hd', t', ht', he⟩ := (c.hall_mul_ch615 hD).1 t ht d hd
  have hd'N : d' ∈ Subgroup.normalizer (UX615 T L H : Set G) :=
    hXN (Subgroup.mem_sup_left (hD.1 hd'))
  have ht'N : t' ∈ Subgroup.normalizer (UX615 T L H : Set G) :=
    hXN (Subgroup.mem_sup_right (c.hH.1.1 ht'))
  refine ⟨_, convI_mem_autI hU hd' hd'N, _, convI_mem_autI hU ht' ht'N, ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext he

theorem autI_hall_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H))
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) :
    IsCyclic (autI hU D) ∧ Nat.card (autI hU D) = 2 ^ n - 1 := by
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hDN : D ≤ Subgroup.normalizer (UX615 T L H : Set G) := hD.1.trans (le_sup_left.trans hXN)
  obtain ⟨hcyc, hcard⟩ := c.hall_ch615 hD
  have hker : (convHom hU D hDN).ker = ⊥ := by
    rw [ker_convHom, c.hall_inf_centralizer_ch615 hD, Subgroup.bot_subgroupOf]
  have hinj : Function.Injective (convHom hU D hDN) := (MonoidHom.ker_eq_bot_iff _).mp hker
  have e : ↥D ≃* ↥(autI hU D) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (range_convHom hU D hDN))
  exact ⟨isCyclic_of_surjective e.toMonoidHom e.surjective,
    by rw [← hcard]; exact (Nat.card_congr e.toEquiv).symm⟩

end Cx615C

end CFSG.Quasithin.H13
