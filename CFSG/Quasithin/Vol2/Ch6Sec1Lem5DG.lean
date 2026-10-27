module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DA
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113NA5K
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QJ

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615B

theorem borelL_le_normalizer_thompsonJ_ch615 (c : Cx615B G T M L V H n) :
    borelL T L ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  have h := c.hyp
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hS := h.toHyp5_0_1.setting516 hD h.module
  obtain ⟨F, _, _, _, -, ψ, Yc, hc⟩ := c.nat.exists_qcoord c.toCx615.isSylowTwoOf_inf
  have hVR : V ≤ reducedAggregate (L ⊔ T) := c.V_eq.le
  set C := (L ⊔ T) ⊓ Subgroup.centralizer (reducedAggregate (L ⊔ T) : Set G) with hC
  have hCT : C ≤ T := hS.centralizer_le
  set R := (T ⊓ L) ⊔ C with hR
  have hRT : R ≤ T := sup_le inf_le_left hCT
  have hJR : thompsonJ T ≤ R := by
    refine iSup₂_le fun A hA => fun a ha => ?_
    obtain ⟨s, hs, has⟩ := hS.exists_mul_of_isMaxElemAbelian hVR c.V_facts.2.1 hc hA ha
    have hasT : a * s⁻¹ ∈ T := T.mul_mem (hA.1 ha) (T.inv_mem hs.1)
    have e1 : a = a * s⁻¹ * s := by group
    rw [e1]
    exact R.mul_mem (Subgroup.mem_sup_right ⟨Subgroup.mem_sup_right hasT, has⟩)
      (Subgroup.mem_sup_left hs)
  have hBL : borelL T L ≤ L := inf_le_left
  have hBTL : borelL T L ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := inf_le_right
  have hBC : borelL T L ≤ Subgroup.normalizer (C : Set G) := fun d hd =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (Subgroup.mem_sup_left (hBL hd)),
        B6.le_normalizer_centralizer hS.reduced.2.1 (Subgroup.mem_sup_left (hBL hd))⟩
  intro d hd
  have hdR : d ∈ Subgroup.normalizer (R : Set G) := by
    have h1 := hBTL hd
    have h2 := hBC hd
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    rw [hR, Subgroup.map_sup, h1, h2]
  rw [← B6.thompsonJ_eq_of_le hJR hRT]
  exact mem_normalizer_thompsonJ_of_mem_normalizer hdR

theorem eq_one_of_centralizes_Z_ch615 (c : Cx615B G T M L V H n) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {d : G} (hd : d ∈ D)
    (hdZ : ∀ y ∈ quasithinOmegaOneCenter T, d * y = y * d) : d = 1 := by
  by_contra hd1
  have hodd : Odd (orderOf d) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hd)
  apply c.ZL
  intro z hz
  refine c.CZd d (hD.1 hd) hodd hd1 ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  rw [Set.mem_singleton_iff.mp hg]
  exact hdZ z hz.1

theorem borelL_le_normalizer_baum_ch615 (c : Cx615B G T M L V H n) :
    borelL T L ≤ Subgroup.normalizer (baum T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have h := c.hyp.toHyp5_0_1
  have hT2 : IsPGroup 2 T := h.sylow.1
  rw [← h.borelL_eq_sup hD]
  refine sup_le ?_ (inf_le_left.trans (Subgroup.le_normalizer.trans
    (normalizer_le_normalizer_baum T)))
  have hDo : ∀ d ∈ D, Odd (orderOf d) := fun d hd =>
    Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hd)
  have hTo : ∀ x ∈ T, ∃ k : ℕ, orderOf x ∣ 2 ^ k := by
    intro x hx
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx⟩
    exact ⟨k, orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)⟩
  have hDZ : ∀ d ∈ D, (∀ y ∈ quasithinOmegaOneCenter T, d * y = y * d) → d = 1 :=
    fun d hd hc => c.eq_one_of_centralizes_Z_ch615 hD hd hc
  have hJT : thompsonJ T ≤ T := B6.thompsonJ_le T
  have hZT : quasithinOmegaOneCenter T ≤ T := fun y hy => (mem_quasithinOmegaOneCenter_iff.mp hy).1
  have hZe : IsElemAbelian 2 (quasithinOmegaOneCenter T) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp
        (mem_quasithinOmegaOneCenter_iff.mp b.2).2.1 a
          (mem_quasithinOmegaOneCenter_iff.mp a.2).1)⟩⟩,
      fun y hy => (mem_quasithinOmegaOneCenter_iff.mp hy).2.2⟩
  have hJZ : thompsonJ T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun j hj => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hy).2.1 j (hJT hj)).symm
  have hZE := le_omegaOneCenterOf_thompsonJ hZe hZT hJZ
  have hDE : D ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
    (hD.1.trans c.borelL_le_normalizer_thompsonJ_ch615).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ T))
  have hTE : T ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) := fun t ht =>
    A4.normalizer_le_normalizer_omegaOneCenterOf (thompsonJ T)
      (mem_normalizer_thompsonJ_of_mem_normalizer (Subgroup.le_normalizer ht))
  have hYE : D ⊔ T ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
    sup_le hDE hTE
  have hDT : ∀ t ∈ T, ∀ d ∈ D, ∃ d' ∈ D, ∃ t' ∈ T, t * d = d' * t' := by
    intro t ht d hd
    have hBT := Subgroup.coe_mul_of_right_le_normalizer_left (borelL T L) T
      h.T_le_normalizer_borel
    have hDS := Subgroup.coe_mul_of_left_le_normalizer_right D (T ⊓ L)
      (hD.1.trans inf_le_right)
    have h1 : t * d ∈ ((borelL T L ⊔ T : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right ht) (Subgroup.mem_sup_left (hD.1 hd))
    rw [hBT] at h1
    obtain ⟨y, hy, s, hs, hys⟩ := h1
    have hys' : y * s = t * d := hys
    have hy' : y ∈ ((D ⊔ (T ⊓ L) : Subgroup G) : Set G) := by
      rw [h.borelL_eq_sup hD]
      exact hy
    rw [hDS] at hy'
    obtain ⟨d', hd', r, hr, hdr⟩ := hy'
    have hdr' : d' * r = y := hdr
    exact ⟨d', hd', r * s, T.mul_mem (Subgroup.mem_inf.mp hr).1 hs,
      by rw [← hys', ← hdr', mul_assoc]⟩
  have key : ∀ d ∈ D, ∀ b ∈ baum T, d * b * d⁻¹ ∈ baum T := by
    intro d hd b hb
    have hbT : b ∈ T := hb.1
    have hbE : b ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) := hb.2
    have hcE : d * b * d⁻¹ ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_centralizer hDE hd) b).mp hbE
    obtain ⟨d', hd', t', ht', he⟩ := hDT b hbT d⁻¹ (D.inv_mem hd)
    have hd'' : d * d' ∈ D := D.mul_mem hd hd'
    have hdbd : d * b * d⁻¹ = d * d' * t' := by rw [mul_assoc d b, he, mul_assoc]
    set φ := A4.actionOn (omegaOneCenterOf (thompsonJ T)) (D ⊔ T) hYE with hφ
    have hφeq : φ ⟨d * d', Subgroup.mem_sup_left hd''⟩ =
        φ ⟨t'⁻¹, Subgroup.mem_sup_right (T.inv_mem ht')⟩ := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      have hx' : t'⁻¹ * (x : G) * t'⁻¹⁻¹ ∈ omegaOneCenterOf (thompsonJ T) :=
        (Subgroup.mem_normalizer_iff.mp (hTE (T.inv_mem ht')) x).mp x.2
      have h1 : d * d' = d * b * d⁻¹ * t'⁻¹ := by rw [hdbd, mul_inv_cancel_right]
      have h2 := Subgroup.mem_centralizer_iff.mp hcE _ hx'
      show d * d' * x * (d * d')⁻¹ = t'⁻¹ * x * t'⁻¹⁻¹
      calc d * d' * x * (d * d')⁻¹ =
          (d * b * d⁻¹) * (t'⁻¹ * x * t'⁻¹⁻¹) * (d * b * d⁻¹)⁻¹ := by rw [h1]; group
        _ = (t'⁻¹ * x * t'⁻¹⁻¹) * (d * b * d⁻¹) * (d * b * d⁻¹)⁻¹ := by rw [h2]
        _ = t'⁻¹ * x * t'⁻¹⁻¹ := by group
    have hord : orderOf (φ ⟨d * d', Subgroup.mem_sup_left hd''⟩) = 1 := by
      have h1 : orderOf (φ ⟨d * d', Subgroup.mem_sup_left hd''⟩) ∣ orderOf (d * d') := by
        have := orderOf_map_dvd φ ⟨d * d', Subgroup.mem_sup_left hd''⟩
        rwa [Subgroup.orderOf_mk] at this
      obtain ⟨k, hk⟩ := hTo _ (T.inv_mem ht')
      have h2 : orderOf (φ ⟨d * d', Subgroup.mem_sup_left hd''⟩) ∣ 2 ^ k := by
        rw [hφeq]
        have := orderOf_map_dvd φ ⟨t'⁻¹, Subgroup.mem_sup_right (T.inv_mem ht')⟩
        rw [Subgroup.orderOf_mk] at this
        exact this.trans hk
      have hcop : Nat.Coprime (orderOf (d * d')) (2 ^ k) :=
        Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hDo _ hd''))
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    have hcE' : d * d' ∈ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
      (A4.actionOn_eq_one_iff hYE _).mp (orderOf_eq_one_iff.mp hord)
    have h1 : d * d' = 1 := hDZ _ hd'' fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hcE' y (hZE hy)).symm
    have ht'eq : d * b * d⁻¹ = t' := by rw [hdbd, h1, one_mul]
    rw [ht'eq] at hcE
    rw [ht'eq]
    exact ⟨ht', hcE⟩
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key d hd b, fun hb => ?_⟩
  have h1 := key d⁻¹ (D.inv_mem hd) _ hb
  simpa [mul_assoc] using h1

end Cx615B

end CFSG.Quasithin.H13
