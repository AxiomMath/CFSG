module

public import CFSG.Quasithin.EmptyFaithful.SBd14Mid

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.Q_le_YL_D (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) {t' : G}
    (ht'T : t' ∈ T) (hc1 : B6.conjSub t' V₁ = V₂) (hc2 : B6.conjSub t' V₂ = V₁) :
    Sgp153 T V₁ ⊓ L ≤ oTwoUpper (Yp ⊓ L) ∧
      Sgp153 T V₁ ⊓ L ≤ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) := by
  classical
  have D0 := r.ctx.hyp.decomp
  obtain ⟨d, hdD, hd3, hdN0⟩ := r.exists_outer h113 ht'T hc2
  have hdYp : d ∈ Yp := r.D_le_Yp ht'T hdD
  have hdL : d ∈ Subgroup.normalizer (L : Set G) := r.Yp_le_L hdYp
  have hdQ : d ∈ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := r.Yp_le_Q hdYp
  have hdV : ∀ v ∈ V₂, d * v * d⁻¹ = v := fun v hv => by
    have := r.D_cV₂ hc1 d hdD v hv
    calc d * v * d⁻¹ = v * d * d⁻¹ := by rw [this]
      _ = v := by group
  obtain ⟨-, hE⟩ := lie_outer r.ctx.c33.quasisimple r.ctx.c33.center_eq r.sylow r.hn2 hdL hdQ hd3
    hdN0 r.V₂_le_Q (fun v hv q hq => r.V₂_cQ v hv q hq) D0.card₂ (r.V₂_inf_Z h113) hdV
  have hQD : Sgp153 T V₁ ⊓ L ≤ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) := by
    refine hE.trans (Subgroup.commutator_le.mpr fun q hq w hw => ?_)
    have hwD : w ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) := (Subgroup.zpowers_le.mpr hdD) hw
    have hqw : q * w * q⁻¹ ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) :=
      ((Subgroup.mem_normalizer_iff.mp (r.S_le_D ht'T ((inf_le_left : Sgp153 T V₁ ⊓ L ≤ _) hq)) w).mp
        hwD)
    have : ⁅q, w⁆ = (q * w * q⁻¹) * w⁻¹ := rfl
    rw [this]
    exact Subgroup.mul_mem _ hqw (Subgroup.inv_mem _ hwD)
  refine ⟨?_, hQD⟩
  have hQ2 : IsPGroup 2 ↥(Sgp153 T V₁ ⊓ L) := r.sylow.2.1
  have hQ'le : B6.conjSub t'⁻¹ (Sgp153 T V₁ ⊓ L) ≤ oTwoUpper (Yp ⊓ L) := by
    intro x hx
    have h1 : (t'⁻¹)⁻¹ * x * t'⁻¹ ∈ Sgp153 T V₁ ⊓ L := B6.mem_conjSub.mp hx
    have h2 : t' * x * t'⁻¹ ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) := hQD (by simpa using h1)
    have h3 := B6.mem_conjSub.mp h2
    simpa [mul_assoc] using h3
  have hQ'2 : IsPGroup 2 ↥(B6.conjSub t'⁻¹ (Sgp153 T V₁ ⊓ L)) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    exact IsPGroup.of_card (n := n) (by rw [card_conjSub', hn])
  have hQ'Q : B6.conjSub t'⁻¹ (Sgp153 T V₁ ⊓ L) ≤ Sgp153 T V₁ ⊓ L :=
    r.le_Q_of_two (hQ'le.trans r.YL_le_B) hQ'2
  have hQ'eq : B6.conjSub t'⁻¹ (Sgp153 T V₁ ⊓ L) = Sgp153 T V₁ ⊓ L :=
    Subgroup.eq_of_le_of_card_ge hQ'Q (by rw [card_conjSub'])
  exact hQ'eq.symm.le.trans hQ'le

theorem RestHyp.centralizer_Q_le (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    L ⊓ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ V₂ ⊔ V₁ := by
  classical
  obtain ⟨K, _, _, _, ρ, hK4, hmod⟩ := exists_borelModel r.ctx.c33.center_eq r.sylow r.hn2
  have hV : V₁ = centerOf L := r.V₁_eq_center h113
  have hV₂C : ∀ v ∈ V₂, v ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) :=
    fun v hv => Subgroup.mem_centralizer_iff.mpr fun q hq => (r.V₂_cQ v hv q hq).symm
  have hex : ∀ v : ↥V₂, ∃ c : K,
      ρ ⟨(v : G), (r.V₂_le_Q v.2).2⟩ = proj 3 K (SBd9.corner c) := fun v =>
    SBd9.exists_corner_of_mem_centralizer (hmod.mem_centralizer (r.V₂_le_Q v.2).2 (hV₂C v v.2))
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro v w hvw
    have h12 : ρ ⟨(v : G), (r.V₂_le_Q v.2).2⟩ = ρ ⟨(w : G), (r.V₂_le_Q w.2).2⟩ := by
      rw [hf, hf, hvw]
    have hyL : (v : G)⁻¹ * (w : G) ∈ L := L.mul_mem (L.inv_mem (r.V₂_le_Q v.2).2) (r.V₂_le_Q w.2).2
    have h1 : ρ ⟨(v : G)⁻¹ * (w : G), hyL⟩ = 1 := by
      have e : (⟨(v : G)⁻¹ * (w : G), hyL⟩ : ↥L) =
          (⟨(v : G), (r.V₂_le_Q v.2).2⟩ : ↥L)⁻¹ * ⟨(w : G), (r.V₂_le_Q w.2).2⟩ := rfl
      rw [e, map_mul, map_inv, h12, inv_mul_cancel]
    have h2 : (v : G)⁻¹ * (w : G) ∈ centerOf L := (hmod.eq_one_iff ⟨_, hyL⟩).mp h1
    have h3 := r.V₂_inf_Z h113 _ (V₂.mul_mem (V₂.inv_mem v.2) w.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hbij : Function.Bijective f := by
    have : Finite ↥V₂ := Nat.finite_of_card_ne_zero (by rw [r.ctx.hyp.decomp.card₂]; norm_num)
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK4]; norm_num)
    exact (Nat.bijective_iff_injective_and_card f).mpr ⟨hfinj, by rw [r.ctx.hyp.decomp.card₂, hK4]⟩
  rintro x ⟨hxL, hx⟩
  obtain ⟨c, hc⟩ := SBd9.exists_corner_of_mem_centralizer (hmod.mem_centralizer hxL hx)
  obtain ⟨v, hv⟩ := hbij.2 c
  have hvL : (v : G) ∈ L := (r.V₂_le_Q v.2).2
  have hxv : x * (v : G)⁻¹ ∈ L := L.mul_mem hxL (L.inv_mem hvL)
  have h1 : ρ ⟨x * (v : G)⁻¹, hxv⟩ = 1 := by
    have e : (⟨x * (v : G)⁻¹, hxv⟩ : ↥L) = ⟨x, hxL⟩ * (⟨(v : G), hvL⟩ : ↥L)⁻¹ := rfl
    rw [e, map_mul, map_inv, hc, hf v, hv, mul_inv_cancel]
  have h2 : x * (v : G)⁻¹ ∈ centerOf L := (hmod.eq_one_iff ⟨_, hxv⟩).mp h1
  rw [← hV] at h2
  have : x = (x * (v : G)⁻¹) * (v : G) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left v.2)

theorem RestHyp.exists_of_mem_centralizer_Q (r : RestHyp T Mc M V₁ V₂ Yp I L t)
    (h113 : StageLemma14113) {s : G} (hsS : s ∈ Sgp153 T V₁)
    (hsQ : s ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G)) :
    ∃ v ∈ V₂, ∃ c ∈ Sgp153 T V₁ ⊓ Subgroup.centralizer (L : Set G), s = v * c := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  have hLie := SBd9.lieL3_of_psl (n := 2) (by norm_num) r.ctx.c33.quasisimple
    r.ctx.c33.center_eq r.sylow r.hn2
  obtain ⟨x, hxL, hx⟩ := hLie.inner s (r.S_le_L hsS) hsQ
  have hV₁S : V₁ ≤ Sgp153 T V₁ := le_inf (D0.le₁.trans hyp.VZ_le_T) Subgroup.le_normalizer
  have hV₁le : V₁ ≤ Sgp153 T V₁ ⊓ Subgroup.centralizer (L : Set G) := le_inf hV₁S r.h1
  set c : G := s * x⁻¹ with hc
  have hcL : ∀ y ∈ L, y * c = c * y := by
    intro y hy
    have h1 := hx y hy
    calc y * c = s * (s⁻¹ * y * s) * x⁻¹ := by rw [hc]; group
      _ = s * (x⁻¹ * y * x) * x⁻¹ := by rw [h1]
      _ = c * y := by rw [hc]; group
  have hxc : x = c⁻¹ * s := by rw [hc]; group
  have hxC : x ∈ Subgroup.centralizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hqc : Commute q c := hcL q hq.2
    have hqs : Commute q s := Subgroup.mem_centralizer_iff.mp hsQ q hq
    rw [hxc]
    exact ((hqc.inv_right).mul_right hqs).eq
  have hxQ : x ∈ Sgp153 T V₁ ⊓ L := hLie.cent ⟨hxL, hxC⟩
  have hcS : c ∈ Sgp153 T V₁ := Subgroup.mul_mem _ hsS (Subgroup.inv_mem _ ((inf_le_left : Sgp153 T V₁ ⊓ L ≤ Sgp153 T V₁) hxQ))
  have hcSC : c ∈ Sgp153 T V₁ ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨hcS, Subgroup.mem_centralizer_iff.mpr hcL⟩
  have hcomm : ∀ a ∈ V₂, ∀ b ∈ V₁, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (r.h1 hb) a (r.V₂_le_Q ha).2
  obtain ⟨v, hv, v₁, hv₁, hxv⟩ := mem_sup_of_commute' hcomm (r.centralizer_Q_le h113 ⟨hxL, hxC⟩)
  refine ⟨v, hv, c * v₁, Subgroup.mul_mem _ hcSC (hV₁le hv₁), ?_⟩
  have hs : s = c * x := by rw [hc]; group
  calc s = c * x := hs
    _ = c * (v * v₁) := by rw [hxv]
    _ = (c * v) * v₁ := by group
    _ = (v * c) * v₁ := by rw [← hcL v (r.V₂_le_Q hv).2]
    _ = v * (c * v₁) := by group

theorem RestHyp.CSL_eq (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    Sgp153 T V₁ ⊓ Subgroup.centralizer (L : Set G) = V₁ := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  obtain ⟨t', ht'T, -, hc1, hc2, -⟩ := exists_swap hyp D0
  have hQD := (r.Q_le_YL_D h113 ht'T hc1 hc2).2
  have hTS := Hyp153.T_le_normalizer_Sgp153 hyp D0 ht'T
  have hV₁S : V₁ ≤ Sgp153 T V₁ := le_inf (D0.le₁.trans hyp.VZ_le_T) Subgroup.le_normalizer
  have hV₁le : V₁ ≤ Sgp153 T V₁ ⊓ Subgroup.centralizer (L : Set G) := le_inf hV₁S r.h1
  set CSL : Subgroup G := Sgp153 T V₁ ⊓ Subgroup.centralizer (L : Set G) with hCSL
  set CSD : Subgroup G := Sgp153 T V₁ ⊓
    Subgroup.centralizer ((B6.conjSub t' (oTwoUpper (Yp ⊓ L)) : Subgroup G) : Set G) with hCSD
  have ha : ∀ s ∈ CSD, ∃ v ∈ V₂, ∃ c ∈ CSL, s = v * c := fun s hs =>
    r.exists_of_mem_centralizer_Q h113 hs.1
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hQD) hs.2)
  have hb : ∀ s ∈ CSD, s ∈ CSL → s = 1 := fun s hsD hsL =>
    r.centralizer_S h113 ht'T hc1 hc2 s hsD.1
      (fun y hy => (Subgroup.mem_centralizer_iff.mp hsL.2 y (oTwoUpper_le _ hy).2).symm)
      (fun y hy => (Subgroup.mem_centralizer_iff.mp hsD.2 y hy).symm)
  have hc : Nat.card ↥CSL ≤ Nat.card ↥CSD := by
    let f : ↥CSL → ↥CSD := fun s => ⟨t' * s * t'⁻¹, ?_⟩
    · refine Nat.card_le_card_of_injective f fun s s' hss => ?_
      have := congrArg Subtype.val hss
      have h2 : (t' * (s : G) * t'⁻¹) = t' * (s' : G) * t'⁻¹ := this
      exact Subtype.ext (by simpa using h2)
    · refine ⟨(Subgroup.mem_normalizer_iff.mp hTS (s : G)).mp s.2.1,
        Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have hx' : t'⁻¹ * x * t' ∈ oTwoUpper (Yp ⊓ L) := B6.mem_conjSub.mp hx
      have h1 := Subgroup.mem_centralizer_iff.mp s.2.2 _ (oTwoUpper_le _ hx').2
      calc x * (t' * (s : G) * t'⁻¹) = t' * ((t'⁻¹ * x * t') * (s : G)) * t'⁻¹ := by group
        _ = t' * ((s : G) * (t'⁻¹ * x * t')) * t'⁻¹ := by rw [h1]
        _ = (t' * (s : G) * t'⁻¹) * x := by group
  have hd : Nat.card ↥CSD ≤ 4 := by
    have hsel : ∀ s : ↥CSD, ∃ v : ↥V₂, ∃ c ∈ CSL, (s : G) = (v : G) * c := fun s => by
      obtain ⟨v, hv, c, hcC, hsv⟩ := ha s s.2
      exact ⟨⟨v, hv⟩, c, hcC, hsv⟩
    choose g hg using hsel
    have hginj : Function.Injective g := by
      intro s s' hss
      obtain ⟨c, hcC, hsc⟩ := hg s
      obtain ⟨c', hcC', hsc'⟩ := hg s'
      have h1 : (s : G)⁻¹ * s' ∈ CSL := by
        have : (s : G)⁻¹ * s' = c⁻¹ * c' := by
          rw [hsc, hsc', hss]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcC) hcC'
      have h2 : (s : G)⁻¹ * s' ∈ CSD := Subgroup.mul_mem _ (Subgroup.inv_mem _ s.2) s'.2
      exact Subtype.ext (inv_mul_eq_one.mp (hb _ h2 h1))
    have := Nat.card_le_card_of_injective g hginj
    rwa [D0.card₂] at this
  have hV₁card : Nat.card ↥V₁ = 4 := D0.card₁
  exact (Subgroup.eq_of_le_of_card_ge hV₁le (by omega)).symm

end CFSG.Quasithin.SBd14
