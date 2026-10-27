module

public import CFSG.Quasithin.EmptyFaithful.SBd14Ctx
public import CFSG.Quasithin.EmptyFaithful.SBd7Case3

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

section Main2

theorem RestHyp.centralizer_S (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) {t' : G}
    (ht'T : t' ∈ T) (hc1 : B6.conjSub t' V₁ = V₂) (hc2 : B6.conjSub t' V₂ = V₁) :
    ∀ w ∈ Sgp153 T V₁, (∀ y ∈ oTwoUpper (Yp ⊓ L), w * y = y * w) →
      (∀ y ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)), w * y = y * w) → w = 1 := by
  classical
  intro w hwS hwYL hwD
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := hyp.qtfe.sylow.1.to_le inf_le_left
  set X : Subgroup G := Sgp153 T V₁ ⊓ Subgroup.centralizer
    ((oTwoUpper (Yp ⊓ L) ⊔ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) : Subgroup G) : Set G) with hX
  have hXS : X ≤ Sgp153 T V₁ := inf_le_left
  have hSYLD : Sgp153 T V₁ ≤ Subgroup.normalizer
      ((oTwoUpper (Yp ⊓ L) ⊔ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) : Subgroup G) : Set G) :=
    fun s hs => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨r.S_le_YL hs, r.S_le_D ht'T hs⟩
  have hXN : Sgp153 T V₁ ≤ Subgroup.normalizer (X : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs,
      S153F.mem_normalizer_centralizer_of_mem_normalizer (hSYLD hs)⟩
  by_contra hw1
  have hwX : w ∈ X := by
    refine ⟨hwS, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hle : oTwoUpper (Yp ⊓ L) ⊔ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) ≤
        Subgroup.centralizer ({w} : Set G) :=
      sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hwYL y hy).symm)
        (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hwD y hy).symm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hX1 : X ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hwX
    exact hw1 hwX
  obtain ⟨n, hnX, hn1, hnS⟩ := SBd7.exists_central_of_normal hS2 hXS hXN hX1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hS2 ⟨n, hXS hnX⟩
  have hk' : orderOf n = 2 ^ k := by rw [← Subgroup.orderOf_coe] at hk; exact hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hn1 (orderOf_eq_one_iff.mp (by simpa using hk'))
  have hdvd : 2 ∣ orderOf n := by rw [hk']; exact dvd_pow_self 2 hk0
  have hne0 : orderOf n ≠ 0 := by rw [hk']; positivity
  set n' : G := n ^ (orderOf n / 2) with hn'
  have hn'ord : orderOf n' = 2 := orderOf_pow_orderOf_div hne0 hdvd
  have hn'X : n' ∈ X := Subgroup.pow_mem _ hnX _
  have hn'S : ∀ s ∈ Sgp153 T V₁, s * n' * s⁻¹ = n' := by
    intro s hs
    have : s * n * s⁻¹ = n := hnS s hs
    calc s * n' * s⁻¹ = (s * n * s⁻¹) ^ (orderOf n / 2) := by rw [hn', conj_pow]
      _ = n' := by rw [this]
  have hn'sq : n' * n' = 1 := by
    have : n' ^ 2 = 1 := by rw [← hn'ord]; exact pow_orderOf_eq_one n'
    rwa [pow_two] at this
  have hΩ : n' ∈ VZ T M := by
    have h8 := (hyp.lemma_15_3_8 D0).1
    have hmem : n' ∈ omegaOneCenterOf (T ⊓ Subgroup.normalizer (V₁ : Set G)) :=
      Subgroup.subset_closure ⟨⟨hXS hn'X, Subgroup.mem_centralizer_iff.mpr fun s hs => by
        have := hn'S s hs
        exact mul_inv_eq_iff_eq_mul.mp this⟩, by rw [pow_two]; exact hn'sq⟩
    rw [h8] at hmem
    exact hmem.1
  have hVab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb => by
    have := hyp.elemAbelian.1
    exact setLike_mul_comm ha hb
  have hfix := SBd7.fixed_in_V_false (V := VZ T M) (Vc := V₁) (Vn := V₂)
    (YL := oTwoUpper (Yp ⊓ L)) (YC := B6.conjSub t' (oTwoUpper (Yp ⊓ L))) D0.sup hVab D0.card₁
    D0.card₂ r.V_sq
    (fun y hy => Subgroup.mem_centralizer_iff.mpr fun v hv => (r.h2 y hy v hv).symm)
    (fun y hy => (r.Yp_le_V h113).2 ((oTwoUpper_le _ hy).1))
    (fun y hy => Subgroup.mem_centralizer_iff.mpr fun v hv => (r.D_cV₂ hc1 y hy v hv).symm)
    (fun y hy => (r.Yp_le_V h113).1 (r.D_le_Yp ht'T hy))
    (fun K hK => (Subgroup.closure_le K).mpr fun y hy => hK y (mem_oTwoUpper_of_odd hy.1 hy.2) hy.2)
    (RestHyp.D_gen t')
    (by
      obtain ⟨y₂, hy₂, y₁, hy₁, ⟨v₂, hv₂, hne⟩, -⟩ := r.exists_pair hc2
      intro hb
      have hmem := Subgroup.commutator_mem_commutator (D0.le₂ hv₂) hy₂
      rw [hb, Subgroup.mem_bot] at hmem
      exact hne (by
        have : v₂ * y₂ * v₂⁻¹ * y₂⁻¹ = 1 := hmem
        calc y₂ * v₂ = (v₂ * y₂ * v₂⁻¹ * y₂⁻¹)⁻¹ * (v₂ * y₂) := by group
          _ = v₂ * y₂ := by rw [this]; group))
    (by
      obtain ⟨y₂, hy₂, y₁, hy₁, -, ⟨v₁, hv₁, hne⟩⟩ := r.exists_pair hc2
      intro hb
      have hmem := Subgroup.commutator_mem_commutator (D0.le₁ hv₁) hy₁
      rw [hb, Subgroup.mem_bot] at hmem
      exact hne (by
        have : v₁ * y₁ * v₁⁻¹ * y₁⁻¹ = 1 := hmem
        calc y₁ * v₁ = (v₁ * y₁ * v₁⁻¹ * y₁⁻¹)⁻¹ * (v₁ * y₁) := by group
          _ = v₁ * y₁ := by rw [this]; group))
    n' hΩ
    (fun y hy => by
      have := Subgroup.mem_centralizer_iff.mp hn'X.2 y (Subgroup.mem_sup_left hy)
      calc y * n' * y⁻¹ = n' * y * y⁻¹ := by rw [← this]
        _ = n' := by group)
    (fun y hy => by
      have := Subgroup.mem_centralizer_iff.mp hn'X.2 y (Subgroup.mem_sup_right hy)
      calc y * n' * y⁻¹ = n' * y * y⁻¹ := by rw [← this]
        _ = n' := by group)
  rw [hfix] at hn'ord
  simp at hn'ord

end Main2

section Final

theorem RestHyp.V₁_eq_center (r : RestHyp T Mc M V₁ V₂ Yp I L t) (h113 : StageLemma14113) :
    V₁ = centerOf L := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  obtain ⟨t', ht'T, ht'S, hc1, hc2, ht'2⟩ := exists_swap hyp D0
  obtain ⟨d, hdD, hd3, hdN0⟩ := r.exists_outer h113 ht'T hc2
  have hdYp : d ∈ Yp := r.D_le_Yp ht'T hdD
  have hdL : d ∈ Subgroup.normalizer (L : Set G) := r.Yp_le_L hdYp
  have hdQ : d ∈ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) := r.Yp_le_Q hdYp
  have hdV : ∀ v ∈ V₂, d * v * d⁻¹ = v := fun v hv => by
    have := r.D_cV₂ hc1 d hdD v hv
    calc d * v * d⁻¹ = v * d * d⁻¹ := by rw [this]
      _ = v := by group
  obtain ⟨hA, hE⟩ := lie_outer r.ctx.c33.quasisimple r.ctx.c33.center_eq r.sylow r.hn2 hdL hdQ hd3
    hdN0 r.V₂_le_Q (fun v hv q hq => r.V₂_cQ v hv q hq) D0.card₂ (r.V₂_inf_Z h113) hdV
  have hQD : Sgp153 T V₁ ⊓ L ≤ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) := by
    refine hE.trans (Subgroup.commutator_le.mpr fun q hq w hw => ?_)
    have hwD : w ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) :=
      (Subgroup.zpowers_le.mpr hdD) hw
    have hqw : q * w * q⁻¹ ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)) :=
      ((Subgroup.mem_normalizer_iff.mp (r.S_le_D ht'T ((inf_le_left : Sgp153 T V₁ ⊓ L ≤ _) hq)) w).mp
        hwD)
    have : ⁅q, w⁆ = (q * w * q⁻¹) * w⁻¹ := rfl
    rw [this]
    exact Subgroup.mul_mem _ hqw (Subgroup.inv_mem _ hwD)
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
  have hQt : ∀ q ∈ Sgp153 T V₁ ⊓ L, t' * q * t'⁻¹ ∈ Sgp153 T V₁ ⊓ L := by
    intro q hq
    have : q ∈ B6.conjSub t'⁻¹ (Sgp153 T V₁ ⊓ L) := by rw [hQ'eq]; exact hq
    simpa using B6.mem_conjSub.mp this
  have hLie := SBd9.lieL3_of_psl (n := 2) (by norm_num) r.ctx.c33.quasisimple
    r.ctx.c33.center_eq r.sylow r.hn2
  have hZQ : centerOf L ≤ Sgp153 T V₁ ⊓ L := hLie.center_le
  apply le_antisymm
  ·
    intro v hv
    have hv2 : t'⁻¹ * v * t' ∈ V₂ := B6.mem_conjSub.mp (hc2 ▸ hv)
    have hvQ : v ∈ Sgp153 T V₁ ⊓ L := by
      have := hQt _ (r.V₂_le_Q hv2)
      simpa [mul_assoc] using this
    exact ⟨hvQ.2, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (r.h1 hv) l hl)⟩
  ·
    intro z hz
    have hzQ : z ∈ Sgp153 T V₁ ⊓ L := hZQ hz
    set z' : G := t' * z * t'⁻¹ with hz'
    have hz'Q : z' ∈ Sgp153 T V₁ ⊓ L := hQt z hzQ
    have hz'D : ∀ y ∈ B6.conjSub t' (oTwoUpper (Yp ⊓ L)), y * z' = z' * y := by
      intro y hy
      have hy₀ : t'⁻¹ * y * t' ∈ oTwoUpper (Yp ⊓ L) := B6.mem_conjSub.mp hy
      have hy₀L : t'⁻¹ * y * t' ∈ L := (oTwoUpper_le _ hy₀).2
      have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hy₀L
      calc y * z' = t' * ((t'⁻¹ * y * t') * z) * t'⁻¹ := by simp [hz', mul_assoc]
        _ = t' * (z * (t'⁻¹ * y * t')) * t'⁻¹ := by rw [h1]
        _ = z' * y := by simp [hz', mul_assoc]
    have hcomm : ⁅z', d⁆ ∈ V₂ ⊔ centerOf L := by
      have : ⁅z', d⁆ = 1 := by
        have h := hz'D d hdD
        calc ⁅z', d⁆ = (z' * d) * z'⁻¹ * d⁻¹ := rfl
          _ = (d * z') * z'⁻¹ * d⁻¹ := by rw [← h]
          _ = 1 := by group
      rw [this]
      exact Subgroup.one_mem _
    have hz'mem := hA z' hz'Q hcomm
    have hcomm2 : ∀ a ∈ V₂, ∀ b ∈ centerOf L, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp hb.2 a ((r.V₂_le_Q ha).2)
    obtain ⟨v, hv, w, hw, hvw⟩ := mem_sup_of_commute' hcomm2 hz'mem
    have hwQ : w ∈ Sgp153 T V₁ ⊓ L := hZQ hw
    have hwv : w = v⁻¹ * z' := by rw [hvw]; group
    have hw1 : w = 1 := by
      refine r.centralizer_S h113 ht'T hc1 hc2 w ((inf_le_left : Sgp153 T V₁ ⊓ L ≤ _) hwQ)
        (fun y hy => ?_) (fun y hy => ?_)
      · exact (Subgroup.mem_centralizer_iff.mp hw.2 y ((oTwoUpper_le _ hy).2)).symm
      · have hyv : Commute y v := r.D_cV₂ hc1 y hy v hv
        have hyz : Commute y z' := hz'D y hy
        have hyw : Commute y w := hwv ▸ (hyv.inv_right.mul_right hyz)
        exact hyw.eq.symm
    have hz'v : z' = v := by rw [hvw, hw1, mul_one]
    have hz'V₂ : z' ∈ V₂ := hz'v ▸ hv
    have h1 : z' ∈ B6.conjSub t' V₁ := by rw [hc1]; exact hz'V₂
    have h2 := B6.mem_conjSub.mp h1
    simpa [hz', mul_assoc] using h2

end Final

end CFSG.Quasithin.SBd14
