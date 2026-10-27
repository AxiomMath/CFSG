module

public import CFSG.Quasithin.EmptyFaithful.Gap6R0D

public section

namespace CFSG.Quasithin

namespace LRed12

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.Gap6

section Abstract

variable {Γ : Type*} [Group Γ] {W : Type*} [CommGroup W] [Finite W]

theorem exists_conj_cube (hW : ∀ w : W, w ^ 2 = 1) (ρ : Γ →* MulAut W)
    (hsolv : Group.IsSolvable ↥ρ.range) (hO : pCoreOf 2 ρ.range = ⊥)
    (hOC : CFSG.pCore 2 ↥ρ.range = ⊥) {t : Γ} (ht : IsTransvection (ρ t)) :
    ∃ g : Γ, (ρ t * ρ (g * t * g⁻¹)) ^ 3 = 1 ∧ ρ t * ρ (g * t * g⁻¹) ≠ 1 := by
  classical
  obtain ⟨ht1, w, hw⟩ := ht
  obtain ⟨𝓗, hb⟩ := exists_blocks hW hsolv hO
  set Y₀ : Subgroup (MulAut W) := Subgroup.closure (transvectionsIn ρ.range) with hY₀
  have hTrans : ∀ g : Γ, ρ (g * t * g⁻¹) ∈ transvectionsIn Y₀ := by
    intro g
    have h1 : IsTransvection (ρ (g * t * g⁻¹)) := by
      rw [map_mul, map_mul, map_inv]
      exact B1.isTransvection_conj ⟨ht1, w, hw⟩ (ρ g)
    exact ⟨Subgroup.subset_closure ⟨⟨_, rfl⟩, h1⟩, h1⟩
  have hts : ρ t * ρ t = 1 := B1.tv_sq hW hw ht1
  have hconj_sq : ∀ g : Γ, ρ (g * t * g⁻¹) * ρ (g * t * g⁻¹) = 1 := by
    intro g
    obtain ⟨hne, w', hw'⟩ := (hTrans g).2
    exact B1.tv_sq hW hw' hne
  have hconj_ne : ∀ g : Γ, ρ (g * t * g⁻¹) ≠ 1 := fun g => (hTrans g).2.1
  have hnc : ∃ g : Γ, ρ t * ρ (g * t * g⁻¹) ≠ ρ (g * t * g⁻¹) * ρ t := by
    by_contra hcon
    push Not at hcon
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let x : ↥ρ.range := ⟨ρ t, t, rfl⟩
    have hx1 : x ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
    have hx2 : x ^ 2 = 1 := by
      apply Subtype.ext
      show ρ t ^ 2 = 1
      rw [pow_two]; exact hts
    have hmem : x ∈ CFSG.pCore 2 ↥ρ.range := by
      rw [CFSG.BaerSuzuki.baer_suzuki_iff]
      intro y
      obtain ⟨g, hg⟩ := y.2
      have hv : ((y * x * y⁻¹ : ↥ρ.range) : MulAut W) = ρ (g * t * g⁻¹) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        simp only [map_mul, map_inv, hg]
        rfl
      have hxy : x * (y * x * y⁻¹) = (y * x * y⁻¹) * x := by
        apply Subtype.ext
        show (x : MulAut W) * ((y * x * y⁻¹ : ↥ρ.range) : MulAut W) =
          ((y * x * y⁻¹ : ↥ρ.range) : MulAut W) * (x : MulAut W)
        rw [hv]
        exact hcon g
      have hy2 : (y * x * y⁻¹) ^ 2 = 1 := by rw [conj_pow, hx2]; simp
      refine isPGroup_closure_of_pairwise_commute ?_ ?_
      · intro a ha b hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · rfl
        · rw [Set.mem_singleton_iff] at hb
          rw [hb]; exact hxy
        · rw [Set.mem_singleton_iff] at ha
          rw [ha]; exact hxy.symm
        · rw [Set.mem_singleton_iff] at ha hb
          rw [ha, hb]
      · intro a ha
        rcases ha with rfl | ha
        · exact hx2
        · rw [Set.mem_singleton_iff] at ha
          rw [ha]; exact hy2
    rw [hOC] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)
  obtain ⟨g, hg⟩ := hnc
  have hT0 : ρ t ∈ transvectionsIn Y₀ := by
    have := hTrans 1
    simpa using this
  obtain ⟨K₁, hK₁, hsK₁⟩ := hb.cover _ hT0
  obtain ⟨K₂, hK₂, hsK₂⟩ := hb.cover _ (hTrans g)
  have hK : K₁ = K₂ := by
    by_contra hne
    exact hg (hb.comm K₁ hK₁ K₂ hK₂ hne _ hsK₁ _ hsK₂)
  subst hK
  have hcube : (ρ t * ρ (g * t * g⁻¹)) ^ 3 = 1 :=
    cube_of_involutions hb hK₁ hsK₁ hsK₂ ht1 (hconj_ne g) hts (hconj_sq g)
  refine ⟨g, hcube, fun h1 => hg ?_⟩
  have h2 : ρ (g * t * g⁻¹) = (ρ t)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : (ρ t)⁻¹ = ρ t := inv_eq_of_mul_eq_one_right hts
  rw [h2, h3]

end Abstract

section Concrete

variable {V : Type*} [CommGroup V] [Finite V] {X Tb : Subgroup (MulAut V)}

theorem exists_three_element (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X)
    (hO2 : pCoreOf 2 X = ⊥) (hsyl : Tb ∈ sylow2Of X)
    (hgen : ∀ W : Subgroup V, (∀ g ∈ X, ∀ z ∈ fixV Tb, g z ∈ W) → W = ⊤)
    {b : MulAut V} (hbJ : b ∈ Jhat X) (hb2 : b ^ 2 = 1)
    (hbC : rk ↥(commSub (fixV (fittingOf (Jhat X))) (Subgroup.zpowers b)) = 1) :
    ∃ g ∈ X, ∃ j : MulAut V, j ∈ Subgroup.closure ({b, g * b * g⁻¹} : Set (MulAut V)) ∧
      b * j * b⁻¹ = j⁻¹ ∧ (∃ n : ℕ, j ^ 3 ^ n = 1) ∧
        ∃ c ∈ fixV (fittingOf (Jhat X)), j c ≠ c := by
  classical
  set F : Subgroup (MulAut V) := fittingOf (Jhat X) with hFdef
  have hJX : Jhat X ≤ X := Jhat_le X
  have hbX : b ∈ X := hJX hbJ
  obtain ⟨hsup, hinf⟩ := commV_sup_fixV hV hO2
  have hV₀ : ∀ g ∈ X, ∀ v ∈ commV F, g v ∈ commV F := fun g hg v hv => apply_mem_commV_F hg hv
  have hC : ∀ g ∈ X, ∀ v ∈ fixV F, g v ∈ fixV F := fun g hg v hv => apply_mem_fixV_F hg hv
  obtain ⟨w, hw1, hw⟩ := exists_transvection_of_rk_comm hV hbC
  have hnontriv : ∃ c₀ ∈ fixV F, b c₀ ≠ c₀ := by
    by_contra hcon
    push Not at hcon
    have h0 : commSub (fixV F) (Subgroup.zpowers b) = ⊥ :=
      commSub_eq_bot_iff.mpr fun v hv => mem_fixV_zpowers_iff.mpr (hcon v hv)
    rw [h0, rk_bot] at hbC
    omega
  obtain ⟨c₀, hc₀, hc₀ne⟩ := hnontriv
  have hwC : w ∈ fixV F := by
    rcases hw c₀ hc₀ with h | h
    · exact absurd h hc₀ne
    · have : w = c₀⁻¹ * b c₀ := by rw [h]; group
      rw [this]
      exact (fixV F).mul_mem ((fixV F).inv_mem hc₀) (hC b hbX c₀ hc₀)
  set ρ : ↥X →* MulAut ↥(fixV F) := restHom (fixV F) hC with hρ
  have hρb1 : ρ ⟨b, hbX⟩ ≠ 1 := by
    intro h
    exact hc₀ne ((restHom_eq_one_iff hC).mp h c₀ hc₀)
  have hρb : IsTransvection (ρ ⟨b, hbX⟩) :=
    ⟨hρb1, ⟨w, hwC⟩, fun h => hw1 (congrArg Subtype.val h), fun v => by
      rcases hw v v.2 with h | h
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext h⟩
  have hO : pCoreOf 2 ρ.range = ⊥ := by
    rw [hρ, restHom_range]
    exact pCoreOf_two_autSub_eq_bot hsyl hgen (U := commV F) (W := fixV F) hsup hinf hV₀ hC
  have hOC : CFSG.pCore 2 ↥ρ.range = ⊥ := by
    have h1 : pCoreOf 2 (autSub X (fixV F)) = ⊥ :=
      pCoreOf_two_autSub_eq_bot hsyl hgen (U := commV F) (W := fixV F) hsup hinf hV₀ hC
    rw [hρ, restHom_range]
    exact (Subgroup.map_eq_bot_iff_of_injective _ (autSub X (fixV F)).subtype_injective).mp h1
  have hsolvρ : Group.IsSolvable ↥ρ.range :=
    Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  have hWC : ∀ u : ↥(fixV F), u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hV u)
  obtain ⟨g, hcube, hne⟩ := exists_conj_cube hWC ρ hsolvρ hO hOC hρb
  set t : ↥X := ⟨b, hbX⟩ with ht
  set t' : ↥X := g * t * g⁻¹ with ht'
  have ht'val : ((t' : ↥X) : MulAut V) = (g : MulAut V) * b * (g : MulAut V)⁻¹ := by
    simp [ht', ht]
  have hb'J : (g : MulAut V) * b * (g : MulAut V)⁻¹ ∈ Jhat X := conj_mem_Jhat g.2 hbJ
  have hb'2 : ((g : MulAut V) * b * (g : MulAut V)⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hb2]; simp
  set A₀ : ↥X := t * t' with hA₀
  have hρA₀ : ρ A₀ = ρ t * ρ t' := map_mul ρ t t'
  have hρA₀3 : (ρ A₀) ^ 3 = 1 := by rw [hρA₀]; exact hcube
  have hρA₀1 : ρ A₀ ≠ 1 := by rw [hρA₀]; exact hne
  have hord3 : orderOf (ρ A₀) = 3 := orderOf_eq_prime hρA₀3 hρA₀1
  have hdvd : 3 ∣ orderOf A₀ := hord3 ▸ orderOf_map_dvd ρ A₀
  have hNpos : orderOf A₀ ≠ 0 := (orderOf_pos A₀).ne'
  obtain ⟨e, n', hn3, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hNpos 3 (by norm_num)
  refine ⟨g, g.2, ((A₀ ^ n' : ↥X) : MulAut V), ?_, ?_, ⟨e, ?_⟩, ?_⟩
  ·
    have haA : ((A₀ : ↥X) : MulAut V) ∈ Subgroup.closure ({b, (g : MulAut V) * b * (g : MulAut V)⁻¹} :
        Set (MulAut V)) := by
      have : ((A₀ : ↥X) : MulAut V) = b * ((g : MulAut V) * b * (g : MulAut V)⁻¹) := by
        simp [hA₀, ht', ht]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
        (Subgroup.subset_closure (Or.inr rfl))
    have := Subgroup.pow_mem _ haA n'
    simpa using this
  ·
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb2)
    have hb'inv : ((g : MulAut V) * b * (g : MulAut V)⁻¹)⁻¹ = (g : MulAut V) * b * (g : MulAut V)⁻¹ :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hb'2)
    have hconj : b * ((A₀ : ↥X) : MulAut V) * b⁻¹ = ((A₀ : ↥X) : MulAut V)⁻¹ := by
      have hA : ((A₀ : ↥X) : MulAut V) = b * ((g : MulAut V) * b * (g : MulAut V)⁻¹) := by
        simp [hA₀, ht', ht]
      rw [hA, mul_inv_rev, hb'inv, hbinv]
      calc b * (b * ((g : MulAut V) * b * (g : MulAut V)⁻¹)) * b
          = (b * b) * ((g : MulAut V) * b * (g : MulAut V)⁻¹) * b := by group
        _ = ((g : MulAut V) * b * (g : MulAut V)⁻¹) * b := by
          rw [show b * b = 1 from by rw [← pow_two]; exact hb2, one_mul]
    have hjc : b * (((A₀ ^ n' : ↥X)) : MulAut V) * b⁻¹ = (((A₀ ^ n' : ↥X)) : MulAut V)⁻¹ := by
      have h1 : (((A₀ ^ n' : ↥X)) : MulAut V) = ((A₀ : ↥X) : MulAut V) ^ n' := by simp
      rw [h1, ← conj_pow, hconj, inv_pow]
    exact hjc
  ·
    have : (A₀ ^ n') ^ 3 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hN]
      exact pow_orderOf_eq_one A₀
    have h2 := congrArg (fun y : ↥X => (y : MulAut V)) this
    simpa using h2
  ·
    by_contra hcon
    push Not at hcon
    have h1 : ρ (A₀ ^ n') = 1 := (restHom_eq_one_iff hC).mpr fun c hc => hcon c hc
    rw [map_pow] at h1
    have h2 : 3 ∣ n' := hord3 ▸ orderOf_dvd_of_pow_eq_one h1
    exact hn3 h2

end Concrete

end LRed12

end CFSG.Quasithin
