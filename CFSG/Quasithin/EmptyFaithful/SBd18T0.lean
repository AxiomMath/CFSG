module

public import CFSG.Quasithin.EmptyFaithful.SBd14Ctx

public section

open CFSG.QuasithinUnique CFSG.Quasithin.S1417

namespace CFSG.Quasithin.SBd16

section Model

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ T' : Subgroup (MulAut W)} {tb : MulAut W}

theorem exists_model_elements_swap (hS : OfourStruct X L₁ L₂ tb) (hT : IsSylowTwoOf T' X) :
    ∃ s₁ s₂ w : MulAut W,
      s₁ ∈ T' ∧ s₂ ∈ T' ∧ s₁ ∈ L₁ ∧ s₂ ∈ L₂ ∧ s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧ s₁ ≠ 1 ∧ s₂ ≠ 1 ∧
        s₁ * s₂ ≠ 1 ∧ s₁ * s₂ = s₂ * s₁ ∧
        (∀ x ∈ T' ⊓ (L₁ ⊔ L₂), x = 1 ∨ x = s₁ ∨ x = s₂ ∨ x = s₁ * s₂) ∧
        (∀ y ∈ X, Odd (orderOf y) → s₁ * s₂ * y * (s₁ * s₂)⁻¹ = y⁻¹) ∧
        w ∈ T' ∧ w * w = s₁ * s₂ ∧ Nat.card ↥(Subgroup.zpowers w) = 4 ∧
        (∀ y ∈ Subgroup.zpowers w, y * y = 1 → y = 1 ∨ y = s₁ * s₂) ∧
        (∃ u ∈ commV L₁, s₁ u ≠ u) ∧ (∀ u ∈ commV L₁, s₂ u = u) ∧
        ∃ b ∈ T', b * s₁ * b⁻¹ = s₂ ∧ b * s₂ * b⁻¹ = s₁ ∧ (∀ u ∈ commV L₁, b u ∈ commV L₂) ∧
          (∀ u ∈ commV L₂, b u ∈ commV L₁) := by
  classical
  obtain ⟨s₁, s₂, τb, a₁, a₂, hF⟩ := hS.exists_sylowFacts hT
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hs₂L : s₂ ∈ L₂ := hF.sylow.s₂_mem_L
  have hs₁T : s₁ ∈ T' := hF.sylow.s₁_mem_S.1
  have hs₂T : s₂ ∈ T' := hF.sylow.s₂_mem_S.1
  have hτT : τb ∈ T' := hF.τ_T
  have hcomm : s₁ * s₂ = s₂ * s₁ := hF.comm
  have hmul_ne : s₁ * s₂ ≠ 1 := hF.mul_ne
  have hs₁1 : s₁ ≠ 1 := hF.sylow.s₁_ne
  have hs₂1 : s₂ ≠ 1 := hF.sylow.s₂_ne
  have hr2 : s₁ * s₂ * (s₁ * s₂) = 1 := by
    calc s₁ * s₂ * (s₁ * s₂) = s₁ * (s₂ * s₁) * s₂ := by group
      _ = s₁ * (s₁ * s₂) * s₂ := by rw [hcomm]
      _ = (s₁ * s₁) * (s₂ * s₂) := by group
      _ = 1 := by rw [hF.s₁_sq, hF.s₂_sq, mul_one]
  have hτc : τb * (s₁ * s₂) * τb⁻¹ = s₁ * s₂ := by
    calc τb * (s₁ * s₂) * τb⁻¹ = (τb * s₁ * τb⁻¹) * (τb * s₂ * τb⁻¹) := by group
      _ = s₂ * s₁ := by rw [hF.τs₁, hF.τs₂]
      _ = s₁ * s₂ := hcomm.symm
  have hτcomm : τb * (s₁ * s₂) = (s₁ * s₂) * τb := by
    have := congrArg (· * τb) hτc
    simpa [mul_assoc] using this
  have hSc : ∀ x ∈ T' ⊓ (L₁ ⊔ L₂), x * (s₁ * s₂) = (s₁ * s₂) * x := by
    intro x hx
    rcases (hF.S_eq x).1 hx with rfl | rfl | rfl | rfl
    · simp
    · calc x * (x * s₂) = x * (s₂ * x) := by rw [← hcomm]
        _ = x * s₂ * x := by group
    · calc x * (s₁ * x) = (x * s₁) * x := by group
        _ = (s₁ * x) * x := by rw [← hcomm]
        _ = s₁ * x * x := by group
    · rfl
  have hcentral : ∀ x ∈ T', x * (s₁ * s₂) = (s₁ * s₂) * x := by
    intro x hx
    rcases hS.coset (hT.1 hx) (hT.1 hτT) hF.τ_N with h1 | h1
    · exact hSc x ⟨hx, h1⟩
    · have hxτ : x * τb⁻¹ ∈ T' ⊓ (L₁ ⊔ L₂) := ⟨T'.mul_mem hx (T'.inv_mem hτT), h1⟩
      have h2 := hSc _ hxτ
      calc x * (s₁ * s₂) = (x * τb⁻¹) * (τb * (s₁ * s₂)) := by group
        _ = (x * τb⁻¹) * ((s₁ * s₂) * τb) := by rw [hτcomm]
        _ = ((x * τb⁻¹) * (s₁ * s₂)) * τb := by group
        _ = ((s₁ * s₂) * (x * τb⁻¹)) * τb := by rw [h2]
        _ = (s₁ * s₂) * x := by group
  obtain ⟨r, hrT, hr1, hrr, hrc, hrz, hrinv⟩ := hS.exists_central hT
  have hrs : s₁ * s₂ = r :=
    (hrz (s₁ * s₂) (T'.mul_mem hs₁T hs₂T) hcentral).resolve_left hmul_ne
  have hτsq : τb * τb = 1 ∨ τb * τb = s₁ * s₂ := by
    have hidx : ((T' ⊓ (L₁ ⊔ L₂)).subgroupOf T').index = 2 := hS.relIndex_S hT
    have hmem := Subgroup.mul_self_mem_of_index_two hidx (⟨τb, hτT⟩ : ↥T')
    have hmem' : τb * τb ∈ T' ⊓ (L₁ ⊔ L₂) := Subgroup.mem_subgroupOf.mp hmem
    have hconj : τb * (τb * τb) * τb⁻¹ = τb * τb := by group
    rcases (hF.S_eq _).1 hmem' with h | h | h | h
    · exact Or.inl h
    · exfalso
      rw [h, hF.τs₁] at hconj
      exact hF.ne.symm hconj
    · exfalso
      rw [h, hF.τs₂] at hconj
      exact hF.ne hconj
    · exact Or.inr h
  have hwex : ∃ w : MulAut W, w ∈ T' ∧ w * w = s₁ * s₂ := by
    rcases hτsq with h | h
    · refine ⟨τb * s₁, T'.mul_mem hτT hs₁T, ?_⟩
      calc τb * s₁ * (τb * s₁) = (τb * s₁ * τb⁻¹) * (τb * τb) * s₁ := by group
        _ = s₂ * 1 * s₁ := by rw [hF.τs₁, h]
        _ = s₁ * s₂ := by rw [mul_one, hcomm]
    · exact ⟨τb, hτT, h⟩
  obtain ⟨w, hwT, hww⟩ := hwex
  have hw2 : w ^ 2 = s₁ * s₂ := by rw [pow_two]; exact hww
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw4 : w ^ 4 = 1 := by
    have : w ^ 4 = (w ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this, hw2, pow_two]
    exact hr2
  have hord : orderOf w = 4 := by
    have h4 : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
    rw [h4]
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, hw2]; exact hmul_ne
    · simpa using hw4
  have hinv_w : ∀ y ∈ Subgroup.zpowers w, y * y = 1 → y = 1 ∨ y = s₁ * s₂ := by
    intro y hy hy2
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : w ^ (2 * k) = 1 := by rw [two_mul, zpow_add]; exact hy2
    have h2 : (4 : ℤ) ∣ 2 * k := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [hord] at this
      exact_mod_cast this
    obtain ⟨m, hm⟩ := (show (2 : ℤ) ∣ k by omega)
    have hwk : w ^ k = (s₁ * s₂) ^ m := by
      rw [hm, zpow_mul, zpow_two, hww]
    rw [hwk]
    have hsq' : (s₁ * s₂) ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hr2
    rw [zpow_eq_zpow_emod m hsq']
    rcases Int.emod_two_eq_zero_or_one m with hm0 | hm1
    · left; rw [hm0, zpow_zero]
    · right; rw [hm1, zpow_one]
  have hmove : ∃ u ∈ commV L₁, s₁ u ≠ u := by
    by_contra hcon
    push Not at hcon
    exact hs₁1 (eq_one_of_forall_apply_eq hS.nat₁ (fun l hl u hu => commV_stable L₁ hl hu) hs₁L
      hcon)
  refine ⟨s₁, s₂, w, hs₁T, hs₂T, hs₁L, hs₂L, hF.s₁_sq, hF.s₂_sq, hs₁1, hs₂1, hmul_ne, hcomm, fun x hx => (hF.S_eq x).1 hx,
    ?_, hwT, hww, ?_, hinv_w, hmove, fun u hu => hS.L₂_fix₁ hs₂L hu, τb, hτT, hF.τs₁, hF.τs₂, ?_, ?_⟩
  · intro y hy hyo
    have := hrinv y hy hyo
    rwa [← hrs] at this
  · rw [Nat.card_zpowers, hord]
  · intro u hu
    have h1 : τb u ∈ (commV L₁).map τb.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [commV_map_conjAut, hF.conj₁] at h1
  · intro u hu
    have h1 : τb u ∈ (commV L₂).map τb.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [commV_map_conjAut, hF.conj₂] at h1

end Model

end CFSG.Quasithin.SBd16

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S1417
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem RestHyp.exists_fusion_elements_t0 (r : RestHyp T Mc M V₁ V₂ Yp I L t) {X : Subgroup G}
    (hXY : X ≤ Yp) (hX3 : IsPGroup 3 ↥X) (hXV : X ⊓ Subgroup.centralizer (VZ T M : Set G) = ⊥)
    (hRQ : T ⊓ Subgroup.centralizer (VZ T M : Set G) = Sgp153 T V₁ ⊓ L)
    (hreg : Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) = ⊥)
    (hfrat : ∀ g ∈ T, ∃ n ∈ T ⊓ Subgroup.normalizer (X : Set G),
      ∃ o ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G), g = n * o) :
    ∃ τ f : G, τ ∈ Sgp153 T V₁ ∧ f ∈ Sgp153 T V₁ ∧ τ ∈ Subgroup.normalizer (X : Set G) ∧
      f ∈ Subgroup.normalizer (X : Set G) ∧ τ * τ = 1 ∧ f * f = 1 ∧ τ * f = f * τ ∧ τ ≠ 1 ∧
      f ≠ 1 ∧ τ ≠ f ∧
      (∀ s ∈ Sgp153 T V₁ ⊓ Subgroup.normalizer (X : Set G), s = 1 ∨ s = τ ∨ s = f ∨ s = τ * f) ∧
      (∀ x ∈ X, f * x * f⁻¹ = x⁻¹) ∧ (∀ v ∈ V₁, (τ * f) * v = v * (τ * f)) ∧
      (∃ v ∈ V₁, τ * v ≠ v * τ) ∧
      (∃ W : Subgroup G, W ≤ T ∧ W.relIndex T = 2 ∧ τ ∉ W ∧
        ∀ y ∈ W, y * y = 1 → y ∈ Sgp153 T V₁ ⊓ L ∨ f⁻¹ * y ∈ Sgp153 T V₁ ⊓ L) ∧
      ∃ t₀ ∈ T ⊓ Subgroup.normalizer (X : Set G),
        t₀ * τ * t₀⁻¹ = τ * f ∧ t₀ * (τ * f) * t₀⁻¹ = τ ∧
        (∀ v ∈ V₁, t₀ * v * t₀⁻¹ ∈ V₂) ∧ (∀ v ∈ V₂, t₀ * v * t₀⁻¹ ∈ V₁) := by
  classical
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  have hTM : T ≤ M := hyp.T_le
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := hyp.le_normalizer
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := hTM.trans hMN
  have hYpM : Yp ≤ M := by rw [r.hYY]; exact Y153_le Mc M
  obtain ⟨hV, L₁, L₂, tb, hS, hV₁, hV₂, -⟩ := D0.model
  have hT' : IsSylowTwoOf (autI hV T) (autI hV M) := hyp.isSylowTwoOf_autI
  obtain ⟨s₁, s₂, w, hs₁T, hs₂T, hs₁L, hs₂L, hs₁sq, hs₂sq, hs₁1, hs₂1, hmn, hcomm, hSeq, hinv,
    hwT, hww, hwcard, hwinv, ⟨u₀, hu₀, hu₀ne⟩, hfix, b, hbT, hbs₁, hbs₂, hbsw₁, hbsw₂⟩ :=
    SBd16.exists_model_elements_swap hS hT'
  have hcard8 : Nat.card ↥(autI hV T) = 8 := hS.card_T hT'
  have hker : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)),
      convI hV ⟨g, hg⟩ = 1 ↔ g ∈ Subgroup.centralizer (VZ T M : Set G) := fun g hg =>
    convI_eq_one_iff hV ⟨g, hg⟩
  have cmul : ∀ (g h : G) (hg : g ∈ Subgroup.normalizer (VZ T M : Set G))
      (hh : h ∈ Subgroup.normalizer (VZ T M : Set G)),
      convI hV ⟨g * h, Subgroup.mul_mem _ hg hh⟩ = convI hV ⟨g, hg⟩ * convI hV ⟨h, hh⟩ :=
    fun g h hg hh => map_mul (convI hV) ⟨g, hg⟩ ⟨h, hh⟩
  have hlift : ∀ b ∈ autI hV T, ∃ n : G, n ∈ T ⊓ Subgroup.normalizer (X : Set G) ∧
      ∃ hn : n ∈ Subgroup.normalizer (VZ T M : Set G), convI hV ⟨n, hn⟩ = b := by
    intro b hb
    obtain ⟨g, hgT, rfl⟩ := (mem_autI hV).1 hb
    obtain ⟨n, hn, o, ho, hgno⟩ := hfrat (g : G) hgT
    have hnV : n ∈ Subgroup.normalizer (VZ T M : Set G) := hTN hn.1
    have hoV : o ∈ Subgroup.normalizer (VZ T M : Set G) := hTN ho.1
    refine ⟨n, hn, hnV, ?_⟩
    have h1 : convI hV ⟨o, hoV⟩ = 1 := (hker o hoV).2 ho.2
    have h2 : g = ⟨n, hnV⟩ * ⟨o, hoV⟩ := Subtype.ext hgno
    rw [h2, map_mul, h1, mul_one]
  have hinj : ∀ n n' : G, n ∈ T ⊓ Subgroup.normalizer (X : Set G) →
      n' ∈ T ⊓ Subgroup.normalizer (X : Set G) →
      ∀ (hn : n ∈ Subgroup.normalizer (VZ T M : Set G))
        (hn' : n' ∈ Subgroup.normalizer (VZ T M : Set G)),
        convI hV ⟨n, hn⟩ = convI hV ⟨n', hn'⟩ → n = n' := by
    intro n n' hnN hn'N hn hn' he
    have hgT : n⁻¹ * n' ∈ T := T.mul_mem (T.inv_mem hnN.1) hn'N.1
    have hgNX : n⁻¹ * n' ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hnN.2) hn'N.2
    have hgNV : n⁻¹ * n' ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hn) hn'
    have hg1 : convI hV ⟨n⁻¹ * n', hgNV⟩ = 1 := by
      have e : (⟨n⁻¹ * n', hgNV⟩ : Subgroup.normalizer (VZ T M : Set G)) =
          ⟨n, hn⟩⁻¹ * ⟨n', hn'⟩ := rfl
      rw [e, map_mul, map_inv, he, inv_mul_cancel]
    have hgV : n⁻¹ * n' ∈ Subgroup.centralizer (VZ T M : Set G) := (hker _ hgNV).1 hg1
    have hgQ : n⁻¹ * n' ∈ Sgp153 T V₁ ⊓ L := by rw [← hRQ]; exact ⟨hgT, hgV⟩
    have hgX : n⁻¹ * n' ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxN : x ∈ Subgroup.normalizer (VZ T M : Set G) := hMN (hYpM (hXY hx))
      have hcN : (n⁻¹ * n')⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := Subgroup.inv_mem _ hgV
      have h1 : x * (n⁻¹ * n')⁻¹ * x⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) := by
        have := S153F.mem_normalizer_centralizer_of_mem_normalizer hxN
        exact (Subgroup.mem_normalizer_iff.mp this _).mp hcN
      have h2 : (n⁻¹ * n') * x * (n⁻¹ * n')⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp hgNX x).mp hx
      have h3 : (n⁻¹ * n') * x * (n⁻¹ * n')⁻¹ * x⁻¹ ∈ X ⊓ Subgroup.centralizer (VZ T M : Set G) := by
        refine ⟨Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hx), ?_⟩
        have : (n⁻¹ * n') * x * (n⁻¹ * n')⁻¹ * x⁻¹ = (n⁻¹ * n') * (x * (n⁻¹ * n')⁻¹ * x⁻¹) := by
          group
        rw [this]
        exact Subgroup.mul_mem _ hgV h1
      rw [hXV, Subgroup.mem_bot] at h3
      have h4 : (n⁻¹ * n') * x = x * (n⁻¹ * n') := by
        calc (n⁻¹ * n') * x = ((n⁻¹ * n') * x * (n⁻¹ * n')⁻¹ * x⁻¹) * (x * (n⁻¹ * n')) := by group
          _ = x * (n⁻¹ * n') := by rw [h3, one_mul]
      exact h4.symm
    have : n⁻¹ * n' ∈ Sgp153 T V₁ ⊓ L ⊓ Subgroup.centralizer (X : Set G) := ⟨hgQ, hgX⟩
    rw [hreg, Subgroup.mem_bot] at this
    exact inv_mul_eq_one.mp this
  obtain ⟨τ, hτN, hτV, hτc⟩ := hlift s₁ hs₁T
  obtain ⟨σ, hσN, hσV, hσc⟩ := hlift s₂ hs₂T
  have hτσV : τ * σ ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.mul_mem _ hτV hσV
  have hfc : convI hV ⟨τ * σ, hτσV⟩ = s₁ * s₂ := by rw [cmul τ σ hτV hσV, hτc, hσc]
  have hfN : τ * σ ∈ T ⊓ Subgroup.normalizer (X : Set G) := Subgroup.mul_mem _ hτN hσN
  have hone : (1 : G) ∈ T ⊓ Subgroup.normalizer (X : Set G) := Subgroup.one_mem _
  have honeV : (1 : G) ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.one_mem _
  have hone1 : convI hV ⟨1, honeV⟩ = 1 := map_one (convI hV)
  have hττ : τ * τ = 1 := by
    refine hinj _ _ (Subgroup.mul_mem _ hτN hτN) hone (Subgroup.mul_mem _ hτV hτV) honeV ?_
    rw [cmul τ τ hτV hτV, hτc, hs₁sq, hone1]
  have hσσ : σ * σ = 1 := by
    refine hinj _ _ (Subgroup.mul_mem _ hσN hσN) hone (Subgroup.mul_mem _ hσV hσV) honeV ?_
    rw [cmul σ σ hσV hσV, hσc, hs₂sq, hone1]
  have hτσ : τ * σ = σ * τ := by
    refine hinj _ _ hfN (Subgroup.mul_mem _ hσN hτN) hτσV (Subgroup.mul_mem _ hσV hτV) ?_
    rw [hfc, cmul σ τ hσV hτV, hσc, hτc, hcomm]
  have hff : τ * σ * (τ * σ) = 1 := by
    calc τ * σ * (τ * σ) = τ * (σ * τ) * σ := by group
      _ = τ * (τ * σ) * σ := by rw [← hτσ]
      _ = (τ * τ) * (σ * σ) := by group
      _ = 1 := by rw [hττ, hσσ, one_mul]
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hs₁1
    rw [← hτc]
    have : (⟨τ, hτV⟩ : Subgroup.normalizer (VZ T M : Set G)) = 1 := Subtype.ext h
    rw [this, map_one]
  have hfne : τ * σ ≠ 1 := by
    intro h
    apply hmn
    rw [← hfc]
    have : (⟨τ * σ, hτσV⟩ : Subgroup.normalizer (VZ T M : Set G)) = 1 := Subtype.ext h
    rw [this, map_one]
  have hτf : τ ≠ τ * σ := by
    intro h
    have hσ1 : σ = 1 := by
      have : τ * σ = τ * 1 := by rw [mul_one]; exact h.symm
      exact mul_left_cancel this
    apply hs₂1
    rw [← hσc]
    have : (⟨σ, hσV⟩ : Subgroup.normalizer (VZ T M : Set G)) = 1 := Subtype.ext hσ1
    rw [this, map_one]
  have hτf_eq : τ * (τ * σ) = σ := by rw [← mul_assoc, hττ, one_mul]
  have hτfc : τ * (τ * σ) = τ * σ * τ := by
    rw [hτf_eq, hτσ, mul_assoc, hττ, mul_one]
  have hS₁ : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)),
      convI hV ⟨g, hg⟩ ∈ L₁ ⊔ L₂ → g ∈ Subgroup.normalizer (V₁ : Set G) := by
    intro g hg hL
    rw [hV₁]
    exact (mem_normalizer_map_inclMod_iff hV hg (commV L₁)).2 (hS.sup_le_stab₁ hL)
  have hτS : τ ∈ Sgp153 T V₁ :=
    ⟨hτN.1, hS₁ τ hτV (by rw [hτc]; exact Subgroup.mem_sup_left hs₁L)⟩
  have hσS : σ ∈ Sgp153 T V₁ :=
    ⟨hσN.1, hS₁ σ hσV (by rw [hσc]; exact Subgroup.mem_sup_right hs₂L)⟩
  have hfS : τ * σ ∈ Sgp153 T V₁ := Subgroup.mul_mem _ hτS hσS
  have hclass : ∀ s ∈ Sgp153 T V₁ ⊓ Subgroup.normalizer (X : Set G),
      s = 1 ∨ s = τ ∨ s = σ ∨ s = τ * σ := by
    intro s hs
    obtain ⟨⟨hsT, hsV₁⟩, hsX⟩ := hs
    have hsNV : s ∈ Subgroup.normalizer (VZ T M : Set G) := hTN hsT
    have hsNX : s ∈ T ⊓ Subgroup.normalizer (X : Set G) := ⟨hsT, hsX⟩
    have hmem : convI hV ⟨s, hsNV⟩ ∈ autI hV T ⊓ (L₁ ⊔ L₂) := by
      refine ⟨convI_mem_autI hV hsT hsNV, ?_⟩
      have hMem : convI hV ⟨s, hsNV⟩ ∈ autI hV M := convI_mem_autI hV (hTM hsT) hsNV
      refine (hS.mem_sup_iff hMem).2 ?_
      have h1 : s ∈ Subgroup.normalizer (((commV L₁).map (inclMod hV) : Subgroup G) : Set G) := by
        rw [← hV₁]; exact hsV₁
      have h2 := (mem_normalizer_map_inclMod_iff hV hsNV (commV L₁)).1 h1
      exact fun u hu => ((mem_stabSub).1 h2 u).2 hu
    rcases hSeq _ hmem with h | h | h | h
    · exact Or.inl (hinj s 1 hsNX hone hsNV honeV (h.trans hone1.symm))
    · exact Or.inr (Or.inl (hinj s τ hsNX hτN hsNV hτV (h.trans hτc.symm)))
    · exact Or.inr (Or.inr (Or.inl (hinj s σ hsNX hσN hsNV hσV (h.trans hσc.symm))))
    · exact Or.inr (Or.inr (Or.inr (hinj s (τ * σ) hsNX hfN hsNV hτσV (h.trans hfc.symm))))
  have hinvX : ∀ x ∈ X, τ * σ * x * (τ * σ)⁻¹ = x⁻¹ := by
    intro x hx
    have hxM : x ∈ M := hYpM (hXY hx)
    have hxV : x ∈ Subgroup.normalizer (VZ T M : Set G) := hMN hxM
    have hL : τ * σ * x * (τ * σ)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hfN.2 x).mp hx
    obtain ⟨k, hk⟩ := hX3 ⟨x, hx⟩
    have hxk : x ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hpow : (convI hV ⟨x, hxV⟩) ^ 3 ^ k = 1 := by
      have : (⟨x, hxV⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using hxk)
      rw [← map_pow, this, map_one]
    have hodd : Odd (orderOf (convI hV ⟨x, hxV⟩)) :=
      Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hpow)
    have hxMA : convI hV ⟨x, hxV⟩ ∈ autI hV M := convI_mem_autI hV hxM hxV
    have hrx := hinv _ hxMA hodd
    have haV : τ * σ * x * (τ * σ)⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hτσV hxV) (Subgroup.inv_mem _ hτσV)
    have hprodV : x * (τ * σ * x * (τ * σ)⁻¹) ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ hxV haV
    have hconv : convI hV ⟨x * (τ * σ * x * (τ * σ)⁻¹), hprodV⟩ = 1 := by
      have e : (⟨x * (τ * σ * x * (τ * σ)⁻¹), hprodV⟩ : Subgroup.normalizer (VZ T M : Set G)) =
          ⟨x, hxV⟩ * (⟨τ * σ, hτσV⟩ * ⟨x, hxV⟩ * ⟨τ * σ, hτσV⟩⁻¹) := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, hfc, hrx, mul_inv_cancel]
    have hmemX : x * (τ * σ * x * (τ * σ)⁻¹) ∈ X ⊓ Subgroup.centralizer (VZ T M : Set G) :=
      ⟨Subgroup.mul_mem _ hx hL, (hker _ hprodV).1 hconv⟩
    rw [hXV, Subgroup.mem_bot] at hmemX
    exact eq_inv_of_mul_eq_one_right hmemX
  have hσcent : ∀ v ∈ V₁, (τ * (τ * σ)) * v = v * (τ * (τ * σ)) := by
    intro v hv
    rw [hτf_eq]
    have hσC : σ ∈ Subgroup.centralizer (V₁ : Set G) := by
      rw [hV₁]
      exact (mem_centralizer_map_inclMod_iff hV hσV (commV L₁)).2
        (fun u hu => by rw [hσc]; exact hfix u hu)
    exact (Subgroup.mem_centralizer_iff.mp hσC v hv).symm
  have hτmove : ∃ v ∈ V₁, τ * v ≠ v * τ := by
    refine ⟨u₀.val, ?_, ?_⟩
    · rw [hV₁]; exact ⟨u₀, hu₀, rfl⟩
    · intro h
      apply hu₀ne
      apply IntMod.val_injective
      have h1 := convI_apply_val hV ⟨τ, hτV⟩ u₀
      rw [hτc] at h1
      rw [h1]
      calc τ * u₀.val * τ⁻¹ = u₀.val * τ * τ⁻¹ := by rw [h]
        _ = u₀.val := by group
  let πT : ↥T →* MulAut (IntMod (VZ T M) hV) := convHom hV T hTN
  have hπ : ∀ z : ↥T, πT z = convI hV ⟨(z : G), hTN z.2⟩ := fun z => rfl
  let W : Subgroup G := ((Subgroup.zpowers w).comap πT).map T.subtype
  have hWT : W ≤ T := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hWsub : W.subgroupOf T = (Subgroup.zpowers w).comap πT :=
    Subgroup.comap_map_eq_self_of_injective T.subtype_injective _
  have hrelW : W.relIndex T = 2 := by
    have h1 : W.relIndex T = ((Subgroup.zpowers w).comap πT).index := by
      rw [Subgroup.relIndex, hWsub]
    rw [h1, Subgroup.index_comap, range_convHom hV T hTN]
    have hzle : Subgroup.zpowers w ≤ autI hV T := (Subgroup.zpowers_le).2 hwT
    have h2 := Subgroup.relIndex_mul_card (Subgroup.zpowers w) (autI hV T)
    rw [inf_eq_left.mpr hzle, hwcard, hcard8] at h2
    omega
  have hτW : τ ∉ W := by
    rintro ⟨z, hz, hzτ⟩
    have hzτ' : z = ⟨τ, hτN.1⟩ := Subtype.ext hzτ
    have hπτ : πT ⟨τ, hτN.1⟩ = s₁ := by rw [hπ]; exact hτc
    have h1 : s₁ ∈ Subgroup.zpowers w := by
      have := Subgroup.mem_comap.mp hz
      rwa [hzτ', hπτ] at this
    rcases hwinv s₁ h1 hs₁sq with h | h
    · exact hs₁1 h
    · apply hs₂1
      have : s₁ * s₂ = s₁ * 1 := by rw [mul_one]; exact h.symm
      exact mul_left_cancel this
  have hWinv : ∀ y ∈ W, y * y = 1 →
      y ∈ Sgp153 T V₁ ⊓ L ∨ (τ * σ)⁻¹ * y ∈ Sgp153 T V₁ ⊓ L := by
    rintro y ⟨z, hz, rfl⟩ hy2
    have hz' : πT z ∈ Subgroup.zpowers w := Subgroup.mem_comap.mp hz
    have hsq : πT z * πT z = 1 := by
      rw [← map_mul]
      have : z * z = 1 := Subtype.ext hy2
      rw [this, map_one]
    have hzN : (z : G) ∈ Subgroup.normalizer (VZ T M : Set G) := hTN z.2
    rcases hwinv _ hz' hsq with h | h
    · left
      have hzV : (z : G) ∈ Subgroup.centralizer (VZ T M : Set G) := by
        refine (hker (z : G) hzN).1 ?_
        rw [← hπ]
        exact h
      rw [← hRQ]
      exact ⟨z.2, hzV⟩
    · right
      have hfT : τ * σ ∈ T := Subgroup.mul_mem _ hτS.1 hσS.1
      have hmemT : (τ * σ)⁻¹ * (z : G) ∈ T := T.mul_mem (T.inv_mem hfT) z.2
      have hmemN : (τ * σ)⁻¹ * (z : G) ∈ Subgroup.normalizer (VZ T M : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hτσV) hzN
      have hc1 : convI hV ⟨(τ * σ)⁻¹ * (z : G), hmemN⟩ = 1 := by
        have e : (⟨(τ * σ)⁻¹ * (z : G), hmemN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
            ⟨τ * σ, hτσV⟩⁻¹ * ⟨(z : G), hzN⟩ := rfl
        rw [e, map_mul, map_inv, hfc]
        have h' : convI hV ⟨(z : G), hzN⟩ = s₁ * s₂ := by rw [← hπ]; exact h
        rw [h', inv_mul_cancel]
      rw [← hRQ]
      exact ⟨hmemT, (hker _ hmemN).1 hc1⟩
  obtain ⟨t₀, ht₀N, ht₀V, ht₀c⟩ := hlift b hbT
  have ht₀inv : t₀⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) := Subgroup.inv_mem _ ht₀V
  have ht₀τN : t₀ * τ * t₀⁻¹ ∈ T ⊓ Subgroup.normalizer (X : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₀N hτN) (Subgroup.inv_mem _ ht₀N)
  have ht₀τV : t₀ * τ * t₀⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₀V hτV) ht₀inv
  have ht₀τc : convI hV ⟨t₀ * τ * t₀⁻¹, ht₀τV⟩ = s₂ := by
    have e : (⟨t₀ * τ * t₀⁻¹, ht₀τV⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        ⟨t₀, ht₀V⟩ * ⟨τ, hτV⟩ * ⟨t₀, ht₀V⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, ht₀c, hτc, hbs₁]
  have ht₀τ : t₀ * τ * t₀⁻¹ = σ :=
    hinj _ σ ht₀τN hσN ht₀τV hσV (by rw [ht₀τc, hσc])
  have ht₀σN : t₀ * σ * t₀⁻¹ ∈ T ⊓ Subgroup.normalizer (X : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₀N hσN) (Subgroup.inv_mem _ ht₀N)
  have ht₀σV : t₀ * σ * t₀⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ht₀V hσV) ht₀inv
  have ht₀σc : convI hV ⟨t₀ * σ * t₀⁻¹, ht₀σV⟩ = s₁ := by
    have e : (⟨t₀ * σ * t₀⁻¹, ht₀σV⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        ⟨t₀, ht₀V⟩ * ⟨σ, hσV⟩ * ⟨t₀, ht₀V⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, ht₀c, hσc, hbs₂]
  have ht₀σ : t₀ * σ * t₀⁻¹ = τ :=
    hinj _ τ ht₀σN hτN ht₀σV hτV (by rw [ht₀σc, hτc])
  have hswap : ∀ (U U' : Subgroup (IntMod (VZ T M) hV)), (∀ u ∈ U, b u ∈ U') →
      ∀ v ∈ U.map (inclMod hV), t₀ * v * t₀⁻¹ ∈ U'.map (inclMod hV) := by
    intro U U' hUU' v hv
    obtain ⟨u, hu, rfl⟩ := (mem_map_inclMod_iff hV).1 hv
    refine ⟨b u, hUU' u hu, ?_⟩
    rw [inclMod_apply, ← ht₀c, convI_apply_val]
  refine ⟨τ, τ * σ, hτS, hfS, hτN.2, hfN.2, hττ, hff, hτfc, hτ1, hfne, hτf, ?_, hinvX, hσcent,
    hτmove, ⟨W, hWT, hrelW, hτW, hWinv⟩, t₀, ht₀N, ?_, ?_, ?_, ?_⟩
  intro s hs
  rcases hclass s hs with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (by rw [hτf_eq]; exact h)))
  · exact Or.inr (Or.inr (Or.inl h))
  · rw [hτf_eq]; exact ht₀τ
  · rw [hτf_eq]; exact ht₀σ
  · rw [hV₁, hV₂]; exact hswap _ _ hbsw₁
  · rw [hV₁, hV₂]; exact hswap _ _ hbsw₂

end CFSG.Quasithin.SBd14
