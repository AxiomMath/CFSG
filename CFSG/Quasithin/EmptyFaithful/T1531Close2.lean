module

public import CFSG.Quasithin.EmptyFaithful.T1531Close
public import CFSG.Quasithin.EmptyFaithful.T1531Gold2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

@[expose] def Stage1531InspectB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ E : Subgroup G) (t s : G),
    Ctx153 G T Mc M V₁ V₂ t → Res15345 T Mc M V₁ V₂ → Res15346 T M V₁ V₂ → Res15349 T Mc M V₁ →
    LineData153 T M V₁ V₂ E → Res15366B T Mc M V₁ V₂ E → Res15367 T Mc M V₁ V₂ E →
    GoldLine153 T V₁ E s → Res15368 T Mc M E s →
    F6.F618Conclusion
      (((G1_153 T Mc M E s).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))))
      (((G2_153 T E).subgroupOf (G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))) →
    XE153 E = oTwoUpper (thompsonJ (G0_153 T Mc M E s)) ∨
      ¬ Group.IsSolvable ↥(thompsonJ (G0_153 T Mc M E s) ⊓ Subgroup.normalizer (V₁ : Set G))

section Geometry

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem exists_goldLine153B (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t)
    (r66 : Res15366B T Mc M V₁ V₂ E) : ∃ s : G, GoldLine153 T V₁ E s := by
  by_contra hno
  push Not at hno
  have hST : Sgp153 T V₁ ≤ TE153 T E := fun s hs => by
    by_contra hs'
    exact hno s ⟨hs, hs'⟩
  have hiS : (Sgp153 T V₁).relIndex T = 2 := D.relIndex_nS h
  have hiE : (TE153 T E).relIndex T = 2 := r66.relIndex_two
  have hmul := Subgroup.relIndex_mul_relIndex (Sgp153 T V₁) (TE153 T E) T hST inf_le_left
  rw [hiS, hiE] at hmul
  have h1 : (Sgp153 T V₁).relIndex (TE153 T E) = 1 := by omega
  have hTS : TE153 T E ≤ Sgp153 T V₁ := Subgroup.relIndex_eq_one.mp h1
  exact r66.barTE_klein.2 (by rw [le_antisymm hTS hST])

theorem exists_conj_mem_YE153B (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) {z e : G} (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (he : e ∈ E) (he1 : e ≠ 1) : ∃ a ∈ YE153 Mc M E, a * z * a⁻¹ = e := by
  have hzE : z ∈ E := r66.Z_le_E hz
  have hsq : ∀ x : ↥E, x ^ 2 = 1 := fun x => Subtype.ext (by
    have := c.hyp.elemAbelian.2 (x : G) (L.le_V x.2)
    simpa using this)
  have hexp : Monoid.exponent ↥E = 2 := by
    have hdvd : Monoid.exponent ↥E ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hsub : Subsingleton ↥E := Monoid.exp_eq_one_iff.mp h1
      have := Nat.card_of_subsingleton (1 : ↥E)
      rw [L.card_eq] at this
      omega
    · exact h2
  have : IsKleinFour ↥E := ⟨L.card_eq, hexp⟩
  obtain ⟨φ, hφ⟩ := CFSG.kleinFour_automorphism_transitive ↥E ⟨z, hzE⟩ ⟨e, he⟩
    (fun h => hz1 (congrArg Subtype.val h)) (fun h => he1 (congrArg Subtype.val h))
  have hφmem : φ ∈ autOn (YE153 Mc M E ⊔ TE153 T E) E := by
    rw [r66.induces_GL]; exact Subgroup.mem_top φ
  obtain ⟨g, hg, hgφ⟩ := Subgroup.mem_map.mp hφmem
  have hg' : (g : G) ∈ YE153 Mc M E ⊔ TE153 T E := hg
  have hcoe : e = (g : G) * z * (g : G)⁻¹ := by
    have h1 := congrArg Subtype.val hφ
    rw [← hgφ, A1b.conjAct_coe] at h1
    exact h1.symm
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (YE153 Mc M E) (TE153 T E)
    (TE153_le_normalizer_YE153 c)
  have hg'' : (g : G) ∈ (YE153 Mc M E : Set G) * (TE153 T E : Set G) := by
    rw [← hmul]; exact hg'
  obtain ⟨a, ha, τ, hτ, hat⟩ := Set.mem_mul.mp hg''
  refine ⟨a, ha, ?_⟩
  have hτz : τ * z * τ⁻¹ = z := by
    have h2 := Subgroup.mem_centralizer_iff.mp (c.hyp.T_le_centralizer_Z hτ.1) z hz
    rw [← h2]; group
  rw [hcoe, ← hat]
  calc a * z * a⁻¹ = a * (τ * z * τ⁻¹) * a⁻¹ := by rw [hτz]
    _ = (a * τ) * z * (a * τ)⁻¹ := by group

theorem commute_XE153_FE153B (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (hX : XE153 E = oTwoUpper (thompsonJ (G0_153 T Mc M E s))) :
    ∀ x ∈ XE153 E, ∀ f ∈ FE153 E s, x * f = f * x := by
  intro x hx f hf
  have hsT : s ∈ T := gl.s_mem.1
  have hef : s * f * s⁻¹ ∈ E := mem_conjSubgroup_iff.mp hf
  by_cases h1 : s * f * s⁻¹ = 1
  · have hf1 : f = 1 := by
      have e1 : f = s⁻¹ * (s * f * s⁻¹) * s := by group
      rw [e1, h1]; group
    rw [hf1]; simp
  · obtain ⟨⟨z, hz⟩, hz1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp c.hyp.qtfe.omegaOneCenter_ne_bot
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨a, ha, hae⟩ := exists_conj_mem_YE153B c L r66 hz hz1' hef h1
    have hszc : z * s = s * z :=
      Subgroup.mem_centralizer_iff.mp (c.hyp.T_le_centralizer_Z hsT) z hz
    have hsz : s⁻¹ * z * s = z := by
      calc s⁻¹ * z * s = s⁻¹ * (z * s) := by group
        _ = s⁻¹ * (s * z) := by rw [hszc]
        _ = z := by group
    obtain ⟨y, hy⟩ : ∃ y : G, y = s⁻¹ * a * s := ⟨_, rfl⟩
    have hfy : f = y * z * y⁻¹ := by
      rw [hy]
      calc f = s⁻¹ * (s * f * s⁻¹) * s := by group
        _ = s⁻¹ * (a * z * a⁻¹) * s := by rw [hae]
        _ = (s⁻¹ * a * s) * (s⁻¹ * z * s) * (s⁻¹ * a * s)⁻¹ := by group
        _ = (s⁻¹ * a * s) * z * (s⁻¹ * a * s)⁻¹ := by rw [hsz]
    have hyYF : y ∈ YF153 Mc M E s := by
      rw [mem_conjSubgroup_iff]
      have : s * y * s⁻¹ = a := by rw [hy]; group
      rw [this]; exact ha
    have hyG0 : y ∈ G0_153 T Mc M E s := Subgroup.mem_sup_left (Subgroup.mem_sup_left hyYF)
    have hN : G0_153 T Mc M E s ≤ Subgroup.normalizer (XE153 E : Set G) := by
      rw [hX]
      exact (B6.le_normalizer_thompsonJ _).trans (normalizer_le_normalizer_oTwoUpper _)
    have hx' : y⁻¹ * x * y ∈ XE153 E := by
      have := (Subgroup.mem_normalizer_iff.mp (hN ((G0_153 T Mc M E s).inv_mem hyG0)) x).mp hx
      simpa using this
    have hcomm : z * (y⁻¹ * x * y) = (y⁻¹ * x * y) * z :=
      Subgroup.mem_centralizer_iff.mp (oTwoUpper_le _ hx') z (r66.Z_le_E hz)
    calc x * f = x * (y * z * y⁻¹) := by rw [← hfy]
      _ = y * ((y⁻¹ * x * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * x * y)) * y⁻¹ := by rw [← hcomm]
      _ = (y * z * y⁻¹) * x := by group
      _ = f * x := by rw [← hfy]

theorem Z_le_FE153B (c : Ctx153 G T Mc M V₁ V₂ t) (r66 : Res15366B T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) : quasithinOmegaOneCenter T ≤ FE153 E s := by
  intro z hz
  rw [mem_conjSubgroup_iff]
  have hszc : z * s = s * z :=
    Subgroup.mem_centralizer_iff.mp (c.hyp.T_le_centralizer_Z gl.s_mem.1) z hz
  have h1 : s * z * s⁻¹ = z := by
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hszc]
      _ = z := by group
  rw [h1]
  exact r66.Z_le_E hz

theorem card_sup_E_FE153B (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    Nat.card ↥(E ⊔ FE153 E s) = 8 := by
  have hV := c.hyp.elemAbelian
  have hFc : Nat.card (FE153 E s) = 4 := card_FE153 L
  have hFn : FE153 E s ≤ Subgroup.normalizer (E : Set G) :=
    (FE153_le_V c L gl).trans (HypF91.le_normalizer_of_isElemAbelian_le hV L.le_V)
  have hprod := S143.card_sup_mul_card_inf_of_le_normalizer hFn
  rw [L.card_eq, hFc] at hprod
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := c.hyp.lemma_15_3_2_two.2
  have hZle : Nat.card (quasithinOmegaOneCenter T) ≤ Nat.card ↥(E ⊓ FE153 E s) :=
    Subgroup.card_le_of_le (le_inf r66.Z_le_E (Z_le_FE153B c r66 gl))
  have hEle : Nat.card E ≤ Nat.card ↥(E ⊔ FE153 E s) := Subgroup.card_le_of_le le_sup_left
  have hne4 : Nat.card ↥(E ⊔ FE153 E s) ≠ 4 := by
    intro h4
    have hle : Nat.card ↥(E ⊔ FE153 E s) ≤ Nat.card ↥E := by rw [L.card_eq]; exact h4.le
    have hEF : E = E ⊔ FE153 E s := Subgroup.eq_of_le_of_card_ge le_sup_left hle
    have hFE : FE153 E s ≤ E := by
      have h' : FE153 E s ≤ E ⊔ FE153 E s := le_sup_right
      rwa [← hEF] at h'
    exact FE153_ne_E gl (Subgroup.eq_of_le_of_card_ge hFE (by rw [hFc, L.card_eq]))
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.card ↥(E ⊔ FE153 E s) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.card ↥(E ⊓ FE153 E s) := ⟨_, rfl⟩
  rw [← ha, ← hb] at hprod
  rw [← hb, hZ2] at hZle
  rw [← ha, L.card_eq] at hEle
  rw [← ha] at hne4 ⊢
  have ha5 : 5 ≤ a := by omega
  have hb3 : b ≤ 3 := by
    by_contra hb3
    push Not at hb3
    have h20 : 5 * 4 ≤ a * b := Nat.mul_le_mul ha5 hb3
    linarith
  interval_cases b <;> omega

theorem not_totSingular_EFB (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    ¬ IsTotSingular153 T M V₁ V₂ (E ⊔ FE153 E s) := by
  rintro ⟨hle, h1, -⟩
  have hV := c.hyp.elemAbelian
  have hV₁N : V₁ ≤ Subgroup.normalizer ((E ⊔ FE153 E s : Subgroup G) : Set G) :=
    c.decomp.le₁.trans (HypF91.le_normalizer_of_isElemAbelian_le hV hle)
  have hprod := S143.card_sup_mul_card_inf_of_le_normalizer hV₁N
  rw [h1, Subgroup.card_bot, card_sup_E_FE153B c L r66 gl, c.decomp.card₁] at hprod
  have hcard : Nat.card ↥((E ⊔ FE153 E s) ⊔ V₁) ≤ Nat.card (VZ T M) :=
    Subgroup.card_le_of_le (sup_le hle c.decomp.le₁)
  rw [c.hyp.card_VZ] at hcard
  omega

theorem normalizer_EF_leB (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    Subgroup.normalizer ((E ⊔ FE153 E s : Subgroup G) : Set G) ≤ M := by
  by_contra hn
  have hEFV : E ⊔ FE153 E s ≤ VZ T M := sup_le L.le_V (FE153_le_V c L gl)
  have h8 := card_sup_E_FE153B c L r66 gl
  have hbot : ⊥ < E ⊔ FE153 E s := bot_lt_iff_ne_bot.mpr fun h => by
    rw [h, Subgroup.card_bot] at h8
    omega
  have hlt : E ⊔ FE153 E s < VZ T M := lt_of_le_of_ne hEFV fun h => by
    rw [h, c.hyp.card_VZ] at h8
    omega
  exact not_totSingular_EFB c L r66 gl (r46.totSingular_of_normalizer _ hEFV hbot hlt hn)

theorem false_of_XE_eqB (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s)
    (hX : XE153 E = oTwoUpper (thompsonJ (G0_153 T Mc M E s))) : False := by
  have hcomm := commute_XE153_FE153B c L r66 gl hX
  have hXN : XE153 E ≤ Subgroup.normalizer ((E ⊔ FE153 E s : Subgroup G) : Set G) := by
    intro x hx
    have hxE : ∀ e ∈ E, e * x = x * e := Subgroup.mem_centralizer_iff.mp (oTwoUpper_le _ hx)
    have hle : E ⊔ FE153 E s ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun e he => ?_) (fun f hf => ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]; exact (hxE e he).symm
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
          rw [Set.mem_singleton_iff.mp hh]; exact hcomm x hx f hf
    refine Subgroup.centralizer_le_normalizer _ ?_
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hle hw) x (Set.mem_singleton x)).symm
  exact r67.XE_not_le (fun x hx => normalizer_EF_leB c r46 L r66 gl (hXN hx))

theorem closing_153B (hF : F6.TheoremF618) (hI : Stage1531InspectB)
    (c : Ctx153 G T Mc M V₁ V₂ t) (r45 : Res15345 T Mc M V₁ V₂) (r46 : Res15346 T M V₁ V₂)
    (r49 : Res15349 T Mc M V₁) (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) (r68 : Res15368 T Mc M E s) :
    False := by
  have hne : pCoreOf 2 (G0_153 T Mc M E s) ≠ ⊥ := by
    intro hbot
    have h0 : VZ T M ≤ ⊥ := hbot ▸ r68.V_le_pCore
    have h16 := c.hyp.card_VZ
    rw [le_bot_iff.mp h0, Subgroup.card_bot] at h16
    omega
  have hq := stronglyQuasithin_of_pCoreOf_ne_bot c.hyp.qtfe.qtke hne
  have hk := kGroup_of_pCoreOf_ne_bot c.hyp.qtfe.qtke c.hyp.qtfe.simple c.hyp.qtfe.nonabelian hne
  rcases r68.triple.f6_18 hF hq hk with ⟨-, -, -, hconc⟩ | ⟨-, -, -, -, hcyc⟩
  · rcases hI G T Mc M V₁ V₂ E t s c r45 r46 r49 L r66 r67 gl r68 hconc with hA | hB
    · exact false_of_XE_eqB c r46 L r66 r67 gl hA
    · exact false_of_nonsolvable c r45 r49 r67 hB
  · apply hcyc
    have hpc : Open.pCore 2 ↥(G0_153 T Mc M E s) = CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
      Subgroup.map_injective (G0_153 T Mc M E s).subtype_injective r68.pCore_eq
    have hbot : (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map
        (QuotientGroup.mk' (Open.pCore 2 ↥(G0_153 T Mc M E s))) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hpc]
    rw [hbot]
    infer_instance

end Geometry

end CFSG.Quasithin
