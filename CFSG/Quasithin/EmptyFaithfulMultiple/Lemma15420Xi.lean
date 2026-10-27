module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Diag

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}

namespace Setting15419

variable (s : Setting15419 G T)

omit [Finite G] in
theorem X₁_le_centralizer_V₂ :
    s.X₁ ≤ Subgroup.centralizer ((⁅VZ T s.M₁, s.X₂⁆ : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, -, -, -, hinf, -⟩ := s.dataX
  have hVN : s.M₁ ≤ Subgroup.normalizer (VZ T s.M₁ : Set G) := le_normalizer_conjClosure _ _
  have hXN₂ : s.X ≤ Subgroup.normalizer ((⁅VZ T s.M₁, s.X₂⁆ : Subgroup G) : Set G) :=
    fun x hx => A4.mem_normalizer_commutator (hVN (s.le_X hx)) (s.X_le_normalizer_X₂ hx)
  have hV₂V : ⁅VZ T s.M₁, s.X₂⁆ ≤ VZ T s.M₁ :=
    commutator_le_of_le_normalizer ((s.X₂_le_X.trans s.le_X).trans hVN)
  have h1 : ⁅⁅VZ T s.M₁, s.X₂⁆, s.X₁⁆ ≤ ⁅VZ T s.M₁, s.X₂⁆ :=
    commutator_le_of_le_normalizer (s.X₁_le_X.trans hXN₂)
  have h2 : ⁅⁅VZ T s.M₁, s.X₂⁆, s.X₁⁆ ≤ ⁅VZ T s.M₁, s.X₁⁆ := Subgroup.commutator_mono hV₂V le_rfl
  have h3 : ⁅⁅VZ T s.M₁, s.X₂⁆, s.X₁⁆ = ⊥ := le_bot_iff.mp (hinf ▸ le_inf h2 h1)
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)

omit [Finite G] in
theorem X₂_le_centralizer_V₁ :
    s.X₂ ≤ Subgroup.centralizer ((⁅VZ T s.M₁, s.X₁⁆ : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, -, -, -, hinf, -⟩ := s.dataX
  have hVN : s.M₁ ≤ Subgroup.normalizer (VZ T s.M₁ : Set G) := le_normalizer_conjClosure _ _
  have hXN₁ : s.X ≤ Subgroup.normalizer ((⁅VZ T s.M₁, s.X₁⁆ : Subgroup G) : Set G) :=
    fun x hx => A4.mem_normalizer_commutator (hVN (s.le_X hx)) (s.X_le_normalizer_X₁ hx)
  have hV₁V : ⁅VZ T s.M₁, s.X₁⁆ ≤ VZ T s.M₁ :=
    commutator_le_of_le_normalizer ((s.X₁_le_X.trans s.le_X).trans hVN)
  have h1 : ⁅⁅VZ T s.M₁, s.X₁⁆, s.X₂⁆ ≤ ⁅VZ T s.M₁, s.X₁⁆ :=
    commutator_le_of_le_normalizer (s.X₂_le_X.trans hXN₁)
  have h2 : ⁅⁅VZ T s.M₁, s.X₁⁆, s.X₂⁆ ≤ ⁅VZ T s.M₁, s.X₂⁆ := Subgroup.commutator_mono hV₁V le_rfl
  have h3 : ⁅⁅VZ T s.M₁, s.X₁⁆, s.X₂⁆ = ⊥ := le_bot_iff.mp (hinf ▸ le_inf h1 h2)
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)

theorem mem_X₁_of_odd (hyp : MultipleCentralizerHypothesis G T) {y : G} (hy : y ∈ s.X)
    (hyo : Odd (orderOf y))
    (hyC : y ∈ Subgroup.centralizer ((⁅VZ T s.M₁, s.X₂⁆ : Subgroup G) : Set G)) : y ∈ s.X₁ := by
  obtain ⟨hX, hO₁, hO₂, -, hi₂, -, -, -, hc₂, -⟩ := s.dataX
  have hVN : s.M₁ ≤ Subgroup.normalizer (VZ T s.M₁ : Set G) := le_normalizer_conjClosure _ _
  exact mem_of_odd_of_mem_centralizer (s.isElemAbelian_VZ hyp)
    ((s.X₂_le_X.trans s.le_X).trans hVN) hO₁ hO₂ hi₂ hc₂ (s.X₂_le_X.trans s.X_le_normalizer_X₁)
    s.X₁_le_centralizer_V₂ (hX ▸ hy) hyo hyC

theorem mem_X₂_of_odd (hyp : MultipleCentralizerHypothesis G T) {y : G} (hy : y ∈ s.X)
    (hyo : Odd (orderOf y))
    (hyC : y ∈ Subgroup.centralizer ((⁅VZ T s.M₁, s.X₁⁆ : Subgroup G) : Set G)) : y ∈ s.X₂ := by
  obtain ⟨hX, hO₁, hO₂, hi₁, -, -, -, hc₁, -⟩ := s.dataX
  have hVN : s.M₁ ≤ Subgroup.normalizer (VZ T s.M₁ : Set G) := le_normalizer_conjClosure _ _
  have hy' : y ∈ s.X₂ ⊔ s.X₁ := by rw [sup_comm, ← hX]; exact hy
  exact mem_of_odd_of_mem_centralizer (s.isElemAbelian_VZ hyp)
    ((s.X₁_le_X.trans s.le_X).trans hVN) hO₂ hO₁ hi₁ hc₁ (s.X₁_le_X.trans s.X_le_normalizer_X₂)
    s.X₂_le_centralizer_V₁ hy' hyo hyC

end Setting15419

namespace Config15420

variable {s : Setting15419 G T} {I₀ : Subgroup G}

theorem irreducible (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) {Y : Subgroup G} (hNY : pCoreOf 2 s.X ≤ Y) (hYX : Y ≤ s.X)
    (hY : T ⊓ I₀ ≤ Subgroup.normalizer (Y : Set G)) : Y = pCoreOf 2 s.X ∨ Y = s.X := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne₁, hne₂⟩ := hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hX, -, -, hi₁, hi₂, -, -, hc₁, -⟩ := s.dataX
  set N := pCoreOf 2 s.X with hNdef
  set V := VZ T s.M₁ with hVdef
  set V₁ := (⁅V, s.X₁⁆ : Subgroup G) with hV₁def
  set V₂ := (⁅V, s.X₂⁆ : Subgroup G) with hV₂def
  have hV := s.isElemAbelian_VZ hyp
  have hVN : s.M₁ ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  have hV₁V : V₁ ≤ V := commutator_le_of_le_normalizer ((s.X₁_le_X.trans s.le_X).trans hVN)
  have hV₂V : V₂ ≤ V := commutator_le_of_le_normalizer ((s.X₂_le_X.trans s.le_X).trans hVN)
  have hV₁2 : ∀ v ∈ V₁, v * v = 1 := fun v hv => by rw [← sq]; exact hV.2 v (hV₁V hv)
  have hXV₁ : s.X ≤ Subgroup.normalizer (V₁ : Set G) := fun x hx =>
    A4.mem_normalizer_commutator (hVN (s.le_X hx)) (s.X_le_normalizer_X₁ hx)
  have hXV₂ : s.X ≤ Subgroup.normalizer (V₂ : Set G) := fun x hx =>
    A4.mem_normalizer_commutator (hVN (s.le_X hx)) (s.X_le_normalizer_X₂ hx)
  have hNC : N ≤ Subgroup.centralizer (V : Set G) := s.pCoreOf_X_le_centralizer hyp h12
  have hpow := (s.relIndex_X_and_pow hyp h12).2
  have hQ₁ : pCoreOf 2 s.X₁ ≤ N := s.pCoreOf_le_pCoreOf_X s.X₁_le_X s.X_le_normalizer_X₁
  have hQ₂ : pCoreOf 2 s.X₂ ≤ N := s.pCoreOf_le_pCoreOf_X s.X₂_le_X s.X_le_normalizer_X₂
  obtain ⟨a, haJ, ha2, haC₂, haC₁⟩ := s.exists_diag hyp
  have haTI : a ∈ T ⊓ I₀ := c.lt.le (s.baum_le_T₀ (L15420.thompsonJ_le_baum T haJ))
  have haM : a ∈ s.M₁ := s.inM₁.2 haTI.1
  have haN₁ : a ∈ Subgroup.normalizer (V₁ : Set G) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hS₁, -⟩ := s.dataX
    exact A4.mem_normalizer_commutator (hVN haM) (hS₁ (L15420.thompsonJ_le_baum T haJ))
  obtain ⟨u, huTI, hu₁, hu₂⟩ := c.exists_swap' hyp h12
  have key : s.X₁ ≤ Y ∨ s.X₂ ≤ Y → False := by
    have hYu : Y.map (MulAut.conj u).toMonoidHom = Y := map_conj_eq_of_mem_normalizer (hY huTI)
    intro h
    have h12' : s.X₁ ≤ Y ∧ s.X₂ ≤ Y := by
      rcases h with h | h
      · refine ⟨h, ?_⟩
        rw [← hu₁, ← hYu]
        exact Subgroup.map_mono h
      · refine ⟨?_, h⟩
        rw [← hu₂, ← hYu]
        exact Subgroup.map_mono h
    apply hne₂
    refine le_antisymm hYX ?_
    rw [hX]
    exact sup_le h12'.1 h12'.2
  obtain ⟨y₀, hy₀Y, hy₀N⟩ : ∃ y₀ ∈ Y, y₀ ∉ N := by
    by_contra h
    push Not at h
    exact hne₁ (le_antisymm h hNY)
  obtain ⟨k, hko, hkN⟩ := L15420.exists_odd_pow_not_mem hy₀N (hpow y₀ (hYX hy₀Y))
  set y := y₀ ^ k with hydef
  have hyY : y ∈ Y := Y.pow_mem hy₀Y k
  have hyX : y ∈ s.X := hYX hyY
  set cc := a * y * a⁻¹ * y⁻¹ with hccdef
  have hayY : a * y * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hY haTI) y).mp hyY
  have hccY : cc ∈ Y := Y.mul_mem hayY (Y.inv_mem hyY)
  have hccC₂ : cc ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : y⁻¹ * v * y ∈ V₂ := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXV₂ hyX)) v).mp hv
      simpa using this
    have hav : a⁻¹ * (y⁻¹ * v * y) * a = y⁻¹ * v * y := by
      have := Subgroup.mem_centralizer_iff.mp haC₂ _ hw
      calc a⁻¹ * (y⁻¹ * v * y) * a = a⁻¹ * ((y⁻¹ * v * y) * a) := by group
        _ = a⁻¹ * (a * (y⁻¹ * v * y)) := by rw [this]
        _ = y⁻¹ * v * y := by group
    have hav' : a * v * a⁻¹ = v := by
      have := Subgroup.mem_centralizer_iff.mp haC₂ _ hv
      calc a * v * a⁻¹ = v * a * a⁻¹ := by rw [this]
        _ = v := by group
    have key : cc * v * cc⁻¹ = v := by
      calc cc * v * cc⁻¹ = a * y * (a⁻¹ * (y⁻¹ * v * y) * a) * y⁻¹ * a⁻¹ := by
            rw [hccdef]; group
        _ = a * v * a⁻¹ := by rw [hav]; group
        _ = v := hav'
    calc v * cc = cc * v * cc⁻¹ * cc := by rw [key]
      _ = cc * v := by group
  by_cases hccN : cc ∈ N
  ·
    have hcard := L15420.card_inf_centralizer_eq_two hc₁
      (L15420.isPGroup_zpowers_of_mul_self ha2) haN₁ haC₁
    obtain ⟨f, hf, hf1⟩ := (Subgroup.bot_or_exists_ne_one
      (V₁ ⊓ Subgroup.centralizer ({a} : Set G))).resolve_left (by
        intro h
        rw [h, Subgroup.card_bot] at hcard
        omega)
    have hfa : a * f * a⁻¹ = f := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hf.2
      calc a * f * a⁻¹ = f * a * a⁻¹ := by rw [this]
        _ = f := by group
    have hyf : y * f * y⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hXV₁ hyX) f).mp hf.1
    have hccv : ∀ v ∈ V, cc * v = v * cc := fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hNC hccN) v hv).symm
    have hfix : a * (y * f * y⁻¹) * a⁻¹ = y * f * y⁻¹ := by
      have e : a * (y * f * y⁻¹) * a⁻¹ = cc * (y * (a * f * a⁻¹) * y⁻¹) * cc⁻¹ := by
        rw [hccdef]; group
      rw [e, hfa]
      have := hccv _ (hV₁V hyf)
      calc cc * (y * f * y⁻¹) * cc⁻¹ = (y * f * y⁻¹) * cc * cc⁻¹ := by rw [this]
        _ = y * f * y⁻¹ := by group
    have hyf1 : y * f * y⁻¹ ≠ 1 := fun h => hf1 (by
      calc f = y⁻¹ * (y * f * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group)
    have hyfC : y * f * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y * f * y⁻¹ * a = a * (y * f * y⁻¹) * a⁻¹ * a := by rw [hfix]
        _ = a * (y * f * y⁻¹) := by group
    have he := L15420.eq_of_card_eq_two hcard ⟨hyf, hyfC⟩ hf hyf1 hf1
    have hyfc : y * f = f * y := by
      calc y * f = y * f * y⁻¹ * y := by group
        _ = f * y := by rw [he]
    have hyC₁ : y ∈ Subgroup.centralizer (V₁ : Set G) :=
      mem_centralizer_of_card_eq_four hc₁ hV₁2 (hXV₁ hyX) hko hf.1 hf1 hyfc
    have hyX₂ : y ∈ s.X₂ := s.mem_X₂_of_odd hyp hyX hko hyC₁
    have hyQ : y ∉ pCoreOf 2 s.X₂ := fun h => hkN (hQ₂ h)
    exact key (Or.inr ((L15420.le_sup_zpowers_of_relIndex_three hi₂ hyX₂ hyQ).trans
      (sup_le (hQ₂.trans hNY) (Subgroup.zpowers_le.mpr hyY))))
  ·
    obtain ⟨j, hjo, hjN⟩ := L15420.exists_odd_pow_not_mem hccN (hpow cc (hYX hccY))
    have hcjY : cc ^ j ∈ Y := Y.pow_mem hccY j
    have hcjC : cc ^ j ∈ Subgroup.centralizer (V₂ : Set G) := Subgroup.pow_mem _ hccC₂ j
    have hcjX₁ : cc ^ j ∈ s.X₁ := s.mem_X₁_of_odd hyp (hYX hcjY) hjo hcjC
    have hcjQ : cc ^ j ∉ pCoreOf 2 s.X₁ := fun h => hjN (hQ₁ h)
    exact key (Or.inl ((L15420.le_sup_zpowers_of_relIndex_three hi₁ hcjX₁ hcjQ).trans
      (sup_le (hQ₁.trans hNY) (Subgroup.zpowers_le.mpr hcjY))))

theorem isXi (hyp : MultipleCentralizerHypothesis G T) (h12 : Stmt15412 G T)
    (c : Config15420 s I₀) : IsXi (T ⊓ I₀) s.X := by
  obtain ⟨hi, hpow⟩ := s.relIndex_X_and_pow hyp h12
  have hTX : T ⊓ I₀ ≤ Subgroup.normalizer (s.X : Set G) :=
    (inf_le_left.trans s.inM₁.2).trans (M₁_le_normalizer_X h12 s)
  have hT : T ≠ ⊥ := by
    obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
    have := hyp.simple
    rw [← hS]
    exact sylow_ne_bot hyp.nonabelian S
  have hZ : quasithinOmegaOneCenter T ≠ ⊥ :=
    CFSG.Quasithin.quasithinOmegaOneCenter_ne_bot hyp.sylow.1 hT
  refine ⟨s.X_eq_oTwoUpper, hTX, fun h => hZ (le_bot_iff.mp (h ▸ c.omegaOneCenter_le_R hyp)),
    3, Nat.prime_three, by norm_num, hpow, Or.inl (by rw [hi]; norm_num), ?_⟩
  intro Y h1 h2 h3
  have hNY : pCoreOf 2 s.X ≤ Y := le_sup_right.trans h1
  rcases c.irreducible hyp h12 hNY h2 h3 with h | h
  · left
    exact le_antisymm (h ▸ le_sup_right) h1
  · exact Or.inr h

end Config15420

end CFSG.Quasithin.EmptyFaithfulMultiple
