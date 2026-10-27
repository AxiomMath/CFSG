module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted TableBOrth

namespace OrthNs

section Recipe

variable {K : Type} [Field K] [Finite K] [CharP K 2]

section Center


theorem center_data_omegaPlus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) :
    Subgroup.center (OrthRest.RPlus K m) = ⊥ ∧ GGCenterPrime p (OrthRest.RPlus K m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero m := ⟨by omega⟩
  obtain ⟨hbij, hZ⟩ := OrthRest.spinPlus_bij (K := K) hm
  have : Finite (spinGroup (quadPlus m K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (plusDatum m K hm).isFiniteType (Dv := (plusDatum m K hm).divisible) rfl
  exact OrthRest.center_data (R := OrthRest.RPlus K m) (MulEquiv.ofBijective _ hbij) hZ
    (fun E _ _ π hπ hcen hc =>
      CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
        (CFSG.LieType.Steinberg.SpinPlus.isCTGroupDatum hm) (plusDatum_steinbergExtras hm)
        (CFSG.LieType.Steinberg.SpinPlus.chevalleyExtras hm O
          CFSG.LieType.Steinberg.SpinPlus.commC
          (CFSG.LieType.Steinberg.SpinPlus.commutatorFormula hm O)) E π hπ hcen hc) hp hp2

end Center

theorem evenSignedEltSC_omegaPlus {p m : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (hm : 1 ≤ m) : GGTorusEvenSignedEltSC p (OrthRest.RPlus K m) := by
  have h := torusEvenSignedEltSC_omega hp hpq (qPlusForm K m) (nondegenerate_qPlusForm m)
  rw [coe_qPlusForm] at h
  exact ggTorusEvenSignedEltSC_of_mulEquiv
    (projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (K := K) hm)).symm h

theorem evenSignedEltSC_omegaMinus {p m : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusEvenSignedEltSC p (OrthRest.RMinus K m b c) := by
  have h := torusEvenSignedEltSC_omega hp hpq (qMinusForm K m b c)
    (nondegenerate_qMinusForm m hirr)
  rw [coe_qMinusForm] at h
  exact ggTorusEvenSignedEltSC_of_mulEquiv
    (projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c)).symm h

end Recipe

section Line

open NbrOrth

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggNoInvariantLineSC_of_evenSignedEltSC [Finite R] (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusEvenSignedEltSC p R) : CorFourTwoOpen.GGNoInvariantLineSC p R I := by
  intro Eh hEhI hEhA h3 hscR Λ hΛ hΛp
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := OrthRest.conj_injective hZ
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hmap : E.map (MulAut.conj : R →* MulAut R) = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI hφ)
  have hcardE : Nat.card E = Nat.card Eh := by
    rw [Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEhA a.2 b.2
    · rw [map_pow, map_one]
      exact hEhA.2 _ hx
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    show MulAut.conj g ∈ Eh
    refine hscR g (fun a ha => ?_) hgp
    obtain ⟨y, rfl⟩ := hI (hEhI ha)
    have hy : y ∈ E := ha
    rw [MulAut.conj_apply, ← hg y hy, mul_inv_cancel_right]
  obtain ⟨k, τ, hτinj, hτE, hdinv, hswap⟩ := h E hEe (hcardE ▸ h3) hscE
  have hk : 3 ≤ k := by
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have h1 : Nat.card τ.range = Nat.card (Fin k → Multiplicative (ZMod p)) :=
      Nat.card_range_of_injective hτinj
    rw [hτE, hcardE, hcV] at h1
    rw [h1] at h3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  set Λ' := Λ.comap (MulAut.conj : R →* MulAut R) with hΛ'
  have hΛmap : Λ'.map (MulAut.conj : R →* MulAut R) = Λ := by
    rw [hΛ', Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI (hΛ hφ))
  have hΛ'card : Nat.card Λ' = p := by
    rw [Nat.card_congr (Λ'.equivMapOfInjective _ hinj).toEquiv, hΛmap, hΛp]
  have hΛ'E : Λ' ≤ E := fun e he => hΛ he
  by_contra hcon
  push Not at hcon
  have hinv : ∀ w : R, (∀ f, ∃ f', w * τ f * w⁻¹ = τ f') → ∀ e ∈ Λ', w * e * w⁻¹ ∈ Λ' := by
    intro w hw e he
    have hwN : MulAut.conj w ∈ Subgroup.normalizer (Eh : Set (MulAut R)) := by
      refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
      obtain ⟨y, rfl⟩ := hI (hEhI hb)
      have hy : y ∈ E := hb
      rw [← hτE] at hy
      obtain ⟨f, rfl⟩ := hy
      obtain ⟨f', hf'⟩ := hw f
      rw [← map_inv, ← map_mul, ← map_mul, hf']
      show τ f' ∈ E
      rw [← hτE]
      exact ⟨f', rfl⟩
    have h1 := hcon w hwN (MulAut.conj e) he
    show MulAut.conj (w * e * w⁻¹) ∈ Λ
    rw [map_mul, map_mul, map_inv]
    exact h1
  rcases eq_bot_or_eq_top_of_dinv hp hp2 hk (Λ'.comap τ)
      (fun i j hij f hf => by
        obtain ⟨w, hw⟩ := hdinv i j hij
        show τ (dinv i j f) ∈ Λ'
        rw [← hw]
        exact hinv w (fun f => ⟨_, hw f⟩) _ hf)
      (fun j t u hjt hju htu f hf => by
        obtain ⟨w, hw⟩ := hswap j t u hjt hju htu
        show τ (f ∘ ⇑(swapComm j t u)⁻¹) ∈ Λ'
        rw [← hw]
        exact hinv w (fun f => ⟨_, hw f⟩) _ hf) with hbot | htop
  · have h1 : Λ' = ⊥ := by
      rw [← Subgroup.map_comap_eq_self (hΛ'E.trans hτE.ge), hbot, Subgroup.map_bot]
    rw [h1, Subgroup.card_bot] at hΛ'card
    exact hp.one_lt.ne hΛ'card
  · have h1 : E ≤ Λ' := by
      rw [← hτE]
      rintro _ ⟨f, rfl⟩
      exact (htop ▸ Subgroup.mem_top f : f ∈ Λ'.comap τ)
    have h2 := Subgroup.card_le_of_le h1
    rw [hcardE, hΛ'card] at h2
    have h4 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h4
    omega

end Line

section RecipeLabels


theorem recipeOmegaPlus_torusIrredSC {l n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hl : 3 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ CorFourTwoOpen.GGTorusIrredSC p R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  obtain ⟨hZ, hcp⟩ := center_data_omegaPlus (K := K) hp hp2 hl
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggTorusIrredSC_of_evenSignedEltSC hp hp2
    (fun _ h => h) hZ hcp (evenSignedEltSC_omegaPlus hp hpK (by omega))⟩

theorem recipeOmegaMinus_torusIrredSC {m n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hm : 3 ≤ m) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ CorFourTwoOpen.GGTorusIrredSC p R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  obtain ⟨hZ, hcp⟩ := ggOrthRestCenterInput_holds.1 K n m p b c hK hm hp hpn hbc
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ,
    ggTorusIrredSC_of_evenSignedEltSC hp hp2 (fun _ h => h) hZ hcp
      (evenSignedEltSC_omegaMinus hp hpK hbc)⟩

theorem recipeOmegaPlus_noInvariantLineSC {l n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hl : 3 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F => Q R I F ∧
      (GGCenterCoprime p R ∧ CorFourTwoOpen.GGNoInvariantLineSC p R I) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  obtain ⟨hZ, hcp⟩ := center_data_omegaPlus (K := K) hp hp2 hl
  exact ⟨K, inferInstance, inferInstance, hK, hQ, CorFourTwoOpen.ggCenterCoprime_of_centerPrime hcp,
    ggNoInvariantLineSC_of_evenSignedEltSC hp hp2 (fun _ h => h) hZ
      (evenSignedEltSC_omegaPlus hp hpK (by omega))⟩

theorem recipeOmegaMinus_noInvariantLineSC {m n p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1)
    (hm : 3 ≤ m) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧
      (GGCenterCoprime p R ∧ CorFourTwoOpen.GGNoInvariantLineSC p R I) := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  obtain ⟨hZ, hcp⟩ := ggOrthRestCenterInput_holds.1 K n m p b c hK hm hp hpn hbc
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ,
    CorFourTwoOpen.ggCenterCoprime_of_centerPrime hcp,
    ggNoInvariantLineSC_of_evenSignedEltSC hp hp2 (fun _ h => h) hZ
      (evenSignedEltSC_omegaMinus hp hpK hbc)⟩

end RecipeLabels


end OrthNs

open OrthNs

@[expose] def GGOrthNsLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1

@[expose] def GGOrthNsVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGOrthNsLabel p lab ∧ GGCorFourTwoOpenVacLabel p lab

theorem ggBstarInnerDiagLInputOn_orthNsVac (ha₀ : GGLNoncyclicInput) :
    GGBstarInnerDiagLInputOn GGOrthNsVacLabel :=
  ggBstarInnerDiagLInputOn_vac ha₀ GGOrthNsLabel

section Labels


theorem largeEvenLabelAll_torusIrredSC_orthNs {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : GGOrthNsLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => CorFourTwoOpen.GGTorusIrredSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  dsimp only at htag hl hpn ⊢
  intro Q hQ
  rcases htag with h | h <;> subst h <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_torusIrredSC hp hpn (by omega) hQ
  · split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_torusIrredSC hp hpn (by omega) hQ

theorem largeEvenLabelAll_torusNbrSC_orthNs {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : GGOrthNsLabel p lab) : LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSC p R I :=
  (largeEvenLabelAll_torusIrredSC_orthNs hp h).mono fun _ _ _ _ hT =>
    ggTorusNbrSC_of_ggTorusIrredSC hp hT

theorem ggTableBIrredInputOn_orthNs : GGTableBIrredInputOn GGOrthNsLabel :=
  CorFourTwoOpen.ggTableBIrredInputOn_of_labelsSC fun _ _ hp _ h =>
    largeEvenLabelAll_torusIrredSC_orthNs hp h

theorem ggTableBNbrInnerInputOn_orthNs : GGTableBNbrInnerInputOn GGOrthNsLabel :=
  ggTableBNbrInnerInputOn_of_labelsSC fun _ _ hp _ h => largeEvenLabelAll_torusNbrSC_orthNs hp h

theorem ggTableBCxInputOn_orthNsVac (ha₀ : GGLNoncyclicInput) :
    GGTableBCxInputOn GGOrthNsVacLabel :=
  ggTableBCxInputOn_of_irred (ggBstarInnerDiagLInputOn_orthNsVac ha₀)
    (ggTableBIrredInputOn_orthNs.mono fun _ _ h => h.1)

theorem ggTableBModuleInputOn_orthNsVac (ha₀ : GGLNoncyclicInput) :
    GGTableBModuleInputOn GGOrthNsVacLabel :=
  ggTableBModuleInputOn_of_irred (ggBstarInnerDiagLInputOn_orthNsVac ha₀)
    (ggTableBIrredInputOn_orthNs.mono fun _ _ h => h.1)

theorem ggTableBActionInputOn_orthNsVac (ha₀ : GGLNoncyclicInput) :
    GGTableBActionInputOn GGOrthNsVacLabel :=
  ggTableBActionInputOn_of_irred (ggBstarInnerDiagLInputOn_orthNsVac ha₀)
    (ggTableBIrredInputOn_orthNs.mono fun _ _ h => h.1)

theorem largeEvenLabelAll_noInvariantLineSC_orthNs {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (h : GGOrthNsLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGCenterCoprime p R ∧ CorFourTwoOpen.GGNoInvariantLineSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  dsimp only at htag hl hpn ⊢
  intro Q hQ
  rcases htag with h | h <;> subst h <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_noInvariantLineSC hp hpn (by omega) hQ
  · split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_noInvariantLineSC hp hpn (by omega) hQ

theorem ggLNoInvariantLineInputOn_orthNs : GGLNoInvariantLineInputOn GGOrthNsLabel :=
  CorFourTwoOpen.ggLNoInvariantLineInputOn_of_labelsSC fun _ _ hp _ h =>
    largeEvenLabelAll_noInvariantLineSC_orthNs hp h

end Labels

end CFSG.StandardType

end
