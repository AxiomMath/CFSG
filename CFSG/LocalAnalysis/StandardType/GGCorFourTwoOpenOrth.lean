module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerOrth
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted

namespace CorFourTwoOpen

section Generic

variable {G : Type*} [Group G]

theorem isPGroup_of_elemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem eq_of_lt_of_card_le_mul [Finite G] {p : ℕ} (hp : p.Prime) {Eb M Eh : Subgroup G}
    (hEh : IsPGroup p Eh) (h1 : Eb < M) (h2 : M ≤ Eh) (hcard : Nat.card Eh ≤ p * Nat.card Eb) :
    M = Eh := by
  have := Fact.mk hp
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hEh.to_le h2)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hEh.to_le (h1.le.trans h2))
  have hlt := Subgroup.card_lt_of_lt h1
  rw [ha, hb] at hlt
  have hba : b < a := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  refine Subgroup.eq_of_le_of_card_ge h2 ?_
  rw [ha]
  calc Nat.card Eh ≤ p * Nat.card Eb := hcard
    _ = p ^ (b + 1) := by rw [hb, pow_succ, mul_comm]
    _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos hba

end Generic

section GenericR

variable {p r : ℕ} {R : Type} [Group R]

theorem ggInnerDiagBound_of_elt [Finite R] (hp : p.Prime) {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : TableBOrth.GGBstarElt p r R) : GGInnerDiagBound p r R I := by
  intro Eb Eh hEbI hEb hr h3 hle hEh hcard hnot
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := OrthRest.conj_injective hZ
  set E₀ := Eb.comap (MulAut.conj : R →* MulAut R) with hE₀
  have hmap : E₀.map (MulAut.conj : R →* MulAut R) = Eb := by
    rw [hE₀, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEbI hφ)
  have hcardE₀ : Nat.card E₀ = Nat.card Eb := by
    rw [Nat.card_congr (E₀.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hE₀e : IsElemAbelian p E₀ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEb a.2 b.2
    · rw [map_pow, map_one]
      exact hEb.2 _ hx
  obtain ⟨φ, hφEh, hφI⟩ := Set.not_subset.mp hnot
  have hφEb : φ ∉ Eb := fun h' => hφI (hEbI h')
  have hφp : φ ^ p = 1 := hEh.2 φ hφEh
  have hφfix : ∀ e ∈ E₀, φ e = e := by
    intro e he
    have hce : MulAut.conj e ∈ Eh := hle he
    have hcomm := TableB.IsElemAbelian.comm hEh hφEh hce
    apply hinj
    rw [← TableBOrth.mulAut_mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
  obtain ⟨U, hU, hU2, hUE, hUφ⟩ := h E₀ hE₀e (hcardE₀ ▸ hr) (hcardE₀ ▸ h3) φ hφp hφfix
  have hM : Eb ⊔ Subgroup.zpowers φ = Eh := by
    refine eq_of_lt_of_card_le_mul hp (isPGroup_of_elemAbelian hEh) ?_
      (sup_le hle (Subgroup.zpowers_le.mpr hφEh)) hcard
    refine lt_of_le_of_ne le_sup_left fun h' => hφEb ?_
    rw [h']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers φ)
  have hle2 : Eb ⊔ Subgroup.zpowers φ ≤ TableBOrth.stabSubgroup U := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr (TableBOrth.mem_stabSubgroup_of_le hUφ))
    intro ψ hψ
    obtain ⟨e, rfl⟩ := hI (hEbI hψ)
    refine TableBOrth.mem_stabSubgroup_of_le fun u hu => ?_
    have heE : e ∈ E₀ := by
      rw [hE₀, Subgroup.mem_comap]
      exact hψ
    rw [MulAut.conj_apply]
    exact hUE e heE u hu
  refine ⟨U, hU, hU2, fun ψ hψ u hu => ?_⟩
  have h1 : U.map ψ.toMonoidHom = U := hle2 (hM ▸ hψ)
  rw [← h1]
  exact ⟨u, hu, rfl⟩

theorem ggInnerDiagBound_of_pow {I : Set (MulAut R)}
    (h : ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I) : GGInnerDiagBound p r R I := by
  intro Eb Eh _ _ _ _ _ hEh _ hnot
  exact (hnot fun φ hφ => h φ (hEh.2 φ hφ)).elim

theorem ggCenterCoprime_of_centerPrime (h : GGCenterPrime p R) : GGCenterCoprime p R := by
  intro L' _ _ ψ hψ hker hperf hdvd
  exact h L' ψ hψ hker hperf (hdvd.trans (Subgroup.card_dvd_of_le hker))

theorem ggNoInvariantLineTorus_of_irredElt [Finite R] (hp : p.Prime) {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hC : GGCenterCoprime p R) (h : GGTorusIrredElt p r R) : GGNoInvariantLineTorus p r R I := by
  intro Eh hEhI hEhA hr h3
  refine ⟨hC, fun Λ hΛ hΛp => ?_⟩
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
  obtain ⟨k, τ, W, -, -, hWE, hirr⟩ := h E hEe (hcardE ▸ hr) (hcardE ▸ h3)
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
  have hinv : ∀ w ∈ W, ∀ e ∈ Λ', w * e * w⁻¹ ∈ Λ' := by
    intro w hw e he
    have hwN : MulAut.conj w ∈ Subgroup.normalizer (Eh : Set (MulAut R)) := by
      refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
      obtain ⟨y, rfl⟩ := hI (hEhI hb)
      have hy : y ∈ E := hb
      have h1 := hWE w hw y hy
      rw [← map_inv, ← map_mul, ← map_mul]
      exact h1
    have h1 := hcon w hwN (MulAut.conj e) he
    show MulAut.conj (w * e * w⁻¹) ∈ Λ
    rw [map_mul, map_mul, map_inv]
    exact h1
  rcases hirr Λ' hΛ'E hinv with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hΛ'card
    exact hp.one_lt.ne hΛ'card
  · rw [htop, hcardE] at hΛ'card
    rw [hΛ'card] at h3
    have h4 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h4
    omega

end GenericR

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]

open TableBOrth in
theorem ggInnerDiagBound_omegaPlus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) :
    GGInnerDiagBound p m (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
      (LargeEvenInnSet _) :=
  ggInnerDiagBound_of_elt hp subset_rfl (center_omegaPlus_eq_bot hp hp2 hpq hm)
    (ggBstarElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (by omega)))
      (ggBstarElt_omegaPlusGroup hp hp2 hpq (by omega)))

open TableBOrth in
theorem ggInnerDiagBound_omegaMinus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGInnerDiagBound p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _) :=
  ggInnerDiagBound_of_elt hp subset_rfl (center_omegaMinus_eq_bot hp hp2 hpq hm hirr)
    (ggBstarElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot b c))
      (ggBstarElt_omegaMinusGroup hp hp2 hpq (by omega) hirr))

section Center


theorem ggCenterPrime_omegaMinus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : GGCenterPrime p (OrthRest.RMinus K m b c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, hZ⟩ := OrthRest.spinMinus_bij (K := K) (n := m + 1) (by omega) hbc
  have : Finite (spinGroup (quadMinus (m + 1) K b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hbc)
  exact (OrthRest.center_data (R := OrthRest.RMinus K m b c)
    ((MulEquiv.ofBijective _ hbij).trans (omegaMinusProjEquiv (m + 1) b c).symm) hZ
    (fun E _ _ π hπ hcen hC =>
      CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_coprime hbc
        (by omega) hπ hcen hC) hp hp2).2

theorem ggCenterPrime_omegaPlus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) :
    GGCenterPrime p (OrthRest.RPlus K m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero m := ⟨by omega⟩
  obtain ⟨hbij, hZ⟩ := OrthRest.spinPlus_bij (K := K) hm
  have : Finite (spinGroup (quadPlus m K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (plusDatum m K hm).isFiniteType (Dv := (plusDatum m K hm).divisible) rfl
  exact (OrthRest.center_data (R := OrthRest.RPlus K m) (MulEquiv.ofBijective _ hbij) hZ
    (fun E _ _ π hπ hcen hc =>
      CFSG.LieType.Steinberg.CentralExt.FieldFour.exists_section_of_coprime
        (CFSG.LieType.Steinberg.SpinPlus.isCTGroupDatum hm) (plusDatum_steinbergExtras hm)
        (CFSG.LieType.Steinberg.SpinPlus.chevalleyExtras hm O
          CFSG.LieType.Steinberg.SpinPlus.commC
          (CFSG.LieType.Steinberg.SpinPlus.commutatorFormula hm O)) E π hπ hcen hc) hp hp2).2

open TableBOrth in
theorem ggNoInvariantLineTorus_omegaPlus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) :
    GGNoInvariantLineTorus p m (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
      (LargeEvenInnSet _) :=
  ggNoInvariantLineTorus_of_irredElt hp subset_rfl (center_omegaPlus_eq_bot hp hp2 hpq hm)
    (ggCenterCoprime_of_centerPrime (ggCenterPrime_omegaPlus hp hp2 hm))
    (ggTorusIrredElt_of_mulEquiv
      (projMkEquiv (scalars_subgroupOf_omegaPlus_eq_bot (by omega))).symm
      (NbrOrth.ggTorusIrredElt_omegaPlusGroup hp hp2 hpq hm))

open TableBOrth in
theorem ggNoInvariantLineTorus_omegaMinus {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGNoInvariantLineTorus p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _) :=
  ggNoInvariantLineTorus_of_irredElt hp subset_rfl (center_omegaMinus_eq_bot hp hp2 hpq hm hirr)
    (ggCenterCoprime_of_centerPrime (ggCenterPrime_omegaMinus hp hp2 hm hirr))
    (ggTorusIrredElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot b c)).symm
      (NbrOrth.ggTorusIrredElt_omegaMinusGroup hp hp2 hpq hm hirr))

end Center

end Omega

theorem recipeOmegaPlus_innerDiag {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 4 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    TableBSymp.ggTorusLift_omegaPlus hp hp2 hpq (by omega),
    ggInnerDiagBound_omegaPlus hp hp2 hpq (by omega)⟩

theorem recipeOmegaMinus_innerDiag {m n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hm : 3 ≤ m) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m,
    TableBSymp.ggTorusLift_omegaMinus hp hp2 hpq hm b c,
    ggInnerDiagBound_omegaMinus hp hp2 hpq hm hbc⟩

section CertsRecipe


theorem recipeOmegaPlus_noInvariantLine {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 4 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus l (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineTorus p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    TableBSymp.ggTorusLift_omegaPlus hp hp2 hpq (by omega),
    ggNoInvariantLineTorus_omegaPlus hp hp2 hpq (by omega)⟩

theorem recipeOmegaMinus_noInvariantLine {m n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hm : 3 ≤ m) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineTorus p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ, m,
    TableBSymp.ggTorusLift_omegaMinus hp hp2 hpq hm b c,
    ggNoInvariantLineTorus_omegaMinus hp hp2 hpq hm hbc⟩

end CertsRecipe

end CorFourTwoOpen

open CorFourTwoOpen

@[expose] def GGCorFourTwoOrthSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

theorem GGCorFourTwoOrthSplitLabel.pilot {p : ℕ} {lab : LargeEvenLabel}
    (h : GGCorFourTwoOrthSplitLabel p lab) : GGOutdiagPilotLabel lab := by
  rcases h.1 with h1 | h1
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, by have := h.2.1; omega⟩))))

theorem largeEvenLabelAll_innerDiag_orthSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGCorFourTwoOrthSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  dsimp only at htag hl hpn ⊢
  have hp2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
  intro Q hQ
  rcases htag with h | h <;> subst h <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_innerDiag hp hp2 hpn hl hQ
  · split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_innerDiag hp hp2 hpn (by omega) hQ

theorem largeEvenLabelAll_noInvariantLine_orthSplit
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGCorFourTwoOrthSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  dsimp only at htag hl hpn ⊢
  have hp2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
  intro Q hQ
  rcases htag with h | h <;> subst h <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · split_ifs at hQ ⊢ with h3
    · omega
    · exact recipeOmegaPlus_noInvariantLine hp hp2 hpn hl hQ
  · split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · exact recipeOmegaMinus_noInvariantLine hp hp2 hpn (by omega) hQ

theorem ggBstarInnerDiagLInputOn_orthSplit (T : ℕ → LargeEvenLabel → Prop) :
    GGBstarInnerDiagLInputOn fun p lab => T p lab ∧ GGCorFourTwoOrthSplitLabel p lab :=
  ggBstarInnerDiagLInputOn_of_labels (fun _ _ h => h.2.pilot) fun _ _ hp hlab h =>
    largeEvenLabelAll_innerDiag_orthSplit hp hlab h.2

theorem ggLNoInvariantLineInputOn_orthSplit :
    GGLNoInvariantLineInputOn GGCorFourTwoOrthSplitLabel :=
  ggLNoInvariantLineInputOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_noInvariantLine_orthSplit hp hlab h

end CFSG.StandardType

end
