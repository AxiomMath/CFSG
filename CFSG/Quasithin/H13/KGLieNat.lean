module

public import CFSG.Quasithin.H13.KGLieGeneric
public import CFSG.Quasithin.H13.A5LieRows

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

@[expose] noncomputable def scal {ι K : Type} [Field K] (c : Kˣ) :
    Multiplicative (ι → K) ≃* Multiplicative (ι → K) :=
  (DistribMulAction.toAddEquiv (ι → K) c).toMultiplicative

theorem toAdd_scal {ι K : Type} [Field K] (c : Kˣ) (x : Multiplicative (ι → K)) :
    Multiplicative.toAdd (scal c x) = (c : K) • Multiplicative.toAdd x := rfl

theorem scalars_of_nat {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {L : Subgroup (MulAut V)} {π : ↥Γ →* ↥L}
    (h : (FFModel.nat Γ).RealizesVia L ⊤ ⊥ π) :
    ∃ m : Kˣ → MulAut V, (∀ c, ∀ l ∈ L, m c * l = l * m c) ∧
      (∀ u : V, u ≠ 1 → Function.Injective fun c => m c u) ∧
      Nat.card V = Nat.card K ^ Fintype.card ι := by
  obtain ⟨f, hfs, hfk, hfe⟩ := G64.RealizesVia.exists_secMap rfl h
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).1 hu
    exact Subtype.ext this
  set e₀ := MulEquiv.ofBijective f ⟨hfi, hfs⟩ with he₀
  set e : V ≃* Multiplicative (ι → K) :=
    (Subgroup.topEquiv (G := V)).symm.trans (e₀.trans Subgroup.topEquiv) with he
  have heapp : ∀ w : V, e w = ((f ⟨w, mem_top w⟩ : ↥(FFModel.nat Γ).sec) :
      (FFModel.nat Γ).Amb) := fun w => rfl
  have hint : ∀ (γ : (FFModel.nat Γ).Gam) (w : V), e (((π γ : ↥L) : MulAut V) w) =
      natAct Γ γ (e w) := by
    intro γ w
    rw [heapp, heapp]
    exact hfe γ ⟨w, mem_top w⟩ (mem_top _)
  refine ⟨fun c => e.trans ((scal c).trans e.symm), ?_, ?_, ?_⟩
  · intro c l hl
    obtain ⟨γ, hγ⟩ := h.1 ⟨l, hl⟩
    have hl' : l = ((π γ : ↥L) : MulAut V) := (congrArg Subtype.val hγ).symm
    rw [hl']
    ext w
    apply e.injective
    simp only [MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [hint, hint, MulEquiv.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_scal, natAct, toAdd_ofAdd]
    rw [Matrix.mulVec_smul]
  · intro u hu c c' hcc
    have h1 : scal c (e u) = scal c' (e u) := by
      have := congrArg e hcc
      simpa using this
    have h2 : (c : K) • Multiplicative.toAdd (e u) = (c' : K) • Multiplicative.toAdd (e u) := by
      rw [← toAdd_scal, ← toAdd_scal, h1]
    have hne : Multiplicative.toAdd (e u) ≠ 0 := by
      intro h0
      apply hu
      apply e.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h0]; rfl)
    exact Units.ext (smul_left_injective K hne h2)
  · rw [Nat.card_congr e.toEquiv]
    show Nat.card (ι → K) = _
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

theorem false_of_nat [Finite V] (hV2 : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)}
    {v : MulAut V} (hB4 : B4Hyp G L) (hc : A5.Cond1321 G L v) {ι : Type} [Fintype ι]
    [DecidableEq ι] (hι : 2 ≤ Fintype.card ι) {K : Type} [Field K] [Finite K]
    (hK : 8 ≤ Nat.card K) {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (h : (FFModel.nat Γ).Realizes L ⊤ ⊥) : False := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨m, hmL, hinj, hcard⟩ := scalars_of_nat hπ
  refine false_of_cond_scalars hV2 hB4 hc (ι := Kˣ) ?_ m hmL hinj ?_
  · rw [Nat.card_units]
    omega
  · rw [hcard]
    calc 16 < 8 ^ 2 := by norm_num
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hK 2
      _ ≤ Nat.card K ^ Fintype.card ι := Nat.pow_le_pow_right (by omega) hι

theorem eight_le_two_pow {n : ℕ} (hn : 3 ≤ n) : 8 ≤ 2 ^ n :=
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem factLieSL2Row1321_holds : A5.FactLieSL2Row1321 := by
  intro V _ _ hV2 G L v hB4 hc n hn h
  obtain ⟨K, _, _, hK, hr⟩ := h
  exact false_of_nat hV2 hB4 hc (ι := Fin 2) (by simp) (hK ▸ eight_le_two_pow hn) hr

theorem factLieSL3Row1321_holds : A5.FactLieSL3Row1321 := by
  intro V _ _ hV2 G L v hB4 hc n hn h
  obtain ⟨K, _, _, hK, hr⟩ := h
  exact false_of_nat hV2 hB4 hc (ι := Fin 3) (by simp) (hK ▸ eight_le_two_pow hn) hr

theorem factLieSp4Row1321_holds : A5.FactLieSp4Row1321 := by
  intro V _ _ hV2 G L v hB4 hc n hn h
  obtain ⟨K, _, _, hK, hr⟩ := h
  exact false_of_nat hV2 hB4 hc (ι := Fin 2 ⊕ Fin 2) (by simp) (hK ▸ eight_le_two_pow hn) hr

end CFSG.Quasithin.H13.KGLie
