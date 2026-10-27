module

public import CFSG.Quasithin.H13.L32AC42i
public import CFSG.Quasithin.H13.L32AC44g
public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Assembly.LowTwoRank Matrix CFSG.QuasithinUnique.Setup.X7a CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups Pointwise

theorem exists_fpf_normalizer {N : Type} [CommGroup N] [Finite N] {X : Subgroup (MulAut N)}
    {d a : ℕ} (hX : BinaryNaturalSL X ⊤ ⊥ d a) {S : Subgroup (MulAut N)} (hS : IsSylowTwoOf S X)
    (hmod : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ a →
      ∃ U : Subgroup SL(d, F), ∃ D : SL(d, F), IsPGroup 2 ↥U ∧ ¬ 2 ∣ U.index ∧
        D ∈ Subgroup.normalizer (U : Set SL(d, F)) ∧
        ∀ v : Fin d → F, (D : Matrix (Fin d) (Fin d) F) *ᵥ v = v → v = 0) :
    ∃ ν ∈ X, ν ∈ Subgroup.normalizer (S : Set (MulAut N)) ∧ ∀ y : N, ν y = y → y = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut N) := B42R.finite_mulAut
  obtain ⟨F, _, _, hF, π, hπ⟩ := hX
  obtain ⟨U, D, hU2, hUi, hDN, hDfix⟩ := hmod F hF
  obtain ⟨f, -, hfk, hfe⟩ := G64.RealizesVia.exists_secMap rfl hπ
  let θ : N → (Fin d → F) := fun x => @Multiplicative.toAdd (Fin d → F)
    (((f ⟨x, Subgroup.mem_top x⟩ : ↥(FFModel.nat (StatedSL d F)).sec) :
      (FFModel.nat (StatedSL d F)).Amb))
  have hθ1 : θ 1 = 0 := by
    show @Multiplicative.toAdd (Fin d → F) (((f 1 : ↥(FFModel.nat (StatedSL d F)).sec) :
      (FFModel.nat (StatedSL d F)).Amb)) = 0
    rw [map_one]
    rfl
  have hθinj : ∀ x y : N, θ x = θ y → x = y := by
    intro x y hxy
    have h1 : f ⟨x, Subgroup.mem_top x⟩ = f ⟨y, Subgroup.mem_top y⟩ :=
      Subtype.ext (Multiplicative.toAdd.injective hxy)
    have h2 : f (⟨x, Subgroup.mem_top x⟩ * ⟨y, Subgroup.mem_top y⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    have h3 := (hfk _).mp h2
    rw [Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.mp h3
  have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
  let Φ : SL(d, F) ≃* ↥X :=
    (specialLinearGroupEquivStatedSL d F).trans (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩)
  have hθΦ : ∀ (g : SL(d, F)) (x : N),
      θ (((Φ g : ↥X) : MulAut N) x) = (g : Matrix (Fin d) (Fin d) F) *ᵥ θ x :=
    fun g x => congrArg Multiplicative.toAdd (hfe _ ⟨x, Subgroup.mem_top x⟩ (Subgroup.mem_top _))
  set S' : Subgroup SL(d, F) := (S.subgroupOf X).comap Φ.toMonoidHom with hS'
  have hS'mem : ∀ γ, γ ∈ S' ↔ ((Φ γ : ↥X) : MulAut N) ∈ S := fun γ => Iff.rfl
  have hS'2 : IsPGroup 2 ↥S' := by
    have h1 : IsPGroup 2 ↥(S.subgroupOf X) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    exact h1.comap_of_injective Φ.toMonoidHom Φ.injective
  have hS'i : ¬ 2 ∣ S'.index := by
    rw [hS', Subgroup.index_comap_of_surjective _ Φ.surjective]
    exact hS.2.2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(d, F) (hU2.toSylow hUi) (hS'2.toSylow hS'i)
  have hgS : ∀ γ : SL(d, F), γ ∈ S' ↔ g⁻¹ * γ * g ∈ U := by
    intro γ
    have h1 : S' = MulAut.conj g • U := by
      have := congrArg (fun P : Sylow 2 SL(d, F) => (P : Subgroup SL(d, F))) hg
      simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
      exact this.symm
    rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
      MulAut.conj_apply, inv_inv]
  refine ⟨((Φ (g * D * g⁻¹) : ↥X) : MulAut N), (Φ _).2,
    Subgroup.mem_normalizer_fintype fun s hs => ?_, fun y hy => ?_⟩
  ·
    have hsX : s ∈ X := hS.1 hs
    have h1 : Φ.symm ⟨s, hsX⟩ ∈ S' := by
      rw [hS'mem, MulEquiv.apply_symm_apply]
      exact hs
    have h2 : g * D * g⁻¹ * Φ.symm ⟨s, hsX⟩ * (g * D * g⁻¹)⁻¹ ∈ S' := by
      rw [hgS] at h1 ⊢
      have e : g⁻¹ * (g * D * g⁻¹ * Φ.symm ⟨s, hsX⟩ * (g * D * g⁻¹)⁻¹) * g =
          D * (g⁻¹ * Φ.symm ⟨s, hsX⟩ * g) * D⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hDN _).mp h1
    rw [hS'mem, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    exact h2
  ·
    have key : ∀ (A B : SL(d, F)) (v : Fin d → F), (A : Matrix (Fin d) (Fin d) F) *ᵥ
        ((B : Matrix (Fin d) (Fin d) F) *ᵥ v) = ((A * B : SL(d, F)) : Matrix (Fin d) (Fin d) F) *ᵥ
          v := fun A B v => by rw [mulVec_mulVec]; rfl
    have h1 : ((g * D * g⁻¹ : SL(d, F)) : Matrix (Fin d) (Fin d) F) *ᵥ θ y = θ y := by
      rw [← hθΦ, hy]
    have h3 : ((g⁻¹ * (g * D * g⁻¹) : SL(d, F)) : Matrix (Fin d) (Fin d) F) *ᵥ θ y =
        ((g⁻¹ : SL(d, F)) : Matrix (Fin d) (Fin d) F) *ᵥ θ y := by rw [← key, h1]
    rw [show g⁻¹ * (g * D * g⁻¹) = D * g⁻¹ by group, ← key] at h3
    have h4 := hDfix _ h3
    have h5 : θ y = 0 := by
      have e : θ y = ((g * g⁻¹ : SL(d, F)) : Matrix (Fin d) (Fin d) F) *ᵥ θ y := by
        rw [mul_inv_cancel]
        exact (one_mulVec _).symm
      rw [e, ← key, h4, mulVec_zero]
    exact hθinj _ _ (h5.trans hθ1.symm)

theorem not_two_dvd_index_of_card {Γ : Type*} [Group Γ] [Finite Γ] {U : Subgroup Γ} {q r : ℕ}
    (hU : Nat.card U = q) (hG : Nat.card Γ = q * r) (hq : 0 < q) (hr : Odd r) :
    ¬ 2 ∣ U.index := by
  have h1 := U.card_mul_index
  rw [hU, hG] at h1
  rw [Nat.eq_of_mul_eq_mul_left hq h1]
  have := Nat.odd_iff.mp hr
  omega

theorem odd_pow_pow_sub_one {a : ℕ} (ha : 1 ≤ a) {j : ℕ} (hj : 1 ≤ j) : Odd ((2 ^ a) ^ j - 1) := by
  have h : Even ((2 ^ a) ^ j) := (Nat.even_pow' (by omega)).mpr ((Nat.even_pow' (by omega)).mpr
    even_two)
  have h1 : 1 ≤ (2 ^ a) ^ j := Nat.one_le_pow _ _ (by positivity)
  obtain ⟨m, hm⟩ := h
  exact ⟨m - 1, by omega⟩

theorem exists_fpf_normalizer_two {N : Type} [CommGroup N] [Finite N] {X : Subgroup (MulAut N)}
    {a : ℕ} (ha : 2 ≤ a) (hX : BinaryNaturalSL X ⊤ ⊥ 2 a) {S : Subgroup (MulAut N)}
    (hS : IsSylowTwoOf S X) :
    ∃ ν ∈ X, ν ∈ Subgroup.normalizer (S : Set (MulAut N)) ∧ ∀ y : N, ν y = y → y = 1 := by
  refine exists_fpf_normalizer hX hS fun F _ _ hF => ?_
  have : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have h4 : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one h4
  refine ⟨CFSG.Timmesfeld.upperUnipotent F,
    CFSG.Timmesfeld.ARS.NaturalModule.diagElt (Units.mk0 c hc0), ?_, ?_,
    CFSG.Timmesfeld.ARS.NaturalModule.diagElt_mem_normalizer_upperUnipotent _, fun v hv => ?_⟩
  · exact IsPGroup.of_card (n := a) (by rw [CFSG.Timmesfeld.RankOne.card_upperUnipotent, hF])
  · refine not_two_dvd_index_of_card (r := (2 ^ a) ^ 2 - 1)
      (CFSG.Timmesfeld.RankOne.card_upperUnipotent F) ?_ Nat.card_pos
      (odd_pow_pow_sub_one (by omega) (by norm_num))
    rw [LinearFlag.card_SL_eq (n := 2) (by norm_num), hF]
    simp
  · have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    simp [CFSG.Timmesfeld.ARS.NaturalModule.diagElt, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at h0 h1
    have hc1' : (c⁻¹ : F) ≠ 1 := fun h => hc1 (by rw [← inv_inv c, h, inv_one])
    funext i
    fin_cases i
    · have : (c - 1) * v 0 = 0 := by rw [sub_mul, one_mul, h0, sub_self]
      simpa [sub_eq_zero, hc1] using this
    · have : (c⁻¹ - 1) * v 1 = 0 := by rw [sub_mul, one_mul, h1, sub_self]
      simpa [sub_eq_zero, hc1'] using this

theorem exists_fpf_normalizer_three {N : Type} [CommGroup N] [Finite N]
    {X : Subgroup (MulAut N)} {a : ℕ} (ha : 2 ≤ a) (hX : BinaryNaturalSL X ⊤ ⊥ 3 a)
    {S : Subgroup (MulAut N)} (hS : IsSylowTwoOf S X) :
    ∃ ν ∈ X, ν ∈ Subgroup.normalizer (S : Set (MulAut N)) ∧ ∀ y : N, ν y = y → y = 1 := by
  refine exists_fpf_normalizer hX hS fun F _ _ hF => ?_
  have : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hF
  have h4 : 2 < Nat.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one h4
  set u := Units.mk0 c hc0 with hu
  refine ⟨upperUni F, SL3N.diagSL u u, ?_, ?_, SL3N.diagSL_mem_borel u u, fun v hv => ?_⟩
  · exact IsPGroup.of_card (n := a * 3) (by rw [card_upperUni, hF, pow_mul])
  · refine not_two_dvd_index_of_card (r := ((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 - 1))
      card_upperUni ?_ (by positivity)
      ((odd_pow_pow_sub_one (by omega) (by norm_num)).mul
        (odd_pow_pow_sub_one (by omega) (by norm_num)))
    rw [LinearFlag.card_SL_eq (n := 3) (by norm_num), hF]
    simp [Finset.prod_Icc_succ_top]
  · have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    simp [SL3N.diagSL, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hu] at h0 h1 h2
    have hcc : c⁻¹ * c⁻¹ ≠ 1 := by
      intro h
      apply hc1
      have h' : c * c = 1 := by rw [← mul_inv, inv_eq_one] at h; exact h
      have : (c - 1) * (c - 1) = 0 := by
        have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
        linear_combination h' - (c - 1) * h2'
      exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
    funext i
    fin_cases i
    · have : (c - 1) * v 0 = 0 := by rw [sub_mul, one_mul, h0, sub_self]
      simpa [sub_eq_zero, hc1] using this
    · have : (c⁻¹ * c⁻¹ - 1) * v 1 = 0 := by rw [sub_mul, one_mul, h1, sub_self]
      simpa [sub_eq_zero, hcc] using this
    · have : (c - 1) * v 2 = 0 := by rw [sub_mul, one_mul, h2, sub_self]
      simpa [sub_eq_zero, hc1] using this

end CFSG.Quasithin.H13.L32A.C
