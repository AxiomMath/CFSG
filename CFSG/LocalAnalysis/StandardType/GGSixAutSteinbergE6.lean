module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergE6Good
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace AutSt

theorem normal_range_conj {S : Type*} [Group S] :
    (MulAut.conj : S →* MulAut S).range.Normal :=
  ⟨fun _ ⟨g, hg⟩ σ => ⟨σ g, by rw [← hg, mulAut_mul_conj_mul_inv]⟩⟩

theorem units_map_entrywiseHom_one {τ : Tag} {K : Type} [Field K] (g : ModGL τ K) :
    Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) g = g :=
  Units.ext (entrywise_id _)

section Model


variable {K : Type} [Field K]

theorem exactNormalAut_one_mul {τ : Tag} (σ σ' : K ≃+* K) (ε ε' : ℕ) :
    exactNormalAut τ K 1 σ ε * exactNormalAut τ K 1 σ' ε' =
      exactNormalAut τ K 1 (σ * σ') (ε + ε') := by
  rw [exactNormalAut_mul]
  congr 1
  funext j
  simp

@[expose] def e6FieldGraph (K : Type) [Field K] : Subgroup (MulAut (adjointGroup .E6 K)) where
  carrier := {α | ∃ (σ : K ≃+* K) (ε : ℕ), ε < 2 ∧ α = exactNormalAut .E6 K 1 σ ε}
  mul_mem' := by
    rintro _ _ ⟨σ, ε, -, rfl⟩ ⟨σ', ε', -, rfl⟩
    refine ⟨σ * σ', (ε + ε') % 2, Nat.mod_lt _ two_pos, ?_⟩
    rw [exactNormalAut_one_mul]
    exact (exactNormalAut_mod (τ := .E6) 1 (σ * σ') (ε + ε')).symm
  one_mem' := ⟨1, 0, two_pos, exactNormalAut_one_one_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨σ, ε, hε, rfl⟩
    refine ⟨σ⁻¹, ε, hε, ?_⟩
    rw [inv_eq_iff_mul_eq_one, exactNormalAut_one_mul, mul_inv_cancel,
      ← exactNormalAut_mod (τ := .E6),
      show (ε + ε) % exactE .E6 = 0 by change (ε + ε) % 2 = 0; omega]
    exact exactNormalAut_one_one_zero

theorem mem_e6FieldGraph {α : MulAut (adjointGroup .E6 K)} :
    α ∈ e6FieldGraph K ↔ ∃ (σ : K ≃+* K) (ε : ℕ), ε < 2 ∧ α = exactNormalAut .E6 K 1 σ ε :=
  Iff.rfl

@[expose] noncomputable def e6DiagHom (K : Type) [Field K] :
    (Fin Tag.E6.rank → Kˣ) →* MulAut (adjointGroup .E6 K) where
  toFun a := exactNormalAut .E6 K a 1 0
  map_one' := exactNormalAut_one_one_zero
  map_mul' a b := (exactNormalAut_diag_mul a b 1 0).symm

theorem odd_card_range_e6DiagHom [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    Odd (Nat.card (e6DiagHom K).range) := by
  refine Odd.of_dvd_nat ?_ (Subgroup.card_range_dvd (e6DiagHom K))
  rw [Nat.card_fun, Nat.card_units, hK]
  exact Odd.pow (Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' (by omega)).2 even_two)
    odd_one)

theorem odd_relIndex_inn_ker_E6 [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    {I : Subgroup (MulAut (adjointGroup .E6 K))}
    (hI : I = (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
      (e6DiagHom K).range) :
    Odd ((MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range.relIndex I) := by
  subst hI
  have := normal_range_conj (S := adjointGroup .E6 K)
  rw [Subgroup.relIndex_sup_left]
  exact Odd.of_dvd_nat (odd_card_range_e6DiagHom hf hK) (Subgroup.relIndex_dvd_card _ _)

theorem exists_conj_of_mem_ker [Finite K] [CharP K 2] {α : MulAut (adjointGroup .E6 K)}
    {g : adjointGroup .E6 K} {a : Fin Tag.E6.rank → Kˣ}
    (hα : ∀ h : adjointGroup .E6 K, (α h : ModGL .E6 K) = (g : ModGL .E6 K) *
      rootDiagUnit .E6 a * (h : ModGL .E6 K) * (rootDiagUnit .E6 a)⁻¹ * (g : ModGL .E6 K)⁻¹)
    (w : adjointGroup .E6 K) :
    ∃ k : adjointGroup .E6 K,
      α (w * xPar (rootOperatorFamily .E6) (Pi.single (e6Node 1) 1) (1 : K) * w⁻¹) =
        k * (w * xPar (rootOperatorFamily .E6) (Pi.single (e6Node 1) 1) (1 : K) * w⁻¹) * k⁻¹ := by
  have hαN : α = MulAut.conj g * exactNormalAut .E6 K a 1 0 :=
    eq_conj_mul_exactNormalAut_of_apply (σ := 1) (ε := 0) fun h => by
      rw [hα h, exactQ_zero, units_map_entrywiseHom_one, inv_one, mul_one, mul_one]
  have h1 : α (xPar (rootOperatorFamily .E6) (Pi.single (e6Node 1) 1) (1 : K)) =
      g * xPar (rootOperatorFamily .E6) (Pi.single (e6Node 1) 1) (a (e6Node 1) : K) * g⁻¹ := by
    rw [hαN, MulAut.mul_apply, MulAut.conj_apply,
      xPar_single_eq_adjX (F := rootOperatorFamily .E6) (e6Node 1) (1 : K),
      exactNormalAut_diag_adjX_one,
      ← xPar_single_eq_adjX (F := rootOperatorFamily .E6) (e6Node 1) (a (e6Node 1) : K)]
  obtain ⟨t, ht⟩ := exists_conj_xPar_single_eq_one (F := rootOperatorFamily .E6) (e6Node 1)
    (Units.ne_zero (a (e6Node 1)))
  refine ⟨α w * g * t⁻¹ * w⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, h1, ← ht]
  group

end Model

section Isogeny


variable {K : Type} [Field K]

theorem exists_conj_of_modelRoot [Finite K] [CharP K 2] {r : adjointGroup .E6 K}
    (hr : GGModelRoot (e6Datum K) .E6 (e6Isogeny K) r) :
    ∃ w : adjointGroup .E6 K,
      r = w * xPar (rootOperatorFamily .E6) (Pi.single (e6Node 1) 1) (1 : K) * w⁻¹ := by
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, z, hz, rfl⟩ := hr
  have hγ' : IsRoot .E6 γ := (e6Data_valid.mem_minDatum_roots isFiniteType_cartan_E6 K).mp hγ
  obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup K).1 hz
  rw [map_mul, map_mul, map_inv, e6Isogeny_xm K hγ'] at hr2 ⊢
  have hz' : yPar (rootOperatorFamily .E6) e6AdjData_valid γ c ∈
      rootGroup (rootOperatorFamily .E6) K γ := xPar_mem hγ' _
  have hz1 : yPar (rootOperatorFamily .E6) e6AdjData_valid γ c ≠ 1 := by
    intro h
    rw [h, mul_one, mul_inv_cancel, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  obtain ⟨g, hg⟩ := exists_conj_one_E6 hγ' hz' hz1
  refine ⟨e6Isogeny K u * g⁻¹, ?_⟩
  rw [← hg]
  group

theorem autModel_E6 [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    GGAutModel (adjointGroup .E6 K) (GGModelRoot (e6Datum K) .E6 (e6Isogeny K)) := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨Θ, -, hΘ, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  have hΘN : ∀ (σ : K ≃+* K) (ε : ℕ) (hε : ε < 2), Θ (exactNormalAut .E6 K 1 σ ε) =
      (σ, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE .E6))) :=
    fun σ ε hε => hΘ _ 1 1 σ ⟨ε, hε⟩ fun h => by
      rw [coe_exactNormalAut, OneMemClass.coe_one, one_mul, inv_one, mul_one]
  have hInn : (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ≤
      Θ.ker := by
    rintro _ ⟨g, rfl⟩
    refine (hker _).2 ⟨g, 1, fun h => ?_⟩
    rw [rootDiagUnit_one, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      mul_one, inv_one, mul_one]
  have hD : (e6DiagHom K).range ≤ Θ.ker := by
    rintro _ ⟨a, rfl⟩
    refine (hker _).2 ⟨1, a, fun h => ?_⟩
    change (exactNormalAut .E6 K a 1 0 h : ModGL .E6 K) = _
    simp only [coe_exactNormalAut, exactQ_zero, units_map_entrywiseHom_one, OneMemClass.coe_one,
      mul_one, inv_one, one_mul]
  have hkerle : Θ.ker ≤
      (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range ⊔
        (e6DiagHom K).range := by
    intro α hα
    obtain ⟨g, a, hga⟩ := (hker α).1 hα
    have e : α = MulAut.conj g * exactNormalAut .E6 K a 1 0 :=
      eq_conj_mul_exactNormalAut_of_apply (σ := 1) (ε := 0) fun h => by
        rw [hga h, exactQ_zero, units_map_entrywiseHom_one, inv_one, mul_one, mul_one]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right ⟨a, rfl⟩)
  refine autModel_of_hom Θ (e6FieldGraph K) hInn
    (odd_relIndex_inn_ker_E6 hf hK (le_antisymm hkerle (sup_le hInn hD))) (fun α => ?_) ?_ ?_
  · obtain ⟨g, a, σ, ε, hα⟩ := hnf α
    exact ⟨exactNormalAut .E6 K 1 σ ε, ⟨σ, ε, ε.isLt, rfl⟩,
      by rw [hΘN σ ε ε.isLt, hΘ α g a σ ε hα]⟩
  · rintro _ ⟨σ, ε, hε, rfl⟩ h1
    rw [hΘN σ ε hε, Prod.mk_eq_one, ofAdd_eq_one, ZMod.natCast_eq_zero_iff] at h1
    obtain ⟨rfl, h2⟩ := h1
    obtain rfl : ε = 0 := by
      change 2 ∣ ε at h2
      omega
    exact exactNormalAut_one_one_zero
  · rintro r hr _ ⟨σ, ε, hε, rfl⟩ hc2 hc1 e he
    have hσ2 : σ ^ 2 = 1 := by
      have h := congrArg Θ hc2
      rw [map_pow, hΘN σ ε hε, map_one, Prod.pow_mk, Prod.mk_eq_one] at h
      exact h.1
    have hne : ¬(σ = 1 ∧ ε = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hc1 exactNormalAut_one_one_zero
    obtain ⟨w, rfl⟩ := exists_conj_of_modelRoot hr
    obtain ⟨g, a, hga⟩ := (hker e).1 he
    exact ((goodAut_e6One hf hK hε hσ2 hne).of_conj w).conj e (exists_conj_of_mem_ker hga w)

end Isogeny

end AutSt

section Family


theorem ggAutModelAt_E6 : GGAutModelAt .E6 := by
  intro n f hadm _ _
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact ⟨adjointGroup .E6 (GaloisField 2 f), inferInstance, e6Isogeny (GaloisField 2 f),
    e6Isogeny_surjective _, CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center,
    AutSt.autModel_E6 hf hK⟩

theorem ggAutStructureAt_E6 : GGAutStructureAt .E6 :=
  ggAutStructureAt_of_autModelAt ggAutModelAt_E6

end Family

end CFSG.StandardType
