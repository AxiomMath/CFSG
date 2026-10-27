module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixNF
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutKb

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.D4q.Struct CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  {S2 : Subgroup (K ≃+* K)} {T S0 : Subgroup (MulAut (Cm σ))}
  (hT : ∀ α : MulAut (Cm σ), α ∈ T ↔ ∃ u ∈ Ust σ, ∃ δ' ∈ S2, α = MulAut.conj u *
    fieldActor σ δ')
  (hS : ∀ α : MulAut (Cm σ), α ∈ S0 ↔ ∃ u ∈ Ust σ, MulAut.conj u = α)

include hT in
theorem T_le_autStab (P : Subgroup (Cm σ)) (hUP : Ust σ ≤ P)
    (hPstab : ∀ δ' : K ≃+* K, (fieldActor σ δ' : MulAut (Cm σ)) ∈ autStab P) : T ≤ autStab P := by
  intro α hα
  obtain ⟨u, hu, δ', -, rfl⟩ := (hT α).1 hα
  exact (autStab P).mul_mem ((conj_mem_autStab_iff P u).2 (Subgroup.le_normalizer (hUP hu)))
    (hPstab δ')

include hT hS in
theorem S_le_T : S0 ≤ T := by
  intro α hα
  obtain ⟨u, hu, rfl⟩ := (hS α).1 hα
  exact (hT _).2 ⟨u, hu, 1, S2.one_mem, by rw [fieldActor_one, mul_one]⟩

include hT hS in
theorem T_le_normalizer : T ≤ Subgroup.normalizer (S0 : Set (MulAut (Cm σ))) := by
  have key : ∀ α ∈ T, ∀ s ∈ S0, α * s * α⁻¹ ∈ S0 := by
    intro α hα s hs
    obtain ⟨u, hu, δ', -, rfl⟩ := (hT α).1 hα
    obtain ⟨x, hx, rfl⟩ := (hS s).1 hs
    refine (hS _).2 ⟨u * fieldActor σ δ' x * u⁻¹, ?_, ?_⟩
    · exact (Ust σ).mul_mem ((Ust σ).mul_mem hu (fieldActor_mem_Ust σ δ' hx)) ((Ust σ).inv_mem hu)
    · have h := mulAut_mul_conj σ (fieldActor σ δ') x
      have h2 : (fieldActor σ δ' : MulAut (Cm σ)) * MulAut.conj x * (fieldActor σ δ')⁻¹ =
          MulAut.conj (fieldActor σ δ' x) := by
        rw [h, mul_assoc, mul_inv_cancel, mul_one]
      calc MulAut.conj (u * fieldActor σ δ' x * u⁻¹) =
          MulAut.conj u * MulAut.conj (fieldActor σ δ' x) * (MulAut.conj u)⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = _ := by rw [← h2]; group
  intro α hα
  exact mem_normalizer_of_conj_mem (S := S0) (key α hα) (by
    intro s hs
    have := key α⁻¹ (T.inv_mem hα) s hs
    simpa using this)

include hT in
theorem fieldActor_mem_T {δ : K ≃+* K} (hδ : δ ∈ S2) : (fieldActor σ δ : MulAut (Cm σ)) ∈ T :=
  (hT _).2 ⟨1, (Ust σ).one_mem, δ, hδ, by rw [map_one, one_mul]⟩

include hf hK hσ hS in
theorem fieldActor_not_mem_S {δ : K ≃+* K} (hδ : δ ≠ 1) :
    (fieldActor σ δ : MulAut (Cm σ)) ∉ S0 := by
  intro h
  obtain ⟨u, -, hu⟩ := (hS _).1 h
  have h1 : theta σ hf hK hσ (MulAut.conj u) = 1 := by
    have := theta_conj_fieldActor σ hf hK hσ u 1
    rwa [fieldActor_one, mul_one] at this
  have h2 : theta σ hf hK hσ (fieldActor σ δ) = δ := by
    have := theta_conj_fieldActor σ hf hK hσ 1 δ
    rwa [map_one, one_mul] at this
  rw [← hu] at h2
  exact hδ (h2.symm.trans h1)

theorem fieldActor_sq {δ : K ≃+* K} (hδ : δ ^ 2 = 1) :
    (fieldActor σ δ : MulAut (Cm σ)) ^ 2 = 1 := by
  rw [pow_two, ← fieldActor_mul, ← pow_two, hδ, fieldActor_one]

include hT hS in
theorem exists_cyc (hcyc : ∃ δ₁ ∈ S2, ∀ δ' ∈ S2, δ' ∈ Subgroup.zpowers δ₁) :
    ∃ t₀ ∈ T, T = S0 ⊔ Subgroup.zpowers t₀ := by
  obtain ⟨δ₁, hδ₁, hgen⟩ := hcyc
  refine ⟨fieldActor σ δ₁, fieldActor_mem_T σ hT hδ₁, le_antisymm ?_ (sup_le (S_le_T σ hT hS) ?_)⟩
  · intro α hα
    obtain ⟨u, hu, δ', hδ', rfl⟩ := (hT α).1 hα
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hgen δ' hδ')
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ((hS _).2 ⟨u, hu, rfl⟩))
      (Subgroup.mem_sup_right ?_)
    exact ⟨k, (map_zpow (fieldActorHom (t := TwistTag.D4) σ) δ₁ k).symm⟩
  · exact Subgroup.zpowers_le.2 (fieldActor_mem_T σ hT hδ₁)

theorem exists_generator_of_le_aut {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (S : Subgroup (K ≃+* K)) : ∃ δ₁ ∈ S, ∀ δ' ∈ S, δ' ∈ Subgroup.zpowers δ₁ := by
  obtain ⟨φ, -, -, htop, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, htop⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥S)
  refine ⟨g, g.2, fun δ' hδ' => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨δ', hδ'⟩)
  exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩

end CFSG.Quasithin.H13.F431.D4q.Out
