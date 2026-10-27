module

public import CFSG.RankThree.Chevalley.SteinbergCFOddInnerFieldLocalCore
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality
  finite_field_prime_power_characteristic)

theorem eq_one_of_entrywiseAdjointAut_eq_conj {τ : Tag} {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K ℓ] {σ : K ≃+* K} {h : adjointGroup τ K}
    (hσh : entrywiseAdjointAut τ σ = MulAut.conj h) : h = 1 ∧ σ = 1 := by
  classical
  set ι : ZMod ℓ →+* K := ZMod.castHom (dvd_refl ℓ) K
  have hodd : Odd (Nat.card (ZMod ℓ)) := by
    rw [Nat.card_zmod]
    exact (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2
  have hfaith := (exceptional_Lang_finite_root_centralizer_faithfulness τ (ZMod ℓ) hodd K ι).2.2.1
  have hh1 : h = 1 := by
    refine Subtype.ext (hfaith h h.2 fun y hy => ?_)
    obtain ⟨g0, hg0, rfl⟩ := hy
    have hyC : baseChangeGL ι g0 ∈ adjointGroup τ K := baseChangeGL_mem_adjointGroup ι hg0
    have h1 := congrArg (fun β : MulAut (adjointGroup τ K) =>
      ((β ⟨_, hyC⟩ : adjointGroup τ K) : ModGL τ K)) hσh
    change Units.map (entrywiseHom σ.toRingHom) (baseChangeGL ι g0) =
      (h : ModGL τ K) * baseChangeGL ι g0 * (h : ModGL τ K)⁻¹ at h1
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      RingHom.ext_zmod (σ.toRingHom.comp ι) ι] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1.symm
  refine ⟨hh1, ?_⟩
  rw [hh1, map_one] at hσh
  exact (injective_iff_map_eq_one _).1 (SteinbergBT.entrywiseAdjointAutHom_injective τ.rank_pos) σ
    hσh

theorem odd_E8_inner_field_automorphisms_and_noninner_prime_core {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) :
    (∀ η : MulAut (adjointGroup .E8 K), ∃! gσ : adjointGroup .E8 K × (K ≃+* K),
      η = MulAut.conj gσ.1 * entrywiseAdjointAut .E8 gσ.2) ∧
    (∃ Θ : MulAut (adjointGroup .E8 K) →* (K ≃+* K),
      (∀ (g : adjointGroup .E8 K) (σ : K ≃+* K),
        Θ (MulAut.conj g * entrywiseAdjointAut .E8 σ) = σ) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range) ∧
    Nonempty (Outer (adjointGroup .E8 K) ≃* (K ≃+* K)) ∧
    Nat.card (Outer (adjointGroup .E8 K)) = f ∧ IsCyclic (K ≃+* K) ∧ Nat.card (K ≃+* K) = f ∧
    ∀ {p : ℕ}, p.Prime → ∀ B : Subgroup (MulAut (adjointGroup .E8 K)),
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B →
      ∀ α : B, (α : MulAut (adjointGroup .E8 K)) ∉
          (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range →
        orderOf α = p →
        aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)) :=
    mulAut_conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  obtain ⟨φ, -, -, hφgen, hcardAut, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφgen⟩
  set π : (K ≃+* K) →* Outer (adjointGroup .E8 K) :=
    (QuotientGroup.mk' (inner (adjointGroup .E8 K))).comp entrywiseAdjointAutHom with hπ
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨h, hh⟩ := (QuotientGroup.eq_one_iff _).1 hσ
    exact (eq_one_of_entrywiseAdjointAut_eq_conj hℓ2 hh.symm).2
  have hOut : Nat.card (Outer (adjointGroup .E8 K)) ∣ f := by
    have h := (ordinary_E_outer_order_Cartan_divisor .E8 (Or.inr (Or.inr rfl)) hℓ hf K hK 1 1
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))).1
    rwa [one_mul, one_mul] at h
  have : Finite (Outer (adjointGroup .E8 K)) := Nat.finite_of_card_ne_zero fun h => by
    rw [h, zero_dvd_iff] at hOut
    omega
  have hπbij : Function.Bijective π :=
    hπinj.bijective_of_nat_card_le (by rw [hcardAut]; exact Nat.le_of_dvd (by omega) hOut)
  set e : (K ≃+* K) ≃* Outer (adjointGroup .E8 K) := MulEquiv.ofBijective π hπbij with he
  set Θ : MulAut (adjointGroup .E8 K) →* (K ≃+* K) :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' (inner (adjointGroup .E8 K))) with hΘ
  have hmk : ∀ (g : adjointGroup .E8 K) (σ : K ≃+* K),
      QuotientGroup.mk' (inner (adjointGroup .E8 K)) (MulAut.conj g * entrywiseAdjointAut .E8 σ) =
        e σ := by
    intro g σ
    have hc : MulAut.conj g ∈ inner (adjointGroup .E8 K) :=
      show MulAut.conj g ∈ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range
        from ⟨g, rfl⟩
    rw [map_mul, show QuotientGroup.mk' (inner (adjointGroup .E8 K)) (MulAut.conj g) = 1 from
      (QuotientGroup.eq_one_iff _).2 hc, one_mul]
    rfl
  have hΘapp : ∀ (g : adjointGroup .E8 K) (σ : K ≃+* K),
      Θ (MulAut.conj g * entrywiseAdjointAut .E8 σ) = σ := by
    intro g σ
    change e.symm (QuotientGroup.mk' _ _) = σ
    rw [hmk, MulEquiv.symm_apply_apply]
  have hexists : ∀ η : MulAut (adjointGroup .E8 K), ∃ g : adjointGroup .E8 K,
      η = MulAut.conj g * entrywiseAdjointAut .E8 (Θ η) := by
    intro η
    have h1 : (QuotientGroup.mk' (inner (adjointGroup .E8 K)) η : Outer (adjointGroup .E8 K)) =
        QuotientGroup.mk' (inner (adjointGroup .E8 K)) (entrywiseAdjointAut .E8 (Θ η)) := by
      change _ = π (Θ η)
      change _ = e (e.symm _)
      rw [MulEquiv.apply_symm_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem] at h1
    obtain ⟨g, hg⟩ := h1
    exact ⟨g, by rw [hg, div_mul_cancel]⟩
  have hNF : ∀ η : MulAut (adjointGroup .E8 K), ∃! gσ : adjointGroup .E8 K × (K ≃+* K),
      η = MulAut.conj gσ.1 * entrywiseAdjointAut .E8 gσ.2 := by
    intro η
    obtain ⟨g, hg⟩ := hexists η
    refine ⟨(g, Θ η), hg, fun ⟨g', σ'⟩ h' => ?_⟩
    simp only at h'
    have hσ' : σ' = Θ η := by rw [h', hΘapp]
    subst hσ'
    rw [h', hΘapp] at hg
    exact Prod.ext (hinj (mul_right_cancel hg)) rfl
  refine ⟨hNF, ⟨Θ, hΘapp, e.symm.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩, ⟨e.symm⟩,
    ?_, hcyc, hcardAut, fun {p} hp B hB α hα hαp => ?_⟩
  · ext η
    rw [MonoidHom.mem_ker]
    change e.symm (QuotientGroup.mk' _ η) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  · rw [← Nat.card_congr e.toEquiv, hcardAut]
  · obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
    exact (odd_Chevalley_inner_field_noninner_prime_local_core_trivial .E8 hℓ hℓ2 hf K hK hNF hp
      B hB α hα hαp x σ hxσ).2.2.2

end CFSG.RankThree.Chevalley
