module

public import CFSG.Walter.PSL2Facts.EvenAutFixedPoints

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter CFSG.ASVolI CFSG.SeitzReduction.LinearPilot
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {a : ℕ}

noncomputable def psl2DiagFixedHom (Φ : Subgroup (K ≃+* K)) :
    (FixedPoints.subfield Φ K)ˣ →* PSL2 K :=
  ((psl2QuotientMap K).comp (burnsideAut_sl2DiagHom K)).comp
    (Units.map (FixedPoints.subfield Φ K).subtype.toMonoidHom)

noncomputable def psl2DiagFixed (Φ : Subgroup (K ≃+* K)) : Subgroup (PSL2 K) :=
  (⊤ : Subgroup (FixedPoints.subfield Φ K)ˣ).map (psl2DiagFixedHom Φ)

theorem psl2DiagFixedHom_injective [CharP K 2] (Φ : Subgroup (K ≃+* K)) :
    Function.Injective (psl2DiagFixedHom Φ) :=
  (psl2QuotientMap_injective_of_charTwo (K := K)).comp <|
    (burnsideAut_sl2DiagHom_injective K).comp <|
      Units.map_injective (f := (FixedPoints.subfield Φ K).subtype.toMonoidHom)
        (fun _ _ h => Subtype.ext h)

theorem card_psl2DiagFixed [CharP K 2] (Φ : Subgroup (K ≃+* K)) :
    Nat.card (psl2DiagFixed Φ) = Nat.card (FixedPoints.subfield Φ K)ˣ := by
  rw [psl2DiagFixed, Subgroup.card_map_of_injective (psl2DiagFixedHom_injective Φ),
    Subgroup.card_top]

theorem card_psl2DiagFixed_eq_two_pow (hK : Nat.card K = 2 ^ a)
    (Φ : Subgroup (K ≃+* K)) :
    Nat.card (psl2DiagFixed Φ) = 2 ^ (a / Nat.card Φ) - 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  rw [card_psl2DiagFixed Φ, Nat.card_units,
    CFSG.Semidihedral.FixedFieldData.fixedSubfield_card 2 a K hK Φ]

theorem isCyclic_psl2DiagFixed [CharP K 2] (Φ : Subgroup (K ≃+* K)) :
    IsCyclic (psl2DiagFixed Φ) := by
  haveI : IsCyclic (FixedPoints.subfield Φ K)ˣ := inferInstance
  haveI : IsCyclic (⊤ : Subgroup (FixedPoints.subfield Φ K)ˣ) := Subgroup.isCyclic ⊤
  exact (Subgroup.equivMapOfInjective (⊤ : Subgroup (FixedPoints.subfield Φ K)ˣ)
    (psl2DiagFixedHom Φ) (psl2DiagFixedHom_injective Φ)).isCyclic.mp inferInstance

theorem mem_psl2DiagFixed_iff (Φ : Subgroup (K ≃+* K)) {x : PSL2 K} :
    x ∈ psl2DiagFixed Φ ↔
      ∃ μ : (FixedPoints.subfield Φ K)ˣ, psl2DiagFixedHom Φ μ = x := by
  rw [psl2DiagFixed, Subgroup.mem_map]
  simp

theorem psl2DiagFixed_le_diag (Φ : Subgroup (K ≃+* K)) :
    psl2DiagFixed Φ ≤ burnsideAut_psl2Diag K := by
  intro x hx
  obtain ⟨μ, rfl⟩ := (mem_psl2DiagFixed_iff Φ).mp hx
  exact ⟨Units.map (FixedPoints.subfield Φ K).subtype.toMonoidHom μ, rfl⟩

theorem psl2DiagFixed_le_normalizer_upper (Φ : Subgroup (K ≃+* K)) :
    psl2DiagFixed Φ ≤ Subgroup.normalizer
      ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K)) := by
  rw [psl2UpperUnipotent_normalizer_eq_borel]
  exact (psl2DiagFixed_le_diag Φ).trans (burnsideAut_psl2Diag_le_borel)

theorem psl2FieldAut_apply_psl2DiagFixed (Φ : Subgroup (K ≃+* K)) {σ : K ≃+* K}
    (hσ : σ ∈ Φ) {h : PSL2 K} (hh : h ∈ psl2DiagFixed Φ) :
    psl2FieldAut K σ h = h := by
  obtain ⟨μ, rfl⟩ := (mem_psl2DiagFixed_iff Φ).mp hh
  refine psl2FieldAut_diag_fixed σ
    (Units.map (FixedPoints.subfield Φ K).subtype.toMonoidHom μ) ?_
  have hfix := (CFSG.Semidihedral.FixedFieldData.mem_fixedSubfield_iff K Φ
    (((μ : (FixedPoints.subfield Φ K)ˣ) : FixedPoints.subfield Φ K) : K)).mp
      (μ : FixedPoints.subfield Φ K).2 ⟨σ, hσ⟩
  simpa using hfix

theorem burnsideAut_psl2Diag_comm {x y : PSL2 K}
    (hx : x ∈ burnsideAut_psl2Diag K) (hy : y ∈ burnsideAut_psl2Diag K) :
    x * y = y * x := by
  obtain ⟨l, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  exact psl2DiagHom_comm l m

theorem conj_diag_mul_field_apply_psl2DiagFixed (Φ : Subgroup (K ≃+* K)) {σ : K ≃+* K}
    (hσ : σ ∈ Φ) {d : PSL2 K} (hd : d ∈ burnsideAut_psl2Diag K) {h : PSL2 K}
    (hh : h ∈ psl2DiagFixed Φ) :
    (MulAut.conj d * psl2FieldAut K σ) h = h := by
  rw [MulAut.mul_apply, psl2FieldAut_apply_psl2DiagFixed Φ hσ hh]
  have hcomm : d * h = h * d :=
    burnsideAut_psl2Diag_comm hd (psl2DiagFixed_le_diag Φ hh)
  rw [MulAut.conj_apply, hcomm]
  group

theorem psl2DiagFixed_centralized_mod_upper (Φ : Subgroup (K ≃+* K))
    {θ : MulAut (PSL2 K)} {u d : PSL2 K} {σ : K ≃+* K}
    (hu : u ∈ psl2UpperUnipotentSubgroup K) (hd : d ∈ burnsideAut_psl2Diag K)
    (hσ : σ ∈ Φ)
    (hfac : θ = MulAut.conj u * (MulAut.conj d * psl2FieldAut K σ))
    {h : PSL2 K} (hh : h ∈ psl2DiagFixed Φ) :
    θ h * h⁻¹ ∈ psl2UpperUnipotentSubgroup K := by
  have hfix := conj_diag_mul_field_apply_psl2DiagFixed Φ hσ hd hh
  have hθh : θ h = MulAut.conj u h := by
    rw [hfac, MulAut.mul_apply, hfix]
  have hhN : h ∈ Subgroup.normalizer
      ((psl2UpperUnipotentSubgroup K) : Set (PSL2 K)) :=
    psl2DiagFixed_le_normalizer_upper Φ hh
  have hconj : h * u⁻¹ * h⁻¹ ∈ psl2UpperUnipotentSubgroup K :=
    (Subgroup.mem_normalizer_iff.mp hhN u⁻¹).1 (Subgroup.inv_mem _ hu)
  rw [hθh, MulAut.conj_apply,
    show u * h * u⁻¹ * h⁻¹ = u * (h * u⁻¹ * h⁻¹) by group]
  exact Subgroup.mul_mem _ hu hconj

theorem exists_fieldPart_factorization [CharP K 2] (hK : Nat.card K = 2 ^ a)
    (Θ : Subgroup (MulAut (PSL2 K))) {θ θ₁ : MulAut (PSL2 K)} {h : PSL2 K}
    (hθ₁U : (psl2UpperUnipotentSubgroup K).map θ₁.toMonoidHom =
      psl2UpperUnipotentSubgroup K)
    (hθeq : θ₁ = (MulAut.conj h)⁻¹ * θ * MulAut.conj h)
    (Φ : Subgroup (K ≃+* K)) (hΦ : ∀ θ ∈ Θ, psl2FieldPart K θ ∈ Φ) (hθ : θ ∈ Θ) :
    ∃ (u d : PSL2 K) (σ : K ≃+* K), u ∈ psl2UpperUnipotentSubgroup K ∧
      d ∈ burnsideAut_psl2Diag K ∧ σ ∈ Φ ∧
      θ₁ = MulAut.conj u * (MulAut.conj d * psl2FieldAut K σ) := by
  obtain ⟨u, d, σ, hu, hd, hfac⟩ :=
    exists_factorization_of_normalizes_upper hK hθ₁U
  have hσeq : psl2FieldPart K θ₁ = σ := by
    rw [hfac, map_mul, map_mul, psl2FieldPart_conj, psl2FieldPart_conj,
      psl2FieldPart_psl2FieldAut, one_mul, one_mul]
  have hfield : psl2FieldPart K θ₁ = psl2FieldPart K θ := by
    rw [hθeq, map_mul, map_mul, map_inv, psl2FieldPart_conj, inv_one, one_mul, mul_one]
  refine ⟨u, d, σ, hu, hd, ?_, hfac⟩
  rw [← hσeq, hfield]
  exact hΦ θ hθ

theorem psl2DiagFixed_conj_centralizes [CharP K 2] (hK : Nat.card K = 2 ^ a)
    (Θ : Subgroup (MulAut (PSL2 K))) (hΘ : IsPGroup 2 Θ)
    (S : Sylow 2 (PSL2 K))
    (hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup (PSL2 K)),
      θ x ∈ (S : Subgroup (PSL2 K)))
    {h : PSL2 K}
    (hhU : (psl2UpperUnipotentSubgroup K).map (MulAut.conj h).toMonoidHom =
      (S : Subgroup (PSL2 K)))
    (Φ : Subgroup (K ≃+* K)) (hΦ : ∀ θ ∈ Θ, psl2FieldPart K θ ∈ Φ) :
    ∀ θ ∈ Θ, ∀ k ∈ (psl2DiagFixed Φ).map (MulAut.conj h).toMonoidHom,
      θ k * k⁻¹ ∈ (S : Subgroup (PSL2 K)) := by
  intro θ hθ k hk
  obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hk
  let θ₁ : MulAut (PSL2 K) := MulAut.conj (MulAut.conj h)⁻¹ θ
  have hθ₁U : (psl2UpperUnipotentSubgroup K).map θ₁.toMonoidHom =
      psl2UpperUnipotentSubgroup K := conj_theta_maps_upper hhU (hΘS θ hθ)
  obtain ⟨u, d, σ, hu, hd, hσmem, hfac⟩ :=
    exists_fieldPart_factorization hK Θ hθ₁U
      (show θ₁ = (MulAut.conj h)⁻¹ * θ * MulAut.conj h from rfl) Φ hΦ hθ
  have hcent : θ₁ h₀ * h₀⁻¹ ∈ psl2UpperUnipotentSubgroup K :=
    psl2DiagFixed_centralized_mod_upper Φ hu hd hσmem hfac hh₀
  have hθeq : θ = MulAut.conj h * θ₁ * (MulAut.conj h)⁻¹ := by
    rw [show θ₁ = (MulAut.conj h)⁻¹ * θ * MulAut.conj h from rfl]
    group
  have hcalc : θ (MulAut.conj h h₀) * (MulAut.conj h h₀)⁻¹ =
      MulAut.conj h (θ₁ h₀ * h₀⁻¹) := by
    have h1 : θ (MulAut.conj h h₀) = MulAut.conj h (θ₁ h₀) := by
      conv_lhs => rw [hθeq]
      simp only [MulAut.mul_apply]
      rw [MulAut.inv_apply_self]
    rw [h1]
    simp only [MulAut.conj_apply]
    group
  change θ ((MulAut.conj h) h₀) * ((MulAut.conj h) h₀)⁻¹ ∈
    (S : Subgroup (PSL2 K))
  rw [hcalc]
  have hmem : MulAut.conj h (θ₁ h₀ * h₀⁻¹) ∈
      (psl2UpperUnipotentSubgroup K).map (MulAut.conj h).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hcent
  rwa [hhU] at hmem

theorem diagFixed_conj_data [CharP K 2] (hK : Nat.card K = 2 ^ a)
    (S : Sylow 2 (PSL2 K)) {h : PSL2 K}
    (hhU : (psl2UpperUnipotentSubgroup K).map (MulAut.conj h).toMonoidHom =
      (S : Subgroup (PSL2 K)))
    (Φ : Subgroup (K ≃+* K)) :
    IsCyclic ((psl2DiagFixed Φ).map (MulAut.conj h).toMonoidHom) ∧
      Nat.card ((psl2DiagFixed Φ).map (MulAut.conj h).toMonoidHom) =
        2 ^ (a / Nat.card Φ) - 1 ∧
      (psl2DiagFixed Φ).map (MulAut.conj h).toMonoidHom ≤
        Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Subgroup.equivMapOfInjective (psl2DiagFixed Φ) (MulAut.conj h).toMonoidHom
      (MulAut.conj h).injective).isCyclic.mp (isCyclic_psl2DiagFixed Φ)
  · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective,
      card_psl2DiagFixed_eq_two_pow hK Φ]
  · have hmap := burnsideAut_map_le_normalizer_map (MulAut.conj h).toMonoidHom
      (psl2DiagFixed_le_normalizer_upper Φ)
    rwa [hhU] at hmap

theorem exists_borel_fixed_psl2 (hK : Nat.card K = 2 ^ a)
    (Θ : Subgroup (MulAut (PSL2 K))) (hΘ : IsPGroup 2 Θ)
    (S : Sylow 2 (PSL2 K))
    (hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup (PSL2 K)),
      θ x ∈ (S : Subgroup (PSL2 K))) :
    ∃ e m : ℕ, Nat.card (Θ.map (psl2FieldPart K)) = 2 ^ e ∧
      a = 2 ^ e * m ∧ ∃ H : Subgroup (PSL2 K), IsCyclic H ∧
        Nat.card H = 2 ^ m - 1 ∧
        H ≤ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K)) ∧
        (∀ θ ∈ Θ, ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup (PSL2 K))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card]; exact hK)
  have ha1 : 1 ≤ a := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    by_contra h
    have ha0 : a = 0 := by omega
    rw [ha0, pow_zero] at hK
    omega
  let Φ : Subgroup (K ≃+* K) := Θ.map (psl2FieldPart K)
  have hΦ : IsPGroup 2 Φ := hΘ.map (psl2FieldPart K)
  obtain ⟨e, he⟩ := hΦ.exists_card_eq
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  have hAut : Nat.card (K ≃+* K) = a :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have hΦdvd : Nat.card Φ ∣ a := by
    rw [← hAut]; exact Subgroup.card_subgroup_dvd_card Φ
  let m := a / Nat.card Φ
  have ham : a = 2 ^ e * m := by
    rw [← he]
    exact (Nat.mul_div_cancel' hΦdvd).symm
  obtain ⟨h, hhU⟩ := exists_conj_upper_of_sylow hK S
  obtain ⟨hHcyc, hHcard, hHnorm⟩ := diagFixed_conj_data hK S hhU Φ
  have hHcent : ∀ θ ∈ Θ, ∀ k ∈ (psl2DiagFixed Φ).map (MulAut.conj h).toMonoidHom,
      θ k * k⁻¹ ∈ (S : Subgroup (PSL2 K)) :=
    psl2DiagFixed_conj_centralizes hK Θ hΘ S hΘS hhU Φ
      (fun θ hθ => Subgroup.mem_map_of_mem _ hθ)
  exact ⟨e, m, he, ham, (psl2DiagFixed Φ).map (MulAut.conj h).toMonoidHom,
    hHcyc, hHcard, hHnorm, hHcent⟩

theorem exists_not_inner_of_trivial_fixed_field (hK : Nat.card K = 2 ^ a)
    (Θ : Subgroup (MulAut (PSL2 K))) (hΘ : IsPGroup 2 Θ) {e m : ℕ}
    (he : Nat.card (Θ.map (psl2FieldPart K)) = 2 ^ e)
    (hm : m = 1) (ha : a = 2 ^ e * m) (ha2 : 2 ≤ a) :
    ∃ θ ∈ Θ, ∀ x : PSL2 K, θ ^ (a / 2) ≠ MulAut.conj x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K))
      (fun _ _ h => RingEquiv.ext (congrFun h))
  obtain ⟨hAut, hcyc⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK
  letI : IsCyclic (K ≃+* K) := hcyc
  have ha' : a = 2 ^ e := by rw [ha, hm, mul_one]
  have hΦcard : Nat.card (Θ.map (psl2FieldPart K)) = a := by rw [he, ha']
  have htop : Θ.map (psl2FieldPart K) = ⊤ := by
    haveI : Finite ↥(Θ.map (psl2FieldPart K)) :=
      Finite.of_injective (fun x : ↥(Θ.map (psl2FieldPart K)) => (x : K ≃+* K))
        Subtype.coe_injective
    refine Subgroup.eq_top_of_card_eq (H := Θ.map (psl2FieldPart K)) ?_
    rw [hΦcard, hAut]
  obtain ⟨φ, hφ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K ≃+* K)
  have hφa : orderOf φ = a := by rw [hφ, hAut]
  obtain ⟨θ, hθ, hθφ⟩ :=
    Subgroup.mem_map.mp (show φ ∈ Θ.map (psl2FieldPart K) by rw [htop]; exact Subgroup.mem_top φ)
  refine ⟨θ, hθ, fun x hx => ?_⟩
  have hnot : φ ^ (a / 2) ≠ 1 := by
    intro hp
    have hdvd : a ∣ a / 2 := by
      have h := orderOf_dvd_of_pow_eq_one hp
      rwa [hφa] at h
    have hpos : 0 < a / 2 := by omega
    have hle : a ≤ a / 2 := Nat.le_of_dvd hpos hdvd
    omega
  apply hnot
  have h := congrArg (psl2FieldPart K) hx
  rwa [map_pow, hθφ, psl2FieldPart_conj] at h

theorem psl2_even_two_group_borel_fixed (hK : Nat.card K = 2 ^ a)
    (Θ : Subgroup (MulAut (PSL2 K))) (hΘ : IsPGroup 2 Θ)
    (S : Sylow 2 (PSL2 K))
    (hΘS : ∀ θ ∈ Θ, ∀ x ∈ (S : Subgroup (PSL2 K)),
      θ x ∈ (S : Subgroup (PSL2 K))) :
    ∃ e m : ℕ, a = 2 ^ e * m ∧ ∃ H : Subgroup (PSL2 K), IsCyclic H ∧
      Nat.card H = 2 ^ m - 1 ∧
      H ≤ Subgroup.normalizer ((S : Subgroup (PSL2 K)) : Set (PSL2 K)) ∧
      (∀ θ ∈ Θ, ∀ h ∈ H, θ h * h⁻¹ ∈ (S : Subgroup (PSL2 K))) ∧
      (m = 1 → 2 ≤ a → ∃ θ ∈ Θ, ∀ x : PSL2 K, θ ^ (a / 2) ≠ MulAut.conj x) := by
  obtain ⟨e, m, he, ham, H, hHcyc, hHcard, hHnorm, hHcent⟩ :=
    exists_borel_fixed_psl2 hK Θ hΘ S hΘS
  refine ⟨e, m, ham, H, hHcyc, hHcard, hHnorm, hHcent, ?_⟩
  intro hm ha2
  exact exists_not_inner_of_trivial_fixed_field hK Θ hΘ he hm ham ha2

end CFSG.Walter
