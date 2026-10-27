module

public import CFSG.RankThree.PartOne.SRC.RankOneNoncentral
public import CFSG.RankThree.PartOne.SRC.RankOneSL2
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.SL2MinimalFaithful Subgroup

theorem coprime_card_center_SL2 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {F : Type*} [Field F]
    [Finite F] :
    Nat.Coprime p (Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F))) := by
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (SpecialLinearGroup (Fin 2) F))
    p hdvd
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp x.2
  have h1 : (x : SpecialLinearGroup (Fin 2) F) ^ 2 = 1 := by
    have hr2 : r * r = 1 := by simpa [pow_two] using hr
    apply Subtype.ext
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, ← hrx, ← map_mul, hr2, map_one]
    rfl
  have h2 : orderOf x ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
    simpa using h1
  rw [hx] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)


theorem rank_four_of_cover_SL2 {p e : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
    [CharP F p] (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2) (he : 4 ≤ e)
    {W : Type} [Group W] [Finite W] (ρ : W →* SpecialLinearGroup (Fin 2) F)
    (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  classical
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hF81 : 81 ≤ p ^ e := by
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
      _ ≤ p ^ e := Nat.pow_le_pow_left hp3 e
  have hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) (F)) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2
      (F) le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  obtain ⟨W₀, -, hW₀min⟩ := Finite.exists_le_minimal (p := fun K : Subgroup W => K.map ρ = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective ρ hρ])
  set ρ₀ : W₀ →* SpecialLinearGroup (Fin 2) (F) := ρ.comp W₀.subtype with hρ₀
  have hρ₀s : Function.Surjective ρ₀ := by
    intro x
    have hx : x ∈ W₀.map ρ := by
      rw [hW₀min.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin₀ : ∀ M : Subgroup W₀, M.map ρ₀ = ⊤ → M = ⊤ := by
    intro M hM
    have h1 : (M.map W₀.subtype).map ρ = ⊤ := by
      rw [Subgroup.map_map]
      exact hM
    have h2 := hW₀min.le_of_le h1 (Subgroup.map_subtype_le M)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  have hker₀ : IsPGroup p ρ₀.ker := by
    intro x
    have hx1 : ρ ((x : W₀) : W) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨k, hk⟩ := hker ⟨((x : W₀) : W), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : ρ.ker => (z : W)) hk))⟩
  have hperf : Group.IsPerfect W₀ := by
    rw [Group.isPerfect_def]
    apply hmin₀
    have h1 := hQ.1.commutator_eq_top
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hρ₀s]
    rwa [_root_.commutator_def] at h1
  suffices H : ∃ (E : Subgroup W₀) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧
      Nat.card E = p ^ k by
    obtain ⟨E, k, hk, hE, hc⟩ := H
    refine ⟨E.map W₀.subtype, k, hk, isElementaryAbelian_map' W₀.subtype hE, ?_⟩
    rw [Subgroup.card_map_of_injective W₀.subtype_injective, hc]
  by_cases hcen : ρ₀.ker ≤ center W₀
  ·
    obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central
      (k := F) (by omega) (by omega) hρ₀s hcen
    let τ : Multiplicative (F) →* W₀ := σ.comp unipotentHom
    have hτinj : Function.Injective τ := by
      intro a b h
      apply unipotentHom_injective
      have := congrArg ρ₀ h
      simpa [τ, hσ] using this
    have hpow : ∀ a : Multiplicative (F), a ^ p = 1 := by
      intro a
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    refine ⟨τ.range, e, he, isElementaryAbelian_range τ hpow, ?_⟩
    rw [← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, ← hF]
    exact Nat.card_congr Multiplicative.toAdd
  ·
    by_contra hno
    push Not at hno
    apply hcen
    obtain ⟨ζ, hζ2, hζo⟩ := exists_torus_gen p e hp2 (by omega) hF
    refine central_of_rank_le_three hp hp2 he hQ ρ₀ hρ₀s hker₀ hmin₀ ?_
      (coprime_card_center_SL2 hp hp2) (torus ζ) (torus_not_mem_center hζ2)
      (Nat.Coprime.coprime_dvd_left (orderOf_torus_dvd ζ) hζo) ?_
    · rw [card_specialLinearGroup_fin_two, hF]
      exact dvd_mul_right _ _
    · intro E hE
      have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
      obtain ⟨k, hk⟩ := hEp.exists_card_eq
      rw [hk]
      by_contra hlt
      have hk4 : 4 ≤ k := by
        by_contra h
        push Not at h
        exact hlt (Nat.pow_le_pow_right hp.pos (by omega))
      exact hno E k hk4 hE hk

end CFSG.RankThree.PartOne.SRC
