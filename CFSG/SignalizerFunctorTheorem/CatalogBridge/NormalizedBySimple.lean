module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Assembly
public import Mathlib.GroupTheory.GroupAction.Period
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open Module CFSG.SignalizerFunctorTheorem.NonLocal CFSG.SignalizerFunctorTheorem.NonLocalExc
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem not_orderOf_eq_nine {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω ≤ 7)
    (α : Equiv.Perm Ω) : orderOf α ≠ 9 := by
  intro h9
  have := Fintype.ofFinite Ω
  have hcard : Fintype.card Ω ≤ 7 := by rwa [Nat.card_eq_fintype_card] at hΩ
  have hα3 : α ^ 3 = 1 := by
    ext x
    have hdvd : MulAction.period α x ∣ 9 := h9 ▸ MulAction.period_dvd_orderOf α x
    have hle : MulAction.period α x ≤ 7 :=
      (Function.minimalPeriod_le_card (f := fun y => α • y) (x := x)).trans hcard
    have h3 : MulAction.period α x ∣ 3 := by
      have h' : MulAction.period α x = 1 ∨ MulAction.period α x = 3 ∨
          MulAction.period α x = 9 := by
        have hm : MulAction.period α x ∈ Nat.divisors 9 := by simpa using hdvd
        have : Nat.divisors 9 = {1, 3, 9} := by decide
        rw [this] at hm
        simpa using hm
      rcases h' with h | h | h
      · rw [h]; exact one_dvd _
      · rw [h]
      · omega
    obtain ⟨c, hc⟩ := h3
    have hp : (α ^ MulAction.period α x) x = x := MulAction.pow_period_smul α x
    rw [hc, pow_mul]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hp c
  have : orderOf α ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
  rw [h9] at this
  omega

theorem exists_forall_exists_pow_apply_eq {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω ≤ 7)
    (α : Equiv.Perm Ω) (hα : α ^ 7 = 1) (hne : α ≠ 1) :
    ∃ x₀ : Ω, ∀ y : Ω, ∃ k : ℕ, (α ^ k) x₀ = y := by
  have := Fintype.ofFinite Ω
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, α x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  have hper : MulAction.period α x₀ = 7 := by
    have hdvd : MulAction.period α x₀ ∣ 7 :=
      (MulAction.period_dvd_orderOf α x₀).trans (orderOf_dvd_of_pow_eq_one hα)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hdvd with h | h
    · exfalso
      apply hx₀
      have := MulAction.pow_period_smul α x₀
      rw [h, pow_one] at this
      exact this
    · exact h
  have hinj : Function.Injective (fun k : Fin 7 => (α ^ (k : ℕ)) x₀) := by
    intro k₁ k₂ h
    simp only at h
    by_contra hne'
    have hne'' : (k₁ : ℕ) ≠ k₂ := fun e => hne' (Fin.ext e)
    wlog hlt : (k₁ : ℕ) < k₂ generalizing k₁ k₂
    · exact this h.symm (Ne.symm hne') (Ne.symm hne'')
        (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne''))
    have h1 : (α ^ ((k₂ : ℕ) - k₁)) x₀ = x₀ := by
      have e : α ^ (k₂ : ℕ) = α ^ (k₁ : ℕ) * α ^ ((k₂ : ℕ) - k₁) := by
        rw [← pow_add]; congr 1; omega
      have h2 : (α ^ (k₁ : ℕ)) ((α ^ ((k₂ : ℕ) - k₁)) x₀) = (α ^ (k₁ : ℕ)) x₀ := by
        rw [← Equiv.Perm.mul_apply, ← e]; exact h.symm
      exact (α ^ (k₁ : ℕ)).injective h2
    have h3 : MulAction.period α x₀ ∣ (k₂ : ℕ) - k₁ :=
      (MulAction.pow_smul_eq_iff_period_dvd).1 h1
    rw [hper] at h3
    have := Nat.le_of_dvd (by omega) h3
    have := k₂.2
    omega
  have hbij : Function.Bijective (fun k : Fin 7 => (α ^ (k : ℕ)) x₀) :=
    hinj.bijective_of_nat_card_le (by simpa using hΩ)
  refine ⟨x₀, fun y => ?_⟩
  obtain ⟨k, hk⟩ := hbij.2 y
  exact ⟨k, hk⟩

theorem eq_bot_of_normalized_by_simple
    {D X : Type*} [Group D] [Group X] [Finite X] (ι : D →* X) (hι : Function.Injective ι)
    {F W : Type*} [Field F] [IsAlgClosed F] [CharP F 3] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (ρ : X →* Module.End F W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank F W ≤ 7) (hZ : ∀ x : X, (∀ y : X, x * y = y * x) → x = 1)
    [IsSimpleGroup D] (g w : D) (hg : orderOf g = 7) (hw : orderOf w = 9)
    (A : Subgroup D) (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    (hAg : ∀ x ∈ A, g * x * g⁻¹ ∈ A) (hAg' : ∃ x ∈ A, g * x * g⁻¹ ≠ x)
    {s : ℕ} (hs : s.Prime) (hs3 : s ≠ 3) (V : Subgroup X)
    (hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVs : ∀ v ∈ V, v ^ s = 1)
    (hVD : ∀ d : D, ∀ v ∈ V, ι d * v * (ι d)⁻¹ ∈ V) : V = ⊥ := by
  classical
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have hVc : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
  have hinvV : (Nat.card V : F) ≠ 0 := cast_card_ne_zero_of_exponent h3 hs hs3 hVs
  obtain ⟨hfinV, hcardV⟩ := finite_card_weights ρ V hVc
  have := hfinV
  have hcardV7 : Nat.card (Wt ρ V) ≤ 7 := hcardV.trans hdim
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (weightAction ρ V ι hVD).ker with hker | hker
  ·
    exfalso
    have hinj : Function.Injective (weightAction ρ V ι hVD) :=
      (MonoidHom.ker_eq_bot_iff _).1 hker
    exact not_orderOf_eq_nine hcardV7 (weightAction ρ V ι hVD w)
      (by rw [orderOf_injective _ hinj, hw])
  ·
    have hcentV : ∀ d : D, ∀ v ∈ V, ι d * v * (ι d)⁻¹ = v := fun d =>
      centralizes_of_weightAction_eq_one ρ hρ V hVc hinvV ι hVD d (by
        have : d ∈ (weightAction ρ V ι hVD).ker := by rw [hker]; trivial
        exact this)
    have hA'V : ∀ a ∈ A.map ι, ∀ v ∈ V, a * v = v * a := by
      rintro _ ⟨a, ha, rfl⟩ v hv
      calc ι a * v = (ι a * v * (ι a)⁻¹) * ι a := by group
        _ = v * ι a := by rw [hcentV a v hv]
    set B : Subgroup X := Subgroup.closure ((A.map ι : Set X) ∪ (V : Set X)) with hBdef
    have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      have hpw : ((A.map ι : Set X) ∪ (V : Set X)).Pairwise Commute := by
        intro x hx y hy _
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · obtain ⟨a, ha, rfl⟩ := hx
          obtain ⟨b, hb, rfl⟩ := hy
          exact (by rw [← map_mul, ← map_mul, hAcomm a ha b hb] : ι a * ι b = ι b * ι a)
        · exact hA'V x hx y hy
        · exact (hA'V y hy x hx).symm
        · exact hVcomm x hx y hy
      have := Subgroup.isMulCommutative_closure hpw
      intro x hx y hy
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : B) ⟨y, hy⟩)
    have hBc : IsMulCommutative B := ⟨⟨fun a b => Subtype.ext (hBcomm _ a.2 _ b.2)⟩⟩
    have hBexp : ∀ x ∈ B, x ^ (2 * s) = 1 := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => x ^ (2 * s) = 1) ?_ ?_ ?_ ?_ hx
      · rintro y (hy | hy)
        · obtain ⟨a, ha, rfl⟩ := hy
          rw [← map_pow, pow_mul, hA2 a ha, one_pow, map_one]
        · rw [mul_comm, pow_mul, hVs y hy, one_pow]
      · exact one_pow _
      · intro y z hy hz hy' hz'
        rw [(show Commute y z from hBcomm y hy z hz).mul_pow, hy', hz', one_mul]
      · intro y hy hy'
        rw [inv_pow, hy', inv_one]
    have hcardB : ¬ 3 ∣ Nat.card B := by
      intro h
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
      have hd : orderOf x ∣ 2 * s := by
        refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
        simpa using hBexp x x.2
      rw [hx] at hd
      have h3s : 3 ∣ s := Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) hd
      exact hs3 ((Nat.prime_dvd_prime_iff_eq h3 hs).1 h3s).symm
    have hinvB : (Nat.card B : F) ≠ 0 := fun h => hcardB ((CharP.cast_eq_zero_iff F 3 _).1 h)
    have hg'V : ∀ v ∈ V, ι g * v * (ι g)⁻¹ = v := hcentV g
    have hg'B : ∀ x ∈ B, ι g * x * (ι g)⁻¹ ∈ B := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => ι g * x * (ι g)⁻¹ ∈ B) ?_ ?_ ?_ ?_ hx
      · rintro y (hy | hy)
        · obtain ⟨a, ha, rfl⟩ := hy
          refine Subgroup.subset_closure (Or.inl ⟨g * a * g⁻¹, hAg a ha, ?_⟩)
          simp [map_mul, map_inv]
        · rw [hg'V y hy]
          exact Subgroup.subset_closure (Or.inr hy)
      · simp
      · intro y z _ _ hy' hz'
        have : ι g * (y * z) * (ι g)⁻¹ = (ι g * y * (ι g)⁻¹) * (ι g * z * (ι g)⁻¹) := by group
        rw [this]
        exact B.mul_mem hy' hz'
      · intro y _ hy'
        have : ι g * y⁻¹ * (ι g)⁻¹ = (ι g * y * (ι g)⁻¹)⁻¹ := by group
        rw [this]
        exact B.inv_mem hy'
    have hgpow : ∀ k : ℕ, ∀ x ∈ B, ι (g ^ k) * x * (ι (g ^ k))⁻¹ ∈ B := by
      intro k
      induction k with
      | zero => intro x hx; simpa using hx
      | succ k ih =>
        intro x hx
        have : ι (g ^ (k + 1)) * x * (ι (g ^ (k + 1)))⁻¹ =
            ι g * (ι (g ^ k) * x * (ι (g ^ k))⁻¹) * (ι g)⁻¹ := by
          rw [pow_succ', map_mul, mul_inv_rev]; group
        rw [this]
        exact hg'B _ (ih x hx)
    obtain ⟨hfinB, hcardB'⟩ := finite_card_weights ρ B hBc
    have := hfinB
    have hcardB7 : Nat.card (Wt ρ B) ≤ 7 := hcardB'.trans hdim
    have hg7 : g ^ 7 = 1 := hg ▸ pow_orderOf_eq_one g
    have hnormB : ∀ γ : Subgroup.zpowers g, ∀ b ∈ B,
        (ι.comp (Subgroup.zpowers g).subtype) γ * b * ((ι.comp (Subgroup.zpowers g).subtype) γ)⁻¹
          ∈ B := by
      rintro ⟨γ, hγ⟩ b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hγ
      have hn : g ^ n = g ^ (n % (7 : ℕ)).toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
        have := zpow_mod_orderOf g n
        rw [hg] at this
        exact this.symm
      simpa [hn] using hgpow (n % (7 : ℕ)).toNat b hb
    set γ0 : Subgroup.zpowers g := ⟨g, Subgroup.mem_zpowers g⟩ with hγ0
    by_cases hψ1 : weightAction ρ B (ι.comp (Subgroup.zpowers g).subtype) hnormB γ0 = 1
    ·
      exfalso
      have hc := centralizes_of_weightAction_eq_one ρ hρ B hBc hinvB
        (ι.comp (Subgroup.zpowers g).subtype) hnormB γ0 hψ1
      obtain ⟨x, hxA, hx⟩ := hAg'
      apply hx
      have hxB : ι x ∈ B := Subgroup.subset_closure (Or.inl ⟨x, hxA, rfl⟩)
      have := hc (ι x) hxB
      apply hι
      simpa [map_mul, map_inv, hγ0] using this
    ·
      have hα7 : weightAction ρ B (ι.comp (Subgroup.zpowers g).subtype) hnormB γ0 ^ 7 = 1 := by
        rw [← map_pow]
        have : γ0 ^ 7 = 1 := Subtype.ext (by simpa [hγ0] using hg7)
        rw [this, map_one]
      obtain ⟨x₀, hx₀⟩ := exists_forall_exists_pow_apply_eq hcardB7 _ hα7 hψ1
      refine (Subgroup.eq_bot_iff_forall V).2 fun v hv => ?_
      have hvB : v ∈ B := Subgroup.subset_closure (Or.inr hv)
      have hconst : ∀ k : ℕ, ((weightAction ρ B (ι.comp (Subgroup.zpowers g).subtype) hnormB γ0 ^ k)
          x₀).1 ⟨v, hvB⟩ = x₀.1 ⟨v, hvB⟩ := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ', Equiv.Perm.mul_apply, weightAction_apply]
          have : conjV (ι.comp (Subgroup.zpowers g).subtype) B hnormB γ0 ⟨v, hvB⟩ = ⟨v, hvB⟩ := by
            refine Subtype.ext ?_
            rw [coe_conjV]
            have hcomm : ι g * v = v * ι g := mul_inv_eq_iff_eq_mul.1 (hg'V v hv)
            simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, hγ0]
            calc (ι g)⁻¹ * v * ι g = (ι g)⁻¹ * (v * ι g) := by group
              _ = (ι g)⁻¹ * (ι g * v) := by rw [hcomm]
              _ = v := by group
          rw [this]
          exact ih
      have hscalar : ρ v = x₀.1 ⟨v, hvB⟩ • (1 : Module.End F W) := by
        refine eq_smul_one_of_weights ρ B hBc hinvB v _ (fun χ hχ w hw => ?_)
        obtain ⟨k, hk⟩ := hx₀ ⟨χ, hχ⟩
        have h1 : χ ⟨v, hvB⟩ = x₀.1 ⟨v, hvB⟩ := by
          rw [← hconst k, hk]
        rw [hw ⟨v, hvB⟩, h1]
      have hcomm : ∀ y : X, v * y = y * v := by
        intro y
        apply hρ
        rw [map_mul, map_mul, hscalar, mul_smul_comm, smul_mul_assoc, one_mul, mul_one]
      exact hZ v hcomm

end CFSG.SignalizerFunctorTheorem.CatalogBridge
