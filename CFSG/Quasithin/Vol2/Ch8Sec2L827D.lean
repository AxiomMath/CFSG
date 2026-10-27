module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827B
public import CFSG.Quasithin.Vol2.Ch8Sec2L827C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

section L827D

theorem map_eq_bot_827 {Γ W : Type} [Group Γ] [Finite Γ] [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) (hW : Nat.card W = 16) (ψ : Γ →* MulAut W)
    {X₅ : Subgroup (MulAut W)} (hX₅ : AlternatingNatural X₅ ⊤ ⊥ 5) (hX₅ψ : X₅ ≤ ψ.range)
    {N O : Subgroup Γ} (hN : N.Normal) (hO : O.Normal) (hO2 : IsPGroup 2 ↥O)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hNp : ∀ n ∈ N, n ^ p ∈ O) : N.map ψ = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut W) := Finite.of_injective (fun f : MulAut W => (f : W → W))
    fun f f' h => MulEquiv.ext (congrFun h)
  set P := O.map ψ with hPdef
  have hP2 : IsPGroup 2 ↥P := hO2.map ψ
  let F : Subgroup W :=
    { carrier := {w | ∀ g ∈ P, g w = w}
      one_mem' := fun g _ => map_one g
      mul_mem' := fun {a b} ha hb g hg => by rw [map_mul, ha g hg, hb g hg]
      inv_mem' := fun {a} ha g hg => by rw [map_inv, ha g hg] }
  have hmemF : ∀ w, w ∈ F ↔ ∀ g ∈ P, g w = w := fun w => Iff.rfl
  have hFinv : ∀ x ∈ X₅, ∀ w ∈ F, x w ∈ F := by
    intro x hx w hw g hg
    obtain ⟨γ, rfl⟩ := hX₅ψ hx
    obtain ⟨o, ho, rfl⟩ := hg
    have hmem : (ψ γ)⁻¹ * ψ o * ψ γ ∈ P := by
      refine ⟨γ⁻¹ * o * γ, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have := hO.conj_mem o ho γ⁻¹
      rwa [inv_inv] at this
    have h1 := (hmemF w).mp hw _ hmem
    calc ψ o (ψ γ w) = ψ γ (((ψ γ)⁻¹ * ψ o * ψ γ) w) := by
          rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
      _ = ψ γ w := by rw [h1]
  have hFne : F ≠ ⊥ := by
    intro hbot
    have h := hP2.card_modEq_card_fixedPoints W
    have hfix : Nat.card (MulAction.fixedPoints ↥P W) = Nat.card F := by
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight fun w => ?_
      constructor
      · intro hw g hg
        have h1 := hw ⟨g, hg⟩
        rwa [Subgroup.smul_def, MulAut.smul_def] at h1
      · intro hw g
        rw [Subgroup.smul_def, MulAut.smul_def]
        exact hw g g.2
    rw [hfix, hbot, Subgroup.card_bot, hW] at h
    exact absurd h (by decide)
  have hFtop : F = ⊤ := eq_top_of_invariant_827 hX₅ hFinv hFne
  have hP1 : ∀ g ∈ P, g = 1 := fun g hg =>
    MulEquiv.ext fun w => (hmemF w).mp (hFtop ▸ Subgroup.mem_top w) g hg
  set R := N.map ψ with hRdef
  have hRp : IsPGroup p ↥R := by
    rintro ⟨r, n, hn, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    exact hP1 _ ⟨_, hNp n hn, rfl⟩
  have hRcard := card_of_isPGroup_827 (fun a b => mul_comm a b) hW2 hW hp hp2 hRp
  have hRn : ∀ y ∈ ψ.range, ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    rintro _ ⟨γ, rfl⟩ _ ⟨n, hn, rfl⟩
    exact ⟨γ * n * γ⁻¹, hN.conj_mem n hn γ, by rw [map_mul, map_mul, map_inv]⟩
  have hRN : ∀ x ∈ X₅, x ∈ Subgroup.normalizer (R : Set (MulAut W)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      exact hRn x (hX₅ψ hx) r hr
    · intro hr
      have := hRn x⁻¹ (inv_mem (hX₅ψ hx)) _ hr
      simpa [mul_assoc] using this
  set Q := Subgroup.centralizer (R : Set (MulAut W)) with hQdef
  have h5 : ∀ x ∈ X₅, x ^ 5 = 1 → x ∈ Q := by
    intro x hx hx5
    set α := R.normalizerMonoidHom ⟨x, hRN x hx⟩ with hαdef
    have hα5 : α ^ 5 = 1 := by
      rw [hαdef, ← map_pow]
      have : (⟨x, hRN x hx⟩ : ↥(Subgroup.normalizer (R : Set (MulAut W)))) ^ 5 = 1 :=
        Subtype.ext hx5
      rw [this, map_one]
    have hα1 : α = 1 := eq_one_of_pow_five_827 hRcard hα5
    have hker : (⟨x, hRN x hx⟩ : ↥(Subgroup.normalizer (R : Set (MulAut W)))) ∈
        R.normalizerMonoidHom.ker := hα1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  have hQn : ∀ x ∈ X₅, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := by
    intro x hx q hq
    rw [hQdef, Subgroup.mem_centralizer_iff] at hq ⊢
    intro r hr
    have hr' : x⁻¹ * r * x ∈ R := by
      have := hRn x⁻¹ (inv_mem (hX₅ψ hx)) r hr
      simpa using this
    have h1 := hq _ hr'
    calc r * (x * q * x⁻¹) = x * ((x⁻¹ * r * x) * q) * x⁻¹ := by group
      _ = x * (q * (x⁻¹ * r * x)) * x⁻¹ := by rw [h1]
      _ = x * q * x⁻¹ * r := by group
  have hX₅Q := le_of_pow_five_827 hX₅ hQn h5
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  refine eq_one_of_commute_827 hX₅ fun x hx => ?_
  exact Subgroup.mem_centralizer_iff.mp (hX₅Q hx) r hr

end L827D

end CFSG.Quasithin.H13
