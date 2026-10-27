module

public import CFSG.Quasithin.MS93.S33Lin
public import CFSG.Quasithin.MS93.S33Base
public import CFSG.Quasithin.MS93.S33Semi

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section SL3

variable {F : Type} [Field F] [Fintype F] {a : ↥L →* ↥(StatedSL 3 F)}
  {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 3 → F)}

omit [Finite G] [Fintype F] in
theorem isCoordAct_of_nat
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    (l : ↥L) : IsCoordAct β l ((a l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec := by
  intro u v huv
  simpa [moduleAct] using hβα l u v huv 0

omit [Finite G] [Fintype F] in
theorem fix_of_mem_centralizer {R : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.centralizer (R : Set G)) {f : (Fin 3 → F) → (Fin 3 → F)}
    (hf : IsCoordAct β y f) {x : Fin 3 → F} (hx : x ∈ coordSub β R) : f x = x := by
  obtain ⟨u, hu, rfl⟩ := hx
  have hc : (u : G) = y * u * y⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hy u hu
    rw [← this, mul_inv_cancel_right]
  exact (hf u u hc).symm

variable (h : PUHyp M T L) (ha : Function.Surjective a) (hβ : Function.Surjective β)
  (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
  (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
    Multiplicative.toAdd (β v) i =
      (moduleAct false (a l : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
include h ha hβ hβker hβα

omit [Fintype F] in
theorem exists_semilinear_of_mem {m : G} (hm : m ∈ M) {f : (Fin 3 → F) → (Fin 3 → F)}
    (hf : IsCoordAct β m f) :
    ∃ σ : F →+* F, ∀ (c : F) (x : Fin 3 → F), f (c • x) = σ c • f x := by
  have hmV := le_normalizer_Uq (T := T) h.le_normalizer hm
  obtain ⟨f₀, hf₀⟩ := exists_isCoordAct' hβ hβker hmV
  obtain ⟨f₁, hf₁⟩ := exists_isCoordAct' hβ hβker (inv_mem hmV)
  obtain ⟨σ, hσ⟩ := exists_semilinear ha (h.L_le.trans (le_normalizer_Uq h.le_normalizer)) hβ
    (isCoordAct_of_nat hβα) hmV (h.le_normalizer hm) hf₀ hf₁
  have he := IsCoordAct.unique hβ hmV hf hf₀
  exact ⟨σ, fun c x => by rw [he]; exact hσ c x⟩

omit [Fintype F] in
theorem linear_of_fix {m : G} (hm : m ∈ M) {f : (Fin 3 → F) → (Fin 3 → F)}
    (hf : IsCoordAct β m f) {x₀ : Fin 3 → F} (hx₀ : x₀ ≠ 0) (hfix : ∀ c : F, f (c • x₀) = c • x₀) :
    ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := by
  obtain ⟨σ, hσ⟩ := exists_semilinear_of_mem h ha hβ hβker hβα hm hf
  have hσc : ∀ c : F, σ c = c := by
    intro c
    have h1 := hσ c x₀
    rw [hfix, show f x₀ = x₀ by simpa using hfix 1] at h1
    have h2 := sub_eq_zero.2 h1
    rw [← sub_smul] at h2
    exact (sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hx₀)).symm
  intro c x
  rw [hσ, hσc]

theorem card_commutator_Uq {n : ℕ} (hcard : Fintype.card F = 2 ^ n) {E Y : Subgroup G}
    (hE : E ≤ T) (hY : Y ≤ T)
    (hlin : ∀ e ∈ E, ∀ f : (Fin 3 → F) → (Fin 3 → F), IsCoordAct β e f →
      ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x)
    (hR : ⁅Uq M T L, E⁆ ≠ ⊥) (hYR : Y ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G))
    (hYn : ¬ ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆) : Nat.card ↥⁅Uq M T L, E⁆ = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hEV : E ≤ Subgroup.normalizer (Uq M T L : Set G) := hE.trans hTV
  have hRV : ⁅Uq M T L, E⁆ ≤ Uq M T L :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hEV
  set P := coordSub β ⁅Uq M T L, E⁆ with hPdef
  have hPs : ∀ (c : F) (x : Fin 3 → F), x ∈ P → c • x ∈ P := fun c x hx =>
    smul_mem_coordSub_commutator hβ hβker hEV hlin c hx
  set S := subOf P hPs with hSdef
  have hcS : Nat.card S = Nat.card ↥⁅Uq M T L, E⁆ :=
    (card_subOf P hPs).trans (card_coordSub hβker hRV)
  have hS : Nat.card S = Fintype.card F ^ Module.finrank F S := card_submodule S
  have hStop : S ≠ ⊤ := by
    intro htop
    have hP : P = ⊤ := by
      ext x
      exact (Submodule.ext_iff.1 htop x)
    rw [hPdef, coordSub_eq_top_iff hβker hβ hRV] at hP
    exact (commutator_Uq_lt h hE).ne hP
  have hd3 : Module.finrank F S < 3 := by
    have := Submodule.finrank_lt hStop
    rwa [Module.finrank_fin_fun] at this
  have hd0 : Module.finrank F S ≠ 0 := by
    intro h0
    rw [h0, pow_zero, hcS] at hS
    exact hR (Subgroup.eq_bot_of_card_eq _ hS)
  have hd2 : Module.finrank F S ≠ 2 := by
    intro h2
    apply hYn
    have hYV : ⁅Uq M T L, Y⁆ ≤ Uq M T L :=
      (Subgroup.le_normalizer_iff_commutator_le_left).mp (hY.trans hTV)
    rw [← coordSub_le_coordSub_iff hβker hYV]
    refine coordSub_commutator_le hβker hβ (hY.trans hTV) fun y hy f hf x => ?_
    obtain ⟨f₀, hf₀⟩ := exists_isCoordAct' hβ hβker (hTV (hY hy))
    rw [IsCoordAct.unique hβ (hTV (hY hy)) hf hf₀]
    have hfix : ∀ x ∈ S, f₀ x = x := fun x hx => fix_of_mem_centralizer (hYR hy) hf₀ hx
    have hSbot : S ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨x₀, hx₀S, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hSbot
    have hlin₀ := linear_of_fix h ha hβ hβker hβα (h.le (hY hy)) hf₀ hx₀
      (fun c => hfix _ (S.smul_mem c hx₀S))
    obtain ⟨e, he⟩ := h.isPGroup ⟨y, hY hy⟩
    have he' : y ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
    have hpow := iterate_eq_of_pow_eq_one hβ (hTV (hY hy)) hf₀ he'
    exact sub_mem_of_finrank_two h2 hlin₀ hfix hpow x
  have hd1 : Module.finrank F S = 1 := by omega
  rw [← hcS, hS, hd1, pow_one, hcard]

theorem relIndex_commutator_Uq {n : ℕ} (hcard : Fintype.card F = 2 ^ n) {E Y : Subgroup G}
    (hE : E ≤ T) (hY : Y ≤ T)
    (hlin : ∀ e ∈ E, ∀ f : (Fin 3 → F) → (Fin 3 → F), IsCoordAct β e f →
      ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x)
    (hEc : E ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G))
    (hYR : Y ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G))
    (hYn : ¬ ⁅Uq M T L, Y⁆ ≤ ⁅Uq M T L, E⁆) (hcardR : Nat.card ↥⁅Uq M T L, E⁆ = 2 ^ n) :
    ⁅Uq M T L, E⁆.relIndex ⁅Uq M T L, Y ⊔ E⁆ = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Y ⊔ E with hKdef
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hKT : K ≤ T := sup_le hY hE
  have hKV : K ≤ Subgroup.normalizer (Uq M T L : Set G) := hKT.trans hTV
  have hEV : E ≤ Subgroup.normalizer (Uq M T L : Set G) := hE.trans hTV
  have hRV : ⁅Uq M T L, E⁆ ≤ Uq M T L :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hEV
  have hRKV : ⁅Uq M T L, K⁆ ≤ Uq M T L :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hKV
  have hKc : K ≤ Subgroup.centralizer ((⁅Uq M T L, E⁆ : Subgroup G) : Set G) := sup_le hYR hEc
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  set P₁ := coordSub β ⁅Uq M T L, E⁆ with hP₁
  have hP₁s : ∀ (c : F) (x : Fin 3 → F), x ∈ P₁ → c • x ∈ P₁ := fun c x hx =>
    smul_mem_coordSub_commutator hβ hβker hEV hlin c hx
  set S₁ := subOf P₁ hP₁s with hS₁
  have hcS₁ : Nat.card S₁ = Nat.card ↥⁅Uq M T L, E⁆ :=
    (card_subOf P₁ hP₁s).trans (card_coordSub hβker hRV)
  have hd₁ : Module.finrank F S₁ = 1 := by
    have h1 := card_submodule S₁
    rw [hcS₁, hcardR, ← hcard] at h1
    exact (Nat.pow_right_injective hq (h1.symm.trans (pow_one _).symm))
  have hS₁bot : S₁ ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hd₁
    exact absurd hd₁ (by norm_num)
  obtain ⟨x₀, hx₀S, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS₁bot
  have hKlin : ∀ k ∈ K, ∀ f : (Fin 3 → F) → (Fin 3 → F), IsCoordAct β k f →
      ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := by
    intro k hk f hf
    exact linear_of_fix h ha hβ hβker hβα (h.le (hKT hk)) hf hx₀
      (fun c => fix_of_mem_centralizer (hKc hk) hf (S₁.smul_mem c hx₀S))
  set P₂ := coordSub β ⁅Uq M T L, K⁆ with hP₂
  have hP₂s : ∀ (c : F) (x : Fin 3 → F), x ∈ P₂ → c • x ∈ P₂ := fun c x hx =>
    smul_mem_coordSub_commutator hβ hβker hKV hKlin c hx
  set S₂ := subOf P₂ hP₂s with hS₂
  have hcS₂ : Nat.card S₂ = Nat.card ↥⁅Uq M T L, K⁆ :=
    (card_subOf P₂ hP₂s).trans (card_coordSub hβker hRKV)
  have hRK : ⁅Uq M T L, E⁆ ≤ ⁅Uq M T L, K⁆ := Subgroup.commutator_mono le_rfl le_sup_right
  have hS₁₂ : S₁ < S₂ := by
    refine lt_of_le_of_ne (fun x hx => (coordSub_le_coordSub_iff hβker hRV).2 hRK hx) ?_
    intro he
    apply hYn
    have hle : ⁅Uq M T L, K⁆ ≤ ⁅Uq M T L, E⁆ := by
      rw [← coordSub_le_coordSub_iff hβker hRKV]
      intro x hx
      have : x ∈ S₂ := hx
      rw [← he] at this
      exact this
    exact (Subgroup.commutator_mono le_rfl le_sup_left).trans hle
  have hS₂top : S₂ ≠ ⊤ := by
    intro htop
    have hP : P₂ = ⊤ := by
      ext x
      exact (Submodule.ext_iff.1 htop x)
    rw [hP₂, coordSub_eq_top_iff hβker hβ hRKV] at hP
    exact (commutator_Uq_lt h hKT).ne hP
  have hd₂ : Module.finrank F S₂ = 2 := by
    have h1 := Submodule.finrank_lt_finrank_of_lt hS₁₂
    have h2 := Submodule.finrank_lt hS₂top
    rw [Module.finrank_fin_fun] at h2
    omega
  have hcK : Nat.card ↥⁅Uq M T L, K⁆ = 2 ^ n * 2 ^ n := by
    rw [← hcS₂, card_submodule, hd₂, hcard]
    ring
  have hmul := Subgroup.relIndex_mul_card (H := ⁅Uq M T L, E⁆) (K := ⁅Uq M T L, K⁆)
  rw [inf_eq_left.2 hRK, hcardR, hcK] at hmul
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero n two_ne_zero)) hmul

end SL3

end CFSG.Quasithin.MS93.S33
