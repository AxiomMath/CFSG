module

public import CFSG.Quasithin.Background.B5Sec
public import CFSG.Quasithin.Background.HSL3Alpha

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank H H.SL3Pair
open scoped Matrix

namespace B69

theorem two_mul_card_fix_le_of_rk {V : Type*} [CommGroup V] [Finite V] (hV : IsPGroup 2 V)
    {B : Subgroup (MulAut V)} (hB2 : IsElemAbelian2 B) (h : rk ↥B + 1 ≤ rkIdx (fixV B)) :
    2 * Nat.card ↥B * Nat.card ↥(fixV B) ≤ Nat.card V := by
  have hBc : Nat.card ↥B = 2 ^ rk ↥B := card_eq_two_pow_of_isPGroup hB2.isPGroup
  have hFc : Nat.card ↥(fixV B) = 2 ^ rk ↥(fixV B) :=
    card_eq_two_pow_of_isPGroup (hV.to_subgroup _)
  have hVc : Nat.card V = 2 ^ rk V := card_eq_two_pow_of_isPGroup hV
  have hr := rk_add_rkIdx (fixV B)
  rw [hBc, hFc, hVc, ← pow_succ', ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

section Pair

open Matrix

variable {K : Type} [Field K] [Finite K]

theorem isPGroup_pairMod {n : ℕ} (hK : Nat.card K = 2 ^ n) : IsPGroup 2 (PairMod K) := by
  have : Nat.card (PairMod K) = 2 ^ (6 * n) := by
    rw [card_pairMod, hK, ← pow_mul, mul_comm]
  exact IsPGroup.of_card this

theorem rk_succ_le_rkIdx_pair_two {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {B : Subgroup (MulAut (PairMod K))} (hBN : B ≤ pairNorm K) (hBs : B ≤ pairSub K)
    (hB2 : IsElemAbelian2 B) (hB1 : B ≠ ⊥) : rk ↥B + 1 ≤ rkIdx (fixV B) := by
  have _ := hBs
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ n) hK
  have := rk_add_two_le_rkIdx_fixV hn hK hBN hB2 hB1
  omega

theorem card_mul_le_of_linear_two [CharP K 2] (hq2 : 2 ≤ Nat.card K)
    {A : Subgroup (MulAut (PairMod K))} (hAN : A ≤ pairNorm K) (hA2 : IsElemAbelian2 A)
    (hA1 : A ≠ ⊥) (hsub : A ≤ pairSub K) (hlin : fstSub A ≤ linSub) :
    2 * Nat.card A * Nat.card ↥(fixV A) ≤ Nat.card K ^ 6 := by
  classical
  have : Finite (MulAut (StdMod (Fin 3) K)) := MulEquiv.finite_left
  have hF2 := isElemAbelian2_fstSub hA2
  set E := linMat (fstSub A) with hEdef
  have hEcard : Nat.card E = Nat.card (fstSub A) := by
    rw [hEdef, card_linMat, inf_eq_left.mpr hlin]
  have h1 := card_le_card_fstSub hAN hA2
  rw [inf_eq_left.mpr hsub] at h1
  obtain ⟨hRC, hcard⟩ := card_le_of_elemAbelian_GL3' E (linMat_sq hF2) (linMat_comm hF2)
  have hfix : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixSp E) *
      Nat.card {w : Fin 3 → K // ∀ B ∈ E, (B : Matrix (Fin 3) (Fin 3) K)ᵀ *ᵥ w = w} := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun v => (⟨Multiplicative.toAdd (v : PairMod K).1, ?_⟩,
        ⟨Multiplicative.toAdd (v : PairMod K).2, ?_⟩)) fun v w h => ?_
    · refine (Submodule.mem_iInf _).mpr fun B => ?_
      obtain ⟨⟨x, hx, hxB⟩, -⟩ := B.2
      have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      have h := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply, hxB] at h
      have h' : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
          Multiplicative.toAdd (v : PairMod K).1 =
          Multiplicative.toAdd (v : PairMod K).1 :=
        congrArg (fun z : PairMod K => Multiplicative.toAdd z.1) h
      rw [LinearMap.mem_ker, nOf_apply, h', sub_self]
    · intro B hB
      obtain ⟨⟨x, hx, hxB⟩, -⟩ := hB
      have hxA : (x : MulAut (PairMod K)) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      have hx2 : (x : MulAut (PairMod K)) * x = 1 := by
        rw [← sq]
        exact hA2.2 _ hxA
      obtain ⟨-, hT⟩ := snd_eq_transpose (hAN hxA) hx2 hxB
      have h := v.2 _ hxA
      rw [eq_pairAut x, pairAut_apply] at h
      have h' : toAddMap (sndHom K x) (Multiplicative.toAdd (v : PairMod K).2) =
          Multiplicative.toAdd (v : PairMod K).2 :=
        congrArg (fun z : PairMod K => Multiplicative.toAdd z.2) h
      rw [← hT]
      exact h'
    · have h1 := congrArg (fun p => (p.1 : Fin 3 → K)) h
      have h2 := congrArg (fun p => (p.2 : Fin 3 → K)) h
      exact Subtype.ext (Prod.ext h1 h2)
  have hD := card_transpose_fix_le E
  have hC : Nat.card ↥(fixSp E) = Nat.card K ^ Module.finrank K (fixSp E) :=
    Module.natCard_eq_pow_finrank (K := K) (V := fixSp E)
  have hc3 : Module.finrank K (fixSp E) ≤ 3 := by
    have := Submodule.finrank_le (fixSp E)
    rwa [Module.finrank_fin_fun] at this
  have hrc := Submodule.finrank_mono hRC
  have hA2' : 2 ≤ Nat.card A := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have := (Finite.one_lt_card_iff_nontrivial (α := ↥A)).mpr ⟨⟨⟨a, ha⟩, 1, ha1⟩⟩
    omega
  have hpos : 1 ≤ (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) := by
    by_contra h
    push Not at h
    have h0 : (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) = 0 := by omega
    rw [h0, pow_zero] at hcard
    omega
  have hexp : Module.finrank K (fixSp E) + (3 - Module.finrank K (commSp E)) +
      (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E) ≤ 5 := by
    generalize Module.finrank K (fixSp E) = c at hc3 hrc hpos ⊢
    generalize Module.finrank K (commSp E) = r at hrc hpos ⊢
    interval_cases c <;> interval_cases r <;> omega
  have hA : Nat.card A ≤
      Nat.card K ^ ((3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) := by
    rw [← hEcard] at h1
    exact h1.trans hcard
  have hfix' : Nat.card ↥(fixV A) ≤ Nat.card K ^ Module.finrank K (fixSp E) *
      Nat.card K ^ (3 - Module.finrank K (commSp E)) := by
    rw [← hC]
    exact hfix.trans (Nat.mul_le_mul_left _ hD)
  calc 2 * Nat.card A * Nat.card ↥(fixV A)
      ≤ 2 * Nat.card K ^ ((3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) *
          (Nat.card K ^ Module.finrank K (fixSp E) *
            Nat.card K ^ (3 - Module.finrank K (commSp E))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hA) hfix'
    _ = 2 * Nat.card K ^ (Module.finrank K (fixSp E) + (3 - Module.finrank K (commSp E)) +
          (3 - Module.finrank K (fixSp E)) * Module.finrank K (commSp E)) := by
        ring
    _ ≤ 2 * Nat.card K ^ 5 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega) hexp)
    _ ≤ Nat.card K * Nat.card K ^ 5 := Nat.mul_le_mul_right _ hq2
    _ = Nat.card K ^ 6 := by ring


omit [Finite K] in
theorem eq_zero_or_one_of_card_two (hK2 : Nat.card K = 2) (c : K) : c = 0 ∨ c = 1 := by
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.1 hK2
  have key : ∀ z : K, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set K) := by rw [hset]; trivial
    simpa using this
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1 <;> rcases key c with hc | hc <;>
    first
    | exact absurd (h0.trans h1.symm) zero_ne_one
    | exact Or.inl (hc.trans h0.symm)
    | exact Or.inr (hc.trans h1.symm)

omit [Finite K] in
theorem fstSub_le_linSub_of_card_two (hK2 : Nat.card K = 2)
    (E : Subgroup (MulAut (StdMod (Fin 3) K))) : E ≤ linSub := by
  intro g _
  rw [mem_linSub]
  intro c v
  rcases eq_zero_or_one_of_card_two hK2 c with rfl | rfl
  · simp [toAddMap_zero]
  · simp

theorem two_mul_card_fix_le_pair {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {B : Subgroup (MulAut (PairMod K))} (hBN : B ≤ pairNorm K) (hBs : B ≤ pairSub K)
    (hB2 : IsElemAbelian2 B) (hB1 : B ≠ ⊥) :
    2 * Nat.card ↥B * Nat.card ↥(fixV B) ≤ Nat.card (PairMod K) := by
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    have hK2 : Nat.card K = 2 := by simpa using hK
    have := card_mul_le_of_linear_two (K := K) (by omega) hBN hB2 hB1 hBs
      (fstSub_le_linSub_of_card_two hK2 _)
    rwa [card_pairMod]
  · exact two_mul_card_fix_le_of_rk (isPGroup_pairMod hK) hB2
      (rk_succ_le_rkIdx_pair_two h2 hK hBN hBs hB2 hB1)

end Pair

section Main

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem secHom_conj {A L : Subgroup (MulAut V)} {W U : Subgroup V} (hAW : A ≤ stabSub W)
    (hAU : A ≤ stabSub U) (hLW : L ≤ stabSub W) (hLU : L ≤ stabSub U)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (a : ↥A) (l : ↥L) :
    B5.secHom A hAW hAU a * B5.secHom L hLW hLU l * (B5.secHom A hAW hAU a)⁻¹ =
      B5.secHom L hLW hLU ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAn a a.2 l l.2⟩ := by
  rw [← map_inv]
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H w => rfl

omit [Finite V] in
theorem two_mul_card_le_of_dual {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {A L : Subgroup (MulAut V)} (hA : IsElemAbelian2 A)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) {W₁ W₂ U : Subgroup V}
    (hAW₁ : A ≤ stabSub W₁) (hAW₂ : A ≤ stabSub W₂) (hAU : A ≤ stabSub U)
    (hLW₁ : L ≤ stabSub W₁) (hLW₂ : L ≤ stabSub W₂) (hLU : L ≤ stabSub U)
    (r : ↥L →* ↥(StatedSL 3 K)) (hr : Function.Surjective r)
    (e₁ : Sec W₁ U ≃* StdMod (Fin 3) K) (e₂ : Sec W₂ U ≃* StdMod (Fin 3) K)
    (he₁ : ∀ (l : ↥L) (s : Sec W₁ U), e₁ (B5.secHom L hLW₁ hLU l s) =
      matAut ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) (e₁ s))
    (he₂ : ∀ (l : ↥L) (s : Sec W₂ U), e₂ (B5.secHom L hLW₂ hLU l s) =
      matAut (dualGL ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K)) (e₂ s))
    (hB : ¬ A ≤ centSec W₁ U) :
    2 * Nat.card ↥A * Nat.card ↥(fixV (autSec A W₁ U)) * Nat.card ↥(fixV (autSec A W₂ U)) ≤
      Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U) *
        Nat.card ↥(A ⊓ centSec W₁ U ⊓ centSec W₂ U) := by
  classical
  let σ₁ := B5.secHom A hAW₁ hAU
  let σ₂ := B5.secHom A hAW₂ hAU
  let ε₁ : ↥A →* MulAut (StdMod (Fin 3) K) := (congrHom e₁).comp σ₁
  let ε₂ : ↥A →* MulAut (StdMod (Fin 3) K) := (congrHom e₂).comp σ₂
  let ξ : ↥A →* MulAut (PairMod K) := (pairHom₂ K).comp (ε₁.prod ε₂)
  have hξ : ∀ a : ↥A, ξ a = pairAut (ε₁ a) (ε₂ a) := fun a => rfl
  have hm₁ : ∀ l : ↥L, congrHom e₁ (B5.secHom L hLW₁ hLU l) =
      matAut ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) := by
    intro l
    refine MulEquiv.ext fun x => ?_
    rw [congrHom_apply]
    have := he₁ l (e₁.symm x)
    rwa [MulEquiv.apply_symm_apply] at this
  have hm₂ : ∀ l : ↥L, congrHom e₂ (B5.secHom L hLW₂ hLU l) =
      matAut (dualGL ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K)) := by
    intro l
    refine MulEquiv.ext fun x => ?_
    rw [congrHom_apply]
    have := he₂ l (e₂.symm x)
    rwa [MulEquiv.apply_symm_apply] at this
  have hc₁ : ∀ (a : ↥A) (l : ↥L), ε₁ a * matAut ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) *
      (ε₁ a)⁻¹ = matAut ((r ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAn a a.2 l l.2⟩ :
        ↥(StatedSL 3 K)) : GL (Fin 3) K) := by
    intro a l
    rw [← hm₁ l, ← hm₁ ⟨_, hAn a a.2 l l.2⟩,
      ← secHom_conj hAW₁ hAU hLW₁ hLU hAn a l]
    simp only [ε₁, σ₁, MonoidHom.comp_apply, map_mul, map_inv]
  have hc₂ : ∀ (a : ↥A) (l : ↥L), ε₂ a *
      matAut (dualGL ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K)) * (ε₂ a)⁻¹ =
      matAut (dualGL ((r ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAn a a.2 l l.2⟩ :
        ↥(StatedSL 3 K)) : GL (Fin 3) K)) := by
    intro a l
    rw [← hm₂ l, ← hm₂ ⟨_, hAn a a.2 l l.2⟩,
      ← secHom_conj hAW₂ hAU hLW₂ hLU hAn a l]
    simp only [ε₂, σ₂, MonoidHom.comp_apply, map_mul, map_inv]
  have hconjN : ∀ a : ↥A, ∀ γ ∈ StatedSL 3 K, ∃ δ ∈ StatedSL 3 K,
      ξ a * pairHom γ * (ξ a)⁻¹ = pairHom δ := by
    intro a γ hγ
    obtain ⟨l, hl⟩ := hr ⟨γ, hγ⟩
    refine ⟨((r ⟨(a : MulAut V) * l * (a : MulAut V)⁻¹, hAn a a.2 l l.2⟩ :
      ↥(StatedSL 3 K)) : GL (Fin 3) K), (r _).2, ?_⟩
    have hγl : γ = ((r l : ↥(StatedSL 3 K)) : GL (Fin 3) K) := by rw [hl]
    rw [hξ, pairHom_apply, pairHom_apply, pairAut_inv, pairAut_mul, pairAut_mul, hγl,
      hc₁ a l, hc₂ a l]
  have hN : ∀ a : ↥A, ξ a ∈ pairNorm K := fun a =>
    mem_pairNorm_of (hconjN a) (fun γ hγ => by
      obtain ⟨δ, hδ, h⟩ := hconjN a⁻¹ γ hγ
      refine ⟨δ, hδ, ?_⟩
      simpa [map_inv] using h)
  set B : Subgroup (MulAut (PairMod K)) := ξ.range with hBdef
  have hBN : B ≤ pairNorm K := by
    rintro _ ⟨a, rfl⟩
    exact hN a
  have hBs : B ≤ pairSub K := by
    rintro _ ⟨a, rfl⟩
    rw [hξ]
    exact pairAut_mem_pairSub _ _
  have hB2 : IsElemAbelian2 B := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hA.1 a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.2 a a.2)
      rw [this, map_one]
  have hB1 : B ≠ ⊥ := by
    obtain ⟨a, haA, haC⟩ := IsConcreteLE.not_le_iff_exists.1 hB
    intro hbot
    have hmem : ξ ⟨a, haA⟩ ∈ B := ⟨_, rfl⟩
    rw [hbot, Subgroup.mem_bot, hξ] at hmem
    have h1 : ε₁ ⟨a, haA⟩ = 1 := (pairAut_injective (hmem.trans pairAut_one.symm)).1
    have h2 : σ₁ ⟨a, haA⟩ = 1 :=
      congrHom_injective e₁ (by rw [map_one]; exact h1)
    exact haC ((B5.mem_ker_secHom A hAW₁ hAU ⟨a, haA⟩).1 (MonoidHom.mem_ker.2 h2))
  have h2 := two_mul_card_fix_le_pair hn hK hBN hBs hB2 hB1
  have hcardV : Nat.card (PairMod K) = Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U) := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.prodCongr e₁.toEquiv e₂.toEquiv)).symm
  have hfixB : fixV B = (fixV ε₁.range).prod (fixV ε₂.range) := by
    ext x
    simp only [mem_fixV, Subgroup.mem_prod]
    constructor
    · intro h
      refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · obtain ⟨a, rfl⟩ := hg
        have := h (ξ a) ⟨a, rfl⟩
        rw [hξ] at this
        exact congrArg Prod.fst this
      · obtain ⟨a, rfl⟩ := hg
        have := h (ξ a) ⟨a, rfl⟩
        rw [hξ] at this
        exact congrArg Prod.snd this
    · rintro ⟨h1, h2⟩ b ⟨a, rfl⟩
      rw [hξ]
      exact Prod.ext (h1 _ ⟨a, rfl⟩) (h2 _ ⟨a, rfl⟩)
  have hrange₁ : ε₁.range = (autSec A W₁ U).map (congrHom e₁) := by
    rw [MonoidHom.range_comp, ← B5.range_secHom A hAW₁ hAU]
  have hrange₂ : ε₂.range = (autSec A W₂ U).map (congrHom e₂) := by
    rw [MonoidHom.range_comp, ← B5.range_secHom A hAW₂ hAU]
  have hF₁ : Nat.card ↥(fixV ε₁.range) = Nat.card ↥(fixV (autSec A W₁ U)) := by
    rw [hrange₁, fixV_map_congrHom e₁ (autSec A W₁ U)]
    exact Subgroup.card_map_of_injective e₁.injective
  have hF₂ : Nat.card ↥(fixV ε₂.range) = Nat.card ↥(fixV (autSec A W₂ U)) := by
    rw [hrange₂, fixV_map_congrHom e₂ (autSec A W₂ U)]
    exact Subgroup.card_map_of_injective e₂.injective
  have hfixcard : Nat.card ↥(fixV B) =
      Nat.card ↥(fixV (autSec A W₁ U)) * Nat.card ↥(fixV (autSec A W₂ U)) := by
    rw [hfixB, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hF₁, hF₂]
  have hker : ξ.ker = (A ⊓ centSec W₁ U ⊓ centSec W₂ U).subgroupOf A := by
    ext a
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      rw [hξ] at h
      obtain ⟨h1, h2⟩ := pairAut_injective (h.trans pairAut_one.symm)
      refine ⟨⟨a.2, ?_⟩, ?_⟩
      · exact (B5.mem_ker_secHom A hAW₁ hAU a).1
          (MonoidHom.mem_ker.2 (congrHom_injective e₁ (by rw [map_one]; exact h1)))
      · exact (B5.mem_ker_secHom A hAW₂ hAU a).1
          (MonoidHom.mem_ker.2 (congrHom_injective e₂ (by rw [map_one]; exact h2)))
    · rintro ⟨⟨-, h1⟩, h2⟩
      rw [hξ]
      have e1 : σ₁ a = 1 := MonoidHom.mem_ker.1 ((B5.mem_ker_secHom A hAW₁ hAU a).2 h1)
      have e2 : σ₂ a = 1 := MonoidHom.mem_ker.1 ((B5.mem_ker_secHom A hAW₂ hAU a).2 h2)
      have f1 : ε₁ a = 1 := by simp only [ε₁, MonoidHom.comp_apply, e1, map_one]
      have f2 : ε₂ a = 1 := by simp only [ε₂, MonoidHom.comp_apply, e2, map_one]
      rw [f1, f2]
      exact pairAut_one
  have hK0A : A ⊓ centSec W₁ U ⊓ centSec W₂ U ≤ A := inf_le_left.trans inf_le_left
  have hcardK : Nat.card ↥ξ.ker = Nat.card ↥(A ⊓ centSec W₁ U ⊓ centSec W₂ U) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0A).toEquiv
  have hcardA : Nat.card ↥B * Nat.card ↥ξ.ker = Nat.card ↥A := by
    have := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥A) ξ
    rwa [← MonoidHom.range_eq_map, top_inf_eq, Subgroup.card_top] at this
  rw [hfixcard, hcardV] at h2
  rw [← hcardA, ← hcardK]
  calc 2 * (Nat.card ↥B * Nat.card ↥ξ.ker) * Nat.card ↥(fixV (autSec A W₁ U)) *
        Nat.card ↥(fixV (autSec A W₂ U))
      = (2 * Nat.card ↥B * (Nat.card ↥(fixV (autSec A W₁ U)) *
          Nat.card ↥(fixV (autSec A W₂ U)))) * Nat.card ↥ξ.ker := by ring
    _ ≤ (Nat.card (Sec W₁ U) * Nat.card (Sec W₂ U)) * Nat.card ↥ξ.ker :=
        Nat.mul_le_mul_right _ h2

end Main

end B69

end CFSG.Quasithin
