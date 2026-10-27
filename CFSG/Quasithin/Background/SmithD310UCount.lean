module

public import CFSG.Quasithin.Background.SmithD310UInner
public import CFSG.Quasithin.Background.SmithD310USetup
public import CFSG.Quasithin.Background.SmithD39TwoSocle
public import CFSG.Quasithin.Background.SmithD39TwoMod

public section

namespace CFSG.Quasithin.SmithD310U

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Quasithin.SmithD39Two
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.F918X
open scoped Pointwise Matrix

section Count

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem count_of_le_isoComp [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {I : Subgroup Q} (hI : XMod.IsIrr ↥Λ I)
    {A : Subgroup Γ} (hA : IsPGroup 2 A) (hAI : ∀ a ∈ A, a • I = I) {Y : Subgroup Q}
    (hYΛ : XMod.IsInv ↥Λ Y) (hYA : ∀ a ∈ A, ∀ y ∈ Y, a • y ∈ Y)
    (hYI : Y ≤ isoComp ↥Λ I) :
    ∃ c : ℕ, rk ↥Y = c * rk ↥I ∧ c * nB A I ≤ nB A Y := by
  classical
  set H : Subgroup Γ := A ⊔ Λ with hH
  have hAImem : ∀ a ∈ A, ∀ v ∈ I, a • v ∈ I := by
    intro a ha v hv
    rw [← hAI a ha]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
  have hΛI : ∀ l ∈ Λ, ∀ v ∈ I, l • v ∈ I := fun l hl v hv => hI.1 ⟨l, hl⟩ v hv
  have hIH : ∀ g : ↥H, ∀ v ∈ I, g • v ∈ I := fun g => smul_mem_of_mem_sup hAImem hΛI g.2
  have hΛY : ∀ l ∈ Λ, ∀ y ∈ Y, l • y ∈ Y := fun l hl y hy => hYΛ ⟨l, hl⟩ y hy
  have hYH : ∀ g : ↥H, ∀ y ∈ Y, g • y ∈ Y := fun g => smul_mem_of_mem_sup hYA hΛY g.2
  let _iI := subAct (Γ := ↥H) I hIH
  let _iY := subAct (Γ := ↥H) Y hYH
  have hA' : IsPGroup 2 (A.subgroupOf H) := A4.isPGroup_subgroupOf_of_le le_sup_left hA
  have hAΛ' : ∀ a ∈ A.subgroupOf H, ∀ l ∈ Λ.subgroupOf H, a * l * a⁻¹ ∈ Λ.subgroupOf H :=
    fun a _ l hl => hΛ a l hl
  have hgen : A.subgroupOf H ⊔ Λ.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hirr : ∀ J : Subgroup ↥I, (∀ l ∈ Λ.subgroupOf H, ∀ p ∈ J, l • p ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hinv : XMod.IsInv ↥Λ (J.map I.subtype) := by
      rintro ⟨l, hl⟩ _ ⟨p, hp, rfl⟩
      have hlH : l ∈ H := (le_sup_right : Λ ≤ A ⊔ Λ) hl
      exact ⟨_, hJ ⟨l, hlH⟩ hl p hp, rfl⟩
    rcases hI.2.2 _ hinv bot_le (Subgroup.map_subtype_le J) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective J I.subtype_injective).1 h
    · right
      rw [eq_top_iff]
      intro p _
      have : (p : Q) ∈ J.map I.subtype := by rw [h]; exact p.2
      obtain ⟨p', hp', he⟩ := this
      rwa [show p' = p from Subtype.ext he] at hp'
  have hYsq : ∀ y : ↥Y, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using hQ y)
  have hgenQ : (⊤ : Subgroup ↥Y) ≤ ⨆ (φ : ↥I →* ↥Y)
      (_ : ∀ l ∈ Λ.subgroupOf H, ∀ p, φ (l • p) = l • φ p), φ.range := by
    have := isSemisimpleModule_toSubmod hI hYΛ hYI
    obtain ⟨c, ⟨e⟩⟩ := (isIsotypicOfType_toSubmod hI hYΛ hYI).linearEquiv_fun
    let f : Fin c → (↥(XMod.toSubmod hI.1) →ₗ[↥(XMod.opRing ↥Λ Q)] ↥(XMod.toSubmod hYΛ)) :=
      fun i => e.symm.toLinearMap ∘ₗ
        LinearMap.single ↥(XMod.opRing ↥Λ Q) (fun _ => ↥(XMod.toSubmod hI.1)) i
    let φ : Fin c → (↥I →* ↥Y) := fun i =>
      { toFun := fun v => ⟨Additive.toMul (f i ⟨Additive.ofMul (v : Q), v.2⟩).1, (f i _).2⟩
        map_one' := by
          apply Subtype.ext
          show Additive.toMul (f i 0).1 = 1
          rw [map_zero]
          rfl
        map_mul' := fun v w => by
          apply Subtype.ext
          show Additive.toMul (f i (⟨Additive.ofMul (v : Q), v.2⟩ +
            ⟨Additive.ofMul (w : Q), w.2⟩)).1 = Additive.toMul (f i ⟨_, v.2⟩).1 *
              Additive.toMul (f i ⟨_, w.2⟩).1
          rw [map_add]
          rfl }
    have hφΛ : ∀ i, ∀ l ∈ Λ.subgroupOf H, ∀ p, φ i (l • p) = l • φ i p := by
      intro i l hl p
      apply Subtype.ext
      let ρ : ↥(XMod.opRing ↥Λ Q) :=
        ⟨XMod.actEnd ↥Λ Q ⟨((l : ↥H) : Γ), hl⟩, XMod.actEnd_mem_opRing _⟩
      have h1 : (⟨Additive.ofMul (((l • p : ↥I) : Q)), (l • p).2⟩ : ↥(XMod.toSubmod hI.1)) =
          ρ • ⟨Additive.ofMul (p : Q), p.2⟩ := Subtype.ext rfl
      have h2 : f i ⟨Additive.ofMul (((l • p : ↥I) : Q)), (l • p).2⟩ =
          ρ • f i ⟨Additive.ofMul (p : Q), p.2⟩ := by
        rw [h1, map_smul]
      exact congrArg (fun z : ↥(XMod.toSubmod hYΛ) => Additive.toMul z.1) h2
    intro y _
    set w := e ⟨Additive.ofMul (y : Q), y.2⟩ with hw
    have key : (⟨Additive.ofMul (y : Q), y.2⟩ : ↥(XMod.toSubmod hYΛ)) = ∑ i, f i (w i) := by
      rw [← e.symm_apply_apply ⟨Additive.ofMul (y : Q), y.2⟩, ← hw]
      conv_lhs => rw [← Finset.univ_sum_single w]
      exact _root_.map_sum e.symm.toLinearMap _ _
    have key2 : y = ∏ i, φ i ⟨Additive.toMul (w i).1, (w i).2⟩ := by
      apply Subtype.ext
      have h1 := congrArg (fun z : ↥(XMod.toSubmod hYΛ) => Additive.toMul (z : Additive Q)) key
      simp only [toMul_ofMul] at h1
      rw [h1, Submodule.coe_sum, toMul_sum, SubmonoidClass.coe_finsetProd]
      rfl
    rw [key2]
    exact Subgroup.prod_mem _ fun i _ =>
      (le_iSup₂_of_le (φ i) (hφΛ i) le_rfl : (φ i).range ≤ _) ⟨_, rfl⟩
  obtain ⟨c, hc1, hc2⟩ := count_of_homs hA' hAΛ' hgen hirr (Nat.card ↥Y) ↥Y rfl hYsq hgenQ
  refine ⟨c, hc1, ?_⟩
  rw [nB_top_subAct I hIH A le_sup_left, nB_top_subAct Y hYH A le_sup_left] at hc2
  exact hc2

theorem card_eqv_smul_le [Finite Q] {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    (g : Γ) (I : Subgroup Q) :
    Nat.card {θ : ↥(g • I) →* ↥(g • I) // IsEqv Λ ((g • I).subtype.comp θ)} ≤
      Nat.card {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} := by
  classical
  have : Finite (↥I →* ↥I) := Finite.of_injective (fun θ : ↥I →* ↥I => (θ : ↥I → ↥I))
    DFunLike.coe_injective
  set e := XMod.smulEquiv g I with he
  let F : {θ : ↥(g • I) →* ↥(g • I) // IsEqv Λ ((g • I).subtype.comp θ)} →
      {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} := fun θ =>
    ⟨e.symm.toMonoidHom.comp (θ.1.comp e.toMonoidHom), by
      intro l v w hvw
      have h1 : ((⟨g * l * g⁻¹, hΛ g l l.2⟩ : ↥Λ) : Γ) • ((e v : ↥(g • I)) : Q) =
          ((e w : ↥(g • I)) : Q) := by
        show (g * l * g⁻¹) • g • (v : Q) = g • (w : Q)
        rw [← hvw, smul_smul, smul_smul, inv_mul_cancel_right]
      have h2 := θ.2 ⟨g * l * g⁻¹, hΛ g l l.2⟩ (e v) (e w) h1
      show g⁻¹ • ((θ.1 (e w) : ↥(g • I)) : Q) = (l : Γ) • g⁻¹ • ((θ.1 (e v) : ↥(g • I)) : Q)
      have h3 : ((θ.1 (e w) : ↥(g • I)) : Q) =
          (g * l * g⁻¹) • ((θ.1 (e v) : ↥(g • I)) : Q) := h2
      rw [h3, smul_smul, smul_smul]
      congr 1
      group⟩
  have hF : Function.Injective F := by
    intro θ θ' h
    have h1 := congrArg Subtype.val h
    apply Subtype.ext
    refine MonoidHom.ext fun y => ?_
    have h2 := congrArg (fun φ : ↥I →* ↥I => e (φ (e.symm y))) h1
    simpa [F] using h2
  exact Nat.card_le_card_of_injective F hF

theorem fixed_eq_sup_of_inf_eq_bot {B : Subgroup Γ} {S₁ S₂ : Subgroup Q}
    (h₁ : ∀ b ∈ B, ∀ s ∈ S₁, b • s ∈ S₁) (h₂ : ∀ b ∈ B, ∀ s ∈ S₂, b • s ∈ S₂)
    (hd : S₁ ⊓ S₂ = ⊥) (htop : S₁ ⊔ S₂ = ⊤) :
    XMod.fixed ↥B (⊤ : Subgroup Q) =
      (S₁ ⊓ XMod.fixed ↥B ⊤) ⊔ (S₂ ⊓ XMod.fixed ↥B ⊤) := by
  refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
  intro x hx
  have hx' : x ∈ S₁ ⊔ S₂ := by rw [htop]; trivial
  obtain ⟨s, hs, s', hs', rfl⟩ := Subgroup.mem_sup.1 hx'
  have hfix : ∀ b : ↥B, b • (s * s') = s * s' := fun b => (XMod.mem_fixed.1 hx).2 b
  have hsfix : ∀ b : ↥B, b • s = s ∧ b • s' = s' := by
    intro b
    have h1 := hfix b
    rw [smul_mul'] at h1
    exact eq_of_mul_eq_of_disjoint hd (h₁ b b.2 s hs) hs (h₂ b b.2 s' hs') hs' h1
  exact Subgroup.mul_mem_sup ⟨hs, XMod.mem_fixed.2 ⟨trivial, fun b => (hsfix b).1⟩⟩
    ⟨hs', XMod.mem_fixed.2 ⟨trivial, fun b => (hsfix b).2⟩⟩

theorem smul_isoSum_le_isoComp {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) (g : Γ) :
    g • isoSum Λ V ≤ isoComp ↥Λ (g • V) := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  rw [← smul_inv_smul g (isoComp ↥Λ (g • V)), Subgroup.pointwise_smul_le_pointwise_smul_iff]
  refine iSup₂_le fun x hx => ?_
  rw [← Subgroup.pointwise_smul_le_pointwise_smul_iff (a := g), smul_inv_smul, smul_smul]
  refine le_isoComp (isIrr_smul hN (g * x) hV) ?_
  rw [mul_smul]
  exact XMod.iso_smul hN g hx

end Count

section Natural

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]
  {Λ : Subgroup Γ} {Vt : Subgroup Q} {hVt : ∀ l : ↥Λ, ∀ v ∈ Vt, l • v ∈ Vt}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥(actAut Λ Vt hVt).range}

theorem card_eqv_le
    (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia (actAut Λ Vt hVt).range ⊤ ⊥ π) :
    Nat.card {θ : ↥Vt →* ↥Vt // IsEqv Λ (Vt.subtype.comp θ)} ≤ Nat.card K := by
  classical
  obtain ⟨E, hE⟩ := exists_coord hπ
  let fth : (↥Vt →* ↥Vt) → (Fin 3 → K) →+ (Fin 3 → K) := fun θ =>
    { toFun := fun v => Multiplicative.toAdd (E (θ (E.symm (Multiplicative.ofAdd v))))
      map_zero' := by simp
      map_add' := fun x y => by rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul] }
  have hfth : ∀ (θ : ↥Vt →* ↥Vt) (u : ↥Vt),
      fth θ (Multiplicative.toAdd (E u)) = Multiplicative.toAdd (E (θ u)) := by
    intro θ u
    simp [fth]
  have hsurjE : ∀ v : Fin 3 → K, ∃ u, Multiplicative.toAdd (E u) = v :=
    fun v => ⟨E.symm (Multiplicative.ofAdd v), by simp⟩
  have hγ : ∀ (θ : {θ : ↥Vt →* ↥Vt // IsEqv Λ (Vt.subtype.comp θ)}) (γ : ↥(StatedSL 3 K))
      (v : Fin 3 → K), fth θ.1 (((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ fth θ.1 v := by
    intro θ γ v
    obtain ⟨u, rfl⟩ := hsurjE v
    obtain ⟨l, hl⟩ := (π γ).2
    have h1 : (l : Γ) • (u : Q) =
        ((((π γ : ↥(actAut Λ Vt hVt).range) : MulAut ↥Vt) u : ↥Vt) : Q) := by
      rw [← hl]
      rfl
    have h2 := θ.2 l u _ h1
    have h3 : θ.1 (((π γ : ↥(actAut Λ Vt hVt).range) : MulAut ↥Vt) u) =
        ((π γ : ↥(actAut Λ Vt hVt).range) : MulAut ↥Vt) (θ.1 u) := by
      apply Subtype.ext
      rw [show ((((π γ : ↥(actAut Λ Vt hVt).range) : MulAut ↥Vt) (θ.1 u) : ↥Vt) : Q) =
        (l : Γ) • ((θ.1 u : ↥Vt) : Q) by rw [← hl]; rfl]
      exact h2
    rw [← hE, hfth, hfth, h3, hE]
  have hcomm : ∀ (θ : {θ : ↥Vt →* ↥Vt // IsEqv Λ (Vt.subtype.comp θ)}) (i j : Fin 3), i ≠ j →
      ∀ (c : K) (v : Fin 3 → K),
        fth θ.1 (v + Pi.single i (c * v j)) = fth θ.1 v + Pi.single i (c * fth θ.1 v j) := by
    intro θ i j hij c v
    have h := hγ θ (specialLinearGroupEquivStatedSL 3 K (tv i j hij c)) v
    rw [specialLinearGroupEquivStatedSL_coe, tv_mulVec, tv_mulVec] at h
    exact h
  let Φ : {θ : ↥Vt →* ↥Vt // IsEqv Λ (Vt.subtype.comp θ)} → K := fun θ =>
    fth θ.1 (Pi.single 0 1) 0
  have hΦ : Function.Injective Φ := by
    intro θ θ' h
    obtain ⟨l, hl⟩ := exists_smul_of_comm (fth θ.1) (hcomm θ)
    obtain ⟨l', hl'⟩ := exists_smul_of_comm (fth θ'.1) (hcomm θ')
    have hll : l = l' := by
      have e1 : Φ θ = l := by simp [Φ, hl]
      have e2 : Φ θ' = l' := by simp [Φ, hl']
      rw [← e1, ← e2, h]
    apply Subtype.ext
    refine MonoidHom.ext fun u => E.injective (Multiplicative.toAdd.injective ?_)
    rw [← hfth, ← hfth, hl, hl', hll]
  exact Nat.card_le_card_of_injective Φ hΦ

end Natural

section Arith

theorem arith_nonswap {n k c c' f₁ f₂ rA rB N NC : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hc : 1 ≤ c) (hc' : 1 ≤ c') (hck : c ≤ k) (hc'k : c' ≤ k)
    (hf₁ : f₁ + n ≤ 3 * n) (hf₂ : f₂ + n ≤ 3 * n)
    (hBA : rB ≤ rA) (hS1 : rA ≤ rB + 2 * n) (hS2 : n + rA + f₁ + f₂ ≤ rB + 6 * n)
    (hNC : c * (3 * n - f₁) + c' * (3 * n - f₂) ≤ NC) (hD7 : NC < 2 * (rA - rB))
    (hN : (2 * k - (c + c')) * (3 * n) + NC ≤ N) (hN2 : N ≤ 2 * rA)
    (hcL : rB ≤ n * c * (k - c) + n * c' * (k - c')) : False := by
  have hcc : c + c' ≤ 3 := by
    by_contra h
    push Not at h
    have h1 : c * n ≤ c * (3 * n - f₁) := Nat.mul_le_mul_left c (by omega)
    have h2 : c' * n ≤ c' * (3 * n - f₂) := Nat.mul_le_mul_left c' (by omega)
    have h3 : 4 * n ≤ (c + c') * n := Nat.mul_le_mul_right n h
    have h4 : (c + c') * n = c * n + c' * n := add_mul c c' n
    omega
  have hnk : n * 2 ≤ n * k := Nat.mul_le_mul_left n hk
  have hf₁' : f₁ ≤ 3 * n := by omega
  have hf₂' : f₂ ≤ 3 * n := by omega
  have hcc2 : c + c' ≤ 2 * k := by omega
  zify [hck, hc'k, hf₁', hf₂', hBA, hcc2] at hNC hD7 hN hcL
  have hc3 : c ≤ 2 := by omega
  have hc'3 : c' ≤ 2 := by omega
  interval_cases c <;> interval_cases c' <;> push_cast at * <;> nlinarith

theorem arith_swap {n k c rA rA₀ rB N : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) (hc : 1 ≤ c)
    (hck : c ≤ k) (hBA : rB ≤ rA) (hA0 : rA ≤ rA₀ + 1) (hS1 : rA₀ ≤ rB + 2 * n)
    (hD7 : c * (3 * n) < 2 * (rA - rB))
    (hN : k * (3 * n) + (k * (3 * n) - c * (3 * n)) ≤ N) (hN2 : N ≤ 2 * rA)
    (hcL : rB ≤ n * c * (k - c)) : False := by
  have hc1 : c = 1 := by
    by_contra h
    have h2 : 2 * (3 * n) ≤ c * (3 * n) := Nat.mul_le_mul_right _ (by omega)
    omega
  subst hc1
  have hnk : n * 2 ≤ n * k := Nat.mul_le_mul_left n hk
  have h1 : 1 * (3 * n) ≤ k * (3 * n) := Nat.mul_le_mul_right _ (by omega)
  zify [hck, hBA, h1] at hD7 hN hcL
  push_cast at *
  nlinarith

theorem card_le_two_mul_of_split {G : Type*} [Group G] [Finite G] {A A₀ : Subgroup G}
    (hA₀A : A₀ ≤ A) {a : G} (ha : a ∈ A) (hsplit : ∀ x ∈ A, x ∈ A₀ ∨ a⁻¹ * x ∈ A₀) :
    Nat.card ↥A ≤ 2 * Nat.card ↥A₀ := by
  let f : ↥A₀ ⊕ ↥A₀ → ↥A := fun x => match x with
    | Sum.inl b => ⟨b, hA₀A b.2⟩
    | Sum.inr b => ⟨a * b, A.mul_mem ha (hA₀A b.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rcases hsplit x hx with h | h
    · exact ⟨Sum.inl ⟨x, h⟩, rfl⟩
    · refine ⟨Sum.inr ⟨a⁻¹ * x, h⟩, Subtype.ext ?_⟩
      show a * (a⁻¹ * x) = x
      group
  have := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_sum] at this
  omega

end Arith

namespace D310USit

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
include hS

theorem mul_self_eq_one {a : MulAut W} (ha : a ∈ A) : a * a = 1 := by
  rw [← pow_two]
  exact hS.isA2.isElemAbelian2.2 a ha

theorem cent_fix {b : MulAut W} (hb : b ∈ A ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    {w : W} (hw : w ∈ orbSup T V) : b w = w :=
  (hS.fix_orbSup_iff hb.1).2 (fun l hl => ((Subgroup.mem_centralizer_iff.1 hb.2) l hl).symm)
    w hw

theorem cent_le_stabSub : A ⊓ Subgroup.centralizer (L : Set (MulAut W)) ≤ stabSub V := by
  intro b hb
  rw [mem_stabSub]
  intro u
  have hfix : ∀ v ∈ V, b v = v := fun v hv => hS.cent_fix hb (le_orbSup T V hv)
  constructor
  · intro hbu
    have h1 : b (b u) = b u := hfix _ hbu
    have h2 : b (b u) = u := by
      rw [← MulAut.mul_apply, hS.mul_self_eq_one hb.1, MulAut.one_apply]
    rw [← h2, h1]
    exact hbu
  · intro hu
    rw [hfix u hu]
    exact hu

theorem conj_mem_stabSub {a : MulAut W} (ha : a ∈ A) (haV : a ∈ stabSub V) :
    t⁻¹ * a * t ∈ stabSub V := by
  have ht2 : t * t ∈ stabSub V := by
    rcases hS.hsplit (t * t) (T.mul_mem hS.htT hS.htT) with h | h
    · exact h
    · exact absurd (by simpa using h) hS.htn
  rcases hS.hsplit (t⁻¹ * a * t)
      (T.mul_mem (T.mul_mem (T.inv_mem hS.htT) (hS.hAT ha)) hS.htT) with h | h
  · exact h
  · exfalso
    apply hS.htn
    have e : t = a⁻¹ * ((t * t) * (t⁻¹ * (t⁻¹ * a * t))) := by group
    rw [e]
    exact (stabSub V).mul_mem ((stabSub V).inv_mem haV) ((stabSub V).mul_mem ht2 h)

theorem split_of_not_mem {a₀ : MulAut W} (ha₀ : a₀ ∈ A) (ha₀V : a₀ ∉ stabSub V)
    {x : MulAut W} (hx : x ∈ A) : x ∈ stabSub V ∨ a₀⁻¹ * x ∈ stabSub V := by
  rcases hS.hsplit x (hS.hAT hx) with h | h
  · exact Or.inl h
  · right
    have h0 : t⁻¹ * a₀ ∈ stabSub V := (hS.hsplit a₀ (hS.hAT ha₀)).resolve_left ha₀V
    have e : a₀⁻¹ * x = (t⁻¹ * a₀)⁻¹ * (t⁻¹ * x) := by group
    rw [e]
    exact (stabSub V).mul_mem ((stabSub V).inv_mem h0) h

theorem smul_tilde_eq {g : ↥M} (hg : (g : MulAut W) ∈ stabSub V) :
    letI := qAct hS.hD.hyp.Mp_normal
    g • tilde L ⊤ V = tilde L ⊤ V := by
  let _i := qAct hS.hD.hyp.Mp_normal
  rw [smul_tildeQ hS.hD.hyp.Mp_normal g V]
  have h1 : (g : MulAut W) • V = V := mem_stabSub_iff_map_eq.1 hg
  rw [h1]

theorem smul_isoSum_self {g : ↥M} (hg : (g : MulAut W) ∈ stabSub V) :
    letI := qAct hS.hD.hyp.Mp_normal
    g • isoSum (L.subgroupOf M) (tilde L ⊤ V) = isoSum (L.subgroupOf M) (tilde L ⊤ V) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  refine smul_isoSum_eq hS.Λ_normal ?_
  rw [hS.smul_tilde_eq hg]
  exact XMod.Iso.refl _

theorem smul_t_self {g : ↥M} (hg : t⁻¹ * (g : MulAut W) * t ∈ stabSub V) :
    letI := qAct hS.hD.hyp.Mp_normal
    g • (⟨t, hS.t_mem⟩ : ↥M) • tilde L ⊤ V = (⟨t, hS.t_mem⟩ : ↥M) • tilde L ⊤ V ∧
      g • (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V) =
        (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  have hg' : ((tM⁻¹ * g * tM : ↥M) : MulAut W) ∈ stabSub V := hg
  have e : ∀ X : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)), g • tM • X =
      tM • (tM⁻¹ * g * tM) • X := by
    intro X
    rw [smul_smul, smul_smul]
    congr 1
    group
  refine ⟨?_, ?_⟩
  · rw [e, hS.smul_tilde_eq hg']
  · rw [e, hS.smul_isoSum_self hg']

theorem smul_isoSum_t {g : ↥M} (hg : t⁻¹ * (g : MulAut W) ∈ stabSub V) :
    letI := qAct hS.hD.hyp.Mp_normal
    g • isoSum (L.subgroupOf M) (tilde L ⊤ V) =
      (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  have hg' : ((tM⁻¹ * g : ↥M) : MulAut W) ∈ stabSub V := hg
  calc g • isoSum (L.subgroupOf M) (tilde L ⊤ V) =
      tM • (tM⁻¹ * g) • isoSum (L.subgroupOf M) (tilde L ⊤ V) := by
        rw [smul_smul, mul_inv_cancel_left]
    _ = tM • isoSum (L.subgroupOf M) (tilde L ⊤ V) := by rw [hS.smul_isoSum_self hg']

theorem exists_natural {n : ℕ} (hα : BinaryNaturalSL L V (V ⊓ fixV L) 3 n) :
    letI := qAct hS.hD.hyp.Mp_normal
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSL 3 K) →* ↥(actAut (L.subgroupOf M) (tilde L ⊤ V) hS.irr.1).range,
        (FFModel.nat (StatedSL 3 K)).RealizesVia
          (actAut (L.subgroupOf M) (tilde L ⊤ V) hS.irr.1).range ⊤ ⊥ π := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hLM : L ≤ M := hS.L_le
  obtain ⟨K, _, _, hK, π₀, hR⟩ := hα
  let ψ : ↥L →* ↥(L.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom
  have hψ : Function.Surjective ψ := (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective
  let f : ↥V →* ↥(tilde L ⊤ V) :=
    (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))).subgroupMap V
  have hf : Function.Surjective f :=
    (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))).subgroupMap_surjective V
  have hfker : ∀ u : ↥V, f u = 1 ↔ (u : W) ∈ V ⊓ fixV L := by
    intro u
    constructor
    · intro h1
      have h2 : (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1 :=
        congrArg Subtype.val h1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq] at h2
      exact ⟨u.2, h2⟩
    · intro h1
      apply Subtype.ext
      show (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq]
      exact h1.2
  exact ⟨K, inferInstance, inferInstance, hK, _,
    realizesVia_actAut hS.irr.1 hR ψ hψ f hf hfker (fun h u hu => rfl)⟩

theorem card_eqv_tilde_le {n : ℕ} (hα : BinaryNaturalSL L V (V ⊓ fixV L) 3 n) :
    letI := qAct hS.hD.hyp.Mp_normal
    Nat.card {θ : ↥(tilde L ⊤ V) →* ↥(tilde L ⊤ V) //
      IsEqv (L.subgroupOf M) ((tilde L ⊤ V).subtype.comp θ)} ≤ 2 ^ n := by
  let _i := qAct hS.hD.hyp.Mp_normal
  obtain ⟨K, _, _, hK, π, hπ⟩ := hS.exists_natural hα
  rw [← hK]
  exact card_eqv_le hπ

theorem tilde_le_fixed :
    letI := qAct hS.hD.hyp.Mp_normal
    tilde L ⊤ V ≤ XMod.fixed ↥((A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf M) ⊤ ∧
      (⟨t, hS.t_mem⟩ : ↥M) • tilde L ⊤ V ≤
        XMod.fixed ↥((A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf M) ⊤ := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have key : ∀ w ∈ orbSup T V,
      (QuotientGroup.mk w : W ⧸ modFix L (⊤ : Subgroup W)) ∈
        XMod.fixed ↥((A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf M) ⊤ := by
    intro w hw
    refine XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩
    show (QuotientGroup.mk (((b : ↥M) : MulAut W) w) : W ⧸ modFix L (⊤ : Subgroup W)) = _
    have hb : ((b : ↥M) : MulAut W) ∈ A ⊓ Subgroup.centralizer (L : Set (MulAut W)) := b.2
    exact congrArg _ (hS.cent_fix hb hw)
  constructor
  · rintro _ ⟨v, hv, rfl⟩
    exact key v (le_orbSup T V hv)
  · intro q hq
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
    obtain ⟨v, hv, hvq⟩ := mem_tilde_iff.1 hq
    have hq' : q = (QuotientGroup.mk (t v) : W ⧸ modFix L (⊤ : Subgroup W)) := by
      have h1 : (⟨t, hS.t_mem⟩ : ↥M) • (QuotientGroup.mk v : W ⧸ modFix L (⊤ : Subgroup W)) =
          (⟨t, hS.t_mem⟩ : ↥M) • (⟨t, hS.t_mem⟩ : ↥M)⁻¹ • q := by rw [hvq]
      rw [smul_inv_smul] at h1
      rw [← h1]
      rfl
    rw [hq']
    exact key _ (map_le_orbSup hS.htT ⟨v, hv, rfl⟩)

theorem eq_one_of_fix_isoSum {x : ↥M}
    (hx : x ∈ (A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf M)
    (h₁ : letI := qAct hS.hD.hyp.Mp_normal
      ∀ q ∈ isoSum (L.subgroupOf M) (tilde L ⊤ V), x • q = q)
    (h₂ : letI := qAct hS.hD.hyp.Mp_normal
      ∀ q ∈ (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V), x • q = q) :
    x = 1 := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hle : isoSum (L.subgroupOf M) (tilde L ⊤ V) ⊔
      (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V) ≤
        XMod.fixed ↥(Subgroup.zpowers x) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) :=
    sup_le (fun q hq => mem_fixed_zpowers_iff.2 (h₁ q hq))
      (fun q hq => mem_fixed_zpowers_iff.2 (h₂ q hq))
  rw [hS.sup_isoSum] at hle
  have hxA : ((x : ↥M) : MulAut W) ∈ A ⊓ Subgroup.centralizer (L : Set (MulAut W)) := hx
  have h1 := hS.faithful x.2 (fun l hl => ((Subgroup.mem_centralizer_iff.1 hxA.2) l hl).symm)
    (fun q => mem_fixed_zpowers_iff.1 (hle trivial))
  exact Subtype.ext h1

theorem smul_mem_fixed_cent {a : ↥M} (ha : a ∈ A.subgroupOf M)
    {q : W ⧸ modFix L (⊤ : Subgroup W)}
    (hq : letI := qAct hS.hD.hyp.Mp_normal
      q ∈ XMod.fixed ↥((A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf M) ⊤) :
    letI := qAct hS.hD.hyp.Mp_normal
    a • q ∈ XMod.fixed ↥((A ⊓ Subgroup.centralizer (L : Set (MulAut W))).subgroupOf M) ⊤ := by
  let _i := qAct hS.hD.hyp.Mp_normal
  refine XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩
  have hbB : ((b : ↥M) : MulAut W) ∈ A ⊓ Subgroup.centralizer (L : Set (MulAut W)) := b.2
  have hbA : ((b : ↥M) : MulAut W) ∈ A := hbB.1
  have hab : (b : ↥M) * a = a * b :=
    Subtype.ext (hS.isA2.isElemAbelian2.1 _ hbA _ (show ((a : ↥M) : MulAut W) ∈ A from ha))
  show (b : ↥M) • a • q = a • q
  rw [smul_smul, hab, mul_smul]
  exact congrArg _ ((XMod.mem_fixed.1 hq).2 b)

theorem false_of_le_stabSub {n : ℕ} (hn : Odd n) (hα : BinaryNaturalSL L V (V ⊓ fixV L) 3 n)
    (hAB : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W))) (hAV : A ≤ stabSub V) : False := by
  classical
  let _i := qAct hS.hD.hyp.Mp_normal
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  set B := A ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hBdef
  have hQ := hS.quot_sq
  have hΛn := hS.Λ_normal
  have hirr := hS.irr
  have hN := normalizes_whole (Q := W ⧸ modFix L (⊤ : Subgroup W)) (L.subgroupOf M) hΛn
  have hirrt : XMod.IsIrr ↥(L.subgroupOf M) (tM • tilde L ⊤ V) := isIrr_smul hN tM hirr
  have hn1 : 1 ≤ n := hn.pos
  have hAt : ∀ a ∈ A, t⁻¹ * a * t ∈ stabSub V := fun a ha => hS.conj_mem_stabSub ha (hAV ha)
  obtain ⟨K, _, _, S, hK, hVK, hS2, hSc, hcardA, hfix1, hfix2, hne⟩ :=
    exists_matrices hS.hD hS.hlt hS.hC hn hα hS.htT hS.t_mem hS.htn hS.A_le hAV hAt
      (fun a ha => hS.mul_self_eq_one ha)
  have h2K : (2 : K) = 0 := two_eq_zero_of_card hK
  obtain ⟨g₀, hg₀S, hg₀1⟩ := hne hAB
  have hApg : IsPGroup 2 ↥A := hS.isA2.isElemAbelian2.isPGroup
  have hBpg : IsPGroup 2 ↥B := hS.isPGroup_cent
  have hcA : Nat.card ↥A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hApg
  have hcB : Nat.card ↥B = 2 ^ rk ↥B := card_eq_two_pow_of_isPGroup hBpg
  have hrkV : rk ↥(tilde L ⊤ V) = 3 * n := by
    have h1 := card_eq_two_pow hQ (tilde L ⊤ V)
    rw [hVK, hK, ← pow_mul] at h1
    have := Nat.pow_right_injective le_rfl h1
    omega
  set f₁ := rk ↥(tilde L ⊤ V ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤) with hf₁def
  set f₂ := rk ↥(tM • tilde L ⊤ V ⊓ XMod.fixed ↥(A.subgroupOf M) ⊤) with hf₂def
  have hcf₁ : Nat.card (fixVec S) = 2 ^ f₁ := by rw [← hfix1, card_eq_two_pow hQ]
  have hcf₂ : Nat.card (fixVecT S) = 2 ^ f₂ := by rw [← hfix2, card_eq_two_pow hQ]
  have hS1 : rk ↥A ≤ rk ↥B + 2 * n := by
    have h1 := card_le_sq h2K hS2 hSc
    have h2 : 2 ^ rk ↥A ≤ 2 ^ (rk ↥B + 2 * n) := by
      calc 2 ^ rk ↥A = Nat.card ↥A := hcA.symm
        _ ≤ Nat.card ↥B * Nat.card S := hcardA
        _ ≤ Nat.card ↥B * Nat.card K ^ 2 := Nat.mul_le_mul_left _ h1
        _ = 2 ^ (rk ↥B + 2 * n) := by rw [hcB, hK, ← pow_mul, ← pow_add, mul_comm n 2]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hS2' : n + rk ↥A + f₁ + f₂ ≤ rk ↥B + 6 * n := by
    have h1 := card_mul_le h2K hS2 hSc hg₀S hg₀1
    rw [hcf₁, hcf₂, hK, ← pow_mul] at h1
    have h2 : 2 ^ (n + rk ↥A + f₁ + f₂) ≤ 2 ^ (rk ↥B + 6 * n) := by
      rw [pow_add, pow_add, pow_add, pow_add, ← hcA, ← hcB]
      calc 2 ^ n * Nat.card ↥A * 2 ^ f₁ * 2 ^ f₂ ≤
          2 ^ n * (Nat.card ↥B * Nat.card S) * 2 ^ f₁ * 2 ^ f₂ := by gcongr
        _ = Nat.card ↥B * (2 ^ n * Nat.card S * 2 ^ f₁ * 2 ^ f₂) := by ring
        _ ≤ Nat.card ↥B * 2 ^ (n * 6) := Nat.mul_le_mul_left _ h1
        _ = Nat.card ↥B * 2 ^ (6 * n) := by rw [mul_comm n 6]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hf₁n : f₁ + n ≤ 3 * n := by
    have h1 := card_fixVec_mul_le hg₀S hg₀1
    rw [hcf₁, hK, ← pow_mul, ← pow_add] at h1
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    omega
  have hf₂n : f₂ + n ≤ 3 * n := by
    have h1 := card_fixVecT_mul_le hg₀S hg₀1
    rw [hcf₂, hK, ← pow_mul, ← pow_add] at h1
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    omega
  set Q₁ := isoSum (L.subgroupOf M) (tilde L ⊤ V) with hQ₁def
  have hQ₁A : ∀ a ∈ A.subgroupOf M, ∀ q ∈ Q₁, a • q ∈ Q₁ := by
    intro a ha q hq
    have h : a • Q₁ = Q₁ := hS.smul_isoSum_self (hAV ha)
    rw [← h]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  have hQ₂A : ∀ a ∈ A.subgroupOf M, ∀ q ∈ tM • Q₁, a • q ∈ tM • Q₁ := by
    intro a ha q hq
    have h : a • tM • Q₁ = tM • Q₁ := (hS.smul_t_self (hAt _ ha)).2
    rw [← h]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  have hBA : B.subgroupOf M ≤ A.subgroupOf M := fun x hx => (hx : ((x : ↥M) : MulAut W) ∈ B).1
  set F := XMod.fixed ↥(B.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)))
    with hFdef
  have hsplitF : F = (Q₁ ⊓ F) ⊔ (tM • Q₁ ⊓ F) :=
    fixed_eq_sup_of_inf_eq_bot (fun b hb => hQ₁A b (hBA hb)) (fun b hb => hQ₂A b (hBA hb))
      hS.inf_isoSum hS.sup_isoSum
  have hY12 : (Q₁ ⊓ F) ⊓ (tM • Q₁ ⊓ F) = ⊥ :=
    le_bot_iff.1 (le_trans (inf_le_inf inf_le_left inf_le_left) hS.inf_isoSum.le)
  have hFA : ∀ a ∈ A.subgroupOf M, ∀ q ∈ F, a • q ∈ F := fun a ha q hq =>
    hS.smul_mem_fixed_cent ha hq
  have hY₁A : ∀ a ∈ A.subgroupOf M, ∀ q ∈ Q₁ ⊓ F, a • q ∈ Q₁ ⊓ F := fun a ha q hq =>
    ⟨hQ₁A a ha q hq.1, hFA a ha q hq.2⟩
  have hY₂A : ∀ a ∈ A.subgroupOf M, ∀ q ∈ tM • Q₁ ⊓ F, a • q ∈ tM • Q₁ ⊓ F :=
    fun a ha q hq => ⟨hQ₂A a ha q hq.1, hFA a ha q hq.2⟩
  have hΛB : ∀ l ∈ L.subgroupOf M, ∀ b ∈ B.subgroupOf M, l * b = b * l := by
    intro l hl b hb
    have hb' : ((b : ↥M) : MulAut W) ∈ B := hb
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hb'.2) _ hl)
  have hQ₁Λ : XMod.IsInv ↥(L.subgroupOf M) Q₁ := isInv_isoSum hΛn hirr.1
  have hQ₂Λ : XMod.IsInv ↥(L.subgroupOf M) (tM • Q₁) :=
    XMod.isInv_smul_of_normalizes hN tM hQ₁Λ
  have hY₁Λ : XMod.IsInv ↥(L.subgroupOf M) (Q₁ ⊓ F) := isInv_inf_fixed hΛB hQ₁Λ
  have hY₂Λ : XMod.IsInv ↥(L.subgroupOf M) (tM • Q₁ ⊓ F) := isInv_inf_fixed hΛB hQ₂Λ
  have hAMpg : IsPGroup 2 ↥(A.subgroupOf M) := A4.isPGroup_subgroupOf_of_le hS.A_le hApg
  have hAVt : ∀ a ∈ A.subgroupOf M, a • tilde L ⊤ V = tilde L ⊤ V := fun a ha =>
    hS.smul_tilde_eq (hAV ha)
  have hAtVt : ∀ a ∈ A.subgroupOf M, a • tM • tilde L ⊤ V = tM • tilde L ⊤ V := fun a ha =>
    (hS.smul_t_self (hAt _ ha)).1
  have hQ₁I : Q₁ ≤ isoComp ↥(L.subgroupOf M) (tilde L ⊤ V) := isoSum_le_isoComp hΛn hirr
  have hQ₂I : tM • Q₁ ≤ isoComp ↥(L.subgroupOf M) (tM • tilde L ⊤ V) :=
    smul_isoSum_le_isoComp hΛn hirr tM
  obtain ⟨c, hc₁, hcn⟩ :=
    count_of_le_isoComp hQ hΛn hirr hAMpg hAVt hY₁Λ hY₁A (inf_le_left.trans hQ₁I)
  obtain ⟨c', hc₂, hcn'⟩ :=
    count_of_le_isoComp hQ hΛn hirrt hAMpg hAtVt hY₂Λ hY₂A (inf_le_left.trans hQ₂I)
  have hc₂v : rk ↥(tM • Q₁ ⊓ F) = c' * rk ↥(tilde L ⊤ V) := by rw [hc₂, rk_smul]
  obtain ⟨hVF, htVF⟩ := hS.tilde_le_fixed
  have hc1 : 1 ≤ c := by
    have h1 : rk ↥(tilde L ⊤ V) ≤ rk ↥(Q₁ ⊓ F) := rk_mono (le_inf self_le_isoSum hVF)
    rw [hc₁, hrkV] at h1
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at h1
      omega
    · exact h
  have hc1' : 1 ≤ c' := by
    have h1 : rk ↥(tM • tilde L ⊤ V) ≤ rk ↥(tM • Q₁ ⊓ F) :=
      rk_mono (le_inf ((Subgroup.pointwise_smul_le_pointwise_smul_iff (a := tM)).2
        self_le_isoSum) htVF)
    rw [hc₂v, hrkV, rk_smul, hrkV] at h1
    rcases Nat.eq_zero_or_pos c' with h | h
    · rw [h, zero_mul] at h1
      omega
    · exact h
  have hck : c ≤ k := by
    have h1 : rk ↥(Q₁ ⊓ F) ≤ rk ↥Q₁ := rk_mono inf_le_left
    rw [hc₁, hS.hk, hrkV] at h1
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  have hc'k : c' ≤ k := by
    have h1 : rk ↥(tM • Q₁ ⊓ F) ≤ rk ↥(tM • Q₁) := rk_mono inf_le_left
    rw [hc₂v, rk_smul, hS.hk, hrkV] at h1
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  have hν : nB (A.subgroupOf M) (tilde L ⊤ V) = 3 * n - f₁ := by
    unfold nB
    rw [hrkV]
  have hν' : nB (A.subgroupOf M) (tM • tilde L ⊤ V) = 3 * n - f₂ := by
    unfold nB
    rw [rk_smul, hrkV]
  have hUA : ¬ fixV B ≤ fixV A := by
    intro hle
    obtain ⟨a, ha, hac⟩ := IsConcreteLE.not_le_iff_exists.mp hAB
    apply hac
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((hS.fix_orbSup_iff ha).1
      (fun w hw => hle (fun b hb => hS.cent_fix hb hw) a ha) l hl).symm
  have hD7 : nB (A.subgroupOf M) F < 2 * (rk ↥A - rk ↥B) :=
    nB_fixed_lt hS.hD.hyp.Mp_normal hS.exp hS.hAQ inf_le_left hS.hB hUA
      (inf_le_left.trans hS.A_le)
      (fun b hb x hx => ((Subgroup.mem_centralizer_iff.1 hb.2) x hx).symm)
      (commOf_eq_of_d3Std hS.hD)
  have hNC : nB (A.subgroupOf M) F =
      nB (A.subgroupOf M) (Q₁ ⊓ F) + nB (A.subgroupOf M) (tM • Q₁ ⊓ F) := by
    conv_lhs => rw [hsplitF]
    exact nB_sup_of_inf_eq_bot _ hY₁A hY₂A hY12
  have hadd : nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) =
      nB (B.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) +
        nB (A.subgroupOf M) F := by
    have h := nB_eq_add_of_le hBA (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)))
    rwa [top_inf_eq] at h
  have hrkF : rk ↥F = (c + c') * (3 * n) := by
    have h1 := rk_sup_add_rk_inf (Q₁ ⊓ F) (tM • Q₁ ⊓ F)
    rw [← hsplitF, hY12, rk_bot, add_zero, hc₁, hc₂v, hrkV] at h1
    rw [h1]
    ring
  have hNB : nB (B.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) +
      (c + c') * (3 * n) = 2 * k * (3 * n) := by
    have h1 : nB (B.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) =
        rk ↥(⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) - rk ↥F := by
      unfold nB
      rw [top_inf_eq]
    have h2 := rk_mono (le_top : F ≤ ⊤)
    rw [hS.rk_top, hrkV] at h1 h2
    rw [hrkF] at h1 h2
    omega
  have hN2 : nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≤ 2 * rk ↥A :=
    (hS.nB_le_rkIdx hS.A_le).trans hS.rkIdx_le
  have hBc : ∀ a ∈ B.subgroupOf M, ∀ b ∈ B.subgroupOf M, a * b = b * a := by
    intro a ha b hb
    have ha' : ((a : ↥M) : MulAut W) ∈ B := ha
    have hb' : ((b : ↥M) : MulAut W) ∈ B := hb
    exact Subtype.ext (hS.isA2.isElemAbelian2.1 _ ha'.1 _ hb'.1)
  have hB2 : ∀ b ∈ B.subgroupOf M, b ^ 2 = 1 := by
    intro b hb
    have hb' : ((b : ↥M) : MulAut W) ∈ B := hb
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hS.isA2.isElemAbelian2.2 _ hb'.1
  have hY₁iso : IsotypicOfLength ↥(L.subgroupOf M) Q₁ (tilde L ⊤ V) k := ⟨hQ₁Λ, hQ₁I, hS.hk⟩
  have hY₂iso : IsotypicOfLength ↥(L.subgroupOf M) (tM • Q₁) (tM • tilde L ⊤ V) k :=
    ⟨hQ₂Λ, hQ₂I, by rw [rk_smul, rk_smul]; exact hS.hk⟩
  have he₁ := hS.card_eqv_tilde_le hα
  have he₂ := (card_eqv_smul_le hΛn tM (tilde L ⊤ V)).trans he₁
  have hcL := rk_le_of_socle_two hQ hΛB hBc hB2 hirr hirrt hY₁iso hY₂iso
    (fun b hb => hQ₁A b (hBA hb)) (fun b hb => hQ₂A b (hBA hb)) hc₁ hc₂ he₁ he₂
  have hrest : B.subgroupOf M ⊓ fixingSubgroup ↥M (Q₁ : Set (W ⧸ modFix L (⊤ : Subgroup W))) ⊓
      fixingSubgroup ↥M ((tM • Q₁ : Subgroup _) : Set (W ⧸ modFix L (⊤ : Subgroup W))) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxB, hx₁⟩, hx₂⟩
    rw [Subgroup.mem_bot]
    exact hS.eq_one_of_fix_isoSum hxB (fun q hq => (mem_fixingSubgroup_iff _).1 hx₁ q hq)
      (fun q hq => (mem_fixingSubgroup_iff _).1 hx₂ q hq)
  rw [hrest, rk_bot, add_zero] at hcL
  have hrkBM : rk ↥(B.subgroupOf M) = rk ↥B := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hS.A_le)).toEquiv]
  rw [hrkBM] at hcL
  have hBAr : rk ↥B ≤ rk ↥A := rk_mono inf_le_left
  refine arith_nonswap hn1 hS.hk2 hc1 hc1' hck hc'k hf₁n hf₂n hBAr hS1 hS2' ?_ hD7 ?_ hN2 hcL
  · rw [hNC]
    rw [hν] at hcn
    rw [hν'] at hcn'
    omega
  · rw [hadd]
    have h1 : (2 * k - (c + c')) * (3 * n) = 2 * k * (3 * n) - (c + c') * (3 * n) :=
      Nat.sub_mul _ _ _
    omega

theorem false_of_not_le_stabSub {n : ℕ} (hn : Odd n)
    (hα : BinaryNaturalSL L V (V ⊓ fixV L) 3 n) {a₀ : MulAut W} (ha₀ : a₀ ∈ A)
    (ha₀V : a₀ ∉ stabSub V) : False := by
  classical
  let _i := qAct hS.hD.hyp.Mp_normal
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  set B := A ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hBdef
  set A₀ := A ⊓ stabSub V with hA₀def
  have hQ := hS.quot_sq
  have hΛn := hS.Λ_normal
  have hirr := hS.irr
  have hn1 : 1 ≤ n := hn.pos
  have hBA₀ : B ≤ A₀ := le_inf inf_le_left hS.cent_le_stabSub
  have hA₀t : ∀ a ∈ A₀, t⁻¹ * a * t ∈ stabSub V := fun a ha => hS.conj_mem_stabSub ha.1 ha.2
  obtain ⟨K, _, _, S, hK, hVK, hS2, hSc, hcardA₀, -, -, -⟩ :=
    exists_matrices hS.hD hS.hlt hS.hC hn hα hS.htT hS.t_mem hS.htn
      (inf_le_left.trans hS.A_le) inf_le_right hA₀t (fun a ha => hS.mul_self_eq_one ha.1)
  have h2K : (2 : K) = 0 := two_eq_zero_of_card hK
  have hApg : IsPGroup 2 ↥A := hS.isA2.isElemAbelian2.isPGroup
  have hBpg : IsPGroup 2 ↥B := hS.isPGroup_cent
  have hA₀pg : IsPGroup 2 ↥A₀ := hApg.to_le inf_le_left
  have hcA : Nat.card ↥A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hApg
  have hcA₀ : Nat.card ↥A₀ = 2 ^ rk ↥A₀ := card_eq_two_pow_of_isPGroup hA₀pg
  have hcB : Nat.card ↥B = 2 ^ rk ↥B := card_eq_two_pow_of_isPGroup hBpg
  have hrkV : rk ↥(tilde L ⊤ V) = 3 * n := by
    have h1 := card_eq_two_pow hQ (tilde L ⊤ V)
    rw [hVK, hK, ← pow_mul] at h1
    have := Nat.pow_right_injective le_rfl h1
    omega
  have hS1 : rk ↥A₀ ≤ rk ↥B + 2 * n := by
    have h1 := card_le_sq h2K hS2 hSc
    have h0 : Nat.card ↥(A₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))) ≤ Nat.card ↥B :=
      Subgroup.card_le_of_le (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    have h2 : 2 ^ rk ↥A₀ ≤ 2 ^ (rk ↥B + 2 * n) := by
      calc 2 ^ rk ↥A₀ = Nat.card ↥A₀ := hcA₀.symm
        _ ≤ Nat.card ↥(A₀ ⊓ Subgroup.centralizer (L : Set (MulAut W))) * Nat.card S := hcardA₀
        _ ≤ Nat.card ↥B * Nat.card K ^ 2 := Nat.mul_le_mul h0 h1
        _ = 2 ^ (rk ↥B + 2 * n) := by rw [hcB, hK, ← pow_mul, ← pow_add, mul_comm n 2]
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have hsplitA : ∀ x ∈ A, x ∈ A₀ ∨ a₀⁻¹ * x ∈ A₀ := by
    intro x hx
    rcases hS.split_of_not_mem ha₀ ha₀V hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨A.mul_mem (A.inv_mem ha₀) hx, h⟩
  have hA0 : rk ↥A ≤ rk ↥A₀ + 1 := by
    have h1 := card_le_two_mul_of_split inf_le_left ha₀ hsplitA
    rw [hcA, hcA₀, ← pow_succ'] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  set a₀M : ↥M := ⟨a₀, hS.A_le ha₀⟩ with ha₀Mdef
  set Q₁ := isoSum (L.subgroupOf M) (tilde L ⊤ V) with hQ₁def
  have hta₀ : t⁻¹ * a₀ ∈ stabSub V := (hS.hsplit a₀ (hS.hAT ha₀)).resolve_left ha₀V
  have ha₀Q : a₀M • Q₁ = tM • Q₁ := hS.smul_isoSum_t hta₀
  have hsup : Q₁ ⊔ a₀M • Q₁ = ⊤ := by rw [ha₀Q]; exact hS.sup_isoSum
  have hinf : Q₁ ⊓ a₀M • Q₁ = ⊥ := by rw [ha₀Q]; exact hS.inf_isoSum
  have hBA₀M : B.subgroupOf M ≤ A₀.subgroupOf M := fun x hx => hBA₀ hx
  have hA₀A : A₀.subgroupOf M ≤ A.subgroupOf M := fun x hx =>
    (hx : ((x : ↥M) : MulAut W) ∈ A₀).1
  have hAc : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hS.isA2.isElemAbelian2.1 _ hx _ hy)
  have ha₀2 : a₀M ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hS.isA2.isElemAbelian2.2 _ ha₀
  have hsplitM : ∀ x ∈ A.subgroupOf M, x ∈ A₀.subgroupOf M ∨ a₀M⁻¹ * x ∈ A₀.subgroupOf M :=
    fun x hx => hsplitA _ hx
  have hQ₁A₀ : ∀ a ∈ A₀.subgroupOf M, ∀ q ∈ Q₁, a • q ∈ Q₁ := by
    intro a ha q hq
    have ha' : ((a : ↥M) : MulAut W) ∈ A₀ := ha
    have h : a • Q₁ = Q₁ := hS.smul_isoSum_self ha'.2
    rw [← h]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  have hQ₂A₀ : ∀ a ∈ A₀.subgroupOf M, ∀ q ∈ tM • Q₁, a • q ∈ tM • Q₁ := by
    intro a ha q hq
    have ha' : ((a : ↥M) : MulAut W) ∈ A₀ := ha
    have h : a • tM • Q₁ = tM • Q₁ := (hS.smul_t_self (hA₀t _ ha')).2
    rw [← h]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  set F := XMod.fixed ↥(B.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)))
    with hFdef
  have hFA : ∀ a ∈ A.subgroupOf M, ∀ q ∈ F, a • q ∈ F := fun a ha q hq =>
    hS.smul_mem_fixed_cent ha hq
  have ha₀F : a₀M • F = F := by
    ext q
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro h
      have h1 := hFA a₀M ha₀ _ h
      rwa [smul_inv_smul] at h1
    · intro h
      exact hFA _ ((A.subgroupOf M).inv_mem ha₀) q h
  have hsplitF : F = (Q₁ ⊓ F) ⊔ a₀M • (Q₁ ⊓ F) := by
    have h := fixed_eq_sup_of_inf_eq_bot (B := B.subgroupOf M) (S₁ := Q₁) (S₂ := a₀M • Q₁)
      (fun b hb => hQ₁A₀ b (hBA₀M hb))
      (fun b hb q hq => by rw [ha₀Q] at hq ⊢; exact hQ₂A₀ b (hBA₀M hb) q hq) hinf hsup
    rw [Subgroup.smul_inf, ha₀F]
    exact h
  have hY₁A₀ : XMod.IsInv ↥(A₀.subgroupOf M) (Q₁ ⊓ F) := fun a q hq =>
    ⟨hQ₁A₀ a a.2 q hq.1, hFA a (hA₀A a.2) q hq.2⟩
  have hY₁dis : (Q₁ ⊓ F) ⊓ a₀M • (Q₁ ⊓ F) = ⊥ := by
    rw [Subgroup.smul_inf, ha₀F]
    exact le_bot_iff.1 (le_trans (inf_le_inf inf_le_left inf_le_left) hinf.le)
  have hQ₁A₀i : XMod.IsInv ↥(A₀.subgroupOf M) Q₁ := fun a q hq => hQ₁A₀ a a.2 q hq
  have ha₀A : a₀M ∈ A.subgroupOf M := ha₀
  have hN1 := nB_index_two ha₀A ha₀2 hAc hA₀A hsplitM hQ₁A₀i hinf
  rw [hsup] at hN1
  have hN3 := nB_index_two ha₀A ha₀2 hAc hA₀A hsplitM hY₁A₀ hY₁dis
  rw [← hsplitF] at hN3
  have hΛB : ∀ l ∈ L.subgroupOf M, ∀ b ∈ B.subgroupOf M, l * b = b * l := by
    intro l hl b hb
    have hb' : ((b : ↥M) : MulAut W) ∈ B := hb
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hb'.2) _ hl)
  have hQ₁Λ : XMod.IsInv ↥(L.subgroupOf M) Q₁ := isInv_isoSum hΛn hirr.1
  have hY₁iso : IsotypicOfLength ↥(L.subgroupOf M) Q₁ (tilde L ⊤ V) k :=
    ⟨hQ₁Λ, isoSum_le_isoComp hΛn hirr, hS.hk⟩
  obtain ⟨c, hck, hc₁⟩ := exists_rk_inf_fixed_eq_mul hQ hΛB hirr hY₁iso
  obtain ⟨hVF, -⟩ := hS.tilde_le_fixed
  have hc1 : 1 ≤ c := by
    have h1 : rk ↥(tilde L ⊤ V) ≤ rk ↥(Q₁ ⊓ F) := rk_mono (le_inf self_le_isoSum hVF)
    rw [hc₁, hrkV] at h1
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at h1
      omega
    · exact h
  have ha₀L : a₀ ∉ Subgroup.centralizer (L : Set (MulAut W)) := fun h =>
    ha₀V (hS.cent_le_stabSub ⟨ha₀, h⟩)
  have hUA : ¬ fixV B ≤ fixV A := by
    intro hle
    apply ha₀L
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((hS.fix_orbSup_iff ha₀).1
      (fun w hw => hle (fun b hb => hS.cent_fix hb hw) a₀ ha₀) l hl).symm
  have hD7 : nB (A.subgroupOf M) F < 2 * (rk ↥A - rk ↥B) :=
    nB_fixed_lt hS.hD.hyp.Mp_normal hS.exp hS.hAQ inf_le_left hS.hB hUA
      (inf_le_left.trans hS.A_le)
      (fun b hb x hx => ((Subgroup.mem_centralizer_iff.1 hb.2) x hx).symm)
      (commOf_eq_of_d3Std hS.hD)
  have hBc : ∀ a ∈ B.subgroupOf M, ∀ b ∈ B.subgroupOf M, a * b = b * a := by
    intro a ha b hb
    have ha' : ((a : ↥M) : MulAut W) ∈ B := ha
    have hb' : ((b : ↥M) : MulAut W) ∈ B := hb
    exact Subtype.ext (hS.isA2.isElemAbelian2.1 _ ha'.1 _ hb'.1)
  have hB2 : ∀ b ∈ B.subgroupOf M, b ^ 2 = 1 := by
    intro b hb
    have hb' : ((b : ↥M) : MulAut W) ∈ B := hb
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact hS.isA2.isElemAbelian2.2 _ hb'.1
  have he₁ := hS.card_eqv_tilde_le hα
  have hcL := rk_le_of_socle hQ hΛB hBc hB2 hirr hY₁iso (fun b hb => hQ₁A₀ b (hBA₀M hb)) hc₁ he₁
  have hrest : B.subgroupOf M ⊓
      fixingSubgroup ↥M (Q₁ : Set (W ⧸ modFix L (⊤ : Subgroup W))) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hx₁⟩
    rw [Subgroup.mem_bot]
    refine hS.eq_one_of_fix_isoSum hxB (fun q hq => (mem_fixingSubgroup_iff _).1 hx₁ q hq) ?_
    intro q hq
    rw [← ha₀Q] at hq
    obtain ⟨q', hq', rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hq
    have hxB' : ((x : ↥M) : MulAut W) ∈ B := hxB
    have hxa : x * a₀M = a₀M * x := Subtype.ext (hS.isA2.isElemAbelian2.1 _ hxB'.1 _ ha₀)
    rw [smul_smul, hxa, mul_smul, (mem_fixingSubgroup_iff _).1 hx₁ q' hq']
  have hrkBM : rk ↥(B.subgroupOf M) = rk ↥B := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hS.A_le)).toEquiv]
  rw [hrest, rk_bot, add_zero, hrkBM] at hcL
  have hN2 : nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) ≤ 2 * rk ↥A :=
    (hS.nB_le_rkIdx hS.A_le).trans hS.rkIdx_le
  have hBAr : rk ↥B ≤ rk ↥A := rk_mono inf_le_left
  have hle1 := nB_le_of_le hBA₀M Q₁
  have hNBQ : nB (B.subgroupOf M) Q₁ = rk ↥Q₁ - rk ↥(Q₁ ⊓ F) := rfl
  have hrkQ₁ : rk ↥Q₁ = k * (3 * n) := by rw [hS.hk, hrkV]
  refine arith_swap hn1 hS.hk2 hc1 hck hBAr hA0 hS1 ?_ ?_ hN2 hcL
  · rw [hc₁, hrkV] at hN3
    omega
  · rw [hc₁, hrkV, hrkQ₁] at hNBQ
    rw [hrkQ₁] at hN1
    omega

end D310USit

theorem caseII_false {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)}
    {V : Subgroup W} {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ}
    (hS : D310USit M T L V t A r k) {n : ℕ} (hn : Odd n)
    (hα : BinaryNaturalSL L V (V ⊓ fixV L) 3 n)
    (hAB : ¬ A ≤ Subgroup.centralizer (L : Set (MulAut W))) : False := by
  by_cases hAV : A ≤ stabSub V
  · exact hS.false_of_le_stabSub hn hα hAB hAV
  · obtain ⟨a₀, ha₀, ha₀V⟩ := IsConcreteLE.not_le_iff_exists.mp hAV
    exact hS.false_of_not_le_stabSub hn hα ha₀ ha₀V

end CFSG.Quasithin.SmithD310U
