module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KMaschke
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)

section Gen

variable {X : Type} [Group X]

theorem stable_of_closure_pair {Ē : Subgroup (MulAut X)} (hE3 : ∀ x ∈ Ē, x ^ 3 = 1)
    {σ τ : MulAut X} (hgen : Subgroup.closure ({σ, τ} : Set (MulAut X)) = Ē) {W : Subgroup X}
    (hσW : ∀ w ∈ W, σ w ∈ W) (hτW : ∀ w ∈ W, τ w ∈ W) : ∀ ρ ∈ Ē, ∀ w ∈ W, ρ w ∈ W := by
  intro ρ hρ
  rw [← hgen] at hρ
  induction hρ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hσW
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hτW
  | one => intro w hw; simpa using hw
  | mul x y hx' hy' hx hy =>
    intro w hw
    have := hx _ (hy w hw)
    simpa [MulAut.mul_apply] using this
  | inv x hx' hx =>
    intro w hw
    have hxE : x ∈ Ē := by rw [← hgen]; exact hx'
    have hx3 : x ^ 3 = 1 := hE3 x hxE
    have hxinv : x⁻¹ = x * x := by
      apply inv_eq_of_mul_eq_one_right
      calc x * (x * x) = x * x * x := (mul_assoc _ _ _).symm
        _ = x ^ 3 := by simp [pow_succ]
        _ = 1 := hx3
    rw [hxinv]
    have := hx _ (hx w hw)
    simpa [MulAut.mul_apply] using this

theorem exists_not_mem_zpowers {Ē : Subgroup (MulAut X)} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9) {σ : MulAut X} (hσE : σ ∈ Ē) (hσ1 : σ ≠ 1) :
    ∃ τ ∈ Ē, τ ∉ Subgroup.zpowers σ := by
  by_contra hcon
  push Not at hcon
  have hle : Ē ≤ Subgroup.zpowers σ := fun x hx => hcon x hx
  have hσ3 : σ ^ 3 = 1 := hE3.2 σ hσE
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hzcard : Nat.card (Subgroup.zpowers σ) = 3 := by rw [Nat.card_zpowers, hord]
  have hfin : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by omega)
  have := Subgroup.card_le_of_le hle
  omega

theorem eInvFour_of_two_gens {Ē : Subgroup (MulAut X)} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9) {σ τ : MulAut X} (hσ : σ ∈ Ē) (hτ : τ ∈ Ē) (hσ1 : σ ≠ 1)
    (hτσ : τ ∉ Subgroup.zpowers σ) {W : Subgroup X} (hW : IsElemAbelian 2 W)
    (hW4 : Nat.card W = 4) (hσW : ∀ w ∈ W, σ w ∈ W) (hτW : ∀ w ∈ W, τ w ∈ W)
    (hmove : (∃ w ∈ W, σ w ≠ w) ∨ ∃ w ∈ W, τ w ≠ w) : EInvFour X Ē := by
  have hgen := closure_pair_eq_of_card_nine hE3 hE9 hσ hτ hσ1 hτσ
  refine ⟨W, hW, hW4, stable_of_closure_pair hE3.2 hgen hσW hτW, ?_⟩
  rcases hmove with ⟨w, hw, h⟩ | ⟨w, hw, h⟩
  · exact ⟨σ, hσ, w, hw, h⟩
  · exact ⟨τ, hτ, w, hw, h⟩

theorem eInvFour_of_map_conj {Ē : Subgroup (MulAut X)} (τ : MulAut X)
    (h : EInvFour X (Ē.map (MulAut.conj τ).toMonoidHom)) : EInvFour X Ē := by
  obtain ⟨W', hW'ab, hW'4, hW'inv, ρ', hρ', w', hw', hmove⟩ := h
  refine ⟨W'.map τ⁻¹.toMonoidHom, CFSG.Open.IsElemAbelian.map hW'ab _, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective τ⁻¹.injective, hW'4]
  · rintro ρ hρ _ ⟨w, hw, rfl⟩
    have hρ'' : MulAut.conj τ ρ ∈ Ē.map (MulAut.conj τ).toMonoidHom := ⟨ρ, hρ, rfl⟩
    refine ⟨(MulAut.conj τ ρ) w, hW'inv _ hρ'' w hw, ?_⟩
    simp [MulAut.conj_apply]
  · obtain ⟨ρ, hρ, rfl⟩ := hρ'
    refine ⟨ρ, hρ, τ⁻¹ w', ⟨w', hw', rfl⟩, fun hρw => hmove ?_⟩
    have hρw' : ρ (τ⁻¹ w') = τ⁻¹ w' := hρw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply]
    rw [hρw']
    simp

theorem eInvFour_of_fixed_four {Ē : Subgroup (MulAut X)} (hE3 : IsElemAbelian 3 Ē)
    (hE9 : Nat.card Ē = 9) {a : MulAut X} (ha : a ∈ Ē) (ha1 : a ≠ 1) {g₀ : X}
    (hg₀ : MulAut.conj g₀ ∈ Ē) (hg₀a : MulAut.conj g₀ ∉ Subgroup.zpowers a) {Y : X}
    (haY : a Y = Y) {V : Subgroup X} (hV : IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (haV : ∀ v ∈ V, a v = v) (hinv : ∀ v ∈ V, (Y * g₀ * Y⁻¹) * v * (Y * g₀ * Y⁻¹)⁻¹ ∈ V)
    (hmove : ∃ v ∈ V, (Y * g₀ * Y⁻¹) * v * (Y * g₀ * Y⁻¹)⁻¹ ≠ v) : EInvFour X Ē := by
  refine eInvFour_of_two_gens hE3 hE9 ha hg₀ ha1 hg₀a
    (W := V.map (MulAut.conj Y⁻¹).toMonoidHom) (CFSG.Open.IsElemAbelian.map hV _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj Y⁻¹).injective, hV4]) ?_ ?_ (Or.inr ?_)
  · rintro _ ⟨v, hv, rfl⟩ 
    refine ⟨v, hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp only [map_mul, map_inv, haY, haV v hv]
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨(Y * g₀ * Y⁻¹) * v * (Y * g₀ * Y⁻¹)⁻¹, hinv v hv, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · obtain ⟨v, hv, hne⟩ := hmove
    refine ⟨_, ⟨v, hv, rfl⟩, fun h => hne ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    calc (Y * g₀ * Y⁻¹) * v * (Y * g₀ * Y⁻¹)⁻¹
        = Y * (g₀ * (Y⁻¹ * v * Y⁻¹⁻¹) * g₀⁻¹) * Y⁻¹ := by group
      _ = Y * (Y⁻¹ * v * Y⁻¹⁻¹) * Y⁻¹ := by rw [h]
      _ = v := by group

end Gen

section Cyclic

variable {X : Type} [Group X] {Γ : Type} [Group Γ] [Finite Γ] [IsCyclic Γ]

theorem exists_inner_of_cyclic_out (Φ : Γ →* MulAut X)
    {Ē : Subgroup (MulAut X)} (hdec : ∀ α ∈ Ē, ∃ (g : X) (γ : Γ), α = MulAut.conj g * Φ γ)
    (hfaith : ∀ γ : Γ, Φ γ ∈ (MulAut.conj : X →* MulAut X).range → γ = 1)
    (hE3 : IsElemAbelian 3 Ē) (hE9 : Nat.card Ē = 9)
    {γ : Γ} (hγ : orderOf γ = 3) (hγE : Φ γ ∈ Ē) :
    ∃ g : X, MulAut.conj g ∈ Ē ∧ MulAut.conj g ∉ Subgroup.zpowers (Φ γ) := by
  classical
  set N : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hN
  haveI : N.Normal := ⟨fun n hn a => by
    obtain ⟨k, rfl⟩ := hn
    refine ⟨a k, ?_⟩
    ext x
    simp [MulAut.mul_apply, MulAut.conj_apply]⟩
  have hγ1 : Φ γ ≠ 1 := by
    intro h
    have := hfaith γ (by rw [h]; exact N.one_mem)
    rw [this, orderOf_one] at hγ
    omega
  obtain ⟨τ, hτE, hτγ⟩ := exists_not_mem_zpowers hE3 hE9 hγE hγ1
  obtain ⟨g, δ, hτ⟩ := hdec τ hτE
  have hδ3 : δ ^ 3 = 1 := by
    apply hfaith
    rw [map_pow]
    have hgN : MulAut.conj g ∈ N := ⟨g, rfl⟩
    have hq : (QuotientGroup.mk' N) (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr hgN
    have h1 : (QuotientGroup.mk' N) (Φ δ) = (QuotientGroup.mk' N) τ := by
      rw [hτ, map_mul, hq, one_mul]
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, h1, ← map_pow,
      hE3.2 τ hτE, map_one]
  have hδmem : δ ∈ Subgroup.zpowers γ := by
    by_cases hδ1 : δ = 1
    · rw [hδ1]; exact Subgroup.one_mem _
    · have hδo : orderOf δ = 3 := orderOf_eq_prime hδ3 hδ1
      have : Subgroup.zpowers δ = Subgroup.zpowers γ :=
        IsCyclic.subgroup_eq_iff_card_eq.mpr
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hδo, hγ])
      rw [← this]
      exact Subgroup.mem_zpowers δ
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hδmem
  refine ⟨g, ?_, ?_⟩
  · have : MulAut.conj g = τ * (Φ γ) ^ (-j) := by
      rw [hτ, ← hj, map_zpow]
      group
    rw [this]
    exact Ē.mul_mem hτE (Ē.zpow_mem hγE _)
  · intro hmem
    apply hτγ
    rw [hτ, ← hj, map_zpow]
    exact Subgroup.mul_mem _ hmem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)


theorem exists_ker_of_cyclic_hom (θ : MulAut X →* Γ) {Ē : Subgroup (MulAut X)}
    (hE3 : IsElemAbelian 3 Ē) (hE9 : Nat.card Ē = 9) {a : MulAut X} (haE : a ∈ Ē)
    (ha1 : θ a ≠ 1) : ∃ b ∈ Ē, θ b = 1 ∧ b ∉ Subgroup.zpowers a := by
  classical
  have ha1' : a ≠ 1 := fun h => ha1 (by rw [h, map_one])
  obtain ⟨τ, hτE, hτa⟩ := exists_not_mem_zpowers hE3 hE9 haE ha1'
  have hθa3 : θ a ^ 3 = 1 := by rw [← map_pow, hE3.2 a haE, map_one]
  have hθτ3 : θ τ ^ 3 = 1 := by rw [← map_pow, hE3.2 τ hτE, map_one]
  have hθao : orderOf (θ a) = 3 := orderOf_eq_prime hθa3 ha1
  have hθτmem : θ τ ∈ Subgroup.zpowers (θ a) := by
    by_cases hθτ1 : θ τ = 1
    · rw [hθτ1]; exact Subgroup.one_mem _
    · have hθτo : orderOf (θ τ) = 3 := orderOf_eq_prime hθτ3 hθτ1
      have : Subgroup.zpowers (θ τ) = Subgroup.zpowers (θ a) :=
        IsCyclic.subgroup_eq_iff_card_eq.mpr
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hθτo, hθao])
      rw [← this]
      exact Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hθτmem
  refine ⟨τ * a ^ (-j), Ē.mul_mem hτE (Ē.zpow_mem haE _), ?_, ?_⟩
  · rw [map_mul, map_zpow, ← hj, zpow_neg, mul_inv_cancel]
  · intro hmem
    apply hτa
    have : τ = (τ * a ^ (-j)) * a ^ j := by group
    rw [this]
    exact Subgroup.mul_mem _ hmem (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)

end Cyclic

section Center

theorem mulAut_mul_conj_mul_inv {X : Type} [Group X] (α : MulAut X) (y : X) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext m
  simp [MulAut.mul_apply, map_mul, map_inv, MulAut.conj_apply]

theorem center_eq_bot_of_simple_of_not_prime {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hcard : ¬ (Nat.card G).Prime) : Subgroup.center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    letI : CommGroup G :=
      { (inferInstance : Group G) with
        mul_comm := fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a }
    exact hcard (IsSimpleGroup.prime_card (α := G))

theorem center_eq_bot_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : Subgroup.center G = ⊥) : Subgroup.center H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e.symm z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz (e g)
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  simpa using congrArg e hz'

theorem conj_injective_of_mulEquiv {Z Y : Type} [Group Z] [Group Y] (e : Z ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Function.Injective (MulAut.conj : Z →* MulAut Z) := by
  intro a b hab
  have hc : ∀ x : Z, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
    have := congrArg (fun f : MulAut Z => f x) hab
    simpa [MulAut.conj_apply] using this
  have hmem : e (a⁻¹ * b) ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    have := hc x
    calc x * (a⁻¹ * b) = a⁻¹ * (a * x * a⁻¹) * b := by group
      _ = a⁻¹ * (b * x * b⁻¹) * b := by rw [this]
      _ = a⁻¹ * b * x := by group
  rw [hY, Subgroup.mem_bot] at hmem
  have : a⁻¹ * b = 1 := e.injective (hmem.trans e.map_one.symm)
  exact inv_mul_eq_one.mp this

end Center

end CFSG.RankThree.PartTwo.Sec21.Hering214
