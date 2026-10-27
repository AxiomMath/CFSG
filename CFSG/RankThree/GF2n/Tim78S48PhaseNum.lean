module

public import CFSG.RankThree.GF2n.Tim78S48PhaseCoord
public import CFSG.RankThree.GF2n.Tim78S48PhaseFrob
public import CFSG.RankThree.GF2n.Tim78S48PhaseCartan
public import Certificates.Certificate43
import CFSG.CGT.Timmesfeld75.L2Aut
import CFSG.RankThree.GF2n.Tim78S45Aux
import CFSG.RankThree.GF2n.Tim78Involution
import CFSG.RankThree.GF2n.Tim78Layers
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartTwo.Sec5.Hyp

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open Matrix
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem eq_one_of_sq_eq_one_char_two {F : Type} [Field F] [CharP F 2] {a : F} (h : a ^ 2 = 1) :
    a = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have : (a - 1) ^ 2 = 0 := by linear_combination h - (a - 1) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp this)

section MulVec

variable {F : Type} [Field F]

theorem utriElt_mulVec (s x y : F) :
    (utriElt s : Matrix (Fin 2) (Fin 2) F) *ᵥ ![x, y] = ![x + s * y, y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, utriElt_apply_00,
    utriElt_apply_01, utriElt_apply_10, utriElt_apply_11]

theorem ltriElt_mulVec (s x y : F) :
    (ltriElt s : Matrix (Fin 2) (Fin 2) F) *ᵥ ![x, y] = ![x, s * x + y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ltriElt_apply_00,
    ltriElt_apply_01, ltriElt_apply_10, ltriElt_apply_11]

theorem torusElt_mulVec (a : Fˣ) (x y : F) :
    (torusElt a : Matrix (Fin 2) (Fin 2) F) *ᵥ ![x, y] = ![(a : F) * x, ((a⁻¹ : Fˣ) : F) * y] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, torusElt_apply_00,
    torusElt_apply_01, torusElt_apply_10, torusElt_apply_11]

end MulVec

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Cert43


theorem torusLift_le_M (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g)
    {F : Type} [Field F] (D : L2Coords B T g F) {K₁ : Subgroup G} (hK₁ : IsTorusLift D K₁) :
    K₁ ≤ M := by
  intro k hk
  have := (H.torus_normalizes h48 hP hTK hTgK D
    (hK₁.eps_mem ⟨k, hK₁.le_X hk⟩ hk)).1
  rwa [H.normalizer_B] at this

theorem T0_relIndex_le (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g)
    {f : ℕ} (hf : f ≠ 0) (D : L2Coords B T g (GaloisField 2 f)) {K₁ : Subgroup G}
    (hK₁ : IsTorusLift D K₁) (hT₀e : Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g))
    (hrel : (T ⊓ kernel48 B T g).relIndex T = 2 ^ f) :
    B.relIndex (T ⊓ kernel48 B T g) ≤ 2 ^ f := by
  classical
  set K := kernel48 B T g with hK
  set T₀ := T ⊓ K with hT₀
  have hBT₀ : B ≤ T₀ := le_inf H.B_le_T
    ((le_sup_left : B ≤ B ⊔ conjSubgroup g B).trans (H.W_le_kernel h48))
  by_cases hT₀B : T₀ = B
  · rw [hT₀B, Subgroup.relIndex_self]
    exact Nat.one_le_two_pow
  have hnorm : ¬ M ≤ Subgroup.normalizer (T₀ : Set G) := fun hMn =>
    hT₀B (H.eq_B_of_normal_comm hBT₀ inf_le_left hMn fun a ha b hb =>
      comm_of_isElemAbelian hT₀e ha hb)
  obtain ⟨h, hhM, hh⟩ := SetLike.not_le_iff_exists.mp hnorm
  set E := conjSubgroup h T₀ with hE
  have hhT : h ∈ Subgroup.normalizer (T : Set G) := H.M_le_normalizer_T hhM
  have hET : E ≤ T := by
    intro x hx
    rw [hE, mem_conjSubgroup] at hx
    have h1 : h⁻¹ * x * h ∈ T := hx.1
    have := (Subgroup.mem_normalizer_iff.mp hhT _).mp h1
    rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this
  have hEe : Assembly.IsElemAbelian 2 E := isElemAbelian_conjSubgroup hT₀e h
  have hEcard : Nat.card E = Nat.card T₀ := card_conjSubgroup h T₀
  have hEne : E ≠ T₀ := fun e => hh (conjSubgroup_eq_self_iff.mp e)
  have hK₁M : K₁ ≤ M := H.torusLift_le_M h48 hP hTK hTgK D hK₁
  have hKX : T ⊔ conjSubgroup g T ≤ Subgroup.normalizer (K : Set G) :=
    H.X_le_normalizer_kernel h48
  have hTN : T ≤ Subgroup.normalizer (T₀ : Set G) := fun t ht =>
    mem_normalizer_inf (Subgroup.le_normalizer ht) (hKX (Subgroup.mem_sup_left ht))
  have hK₁T : K₁ ≤ Subgroup.normalizer (T : Set G) := fun k hk => H.M_le_normalizer_T (hK₁M hk)
  have hK₁T₀ : K₁ ≤ Subgroup.normalizer (T₀ : Set G) := fun k hk =>
    mem_normalizer_inf (hK₁T hk) (hKX (hK₁.le_X hk))
  have hK₁card : Nat.card K₁ = 2 ^ f - 1 := by rw [hK₁.card, GaloisField.card 2 f hf]
  have hK₁c : ∀ a ∈ K₁, ∀ b ∈ K₁, a * b = b * a := by
    have := hK₁.cyclic
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : K₁) ⟨b, hb⟩)
  have hK₁inf : K₁ ⊓ T₀ = ⊥ := by
    rw [eq_bot_iff, ← hK₁.inf_ker]
    exact inf_le_inf_left _ inf_le_right
  have hfrob : ∀ k ∈ K₁, k ≠ 1 → ∀ t ∈ T, (k * t * k⁻¹)⁻¹ * t ∈ T₀ → t ∈ T₀ := by
    intro k hk hk1 t ht hmem
    set kx : ↥(T ⊔ conjSubgroup g T) := ⟨k, hK₁.le_X hk⟩ with hkx
    set tx : ↥(T ⊔ conjSubgroup g T) := ⟨t, Subgroup.mem_sup_left ht⟩ with htx
    obtain ⟨a, ha⟩ := mem_torus_iff.mp (hK₁.eps_mem kx hk)
    obtain ⟨s, hs⟩ := D.exists_utri ht
    have hkne : D.ε kx ≠ 1 := fun h1 => hk1 (by
      have h2 : k ∈ K₁ ⊓ K := ⟨hk, (D.ker_iff kx).mp h1⟩
      rw [hK₁.inf_ker, Subgroup.mem_bot] at h2
      exact h2)
    have ha1 : (a : GaloisField 2 f) ≠ 1 := fun h1 => hkne (by
      rw [ha, show a = 1 from Units.ext h1]
      exact map_one (CFSG.Glauberman.Dickson.splitTorusSLHom (GaloisField 2 f)))
    have hy : (D.ε ((kx * tx * kx⁻¹)⁻¹ * tx)) = 1 := by
      rw [D.ker_iff]
      exact hmem.2
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, ha, hs] at hy
    rw [torusElt_mul_utriElt_mul_inv, utriElt_inv, ← utriElt_add] at hy
    have hs0 : s = 0 := by
      have h1 : -((a : GaloisField 2 f) ^ 2 * s) + s = 0 := by
        have := congrArg (fun m : SL(2, GaloisField 2 f) => m 0 1) hy
        simpa [utriElt_apply_01] using this
      by_contra hs0
      have h2 : ((a : GaloisField 2 f) ^ 2 - 1) * s = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact ha1 (eq_one_of_sq_eq_one_char_two (sub_eq_zero.mp h3))
      · exact hs0 h3
    have hε1 : D.ε tx = 1 := by rw [hs, hs0, utriElt_zero]
    exact ⟨ht, (D.ker_iff tx).mp hε1⟩
  have key := card_le_of_frobenius (T₀ := T₀) (T := T) (K₁ := K₁) (E := E) inf_le_left hTN hT₀e
    hK₁T hK₁T₀ hrel hK₁card hK₁c hK₁inf hfrob hET hEe hEcard hEne
  have hCB : T₀ ⊓ Subgroup.centralizer (T : Set G) ≤ B := by
    intro x hx
    have : x ∈ T ⊓ Subgroup.centralizer (T : Set G) := ⟨hx.1.1, hx.2⟩
    rwa [H.inf_centralizer_eq_B H.B_le_T H.T_le_Q H.M_le_normalizer_T] at this
  have hcardle : Nat.card ↥(T₀ ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) ≤ Nat.card B :=
    Subgroup.card_le_of_le hCB
  have hmul : B.relIndex T₀ * Nat.card B = Nat.card T₀ := by
    have := Subgroup.relIndex_mul_card B T₀
    rwa [inf_of_le_left hBT₀] at this
  have hBpos : 0 < Nat.card B := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hBpos
  calc B.relIndex T₀ * Nat.card B = Nat.card T₀ := hmul
    _ ≤ 2 ^ f * Nat.card ↥(T₀ ⊓ Subgroup.centralizer (T : Set G) : Subgroup G) := key
    _ ≤ 2 ^ f * Nat.card B := Nat.mul_le_mul_left _ hcardle

theorem false_of_T0_eq_B (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g)
    {f : ℕ} (hf : f ≠ 0) (D : L2Coords B T g (GaloisField 2 f)) {K₁ : Subgroup G}
    (hK₁ : IsTorusLift D K₁) (hΘ : HasNatCoords D) (hq : Nat.card B = 2 ^ f)
    (hT₀B : T ⊓ kernel48 B T g = B) : False := by
  classical
  obtain ⟨Θ, hΘW, hΘmul, hΘinj, hΘsurj, hΘconj⟩ := hΘ
  have hΘ0 : Θ 0 = 1 := by
    have h := hΘmul 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Θ 0) (by rw [mul_one]; exact h.symm)
  have hΘB : ∀ x : GaloisField 2 f, Θ ![x, 0] ∈ B := by
    intro x
    refine H.W_cent_T h48 hP hTK _ (hΘW _) fun t ht => ?_
    obtain ⟨s, hs⟩ := D.exists_utri ht
    have h := hΘconj ⟨t, Subgroup.mem_sup_left ht⟩ ![x, 0]
    rw [hs, utriElt_mulVec] at h
    simp only [mul_zero, add_zero] at h
    calc t * Θ ![x, 0] = (t * Θ ![x, 0] * t⁻¹) * t := by group
      _ = Θ ![x, 0] * t := by rw [h]
  have hBΘ : ∀ b ∈ B, ∃ x : GaloisField 2 f, Θ ![x, 0] = b := by
    intro b hb
    obtain ⟨v, hv⟩ := hΘsurj b (Subgroup.mem_sup_left hb)
    obtain ⟨t, ht, hεt⟩ := D.exists_T (1 : GaloisField 2 f)
    have h := hΘconj ⟨t, Subgroup.mem_sup_left ht⟩ v
    rw [hεt, hv] at h
    have hc := H.T_comm_B ht hb
    have h2 : t * b * t⁻¹ = b := by rw [hc]; group
    rw [h2] at h
    have h3 : v = (utriElt (1 : GaloisField 2 f) : Matrix (Fin 2) (Fin 2) _) *ᵥ v :=
      hΘinj (hv.trans h)
    have hv' : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv', utriElt_mulVec] at h3
    have h4 : v 1 = 0 := by
      have := congrFun h3 0
      simp at this
      exact this
    refine ⟨v 0, ?_⟩
    rw [← hv]
    congr 1
    ext i
    fin_cases i <;> simp [h4]
  let σ : GaloisField 2 f ≃+* GaloisField 2 f := (frobeniusEquiv (GaloisField 2 f) 2).symm
  have hσsq : ∀ x : GaloisField 2 f, σ (x ^ 2) = x := fun x => by
    have h := (frobeniusEquiv (GaloisField 2 f) 2).symm_apply_apply x
    rw [frobeniusEquiv_apply] at h
    exact h
  have hσ0 : σ 0 = 0 := map_zero σ
  have hzero : (![(0 : GaloisField 2 f), 0] : Fin 2 → GaloisField 2 f) = 0 := by
    ext i; fin_cases i <;> rfl
  let α : ↥T → GaloisField 2 f := fun t =>
    (D.ε ⟨t, Subgroup.mem_sup_left t.2⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1
  have hαeq : ∀ t : ↥T, D.ε ⟨t, Subgroup.mem_sup_left t.2⟩ = utriElt (α t) := by
    intro t
    obtain ⟨s, hs⟩ := D.exists_utri t.2
    have : α t = s := by
      show (D.ε ⟨t, Subgroup.mem_sup_left t.2⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 1 = s
      rw [hs]
      simp [utriElt_apply_01]
    rw [this]
    exact hs
  have hαmul : ∀ t t' : ↥T, α (t * t') = α t + α t' := by
    intro t t'
    have h1 : D.ε ⟨((t * t' : ↥T) : G), Subgroup.mem_sup_left (t * t').2⟩ =
        D.ε ⟨t, Subgroup.mem_sup_left t.2⟩ * D.ε ⟨t', Subgroup.mem_sup_left t'.2⟩ := by
      rw [← map_mul]; rfl
    rw [hαeq, hαeq, hαeq, ← utriElt_add] at h1
    exact utriElt_injective h1
  have hα1 : α 1 = 0 := by
    have h1 : D.ε ⟨((1 : ↥T) : G), Subgroup.mem_sup_left (1 : ↥T).2⟩ = 1 := map_one D.ε
    rw [hαeq, ← utriElt_zero] at h1
    exact utriElt_injective h1
  let ψ : ↥T →* ↥B :=
    { toFun := fun t => ⟨Θ ![σ (α t), 0], hΘB _⟩
      map_one' := by
        apply Subtype.ext
        show Θ ![σ (α 1), 0] = 1
        rw [hα1, hσ0, hzero, hΘ0]
      map_mul' := fun t t' => by
        apply Subtype.ext
        show Θ ![σ (α (t * t')), 0] = Θ ![σ (α t), 0] * Θ ![σ (α t'), 0]
        rw [hαmul, map_add, ← hΘmul]
        congr 1
        ext i; fin_cases i <;> simp }
  have hψker : ∀ a : ↥T, ψ a = 1 ↔ (a : G) ∈ B := by
    intro a
    constructor
    · intro h
      have h1 : Θ ![σ (α a), 0] = 1 := congrArg Subtype.val h
      have h2 : ![σ (α a), 0] = (0 : Fin 2 → GaloisField 2 f) := hΘinj (h1.trans hΘ0.symm)
      have h3 : σ (α a) = 0 := by simpa using congrFun h2 0
      have h4 : α a = 0 := σ.injective (h3.trans hσ0.symm)
      have h5 : D.ε ⟨a, Subgroup.mem_sup_left a.2⟩ = 1 := by rw [hαeq, h4, utriElt_zero]
      have h6 : (a : G) ∈ kernel48 B T g := (D.ker_iff _).mp h5
      rw [← hT₀B]
      exact ⟨a.2, h6⟩
    · intro h
      have h1 : (a : G) ∈ T ⊓ kernel48 B T g := by rw [hT₀B]; exact h
      have h2 : D.ε ⟨a, Subgroup.mem_sup_left a.2⟩ = 1 := (D.ker_iff _).mpr h1.2
      have h3 : α a = 0 := by
        have h4 := hαeq a
        rw [h2, ← utriElt_zero] at h4
        exact (utriElt_injective h4).symm
      apply Subtype.ext
      show Θ ![σ (α a), 0] = 1
      rw [h3, hσ0, hzero, hΘ0]
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, rfl⟩ := hBΘ b hb
    obtain ⟨t, ht, hεt⟩ := D.exists_T (x ^ 2)
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    show Θ ![σ (α ⟨t, ht⟩), 0] = Θ ![x, 0]
    have h1 : α ⟨t, ht⟩ = x ^ 2 := by
      have h2 := hαeq ⟨t, ht⟩
      rw [hεt] at h2
      exact (utriElt_injective h2).symm
    rw [h1, hσsq]
  have hψH : ∀ k ∈ K₁, ∀ a b : ↥T, (b : G) = k * a * k⁻¹ →
      ((ψ b : ↥B) : G) = k * ((ψ a : ↥B) : G) * k⁻¹ := by
    intro k hk a b hab
    obtain ⟨c, hc⟩ := mem_torus_iff.mp (hK₁.eps_mem ⟨k, hK₁.le_X hk⟩ hk)
    have hbx : D.ε ⟨b, Subgroup.mem_sup_left b.2⟩ =
        torusElt c * utriElt (α a) * (torusElt c)⁻¹ := by
      have : (⟨b, Subgroup.mem_sup_left b.2⟩ : ↥(T ⊔ conjSubgroup g T)) =
          ⟨k, hK₁.le_X hk⟩ * ⟨a, Subgroup.mem_sup_left a.2⟩ * ⟨k, hK₁.le_X hk⟩⁻¹ :=
        Subtype.ext hab
      rw [this, map_mul, map_mul, map_inv, hc, hαeq a]
    rw [torusElt_mul_utriElt_mul_inv, hαeq b] at hbx
    have hαb : α b = (c : GaloisField 2 f) ^ 2 * α a := utriElt_injective hbx
    show Θ ![σ (α b), 0] = k * Θ ![σ (α a), 0] * k⁻¹
    have h := hΘconj ⟨k, hK₁.le_X hk⟩ ![σ (α a), 0]
    rw [hc, torusElt_mulVec] at h
    refine Eq.trans ?_ h.symm
    congr 1
    ext i
    fin_cases i
    · simp [hαb, map_mul, hσsq]
    · simp
  have hfaith : ∀ k ∈ K₁, (∀ x ∈ B, k * x * k⁻¹ = x) → k = 1 := by
    intro k hk hall
    obtain ⟨c, hc⟩ := mem_torus_iff.mp (hK₁.eps_mem ⟨k, hK₁.le_X hk⟩ hk)
    have h1 := hall (Θ ![1, 0]) (hΘB 1)
    have h2 := hΘconj ⟨k, hK₁.le_X hk⟩ ![1, 0]
    rw [hc, torusElt_mulVec] at h2
    change k * Θ ![1, 0] * k⁻¹ = _ at h2
    rw [h1] at h2
    have h3 := hΘinj h2
    have hc1 : (c : GaloisField 2 f) = 1 := by simpa using (congrFun h3 0).symm
    have h4 : D.ε ⟨k, hK₁.le_X hk⟩ = 1 := by
      rw [hc, show c = 1 from Units.ext hc1]
      exact map_one (CFSG.Glauberman.Dickson.splitTorusSLHom (GaloisField 2 f))
    have h5 : k ∈ K₁ ⊓ kernel48 B T g := ⟨hk, (D.ker_iff _).mp h4⟩
    rw [hK₁.inf_ker, Subgroup.mem_bot] at h5
    exact h5
  have hK₁M : K₁ ≤ M := H.torusLift_le_M h48 hP hTK hTgK D hK₁
  have hK₁c : ∀ a ∈ K₁, ∀ b ∈ K₁, a * b = b * a := by
    have := hK₁.cyclic
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : K₁) ⟨b, hb⟩)
  have hK₁card : Nat.card K₁ = 2 ^ f - 1 := by rw [hK₁.card, GaloisField.card 2 f hf]
  have hTab := abelian_of_equivalent_layers (A := T) (Ω := B) (H := K₁) (n := f) hK₁c hK₁card
    (H.isPGroup_Q.to_le H.T_le_Q) H.B_le_T H.elemAb hq
    (fun k hk => H.M_le_normalizer_T (hK₁M hk)) (fun k hk => H.M_le_normalizer_B (hK₁M hk))
    hfaith ψ hψker hψsurj hψH
  obtain ⟨x₀, hx₀T, hx₀B⟩ := SetLike.exists_of_lt (lt_of_le_of_ne H.B_le_T H.B_ne_T)
  have h1 : x₀ ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    ⟨hx₀T, Subgroup.mem_centralizer_iff.mpr fun h hh => hTab h hh x₀ hx₀T⟩
  rw [H.inf_centralizer_eq_B H.B_le_T H.T_le_Q H.M_le_normalizer_T] at h1
  exact hx₀B h1

theorem l2_numerics (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P)
    (hTK : ∃ t ∈ T, t ∉ kernel48 B T g) (hTgK : ∃ t ∈ conjSubgroup g T, t ∉ kernel48 B T g)
    (hconj : ∃ x ∈ T ⊔ conjSubgroup g T, conjSubgroup g B = conjSubgroup x B)
    {f : ℕ} (hf : 2 ≤ f) (D : L2Coords B T g (GaloisField 2 f)) {K₁ : Subgroup G}
    (hK₁ : IsTorusLift D K₁) (hT₀e : Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g))
    (hrel : (T ⊓ kernel48 B T g).relIndex T = 2 ^ f) :
    Nat.card B = 2 ^ f ∧ B < T ⊓ kernel48 B T g ∧ HasNatCoords D := by
  classical
  have hf0 : f ≠ 0 := by omega
  obtain ⟨s, hs, hΘ⟩ := H.exists_natural_W h48 hP hTK hTgK hconj D
  rw [GaloisField.card 2 f hf0] at hs
  have hE1 := H.cartan_on_quotient
  have hE2 := H.T0_relIndex_le h48 hP hTK hTgK hf0 D hK₁ hT₀e hrel
  have hBT₀ : B ≤ T ⊓ kernel48 B T g := le_inf H.B_le_T
    ((le_sup_left : B ≤ B ⊔ conjSubgroup g B).trans (H.W_le_kernel h48))
  have hmul := Subgroup.relIndex_mul_relIndex B (T ⊓ kernel48 B T g) T hBT₀ inf_le_left
  rw [hrel] at hmul
  have hq4 := H.q4
  have hP4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hm1 : B.relIndex (T ⊓ kernel48 B T g) ≠ 1 → B < T ⊓ kernel48 B T g := fun h =>
    lt_of_le_not_ge hBT₀ fun hle => h (Subgroup.relIndex_eq_one.mpr hle)
  set m := B.relIndex (T ⊓ kernel48 B T g) with hmdef
  have hqm : Nat.card B ≤ m * 2 ^ f := by rw [hmul]; exact hE1.1
  have hP0 : 0 < 2 ^ f := by omega
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · interval_cases s
    · rw [pow_zero] at hs; omega
    · rw [pow_one] at hs
      have hm : m ≠ 1 := by
        intro hm1'
        have hT₀B : T ⊓ kernel48 B T g = B :=
          le_antisymm (Subgroup.relIndex_eq_one.mp hm1') hBT₀
        exact H.false_of_T0_eq_B h48 hP hTK hTgK hf0 D hK₁ (hΘ rfl) hs hT₀B
      exact ⟨hs, hm1 hm, hΘ rfl⟩
  · exfalso
    have h1 : (2 ^ f) ^ 2 ≤ (2 ^ f) ^ s := Nat.pow_le_pow_right hP0 hs2
    have h2 : m * 2 ^ f ≤ (2 ^ f) * (2 ^ f) := Nat.mul_le_mul_right _ hE2
    have h3 : Nat.card B = (2 ^ f) ^ 2 := by nlinarith
    have h4 : m = 2 ^ f := by nlinarith
    have hmne : m ≠ 1 := by omega
    have hlt := hm1 hmne
    obtain ⟨x₀, hx₀, hx₀B⟩ := SetLike.exists_of_lt hlt
    refine H.false_of_regular hx₀.1 hx₀B (CFSG.Open.IsElemAbelian.mul_self_eq_one hT₀e hx₀)
      (hE1.2 ?_)
    rw [← hmul, h3, h4]
    ring

end Cert43

end Hyp4

end CFSG.RankThree.GF2n.Tim78
