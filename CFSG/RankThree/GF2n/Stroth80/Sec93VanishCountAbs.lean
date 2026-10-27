module

public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.GF2n.Stroth80

lemma card_mul_card_le_of_sum_inf {K : Type} [Field K] {E : Type} [AddCommGroup E]
    [Module K E] [Finite E] (W' V' : Submodule K E) (A₁ A₂ : AddSubgroup E)
    (hVA : ∀ v ∈ V', v ∈ A₁) (hVB : ∀ v ∈ V', v ∈ A₂)
    (hsum : ∀ w ∈ W', ∃ a ∈ A₁, ∃ b ∈ A₂, w = a + b) :
    Nat.card W' * Nat.card V' ≤ Nat.card A₁ * Nat.card A₂ := by
  obtain ⟨f, hf⟩ : ∃ f : (↥A₁ × ↥A₂) →+ E, ∀ p, f p = p.1.1 + p.2.1 :=
    ⟨A₁.subtype.coprod A₂.subtype, fun p => rfl⟩
  have hrange : Nat.card f.ker * Nat.card f.range = Nat.card A₁ * Nat.card A₂ := by
    rw [AddSubgroup.card_ker_mul_card_range f, Nat.card_prod]
  have hWr : ∀ w ∈ W', w ∈ f.range := by
    intro w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hsum w hw
    exact AddMonoidHom.mem_range.mpr ⟨(⟨a, ha⟩, ⟨b, hb⟩), by simp [hf]⟩
  have hmemker : ∀ v (hv : v ∈ V'),
      ((⟨v, hVA v hv⟩, ⟨-v, A₂.neg_mem (hVB v hv)⟩) : ↥A₁ × ↥A₂) ∈ f.ker := by
    intro v hv
    rw [AddMonoidHom.mem_ker, hf]
    simp
  have h1 : Nat.card W' ≤ Nat.card f.range := by
    refine Nat.card_le_card_of_injective (fun w : W' => (⟨w.1, hWr w.1 w.2⟩ : f.range)) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext h
  have h2 : Nat.card V' ≤ Nat.card f.ker := by
    refine Nat.card_le_card_of_injective
      (fun v : V' => (⟨((⟨v.1, hVA v.1 v.2⟩, ⟨-v.1, A₂.neg_mem (hVB v.1 v.2)⟩) : ↥A₁ × ↥A₂),
        hmemker v.1 v.2⟩ : f.ker)) ?_
    intro x y hxy
    have h := congrArg (fun z : f.ker => z.1.1.1) hxy
    exact Subtype.ext h
  calc Nat.card W' * Nat.card V' ≤ Nat.card f.range * Nat.card f.ker := Nat.mul_le_mul h1 h2
    _ = Nat.card f.ker * Nat.card f.range := Nat.mul_comm _ _
    _ = Nat.card A₁ * Nat.card A₂ := hrange

lemma card_key_bound {K : Type} [Field K] [Finite K] {E : Type} [AddCommGroup E] [Module K E]
    [Module.Finite K E] (B : E →ₗ[K] E →ₗ[K] K) (hnd : ∀ y : E, (∀ e, B e y = 0) → y = 0)
    (T N : E →ₗ[K] E) (hN : ∀ e, N e = T e - e)
    (hTB : ∀ e f, B (T e) (T f) = B e f) (hTT : ∀ e, T (T e) = e)
    (V' W' : Submodule K E) (hW' : ∀ w, w ∈ W' ↔ ∀ v ∈ V', B w v = 0)
    (hnt : ∃ v ∈ V', T v ≠ v) (A : AddSubgroup E) (hA1 : ∀ a ∈ A, a ∈ W')
    (hA2 : ∀ a ∈ A, T a ∈ W') (hA3 : ∀ a ∈ A, T a = a → a ∈ V') :
    Nat.card K ^ 2 * Nat.card A ≤ Nat.card (LinearMap.range N) * Nat.card V' := by
  haveI : Finite E := Module.finite_of_finite K
  obtain ⟨v0, hv0V, hv0⟩ := hnt
  have hNv0 : N v0 ≠ 0 := by
    rw [hN v0]
    exact sub_ne_zero.mpr hv0
  have hBT : ∀ e v, B (T e) v = B e (T v) := by
    intro e v
    have h := hTB (T e) v
    rw [hTT e] at h
    exact h.symm
  obtain ⟨e, he⟩ : ∃ e, B e (N v0) ≠ 0 := by
    by_contra hcon
    exact hNv0 (hnd _ fun e => Classical.byContradiction fun h => hcon ⟨e, h⟩)
  have hBN : B (N e) v0 = B e (N v0) := by
    simp only [hN, map_sub, LinearMap.sub_apply, hBT]
  have hNe : N e ∉ W' := by
    intro hmem
    apply he
    rw [← hBN]
    exact (hW' _).mp hmem v0 hv0V
  have hS_lt : LinearMap.range N ⊓ W' < LinearMap.range N := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    apply hNe
    have hmem : N e ∈ LinearMap.range N ⊓ W' := by
      rw [h]
      exact LinearMap.mem_range_self N e
    exact (Submodule.mem_inf.mp hmem).2
  have hC_lt : V' ⊓ LinearMap.ker N < V' := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    apply hNv0
    have hmem : v0 ∈ V' ⊓ LinearMap.ker N := by
      rw [h]
      exact hv0V
    exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hmem).2
  have hcardS : ∀ U : Submodule K E, Nat.card U = Nat.card K ^ Module.finrank K U :=
    fun U => Module.natCard_eq_pow_finrank
  have hq : 0 < Nat.card K := Nat.card_pos
  have hrS : Nat.card K * Nat.card ↥(LinearMap.range N ⊓ W') ≤
      Nat.card ↥(LinearMap.range N) := by
    rw [hcardS, hcardS, ← pow_succ']
    exact Nat.pow_le_pow_right hq (Nat.succ_le_of_lt (Submodule.finrank_lt_finrank_of_lt hS_lt))
  have hrC : Nat.card K * Nat.card ↥(V' ⊓ LinearMap.ker N) ≤ Nat.card ↥V' := by
    rw [hcardS, hcardS, ← pow_succ']
    exact Nat.pow_le_pow_right hq (Nat.succ_le_of_lt (Submodule.finrank_lt_finrank_of_lt hC_lt))
  obtain ⟨D, hD⟩ : ∃ D : A →+ E, ∀ a : A, D a = N a.1 :=
    ⟨N.toAddMonoidHom.comp A.subtype, fun a => rfl⟩
  have hAD : Nat.card D.ker * Nat.card D.range = Nat.card A :=
    AddSubgroup.card_ker_mul_card_range D
  have hker_mem : ∀ x : D.ker, x.1.1 ∈ V' ⊓ LinearMap.ker N := by
    intro x
    have hx : N x.1.1 = 0 := by
      have h := AddMonoidHom.mem_ker.mp x.2
      rwa [hD] at h
    have hfix : T x.1.1 = x.1.1 := by
      have h := hN x.1.1
      rw [hx] at h
      exact sub_eq_zero.mp h.symm
    exact Submodule.mem_inf.mpr ⟨hA3 x.1.1 x.1.2 hfix, LinearMap.mem_ker.mpr hx⟩
  have hker_le : Nat.card D.ker ≤ Nat.card ↥(V' ⊓ LinearMap.ker N) := by
    refine Nat.card_le_card_of_injective
      (fun x : D.ker => (⟨x.1.1, hker_mem x⟩ : ↥(V' ⊓ LinearMap.ker N))) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hrange_mem : ∀ x ∈ D.range, x ∈ LinearMap.range N ⊓ W' := by
    intro x hx
    obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hx
    rw [hD]
    refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self N a.1, ?_⟩
    rw [hN a.1]
    exact W'.sub_mem (hA2 a.1 a.2) (hA1 a.1 a.2)
  have hrange_le : Nat.card D.range ≤ Nat.card ↥(LinearMap.range N ⊓ W') := by
    refine Nat.card_le_card_of_injective
      (fun x : D.range => (⟨x.1, hrange_mem x.1 x.2⟩ : ↥(LinearMap.range N ⊓ W'))) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext h
  rw [← hAD]
  calc Nat.card K ^ 2 * (Nat.card D.ker * Nat.card D.range)
      = (Nat.card K * Nat.card D.range) * (Nat.card K * Nat.card D.ker) := by ring
    _ ≤ (Nat.card K * Nat.card D.range) *
          (Nat.card K * Nat.card ↥(V' ⊓ LinearMap.ker N)) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl hker_le)
    _ ≤ Nat.card (LinearMap.range N) * Nat.card V' :=
        Nat.mul_le_mul (le_trans (Nat.mul_le_mul le_rfl hrange_le) hrS) hrC

theorem card_range_sub_id_sq_ge
    {K : Type} [Field K] [Finite K] {E : Type} [AddCommGroup E] [Module K E] [Module.Finite K E]
    (B : E →ₗ[K] E →ₗ[K] K) (hnd : ∀ y : E, (∀ e, B e y = 0) → y = 0)
    (T : E →ₗ[K] E) (hTB : ∀ e f, B (T e) (T f) = B e f) (hTT : ∀ e, T (T e) = e)
    (V' W' : Submodule K E) (hW' : ∀ w, w ∈ W' ↔ ∀ v ∈ V', B w v = 0)
    (hTV : ∀ v ∈ V', T v ∈ V') (hnt : ∃ v ∈ V', T v ≠ v)
    (A₁ A₂ : AddSubgroup E) (hVA : ∀ v ∈ V', v ∈ A₁) (hVB : ∀ v ∈ V', v ∈ A₂)
    (hAW : ∀ a ∈ A₁, a ∈ W') (hBW : ∀ b ∈ A₂, b ∈ W')
    (hsum : ∀ w ∈ W', ∃ a ∈ A₁, ∃ b ∈ A₂, w = a + b)
    (hinf : ∀ e, e ∈ A₁ → e ∈ A₂ → e ∈ V')
    (hTA : ∀ a ∈ A₁, T a ∈ A₂) (hTB' : ∀ b ∈ A₂, T b ∈ A₁)
    (hdual : Nat.card W' * Nat.card V' = Nat.card E) :
    Nat.card K ^ 4 * Nat.card E ≤
      (Nat.card (LinearMap.range (T - LinearMap.id)) * Nat.card V') ^ 2 := by
  haveI : Finite E := Module.finite_of_finite K
  have hN : ∀ e, (T - LinearMap.id : E →ₗ[K] E) e = T e - e := fun e => rfl
  have h1 := card_key_bound B hnd T (T - LinearMap.id) hN hTB hTT V' W' hW' hnt A₁
    hAW (fun a ha => hBW _ (hTA a ha))
    (fun a ha hfix => hinf a ha (by have h := hTA a ha; rwa [hfix] at h))
  have h2 := card_key_bound B hnd T (T - LinearMap.id) hN hTB hTT V' W' hW' hnt A₂
    hBW (fun b hb => hAW _ (hTB' b hb))
    (fun b hb hfix => hinf b (by have h := hTB' b hb; rwa [hfix] at h) hb)
  have hprod := card_mul_card_le_of_sum_inf W' V' A₁ A₂ hVA hVB hsum
  calc Nat.card K ^ 4 * Nat.card E
      = Nat.card K ^ 4 * (Nat.card W' * Nat.card V') := by rw [hdual]
    _ ≤ Nat.card K ^ 4 * (Nat.card A₁ * Nat.card A₂) := Nat.mul_le_mul le_rfl hprod
    _ = (Nat.card K ^ 2 * Nat.card A₁) * (Nat.card K ^ 2 * Nat.card A₂) := by ring
    _ ≤ (Nat.card (LinearMap.range (T - LinearMap.id)) * Nat.card V') *
          (Nat.card (LinearMap.range (T - LinearMap.id)) * Nat.card V') :=
        Nat.mul_le_mul h1 h2
    _ = (Nat.card (LinearMap.range (T - LinearMap.id)) * Nat.card V') ^ 2 := by ring

end CFSG.RankThree.GF2n.Stroth80
