module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.LocalAnalysis.StandardType.GGTBJReflLemma
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.StandardType

open Module QTwoLin

theorem ggQ2_reflKill {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (E : Submodule (ZMod p) V) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hAE : ∀ a ∈ A, ∀ v ∈ E, a v = v) (hTF : TransvectionFree A)
    {ι : Type} [Nonempty ι] (c : ι → V) (f : ι → Module.Dual (ZMod p) V)
    (hfc : ∀ i, f i (c i) = 2)
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ i j, (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ)
    (hfix : ∀ v : V, (∀ i, f i v = 0) → v ∈ E)
    (hdim : Submodule.span (ZMod p) (Set.range c) ⊔ E = ⊤ ∨
      (Submodule.span (ZMod p) (Set.range c) ⊓ E ≠ ⊥ ∧
        Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) (Set.range c) ⊔ E) + 1 =
          Module.finrank (ZMod p) V))
    (hTBC : ∀ i, Module.reflection (hfc i) ∈ A ∨
      ∀ a ∈ A, Module.reflection (hfc i) * a = a * Module.reflection (hfc i)) :
    (∀ v : V, (∀ a ∈ A, a v = v) → v ∈ E) ∨ Nat.card A ≤ p - 1 := by
  classical
  have h2ne : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (p := p) hp2
  have hc0 : ∀ i, c i ≠ 0 := fun i => (ne_zero_of_apply_eq_two hp2 (hfc i)).1
  let t : ι → V ≃ₗ[ZMod p] V := fun i => Module.reflection (hfc i)
  have ht_apply : ∀ i v, t i v = v - f i v • c i := fun i v => Module.reflection_apply v (hfc i)
  let U : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range c)
  by_cases hS : ∃ i, t i ∈ A
  · left
    obtain ⟨i₀, hi₀⟩ := hS
    have hSA : ∀ i, t i ∈ A := by
      let S : Set ι := {i | t i ∈ A}
      have hSne : S.Nonempty := ⟨i₀, hi₀⟩
      have hclosed : ∀ i j, (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → (i ∈ S ↔ j ∈ S) := by
        intro i j hadj
        constructor
        · intro hi
          have hti : t i ∈ A := by simpa [S] using hi
          by_contra hj
          have htj : t j ∉ A := by simpa [S] using hj
          have hcomm : Commute (t i) (t j) :=
            ((hTBC j).resolve_left htj (t i) hti).symm
          have heq : t i = t j :=
            ggReflEq_of_commute_of_adjacent hp2 (hfc i) (hfc j) hcomm hadj
          exact htj (heq ▸ hti)
        · intro hj
          have htj : t j ∈ A := by simpa [S] using hj
          by_contra hi
          have hti : t i ∉ A := by simpa [S] using hi
          have hcomm : Commute (t i) (t j) := (hTBC i).resolve_left hti (t j) htj
          have heq : t i = t j :=
            ggReflEq_of_commute_of_adjacent hp2 (hfc i) (hfc j) hcomm hadj
          exact hti (heq ▸ htj)
      have hSuniv : S = Set.univ := hconn S hSne hclosed
      intro i
      have hi : i ∈ S := by rw [hSuniv]; exact Set.mem_univ i
      simpa [S] using hi
    intro v hv
    apply hfix v
    intro i
    have hvi : t i v = v := hv (t i) (hSA i)
    rw [ht_apply i v] at hvi
    have h0 : f i v • c i = 0 := sub_eq_self.mp hvi
    exact (smul_eq_zero.mp h0).resolve_right (hc0 i)
  ·
    right
    have hcommA : ∀ i, ∀ a ∈ A, t i * a = a * t i := by
      intro i a ha
      rcases hTBC i with h | h
      · exact absurd h (fun hmem => hS ⟨i, hmem⟩)
      · exact h a ha
    let lam : ι → (V ≃ₗ[ZMod p] V) → ZMod p :=
      fun i a => (2 : ZMod p)⁻¹ * f i (a (c i))
    have hlam_smul : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (i : ι),
        a (c i) = lam i a • c i := by
      intro a ha i
      have happ := congrArg (fun T : V ≃ₗ[ZMod p] V => T (c i)) (hcommA i a ha)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at happ
      rw [show t i (a (c i)) = a (c i) - f i (a (c i)) • c i from ht_apply i (a (c i)),
        show t i (c i) = -c i from Module.reflection_apply_self (hfc i), map_neg] at happ
      have h2ac : (2 : ZMod p) • a (c i) = f i (a (c i)) • c i := by
        linear_combination (norm := module) happ
      calc a (c i) = ((2 : ZMod p)⁻¹ * 2) • a (c i) := by
              rw [inv_mul_cancel₀ h2ne, one_smul]
        _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • a (c i)) := by rw [smul_smul]
        _ = (2 : ZMod p)⁻¹ • (f i (a (c i)) • c i) := by rw [h2ac]
        _ = lam i a • c i := by rw [smul_smul]
    have hlam_apply : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (i : ι) (v : V),
        f i (a v) = f i v * lam i a := by
      intro a ha i v
      have happ := congrArg (fun T : V ≃ₗ[ZMod p] V => T v) (hcommA i a ha)
      simp only [t, LinearEquiv.mul_apply, Module.reflection_apply, map_sub, map_smul] at happ
      rw [hlam_smul a ha i] at happ
      have h3 : f i (a v) • c i = (f i v * lam i a) • c i := by
        simpa [smul_smul] using sub_right_injective happ
      exact (smul_left_inj (hc0 i)).mp h3
    have hlam_eq_of_adj : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) {i j : ι},
        (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → lam i a = lam j a := by
      intro a ha i j hadj
      rcases hadj with hij | hji
      · have h1 := hlam_apply a ha i (c j)
        have h2 : a (c j) = lam j a • c j := hlam_smul a ha j
        rw [h2, map_smul, smul_eq_mul] at h1
        exact mul_right_cancel₀ hij
          ((mul_comm (lam i a) (f i (c j))).trans h1.symm)
      · have h1 := hlam_apply a ha j (c i)
        have h2 : a (c i) = lam i a • c i := hlam_smul a ha i
        rw [h2, map_smul, smul_eq_mul] at h1
        exact mul_right_cancel₀ hji
          (h1.trans (mul_comm (f j (c i)) (lam j a)))
    let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
    have hlam_eq : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (i : ι), lam i a = lam i0 a := by
      intro a ha i
      let S : Set ι := {j | lam j a = lam i0 a}
      have hSne : S.Nonempty := ⟨i0, rfl⟩
      have hclosed : ∀ i j, (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → (i ∈ S ↔ j ∈ S) := by
        intro i j hadj
        have heq := hlam_eq_of_adj a ha hadj
        constructor
        · intro hi
          exact heq.symm.trans hi
        · intro hj
          exact heq.trans hj
      have hSuniv : S = Set.univ := hconn S hSne hclosed
      have hi : i ∈ S := by rw [hSuniv]; exact Set.mem_univ i
      simpa [S] using hi
    have hsmul_U : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) {u : V}, u ∈ U →
        a u = lam i0 a • u := by
      intro a ha u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro x ⟨i, rfl⟩
        rw [hlam_smul a ha i, hlam_eq a ha i]
      · simp
      · intro x y _ _ ihx ihy
        rw [map_add, ihx, ihy, smul_add]
      · intro r x _ ih
        rw [map_smul, ih, smul_comm r (lam i0 a) x]
    have hlam_ne : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A), lam i0 a ≠ 0 := by
      intro a ha h0
      have h1 : a (c i0) = lam i0 a • c i0 := hlam_smul a ha i0
      rw [h0, zero_smul] at h1
      exact hc0 i0 (a.injective (by rw [h1, map_zero]))
    rcases hdim with htop | ⟨hinf, hfr⟩
    ·
      have hlam_inj : ∀ (a b : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (hb : b ∈ A),
          lam i0 a = lam i0 b → a = b := by
        intro a b ha hb h
        refine LinearEquiv.ext fun v => ?_
        have hv : v ∈ U ⊔ E := by rw [htop]; exact Submodule.mem_top
        obtain ⟨u, hu, e, he, rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add, map_add, hsmul_U a ha hu, hsmul_U b hb hu, h,
          hAE a ha e he, hAE b hb e he]
      have hcard : Nat.card A ≤ p - 1 := by
        have hinj : Function.Injective (fun a : A =>
            Units.mk0 (lam i0 (a : V ≃ₗ[ZMod p] V))
              (hlam_ne (a : V ≃ₗ[ZMod p] V) a.2)) := by
          intro a b hab
          refine Subtype.ext ?_
          apply hlam_inj (a : V ≃ₗ[ZMod p] V) (b : V ≃ₗ[ZMod p] V) a.2 b.2
          have h := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hab
          simpa using h
        have h1 := Nat.card_le_card_of_injective _ hinj
        have h2 : Nat.card (ZMod p)ˣ = p - 1 := by
          rw [Nat.card_eq_fintype_card, ZMod.card_units]
        rwa [h2] at h1
      exact hcard
    ·
      have hlam_one : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A), lam i0 a = 1 := by
        intro a ha
        obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
        have h1 : a u = lam i0 a • u := hsmul_U a ha hu.1
        have h2 : a u = u := hAE a ha u hu.2
        have h3 : lam i0 a • u = (1 : ZMod p) • u := by rw [← h1, h2, one_smul]
        exact (smul_left_inj hu0).mp h3
      have hfixP : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (p : V),
          p ∈ U ⊔ E → a p = p := by
        intro a ha p hp
        obtain ⟨u, hu, e, he, rfl⟩ := Submodule.mem_sup.mp hp
        rw [map_add, hsmul_U a ha hu, hlam_one a ha, one_smul, hAE a ha e he]
      have hPtop : U ⊔ E < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro htop'
        have hfr' : Module.finrank (ZMod p) ↥(U ⊔ E) + 1 = Module.finrank (ZMod p) V := hfr
        rw [htop', finrank_top] at hfr'
        omega
      obtain ⟨v0, _, hv0⟩ := SetLike.exists_of_lt hPtop
      obtain ⟨ψ0, hψ0ne, hPle⟩ := Submodule.exists_le_ker_of_lt_top (U ⊔ E) hPtop
      have hkerψ0 : LinearMap.ker ψ0 = U ⊔ E := by
        have hfrP : Module.finrank (ZMod p) ↥(U ⊔ E) + 1 = Module.finrank (ZMod p) V := hfr
        have hfrker : Module.finrank (ZMod p) ↥(LinearMap.ker ψ0) + 1 =
            Module.finrank (ZMod p) V := Module.Dual.finrank_ker_add_one_of_ne_zero hψ0ne
        have hmono : Module.finrank (ZMod p) ↥(U ⊔ E) ≤
            Module.finrank (ZMod p) ↥(LinearMap.ker ψ0) := Submodule.finrank_mono hPle
        have heq : Module.finrank (ZMod p) ↥(U ⊔ E) =
            Module.finrank (ZMod p) ↥(LinearMap.ker ψ0) := by omega
        exact (Submodule.eq_of_le_of_finrank_eq hPle heq).symm
      have hψ0v0 : ψ0 v0 ≠ 0 := by
        intro h0
        exact hv0 (hkerψ0 ▸ LinearMap.mem_ker.mpr h0)
      let ψ : Module.Dual (ZMod p) V := (ψ0 v0)⁻¹ • ψ0
      have hψv0 : ψ v0 = 1 := by
        rw [show ψ v0 = (ψ0 v0)⁻¹ * ψ0 v0 by
          simp [ψ, LinearMap.smul_apply, smul_eq_mul]]
        exact inv_mul_cancel₀ hψ0v0
      have hkerψ : LinearMap.ker ψ = U ⊔ E := by
        rw [show ψ = (ψ0 v0)⁻¹ • ψ0 from rfl,
          LinearMap.ker_smul ψ0 (ψ0 v0)⁻¹ (inv_ne_zero hψ0v0), hkerψ0]
      let nu : (V ≃ₗ[ZMod p] V) → ZMod p := fun a => ψ (a v0)
      have hν_apply : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (v : V),
          ψ (a v) = nu a * ψ v := by
        intro a ha v
        have hp : v - ψ v • v0 ∈ U ⊔ E := by
          rw [← hkerψ, LinearMap.mem_ker, map_sub, map_smul, hψv0, smul_eq_mul, mul_one]
          exact sub_self (ψ v)
        have hp0 : ψ (v - ψ v • v0) = 0 :=
          LinearMap.mem_ker.mp (hkerψ ▸ hp)
        have hv : v = (v - ψ v • v0) + ψ v • v0 := by abel
        calc ψ (a v) = ψ (a ((v - ψ v • v0) + ψ v • v0)) :=
              congrArg (fun w => ψ (a w)) hv
          _ = ψ (a (v - ψ v • v0) + ψ v • a v0) := by rw [map_add, map_smul]
          _ = ψ (v - ψ v • v0) + ψ v • ψ (a v0) := by
                rw [map_add, map_smul, hfixP a ha (v - ψ v • v0) hp]
          _ = ψ v * nu a := by rw [hp0, zero_add, smul_eq_mul]
          _ = nu a * ψ v := mul_comm _ _
      have hν_mul : ∀ (a b : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (hb : b ∈ A),
          nu (a * b) = nu a * nu b := by
        intro a b ha hb
        have h := hν_apply a ha (b v0)
        simpa [nu, LinearEquiv.mul_apply] using h
      have hν_one : nu (1 : V ≃ₗ[ZMod p] V) = 1 := by simp [nu, hψv0]
      have hν_ne : ∀ (a : V ≃ₗ[ZMod p] V) (ha : a ∈ A), nu a ≠ 0 := by
        intro a ha h0
        have haP : a v0 ∈ U ⊔ E := hkerψ ▸ LinearMap.mem_ker.mpr h0
        have hinv : a⁻¹ ∈ A := A.inv_mem ha
        have hfixv : a⁻¹ (a v0) = v0 := a.symm_apply_apply v0
        have hmemp : v0 ∈ U ⊔ E := by
          rw [← hfixv, hfixP a⁻¹ hinv (a v0) haP]
          exact haP
        exact hv0 hmemp
      have hν_inj : ∀ (a b : V ≃ₗ[ZMod p] V) (ha : a ∈ A) (hb : b ∈ A),
          nu a = nu b → a = b := by
        intro a b ha hb hν
        let g : V ≃ₗ[ZMod p] V := b⁻¹ * a
        have hgA : g ∈ A := A.mul_mem (A.inv_mem hb) ha
        have hνg : nu g = 1 := by
          have hb' : nu b⁻¹ * nu b = 1 := by
            have hm := hν_mul b⁻¹ b (A.inv_mem hb) hb
            rw [inv_mul_cancel, hν_one] at hm
            exact hm.symm
          calc nu g = nu b⁻¹ * nu a := by rw [hν_mul b⁻¹ a (A.inv_mem hb) ha]
            _ = nu b⁻¹ * nu b := by rw [hν]
            _ = 1 := hb'
        have hgP : ∀ p, p ∈ U ⊔ E → g p = p := fun p hp => hfixP g hgA p hp
        have hgv0 : g v0 = v0 := by
          by_contra hne
          apply hTF g hgA
          refine ⟨g v0 - v0, ψ, ?_, ?_, ?_, ?_⟩
          · intro h0
            exact hne (sub_eq_zero.mp h0)
          · intro hψ
            rw [hψ] at hψv0
            simp at hψv0
          · rw [map_sub, show ψ (g v0) = 1 from hνg, hψv0]
            exact sub_self (1 : ZMod p)
          · intro v
            have hp : v - ψ v • v0 ∈ U ⊔ E := by
              rw [← hkerψ, LinearMap.mem_ker, map_sub, map_smul, hψv0, smul_eq_mul, mul_one]
              exact sub_self (ψ v)
            have h1 : g (v - ψ v • v0) = v - ψ v • v0 := hgP _ hp
            have hv : v = (v - ψ v • v0) + ψ v • v0 := by abel
            calc g v = g ((v - ψ v • v0) + ψ v • v0) :=
                  congrArg (fun w => g w) hv
              _ = g (v - ψ v • v0) + ψ v • g v0 := by rw [map_add, map_smul]
              _ = (v - ψ v • v0) + ψ v • g v0 := by rw [h1]
              _ = v + ψ v • (g v0 - v0) := by module
        have hspan_top : (U ⊔ E) ⊔ Submodule.span (ZMod p) {v0} = ⊤ := by
          have hfr' : Module.finrank (ZMod p) ↥((U ⊔ E) ⊔ Submodule.span (ZMod p) {v0}) =
              Module.finrank (ZMod p) V := by
            rw [Submodule.finrank_sup_span_singleton (p := U ⊔ E) hv0, hfr]
          exact Submodule.eq_top_of_finrank_eq hfr'
        have hg1 : g = 1 := by
          refine LinearEquiv.ext fun v => ?_
          have hv : v ∈ (U ⊔ E) ⊔ Submodule.span (ZMod p) {v0} := by
            rw [hspan_top]; exact Submodule.mem_top
          obtain ⟨p, hp, w, hw, hvw⟩ := Submodule.mem_sup.mp hv
          obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hw
          rw [← hvw, map_add, map_smul, hgP p hp, hgv0]
          simp
        have hba : b⁻¹ * a = 1 := hg1
        calc a = b * (b⁻¹ * a) := by group
          _ = b * 1 := by rw [hba]
          _ = b := by group
      have hcard : Nat.card A ≤ p - 1 := by
        have hinj : Function.Injective (fun a : A =>
            Units.mk0 (nu (a : V ≃ₗ[ZMod p] V))
              (hν_ne (a : V ≃ₗ[ZMod p] V) a.2)) := by
          intro a b hab
          refine Subtype.ext ?_
          apply hν_inj (a : V ≃ₗ[ZMod p] V) (b : V ≃ₗ[ZMod p] V) a.2 b.2
          have h := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hab
          simpa using h
        have h1 := Nat.card_le_card_of_injective _ hinj
        have h2 : Nat.card (ZMod p)ˣ = p - 1 := by
          rw [Nat.card_eq_fintype_card, ZMod.card_units]
        rwa [h2] at h1
      exact hcard

theorem ggQ2_reflKill_three
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]
    (E : Submodule (ZMod 3) V) (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hAE : ∀ a ∈ A, ∀ v ∈ E, a v = v) (hTF : TransvectionFree A)
    {ι : Type} [Nonempty ι] (c : ι → V) (f : ι → Module.Dual (ZMod 3) V)
    (hfc : ∀ i, f i (c i) = 2)
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ i j, (f i (c j) ≠ 0 ∨ f j (c i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ)
    (hfix : ∀ v : V, (∀ i, f i v = 0) → v ∈ E)
    (hdim : Submodule.span (ZMod 3) (Set.range c) ⊔ E = ⊤ ∨
      (Submodule.span (ZMod 3) (Set.range c) ⊓ E ≠ ⊥ ∧
        Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) (Set.range c) ⊔ E) + 1 =
          Module.finrank (ZMod 3) V))
    (hTBC : ∀ i, Module.reflection (hfc i) ∈ A ∨
      ∀ a ∈ A, Module.reflection (hfc i) * a = a * Module.reflection (hfc i))
    (hI1 : ∃ v : V, (∀ a ∈ A, a v = v) ∧ v ∉ E) (hCav : 4 ∣ Nat.card A) : False := by
  have hnot : ¬ (∀ v : V, (∀ a ∈ A, a v = v) → v ∈ E) := by
    rintro h
    obtain ⟨v, hv, hve⟩ := hI1
    exact hve (h v hv)
  have hle := (ggQ2_reflKill (p := 3) (by norm_num) E A hAE hTF c f hfc hconn hfix hdim
    hTBC).resolve_left hnot
  have hV : Finite V := Module.finite_of_finite (R := ZMod 3) (M := V)
  have hE : Finite (V ≃ V) := @Equiv.finite_right V V hV
  have hGL : Finite (V ≃ₗ[ZMod 3] V) :=
    @Finite.of_injective (V ≃ₗ[ZMod 3] V) (V ≃ V) hE (fun e => e.toEquiv)
      LinearEquiv.toEquiv_injective
  have hfinA : Finite A :=
    @Subgroup.instFiniteSubtypeMem (V ≃ₗ[ZMod 3] V) _ A hGL
  have hpos : 0 < Nat.card A :=
    Nat.card_pos_iff.mpr ⟨⟨⟨1, A.one_mem⟩⟩, hfinA⟩
  have h4 : 4 ≤ Nat.card A := Nat.le_of_dvd hpos hCav
  omega

end CFSG.StandardType

end
