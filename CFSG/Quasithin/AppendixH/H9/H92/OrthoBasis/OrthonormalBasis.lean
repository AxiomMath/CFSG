module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.ASVolI.ChH

private theorem zmod_two_eq_zero_of_ne_one : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private def perpIn (b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (W : Submodule (ZMod 2) V) (x : V) :
    Submodule (ZMod 2) V :=
  W ⊓ LinearMap.ker (b.flip x)

private theorem mem_perpIn {b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2} {W : Submodule (ZMod 2) V}
    {x w : V} : w ∈ perpIn b W x ↔ w ∈ W ∧ b w x = 0 := by
  simp [perpIn]

private theorem perpIn_le (b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (W : Submodule (ZMod 2) V)
    (x : V) : perpIn b W x ≤ W := inf_le_left

private theorem sub_smul_mem_perpIn {b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2}
    {W : Submodule (ZMod 2) V} {x z : V} (hxW : x ∈ W) (hx : b x x = 1) (hz : z ∈ W) :
    z - b z x • x ∈ perpIn b W x := by
  refine mem_perpIn.mpr ⟨W.sub_mem hz (W.smul_mem _ hxW), ?_⟩
  simp [hx]

private theorem perpIn_nondeg {b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2}
    {W : Submodule (ZMod 2) V} {x : V} (hxW : x ∈ W) (hx : b x x = 1)
    (hnd : ∀ w ∈ W, (∀ w' ∈ W, b w w' = 0) → w = 0) :
    ∀ w ∈ perpIn b W x, (∀ w' ∈ perpIn b W x, b w w' = 0) → w = 0 := by
  intro w hw hw'
  obtain ⟨hwW, hwx⟩ := mem_perpIn.mp hw
  refine hnd w hwW fun z hz => ?_
  have h := hw' _ (sub_smul_mem_perpIn hxW hx hz)
  simpa [hwx] using h

private theorem finrank_perpIn {b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2}
    {W : Submodule (ZMod 2) V} {x : V} (hxW : x ∈ W) (hx : b x x = 1) :
    Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) (perpIn b W x) + 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hsup : (ZMod 2 ∙ x) ⊔ perpIn b W x = W := by
    refine le_antisymm (sup_le ((Submodule.span_singleton_le_iff_mem x W).mpr hxW)
      (perpIn_le b W x)) fun z hz => ?_
    have h1 := sub_smul_mem_perpIn hxW hx hz
    have h2 : z = b z x • x + (z - b z x • x) := by abel
    rw [h2]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)) h1
  have hinf : (ZMod 2 ∙ x) ⊓ perpIn b W x = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy1
    have h := (mem_perpIn.mp hy2).2
    simp only [map_smul, LinearMap.smul_apply, hx, smul_eq_mul, mul_one] at h
    simp [h]
  have key := Submodule.finrank_sup_add_finrank_inf_eq (ZMod 2 ∙ x) (perpIn b W x)
  rw [hsup, hinf, finrank_bot, finrank_span_singleton hx0] at key
  omega

theorem exists_orthonormal_family (b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hsymm : ∀ x y, b x y = b y x) :
    ∀ (k : ℕ) (W : Submodule (ZMod 2) V), Module.finrank (ZMod 2) W = k →
      (∀ w ∈ W, (∀ w' ∈ W, b w w' = 0) → w = 0) → (k ≠ 0 → ∃ x ∈ W, b x x = 1) →
      ∃ e : Fin k → V, (∀ i, e i ∈ W) ∧ ∀ i j, b (e i) (e j) = if i = j then 1 else 0 := by
  intro k
  induction k with
  | zero => intro W _ _ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro W hW hnd hna
    obtain ⟨x₀, hx₀W, hx₀⟩ := hna (Nat.succ_ne_zero k)
    have hchoose : ∃ x₁ ∈ W, b x₁ x₁ = 1 ∧
        (k ≠ 0 → ∃ y ∈ perpIn b W x₁, b y y = 1) := by
      by_cases hk : k = 0
      · exact ⟨x₀, hx₀W, hx₀, fun h => absurd hk h⟩
      by_cases hex : ∃ y ∈ perpIn b W x₀, b y y = 1
      · exact ⟨x₀, hx₀W, hx₀, fun _ => hex⟩
      have hex' : ∀ y ∈ perpIn b W x₀, b y y = 0 := fun y hy =>
        zmod_two_eq_zero_of_ne_one _ fun h => hex ⟨y, hy, h⟩
      have hdim : Module.finrank (ZMod 2) (perpIn b W x₀) = k := by
        have := finrank_perpIn hx₀W hx₀
        omega
      have hne : perpIn b W x₀ ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hdim
        exact hk hdim.symm
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hnd0 := perpIn_nondeg hx₀W hx₀ hnd
      have hvw : ∃ w ∈ perpIn b W x₀, b v w = 1 := by
        by_contra hcon
        exact hv0 (hnd0 v hv fun w hw =>
          zmod_two_eq_zero_of_ne_one _ fun h => hcon ⟨w, hw, h⟩)
      obtain ⟨w, hw, hvw⟩ := hvw
      obtain ⟨hvW, hvx⟩ := mem_perpIn.mp hv
      obtain ⟨hwW, hwx⟩ := mem_perpIn.mp hw
      have hvv : b v v = 0 := hex' v hv
      have hww : b w w = 0 := hex' w hw
      have hxv : b x₀ v = 0 := by rw [hsymm]; exact hvx
      have hxw : b x₀ w = 0 := by rw [hsymm]; exact hwx
      have hwv : b w v = 1 := by rw [hsymm]; exact hvw
      refine ⟨x₀ + v, W.add_mem hx₀W hvW, ?_, fun _ => ⟨x₀ + w, ?_, ?_⟩⟩
      · simp only [map_add, LinearMap.add_apply, hx₀, hxv, hvx, hvv]
        decide
      · refine mem_perpIn.mpr ⟨W.add_mem hx₀W hwW, ?_⟩
        simp only [map_add, LinearMap.add_apply, hx₀, hxv, hwx, hwv]
        decide
      · simp only [map_add, LinearMap.add_apply, hx₀, hxw, hwx, hww]
        decide
    obtain ⟨x₁, hx₁W, hx₁, hna'⟩ := hchoose
    have hdim : Module.finrank (ZMod 2) (perpIn b W x₁) = k := by
      have := finrank_perpIn hx₁W hx₁
      omega
    obtain ⟨e', he'W, he'⟩ := ih (perpIn b W x₁) hdim (perpIn_nondeg hx₁W hx₁ hnd) hna'
    have hperp : ∀ j, b (e' j) x₁ = 0 := fun j => (mem_perpIn.mp (he'W j)).2
    refine ⟨Fin.cons x₁ e', fun i => ?_, fun i j => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx₁W
      · simpa using perpIn_le b W x₁ (he'W j)
    · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hx₁
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [if_neg (Fin.succ_ne_zero j).symm, hsymm]
        exact hperp j
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [if_neg (Fin.succ_ne_zero i)]
        exact hperp i
      · simpa using he' i j

theorem exists_orthonormal_family_of_nondegenerate (b : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (hsymm : ∀ x y, b x y = b y x) (hnd : ∀ w, (∀ w', b w w' = 0) → w = 0)
    (hna : ∃ x, b x x = 1) {k : ℕ} (hk : Module.finrank (ZMod 2) V = k) :
    ∃ e : Fin k → V, ∀ i j, b (e i) (e j) = if i = j then 1 else 0 := by
  obtain ⟨e, -, he⟩ := exists_orthonormal_family b hsymm k ⊤ (by rw [finrank_top, hk])
    (fun w _ hw => hnd w fun w' => hw w' trivial)
    (fun _ => by obtain ⟨x, hx⟩ := hna; exact ⟨x, trivial, hx⟩)
  exact ⟨e, he⟩

end CFSG.ASVolI.ChH
