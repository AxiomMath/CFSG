module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped commutatorElement

namespace CFSG.Monster.Schur

noncomputable def toZ2 {E : Type*} [One E] (y : E) : ZMod 2 := by
  classical
  exact if y = 1 then 0 else 1

theorem toZ2_eq_zero_iff {E : Type*} [One E] {y : E} : toZ2 y = 0 ↔ y = 1 := by
  classical
  unfold toZ2
  by_cases h : y = 1 <;> simp [h]

structure LiftData (E Γ V : Type*) [Group E] [Group Γ] [AddCommGroup V] [Module (ZMod 2) V] where
  P : Subgroup E
  [normal : P.Normal]
  p : E →* Γ
  ρ : Representation (ZMod 2) Γ V
  vec : P → V
  n : E
  zh : E
  surj_p : Function.Surjective p
  ker_p : p.ker = P
  perfect : Group.IsPerfect Γ
  finV : Finite V
  dim : 1 < Module.finrank (ZMod 2) V
  n_central : n ∈ Subgroup.center E
  n_sq : n * n = 1
  n_ne_one : n ≠ 1
  n_mem : n ∈ P
  zh_mem : zh ∈ P
  zh_ne_one : zh ≠ 1
  zh_ne_n : zh ≠ n
  vec_mul : ∀ x y, vec (x * y) = vec x + vec y
  vec_conj : ∀ (c : E) (x : P), vec (MulAut.conjNormal c x) = ρ (p c) (vec x)
  vec_surj : Function.Surjective vec
  vec_ker : ∀ x : P, vec x = 0 ↔ (x : E) = 1 ∨ (x : E) = n ∨ (x : E) = zh ∨ (x : E) = zh * n
  center : ∀ x : P, vec x = 0 ↔ ∀ y : P, ⁅(x : E), (y : E)⁆ ∈ Subgroup.zpowers n
  irr : ∀ W : Submodule (ZMod 2) V, (∀ γ : Γ, ∀ w ∈ W, ρ γ w ∈ W) → W = ⊥ ∨ W = ⊤
  end_ : ∀ ψ : V →ₗ[ZMod 2] V, (∀ γ v, ψ (ρ γ v) = ρ γ (ψ v)) → ψ = 0 ∨ ψ = 1
  ext1 : ∀ f : Γ → Module.Dual (ZMod 2) V, (∀ g h v, f (g * h) v = f g (ρ h v) + f h v) →
    ∃ φ : Module.Dual (ZMod 2) V, ∀ g v, f g v = φ (ρ g v) - φ v

namespace LiftData

variable {E Γ V : Type*} [Group E] [Group Γ] [AddCommGroup V] [Module (ZMod 2) V]
  (D : LiftData E Γ V)

attribute [instance] LiftData.normal

theorem char2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have h : (2 : ZMod 2) = 0 := by decide
  rw [h, zero_smul]

theorem vec_one : D.vec 1 = 0 := by
  have h := D.vec_mul 1 1
  rw [mul_one] at h
  exact (add_eq_left.1 h.symm)

theorem vec_inv (x : D.P) : D.vec x⁻¹ = - D.vec x := by
  have h := D.vec_mul x x⁻¹
  rw [mul_inv_cancel, D.vec_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem vec_sq (x : D.P) : D.vec (x * x) = 0 := by
  rw [D.vec_mul, char2]

theorem vec_comm (x y : D.P) : D.vec (x * y) = D.vec (y * x) := by
  rw [D.vec_mul, D.vec_mul, add_comm]

theorem vec_comm' (x y : D.P) : D.vec (x * y * x⁻¹ * y⁻¹) = 0 := by
  rw [D.vec_mul, D.vec_mul, D.vec_mul, D.vec_inv, D.vec_inv]
  abel

def InK (k : E) : Prop := k = 1 ∨ k = D.n ∨ k = D.zh ∨ k = D.zh * D.n


theorem descend {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (g : D.P → M)
    (hg : ∀ x y, g (x * y) = g x + g y) (hk : ∀ x, D.vec x = 0 → g x = 0) :
    ∃ φ : V →ₗ[ZMod 2] M, ∀ x, φ (D.vec x) = g x := by
  classical
  have hg1 : g 1 = 0 := by
    have h := hg 1 1
    rw [mul_one] at h
    exact add_eq_left.1 h.symm
  have hginv : ∀ x, g x⁻¹ = - g x := fun x => by
    have h := hg x x⁻¹
    rw [mul_inv_cancel, hg1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have heq : ∀ x y, D.vec x = D.vec y → g x = g y := by
    intro x y h
    have h1 : D.vec (x⁻¹ * y) = 0 := by rw [D.vec_mul, D.vec_inv, h]; simp
    have h2 := hk _ h1
    rw [hg, hginv] at h2
    exact neg_add_eq_zero.1 h2
  let f : V → M := fun v => g (Classical.choose (D.vec_surj v))
  have hf : ∀ x, f (D.vec x) = g x := fun x =>
    heq _ _ (Classical.choose_spec (D.vec_surj (D.vec x)))
  have hadd : ∀ v w, f (v + w) = f v + f w := by
    intro v w
    obtain ⟨x, rfl⟩ := D.vec_surj v
    obtain ⟨y, rfl⟩ := D.vec_surj w
    rw [← D.vec_mul, hf, hf, hf, hg]
  have hzero : f 0 = 0 := by
    have := hf 1
    rwa [D.vec_one, hg1] at this
  let F : V →+ M := ⟨⟨f, hzero⟩, hadd⟩
  exact ⟨F.toZModLinearMap 2, fun x => hf x⟩

theorem inv_functional_zero (φ : V →ₗ[ZMod 2] ZMod 2) (h : ∀ γ v, φ (D.ρ γ v) = φ v) :
    φ = 0 := by
  have := D.finV
  rcases D.irr (LinearMap.ker φ) (fun γ w hw => by
    rw [LinearMap.mem_ker] at hw ⊢
    rw [h, hw]) with h1 | h1
  · exfalso
    have hinj : Function.Injective φ := LinearMap.ker_eq_bot.1 h1
    have hfin := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_self] at hfin
    have := D.dim
    omega
  · exact LinearMap.ker_eq_top.1 h1


theorem n_comm (g : E) : g * D.n = D.n * g := Subgroup.mem_center_iff.1 D.n_central g

theorem n_conj (g : E) : D.n * g * D.n⁻¹ = g := by
  rw [mul_inv_eq_iff_eq_mul, ← D.n_comm g]

theorem n_inv : D.n⁻¹ = D.n := inv_eq_of_mul_eq_one_right D.n_sq

theorem mem_zpowers_n {y : E} : y ∈ Subgroup.zpowers D.n ↔ y = 1 ∨ y = D.n := by
  constructor
  · intro h
    let H : Subgroup E :=
      { carrier := {1, D.n}
        one_mem' := Or.inl rfl
        mul_mem' := by
          rintro a b (rfl | rfl) (rfl | rfl)
          · exact Or.inl (mul_one 1)
          · exact Or.inr (one_mul _)
          · exact Or.inr (mul_one _)
          · exact Or.inl D.n_sq
        inv_mem' := by
          rintro a (rfl | rfl)
          · exact Or.inl inv_one
          · exact Or.inr D.n_inv }
    exact Subgroup.zpowers_le.2 (show D.n ∈ H from Or.inr rfl) h
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem toZ2_mul {y z : E} (hy : y = 1 ∨ y = D.n) (hz : z = 1 ∨ z = D.n) :
    toZ2 (y * z) = toZ2 y + toZ2 z := by
  classical
  unfold toZ2
  rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
  · simp
  · simp
  · simp
  · simp [D.n_sq, D.n_ne_one]
    decide

theorem zhn_ne_one : D.zh * D.n ≠ 1 := fun h => D.zh_ne_n (by
  rw [mul_eq_one_iff_eq_inv, D.n_inv] at h
  exact h)

theorem vec_zh : D.vec ⟨D.zh, D.zh_mem⟩ = 0 :=
  (D.vec_ker _).2 (Or.inr (Or.inr (Or.inl rfl)))

theorem conj_zh (c : E) : c * D.zh * c⁻¹ = D.zh ∨ c * D.zh * c⁻¹ = D.zh * D.n := by
  have h1 : D.vec (MulAut.conjNormal c ⟨D.zh, D.zh_mem⟩) = 0 := by
    rw [D.vec_conj, D.vec_zh, map_zero]
  have h2 := (D.vec_ker _).1 h1
  rw [MulAut.conjNormal_apply] at h2
  simp only at h2
  rcases h2 with h | h | h | h
  · exfalso
    apply D.zh_ne_one
    have := congrArg (fun y => c⁻¹ * y * c) h
    simpa [mul_assoc] using this
  · exfalso
    apply D.zh_ne_n
    have := congrArg (fun y => c⁻¹ * y * c) h
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at this
    rw [this, ← D.n_comm c, inv_mul_cancel_left]
  · exact Or.inl h
  · exact Or.inr h


theorem commute_zh_n : Commute D.zh D.n := D.n_comm D.zh

theorem commute_zh_K {k : E} (hk : D.InK k) : Commute D.zh k := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact Commute.one_right _
  · exact D.commute_zh_n
  · exact Commute.refl _
  · exact (Commute.refl _).mul_right D.commute_zh_n

theorem comm_mul_right_of_central {a x y : E} (h : ∀ g : E, g * ⁅a, y⁆ = ⁅a, y⁆ * g) :
    ⁅a, x * y⁆ = ⁅a, x⁆ * ⁅a, y⁆ := by
  have e : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, h x, mul_inv_cancel_right]

theorem central_of_zpowers {c : E} (hc : c = 1 ∨ c = D.n) (g : E) : g * c = c * g := by
  rcases hc with rfl | rfl
  · rw [mul_one, one_mul]
  · exact D.n_comm g

theorem comm_zh_mem (x : D.P) : ⁅D.zh, (x : E)⁆ = 1 ∨ ⁅D.zh, (x : E)⁆ = D.n :=
  D.mem_zpowers_n.1 ((D.center ⟨D.zh, D.zh_mem⟩).1 D.vec_zh x)

noncomputable def lz (x : D.P) : ZMod 2 := toZ2 ⁅D.zh, (x : E)⁆

theorem lz_mul (x y : D.P) : D.lz (x * y) = D.lz x + D.lz y := by
  unfold lz
  have h : ⁅D.zh, ((x * y : D.P) : E)⁆ = ⁅D.zh, (x : E)⁆ * ⁅D.zh, (y : E)⁆ :=
    comm_mul_right_of_central (fun g => D.central_of_zpowers (D.comm_zh_mem y) g)
  rw [h, D.toZ2_mul (D.comm_zh_mem x) (D.comm_zh_mem y)]

theorem lz_ker (x : D.P) (hx : D.vec x = 0) : D.lz x = 0 := by
  unfold lz
  rw [toZ2_eq_zero_iff]
  exact (D.commute_zh_K ((D.vec_ker x).1 hx)).commutator_eq

theorem lz_conj (c : E) (x : D.P) : D.lz (MulAut.conjNormal c x) = D.lz x := by
  unfold lz
  rw [MulAut.conjNormal_apply]
  have e : ⁅D.zh, c * (x : E) * c⁻¹⁆ = c * ⁅c⁻¹ * D.zh * c, (x : E)⁆ * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hx := D.comm_zh_mem x
  have h2 : ⁅D.zh * D.n, (x : E)⁆ = ⁅D.zh, (x : E)⁆ := by
    calc ⁅D.zh * D.n, (x : E)⁆ = D.zh * (D.n * (x : E) * D.n⁻¹) * D.zh⁻¹ * (x : E)⁻¹ := by
          simp only [commutatorElement_def, mul_inv_rev]
          group
      _ = ⁅D.zh, (x : E)⁆ := by
          rw [D.n_conj]
          rfl
  have key : ⁅c⁻¹ * D.zh * c, (x : E)⁆ = ⁅D.zh, (x : E)⁆ := by
    rcases D.conj_zh c⁻¹ with h | h
    · rw [inv_inv] at h
      rw [h]
    · rw [inv_inv] at h
      rw [h]
      exact h2
  rw [e, key, D.central_of_zpowers hx c, mul_inv_cancel_right]

theorem zh_comm_P (x : D.P) : D.zh * (x : E) = (x : E) * D.zh := by
  have := D.finV
  obtain ⟨φ, hφ⟩ := D.descend (M := ZMod 2) D.lz D.lz_mul D.lz_ker
  have hinv : ∀ γ v, φ (D.ρ γ v) = φ v := by
    intro γ v
    obtain ⟨c, rfl⟩ := D.surj_p γ
    obtain ⟨y, rfl⟩ := D.vec_surj v
    rw [← D.vec_conj, hφ, hφ, D.lz_conj]
  have h0 := D.inv_functional_zero φ hinv
  have h1 : D.lz x = 0 := by
    rw [← hφ, h0]
    rfl
  have h2 : ⁅D.zh, (x : E)⁆ = 1 := (toZ2_eq_zero_iff).1 h1
  exact commutatorElement_eq_one_iff_mul_comm.1 h2


theorem hom_trivial_of_perfect (f : E →* Multiplicative (ZMod 2)) (hf : D.P ≤ f.ker) : f = 1 := by
  have h1 : Subgroup.map D.p (commutator E) = ⊤ := by
    have h2 : (commutator Γ) = ⊤ := Group.isPerfect_def.1 D.perfect
    have h3 : Subgroup.map D.p (commutator E) = commutator Γ := by
      unfold commutator
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ D.surj_p]
    rw [h3, h2]
  have h4 : commutator E ⊔ D.p.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, h1, Subgroup.comap_top]
  have h5 : commutator E ≤ f.ker := Abelianization.commutator_subset_ker f
  have h6 : (⊤ : Subgroup E) ≤ f.ker := by
    rw [← h4]
    exact sup_le h5 (D.ker_p ▸ hf)
  refine MonoidHom.ext fun g => ?_
  exact h6 (Subgroup.mem_top g)

def wz (c : E) : E := c * D.zh * c⁻¹ * D.zh⁻¹

theorem wz_mem (c : E) : D.wz c = 1 ∨ D.wz c = D.n := by
  unfold wz
  rcases D.conj_zh c with h | h
  · left
    rw [h]
    group
  · right
    rw [h]
    exact mul_inv_eq_iff_eq_mul.2 (D.n_comm D.zh)

theorem wz_mul (c d : E) : D.wz (c * d) = D.wz d * D.wz c := by
  have hu : ∀ g : E, g * D.wz d = D.wz d * g := fun g => D.central_of_zpowers (D.wz_mem d) g
  have e : D.wz (c * d) = c * D.wz d * c⁻¹ * D.wz c := by
    unfold wz
    group
  rw [e, hu c, mul_inv_cancel_right]

theorem wz_P (x : D.P) : D.wz x = 1 := by
  unfold wz
  rw [← D.zh_comm_P x, mul_inv_cancel_right, mul_inv_cancel]

noncomputable def wzHom : E →* Multiplicative (ZMod 2) where
  toFun c := Multiplicative.ofAdd (toZ2 (D.wz c))
  map_one' := by
    have : D.wz 1 = 1 := by simp [wz]
    rw [this]
    simp [toZ2_eq_zero_iff.2 rfl]
  map_mul' c d := by
    rw [D.wz_mul, D.toZ2_mul (D.wz_mem d) (D.wz_mem c), add_comm]
    rfl

theorem zh_central (c : E) : c * D.zh * c⁻¹ = D.zh := by
  have h := D.hom_trivial_of_perfect D.wzHom (fun x hx => by
    rw [MonoidHom.mem_ker]
    simp [wzHom, D.wz_P ⟨x, hx⟩, toZ2_eq_zero_iff.2 rfl])
  have h1 : D.wzHom c = 1 := by rw [h]; rfl
  have h2 : D.wz c = 1 := by
    have : toZ2 (D.wz c) = 0 := by simpa [wzHom] using h1
    exact toZ2_eq_zero_iff.1 this
  exact mul_inv_eq_one.1 h2

theorem zh_comm (g : E) : g * D.zh = D.zh * g := by
  have := D.zh_central g
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem InK_comm {k : E} (hk : D.InK k) (g : E) : g * k = k * g := by
  rcases hk with rfl | rfl | rfl | rfl
  · rw [mul_one, one_mul]
  · exact D.n_comm g
  · exact D.zh_comm g
  · rw [← mul_assoc, D.zh_comm g, mul_assoc, D.n_comm g, mul_assoc]


theorem exists_noncomm : ∃ x y : D.P, ⁅(x : E), (y : E)⁆ ∉ Subgroup.zpowers D.n := by
  have := D.finV
  have hnt : Nontrivial V :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by have := D.dim; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨x, rfl⟩ := D.vec_surj v
  by_contra h
  apply hv
  apply (D.center x).2
  intro y
  by_contra hy
  exact h ⟨x, y, hy⟩

theorem comm_mem_K (x y : D.P) : D.InK ⁅(x : E), (y : E)⁆ :=
  (D.vec_ker (x * y * x⁻¹ * y⁻¹)).1 (D.vec_comm' x y)

end LiftData

theorem sq_comm_of_central {E : Type*} [Group E] {x y c : E} (hc : x * y * x⁻¹ * y⁻¹ = c)
    (hxc : x * c = c * x) : ⁅x * x, y⁆ = c * c := by
  have e1 : x * y * x⁻¹ = c * y := mul_inv_eq_iff_eq_mul.1 hc
  have e2 : x * c * x⁻¹ = c := mul_inv_eq_iff_eq_mul.2 hxc
  calc ⁅x * x, y⁆ = x * (x * y * x⁻¹) * x⁻¹ * y⁻¹ := by
        simp only [commutatorElement_def]
        group
    _ = x * (c * y) * x⁻¹ * y⁻¹ := by rw [e1]
    _ = (x * c * x⁻¹) * (x * y * x⁻¹) * y⁻¹ := by group
    _ = c * (c * y) * y⁻¹ := by rw [e2, e1]
    _ = c * c := by group

namespace LiftData

variable {E Γ V : Type*} [Group E] [Group Γ] [AddCommGroup V] [Module (ZMod 2) V]
  (D : LiftData E Γ V)

theorem zh_sq : D.zh * D.zh = 1 := by
  obtain ⟨x, y, hxy⟩ := D.exists_noncomm
  obtain ⟨c, hc⟩ : ∃ c : E, (x : E) * y * (x : E)⁻¹ * (y : E)⁻¹ = c := ⟨_, rfl⟩
  have hcK : D.InK c := by
    rw [← hc]
    exact D.comm_mem_K x y
  have hcne : c ∉ Subgroup.zpowers D.n := by
    rw [commutatorElement_def, hc] at hxy
    exact hxy
  have hcases : c = D.zh ∨ c = D.zh * D.n := by
    rcases hcK with h | h | h | h
    · exact absurd (h ▸ Subgroup.one_mem _) hcne
    · exact absurd (h ▸ Subgroup.mem_zpowers _) hcne
    · exact Or.inl h
    · exact Or.inr h
  have hx2 : D.InK ((x : E) * x) := (D.vec_ker (x * x)).1 (D.vec_sq x)
  have h1 : ⁅(x : E) * x, (y : E)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (D.InK_comm hx2 y).symm
  have hcc : c * c = 1 := by
    rw [← sq_comm_of_central hc (D.InK_comm hcK x)]
    exact h1
  rcases hcases with rfl | rfl
  · exact hcc
  · have : D.zh * D.n * (D.zh * D.n) = D.zh * D.zh * (D.n * D.n) := by
      calc D.zh * D.n * (D.zh * D.n) = D.zh * (D.n * D.zh) * D.n := by group
        _ = D.zh * (D.zh * D.n) * D.n := by rw [← D.n_comm D.zh]
        _ = D.zh * D.zh * (D.n * D.n) := by group
    rw [this, D.n_sq, mul_one] at hcc
    exact hcc


theorem n_mul_zh : D.n * D.zh = D.zh * D.n := (D.n_comm D.zh).symm

theorem zh_mul_zh_n : D.zh * (D.zh * D.n) = D.n := by
  rw [← mul_assoc, D.zh_sq, one_mul]

theorem zh_n_mul_zh : D.zh * D.n * D.zh = D.n := by
  rw [mul_assoc, ← D.n_comm D.zh, ← mul_assoc, D.zh_sq, one_mul]

theorem zh_n_mul_n : D.zh * D.n * D.n = D.zh := by
  rw [mul_assoc, D.n_sq, mul_one]

theorem n_mul_zh_n : D.n * (D.zh * D.n) = D.zh := by
  rw [← mul_assoc, D.n_mul_zh, mul_assoc, D.n_sq, mul_one]

theorem zh_n_mul_zh_n : D.zh * D.n * (D.zh * D.n) = 1 := by
  rw [mul_assoc, D.n_mul_zh_n, D.zh_sq]

theorem zhn_ne_n : D.zh * D.n ≠ D.n := fun h => D.zh_ne_one (by
  have := congrArg (· * D.n) h
  simpa [mul_assoc, D.n_sq] using this)

theorem zhn_ne_zh : D.zh * D.n ≠ D.zh := fun h => D.n_ne_one (by
  have := congrArg (D.zh⁻¹ * ·) h
  simpa using this)

theorem InK_mul {k k' : E} (hk : D.InK k) (hk' : D.InK k') : D.InK (k * k') := by
  have h1 := D.zh_ne_one
  rcases hk with rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl <;>
    simp only [InK, mul_one, one_mul, D.n_sq, D.zh_sq, D.n_mul_zh, D.zh_mul_zh_n, D.zh_n_mul_zh,
      D.zh_n_mul_n, D.n_mul_zh_n, D.zh_n_mul_zh_n, true_or, or_true]


noncomputable def chi (k : E) : ZMod 2 × ZMod 2 := by
  classical
  exact (if k = D.zh ∨ k = D.zh * D.n then 1 else 0, if k = D.n ∨ k = D.zh * D.n then 1 else 0)

theorem chi_one : D.chi 1 = (0, 0) := by
  have h1 := D.zh_ne_one
  have h2 := D.n_ne_one
  have h4 := D.zhn_ne_one
  simp [chi, h1.symm, h2.symm, h4.symm]

theorem chi_n : D.chi D.n = (0, 1) := by
  have h3 := D.zh_ne_n
  have h5 := D.zhn_ne_n
  simp [chi, h3.symm, h5.symm]

theorem chi_zh : D.chi D.zh = (1, 0) := by
  have h3 := D.zh_ne_n
  have h6 := D.zhn_ne_zh
  simp [chi, h3, h6.symm]

theorem chi_zhn : D.chi (D.zh * D.n) = (1, 1) := by
  simp [chi]

theorem chi_mul {k k' : E} (hk : D.InK k) (hk' : D.InK k') :
    D.chi (k * k') = D.chi k + D.chi k' := by
  rcases hk with rfl | rfl | rfl | rfl <;> rcases hk' with rfl | rfl | rfl | rfl <;>
    simp only [mul_one, one_mul, D.n_sq, D.zh_sq, D.n_mul_zh, D.zh_mul_zh_n, D.zh_n_mul_zh,
      D.zh_n_mul_n, D.n_mul_zh_n, D.zh_n_mul_zh_n, D.chi_one, D.chi_n, D.chi_zh, D.chi_zhn] <;>
    decide


theorem chi_fst_zero {k : E} (hk : D.InK k) (h : (D.chi k).1 = 0) : k = 1 ∨ k = D.n := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · simp only [D.chi_zh] at h
    exact absurd h (by decide)
  · simp only [D.chi_zhn] at h
    exact absurd h (by decide)

theorem comm_mul_left (x x' y : D.P) :
    ⁅((x * x' : D.P) : E), (y : E)⁆ = ⁅(x : E), (y : E)⁆ * ⁅(x' : E), (y : E)⁆ := by
  have hc : ∀ g : E, g * ⁅(x' : E), (y : E)⁆ = ⁅(x' : E), (y : E)⁆ * g := fun g =>
    D.InK_comm (D.comm_mem_K x' y) g
  have e : ⁅((x * x' : D.P) : E), (y : E)⁆ =
      (x : E) * ⁅(x' : E), (y : E)⁆ * (x : E)⁻¹ * ⁅(x : E), (y : E)⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul]
    group
  rw [e, hc (x : E), mul_inv_cancel_right]
  exact D.InK_comm (D.comm_mem_K x y) _


theorem comm_mul_right (x y y' : D.P) :
    ⁅(x : E), ((y * y' : D.P) : E)⁆ = ⁅(x : E), (y : E)⁆ * ⁅(x : E), (y' : E)⁆ :=
  comm_mul_right_of_central (fun g => D.InK_comm (D.comm_mem_K x y') g)

theorem comm_eq_one_of_vec_left (x y : D.P) (hx : D.vec x = 0) : ⁅(x : E), (y : E)⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.2 (D.InK_comm ((D.vec_ker x).1 hx) y).symm

theorem comm_eq_one_of_vec_right (x y : D.P) (hy : D.vec y = 0) : ⁅(x : E), (y : E)⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.2 (D.InK_comm ((D.vec_ker y).1 hy) x)

theorem comm_conj (c : E) (x y : D.P) :
    ⁅((MulAut.conjNormal c x : D.P) : E), ((MulAut.conjNormal c y : D.P) : E)⁆ =
      ⁅(x : E), (y : E)⁆ := by
  simp only [MulAut.conjNormal_apply]
  have e : ⁅c * (x : E) * c⁻¹, c * (y : E) * c⁻¹⁆ = c * ⁅(x : E), (y : E)⁆ * c⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e, D.InK_comm (D.comm_mem_K x y) c, mul_inv_cancel_right]

theorem exists_bilin (g : D.P → D.P → ZMod 2)
    (hl : ∀ x x' y, g (x * x') y = g x y + g x' y)
    (hr : ∀ x y y', g x (y * y') = g x y + g x y')
    (hkl : ∀ x y, D.vec x = 0 → g x y = 0) (hkr : ∀ x y, D.vec y = 0 → g x y = 0) :
    ∃ B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2, ∀ x y, B (D.vec x) (D.vec y) = g x y := by
  have h1 : ∀ x, ∃ φ : V →ₗ[ZMod 2] ZMod 2, ∀ y, φ (D.vec y) = g x y := fun x =>
    D.descend (M := ZMod 2) (g x) (hr x) (hkr x)
  choose φ hφ using h1
  have hadd : ∀ x x', φ (x * x') = φ x + φ x' := by
    intro x x'
    refine LinearMap.ext fun w => ?_
    obtain ⟨y, rfl⟩ := D.vec_surj w
    rw [LinearMap.add_apply, hφ, hφ, hφ, hl]
  have hker : ∀ x, D.vec x = 0 → φ x = 0 := by
    intro x hx
    refine LinearMap.ext fun w => ?_
    obtain ⟨y, rfl⟩ := D.vec_surj w
    rw [hφ, hkl x y hx]
    rfl
  obtain ⟨B, hB⟩ := D.descend (M := V →ₗ[ZMod 2] ZMod 2) φ hadd hker
  exact ⟨B, fun x y => by rw [hB, hφ]⟩


theorem exists_forms :
    ∃ Bβ B2 : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2,
      (∀ x y : D.P, Bβ (D.vec x) (D.vec y) = (D.chi ⁅(x : E), (y : E)⁆).1) ∧
      (∀ x y : D.P, B2 (D.vec x) (D.vec y) = (D.chi ⁅(x : E), (y : E)⁆).2) := by
  have hl : ∀ x x' y : D.P, D.chi ⁅((x * x' : D.P) : E), (y : E)⁆ =
      D.chi ⁅(x : E), (y : E)⁆ + D.chi ⁅(x' : E), (y : E)⁆ := fun x x' y => by
    rw [D.comm_mul_left, D.chi_mul (D.comm_mem_K x y) (D.comm_mem_K x' y)]
  have hr : ∀ x y y' : D.P, D.chi ⁅(x : E), ((y * y' : D.P) : E)⁆ =
      D.chi ⁅(x : E), (y : E)⁆ + D.chi ⁅(x : E), (y' : E)⁆ := fun x y y' => by
    rw [D.comm_mul_right, D.chi_mul (D.comm_mem_K x y) (D.comm_mem_K x y')]
  have hkl : ∀ x y : D.P, D.vec x = 0 → D.chi ⁅(x : E), (y : E)⁆ = 0 := fun x y hx => by
    rw [D.comm_eq_one_of_vec_left x y hx, D.chi_one]
    rfl
  have hkr : ∀ x y : D.P, D.vec y = 0 → D.chi ⁅(x : E), (y : E)⁆ = 0 := fun x y hy => by
    rw [D.comm_eq_one_of_vec_right x y hy, D.chi_one]
    rfl
  obtain ⟨Bβ, hBβ⟩ := D.exists_bilin (fun x y => (D.chi ⁅(x : E), (y : E)⁆).1)
    (fun x x' y => by simp only [hl, Prod.fst_add])
    (fun x y y' => by simp only [hr, Prod.fst_add])
    (fun x y hx => by simp only [hkl x y hx, Prod.fst_zero])
    (fun x y hy => by simp only [hkr x y hy, Prod.fst_zero])
  obtain ⟨B2, hB2⟩ := D.exists_bilin (fun x y => (D.chi ⁅(x : E), (y : E)⁆).2)
    (fun x x' y => by simp only [hl, Prod.snd_add])
    (fun x y y' => by simp only [hr, Prod.snd_add])
    (fun x y hx => by simp only [hkl x y hx, Prod.snd_zero])
    (fun x y hy => by simp only [hkr x y hy, Prod.snd_zero])
  exact ⟨Bβ, B2, hBβ, hB2⟩


end LiftData

theorem surjective_of_injective_dual {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V) (h : Function.Injective B) :
    Function.Surjective B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ZMod 2) (V := V)).symm).1 h

namespace LiftData

variable {E Γ V : Type*} [Group E] [Group Γ] [AddCommGroup V] [Module (ZMod 2) V]
  (D : LiftData E Γ V)

theorem K_cases {k : E} (hk : D.InK k) :
    (k = 1 ∧ D.chi k = (0, 0)) ∨ (k = D.n ∧ D.chi k = (0, 1)) ∨ (k = D.zh ∧ D.chi k = (1, 0)) ∨
      (k = D.zh * D.n ∧ D.chi k = (1, 1)) := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, D.chi_one⟩
  · exact Or.inr (Or.inl ⟨rfl, D.chi_n⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, D.chi_zh⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, D.chi_zhn⟩))

theorem exists_zeta : ∃ ζ : E, (ζ = D.zh ∨ ζ = D.zh * D.n) ∧
    ∀ x y : D.P, ⁅(x : E), (y : E)⁆ = 1 ∨ ⁅(x : E), (y : E)⁆ = ζ := by
  have hfin := D.finV
  obtain ⟨Bβ, B2, hBβ, hB2⟩ := D.exists_forms
  have hinvβ : ∀ γ v w, Bβ (D.ρ γ v) (D.ρ γ w) = Bβ v w := by
    intro γ v w
    obtain ⟨c, rfl⟩ := D.surj_p γ
    obtain ⟨x, rfl⟩ := D.vec_surj v
    obtain ⟨y, rfl⟩ := D.vec_surj w
    rw [← D.vec_conj, ← D.vec_conj, hBβ, hBβ, D.comm_conj]
  have hinv2 : ∀ γ v w, B2 (D.ρ γ v) (D.ρ γ w) = B2 v w := by
    intro γ v w
    obtain ⟨c, rfl⟩ := D.surj_p γ
    obtain ⟨x, rfl⟩ := D.vec_surj v
    obtain ⟨y, rfl⟩ := D.vec_surj w
    rw [← D.vec_conj, ← D.vec_conj, hB2, hB2, D.comm_conj]
  have hnd : Function.Injective Bβ := by
    refine (injective_iff_map_eq_zero Bβ).2 fun v hv => ?_
    obtain ⟨x, rfl⟩ := D.vec_surj v
    apply (D.center x).2
    intro y
    have h1 : (D.chi ⁅(x : E), (y : E)⁆).1 = 0 := by
      rw [← hBβ, hv]
      rfl
    exact D.mem_zpowers_n.2 (D.chi_fst_zero (D.comm_mem_K x y) h1)
  have hsurj : Function.Surjective Bβ := surjective_of_injective_dual Bβ hnd
  let e : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V := LinearEquiv.ofBijective Bβ ⟨hnd, hsurj⟩
  let ψ : V →ₗ[ZMod 2] V := e.symm.toLinearMap ∘ₗ B2
  have hψ : ∀ v w, Bβ (ψ v) w = B2 v w := by
    intro v w
    have h := e.apply_symm_apply (B2 v)
    exact congrArg (fun f => f w) h
  have hψγ : ∀ γ v, ψ (D.ρ γ v) = D.ρ γ (ψ v) := by
    intro γ v
    apply hnd
    refine LinearMap.ext fun w => ?_
    obtain ⟨w', rfl⟩ : ∃ w', D.ρ γ w' = w :=
      ⟨D.ρ γ⁻¹ w, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]⟩
    rw [hψ, hinv2, ← hψ, hinvβ]
  rcases D.end_ ψ hψγ with h | h
  · refine ⟨D.zh, Or.inl rfl, fun x y => ?_⟩
    have h2 : (D.chi ⁅(x : E), (y : E)⁆).2 = 0 := by
      rw [← hB2, ← hψ, h]
      simp
    rcases D.K_cases (D.comm_mem_K x y) with ⟨h3, _⟩ | ⟨_, h3⟩ | ⟨h3, _⟩ | ⟨_, h3⟩
    · exact Or.inl h3
    · rw [h3] at h2
      exact absurd h2 (by decide)
    · exact Or.inr h3
    · rw [h3] at h2
      exact absurd h2 (by decide)
  · refine ⟨D.zh * D.n, Or.inr rfl, fun x y => ?_⟩
    have h2 : (D.chi ⁅(x : E), (y : E)⁆).2 = (D.chi ⁅(x : E), (y : E)⁆).1 := by
      rw [← hB2, ← hψ, h, ← hBβ]
      simp
    rcases D.K_cases (D.comm_mem_K x y) with ⟨h3, _⟩ | ⟨_, h3⟩ | ⟨_, h3⟩ | ⟨h3, _⟩
    · exact Or.inl h3
    · rw [h3] at h2
      exact absurd h2 (by decide)
    · rw [h3] at h2
      exact absurd h2 (by decide)
    · exact Or.inr h3


theorem InK_sq {k : E} (hk : D.InK k) : k * k = 1 := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact D.n_sq
  · exact D.zh_sq
  · exact D.zh_n_mul_zh_n

theorem InK_mem {k : E} (hk : D.InK k) : k ∈ D.P := by
  rcases hk with rfl | rfl | rfl | rfl
  · exact D.P.one_mem
  · exact D.n_mem
  · exact D.zh_mem
  · exact D.P.mul_mem D.zh_mem D.n_mem

structure ZetaData (D : LiftData E Γ V) where
  ζ : E
  nu : E → ZMod 2
  inK : D.InK ζ
  ne_one : ζ ≠ 1
  ne_n : ζ ≠ D.n
  comm : ∀ x y : D.P, ⁅(x : E), (y : E)⁆ = 1 ∨ ⁅(x : E), (y : E)⁆ = ζ
  nu_mul : ∀ k k', D.InK k → D.InK k' → nu (k * k') = nu k + nu k'
  nu_zero : ∀ k, D.InK k → (nu k = 0 ↔ k = 1 ∨ k = ζ)
  nu_n : nu D.n = 1

theorem exists_zetaData : Nonempty D.ZetaData := by
  obtain ⟨ζ, hζ, hcomm⟩ := D.exists_zeta
  rcases hζ with rfl | rfl
  · refine ⟨⟨D.zh, fun k => (D.chi k).2, Or.inr (Or.inr (Or.inl rfl)), D.zh_ne_one, D.zh_ne_n,
      hcomm, fun k k' hk hk' => by simp only [D.chi_mul hk hk', Prod.snd_add], fun k hk => ?_,
      by simp [D.chi_n]⟩⟩
    rcases D.K_cases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h2]
    · simp [h1]
    · simp only [h1]
      constructor
      · intro h
        exact absurd h (by decide)
      · rintro (h | h)
        · exact absurd h D.n_ne_one
        · exact absurd h D.zh_ne_n.symm
    · simp [h1]
    · simp only [h1]
      constructor
      · intro h
        exact absurd h (by decide)
      · rintro (h | h)
        · exact absurd h D.zhn_ne_one
        · exact absurd h D.zhn_ne_zh
  · refine ⟨⟨D.zh * D.n, fun k => (D.chi k).1 + (D.chi k).2,
      Or.inr (Or.inr (Or.inr rfl)), D.zhn_ne_one, D.zhn_ne_n, hcomm,
      fun k k' hk hk' => by simp only [D.chi_mul hk hk', Prod.fst_add, Prod.snd_add]; abel,
      fun k hk => ?_, by simp [D.chi_n]⟩⟩
    rcases D.K_cases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h2]
    · simp [h1]
    · simp only [h1]
      constructor
      · intro h
        exact absurd h (by decide)
      · rintro (h | h)
        · exact absurd h D.n_ne_one
        · exact absurd h D.zhn_ne_n.symm
    · simp only [h1]
      constructor
      · intro h
        exact absurd h (by decide)
      · rintro (h | h)
        · exact absurd h D.zh_ne_one
        · exact absurd h D.zhn_ne_zh.symm
    · simp [h1]
      decide

namespace ZetaData

variable {D} (Z : D.ZetaData)

theorem sq_zeta : Z.ζ * Z.ζ = 1 := D.InK_sq Z.inK

theorem zeta_mem : Z.ζ ∈ D.P := D.InK_mem Z.inK

theorem sq_mul_eq {x y c : E} (hc : y * x * y⁻¹ * x⁻¹ = c) (hcx : ∀ g : E, g * c = c * g) :
    (x * y) * (x * y) = c * (x * x) * (y * y) := by
  have e : y * x = c * x * y := by
    rw [← hc]
    group
  calc (x * y) * (x * y) = x * (y * x) * y := by group
    _ = x * (c * x * y) * y := by rw [e]
    _ = (x * c) * x * y * y := by group
    _ = c * (x * x) * (y * y) := by rw [hcx x]; group

theorem sq_mem (x : D.P) : (x : E) * x = 1 ∨ (x : E) * x = Z.ζ := by
  have hK : ∀ x : D.P, D.InK ((x : E) * x) := fun x => (D.vec_ker (x * x)).1 (D.vec_sq x)
  let s : D.P → ZMod 2 := fun x => Z.nu ((x : E) * x)
  have hs_mul : ∀ x y : D.P, s (x * y) = s x + s y := by
    intro x y
    have hc := D.comm_mem_K y x
    have h1 : ((x * y : D.P) : E) * ((x * y : D.P) : E) =
        ⁅(y : E), (x : E)⁆ * ((x : E) * x) * ((y : E) * y) :=
      sq_mul_eq (rfl : (y : E) * x * (y : E)⁻¹ * (x : E)⁻¹ = ⁅(y : E), (x : E)⁆)
        (fun g => D.InK_comm hc g)
    have h2 : Z.nu ⁅(y : E), (x : E)⁆ = 0 := by
      refine (Z.nu_zero _ hc).2 ?_
      rcases Z.comm y x with h | h
      · exact Or.inl h
      · exact Or.inr h
    show Z.nu (((x * y : D.P) : E) * ((x * y : D.P) : E)) = _
    rw [h1, Z.nu_mul _ _ (D.InK_mul hc (hK x)) (hK y), Z.nu_mul _ _ hc (hK x), h2, zero_add]
  have hs_ker : ∀ x : D.P, D.vec x = 0 → s x = 0 := by
    intro x hx
    show Z.nu ((x : E) * x) = 0
    rw [D.InK_sq ((D.vec_ker x).1 hx)]
    exact (Z.nu_zero 1 (Or.inl rfl)).2 (Or.inl rfl)
  obtain ⟨φ, hφ⟩ := D.descend (M := ZMod 2) s hs_mul hs_ker
  have hinv : ∀ γ v, φ (D.ρ γ v) = φ v := by
    intro γ v
    obtain ⟨c, rfl⟩ := D.surj_p γ
    obtain ⟨y, rfl⟩ := D.vec_surj v
    rw [← D.vec_conj, hφ, hφ]
    show Z.nu (c * (y : E) * c⁻¹ * (c * (y : E) * c⁻¹)) = Z.nu ((y : E) * y)
    have : c * (y : E) * c⁻¹ * (c * (y : E) * c⁻¹) = (y : E) * y := by
      calc c * (y : E) * c⁻¹ * (c * (y : E) * c⁻¹) = c * ((y : E) * y) * c⁻¹ := by group
        _ = (y : E) * y := by rw [D.InK_comm (hK y) c, mul_inv_cancel_right]
    rw [this]
  have h0 := D.inv_functional_zero φ hinv
  have h1 : s x = 0 := by
    rw [← hφ, h0]
    rfl
  exact (Z.nu_zero _ (hK x)).1 h1


theorem exists_of_ab (v : Additive (Abelianization D.P)) :
    ∃ x : D.P, Additive.ofMul (Abelianization.of x) = v := by
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective v.toMul
  refine ⟨q, ?_⟩
  change Additive.ofMul (QuotientGroup.mk q : Abelianization D.P) = v
  rw [hq]
  rfl

theorem comm_G (x y : D.P) : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = (⟨Z.ζ, Z.zeta_mem⟩ : D.P) := by
  rcases Z.comm x y with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem sq_G (x : D.P) : x * x = 1 ∨ x * x = (⟨Z.ζ, Z.zeta_mem⟩ : D.P) := by
  rcases Z.sq_mem x with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem zeta_mem_commutator : (⟨Z.ζ, Z.zeta_mem⟩ : D.P) ∈ commutator D.P := by
  obtain ⟨x, y, hxy⟩ := D.exists_noncomm
  have h1 : ⁅x, y⁆ = (⟨Z.ζ, Z.zeta_mem⟩ : D.P) := by
    rcases Z.comm_G x y with h | h
    · exfalso
      apply hxy
      have : ⁅(x : E), (y : E)⁆ = 1 := congrArg Subtype.val h
      rw [this]
      exact Subgroup.one_mem _
    · exact h
  rw [← h1]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

theorem mem_zpowers_zeta {y : D.P} :
    y ∈ Subgroup.zpowers (⟨Z.ζ, Z.zeta_mem⟩ : D.P) ↔ y = 1 ∨ y = ⟨Z.ζ, Z.zeta_mem⟩ := by
  have hsq : (⟨Z.ζ, Z.zeta_mem⟩ : D.P) * ⟨Z.ζ, Z.zeta_mem⟩ = 1 := Subtype.ext Z.sq_zeta
  constructor
  · intro h
    let H : Subgroup D.P :=
      { carrier := {1, ⟨Z.ζ, Z.zeta_mem⟩}
        one_mem' := Or.inl rfl
        mul_mem' := by
          rintro a b (rfl | rfl) (rfl | rfl)
          · exact Or.inl (mul_one 1)
          · exact Or.inr (one_mul _)
          · exact Or.inr (mul_one _)
          · exact Or.inl hsq
        inv_mem' := by
          rintro a (rfl | rfl)
          · exact Or.inl inv_one
          · exact Or.inr (inv_eq_of_mul_eq_one_right hsq) }
    exact Subgroup.zpowers_le.2 (show (⟨Z.ζ, Z.zeta_mem⟩ : D.P) ∈ H from Or.inr rfl) h
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

include Z in
theorem n_not_mem_commutator : (⟨D.n, D.n_mem⟩ : D.P) ∉ commutator D.P := by
  intro h
  have hle : commutator D.P ≤ Subgroup.zpowers (⟨Z.ζ, Z.zeta_mem⟩ : D.P) := by
    unfold commutator
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    exact Z.mem_zpowers_zeta.2 (Z.comm_G g₁ g₂)
  rcases Z.mem_zpowers_zeta.1 (hle h) with h1 | h1
  · exact D.n_ne_one (congrArg Subtype.val h1)
  · exact Z.ne_n (congrArg Subtype.val h1).symm

include Z in
theorem exists_additive_n : ∃ l : D.P → ZMod 2, (∀ x y, l (x * y) = l x + l y) ∧
    l ⟨D.n, D.n_mem⟩ = 1 := by
  have hsq : ∀ v : Additive (Abelianization D.P), 2 • v = 0 := by
    intro v
    obtain ⟨x, rfl⟩ := exists_of_ab v
    rw [two_nsmul, ← ofMul_mul, ← map_mul]
    have hx : x * x ∈ commutator D.P := by
      rcases Z.sq_G x with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Z.zeta_mem_commutator
    rw [← Abelianization.ker_of] at hx
    rw [MonoidHom.mem_ker.1 hx]
    rfl
  let _ : Module (ZMod 2) (Additive (Abelianization D.P)) := AddCommGroup.zmodModule hsq
  have hnn : Additive.ofMul (Abelianization.of (⟨D.n, D.n_mem⟩ : D.P)) ≠ 0 := by
    intro h
    apply Z.n_not_mem_commutator
    rw [← Abelianization.ker_of]
    exact h
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual (ZMod 2) (Additive (Abelianization D.P)),
      f (Additive.ofMul (Abelianization.of (⟨D.n, D.n_mem⟩ : D.P))) ≠ 0 := by
    by_contra h
    apply hnn
    refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 fun f => ?_
    by_contra hf
    exact h ⟨f, hf⟩
  refine ⟨fun x => f (Additive.ofMul (Abelianization.of x)), fun x y => ?_, ?_⟩
  · simp only [map_mul, ofMul_mul, map_add]
  · rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1)
      (f (Additive.ofMul (Abelianization.of (⟨D.n, D.n_mem⟩ : D.P)))) with h | h
    · exact absurd h hf
    · exact h


theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

include Z in
theorem exists_invariant_additive : ∃ lam : D.P → ZMod 2, (∀ x y, lam (x * y) = lam x + lam y) ∧
    lam ⟨D.n, D.n_mem⟩ = 1 ∧ ∀ (c : E) (x : D.P), lam (MulAut.conjNormal c x) = lam x := by
  obtain ⟨l, hl, hln⟩ := Z.exists_additive_n
  have hl1 : l 1 = 0 := by
    have h := hl 1 1
    rw [mul_one] at h
    exact add_eq_left.1 h.symm
  have hlinv : ∀ x, l x⁻¹ = - l x := fun x => by
    have h := hl x x⁻¹
    rw [mul_inv_cancel, hl1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hlcomm : ∀ x y : D.P, l (x * y * x⁻¹ * y⁻¹) = 0 := fun x y => by
    rw [hl, hl, hl, hlinv, hlinv]
    abel
  let g : E → D.P → ZMod 2 := fun c a => l (MulAut.conjNormal c a) + l a
  have hg_add : ∀ c a b, g c (a * b) = g c a + g c b := fun c a b => by
    simp only [g, map_mul, hl]
    abel
  have hg_ker : ∀ c a, D.vec a = 0 → g c a = 0 := by
    intro c a ha
    have h1 : MulAut.conjNormal c a = a := by
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply]
      exact mul_inv_eq_iff_eq_mul.2 (D.InK_comm ((D.vec_ker a).1 ha) c)
    simp only [g, h1]
    exact CharTwo.add_self_eq_zero _
  choose F hF using fun c => D.descend (M := ZMod 2) (g c) (hg_add c) (hg_ker c)
  have hact : ∀ c d : E, ∀ a : D.P, MulAut.conjNormal (c * d) a =
      MulAut.conjNormal c (MulAut.conjNormal d a) := fun c d a => by
    rw [map_mul]
    rfl
  have hcoc : ∀ c d v, F (c * d) v = F c (D.ρ (D.p d) v) + F d v := by
    intro c d v
    obtain ⟨a, rfl⟩ := D.vec_surj v
    rw [← D.vec_conj, hF, hF, hF]
    simp only [g, hact]
    linear_combination (-(l (MulAut.conjNormal d a))) * two_eq_zero
  have hFP : ∀ q : E, q ∈ D.P → F q = 0 := by
    intro q hq
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, rfl⟩ := D.vec_surj v
    rw [hF]
    have h1 : MulAut.conjNormal q a = (⟨q, hq⟩ * a * ⟨q, hq⟩⁻¹ * a⁻¹ : D.P) * a := by
      refine Subtype.ext ?_
      rw [MulAut.conjNormal_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show l (MulAut.conjNormal q a) + l a = 0
    rw [h1, hl, hlcomm, zero_add]
    exact CharTwo.add_self_eq_zero _
  let Fb : Γ → Module.Dual (ZMod 2) V := fun γ => F (Function.surjInv D.surj_p γ)
  have hFb' : ∀ c, F c = Fb (D.p c) := by
    intro c
    set c' := Function.surjInv D.surj_p (D.p c) with hc'
    have hp' : D.p c' = D.p c := Function.surjInv_eq D.surj_p _
    have hq : c'⁻¹ * c ∈ D.P := by
      rw [← D.ker_p, MonoidHom.mem_ker, map_mul, map_inv, hp', inv_mul_cancel]
    have hp1 : D.p (c'⁻¹ * c) = 1 := by rw [map_mul, map_inv, hp', inv_mul_cancel]
    refine LinearMap.ext fun v => ?_
    have h2 := hcoc c' (c'⁻¹ * c) v
    rw [mul_inv_cancel_left, hFP _ hq, LinearMap.zero_apply, add_zero, hp1, map_one,
      Module.End.one_apply] at h2
    exact h2
  have hcocb : ∀ γ δ v, Fb (γ * δ) v = Fb γ (D.ρ δ v) + Fb δ v := by
    intro γ δ v
    obtain ⟨c, rfl⟩ := D.surj_p γ
    obtain ⟨d, rfl⟩ := D.surj_p δ
    rw [← map_mul, ← hFb', hcoc, hFb' c, hFb' d]
  obtain ⟨φ, hφ⟩ := D.ext1 Fb hcocb
  refine ⟨fun a => l a + φ (D.vec a), fun x y => ?_, ?_, fun c x => ?_⟩
  · simp only [hl, D.vec_mul, map_add]
    abel
  · have : D.vec (⟨D.n, D.n_mem⟩ : D.P) = 0 := (D.vec_ker _).2 (Or.inr (Or.inl rfl))
    simp only [this, map_zero, add_zero, hln]
  · have h1 := hφ (D.p c) (D.vec x)
    rw [← hFb', hF] at h1
    simp only [g] at h1
    show l (MulAut.conjNormal c x) + φ (D.vec (MulAut.conjNormal c x)) = l x + φ (D.vec x)
    rw [D.vec_conj]
    linear_combination h1 + (φ (D.ρ (D.p c) (D.vec x)) - l x - φ (D.vec x)) * two_eq_zero


theorem inK_iff (k : E) :
    D.InK k ↔ k = 1 ∨ k = D.n ∨ k = Z.ζ ∨ k = Z.ζ * D.n := by
  rcases Z.inK with h | h | h | h
  · exact absurd h Z.ne_one
  · exact absurd h Z.ne_n
  · rw [h]
    exact Iff.rfl
  · rw [h]
    unfold InK
    rw [D.zh_n_mul_n]
    tauto

end ZetaData

def kerAdd (h : D.P → ZMod 2) (hh : ∀ x y, h (x * y) = h x + h y) : Subgroup D.P where
  carrier := {a | h a = 0}
  one_mem' := by
    show h 1 = 0
    have h1 := hh 1 1
    rw [mul_one] at h1
    exact add_eq_left.1 h1.symm
  mul_mem' := by
    intro a b ha hb
    show h (a * b) = 0
    rw [hh]
    have ha' : h a = 0 := ha
    have hb' : h b = 0 := hb
    rw [ha', hb', add_zero]
  inv_mem' := by
    intro a ha
    show h a⁻¹ = 0
    have h1 := hh a a⁻¹
    have ha' : h a = 0 := ha
    have h2 : h 1 = 0 := by
      have h3 := hh 1 1
      rw [mul_one] at h3
      exact add_eq_left.1 h3.symm
    rw [mul_inv_cancel, h2, ha', zero_add] at h1
    exact h1.symm

theorem additive_commutator {h : D.P → ZMod 2} (hh : ∀ x y, h (x * y) = h x + h y)
    {g : D.P} (hg : g ∈ commutator D.P) : h g = 0 := by
  have hle : commutator D.P ≤ D.kerAdd h hh := by
    unfold commutator
    rw [Subgroup.commutator_le]
    intro x _ y _
    show h ⁅x, y⁆ = 0
    have hinv : ∀ z, h z⁻¹ = - h z := fun z => by
      have h1 := hh z z⁻¹
      rw [mul_inv_cancel] at h1
      have h2 : h 1 = 0 := by
        have h3 := hh 1 1
        rw [mul_one] at h3
        exact add_eq_left.1 h3.symm
      rw [h2] at h1
      exact eq_neg_of_add_eq_zero_right h1.symm
    rw [commutatorElement_def, hh, hh, hh, hinv, hinv]
    abel
  exact hle hg


theorem additive_one {h : D.P → ZMod 2} (hh : ∀ x y, h (x * y) = h x + h y) : h 1 = 0 := by
  have h1 := hh 1 1
  rw [mul_one] at h1
  exact add_eq_left.1 h1.symm

instance zpowers_n_normal : (Subgroup.zpowers D.n).Normal :=
  ⟨fun x hx g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [(Commute.zpow_right (D.n_comm g : Commute g D.n) k).mul_inv_cancel]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers D.n) k⟩

namespace ZetaData

variable {D} (Z : D.ZetaData)

include Z in
theorem exists_unique_complement :
    ∃! Q : Subgroup E, Q ≤ D.P ∧ (∀ c : E, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧
      Q ⊓ Subgroup.zpowers D.n = ⊥ ∧ Q ⊔ Subgroup.zpowers D.n = D.P := by
  classical
  obtain ⟨lam, hlam, hlamn, hlaminv⟩ := Z.exists_invariant_additive
  have hlam1 : lam 1 = 0 := D.additive_one hlam
  let Qex : Subgroup E := (D.kerAdd lam hlam).map D.P.subtype
  have hmemQ : ∀ x : E, x ∈ Qex ↔ ∃ h : x ∈ D.P, lam ⟨x, h⟩ = 0 := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, h0⟩
      exact ⟨⟨x, h⟩, h0, rfl⟩
  have hn_one : (1 : ZMod 2) ≠ 0 := by decide
  refine ⟨Qex, ⟨fun x hx => ((hmemQ x).1 hx).1, ?_, ?_, ?_⟩, fun Q' hQ' => ?_⟩
  · intro c q hq
    obtain ⟨hqP, hq0⟩ := (hmemQ q).1 hq
    refine (hmemQ _).2 ⟨D.normal.conj_mem q hqP c, ?_⟩
    have := hlaminv c ⟨q, hqP⟩
    rw [← hq0]
    exact this
  · refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    obtain ⟨hyQ, hyn⟩ := hy
    rcases D.mem_zpowers_n.1 hyn with rfl | rfl
    · rfl
    · obtain ⟨_, h0⟩ := (hmemQ _).1 hyQ
      exact absurd (hlamn.symm.trans h0) hn_one
  · apply le_antisymm
    · exact sup_le (fun x hx => ((hmemQ x).1 hx).1) (Subgroup.zpowers_le.2 D.n_mem)
    · intro a ha
      by_cases h0 : lam ⟨a, ha⟩ = 0
      · exact Subgroup.mem_sup_left ((hmemQ a).2 ⟨ha, h0⟩)
      · have h1 : lam ⟨a, ha⟩ = 1 := by
          rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (lam ⟨a, ha⟩) with h | h
          · exact absurd h h0
          · exact h
        have hqn : a * D.n ∈ Qex := by
          refine (hmemQ _).2 ⟨D.P.mul_mem ha D.n_mem, ?_⟩
          have : (⟨a * D.n, D.P.mul_mem ha D.n_mem⟩ : D.P) = ⟨a, ha⟩ * ⟨D.n, D.n_mem⟩ := rfl
          rw [this, hlam, h1, hlamn]
          decide
        have : a = a * D.n * D.n := by rw [mul_assoc, D.n_sq, mul_one]
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hqn)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.n))
  · obtain ⟨hQP, hQinv, hQinf, hQsup⟩ := hQ'
    have hn' : D.n ∉ Q' := by
      intro h
      have : D.n ∈ Q' ⊓ Subgroup.zpowers D.n := ⟨h, Subgroup.mem_zpowers D.n⟩
      rw [hQinf] at this
      exact D.n_ne_one (Subgroup.mem_bot.1 this)
    have hdec : ∀ a : E, a ∈ D.P → ∃ q ∈ Q', ∃ z : E, (z = 1 ∨ z = D.n) ∧ a = q * z := by
      intro a ha
      have h1 : a ∈ (Q' ⊔ Subgroup.zpowers D.n : Subgroup E) := by rw [hQsup]; exact ha
      have h2 := Subgroup.mul_normal Q' (Subgroup.zpowers D.n)
      rw [← SetLike.mem_coe, h2] at h1
      obtain ⟨q, hq, z, hz, rfl⟩ := Set.mem_mul.1 h1
      exact ⟨q, hq, z, D.mem_zpowers_n.1 hz, rfl⟩
    let lam' : D.P → ZMod 2 := fun a => if (a : E) ∈ Q' then 0 else 1
    have hlam'_decomp : ∀ (a : D.P) (q z : E), q ∈ Q' → (z = 1 ∨ z = D.n) → (a : E) = q * z →
        lam' a = toZ2 z := by
      intro a q z hq hz haz
      rcases hz with rfl | rfl
      · rw [mul_one] at haz
        have : (a : E) ∈ Q' := haz ▸ hq
        simp [lam', this, toZ2]
      · have hanot : (a : E) ∉ Q' := by
          intro ha
          apply hn'
          have : D.n = q⁻¹ * a := by rw [haz, inv_mul_cancel_left]
          rw [this]
          exact Q'.mul_mem (Q'.inv_mem hq) ha
        simp [lam', hanot, toZ2, D.n_ne_one]
    have hlam'_add : ∀ a b : D.P, lam' (a * b) = lam' a + lam' b := by
      intro a b
      obtain ⟨q₁, hq₁, z₁, hz₁, ha⟩ := hdec a a.2
      obtain ⟨q₂, hq₂, z₂, hz₂, hb⟩ := hdec b b.2
      have hz12 : z₁ * z₂ = 1 ∨ z₁ * z₂ = D.n :=
        D.mem_zpowers_n.1
          (Subgroup.mul_mem _ (D.mem_zpowers_n.2 hz₁) (D.mem_zpowers_n.2 hz₂))
      have hab : ((a * b : D.P) : E) = (q₁ * q₂) * (z₁ * z₂) := by
        show (a : E) * b = _
        rw [ha, hb]
        calc q₁ * z₁ * (q₂ * z₂) = q₁ * (z₁ * q₂) * z₂ := by group
          _ = q₁ * (q₂ * z₁) * z₂ := by rw [← D.central_of_zpowers hz₁ q₂]
          _ = q₁ * q₂ * (z₁ * z₂) := by group
      rw [hlam'_decomp (a * b) (q₁ * q₂) (z₁ * z₂) (Q'.mul_mem hq₁ hq₂) hz12 hab,
        hlam'_decomp a q₁ z₁ hq₁ hz₁ ha, hlam'_decomp b q₂ z₂ hq₂ hz₂ hb]
      exact D.toZ2_mul hz₁ hz₂
    have hlam'_inv : ∀ (c : E) (a : D.P), lam' (MulAut.conjNormal c a) = lam' a := by
      intro c a
      have hiff : ((MulAut.conjNormal c a : D.P) : E) ∈ Q' ↔ (a : E) ∈ Q' := by
        rw [MulAut.conjNormal_apply]
        constructor
        · intro h
          have := hQinv c⁻¹ _ h
          simpa [mul_assoc] using this
        · exact hQinv c _
      simp only [lam', hiff]
    have hlam'_n : lam' ⟨D.n, D.n_mem⟩ = 1 := by simp [lam', hn']
    let d : D.P → ZMod 2 := fun a => lam a + lam' a
    have hd_add : ∀ x y, d (x * y) = d x + d y := by
      intro x y
      simp only [d, hlam, hlam'_add]
      abel
    have hd_inv : ∀ (c : E) (x : D.P), d (MulAut.conjNormal c x) = d x := by
      intro c x
      simp only [d, hlaminv, hlam'_inv]
    have hdn : d ⟨D.n, D.n_mem⟩ = 0 := by
      show lam ⟨D.n, D.n_mem⟩ + lam' ⟨D.n, D.n_mem⟩ = 0
      rw [hlamn, hlam'_n]
      decide
    have hdz : d ⟨Z.ζ, Z.zeta_mem⟩ = 0 := D.additive_commutator hd_add Z.zeta_mem_commutator
    have hd_K : ∀ a : D.P, D.vec a = 0 → d a = 0 := by
      intro a ha
      rcases (Z.inK_iff _).1 ((D.vec_ker a).1 ha) with h | h | h | h
      · have : a = 1 := Subtype.ext h
        rw [this]
        show lam 1 + lam' 1 = 0
        rw [hlam1, D.additive_one hlam'_add, add_zero]
      · have : a = ⟨D.n, D.n_mem⟩ := Subtype.ext h
        rw [this]
        exact hdn
      · have : a = ⟨Z.ζ, Z.zeta_mem⟩ := Subtype.ext h
        rw [this]
        exact hdz
      · have : a = ⟨Z.ζ, Z.zeta_mem⟩ * ⟨D.n, D.n_mem⟩ := Subtype.ext h
        rw [this, hd_add, hdz, hdn, add_zero]
    obtain ⟨φ, hφ⟩ := D.descend (M := ZMod 2) d hd_add hd_K
    have hφinv : ∀ γ v, φ (D.ρ γ v) = φ v := by
      intro γ v
      obtain ⟨c, rfl⟩ := D.surj_p γ
      obtain ⟨y, rfl⟩ := D.vec_surj v
      rw [← D.vec_conj, hφ, hφ, hd_inv]
    have hφ0 := D.inv_functional_zero φ hφinv
    have hd0 : ∀ a, d a = 0 := fun a => by
      rw [← hφ, hφ0]
      rfl
    have hlamlam' : ∀ a, lam a = lam' a := fun a => by
      have h1 : lam a + lam' a = 0 := hd0 a
      rw [eq_neg_of_add_eq_zero_left h1, ZMod.neg_eq_self_mod_two]
    ext x
    constructor
    · intro hx
      have hxP := hQP hx
      refine (hmemQ x).2 ⟨hxP, ?_⟩
      rw [hlamlam']
      simp [lam', hx]
    · intro hx
      obtain ⟨hxP, hx0⟩ := (hmemQ x).1 hx
      by_contra hxQ
      have h1 : lam' ⟨x, hxP⟩ = 1 := by simp [lam', hxQ]
      rw [← hlamlam'] at h1
      exact hn_one (h1.symm.trans hx0)

end ZetaData


end LiftData

theorem exists_unique_invariant_complement
    {E Γ V : Type*} [Group E] [Group Γ] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    [Group.IsPerfect Γ]
    (P : Subgroup E) [P.Normal] (p : E →* Γ) (hp : Function.Surjective p) (hpk : p.ker = P)
    (ρ : Representation (ZMod 2) Γ V) (hdim : 1 < Module.finrank (ZMod 2) V)
    (n zh : E) (hn : n ∈ Subgroup.center E) (hn2 : n * n = 1) (hn1 : n ≠ 1)
    (hnP : n ∈ P) (hzhP : zh ∈ P) (hzh1 : zh ≠ 1) (hzhn : zh ≠ n)
    (vec : P → V) (hvec_mul : ∀ x y, vec (x * y) = vec x + vec y)
    (hvec_conj : ∀ (c : E) (x : P), vec (MulAut.conjNormal c x) = ρ (p c) (vec x))
    (hvec_surj : Function.Surjective vec)
    (hvec_ker : ∀ x : P, vec x = 0 ↔
      (x : E) = 1 ∨ (x : E) = n ∨ (x : E) = zh ∨ (x : E) = zh * n)
    (hcenter : ∀ x : P, vec x = 0 ↔ ∀ y : P, ⁅(x : E), (y : E)⁆ ∈ Subgroup.zpowers n)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ γ : Γ, ∀ w ∈ W, ρ γ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hend : ∀ ψ : V →ₗ[ZMod 2] V, (∀ γ v, ψ (ρ γ v) = ρ γ (ψ v)) → ψ = 0 ∨ ψ = 1)
    (hext : ∀ f : Γ → Module.Dual (ZMod 2) V,
      (∀ g h v, f (g * h) v = f g (ρ h v) + f h v) →
      ∃ φ : Module.Dual (ZMod 2) V, ∀ g v, f g v = φ (ρ g v) - φ v) :
    ∃! Q : Subgroup E, Q ≤ P ∧ (∀ c : E, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧
      Q ⊓ Subgroup.zpowers n = ⊥ ∧ Q ⊔ Subgroup.zpowers n = P := by
  let D : LiftData E Γ V :=
    { P := P, p := p, ρ := ρ, vec := vec, n := n, zh := zh, surj_p := hp, ker_p := hpk,
      perfect := inferInstance, finV := inferInstance, dim := hdim, n_central := hn,
      n_sq := hn2, n_ne_one := hn1, n_mem := hnP, zh_mem := hzhP, zh_ne_one := hzh1,
      zh_ne_n := hzhn, vec_mul := hvec_mul, vec_conj := hvec_conj, vec_surj := hvec_surj,
      vec_ker := hvec_ker, center := hcenter, irr := hirr, end_ := hend, ext1 := hext }
  obtain ⟨Z⟩ := D.exists_zetaData
  exact Z.exists_unique_complement

end CFSG.Monster.Schur
