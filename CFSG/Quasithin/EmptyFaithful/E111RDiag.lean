module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.E2.E22N.E111R

variable {G : Type*} [Group G]

@[expose] def DiagComm (S C : Subgroup G) : Prop :=
  ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → ∀ x ∈ S, ∀ y ∈ S,
    Commute ((c : G) * x * c⁻¹) ((c' : G) * y * c'⁻¹)

theorem multiset_noncommProd_congr {β : Type*} [Monoid β] {s s' : Multiset β} (h : s = s')
    (comm comm') : s.noncommProd comm = s'.noncommProd comm' := by
  subst h
  rfl

theorem noncommProd_univ_comp_equiv {α β : Type*} [Fintype α] [Monoid β] (f : α → β) (e : α ≃ α)
    (comm₁ comm₂) :
    (Finset.univ : Finset α).noncommProd (f ∘ e) comm₁ = Finset.univ.noncommProd f comm₂ := by
  unfold Finset.noncommProd
  apply multiset_noncommProd_congr
  rw [← Multiset.map_map]
  congr 1
  simp

variable {S C : Subgroup G} [Fintype ↥C]

theorem DiagComm.pairwise (hC : DiagComm S C) (x y : ↥S) :
    ((Finset.univ : Finset ↥C) : Set ↥C).Pairwise fun a b =>
      Commute ((a : G) * x * (a : G)⁻¹) ((b : G) * y * (b : G)⁻¹) :=
  fun a _ b _ hab => hC a a.2 b b.2 (fun h => hab (Subtype.ext h)) x x.2 y y.2

@[expose] noncomputable def diagHom (S C : Subgroup G) [Fintype ↥C] (hC : DiagComm S C) :
    ↥S →* G where
  toFun x := (Finset.univ : Finset ↥C).noncommProd (fun c => (c : G) * x * (c : G)⁻¹)
    (hC.pairwise x x)
  map_one' := by
    rw [Finset.noncommProd_eq_pow_card _ _ _ 1 (fun c _ => by simp), one_pow]
  map_mul' x y := by
    rw [← Finset.noncommProd_mul_distrib _ _ (hC.pairwise x x) (hC.pairwise y y)
      (fun a _ b _ hab => hC a a.2 b b.2 (fun h => hab (Subtype.ext h)) y y.2 x x.2)]
    refine Finset.noncommProd_congr rfl (fun c _ => ?_) _
    simp [mul_assoc]

theorem diagHom_apply (hC : DiagComm S C) (x : ↥S) :
    diagHom S C hC x = (Finset.univ : Finset ↥C).noncommProd
      (fun c => (c : G) * x * (c : G)⁻¹) (hC.pairwise x x) := rfl

theorem inv_mul_diagHom_mem (hC : DiagComm S C) (x : ↥S) :
    (x : G)⁻¹ * diagHom S C hC x ∈ Subgroup.centralizer (S : Set G) := by
  classical
  rw [diagHom_apply, ← Finset.mul_noncommProd_erase _ (Finset.mem_univ (1 : ↥C))]
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, inv_mul_cancel_left]
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  refine (Finset.noncommProd_commute _ _ _ s fun c hc => ?_).eq
  have hc1 : (c : G) ≠ 1 := fun h => (Finset.mem_erase.mp hc).1 (Subtype.ext h)
  have := hC 1 C.one_mem c c.2 (Ne.symm hc1) s hs x x.2
  simpa using this

theorem conj_diagHom_of_mem (hC : DiagComm S C) (x : ↥S) {c₀ : G} (hc₀ : c₀ ∈ C) :
    c₀ * diagHom S C hC x * c₀⁻¹ = diagHom S C hC x := by
  have h1 : c₀ * diagHom S C hC x * c₀⁻¹ = MulAut.conj c₀ (diagHom S C hC x) := rfl
  rw [h1, diagHom_apply, Finset.map_noncommProd]
  set e : ↥C ≃ ↥C := Equiv.mulLeft (⟨c₀, hc₀⟩ : ↥C)
  have key := noncommProd_univ_comp_equiv (fun c : ↥C => (c : G) * x * (c : G)⁻¹) e
    (fun a _ b _ hab => hC.pairwise x x (Finset.mem_coe.mpr (Finset.mem_univ (e a)))
      (Finset.mem_coe.mpr (Finset.mem_univ (e b))) (fun h => hab (e.injective h)))
    (hC.pairwise x x)
  rw [← key]
  refine Finset.noncommProd_congr rfl (fun c _ => ?_) _
  simp [e, MulAut.conj_apply, mul_assoc]

theorem conj_diagHom_of_comm (hC : DiagComm S C) (x : ↥S) {h : G}
    (hhS : h ∈ Subgroup.normalizer (S : Set G)) (hhC : ∀ c ∈ C, h * c = c * h) :
    h * diagHom S C hC x * h⁻¹ =
      diagHom S C hC ⟨h * x * h⁻¹, (Subgroup.mem_normalizer_iff.mp hhS x).mp x.2⟩ := by
  have h1 : h * diagHom S C hC x * h⁻¹ = MulAut.conj h (diagHom S C hC x) := rfl
  rw [h1, diagHom_apply, Finset.map_noncommProd, diagHom_apply]
  refine Finset.noncommProd_congr rfl (fun c _ => ?_) _
  have hc := hhC c c.2
  have hc' : h⁻¹ * (c : G) = c * h⁻¹ := by
    calc h⁻¹ * (c : G) = h⁻¹ * (c * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * c) * h⁻¹ := by rw [hc]
      _ = c * h⁻¹ := by group
  simp only [MulAut.conj_apply]
  calc h * (c * x * (c : G)⁻¹) * h⁻¹ = (h * c) * x * ((c : G)⁻¹ * h⁻¹) := by group
    _ = (c * h) * x * (h⁻¹ * (c : G)⁻¹) := by
        rw [hc, show (c : G)⁻¹ * h⁻¹ = h⁻¹ * (c : G)⁻¹ by
          rw [← mul_inv_rev, ← mul_inv_rev, hc]]
    _ = c * (h * x * h⁻¹) * (c : G)⁻¹ := by group

theorem commute_conj_diagHom (hC : DiagComm S C) {g : G}
    (hg : ∀ c ∈ C, ∀ c' ∈ C, ∀ x ∈ S, ∀ y ∈ S,
      Commute (g * c * x * (g * c)⁻¹) ((c' : G) * y * c'⁻¹)) (x y : ↥S) :
    Commute (g * diagHom S C hC x * g⁻¹) (diagHom S C hC y) := by
  have h1 : g * diagHom S C hC x * g⁻¹ = MulAut.conj g (diagHom S C hC x) := rfl
  rw [h1, diagHom_apply, Finset.map_noncommProd, diagHom_apply]
  refine Finset.noncommProd_commute _ _ _ _ fun c' _ => ?_
  refine (Finset.noncommProd_commute _ _ _ _ fun c _ => ?_).symm
  have h2 : g * (c * x * (c : G)⁻¹) * g⁻¹ = g * c * x * (g * c)⁻¹ := by group
  simp only [MulAut.conj_apply]
  rw [h2]
  exact (hg c c.2 c' c'.2 x x.2 y y.2).symm

theorem diagHom_injective (hC : DiagComm S C)
    (hZ : ∀ x ∈ S, x ∈ Subgroup.centralizer (S : Set G) → x = 1) :
    Function.Injective (diagHom S C hC) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h := inv_mul_diagHom_mem hC x
  rw [hx, mul_one] at h
  have h1 := hZ _ (S.inv_mem x.2) h
  rw [Subgroup.mem_bot]
  exact Subtype.ext (inv_eq_one.mp h1)

theorem diagHom_mem (hC : DiagComm S C) {Y : Subgroup G} (hSY : S ≤ Y)
    (hCY : ∀ c ∈ C, ∀ y ∈ Y, (c : G) * y * c⁻¹ ∈ Y) (x : ↥S) : diagHom S C hC x ∈ Y := by
  rw [diagHom_apply]
  exact Subgroup.noncommProd_mem _ _ fun c _ => hCY c c.2 x (hSY x.2)

theorem diagHom_mem_of (hC : DiagComm S C) {Y : Subgroup G} (x : ↥S)
    (hx : ∀ c ∈ C, (c : G) * x * c⁻¹ ∈ Y) : diagHom S C hC x ∈ Y := by
  rw [diagHom_apply]
  exact Subgroup.noncommProd_mem _ _ fun c _ => hx c c.2

end CFSG.Quasithin.E2.E22N.E111R
