module

public import CFSG.RankThree.PartOne.TAIL.Basic

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

@[expose] def Xs (A B : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (A : Set G) ∧ (∀ β ∈ B, x * β * x⁻¹ = β) ∧
    ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ B}
  one_mem' := ⟨Subgroup.one_mem _, fun β _ => by group, fun a _ => by simp⟩
  mul_mem' := by
    rintro x x' ⟨hxN, hxB, hxA⟩ ⟨hx'N, hx'B, hx'A⟩
    refine ⟨Subgroup.mul_mem _ hxN hx'N, fun β hβ => ?_, fun a ha => ?_⟩
    · calc x * x' * β * (x * x')⁻¹ = x * (x' * β * x'⁻¹) * x⁻¹ := by group
        _ = β := by rw [hx'B β hβ, hxB β hβ]
    · have hu := hx'A a ha
      have hv := hxA a ha
      have key : x * x' * a * (x * x')⁻¹ * a⁻¹ =
          (x * (x' * a * x'⁻¹ * a⁻¹) * x⁻¹) * (x * a * x⁻¹ * a⁻¹) := by group
      rw [key, hxB _ hu]
      exact B.mul_mem hu hv
  inv_mem' := by
    rintro x ⟨hxN, hxB, hxA⟩
    refine ⟨Subgroup.inv_mem _ hxN, fun β hβ => ?_, fun a ha => ?_⟩
    · have := hxB β hβ
      calc x⁻¹ * β * x⁻¹⁻¹ = x⁻¹ * (x * β * x⁻¹) * x⁻¹⁻¹ := by rw [this]
        _ = β := by group
    · have ha' : x⁻¹ * a * x ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) a).mp ha
        simpa using this
      have hv := hxA _ ha'
      have e : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = (x * (x⁻¹ * a * x) * x⁻¹ * (x⁻¹ * a * x)⁻¹)⁻¹ := by group
      rw [e]
      exact B.inv_mem hv

theorem Xs_le_normalizer {A B : Subgroup G} : Xs A B ≤ Subgroup.normalizer (A : Set G) :=
  fun _ hx => hx.1

theorem Xs_le_centralizer {A B : Subgroup G} : Xs A B ≤ Subgroup.centralizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro β hβ
  have := hx.2.1 β hβ
  calc β * x = (x * β * x⁻¹) * x := by rw [this]
    _ = x * β := by group

theorem centralizer_le_Xs {A B : Subgroup G} (hBA : B ≤ A) :
    Subgroup.centralizer (A : Set G) ≤ Xs A B := by
  intro x hx
  have hxc := (Subgroup.mem_centralizer_iff.mp hx)
  refine ⟨Subgroup.centralizer_le_normalizer (A : Set G) hx, fun β hβ => ?_, fun a ha => ?_⟩
  · have := hxc β (hBA hβ)
    calc x * β * x⁻¹ = (β * x) * x⁻¹ := by rw [this]
      _ = β := by group
  · have := hxc a ha
    have e : x * a * x⁻¹ * a⁻¹ = 1 := by
      calc x * a * x⁻¹ * a⁻¹ = (a * x) * x⁻¹ * a⁻¹ := by rw [this]
        _ = 1 := by group
    rw [e]; exact B.one_mem

theorem conj_mem_Xs {A B : Subgroup G} {n x : G} (hnA : n ∈ Subgroup.normalizer (A : Set G))
    (hnB : n ∈ Subgroup.normalizer (B : Set G)) (hx : x ∈ Xs A B) : n * x * n⁻¹ ∈ Xs A B := by
  obtain ⟨hxN, hxB, hxA⟩ := hx
  refine ⟨?_, fun β hβ => ?_, fun a ha => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnA hxN) (Subgroup.inv_mem _ hnA)
  · have hβ' : n⁻¹ * β * n ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnB) β).mp hβ
      simpa using this
    have := hxB _ hβ'
    calc n * x * n⁻¹ * β * (n * x * n⁻¹)⁻¹ = n * (x * (n⁻¹ * β * n) * x⁻¹) * n⁻¹ := by group
      _ = β := by rw [this]; group
  · have ha' : n⁻¹ * a * n ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnA) a).mp ha
      simpa using this
    have hv := hxA _ ha'
    have e : n * x * n⁻¹ * a * (n * x * n⁻¹)⁻¹ * a⁻¹ =
        n * (x * (n⁻¹ * a * n) * x⁻¹ * (n⁻¹ * a * n)⁻¹) * n⁻¹ := by group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp hnB _).mp hv
    exact this

@[expose] def eps (c x : G) : G := x * c * x⁻¹ * c⁻¹

theorem eps_one {c : G} : eps c (1 : G) = 1 := by unfold eps; group

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀)

include h

theorem eps_mem {x : G} (hx : x ∈ Xs A B) : eps c x ∈ B := hx.2.2 c h.c_mem

theorem eps_mul {x x' : G} (hx : x ∈ Xs A B) (hx' : x' ∈ Xs A B) :
    eps c (x * x') = eps c x * eps c x' := by
  have hu := h.eps_mem hx'
  have e : eps c (x * x') = (x * eps c x' * x⁻¹) * eps c x := by unfold eps; group
  rw [e, hx.2.1 _ hu]
  exact h.B_comm hu (h.eps_mem hx)

@[expose] def epsHom : ↥(Xs A B) →* ↥B where
  toFun x := ⟨eps c x, h.eps_mem x.2⟩
  map_one' := Subtype.ext (by simpa using eps_one (c := c))
  map_mul' x x' := Subtype.ext (by simpa using h.eps_mul x.2 x'.2)

theorem epsHom_apply (x : ↥(Xs A B)) : ((h.epsHom x : ↥B) : G) = eps c x := rfl

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL
