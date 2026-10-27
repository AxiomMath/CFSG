module

public import CFSG.RankThree.PartOne.SEITZ9.SzField
public import CFSG.RankThree.PartOne.SEITZ9.SzClose

public section

namespace CFSG.RankThree.PartOne.SEITZ9

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K]

section Coordinates

@[expose] def uCoord (H : Subgroup (suzukiGroup a K)) : Set K :=
  {x | ∃ y, suzukiSElt a K x y ∈ H}

@[expose] def zCoord (H : Subgroup (suzukiGroup a K)) : Set K :=
  {z | suzukiSElt a K 0 z ∈ H}

variable [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Subgroup (suzukiGroup a K)}
include hK

theorem zero_mem_zCoord : (0 : K) ∈ zCoord H := by
  show suzukiSElt a K 0 0 ∈ H
  rw [suzukiSElt_zero_zero hK]
  exact H.one_mem

theorem zCoord_add {x y : K} (hx : x ∈ zCoord H) (hy : y ∈ zCoord H) : x + y ∈ zCoord H := by
  show suzukiSElt a K 0 (x + y) ∈ H
  have := H.mul_mem hx hy
  rw [suzukiSElt_mul hK] at this
  simpa using this

theorem uCoord_add {x x' : K} (hx : x ∈ uCoord H) (hx' : x' ∈ uCoord H) :
    x + x' ∈ uCoord H := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨y', hy'⟩ := hx'
  refine ⟨y + y' + x ^ 2 ^ (a + 1) * x', ?_⟩
  rw [← suzukiSElt_mul hK]
  exact H.mul_mem hy hy'

theorem zCoord_mul_of_mem {u v : K} {l : Kˣ}
    (h : suzukiSElt a K u v * suzukiDElt a K l ∈ H) {z : K} (hz : z ∈ zCoord H) :
    (l : K) ^ (2 ^ (a + 1) + 1) * z ∈ zCoord H := by
  have hc := suzukiSElt_zero_commute hK z u v
  have e1 : (suzukiSElt a K u v)⁻¹ * suzukiSElt a K 0 z * suzukiSElt a K u v =
      suzukiSElt a K 0 z := by
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hconj : (suzukiSElt a K u v * suzukiDElt a K l)⁻¹ * suzukiSElt a K 0 z *
      (suzukiSElt a K u v * suzukiDElt a K l) =
      suzukiSElt a K 0 ((l : K) ^ (2 ^ (a + 1) + 1) * z) := by
    calc (suzukiSElt a K u v * suzukiDElt a K l)⁻¹ * suzukiSElt a K 0 z *
        (suzukiSElt a K u v * suzukiDElt a K l)
        = (suzukiDElt a K l)⁻¹ * ((suzukiSElt a K u v)⁻¹ * suzukiSElt a K 0 z *
            suzukiSElt a K u v) * suzukiDElt a K l := by group
      _ = (suzukiDElt a K l)⁻¹ * suzukiSElt a K 0 z * suzukiDElt a K l := by rw [e1]
      _ = _ := by rw [suzukiDElt_conj hK, mul_zero]
  show suzukiSElt a K 0 _ ∈ H
  rw [← hconj]
  exact H.mul_mem (H.mul_mem (H.inv_mem h) hz) h

theorem uCoord_mul_of_mem {u v : K} {l : Kˣ}
    (h : suzukiSElt a K u v * suzukiDElt a K l ∈ H) {x : K} (hx : x ∈ uCoord H) :
    (l : K) * x ∈ uCoord H := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  obtain ⟨y1, hy1⟩ : ∃ y1, (suzukiSElt a K u v)⁻¹ * suzukiSElt a K x y * suzukiSElt a K u v =
      suzukiSElt a K x y1 :=
    ⟨_, by
      rw [suzukiSElt_inv hK, suzukiSElt_mul hK, suzukiSElt_mul hK]
      exact congrArg₂ (suzukiSElt a K) (by linear_combination u * h2) rfl⟩
  have hconj : (suzukiSElt a K u v * suzukiDElt a K l)⁻¹ * suzukiSElt a K x y *
      (suzukiSElt a K u v * suzukiDElt a K l) =
      suzukiSElt a K ((l : K) * x) ((l : K) ^ (2 ^ (a + 1) + 1) * y1) := by
    calc (suzukiSElt a K u v * suzukiDElt a K l)⁻¹ * suzukiSElt a K x y *
        (suzukiSElt a K u v * suzukiDElt a K l)
        = (suzukiDElt a K l)⁻¹ * ((suzukiSElt a K u v)⁻¹ * suzukiSElt a K x y *
            suzukiSElt a K u v) * suzukiDElt a K l := by group
      _ = (suzukiDElt a K l)⁻¹ * suzukiSElt a K x y1 * suzukiDElt a K l := by rw [hy1]
      _ = _ := suzukiDElt_conj hK l x y1
  refine ⟨(l : K) ^ (2 ^ (a + 1) + 1) * y1, ?_⟩
  rw [← hconj]
  exact H.mul_mem (H.mul_mem (H.inv_mem h) hy) h

end Coordinates

section Main

variable [Finite K] {k : Subfield K} {p : ℕ}

theorem suzuki_unipotent_of_irrational_torus (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hKk : Nat.card K = Nat.card k ^ p) (H : Subgroup (suzukiGroup a K))
    (hUk : ∀ u ∈ k, ∀ v ∈ k, suzukiSElt a K u v ∈ H)
    (hTk : ∀ l : Kˣ, (l : K) ∈ k → suzukiDElt a K l ∈ H) {u₀ v₀ : K} {l₀ : Kˣ}
    (hl₀ : (l₀ : K) ∉ k) (h₀ : suzukiSElt a K u₀ v₀ * suzukiDElt a K l₀ ∈ H) (u v : K) :
    suzukiSElt a K u v ∈ H := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  have hD : ∀ l : Kˣ, (l : K) ∈ k → suzukiSElt a K 0 0 * suzukiDElt a K l ∈ H := fun l hl => by
    rw [suzukiSElt_zero_zero hK, one_mul]
    exact hTk l hl
  have hZ : zCoord H = Set.univ := by
    refine eq_univ_of_smul_closed hp hKk (zCoord H) (hUk 0 k.zero_mem 1 k.one_mem)
      (fun x hx y hy => zCoord_add hK hx hy) ?_
      (μ := (l₀ : K) ^ (2 ^ (a + 1) + 1)) (fun x hx => zCoord_mul_of_mem hK h₀ hx) ?_
    · intro c hc x hx
      obtain ⟨κ, hκ, rfl⟩ := exists_pow_theta_succ_eq (a := a) hK hc
      by_cases hκ0 : κ = 0
      · subst hκ0
        simpa using zero_mem_zCoord hK
      · simpa using zCoord_mul_of_mem hK (hD (Units.mk0 κ hκ0) hκ) hx
    · intro hμ
      exact hl₀ (mem_of_pow_theta_succ_mem hK hμ)
  have hV : uCoord H = Set.univ := by
    refine eq_univ_of_smul_closed hp hKk (uCoord H) ⟨0, hUk 1 k.one_mem 0 k.zero_mem⟩
      (fun x hx y hy => uCoord_add hK hx hy) ?_
      (μ := (l₀ : K)) (fun x hx => uCoord_mul_of_mem hK h₀ hx) hl₀
    intro c hc x hx
    by_cases hc0 : c = 0
    · subst hc0
      refine ⟨0, ?_⟩
      rw [zero_mul, suzukiSElt_zero_zero hK]
      exact H.one_mem
    · simpa using uCoord_mul_of_mem hK (hD (Units.mk0 c hc0) hc) hx
  obtain ⟨y, hy⟩ : u ∈ uCoord H := by rw [hV]; trivial
  have hz : v + y ∈ zCoord H := by rw [hZ]; trivial
  have e : suzukiSElt a K u y * suzukiSElt a K 0 (v + y) = suzukiSElt a K u v := by
    rw [suzukiSElt_mul hK]
    exact congrArg₂ (suzukiSElt a K) (by simp) (by linear_combination y * h2)
  rw [← e]
  exact H.mul_mem hy hz

theorem suzuki_eq_top_of_irrational_torus (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hKk : Nat.card K = Nat.card k ^ p) (H : Subgroup (suzukiGroup a K))
    (hUk : ∀ u ∈ k, ∀ v ∈ k, suzukiSElt a K u v ∈ H)
    (hTk : ∀ l : Kˣ, (l : K) ∈ k → suzukiDElt a K l ∈ H) (hW : suzukiWElt a K ∈ H)
    {u₀ v₀ : K} {l₀ : Kˣ} (hl₀ : (l₀ : K) ∉ k)
    (h₀ : suzukiSElt a K u₀ v₀ * suzukiDElt a K l₀ ∈ H) : H = ⊤ :=
  suzuki_eq_top_of_unipotent_weyl hK H
    (suzuki_unipotent_of_irrational_torus hK hp hKk H hUk hTk hl₀ h₀) hW

end Main

end CFSG.RankThree.PartOne.SEITZ9
