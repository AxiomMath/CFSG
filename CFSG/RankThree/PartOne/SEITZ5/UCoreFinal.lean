module

public import CFSG.RankThree.PartOne.SEITZ5.UCount
public import CFSG.RankThree.PartOne.SEITZ5.UCenter
public import CFSG.RankThree.PartOne.SEITZ5.UDickson

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_isTv_z [Finite K] [CharP K 2] {k : Subfield K}
    (hσ : ∀ c, σ (σ c) = c) (hk4 : Nat.card k = 4) (hr2 : Nat.card (ratFix σ k) = 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p)
    {P : Frame σ n} (hz0 : P.z ≠ 0) {H : Subgroup (SUid σ n)} {ω : K} (hωk : ω ∈ k)
    (hω : σ ω = ω ^ 2) (hω2 : ω ^ 2 + ω + 1 = 0) {x y γ : fixSub σ} {ρ ζ : K} (hρ : ρ ∉ k)
    (hζ : ζ ≠ 0) (hρxy : ρ = x + ω ^ 2 * y)
    (hγ : (γ : K) = (x : K) ^ 2 + x * y + (y : K) ^ 2)
    (hE : ∃ t ∈ affGroup P H, Aff P t (u2 (1 : fixSub σ)) 0 0)
    (hU : ∃ t ∈ affGroup P H, ∃ b₀ : fixSub σ, b₀ ≠ 0 ∧ Aff P t (l2 b₀) 0 0)
    (hW : ∃ t ∈ affGroup P H, Aff P t (u2 γ) 0 (ρ * ζ))
    (h1 : ∃ t ∈ affGroup P H, Aff P t (u2 y) 0 ζ)
    (hωg : ∃ t ∈ affGroup P H, Aff P t (u2 (x + y)) 0 (ω * ζ)) :
    ∀ c : fixSub σ, ∃ t ∈ H, IsTv σ t P.z (c : K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨te, hte, hteA⟩ := hE
  obtain ⟨tu, htu, b₀, hb₀, htuA⟩ := hU
  obtain ⟨ty, hty, htyA⟩ := h1
  obtain ⟨tω, htω, htωA⟩ := hωg
  have hu1 : u2 (1 : fixSub σ) ∈ lSub P H := ⟨te, hte, 0, 0, hteA⟩
  have huy : u2 y ∈ lSub P H := ⟨ty, hty, 0, ζ, htyA⟩
  have huxy : u2 (x + y) ∈ lSub P H := ⟨tω, htω, 0, ω * ζ, htωA⟩
  have hl : l2 b₀ ∈ lSub P H := ⟨tu, htu, 0, 0, htuA⟩
  have hL : lSub P H = ⊤ := by
    by_cases hy : y ∈ ratFix σ k
    · have hx : x + y ∉ ratFix σ k := by
        intro hxy
        apply hρ
        have hxk : (x : K) ∈ k := by
          have := (ratFix σ k).sub_mem hxy hy
          rw [add_sub_cancel_right] at this
          exact this
        rw [hρxy]
        exact k.add_mem hxk (k.mul_mem (k.pow_mem hωk 2) hy)
      exact lSub_eq_top hp hp2 hK hr2 hx hb₀ hu1 huxy hl
    · exact lSub_eq_top hp hp2 hK hr2 hy hb₀ hu1 huy hl
  obtain ⟨s₀, hs₀⟩ := exists_not_mem_ratFix (σ := σ) (k := k) hp.two_le hK
  have hF : ∃ s : fixSub σ, s ≠ 0 ∧ s ≠ 1 :=
    ⟨s₀, fun h => hs₀ (h ▸ (ratFix σ k).zero_mem), fun h => hs₀ (h ▸ (ratFix σ k).one_mem)⟩
  have hS : sSub P H hL = ⊤ :=
    sSub_eq_top hσ hk4 hL hF hω hω2 hρ hζ hρxy hγ ⟨te, hte, hteA⟩ hW ⟨ty, hty, htyA⟩
      ⟨tω, htω, htωA⟩
  have hX : xTrans P H = ⊤ := xTrans_eq_top hL hS
  have hωσ : ω + σ ω = 1 := by
    rw [hω]
    linear_combination hω2 - h2
  obtain ⟨f, hff, hzf, hef, huf⟩ := exists_dual hσ P hz0 hωσ
  intro c
  have hm1 : ((c : K) * ω, (0 : K)) ∈ xTrans P H := hX ▸ AddSubgroup.mem_top _
  have hm2 : ((0 : K), (1 : K)) ∈ xTrans P H := hX ▸ AddSubgroup.mem_top _
  obtain ⟨g₁, hg₁, h₁⟩ := hm1
  obtain ⟨g₂, hg₂, h₂⟩ := hm2
  have key := mul_comm_aff hσ P hzf hef huf h₁ h₂ hg₁.2.1 hg₂.2.1
  refine ⟨g₁ * g₂ * (g₂ * g₁)⁻¹, ?_, ?_⟩
  · exact H.mul_mem (H.mul_mem hg₁.1 hg₂.1) (H.inv_mem (H.mul_mem hg₂.1 hg₁.1))
  · have hcω : (c : K) * ω + σ ((c : K) * ω) = c := by
      rw [map_mul, mem_fixSub.1 c.2]
      linear_combination (c : K) * hωσ
    rw [hcω] at key
    exact key

end CFSG.RankThree.PartOne.SEITZ5
