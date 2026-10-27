module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.Assembly.Defs

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def PieceDichotomy (M : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N ≤ M → M ≤ normalizer (N : Set G) → N ≤ centralizer (M : Set G) ∨ N = M

theorem false_of_pieceDichotomy_of_eq_sup_conj {M F : Subgroup G} {t : G}
    (hdich : PieceDichotomy M) (hM : M = F ⊔ F.map (MulAut.conj t).toMonoidHom)
    (hFt : F.map (MulAut.conj t).toMonoidHom ≤ centralizer (F : Set G))
    (hFp : ⁅F, F⁆ = F) (hF : F ≠ ⊥) (htM : t ∈ normalizer (M : Set G)) : False := by
  have hFM : F ≤ M := hM ▸ le_sup_left
  have hab : F ≤ centralizer (F : Set G) → False := fun h => by
    apply hF
    rw [← hFp]
    exact commutator_eq_bot_iff_le_centralizer.2 h
  have hMN : M ≤ normalizer (F : Set G) := by
    rw [hM]
    exact sup_le le_normalizer (hFt.trans (centralizer_le_normalizer _))
  rcases hdich F hFM hMN with h | h
  · exact hab (h.trans (centralizer_le (SetLike.coe_subset_coe.2 hFM)))
  · have hFt' : F.map (MulAut.conj t).toMonoidHom = F := by
      rw [h]
      exact mem_normalizer_iff_map_conj_eq.1 htM
    have hFF := hFt
    rw [hFt'] at hFF
    exact hab hFF

theorem pieceDichotomy_map_of_isSimpleGroup {S H : Type*} [Group S] [Group H] {P : Subgroup S}
    (hP : ⁅P, P⁆ = P) (Φ : S →* G) (Ψ : S →* H) (hΨ : Ψ.ker ≤ center S)
    (hsimple : IsSimpleGroup (P.map Ψ)) : PieceDichotomy (P.map Φ) := by
  intro N hN hNn
  set N' : Subgroup S := N.comap Φ ⊓ P with hN'
  have hN'n : ∀ p ∈ P, ∀ n ∈ N', p * n * p⁻¹ ∈ N' := by
    intro p hp n hn
    refine Subgroup.mem_inf.2 ⟨?_, P.mul_mem (P.mul_mem hp (Subgroup.mem_inf.1 hn).2)
      (P.inv_mem hp)⟩
    change Φ (p * n * p⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 (hNn ⟨p, hp, rfl⟩) (Φ n)).1 (Subgroup.mem_inf.1 hn).1
  have hnorm : ((N'.map Ψ).subgroupOf (P.map Ψ)).Normal := by
    constructor
    intro x hx g
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨p, hp, hpg⟩ := g.2
    rw [coe_mul, coe_mul, coe_inv, ← hnx, ← hpg, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hN'n p hp n hn, rfl⟩
  rcases hsimple.eq_bot_or_eq_top_of_normal ((N'.map Ψ).subgroupOf (P.map Ψ)) with h | h
  · left
    have hN'Z : N' ≤ center S := by
      intro n hn
      apply hΨ
      rw [MonoidHom.mem_ker]
      have hmem : (⟨Ψ n, ⟨n, hn.2, rfl⟩⟩ : P.map Ψ) ∈ (N'.map Ψ).subgroupOf (P.map Ψ) :=
        mem_subgroupOf.2 ⟨n, hn, rfl⟩
      rw [h, mem_bot] at hmem
      exact congrArg Subtype.val hmem
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hN hx
    rw [mem_centralizer_iff]
    rintro _ ⟨p', -, rfl⟩
    rw [← map_mul, ← map_mul, mem_center_iff.1 (hN'Z ⟨hx, hp⟩) p']
  · right
    refine le_antisymm hN ?_
    have hdec : ∀ p ∈ P, ∃ n ∈ N', p * n⁻¹ ∈ center S := by
      intro p hp
      have hmem : (⟨Ψ p, ⟨p, hp, rfl⟩⟩ : P.map Ψ) ∈ (N'.map Ψ).subgroupOf (P.map Ψ) :=
        h ▸ mem_top _
      obtain ⟨n, hn, hnp⟩ := mem_subgroupOf.1 hmem
      refine ⟨n, hn, hΨ ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnp, mul_inv_cancel]
    have hPN' : P ≤ N' := by
      rw [← hP, commutator_le]
      intro p₁ hp₁ p₂ hp₂
      obtain ⟨n₁, hn₁, hc₁⟩ := hdec p₁ hp₁
      obtain ⟨n₂, hn₂, hc₂⟩ := hdec p₂ hp₂
      have e : ⁅p₁, p₂⁆ = ⁅n₁, n₂⁆ := by
        rw [← CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hc₁ hc₂ n₁ n₂,
          inv_mul_cancel_right, inv_mul_cancel_right]
      rw [e, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)
    rintro _ ⟨p, hp, rfl⟩
    exact (hPN' hp).1

end CFSG.SeitzReduction.TwistedE6Pilot
