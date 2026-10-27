module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Transport

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {p ℓ : ℕ} {X : Type*} [Group X]

structure Frame (p ℓ : ℕ) (f : MulAut X) : Prop where
  prime : p.Prime
  prime_ℓ : ℓ.Prime
  ord : orderOf f = p
  coprime : Nat.Coprime p (Nat.card X)
  simple : IsSimpleGroup X
  nonabelian : ∃ a b : X, a * b ≠ b * a
  fixed_solvable : Group.IsSolvable (signalizerFixedSubgroup f)
  C0_ne_bot : fixedFitting f ≠ ⊥
  C0_pgroup : IsPGroup ℓ (fixedFitting f)
  C0_comm : IsMulCommutative (fixedFitting f)
  C0_sylow : ∀ P : Subgroup X, IsPGroup ℓ P → fixedFitting f ≤ P → P = fixedFitting f
  C0_ne : fixedFitting f ≠ signalizerFixedSubgroup f
  C1_ne : fixedCore1 f ≠ fixedFitting f
  minimal : ∀ N : Subgroup X, N ≤ signalizerFixedSubgroup f →
    (N.subgroupOf (signalizerFixedSubgroup f)).Normal → N ≠ ⊥ → fixedFitting f ≤ N
  centralizer_comm : IsMulCommutative (Subgroup.centralizer (fixedFitting f : Set X))
  fpf : ∀ v ∈ signalizerFixedSubgroup f, v ∉ fixedFitting f →
    ∀ z ∈ Subgroup.centralizer (fixedFitting f : Set X), v * z = z * v → z = 1
  normalizer_le : ∀ x ∈ fixedNormalizer f, ∃ z ∈ Subgroup.centralizer (fixedFitting f : Set X),
    ∃ c ∈ signalizerFixedSubgroup f, x = z * c
  overgroup : ∀ H : Subgroup X, signalizerFixedSubgroup f ≤ H → H ≠ ⊤ → H ≤ fixedNormalizer f

theorem Frame.of_fixed_eq {f f' : MulAut X}
    (hC : signalizerFixedSubgroup f = signalizerFixedSubgroup f')
    (hord : orderOf f = orderOf f') (h : Frame p ℓ f') : Frame p ℓ f := by
  have hF := fixedFitting_eq_of_fixed_eq hC
  have hM := fixedNormalizer_eq_of_fixed_eq hC
  have h1 := fixedCore1_eq_of_fixed_eq hC
  exact
    { prime := h.prime
      prime_ℓ := h.prime_ℓ
      ord := hord.trans h.ord
      coprime := h.coprime
      simple := h.simple
      nonabelian := h.nonabelian
      fixed_solvable := by rw [hC]; exact h.fixed_solvable
      C0_ne_bot := by rw [hF]; exact h.C0_ne_bot
      C0_pgroup := by rw [hF]; exact h.C0_pgroup
      C0_comm := by rw [hF]; exact h.C0_comm
      C0_sylow := by rw [hF]; exact h.C0_sylow
      C0_ne := by rw [hF, hC]; exact h.C0_ne
      C1_ne := by rw [h1, hF]; exact h.C1_ne
      minimal := by rw [hF, hC]; exact h.minimal
      centralizer_comm := by rw [hF]; exact h.centralizer_comm
      fpf := by rw [hF, hC]; exact h.fpf
      normalizer_le := by rw [hM, hF, hC]; exact h.normalizer_le
      overgroup := by rw [hM, hC]; exact h.overgroup }

theorem Frame.of_congr {Y : Type*} [Group Y] [Finite X] [Finite Y] (e : X ≃* Y) {f : MulAut X}
    (h : Frame p ℓ (MulAut.congr e f)) : Frame p ℓ f := by
  have hC := signalizerFixedSubgroup_congr e f
  have hF := fixedFitting_congr e f
  have hM := fixedNormalizer_congr e f
  have h1 := fixedCore1_congr e f
  have hZ := centralizer_map_equiv e (fixedFitting f)
  have hinj : Function.Injective (Subgroup.map e.toMonoidHom) := Subgroup.map_injective e.injective
  exact
    { prime := h.prime
      prime_ℓ := h.prime_ℓ
      ord := by rw [← orderOf_congr e f]; exact h.ord
      coprime := by rw [Nat.card_congr e.toEquiv]; exact h.coprime
      simple := by have := h.simple; exact e.isSimpleGroup
      nonabelian := by
        obtain ⟨a, b, hab⟩ := h.nonabelian
        exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
      fixed_solvable := by
        have hs := h.fixed_solvable
        rw [hC] at hs
        exact isSolvable_of_map_equiv e hs
      C0_ne_bot := by
        have hb := h.C0_ne_bot
        rw [hF] at hb
        exact fun hc => hb (by rw [hc, Subgroup.map_bot])
      C0_pgroup := by
        have hp := h.C0_pgroup
        rw [hF] at hp
        exact isPGroup_of_map_equiv e hp
      C0_comm := by
        have hc := h.C0_comm
        rw [hF] at hc
        exact isMulCommutative_of_map_equiv e hc
      C0_sylow := by
        intro P hP hFP
        have h2 := h.C0_sylow (P.map e.toMonoidHom)
          (hP.of_equiv (Subgroup.equivMapOfInjective P e.toMonoidHom e.injective))
          (by rw [hF]; exact Subgroup.map_mono hFP)
        rw [hF] at h2
        exact hinj h2
      C0_ne := by
        intro hc
        apply h.C0_ne
        rw [hF, hC, hc]
      C1_ne := by
        intro hc
        apply h.C1_ne
        rw [h1, hF, hc]
      minimal := by
        intro N hNC hNn hN0
        have hN' : N.map e.toMonoidHom ≤ signalizerFixedSubgroup (MulAut.congr e f) := by
          rw [hC]; exact Subgroup.map_mono hNC
        have h2 := h.minimal (N.map e.toMonoidHom) hN'
          (by rw [hC]; exact normal_subgroupOf_map_equiv e hNC hNn)
          (fun hb => hN0 ((Subgroup.map_eq_bot_iff_of_injective N e.injective).mp hb))
        rw [hF] at h2
        exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h2
      centralizer_comm := by
        have hc := h.centralizer_comm
        rw [hF, hZ] at hc
        exact isMulCommutative_of_map_equiv e hc
      fpf := by
        intro v hv hvF z hz hvz
        have h2 := h.fpf (e v) (by rw [hC]; exact Subgroup.mem_map_of_mem _ hv)
          (by
            rw [hF]
            intro hm
            exact hvF (by simpa using Subgroup.mem_map_equiv.mp hm))
          (e z) (by rw [hF, hZ]; exact Subgroup.mem_map_of_mem _ hz)
          (by rw [← map_mul, ← map_mul, hvz])
        exact e.injective (by simpa using h2)
      normalizer_le := by
        intro x hx
        obtain ⟨z', hz', c', hc', hxz⟩ := h.normalizer_le (e x)
          (by rw [hM]; exact Subgroup.mem_map_of_mem _ hx)
        rw [hF, hZ] at hz'
        rw [hC] at hc'
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hz'
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hc'
        exact ⟨z, hz, c, hc, e.injective (by simpa using hxz)⟩
      overgroup := by
        intro H hCH hHtop
        have h2 := h.overgroup (H.map e.toMonoidHom)
          (by rw [hC]; exact Subgroup.map_mono hCH)
          (fun htop => hHtop
            (hinj (htop.trans (Subgroup.map_top_of_surjective _ e.surjective).symm)))
        rw [hM] at h2
        exact (Subgroup.map_le_map_iff_of_injective e.injective).mp h2 }

end CFSG.SignalizerFunctorTheorem.McBride
