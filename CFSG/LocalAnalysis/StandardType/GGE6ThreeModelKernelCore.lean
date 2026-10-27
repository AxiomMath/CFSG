module

public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.StandardType

namespace E6ThreeKernel

open CFSG.LieType.Steinberg (pullback mem_pullback pullbackFst pullbackFst_surjective
  ker_pullbackFst_le_center commutatorElement_mul_mul_of_mem_center)
open scoped commutatorElement

variable {H R L : Type} [Group H] [Group R] [Group L]

theorem exists_surjective_of_split [Finite H] [Finite L] {q : H →* R} (hq : Function.Surjective q)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : H →* E, ∀ h, π (s h) = h)
    {ψ : L →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) :
    ∃ α : H →* L, (∀ s, ψ (α s) = q s) ∧ Function.Surjective α := by
  have hfst := pullbackFst_surjective (β := q) hψ
  have hfstc := ker_pullbackFst_le_center (β := q) hker
  obtain ⟨σ, hσ⟩ := hsplit (pullback q ψ) (pullbackFst q ψ) hfst hfstc
  let α : H →* L := ((MonoidHom.snd H L).comp (pullback q ψ).subtype).comp σ
  have hα : ∀ s, ψ (α s) = q s := fun s => by
    have hmem := mem_pullback.1 (σ s).2
    have h1 : ((σ s : pullback q ψ) : H × L).1 = s := hσ s
    change ψ ((σ s : pullback q ψ) : H × L).2 = q s
    rw [← hmem, h1]
  have hdecomp : ∀ x : L, ∃ s, x * (α s)⁻¹ ∈ Subgroup.center L := fun x => by
    obtain ⟨s, hs⟩ := hq (ψ x)
    refine ⟨s, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hs, mul_inv_cancel]
  refine ⟨α, hα, ?_⟩
  have hcomm : commutator L ≤ α.range := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨s, hs⟩ := hdecomp x
    obtain ⟨t, ht⟩ := hdecomp y
    have e : ⁅x, y⁆ = ⁅α s, α t⁆ := by
      have h := commutatorElement_mul_mul_of_mem_center hs ht (α s) (α t)
      rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
    rw [e, ← map_commutatorElement]
    exact ⟨_, rfl⟩
  intro x
  exact hcomm (by rw [hperf]; exact Subgroup.mem_top x)

theorem card_ker_dvd_of_split [Finite H] [Finite L] {q : H →* R} (hq : Function.Surjective q)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : H →* E, ∀ h, π (s h) = h)
    {ψ : L →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hperf : commutator L = ⊤) : Nat.card ψ.ker ∣ Nat.card q.ker := by
  obtain ⟨α, hα, hαs⟩ := exists_surjective_of_split hq hsplit hψ hker hperf
  have hk : ψ.ker = q.ker.map α := by
    ext z
    constructor
    · intro hz
      obtain ⟨s, hs⟩ := hαs z
      refine ⟨s, ?_, hs⟩
      change s ∈ q.ker
      rw [MonoidHom.mem_ker, ← hα, hs]
      exact MonoidHom.mem_ker.mp hz
    · rintro ⟨s, hs, rfl⟩
      rw [MonoidHom.mem_ker, hα]
      exact hs
  rw [hk]
  exact Subgroup.card_map_dvd _ _

end E6ThreeKernel

end CFSG.StandardType
