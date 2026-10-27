module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport
public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartOne

namespace Res417Six

theorem map_eq_of_conj_le {X M : Type*} [Group X] [Group M] (φ : X ≃* M) {D : Subgroup X}
    (hmax : ∀ x : X, x ^ 3 = 1 → (∀ d ∈ D, x * d = d * x) → x ∈ D) {T : Subgroup M}
    (hTcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hTexp : ∀ t ∈ T, t ^ 3 = 1) {g : M}
    (hg : ∀ x ∈ D, g * φ x * g⁻¹ ∈ T) :
    D.map (φ.trans (MulAut.conj g)).toMonoidHom = T := by
  have happ : ∀ x : X, (φ.trans (MulAut.conj g)) x = g * φ x * g⁻¹ := fun x => rfl
  refine le_antisymm ?_ fun t ht => ?_
  · rintro _ ⟨x, hx, rfl⟩
    show (φ.trans (MulAut.conj g)) x ∈ T
    rw [happ]
    exact hg x hx
  · set x : X := (φ.trans (MulAut.conj g)).symm t with hx
    have hxt : (φ.trans (MulAut.conj g)) x = t := by rw [hx, MulEquiv.apply_symm_apply]
    have hx3 : x ^ 3 = 1 := by
      apply (φ.trans (MulAut.conj g)).injective
      rw [map_pow, hxt, map_one]
      exact hTexp t ht
    have hxD : x ∈ D := hmax x hx3 fun d hd => by
      apply (φ.trans (MulAut.conj g)).injective
      rw [map_mul, map_mul, hxt]
      have hdT : (φ.trans (MulAut.conj g)) d ∈ T := by rw [happ]; exact hg d hd
      exact hTcomm t ht _ hdT
    exact ⟨x, hxD, hxt⟩

theorem autIn_eq_torusImage {M : Type} [Group M] (L T : Subgroup M) :
    autIn L T = torusImage T L := by
  rw [autIn, torusImage, Subgroup.inf_subgroupOf_right]

theorem nonempty_autIn_mulEquiv_of_map_eq {X M : Type} [Group X] [Group M] (ψ : X ≃* M)
    {D : Subgroup X} {T : Subgroup M} (h : D.map ψ.toMonoidHom = T) :
    Nonempty (autIn ⊤ D ≃* torusImage T ⊤) := by
  subst h
  rw [← autIn_eq_torusImage]
  exact ⟨Sporadic.autInTopCongr ψ D⟩

theorem card_eq_of_map_eq {X M : Type*} [Group X] [Group M] (ψ : X ≃* M) {D : Subgroup X}
    {T : Subgroup M} (h : D.map ψ.toMonoidHom = T) : Nat.card D = Nat.card T := by
  rw [← h, Subgroup.card_map_of_injective ψ.injective]

end Res417Six

end CFSG.RankThree.PartTwo.Sec4
