module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fintype.Perm
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.RankThree.PartOne.Q1327T

@[expose] def d3ToPerm : DihedralGroup 3 → Equiv.Perm (Fin 3)
  | .r i => finRotate 3 ^ (i.val)
  | .sr i => Equiv.swap 1 2 * finRotate 3 ^ (i.val)

theorem d3ToPerm_mul :
    ∀ x y : DihedralGroup 3, d3ToPerm (x * y) = d3ToPerm x * d3ToPerm y := by
  decide

theorem d3ToPerm_bijective : Function.Bijective d3ToPerm := by
  refine ⟨?_, ?_⟩
  · intro x y h
    revert x y
    decide
  · intro y
    revert y
    decide

noncomputable def d3EquivPerm : DihedralGroup 3 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective (MonoidHom.mk' d3ToPerm d3ToPerm_mul) d3ToPerm_bijective

theorem nonempty_mulEquiv_perm_three {D : Type*} [Group D] [Finite D] (ρ σ : D) (hρ3 : ρ ^ 3 = 1)
    (hρ1 : ρ ≠ 1) (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) (hc : σ * ρ * σ⁻¹ = ρ⁻¹)
    (hcard : Nat.card D = 6) : Nonempty (D ≃* Equiv.Perm (Fin 3)) := by
  have hρo : orderOf ρ = 3 := orderOf_eq_prime hρ3 hρ1
  have hσ2 : σ ^ 2 = 1 := by rw [pow_two]; exact hσ
  have hσo : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hcomm : σ * ρ = ρ * σ := by
      rw [← hk]
      exact ((Commute.self_zpow ρ k).symm).eq
    have h1 : ρ = ρ⁻¹ := by
      rw [← hc, hcomm]
      group
    have h2 : ρ * ρ = 1 := by
      calc ρ * ρ = ρ * ρ⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel ρ
    apply hρ1
    calc ρ = ρ ^ 3 * (ρ * ρ)⁻¹ := by group
      _ = 1 := by rw [hρ3, h2]; simp
  have hK : Nat.card ↥(Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ) = 6 := by
    set K := Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ with hKdef
    have h3 : 3 ∣ Nat.card K := by
      have := Subgroup.orderOf_dvd_natCard K (Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ))
      rwa [hρo] at this
    have h2 : 2 ∣ Nat.card K := by
      have := Subgroup.orderOf_dvd_natCard K (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ))
      rwa [hσo] at this
    have h6 : 6 ∣ Nat.card K :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 3 2) h3 h2
    have h7 : Nat.card K ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card K
    exact Nat.dvd_antisymm h7 h6
  have hgen : ⊤ = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ :=
    (Subgroup.eq_top_of_card_eq _ (by rw [hK, hcard])).symm
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hc hσρ
  rw [hρo] at e
  exact ⟨e.trans d3EquivPerm⟩

end CFSG.RankThree.PartOne.Q1327T
