module

public import CFSG.GH74.GLS.Stage4.Q9.Rigidity

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16e_d5_index_dvd_48 {G : Type*} [Group G] {L A : Subgroup G} (hL : Nat.card ↥L ∣ 9)
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set G)) :
    ((A ⊓ Subgroup.centralizer (L : Set G)).subgroupOf A).index ∣ 48 := by
  have hLne : Nat.card ↥L ≠ 0 := by
    intro h0
    have h := hL
    rw [h0] at h
    exact absurd h (by norm_num)
  haveI : Finite ↥L := Nat.finite_of_card_ne_zero hLne
  have hA : A ≤ Subgroup.normalizer (L : Set G) := hLn
  let ψ : ↥A →* MulAut ↥L :=
    (Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hA)
  have hker : ψ.ker = (A ⊓ Subgroup.centralizer (L : Set G)).subgroupOf A := by
    ext g
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hg
      refine ⟨g.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := congrArg (fun f : MulAut ↥L => f ⟨l, hl⟩) hg
      have h' : (g : G) * l * (g : G)⁻¹ = l := by
        have hval := congrArg (fun x : ↥L => (x : G)) h
        have hsmul : ((L.normalizerMonoidHom ((Subgroup.inclusion hA) g)) ⟨l, hl⟩ :
            ↥L).1 = (g : G) * l * (g : G)⁻¹ := rfl
        simp only [ψ, MonoidHom.comp_apply] at hval
        rw [hsmul] at hval
        simpa using hval
      calc (l : G) * (g : G) = ((g : G) * l * (g : G)⁻¹) * (g : G) := by rw [h']
        _ = (g : G) * (l : G) := by rw [mul_assoc, inv_mul_cancel, mul_one]
    · rintro ⟨-, hg⟩
      ext l
      have h := (Subgroup.mem_centralizer_iff.1 hg) l.1 l.2
      have h' : (g : G) * l * (g : G)⁻¹ = l := by
        rw [h.symm, mul_assoc, mul_inv_cancel, mul_one]
      change (g : G) * (l : G) * (g : G)⁻¹ = (l : G)
      exact h'
  calc
    ((A ⊓ Subgroup.centralizer (L : Set G)).subgroupOf A).index = ψ.ker.index := by rw [hker]
    _ = Nat.card ψ.range := Subgroup.index_ker ψ
    _ ∣ Nat.card (MulAut ↥L) := Subgroup.card_subgroup_dvd_card ψ.range
    _ ∣ 48 := CFSG.GH74.GLS.Stage4.Q9.card_mulAut_dvd_48 hL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
