module

public import CFSG.RankThree.PartOne.N143.JFacts

public section

namespace CFSG.RankThree.PartOne.N143

variable {G : Type} [Group G] {A : Subgroup G}

theorem Vof_gen_subset (J : Subgroup G) :
    ({d : G | d ∈ J ⊓ Subgroup.centralizer (A : Set G) ∧ d ^ 3 = 1} : Set G) ⊆ Vof A J :=
  Subgroup.subset_closure

theorem Vof_le (J : Subgroup G) : Vof A J ≤ J ⊓ Subgroup.centralizer (A : Set G) :=
  (Subgroup.closure_le _).2 fun _ hd => hd.1

theorem conj_mem_Vof {J : Subgroup G} {y : G} (hyJ : y ∈ Subgroup.normalizer (J : Set G))
    (hyA : y ∈ Subgroup.normalizer (A : Set G)) {v : G} (hv : v ∈ Vof A J) :
    y * v * y⁻¹ ∈ Vof A J := by
  have hle : (Vof A J).map (MulAut.conj y).toMonoidHom ≤ Vof A J := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 fun d hd => ?_
    have hJd : y * d * y⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hyJ d).1 hd.1.1
    have hCd : y * d * y⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' : y⁻¹ * a * y ∈ A := by
        have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set G)).inv_mem hyA) a).1 ha
        simpa using this
      have hcomm : (y⁻¹ * a * y) * d = d * (y⁻¹ * a * y) :=
        Subgroup.mem_centralizer_iff.1 hd.1.2 _ ha'
      calc a * (y * d * y⁻¹) = y * ((y⁻¹ * a * y) * d) * y⁻¹ := by group
        _ = y * (d * (y⁻¹ * a * y)) * y⁻¹ := by rw [hcomm]
        _ = (y * d * y⁻¹) * a := by group
    have h3 : (y * d * y⁻¹) ^ 3 = 1 := by rw [conj_pow, hd.2, mul_one, mul_inv_cancel]
    exact Vof_gen_subset J (show y * d * y⁻¹ ∈ {d : G | d ∈ J ⊓ Subgroup.centralizer (A : Set G) ∧ d ^ 3 = 1} from ⟨⟨hJd, hCd⟩, h3⟩)
  exact hle ⟨v, hv, rfl⟩

theorem conj_mem_Vof_conjBy {J : Subgroup G} {x : G} (hxA : x ∈ Subgroup.normalizer (A : Set G))
    {v : G} (hv : v ∈ Vof A J) : x * v * x⁻¹ ∈ Vof A (conjBy x J) := by
  have hle : (Vof A J).map (MulAut.conj x).toMonoidHom ≤ Vof A (conjBy x J) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 fun d hd => ?_
    have hJd : x * d * x⁻¹ ∈ conjBy x J := by
      rw [Equivariance.mem_conjBy]
      have : d ∈ J := hd.1.1
      simpa [mul_assoc] using this
    have hCd : x * d * x⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have ha' : x⁻¹ * a * x ∈ A := by
        have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (A : Set G)).inv_mem hxA) a).1 ha
        simpa using this
      have hcomm : (x⁻¹ * a * x) * d = d * (x⁻¹ * a * x) :=
        Subgroup.mem_centralizer_iff.1 hd.1.2 _ ha'
      calc a * (x * d * x⁻¹) = x * ((x⁻¹ * a * x) * d) * x⁻¹ := by group
        _ = x * (d * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
        _ = (x * d * x⁻¹) * a := by group
    have h3 : (x * d * x⁻¹) ^ 3 = 1 := by rw [conj_pow, hd.2, mul_one, mul_inv_cancel]
    exact Vof_gen_subset (conjBy x J) (show x * d * x⁻¹ ∈ {d : G | d ∈ conjBy x J ⊓ Subgroup.centralizer (A : Set G) ∧ d ^ 3 = 1} from ⟨⟨hJd, hCd⟩, h3⟩)
  exact hle ⟨v, hv, rfl⟩

end CFSG.RankThree.PartOne.N143
