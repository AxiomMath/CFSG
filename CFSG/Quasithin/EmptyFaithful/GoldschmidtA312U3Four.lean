module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Geom

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

variable {p f : ℕ} {F : Type} [Field F]

section FourGroup

variable (h : UnitaryFieldData p f F)

@[expose] def dS (k : Fin 3) : ↥(unitarySU p f F 3) := ⟨dsignGL F k, dsignGL_mem h k⟩

theorem dS_mul_self (k : Fin 3) : dS h k * dS h k = 1 :=
  Subtype.ext (Units.ext (dsign_mul_self F k))

theorem dS_commute (i j : Fin 3) : Commute (dS h i) (dS h j) := by
  refine Subtype.ext (Units.ext ?_)
  show dsign F i * dsign F j = dsign F j * dsign F i
  simp only [dsign, Matrix.diagonal_mul_diagonal, mul_comm]

@[expose] def E₀ : Subgroup ↥(unitarySU p f F 3) := Subgroup.closure (Set.range (dS h))

theorem dS_mem_E₀ (k : Fin 3) : dS h k ∈ E₀ h := Subgroup.subset_closure ⟨k, rfl⟩

theorem isPGroup_two_E₀ : IsPGroup 2 ↥(E₀ h) := by
  have hcomm : (Set.range (dS h)).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact dS_commute h i j
  have hcc : IsMulCommutative ↥(Subgroup.closure (Set.range (dS h))) :=
    Subgroup.isMulCommutative_closure hcomm
  have hsq : ∀ x ∈ E₀ h, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact dS_mul_self h k
    | one => simp
    | mul x y hx hy hxx hyy =>
      have hc : x * y = y * x :=
        congrArg Subtype.val (hcc.is_comm.comm (⟨x, hx⟩ : ↥(E₀ h)) ⟨y, hy⟩)
      calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
        _ = x * (x * y) * y := by rw [← hc]
        _ = (x * x) * (y * y) := by simp only [mul_assoc]
        _ = 1 := by rw [hxx, hyy, mul_one]
    | inv x hx hxx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by rw [_root_.mul_inv_rev]
        _ = 1 := by rw [hxx, inv_one]
  intro x
  refine ⟨1, ?_⟩
  have := hsq x.1 x.2
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_one, sq]
  exact this

theorem exists_sylow_le_of_odd_index {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hodd : Odd M.index) : ∃ Q : Sylow 2 G, (Q : Subgroup G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pm⟩ : Nonempty (Sylow 2 ↥M) := inferInstance
  obtain ⟨Q, hQ⟩ := Sylow.exists_comap_subtype_eq Pm
  refine ⟨Q, ?_⟩
  have hfac : (Nat.card G).factorization 2 = (Nat.card M).factorization 2 := by
    rw [← Subgroup.card_mul_index M, Nat.factorization_mul Nat.card_pos.ne'
      (Subgroup.index_ne_zero_of_finite), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (Nat.not_even_iff_odd.mpr hodd |> fun _ =>
        hodd.not_two_dvd_nat), add_zero]
  have hcardQ : Nat.card (Q : Subgroup G) = 2 ^ (Nat.card M).factorization 2 := by
    rw [Sylow.card_eq_multiplicity Q, hfac]
  have hsub : (Q : Subgroup G).subgroupOf M = (Pm : Subgroup ↥M) := hQ
  have hcardP : Nat.card ((Q : Subgroup G).subgroupOf M) = 2 ^ (Nat.card M).factorization 2 := by
    rw [hsub, Sylow.card_eq_multiplicity Pm]
  have hmap : ((Q : Subgroup G).subgroupOf M).map M.subtype = (Q : Subgroup G) ⊓ M :=
    Subgroup.subgroupOf_map_subtype _ _
  have hinf : Nat.card ↥((Q : Subgroup G) ⊓ M) = Nat.card (Q : Subgroup G) := by
    rw [← hmap, Subgroup.card_map_of_injective M.subtype_injective, hcardP, hcardQ]
  have heq : (Q : Subgroup G) ⊓ M = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hinf])
  intro x hx
  have hx' : x ∈ (Q : Subgroup G) ⊓ M := by
    rw [heq]
    exact hx
  exact hx'.2

theorem exists_conj_contains_four (M : Subgroup ↥(unitarySU p f F 3)) (hodd : Odd M.index) :
    ∃ g : ↥(unitarySU p f F 3), ∀ k, dS h k ∈ M.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.finite
  obtain ⟨Q, hQM⟩ := exists_sylow_le_of_odd_index hodd
  obtain ⟨Q₁, hQ₁⟩ := (isPGroup_two_E₀ h).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(unitarySU p f F 3) Q₁ Q
  refine ⟨g⁻¹, fun k => ?_⟩
  have hd : dS h k ∈ (Q₁ : Subgroup ↥(unitarySU p f F 3)) := hQ₁ (dS_mem_E₀ h k)
  have hmem : g * dS h k * g⁻¹ ∈ (Q : Subgroup ↥(unitarySU p f F 3)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨dS h k, hd, by simp [MulAut.conj_apply]⟩
  refine ⟨g * dS h k * g⁻¹, hQM hmem, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
  group

end FourGroup

end CFSG.Quasithin.A312U3
