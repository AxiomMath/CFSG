module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aKron
public import CFSG.Quasithin.Vol2.F134LieL3Plane

public section

namespace CFSG.Quasithin.H13.NQCore.Psl3Even

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.F134.LieL3
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped MatrixGroups

theorem exists_equiv_map_eq_projUnitriangular {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    [CharP K 2] (e₁ : G ≃* projectiveSL 3 K) {UL : Subgroup G} (hUL : IsPGroup 2 UL)
    (hULi : ¬ 2 ∣ UL.index) :
    ∃ e : G ≃* projectiveSL 3 K, UL.map e.toMonoidHom = projUnitriangular 3 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU1 : IsPGroup 2 (UL.map e₁.toMonoidHom) := hUL.map _
  have hU1i : ¬ 2 ∣ (UL.map e₁.toMonoidHom).index := by
    rw [show UL.map e₁.toMonoidHom = UL.map (e₁ : G →* projectiveSL 3 K) from rfl,
      Subgroup.index_map_equiv]
    exact hULi
  obtain ⟨S₀, hS₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) S₀ (hU1.toSylow hU1i)
  have hmem : ∀ z, z ∈ UL.map e₁.toMonoidHom ↔ g⁻¹ * z * g ∈ projUnitriangular 3 K := by
    intro z
    have h1 : UL.map e₁.toMonoidHom = ((g • S₀ : Sylow 2 (projectiveSL 3 K)) :
        Subgroup (projectiveSL 3 K)) := by
      rw [hg]
      rfl
    rw [h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, hS₀]
  refine ⟨e₁.trans (MulAut.conj g⁻¹), ?_⟩
  have he : ∀ y : G, (e₁.trans (MulAut.conj g⁻¹)) y = g⁻¹ * e₁ y * g := fun y => by
    rw [MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (e₁.trans (MulAut.conj g⁻¹)) y ∈ _
    rw [he]
    exact (hmem _).mp ⟨y, hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, hye⟩ := (hmem (g * x * g⁻¹)).mpr (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x
      by group])
    refine ⟨y, hy, ?_⟩
    change (e₁.trans (MulAut.conj g⁻¹)) y = x
    rw [he]
    change e₁ y = g * x * g⁻¹ at hye
    rw [hye]
    group

variable {A : Type} [Group A] {p : ℕ} {L P T : Subgroup A}

theorem commutator_eq_bot_of_map {K : Type} [Field K] (h : P ≤ L) (e : ↥L ≃* projectiveSL 3 K)
    (hab : ∀ x ∈ (P.subgroupOf L).map e.toMonoidHom, ∀ y ∈ (P.subgroupOf L).map e.toMonoidHom,
      x * y = y * x) : ⁅P, P⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have := hab (e ⟨b, h hb⟩) ⟨⟨b, h hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩ (e ⟨a, h ha⟩)
    ⟨⟨a, h ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  rw [← map_mul, ← map_mul] at this
  exact congrArg Subtype.val (e.injective this)

end CFSG.Quasithin.H13.NQCore.Psl3Even
