module

public import CFSG.Quasithin.Background.KnownMultTransfer
public import CFSG.Quasithin.Background.KnownMultIndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter

variable {X G : Type*} [Group X] [Finite X] [Group G]

theorem card_ker_le_two_of_dihedral_sylow [Group.IsPerfect X] (φ : X →* G)
    (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center X) (h2 : IsPGroup 2 φ.ker)
    (hD : ∀ T : Sylow 2 G, ∃ m : ℕ, 1 ≤ m ∧ Nonempty (T ≃* DihedralGroup (2 ^ m))) :
    Nat.card φ.ker ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 X := default
  obtain ⟨m, hm, ⟨e⟩⟩ := hD (S.mapSurjective hφ)
  set S₀ : Subgroup X := (S : Subgroup X) with hS₀
  let e' : ↥(S₀.map φ) ≃* DihedralGroup (2 ^ m) := e
  let ψ : ↥S₀ →* ↥(S₀.map φ) := φ.subgroupMap S₀
  have hψ : Function.Surjective ψ := φ.subgroupMap_surjective S₀
  let ε : ↥S₀ →* DihedralGroup (2 ^ m) := e'.toMonoidHom.comp ψ
  have hε : Function.Surjective ε := e'.surjective.comp hψ
  have hker : ∀ x : ↥S₀, ε x = 1 ↔ (x : X) ∈ φ.ker := by
    intro x
    simp only [ε, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      MonoidHom.mem_ker]
    constructor
    · intro h
      simpa [ψ] using congrArg Subtype.val h
    · intro h
      exact Subtype.ext (by simpa [ψ] using h)
  have hZS : φ.ker ≤ S₀ := by
    intro a ha
    obtain ⟨k, hk⟩ := h2 ⟨a, ha⟩
    exact mem_sylow_of_mem_center S (hZ ha) (k := k) (by simpa using congrArg Subtype.val hk)
  have hZcomm : ∀ x : ↥S₀, (x : X) ∈ φ.ker → x ∈ commutator ↥S₀ := by
    intro x hx
    obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
    exact mem_commutator_sylow_of_mem_center S (hZ hx) (by simp)
      (k := k) (by simpa using congrArg Subtype.val hk)
  have hcomm_map : (commutator ↥S₀).map ψ = commutator ↥(S₀.map φ) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ψ hψ]
  have hcomm_ψ : commutator ↥S₀ = (commutator ↥(S₀.map φ)).comap ψ := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_comap, ← hcomm_map]
      exact Subgroup.mem_map_of_mem ψ hx
    · intro x hx
      rw [Subgroup.mem_comap, ← hcomm_map] at hx
      obtain ⟨c, hc, hcx⟩ := hx
      have hcx' : c⁻¹ * x ∈ commutator ↥S₀ := by
        refine hZcomm _ ?_
        have h1 : ε (c⁻¹ * x) = 1 := by
          have h2 : ψ c = ψ x := hcx
          simp [ε, map_mul, map_inv, h2]
        exact (hker _).1 h1
      simpa using (commutator ↥S₀).mul_mem hc hcx'
  have hcomm : commutator ↥S₀ = (dihedralRotationSubgroup m 1).comap ε := by
    rw [hcomm_ψ, commutator_eq_dihedral_even_rotations_comap (S₀.map φ) e', Subgroup.comap_comap]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hDcard : Nat.card (DihedralGroup (2 ^ (k + 1))) = 4 * 2 ^ k := by
    rw [DihedralGroup.nat_card, pow_succ]
    ring
  have hrot1 : (dihedralRotationSubgroup (k + 1) 1).index = 4 := by
    have h := (dihedralRotationSubgroup (k + 1) 1).card_mul_index
    rw [card_dihedralRotationSubgroup (by omega : 1 ≤ k + 1), hDcard,
      show k + 1 - 1 = k from rfl] at h
    generalize (dihedralRotationSubgroup (k + 1) 1).index = i at h ⊢
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos two_pos k) (by rw [h]; ring)).symm
  have hrot0 : (dihedralRotationSubgroup (k + 1) 0).index = 2 := by
    have h := (dihedralRotationSubgroup (k + 1) 0).card_mul_index
    rw [card_dihedralRotationSubgroup (by omega : 0 ≤ k + 1), hDcard,
      show k + 1 - 0 = k + 1 from rfl] at h
    generalize (dihedralRotationSubgroup (k + 1) 0).index = i at h ⊢
    have h' : 2 ^ k * (2 * i) = 2 ^ k * 4 := by rw [pow_succ] at h; linarith
    have := Nat.eq_of_mul_eq_mul_left (pow_pos two_pos k) h'
    omega
  set C : Subgroup ↥S₀ := (dihedralRotationSubgroup (k + 1) 0).comap ε with hCdef
  set Zs : Subgroup ↥S₀ := φ.ker.subgroupOf S₀ with hZsdef
  have hCindex : C.index = 2 := (Subgroup.index_comap_of_surjective _ hε).trans hrot0
  have hS' : (commutator ↥S₀).index = 4 := by
    rw [hcomm]; exact (Subgroup.index_comap_of_surjective _ hε).trans hrot1
  have hZsmem : ∀ x : ↥S₀, x ∈ Zs ↔ ε x = 1 := fun x => by
    rw [hZsdef, Subgroup.mem_subgroupOf, hker]
  have hZsC : Zs ≤ C := fun x hx => by
    rw [hCdef, Subgroup.mem_comap, (hZsmem x).1 hx]
    exact Subgroup.one_mem _
  have hZsc : Zs ≤ Subgroup.center ↥S₀ := fun x hx => by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hZ ((hZsmem x).1 hx |> (hker x).1))) y)
  have hab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    let f : ↥C →* ↥(dihedralRotationSubgroup (k + 1) 0) :=
      (ε.comp C.subtype).codRestrict _ (fun c => c.2)
    have hcyc : IsCyclic ↥(dihedralRotationSubgroup (k + 1) 0) := by
      rw [dihedralRotationSubgroup_def]; infer_instance
    have hfker : f.ker ≤ Subgroup.center ↥C := by
      intro c hc
      rw [Subgroup.mem_center_iff]
      intro d
      have hc1 : ε (c : ↥S₀) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
      apply Subtype.ext
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (hZ ((hker _).1 hc1))) (d : X)
    intro a ha b hb
    have := (f.isMulCommutative_of_isCyclic_of_ker_le_center hfker).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hcard := card_le_two_of_index_commutator hCindex hab hZsc hZsC hS'
  rwa [hZsdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv] at hcard

end CFSG.Quasithin
