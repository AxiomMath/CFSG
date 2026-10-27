module

public import CFSG.RankThree.GroupTheory.SteinbergCEExtraspecialMinusModule

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG CFSG.RankThree.GroupTheory

variable {S : Type*} [Group S] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def restrictRep (ρ : Representation K S V) (W : Submodule K V)
    (hW : ∀ s : S, ∀ v ∈ W, ρ s v ∈ W) : Representation K S W where
  toFun s := (ρ s).restrict (fun v hv => hW s v hv)
  map_one' := by
    ext v
    simp
  map_mul' s t := by
    ext v
    simp

theorem restrictRep_apply (ρ : Representation K S V) (W : Submodule K V)
    (hW : ∀ s : S, ∀ v ∈ W, ρ s v ∈ W) (s : S) (v : W) :
    ((restrictRep ρ W hW s v : W) : V) = ρ s v := rfl

theorem exists_center_generator_of_extraspecial [Finite S] (hS : IsExtraspecialPGroup 2 S) :
    ∃ z : S, Subgroup.center S = Subgroup.zpowers z ∧ z ≠ 1 := by
  obtain ⟨z, hzc, hz1⟩ : ∃ z ∈ Subgroup.center S, z ≠ 1 := by
    by_contra h
    push Not at h
    have h1 : Subgroup.center S = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    have h2 := hS.2.2.2
    rw [h1, Subgroup.card_bot] at h2
    omega
  have hle : Subgroup.zpowers z ≤ Subgroup.center S := Subgroup.zpowers_le.2 hzc
  have hdvd : orderOf z ∣ 2 := by
    rw [← Nat.card_zpowers, ← hS.2.2.2]
    exact Subgroup.card_dvd_of_le hle
  have hord : orderOf z = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  refine ⟨z, ?_, hz1⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Nat.card_zpowers, hord, hS.2.2.2]

theorem minimal_module_facts [Finite S] (hK : (2 : K) ≠ 0) [FiniteDimensional K V]
    (hS : IsExtraspecialPGroup 2 S) (hcard : Nat.card S = 32)
    (ρ : Representation K S V) (hρ : Function.Injective ρ) (hdim : Module.finrank K V = 4) :
    (∀ z : S, Subgroup.center S = Subgroup.zpowers z → z ≠ 1 → ρ z = -1) ∧
    (∀ W : Submodule K V, (∀ s : S, ∀ v ∈ W, ρ s v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    (∀ s : S, s ∉ Subgroup.center S → orderOf s = 2 → ∃ v : V, v ≠ 0 ∧ ρ s v = v) := by
  classical
  have hcard' : Nat.card S = 2 ^ (1 + 2 * 2) := by rw [hcard]; norm_num
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hz : ∀ z : S, Subgroup.center S = Subgroup.zpowers z → z ≠ 1 → ρ z = -1 := by
    intro z hzc hz1
    have hzmem : z ∈ Subgroup.center S := by rw [hzc]; exact Subgroup.mem_zpowers z
    have hzcomm : ∀ s : S, s * z = z * s := fun s => Subgroup.mem_center_iff.mp hzmem s
    have hord : orderOf z = 2 := by
      rw [← Nat.card_zpowers, ← hzc]
      exact hS.2.2.2
    have hzz : z * z = 1 := by
      rw [← pow_two, ← hord]
      exact pow_orderOf_eq_one z
    have hρzz : ∀ v : V, ρ z (ρ z v) = v := by
      intro v
      rw [← Module.End.mul_apply, ← map_mul, hzz, map_one]
      rfl
    set Vm : Submodule K V := Module.End.eigenspace (ρ z) (-1) with hVm
    have hVminv : ∀ s : S, ∀ v ∈ Vm, ρ s v ∈ Vm := by
      intro s v hv
      rw [hVm, Module.End.mem_eigenspace_iff] at hv ⊢
      have h1 : ρ z (ρ s v) = ρ s (ρ z v) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hzcomm s]
      rw [h1, hv, map_smul]
    have hVmne : Vm ≠ ⊥ := by
      intro hbot
      have hall : ∀ v : V, ρ z v = v := by
        intro v
        have hw : (v - ρ z v) ∈ Vm := by
          rw [hVm, Module.End.mem_eigenspace_iff, map_sub, hρzz]
          module
        rw [hbot, Submodule.mem_bot] at hw
        exact (sub_eq_zero.mp hw).symm
      have h1 : ρ z = ρ 1 := by
        ext v
        rw [map_one]
        exact hall v
      exact hz1 (hρ h1)
    have : Nontrivial Vm := Submodule.nontrivial_iff_ne_bot.mpr hVmne
    have hρmz : restrictRep ρ Vm hVminv z = -1 := by
      ext v
      have hv : ρ z v = (-1 : K) • (v : V) := Module.End.mem_eigenspace_iff.mp v.2
      change ρ z v = -(v : V)
      rw [hv]
      simp
    have hb := (extraspecial_two_minus_module_bound hS hcard' hzc hK
      (restrictRep ρ Vm hVminv) hρmz).1
    have hle : Module.finrank K Vm ≤ Module.finrank K V := Submodule.finrank_le Vm
    have htop : Vm = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    ext v
    have hv : v ∈ Vm := htop ▸ Submodule.mem_top
    have hv' : ρ z v = (-1 : K) • v := Module.End.mem_eigenspace_iff.mp hv
    rw [hv']
    simp
  refine ⟨hz, ?_, ?_⟩
  ·
    intro W hW
    obtain ⟨z, hzc, hz1⟩ := exists_center_generator_of_extraspecial hS
    have hρz := hz z hzc hz1
    by_cases hWbot : W = ⊥
    · exact Or.inl hWbot
    · right
      have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWbot
      have hρWz : restrictRep ρ W hW z = -1 := by
        ext v
        change ρ z v = -(v : V)
        rw [hρz]
        simp
      have hb := (extraspecial_two_minus_module_bound hS hcard' hzc hK
        (restrictRep ρ W hW) hρWz).1
      exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) (by omega))
  ·
    intro s hs hs2
    obtain ⟨z, hzc, hz1⟩ := exists_center_generator_of_extraspecial hS
    have hρz := hz z hzc hz1
    have hb := (extraspecial_two_minus_module_bound hS hcard' hzc hK ρ hρz).2 s hs hs2
    have hpos : 0 < Module.finrank K (Module.End.eigenspace (ρ s) 1) := by omega
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    refine ⟨v, fun h => hv0 (Subtype.ext h), ?_⟩
    have := Module.End.mem_eigenspace_iff.mp hv
    simpa using this

end CFSG.RankThree.PartOne.Torsion37
