module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Core

public section

namespace CFSG.Quasithin.A312U3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.A38c15
open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.RankThree.CentralCover
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

theorem coreProj_of_coreC (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    (hC : ∀ M : Subgroup ↥(unitarySU p 1 F 3), Odd M.index → M ≠ ⊤ → CoreC p M)
    (M' : Subgroup (StatedProj (unitarySU p 1 F 3))) (hodd : Odd M'.index) (hne : M' ≠ ⊤) :
    Group.IsSolvable ↥M' ∨ IsSL2 p ↥(perfectCore M') ∨ (p = 5 ∧ IsAlt 6 ↥(perfectCore M')) := by
  classical
  have hU := uniData (p := p) hF
  let π : ↥(unitarySU p 1 F 3) →* StatedProj (unitarySU p 1 F 3) := statedProjMk _
  have hπ : Function.Surjective π := statedProjMk_surjective _
  let M : Subgroup ↥(unitarySU p 1 F 3) := M'.comap π
  have hMidx : M.index = M'.index := Subgroup.index_comap_of_surjective M' hπ
  have hMmap : M.map π = M' := Subgroup.map_comap_eq_self_of_surjective hπ M'
  have hMne : M ≠ ⊤ := by
    intro htop
    apply hne
    rw [← hMmap, htop, Subgroup.map_top_of_surjective _ hπ]
  have hker3 : ∀ z ∈ π.ker, z ^ 3 = 1 := fun z hz => Lemma41aU3.ker_pow_three hU z hz
  rcases hC M (by rwa [hMidx]) hMne with hs | hSL | ⟨hp5, hHat, hz⟩
  · left
    rw [← hMmap]
    exact isSolvable_map_hom π M hs
  · right
    left
    have hperf : Group.IsPerfect ↥(perfectCore M) :=
      Subgroup.isPerfect_iff.mpr (perfectCore_perfect M)
    have hp3 : p ≠ 3 := ne_three_of_leviBlock (Or.inl hSL : IsLeviBlock p ↥(perfectCore M))
    have hinj : ∀ x ∈ perfectCore M, ∀ y ∈ perfectCore M, π x = π y → x = y := by
      intro x hx y hy hxy
      have hzm : x⁻¹ * y ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
      let w : ↥(perfectCore M) := ⟨x⁻¹ * y, mul_mem (inv_mem hx) hy⟩
      have hw : w = 1 := by
        refine IsLeviBlock.eq_one_of_central hp2 (Or.inl hSL) ?_ ?_
        · intro k
          apply Subtype.ext
          exact (Subgroup.mem_center_iff.mp (ker_statedProjMk_le_center _ hzm) k.1)
        · have h1 : orderOf w = orderOf (x⁻¹ * y) := (Subgroup.orderOf_coe w).symm
          rw [h1]
          have hd : orderOf (x⁻¹ * y) ∣ 3 := orderOf_dvd_of_pow_eq_one (hker3 _ hzm)
          refine Nat.Coprime.coprime_dvd_left hd ?_
          refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun hdvd => ?_
          rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h2 | h2
          · omega
          · exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Fact.out).mp h2).symm
      have : x⁻¹ * y = 1 := congrArg Subtype.val hw
      exact inv_mul_eq_one.mp this
    obtain ⟨e⟩ := hSL
    exact ⟨((perfectCoreMapEquiv π M hinj).trans
      (MulEquiv.subgroupCongr (by rw [hMmap]))).symm.trans e⟩
  · right
    right
    refine ⟨hp5, ?_⟩
    obtain ⟨-, -, ⟨φ⟩⟩ := hHat
    let f : ↥(perfectCore M) →* StatedProj (unitarySU p 1 F 3) := π.comp (perfectCore M).subtype
    have hkerf : f.ker = Subgroup.center ↥(perfectCore M) := by
      ext z
      rw [MonoidHom.mem_ker]
      constructor
      · intro hz1
        have hzker : (z : ↥(unitarySU p 1 F 3)) ∈ π.ker := hz1
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        exact (Subgroup.mem_center_iff.mp (ker_statedProjMk_le_center _ hzker)) k.1
      · intro hzc
        have h1 := hz z hzc
        show π (z : ↥(unitarySU p 1 F 3)) = 1
        exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h1)
    have hrange : f.range = perfectCore M' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, CFSG.Quasithin.map_perfectCore, hMmap]
    exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkerf).trans φ))⟩

section Transport

variable {Γ Γ' : Type} [Group Γ] [Group Γ']

theorem core_of_equiv [Finite Γ] [Finite Γ'] (e : Γ ≃* Γ') {P : ∀ (K : Type) [Group K], Prop}
    (hP : ∀ (K L : Type) [Group K] [Group L], K ≃* L → P K → P L) {M : Subgroup Γ}
    (h : Group.IsSolvable ↥(M.map e.toMonoidHom) ∨ P ↥(perfectCore (M.map e.toMonoidHom))) :
    Group.IsSolvable ↥M ∨ P ↥(perfectCore M) := by
  rcases h with hs | hP'
  · left
    exact Group.isSolvable_of_isSolvable_injective
      (f := (M.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.injective _)
  · right
    exact hP _ _ (((perfectCore M).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (CFSG.Quasithin.map_perfectCore e.toMonoidHom M))).symm hP'

theorem odd_ne_top_map (e : Γ ≃* Γ') {M : Subgroup Γ} (hodd : Odd M.index) (hne : M ≠ ⊤) :
    Odd (M.map e.toMonoidHom).index ∧ M.map e.toMonoidHom ≠ ⊤ := by
  refine ⟨by rwa [Subgroup.index_map_of_bijective e.bijective M], fun htop => hne ?_⟩
  rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective M, htop,
    Subgroup.comap_top]

end Transport

end CFSG.Quasithin.A312U3
