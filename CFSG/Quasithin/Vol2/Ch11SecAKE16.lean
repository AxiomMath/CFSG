module

public import CFSG.Quasithin.Vol2.Ch11SecAKE15
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.QuasithinUnique

theorem card_sylow_of_card_7800 {G : Type} [Group G] [Finite G] (hG : Nat.card G = 7800)
    {P : Subgroup G} (hP : IsSylowTwoOf P ⊤) : Nat.card P = 8 := by
  have hidx : ¬ 2 ∣ P.index := by
    have := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at this
  obtain ⟨a, ha⟩ := hP.2.1.exists_card_eq
  have h1 := P.card_mul_index
  rw [hG, ha] at h1
  have ha3 : a ≤ 3 := by
    by_contra h
    have h16 : 2 ^ 4 ∣ 2 ^ a := Nat.pow_dvd_pow 2 (by omega)
    have : 2 ^ 4 ∣ 7800 := h16.trans ⟨_, h1.symm⟩
    norm_num at this
  interval_cases a
  · exact absurd ⟨3900, by omega⟩ hidx
  · exact absurd ⟨1950, by omega⟩ hidx
  · exact absurd ⟨975, by omega⟩ hidx
  · exact ha

variable {K : Type} [Field K] [Finite K]

theorem sylow_nonabelian (hK : Nat.card K = 5 ^ 2)
    {P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)} (hP : IsSylowTwoOf P ⊤) :
    ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ P.index := by
    have := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at this
  let P' : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := hP.2.1.toSylow hidx
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨5, 2, Nat.prime_five, by decide, by norm_num, hK⟩
  obtain ⟨m, -, ⟨eD⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd P'
  have hcardS : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = 7800 := by
    rw [CFSG.GorensteinWalter.psl2_card_formula K hodd, hK]
    norm_num
  have hP8 := card_sylow_of_card_7800 hcardS hP
  have hm : m = 2 := by
    have h := Nat.card_congr eD.toEquiv
    rw [DihedralGroup.nat_card] at h
    have h' : Nat.card (P' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) = 8 := hP8
    rw [h'] at h
    have : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl this
  subst hm
  obtain ⟨x, y, hxy⟩ := d8_nonabelian
  refine ⟨(eD.symm x : P'), (eD.symm x).2, (eD.symm y : P'), (eD.symm y).2, fun h => hxy ?_⟩
  apply eD.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext h

theorem psl225_subgroup [Fact (Nat.Prime 5)] (hK : Nat.card K = 5 ^ 2)
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
    (hns : ¬ Group.IsSolvable H) :
    Nat.card H = 60 ∨ Nat.card H = 7800 ∨
      (Nat.card H = 120 ∧ Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField 5 1))) := by
  have solv_of : ∀ {T : Type} [Group T] [Group.IsSolvable T], (H ≃* T) → False := fun e =>
    hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, -, hHz, ⟨eD⟩⟩ | ⟨-, ⟨eA4⟩⟩ | ⟨-, ⟨eS4⟩⟩ | ⟨-, ⟨eA5⟩⟩ |
      ⟨m, t, -, -, N, C, hNn, hNel, -, hCcyc, -, -, hNC⟩ | ⟨m, hm0, hmf, ⟨ePSL⟩⟩ |
      ⟨m, hm0, hmf, ⟨ePGL⟩⟩
  · have : IsMulCommutative H := hel.toIsMulCommutative
    exact absurd (Group.isSolvable_of_comm fun a b => mul_comm' a b) hns
  · have : IsMulCommutative H := hcyc.isMulCommutative
    exact absurd (Group.isSolvable_of_comm fun a b => mul_comm' a b) hns
  · have hz : z ≠ 0 := by
      rintro rfl
      have h1 : Nat.card H = 0 := by simpa using hHz
      have := Nat.card_pos (α := H)
      omega
    have : NeZero z := ⟨hz⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact (solv_of eD).elim
  · have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact (solv_of eA4).elim
  · have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact (solv_of eS4).elim
  · left
    rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  · exfalso
    have : IsMulCommutative N := hNel.toIsMulCommutative
    have : Group.IsSolvable N := Group.isSolvable_of_comm fun a b => mul_comm' a b
    have hmapC : C.map (QuotientGroup.mk' N) = ⊤ := by
      have h := congrArg (Subgroup.map (QuotientGroup.mk' N)) hNC
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
    have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp C.subtype) := by
      intro q
      have hq : q ∈ C.map (QuotientGroup.mk' N) := hmapC ▸ Subgroup.mem_top q
      obtain ⟨c, hc, rfl⟩ := hq
      exact ⟨⟨c, hc⟩, rfl⟩
    have : IsCyclic (H ⧸ N) := isCyclic_of_surjective _ hsurj
    have : Group.IsSolvable (H ⧸ N) :=
      Group.isSolvable_of_comm fun a b => IsCyclic.isMulCommutative.is_comm.comm a b
    exact hns (Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
  · have hm : m = 1 ∨ m = 2 := by
      have := Nat.le_of_dvd (by norm_num) hmf
      omega
    rw [Nat.card_congr ePSL.toEquiv,
      CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField (by norm_num) hm0]
    rcases hm with rfl | rfl
    · left; norm_num
    · right; left; norm_num
  · have hm : m = 1 := by
      have := Nat.le_of_dvd (by norm_num) hmf
      omega
    subst hm
    refine Or.inr (Or.inr ⟨?_, ⟨ePGL⟩⟩)
    rw [Nat.card_congr ePGL.toEquiv,
      CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hm0]
    norm_num

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
