module

public import CFSG.Quasithin.Background.RonanE114Pair
public import CFSG.Quasithin.Background.RonanE114A7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.RonanE114

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11

section Pair

open CFSG.QuasithinUnique.Setup.Family

theorem flagStabilizer_pair_invariant_four (α : MulAut (SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hα : (unitriangular 4 (ZMod 2)).map α.toMonoidHom = unitriangular 4 (ZMod 2)) :
    (flagStabilizer 4 (ZMod 2) {1, 4 - 1}).map α.toMonoidHom = flagStabilizer 4 (ZMod 2) {1, 4 - 1} ∧
      (flagStabilizer 4 (ZMod 2) {2, 4 - 2}).map α.toMonoidHom =
        flagStabilizer 4 (ZMod 2) {2, 4 - 2} := by
  set β : MulAut (projectiveSL 4 (ZMod 2)) :=
    (projEquiv 4).symm.trans (α.trans (projEquiv 4)) with hβ
  have hβp : ∀ x : SpecialLinearGroup (Fin 4) (ZMod 2),
      β (proj 4 (ZMod 2) x) = proj 4 (ZMod 2) (α x) := by
    intro x
    have h1 : proj 4 (ZMod 2) x = projEquiv 4 x := rfl
    have h2 : proj 4 (ZMod 2) (α x) = projEquiv 4 (α x) := rfl
    rw [h1, h2, hβ]
    simp
  have hmap : ∀ Q : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)),
      (Q.map (proj 4 (ZMod 2))).map β.toMonoidHom = (Q.map α.toMonoidHom).map (proj 4 (ZMod 2)) := by
    intro Q
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hβp x
  have hU : (projUnitriangular 4 (ZMod 2)).map β.toMonoidHom = projUnitriangular 4 (ZMod 2) := by
    rw [projUnitriangular, hmap, hα]
  obtain ⟨h1, h2⟩ := pair_invariant (n := 4) (by norm_num) β hU
  have e1 := map_proj_flagStabilizer_pair (n := 4) 1 (4 - 1)
  have e2 := map_proj_flagStabilizer_pair (n := 4) 2 (4 - 2)
  rw [← e1, hmap] at h1
  rw [← e2, hmap] at h2
  have hinj := Subgroup.map_injective (proj_injective_zmod_two 4)
  exact ⟨hinj h1, hinj h2⟩

theorem solvable_flagStabilizer_four {I : Set ℕ}
    (hsmall : ∀ a m : ℕ, a + m ≤ 4 → (a = 0 ∨ a ∈ I) → (a + m = 4 ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) → m ≤ 2) :
    Group.IsSolvable ↥(flagStabilizer 4 (ZMod 2) I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  exact (isSolvable_iff_perfectCore_eq_bot _).mpr
    (perfectCore_eq_bot_of_small (n := 4) hK2 (by norm_num) hsmall)

theorem hasSolvInvPair_sl4 : HasSolvInvPair (SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 4) (by norm_num)
  have hU : IsSylowTwoOf (unitriangular 4 (ZMod 2)) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hUle : ∀ I : Set ℕ, unitriangular 4 (ZMod 2) ≤ flagStabilizer 4 (ZMod 2) I := fun I =>
    (unitriangular_le_upperTriangular 4 (ZMod 2)).trans (upperTriangular_le_flagStabilizer I)
  refine ⟨unitriangular 4 (ZMod 2), flagStabilizer 4 (ZMod 2) {1, 4 - 1},
    flagStabilizer 4 (ZMod 2) {2, 4 - 2}, hU, hUle _, hUle _, solvable_flagStabilizer_four ?_,
    solvable_flagStabilizer_four ?_, flagStabilizer_sup_eq_top (by norm_num),
    fun α hα => flagStabilizer_pair_invariant_four α hα⟩
  · intro a m h ha hb hno
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hno
    by_contra hm
    have := hno 1 (Or.inl rfl)
    have := hno (4 - 1) (Or.inr rfl)
    omega
  · intro a m h ha hb hno
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hno
    by_contra hm
    have := hno 2 (Or.inl rfl)
    omega

end Pair

variable {G : Type} [Group G] [Finite G]

theorem nParam_eq_one_of_isPSL42 {T : Subgroup G} (hL : IsPSL 4 2 1 (ASInputs.FStar G))
    (hT : quasithinIsSylowTwo T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) = 1 := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hL
  have hK : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have hKc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let σ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hKc
  let φ : ↥(CFSG.generalizedFitting G) ≃* SpecialLinearGroup (Fin 4) (ZMod 2) :=
    e.trans ((slEquivStatedProj hK 4).symm.trans (L52.slEquivOfRingEquiv σ 4))
  refine le_antisymm (nParam_le_one_of_hasSolvInvPair hasSolvInvPair_sl4 hLn φ hTs hFT) ?_
  refine Vol2.Ch11.SecE3.one_le_nParam_of_not_odd
    (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G) ?_)
  rw [Nat.card_congr φ.toEquiv]
  have hU : Nat.card (unitriangular 4 (ZMod 2)) = 2 ^ 6 := by
    rw [card_unitriangular, Nat.card_zmod]
  have hdvd := Subgroup.card_subgroup_dvd_card (unitriangular 4 (ZMod 2))
  rw [hU] at hdvd
  exact dvd_trans (dvd_pow_self 2 (by norm_num)) hdvd

end CFSG.Quasithin.RonanE114
