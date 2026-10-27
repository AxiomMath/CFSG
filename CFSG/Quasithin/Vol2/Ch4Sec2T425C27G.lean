module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics
public import CFSG.Quasithin.EmptyFaithful.S153QPA1
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27E

public section

namespace CFSG.Quasithin.H13.Ch4.T425C27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SmithC27 CFSG.Quasithin.SBc17
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

noncomputable def slEquivOfRingEquiv {n : ℕ} {F F' : Type} [Field F] [Field F'] (f : F ≃+* F') :
    SpecialLinearGroup (Fin n) F ≃* SpecialLinearGroup (Fin n) F' where
  toFun := SpecialLinearGroup.map f.toRingHom
  invFun := SpecialLinearGroup.map f.symm.toRingHom
  left_inv x := by
    ext i j
    simp
  right_inv x := by
    ext i j
    simp
  map_mul' := map_mul _

open CFSG.SectionRank.ClassicalEven CFSG.QuasithinUnique.Vol2Native.EvenWit in
theorem two_le_pRank_psl3 {F : Type} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime]
    (hdvd : p ∣ Nat.card F - 1) :
    2 ≤ CFSG.Open.pRank p
      (⊤ : Subgroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL 3 F))) := by
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p
    (by rw [Nat.card_units]; exact hdvd)
  by_cases hp3 : p = 3
  · subst hp3
    exact two_le_pRank_three_of_cubic hζ _ (torusDiag_mem_SL (by simp [Fin.prod_univ_three]))
      (torusDiag_mem_SL (by simp [Fin.prod_univ_three])) (cycGL_mem_SL F)
  · exact two_le_pRank_torus hp3 hζ (i₀ := (0 : Fin 3)) (i₁ := 1) (i₂ := 2) (by decide)
      (by decide) (by decide) (torusDiag_mem_SL (prod_torusVec ζ _ _))
      (torusDiag_mem_SL (prod_torusVec ζ _ _))

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {H R M K J : Subgroup G} (c : Ctx H R M K J) (hC27 : ASC27Statement G)
include c hC27

theorem false_of_sl32 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (e₀ : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hmax : IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
      (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))) : False := by
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime hF
  let e : ↥(autOn K V) ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm).trans
      (slEquivOfRingEquiv (ZMod.ringEquiv F hF).symm)
  obtain ⟨g, d, hd1, hd3, hP⟩ := QP.exists_conj_stabilizer_of_mulEquiv (by norm_num) hmax e
  have hPL : autOn (M ⊓ K) V ≤ autOn K V := autOn_mono' inf_le_right
  have hcard : Nat.card (autOn (M ⊓ K) V) = 2 ^ 3 * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).symm.toEquiv,
      ← Subgroup.card_map_of_injective (show Function.Injective e.toMonoidHom from e.injective), hP,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, ← flagStabilizer_singleton]
    have hset : ({d} : Set ℕ) = Set.Icc 1 (3 - 1) \ {3 - d} := by
      ext i
      simp only [Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_Icc]
      omega
    rw [hset, BinaryParabolic.card_parabolic_three (by omega) (by omega)]
    norm_num
  refine c.not_le_of_isSolvable hC27 ?_ (autOn_mono' c.J_le)
  refine isSolvable_of_prime_dvd Nat.prime_two Nat.prime_three fun r hr hrd => ?_
  rw [hcard] at hrd
  rcases eq_or_dvd_of_dvd_pow_mul hr Nat.prime_two hrd with h | h
  · exact Or.inl h
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)

end Ctx

end CFSG.Quasithin.H13.Ch4.T425C27
