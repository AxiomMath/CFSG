module

public import CFSG.Quasithin.EmptyFaithful.S146B0
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base

public section

namespace CFSG.Quasithin

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a

section Bridge

noncomputable def slMulEquivOfRingEquiv {K K' : Type} [Field K] [Field K'] (ε : K ≃+* K') (n : ℕ) :
    SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) K' :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map ε.toRingHom) (SpecialLinearGroup.map ε.symm.toRingHom)
    (MonoidHom.ext fun A => Subtype.ext (by
      ext i j
      simp [SpecialLinearGroup.map_apply_coe]))
    (MonoidHom.ext fun A => Subtype.ext (by
      ext i j
      simp [SpecialLinearGroup.map_apply_coe]))

noncomputable def slEquivProjectiveSL_two {K : Type} [Field K] (hK : ∀ c : Kˣ, c = 1) (n : ℕ) :
    SpecialLinearGroup (Fin n) K ≃* projectiveSL n K := by
  have hscal : scalars n K = ⊥ := by
    rw [eq_bot_iff]
    rintro A ⟨c, -, hA⟩
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [hA, hK c]
    simp
  exact MulEquiv.ofBijective (proj n K)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [ker_proj, hscal]), proj_surjective n K⟩

theorem nonempty_mulEquiv_slThree_of_isPSL {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nonempty (X ≃* SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have : Fintype K := Fintype.ofFinite K
  have hcard' : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card]
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  have hunits : ∀ c : Kˣ, c = 1 := fun c => by
    have h1 : Units.map ε.toMonoidHom c = 1 := Subsingleton.elim _ _
    exact (Units.map_injective ε.injective) (by simpa using h1)
  exact ⟨e.trans ((statedSLEquivProjectiveSL 3 K).trans
    ((slEquivProjectiveSL_two hunits 3).symm.trans (slMulEquivOfRingEquiv ε 3)))⟩

theorem isPSL_three_two_iff {X : Type} [Group X] :
    IsPSL 3 2 1 X ↔ Nonempty (X ≃* SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  ⟨nonempty_mulEquiv_slThree_of_isPSL, fun ⟨e⟩ =>
    CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two e⟩

variable {G : Type} [Group G]

theorem kbarIsL3Two_of_isPSL {K : Subgroup G} (h : IsPSL 3 2 1 (KBar K)) : KbarIsL3Two K :=
  nonempty_mulEquiv_slThree_of_isPSL h

theorem isPSL_of_kbarIsL3Two {K : Subgroup G} (h : KbarIsL3Two K) : IsPSL 3 2 1 (KBar K) :=
  isPSL_three_two_iff.mpr h

end Bridge

end CFSG.Quasithin
