module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.F918X4
public import CFSG.Quasithin.Background.F918XN2Aut
public import CFSG.Quasithin.Background.FFC4Ext

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace SLTwist

variable {n : ℕ} {K : Type} [Field K]

theorem twoClassMod_of_natural {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} [Finite K]
    (hn : 3 ≤ n) {π : ↥(StatedSL n K) →* ↥L}
    (hπ : (FFModel.nat (StatedSL n K)).RealizesVia L ⊤ ⊥ π) : TwoClassMod L := by
  have hbij : Function.Bijective π :=
    ⟨hπ.injective_of_faithful (FFModel.nat_faithful _), hπ.1⟩
  let s : Matrix.SpecialLinearGroup (Fin n) K ≃* ↥(StatedSL n K) :=
    specialLinearGroupEquivStatedSL n K
  let ψ : Matrix.SpecialLinearGroup (Fin n) K ≃* ↥L := s.trans (MulEquiv.ofBijective π hbij)
  refine twoClassMod_of_equiv_sl hn ψ fun β hβ => ?_
  obtain ⟨A, σ, hA⟩ := hβ
  refine mem_realized_of_semilinear hπ (MulAut.congr ψ β) (MulAut.congr s β) ?_ A σ ?_
  · intro γ
    have h1 : ψ.symm (π γ) = s.symm γ := by
      apply ψ.injective
      simp [ψ]
    simp [MulAut.congr_apply, h1, ψ]
  · intro γ
    have h1 := hA (s.symm γ)
    have h2 : ((s.symm γ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((γ : Matrix.GeneralLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have := specialLinearGroupEquivStatedSL_coe n K (s.symm γ)
      rw [show specialLinearGroupEquivStatedSL n K (s.symm γ) = γ from s.apply_symm_apply γ]
        at this
      exact this.symm
    have h3 : ((((MulAut.congr s β) γ : ↥(StatedSL n K)) : Matrix.GeneralLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = (β (s.symm γ) : Matrix (Fin n) (Fin n) K) :=
      specialLinearGroupEquivStatedSL_coe n K _
    rw [h3, h1, h2]

end SLTwist

theorem case2Twist_holds : Case2Twist := by
  intro V _ _ _ G L _ h2
  obtain ⟨-, ⟨n, hn⟩, -⟩ := h2
  refine ⟨?_, ?_⟩
  · obtain ⟨K, hK, hfin, -, π, hπ⟩ := hn
    exact SLTwist.twoClassMod_of_natural (by norm_num) hπ
  · obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
    exact Or.inr (Or.inl (Or.inl ⟨n, K, hK, hfin, hcard, ⟨e.symm⟩⟩))

theorem case9Twist_holds : Case9Twist := by
  intro V _ _ _ G L _ h9
  obtain ⟨-, d, hd, hn, -⟩ := h9
  refine ⟨?_, ?_⟩
  · obtain ⟨K, hK, hfin, -, π, hπ⟩ := hn
    exact SLTwist.twoClassMod_of_natural (by omega) hπ
  · obtain ⟨K, hK, hfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hn
    have hcard' : Nat.card K = 2 := by rw [hcard]; norm_num
    rcases hd with rfl | rfl
    · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨K, hK, hfin, hcard', ⟨e.symm⟩⟩)))
    · exact Or.inr (Or.inl (Or.inr (Or.inr ⟨K, hK, hfin, hcard', ⟨e.symm⟩⟩)))

theorem case11Twist_holds : Case11Twist := by
  intro V _ _ _ G L A _ h11
  obtain ⟨-, -, -, -, π, hπ, -⟩ := h11
  have hbij : Function.Bijective π :=
    ⟨hπ.injective_of_faithful (FFC.extSq_faithful (by norm_num)), hπ.1⟩
  let e : ↥(StatedSL 5 (ZMod 2)) ≃* ↥L := MulEquiv.ofBijective π hbij
  have hcard : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  refine ⟨SLTwist.twoClassMod_of_equiv_statedSL_two (by norm_num) hcard e.symm, ?_⟩
  exact Or.inr (Or.inl (Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩)))

end CFSG.Quasithin.F918X
