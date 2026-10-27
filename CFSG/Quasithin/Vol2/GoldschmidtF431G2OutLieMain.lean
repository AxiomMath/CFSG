module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructLoc
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45
  CFSG.QuasithinUnique CFSG.GH74.GLS.Stage4.Hex CFSG.Quasithin.H13.F431.D4q.Struct

section Generic

theorem map_conj_conj_inv' {H : Type} [Group H] (S : Subgroup H) (c : H) :
    (S.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = S := by
  rw [Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end Generic

section Normalize


theorem exists_normalized_g2 {D : Type} [Group D] {f : ℕ} (hD : LieModel D .G2 0 2 f)
    (A : LieAmalgamExt D) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧ 2 ≤ f ∧
      Nonempty (D ≃* C K) ∧
      ∃ A' : LieAmalgamExt (C K), IsNormalized A' ∧ Nonempty (KIso A A') := by
  obtain ⟨hf, K, hF, hFin, hcp, hKc, ⟨ε₀⟩⟩ := g2_model_data hD
  have hFinC : Finite (C K) := finite_C (K := K)
  have YS := g2_yamStd hKc hf
  obtain ⟨c, hTD, hP⟩ := YS.pair ε₀ A.yam
  let E : LieExt D A.N1 A.N2 := A.toLieExt
  let E1 : LieExt (C K) A.N1 A.N2 := E.congr ε₀
  let L1 : LocIso E E1 := E.congrOfLocIso ε₀ _ rfl
  let E2 : LieExt (C K) A.N1 A.N2 := E1.conjSylow c⁻¹
  let L2 : LocIso E1 E2 :=
    E1.congrOfLocIso (MulAut.conj c⁻¹) E1.Mbar (E1.Mbar_eq_map_conj c⁻¹)
  have hfin2 : ∀ i : Fin Tag.G2.rank, i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ := by decide
  have hne01 : Setup.X6.g2Index 0 ≠ Setup.X6.g2Index 1 := fun h =>
    absurd (Setup.X6.g2Index_injective h) (by decide)
  have hidx : (Setup.X6.g2Index 0 = ⟨0, by decide⟩ ∧ Setup.X6.g2Index 1 = ⟨1, by decide⟩) ∨
      (Setup.X6.g2Index 0 = ⟨1, by decide⟩ ∧ Setup.X6.g2Index 1 = ⟨0, by decide⟩) := by
    rcases hfin2 (Setup.X6.g2Index 0) with h0 | h0 <;>
      rcases hfin2 (Setup.X6.g2Index 1) with h1 | h1
    · exact absurd (h0.trans h1.symm) hne01
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hne01
  have hP1 : ∀ (X : Subgroup D) (Y : Subgroup (C K)),
      X.map ε₀.toMonoidHom = Y.map (MulAut.conj c).toMonoidHom →
        (X.map ε₀.toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = Y :=
    fun X Y h => by rw [h, map_conj_conj_inv']
  refine ⟨K, hF, hFin, hcp, hKc, hf, ⟨ε₀⟩, E2.toLieAmalgamExt, ⟨?_, ?_⟩, ⟨(L1.trans L2).toKIso⟩⟩
  · show E1.TD.map (MulAut.conj c⁻¹).toMonoidHom = U K
    rw [show E1.TD = A.TD.map ε₀.toMonoidHom from rfl, hTD, map_conj_conj_inv']
    rfl
  · have q1 : ∀ i, (A.P1.map ε₀.toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom =
        (parabolicSubgroup Tag.G2 K {Setup.X6.g2Index i}).subgroupOf (adjointGroup Tag.G2 K) →
        E2.P1 = Pmin K (Setup.X6.g2Index i) := fun i h => h
    have q2 : ∀ i, (A.P2.map ε₀.toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom =
        (parabolicSubgroup Tag.G2 K {Setup.X6.g2Index i}).subgroupOf (adjointGroup Tag.G2 K) →
        E2.P2 = Pmin K (Setup.X6.g2Index i) := fun i h => h
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have a1 := q1 0 (hP1 _ _ h1)
      have a2 := q2 1 (hP1 _ _ h2)
      rcases hidx with ⟨e0, e1⟩ | ⟨e0, e1⟩
      · rw [e0] at a1
        rw [e1] at a2
        exact Or.inr ⟨a1, a2⟩
      · rw [e0] at a1
        rw [e1] at a2
        exact Or.inl ⟨a1, a2⟩
    · have a1 := q1 1 (hP1 _ _ h1)
      have a2 := q2 0 (hP1 _ _ h2)
      rcases hidx with ⟨e0, e1⟩ | ⟨e0, e1⟩
      · rw [e1] at a1
        rw [e0] at a2
        exact Or.inl ⟨a1, a2⟩
      · rw [e1] at a1
        rw [e0] at a2
        exact Or.inr ⟨a1, a2⟩

theorem twoOutConcl_of_normalized {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (A : LieAmalgamExt (C K)) (h : IsNormalized A)
    (hev : ¬ Odd (Nat.card ↥A.K / Nat.card (C K))) : TwoOutConcl A := by
  obtain ⟨σ₁, hσ₁, hgen⟩ := exists_gen_Fz hn hK A
  have hevσ := even_orderOf_of_not_odd hn hK h hσ₁ hgen hev
  rcases h.pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨_, _, _, _, _, Or.inl (f431TwoOut_of_gen hn hK h hσ₁ hgen hevσ
      (mem_Mb1_iff hn hK h h1) (mem_Mb2_iff hn hK h h2))⟩
  · exact ⟨_, _, _, _, _, Or.inr (f431TwoOut_of_gen hn hK h hσ₁ hgen hevσ
      (mem_Mb2_iff hn hK h h2) (mem_Mb1_iff hn hK h h1))⟩

end Normalize

end CFSG.Quasithin.H13.F431.G2.OutK

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.Quasithin.H13.F431.G2.OutK

section Final


theorem f431TwoOutLieProp_g2 (f : ℕ) : F431TwoOutLieProp .G2 0 f := by
  intro D _ hD A hnodd
  obtain ⟨K, hF, hFin, hcp, hKc, hf, ⟨ε⟩, A', hN, ⟨L⟩⟩ := exists_normalized_g2 hD A
  have hFinC : Finite (C K) := finite_C (K := K)
  have hFinA : Finite (MulAut (C K)) := finite_mulAut_C (K := K)
  have : Finite D := Finite.of_injective ε ε.injective
  have hFinD : Finite (MulAut D) :=
    Finite.of_injective (fun φ : MulAut D => (φ : D → D)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hcard : Nat.card ↥A'.K / Nat.card (C K) = Nat.card ↥A.K / Nat.card D := by
    rw [L.card_K, Nat.card_congr ε.toEquiv.symm]
  exact L.twoOutConcl (twoOutConcl_of_normalized hf hKc A' hN (hcard ▸ hnodd))

end Final

end CFSG.Quasithin.H13.F431.G2
