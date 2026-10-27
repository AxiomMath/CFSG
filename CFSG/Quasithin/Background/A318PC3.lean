module

public import CFSG.Quasithin.Background.A318PC6
public import CFSG.Quasithin.Background.A318PHatInst
public import CFSG.Quasithin.Background.A318PCenter

public section

namespace CFSG.Quasithin

open CFSG.RankThree.PartTwo.Sec4

@[expose] def QCentralTail : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal], CFSG.IsQuasisimple ↥S →
    Nat.card (Subgroup.center ↥S) = 3 → ∀ (s : Bool) (q : ℕ), IsSLEps3 s q ↥S →
    Int.ModEq 3 (q : ℤ) (if s then 1 else -1) → CFSG.pPrimeCore 3 X = ⊥ →
    2 ≤ CFSG.Open.pRank 3 S → CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 → ∀ x : X, orderOf x = 3 →
      x ∉ S → oPrimeResidualOf 3 (⊤ : Subgroup X) = S ⊔ Subgroup.zpowers x

namespace A318P

open CFSG.Assembly.LowTwoRank (StatedScalars)

theorem false_of_isHat {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]
    (hQ : CFSG.IsQuasisimple ↥S) (hZ : Nat.card (Subgroup.center ↥S) = 3)
    (hS2 : 2 ≤ CFSG.Open.pRank 3 S) (hX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {x : X} (hx : orderOf x = 3)
    (hxS : x ∉ S) {T : Type} [Group T] (hT : HatData T) (hiso : Nonempty (↥S ⧸ Subgroup.center ↥S ≃* T)) : False := by
  obtain ⟨e⟩ := hiso
  exact hat_false hQ.1 hZ (HatData.of_mulEquiv e.symm hT) hS2 hX hx hxS

theorem a318CentralFact_of_tail
    (qt : QCentralTail) : A318CentralFact := by
  intro X _ _ S _ hQ hZ hL hP hS2 hX x hx hxS
  rcases a318CenterFact ↥S hL hZ with ⟨s, q, hmod, hSL⟩ | ⟨-, -, hiso⟩ | ⟨-, -, hiso⟩ | ⟨-, -, hiso⟩
  ·
    have hSLpi : IsSLThreePi ↥S := by
      refine ⟨q, ?_⟩
      cases s
      · obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
        refine ⟨K, hKf, hKfin, Or.inr ⟨hKcard, ?_, ⟨e⟩⟩⟩
        simp only [Bool.false_eq_true, ↓reduceIte] at hmod
        unfold Int.ModEq at hmod
        omega
      · obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
        refine ⟨K, hKf, hKfin, Or.inl ⟨hKcard, ?_, ⟨e⟩⟩⟩
        simp only [↓reduceIte] at hmod
        unfold Int.ModEq at hmod
        omega
    obtain ⟨π, p, f, K, hKf, hK, hq, hq2, ⟨e⟩⟩ := exists_slPi_model hSLpi hQ
    obtain ⟨y, hxy, hy3, -, hnon, hcyc, hcard⟩ := central_type_iii hQ hS2 hX hK hq hq2 e hx hxS
    have hSLmodel : IsSLEps3 π (p ^ f) ↥S := by
      cases π
      · exact ⟨K, hKf, hK.finite, hK.card, ⟨e⟩⟩
      · exact ⟨K, hKf, hK.finite, hK.card, ⟨e⟩⟩
    have hmodel : Int.ModEq 3 ((p ^ f : ℕ) : ℤ) (if π then 1 else -1) := by
      unfold Int.ModEq
      cases π
      · change (p ^ f) % 3 = 2 at hq
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · change (p ^ f) % 3 = 1 at hq
        simp only [↓reduceIte]
        omega
    have hb := qt X S hQ hZ π (p ^ f) hSLmodel hmodel hP hS2 hX x hx hxS
    have hA : ∀ g : X, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ S ⊔ Subgroup.zpowers x := fun g hg =>
      hb ▸ Subgroup.subset_closure ⟨Subgroup.mem_top g, hg⟩
    refine ⟨π, p ^ f, x, hSLmodel, hx, hxS, hb, isPGLModCenter_of_type_iii hK hq hx hxy hy3 hnon,
      ?_, ?_, fun Y hY hYS => exists_conj_of_orderThree e hQ hS2 hX hK hq hq2 hZ hP hx hxS hA hY hYS⟩
    · exact isCyclic_of_surjective (centEquiv hxy).symm.toMonoidHom (centEquiv hxy).symm.surjective
    · rw [Nat.card_congr (centEquiv hxy).toEquiv, hcard,
        qSubPi_cube_div hq (qSubPi_ne_zero hK hq)]
  · exact (false_of_isHat hQ hZ hS2 hX hx hxS hatData_alt6 hiso).elim
  · exact (false_of_isHat hQ hZ hS2 hX hx hxS hatData_alt7 hiso).elim
  · exact (false_of_isHat hQ hZ hS2 hX hx hxS hatData_M22 hiso).elim

end A318P

end CFSG.Quasithin
