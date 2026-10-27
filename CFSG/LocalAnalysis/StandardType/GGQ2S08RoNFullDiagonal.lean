module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQAux
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryInnFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUDvdBound
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNFrame

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] {n : ℕ}

omit [Finite G] in
theorem e6QTwoNFrameFullDiagonal (hK : Nat.card K = 4) (hn : 3 ≤ n) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ (n + 1))
    (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1))) (LargeEvenGUSet (Fin (n + 1))
          K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ) :
    Nat.card ↥(e6QTwoNFrameAction hNL θ).ker = 3 ∧
      Nat.card ↥(e6QTwoNFrameAction hNL θ).range = 3 ^ n ∧
        ∃ (Q : GL (Fin (n + 1)) K) (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
            (RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))),
          ∀ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 → (∀ k, σ k ^ 3 = 1) →
            ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
              (e6QTwoNFrameAction hNL θ b) σ := by
  let β := e6QTwoNFrameAction hNL θ
  have hker_le : Nat.card ↥β.ker ≤ 3 :=
    e6QTwoNFrameAction_card_ker_le hNL θ hperf hBs hx hBL
  have hrange_le : Nat.card ↥β.range ≤ 3 ^ n :=
    e6QTwoNFrameAction_card_range_le hK hn hNL θ hBs hI
  have hprod : Nat.card ↥β.ker * Nat.card ↥β.range = 3 ^ (n + 1) := by
    rw [← hcard]
    exact Subgroup.card_ker_mul_card_range β
  have hker3 : Nat.card ↥β.ker = 3 := by
    by_contra hne
    have hle : Nat.card ↥β.ker ≤ 2 := by omega
    have hb : Nat.card ↥β.ker * Nat.card ↥β.range ≤ 2 * 3 ^ n :=
      Nat.mul_le_mul hle hrange_le
    have h2 : 2 * 3 ^ n < 3 ^ (n + 1) := by
      have h0 : 0 < 3 ^ n := pow_pos (by norm_num) n
      rw [pow_succ]
      omega
    exact absurd (hprod ▸ hb) (not_le.mpr h2)
  have hrange5 : Nat.card ↥β.range = 3 ^ n := by
    rw [hker3] at hprod
    rw [show (3 : ℕ) ^ (n + 1) = 3 * 3 ^ n from pow_succ' 3 n] at hprod
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hprod
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨Q, hQ, hQfr⟩ := TableBUD.exists_frame_inndiag (h := USixTwo.fieldDataFour hK) hK'
    (by omega : 3 ≤ n + 1) (by simp; omega : (n + 1, 2 ^ 1) ≠ (3, 2))
    (by omega : ¬(n + 1 = 3 ∧ 2 ^ 1 = 2)) (by norm_num : Nat.Prime 3)
    (by norm_num : 3 ∣ 2 ^ 1 + 1)
    (e6QTwoNFrameAction_isElemAbelian_range hNL θ hBs)
    (e6QTwoNFrameAction_range_le_inndiag hK hNL θ hI)
    (by rw [hrange5]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hQ' : ∀ e : β.range, ∃ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 ∧
      (∀ k, σ k ^ 3 = 1) ∧
      (∀ k, ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1) ∧
      TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e : MulAut _) σ :=
    fun e => hQfr e.1 e.2
  choose σ hσ0 hσ3 hσn hσfr using hQ'
  let f : β.range → (Fin n → Kˣ) := fun e i => σ e (Fin.succAbove 0 i)
  have hf_inj : Function.Injective f := by
    intro e e' he
    have hσeq : σ e = σ e' := by
      funext k
      by_cases hk : k = 0
      · rw [hk, hσ0 e, hσ0 e']
      · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (x := k) (y := (0 : Fin (n + 1))) hk
        exact congrFun he i
    have h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e : MulAut _) (σ e) := hσfr e
    have h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ (e' : MulAut _) (σ e) :=
      hσeq ▸ hσfr e'
    exact Subtype.ext (TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour hK)
      (Q := Q) (hQ := hQ) (hσ := hσn e) h1 h2)
  have hcardf : Nat.card (Fin n → Kˣ) = 3 ^ n := by
    rw [Nat.card_pi]
    have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hunits]
  have hbij : Function.Bijective f :=
    hf_inj.bijective_of_nat_card_le (by rw [hcardf, hrange5])
  refine ⟨hker3, hrange5, Q, hQ, fun τ hτ0 hτ3 => ?_⟩
  obtain ⟨e, he⟩ := hbij.2 (fun i => τ (Fin.succAbove 0 i))
  have hτe : σ e = τ := by
    funext k
    by_cases hk : k = 0
    · rw [hk, hσ0 e, hτ0]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq (x := k) (y := (0 : Fin (n + 1))) hk
      exact congrFun he i
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp e.2
  refine ⟨b, ?_⟩
  rw [hb]
  exact hτe ▸ hσfr e

end CFSG.StandardType.E6QTwo

end
