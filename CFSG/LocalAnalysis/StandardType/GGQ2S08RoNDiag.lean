module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrameAux3

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] {n : ℕ}
variable {Bs L : Subgroup G} {x : G}

omit [Finite K] in
theorem e6QTwoNPowThreeVal (_hK : Nat.card K = 4) {σ : Fin (n + 1) → Kˣ}
    (hσ : ∀ k, σ k ^ 3 = 1) (k : Fin (n + 1)) :
    ((σ k : Kˣ) : K) ^ (2 ^ 1 + 1) = 1 := by
  rw [show 2 ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val, hσ k, Units.val_one]

omit [Finite K] in
theorem e6QTwoNFrameAct_inj (hK : Nat.card K = 4) (hn : 3 ≤ n) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K (n + 1))}
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))} {σ σ' : Fin (n + 1) →
      Kˣ}
    (hσ0 : σ (0 : Fin (n + 1)) = 1) (hσ'0 : σ' (0 : Fin (n + 1)) = 1)
    (hσ : ∀ k, σ k ^ 3 = 1) (hσ' : ∀ k, σ' k ^ 3 = 1)
    (h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ)
    (h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ') : σ = σ' := by
  have : Finite K := USixTwo.finite_of_card_eq_four hK
  obtain ⟨c, hc⟩ := TableBUD.FrameAct.eq_smul (n := 1) (h := USixTwo.fieldDataFour hK)
    (by rw [hK]; norm_num) (by omega : 3 ≤ n + 1) (by simp; omega : (n + 1, 2 ^ 1) ≠ (3, 2))
    (p := 3) (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1)
    (fun k => e6QTwoNPowThreeVal hK hσ k)
    (fun k => e6QTwoNPowThreeVal hK hσ' k) h1 h2
  have hc1 : c = 1 := by
    have h0 := hc (0 : Fin (n + 1))
    rw [hσ'0, hσ0, mul_one] at h0
    exact h0.symm
  funext k
  rw [hc k, hc1, one_mul]

private def e6QTwoNDiagSet (n : ℕ) (K : Type) [Field K] : Type :=
  {σ : Fin (n + 1) → Kˣ // σ (0 : Fin (n + 1)) = 1}

private noncomputable def e6QTwoNDiagSetEquiv (n : ℕ) (K : Type) [Field K] :
    e6QTwoNDiagSet n K ≃ (Fin n → Kˣ) where
  toFun σ := fun i => σ.1 (Fin.succAbove (0 : Fin (n + 1)) i)
  invFun τ := ⟨Fin.insertNth (0 : Fin (n + 1)) 1 τ, by simp⟩
  left_inv σ := by
    apply Subtype.ext
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [σ.2]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hk
      simp
  right_inv τ := by
    funext i
    simp

omit [Finite K] in
private theorem e6QTwoN_card_diagSet
    (hK : Nat.card K = 4) :
    Nat.card (e6QTwoNDiagSet n K) = 3 ^ n := by
  rw [Nat.card_congr (e6QTwoNDiagSetEquiv n K), Nat.card_pi]
  have hunits : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hunits]

omit [Finite G] in
theorem e6QTwoNFrameAct_of_mem_range
    (hK : Nat.card K = 4) (hn : 3 ≤ n) {Q : GL (Fin (n + 1)) K}
    {hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK)
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K (n + 1))}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))
    (hfull : ∀ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 → (∀ k, σ k ^ 3 = 1) →
      ∃ b : Bs, TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNFrameAction hNL θ b) σ)
    (hrange : Nat.card ↥(e6QTwoNFrameAction hNL θ).range = 3 ^ n)
    {e : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (n + 1)) K (2 ^ 1)))}
    (he : e ∈ (e6QTwoNFrameAction hNL θ).range) :
    ∃ σ : Fin (n + 1) → Kˣ, σ (0 : Fin (n + 1)) = 1 ∧ (∀ k, σ k ^ 3 = 1) ∧
      TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ e σ := by
  classical
  let DiagSet := {σ : Fin (n + 1) → Kˣ // σ (0 : Fin (n + 1)) = 1}
  have hDiagCard : Nat.card DiagSet = 3 ^ n := e6QTwoN_card_diagSet (n := n) hK
  let F : DiagSet → (e6QTwoNFrameAction hNL θ).range := fun σ =>
    ⟨e6QTwoNFrameAction hNL θ
        (Classical.choose (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))),
      MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  have hF_inj : Function.Injective F := by
    intro σ σ' h
    have hβ : e6QTwoNFrameAction hNL θ
        (Classical.choose (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))) =
        e6QTwoNFrameAction hNL θ
          (Classical.choose (hfull σ'.1 σ'.2 (fun k =>
            USixTwo.cube_unit_eq_one hK (σ'.1 k)))) := by
      simpa [F] using congrArg Subtype.val h
    have h1 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNFrameAction hNL θ
          (Classical.choose (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))))
        σ.1 :=
      Classical.choose_spec (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))
    have h2 : TableBUD.FrameAct (USixTwo.fieldDataFour hK) Q hQ
        (e6QTwoNFrameAction hNL θ
          (Classical.choose (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))))
        σ'.1 := by
      rw [hβ]
      exact Classical.choose_spec (hfull σ'.1 σ'.2 (fun k =>
        USixTwo.cube_unit_eq_one hK (σ'.1 k)))
    have heq : σ.1 = σ'.1 := e6QTwoNFrameAct_inj hK hn σ.2 σ'.2
      (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k))
      (fun k => USixTwo.cube_unit_eq_one hK (σ'.1 k)) h1 h2
    exact Subtype.ext heq
  have hF_bij : Function.Bijective F :=
    hF_inj.bijective_of_nat_card_le (by rw [hDiagCard, hrange])
  obtain ⟨σ, hσ⟩ := hF_bij.2 ⟨e, he⟩
  refine ⟨σ.1, σ.2, fun k => USixTwo.cube_unit_eq_one hK (σ.1 k), ?_⟩
  have hval : e = (F σ).val := (congrArg Subtype.val hσ).symm
  rw [hval]
  exact Classical.choose_spec (hfull σ.1 σ.2 (fun k => USixTwo.cube_unit_eq_one hK (σ.1 k)))


namespace GGQ2S08RoN

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

theorem exists_frameDiag (c : GGQ2S08RoN n Bs L x) (b : Bs) :
    ∃ σ : Fin (n + 1) → c.Kˣ, σ (0 : Fin (n + 1)) = 1 ∧ c.FrameDiag b σ := by
  obtain ⟨σ, h0, -,
    h⟩ := e6QTwoNFrameAct_of_mem_range c.hK (by have := c.hn; omega) c.hNL c.θ c.hfull c.hrange
    (MonoidHom.mem_range.mpr ⟨b, rfl⟩)
  exact ⟨σ, h0, h⟩

@[expose] noncomputable def diag (c : GGQ2S08RoN n Bs L x) (b : Bs) : Fin (n + 1) → c.Kˣ :=
  (c.exists_frameDiag b).choose

theorem diag_zero (c : GGQ2S08RoN n Bs L x) (b : Bs) : c.diag b (0 : Fin (n + 1)) = 1 :=
  (c.exists_frameDiag b).choose_spec.1

theorem frameDiag_diag (c : GGQ2S08RoN n Bs L x) (b : Bs) : c.FrameDiag b (c.diag b) :=
  (c.exists_frameDiag b).choose_spec.2

theorem cube (c : GGQ2S08RoN n Bs L x) (t : c.Kˣ) : t ^ 3 = 1 :=
  USixTwo.cube_unit_eq_one c.hK t

theorem norm_one (c : GGQ2S08RoN n Bs L x) (σ : Fin (n + 1) → c.Kˣ) (k : Fin (n + 1)) :
    ((σ k : c.Kˣ) : c.K) ^ (2 ^ 1 + 1) = 1 := by
  rw [show (2 : ℕ) ^ 1 + 1 = 3 by norm_num, ← Units.val_pow_eq_pow_val, c.cube, Units.val_one]

theorem frameDiag_eq_smul (c : GGQ2S08RoN n Bs L x) {b : Bs} {σ σ' : Fin (n + 1) → c.Kˣ}
    (h : c.FrameDiag b σ) (h' : c.FrameDiag b σ') : ∃ μ : c.Kˣ, ∀ k, σ' k = μ * σ k :=
  TableBUD.FrameAct.eq_smul (n := 1) (h := USixTwo.fieldDataFour c.hK)
    (by rw [c.hK]; norm_num) (by have := c.hn; omega : 3 ≤ n + 1)
    (by have := c.hn; simp; omega : (n + 1, 2 ^ 1) ≠ (3, 2))
    (p := 3) (by norm_num) (by norm_num : 3 ∣ 2 ^ 1 + 1) (c.norm_one σ) (c.norm_one σ') h h'

theorem diag_eq_of_frameDiag (c : GGQ2S08RoN n Bs L x) {b : Bs} {σ : Fin (n + 1) → c.Kˣ}
    (h0 : σ (0 : Fin (n + 1)) = 1) (h : c.FrameDiag b σ) : c.diag b = σ :=
  e6QTwoNFrameAct_inj c.hK (by have := c.hn; omega) (c.diag_zero b) h0 (fun k => c.cube _) (fun k
    => c.cube _)
    (c.frameDiag_diag b) h

theorem exists_eq_smul_diag (c : GGQ2S08RoN n Bs L x) {b : Bs} {σ : Fin (n + 1) → c.Kˣ}
    (h : c.FrameDiag b σ) : ∃ μ : c.Kˣ, ∀ k, σ k = μ * c.diag b k :=
  c.frameDiag_eq_smul (c.frameDiag_diag b) h

theorem diag_mul (c : GGQ2S08RoN n Bs L x) (b b' : Bs) :
    c.diag (b * b') = c.diag b * c.diag b' := by
  refine c.diag_eq_of_frameDiag ?_ ?_
  · rw [Pi.mul_apply, c.diag_zero, c.diag_zero, mul_one]
  · have h := TableBUD.FrameAct.mul (c.frameDiag_diag b) (c.frameDiag_diag b')
      (c.norm_one (c.diag b'))
    rwa [← map_mul] at h

theorem diag_one (c : GGQ2S08RoN n Bs L x) : c.diag 1 = 1 := by
  refine c.diag_eq_of_frameDiag rfl ?_
  rw [FrameDiag, map_one]
  exact TableBUD.frameAct_one

theorem diag_eq_one_iff (c : GGQ2S08RoN n Bs L x) (b : Bs) :
    c.diag b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
  have hker := e6QTwoNFrameAction_ker c.hNL c.θ c.hperf
  constructor
  · intro h
    have h1 : c.act b = 1 := by
      have hb := c.frameDiag_diag b
      rw [h] at hb
      exact TableBUD.FrameAct.unique (h := USixTwo.fieldDataFour c.hK) (Q := c.Q) (hQ := c.hQ)
        (hσ := c.norm_one 1) hb TableBUD.frameAct_one
    have hb : b ∈ (c.act).ker := h1
    rw [show (c.act).ker = (e6QTwoNFrameAction c.hNL c.θ).ker from rfl, hker,
      Subgroup.mem_subgroupOf] at hb
    rw [c.hBL] at hb
    exact hb
  · intro h
    have hb : b ∈ (e6QTwoNFrameAction c.hNL c.θ).ker := by
      rw [hker, Subgroup.mem_subgroupOf, c.hBL]
      exact h
    refine c.diag_eq_of_frameDiag rfl ?_
    rw [FrameDiag, show c.act b = 1 from hb]
    exact TableBUD.frameAct_one

theorem exists_diag_eq (c : GGQ2S08RoN n Bs L x) (σ : Fin (n + 1) → c.Kˣ) (h0 : σ
  (0 : Fin (n + 1)) = 1) :
    ∃ b : Bs, c.diag b = σ := by
  obtain ⟨b, hb⟩ := c.hfull σ h0 (fun k => c.cube _)
  exact ⟨b, c.diag_eq_of_frameDiag h0 hb⟩

end GGQ2S08RoN


end CFSG.StandardType.E6QTwo

end
