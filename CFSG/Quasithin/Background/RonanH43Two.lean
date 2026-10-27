module

public import CFSG.Quasithin.Background.RonanH43Red
public import CFSG.Quasithin.Background.RonanH43Sub

public section

namespace CFSG.Quasithin.RonanH43

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SL3Pair CFSG.Quasithin.H.SL3One CFSG.Open
  CFSG.Assembly.LowTwoRank Matrix

theorem trv0_mem {B : Subgroup (MulAut PV)} (hB4 : Nat.card B = 4)
    (hB : ∀ y ∈ B, ∃ φ : Fin 3 → ZMod 2, ∃ h : φ 0 = 0, y = trv0 φ h)
    {φ : Fin 3 → ZMod 2} (h : φ 0 = 0) : trv0 φ h ∈ B := by
  have hS : Nat.card {ψ : Fin 3 → ZMod 2 // ψ 0 = 0} = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide +kernel
  have hch : ∀ y : B, ∃ χ : {ψ : Fin 3 → ZMod 2 // ψ 0 = 0},
      (y : MulAut PV) = trv0 χ.1 χ.2 := by
    intro y
    obtain ⟨ψ, hψ, hy⟩ := hB (y : MulAut PV) y.2
    exact ⟨⟨ψ, hψ⟩, hy⟩
  choose κ hκ using hch
  have hinj : Function.Injective κ := by
    intro y y' hyy'
    apply Subtype.ext
    have h1 := hκ y
    have h2 := hκ y'
    rw [hyy'] at h1
    rw [h1, h2]
  have hbij : Function.Bijective κ :=
    hinj.bijective_of_nat_card_le (hS.trans hB4.symm).le
  obtain ⟨y, hy⟩ := hbij.2 ⟨φ, h⟩
  have h1 : (y : MulAut PV) = trv0 φ h := by
    have h2 := hκ y
    rw [hy] at h2
    exact h2
  rw [← h1]
  exact y.2

theorem q1_fix_key : ∀ v w : Fin 3 → ZMod 2,
    (∀ φ : Fin 3 → ZMod 2, φ 0 = 0 → v + (φ ⬝ᵥ v) • e0 = v ∧ w + w 0 • φ = w) ↔
      (v 1 = 0 ∧ v 2 = 0 ∧ w 0 = 0) := by
  decide +kernel

theorem q1_decomp : ∀ v w : Fin 3 → ZMod 2, v 1 = 0 → v 2 = 0 → w 0 = 0 →
    v = (Pi.single (0 : Fin 3) (v 0) : Fin 3 → ZMod 2) + (0 + 0) ∧
      w = 0 + ((Pi.single (1 : Fin 3) (w 1) : Fin 3 → ZMod 2) +
        (Pi.single (2 : Fin 3) (w 2) : Fin 3 → ZMod 2)) := by
  decide +kernel

theorem q1_mk_decomp {v w : Fin 3 → ZMod 2} (hv1 : v 1 = 0) (hv2 : v 2 = 0) (hw0 : w 0 = 0) :
    mk v w =
      mk (Pi.single 0 (v 0)) 0 * (mk 0 (Pi.single 1 (w 1)) * mk 0 (Pi.single 2 (w 2))) := by
  obtain ⟨h1, h2⟩ := q1_decomp v w hv1 hv2 hw0
  exact (mk_inj.mpr ⟨h1, h2⟩).trans rfl

theorem q1_mem_A (s : ZMod 2) :
    mk (Pi.single 0 s) 0 ∈ Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV) := by
  rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) s with rfl | rfl
  · simp [mk_zero]
  · show b1R 0 ∈ Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV)
    exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem q1_mem_B (t : ZMod 2) :
    mk 0 (Pi.single 1 t) ∈ Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV) := by
  rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) t with rfl | rfl
  · simp [mk_zero]
  · show b2R 1 ∈ Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV)
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem q1_mem_C (u : ZMod 2) :
    mk 0 (Pi.single 2 u) ∈ Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV) := by
  rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) u with rfl | rfl
  · simp [mk_zero]
  · show b2R 2 ∈ Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV)
    exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem fixV_eq_cTarget {B : Subgroup (MulAut PV)}
    (hB : ∀ y ∈ B, ∃ φ : Fin 3 → ZMod 2, ∃ h : φ 0 = 0, y = trv0 φ h)
    (hB' : ∀ (φ : Fin 3 → ZMod 2) (h : φ 0 = 0), trv0 φ h ∈ B) : fixV B = cTarget := by
  ext x
  obtain ⟨v, w, rfl⟩ : ∃ v w : Fin 3 → ZMod 2, x = mk v w := ⟨_, _, eq_mk x⟩
  change (∀ y ∈ B, y (mk v w) = mk v w) ↔ mk v w ∈ cTarget
  rw [mem_cTarget]
  constructor
  · intro H
    refine (q1_fix_key v w).mp fun φ h => ?_
    have h' := H (trv0 φ h) (hB' φ h)
    rwa [trv0_apply, mk_inj] at h'
  · intro H y hy
    obtain ⟨φ, h, rfl⟩ := hB y hy
    rw [trv0_apply, mk_inj]
    exact (q1_fix_key v w).mpr H φ h

theorem closure_eq_cTarget :
    Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV) = cTarget := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    show x ∈ cTarget
    rw [mem_cTarget]
    rcases hx with rfl | rfl | rfl <;> decide +kernel
  · intro x hx
    obtain ⟨v, w, rfl⟩ : ∃ v w : Fin 3 → ZMod 2, x = mk v w := ⟨_, _, eq_mk x⟩
    obtain ⟨hv1, hv2, hw0⟩ : v 1 = 0 ∧ v 2 = 0 ∧ w 0 = 0 := mem_cTarget.mp hx
    rw [q1_mk_decomp hv1 hv2 hw0]
    exact Subgroup.mul_mem _ (q1_mem_A (v 0))
      (Subgroup.mul_mem _ (q1_mem_B (w 1)) (q1_mem_C (w 2)))

abbrev unitVec3 (i : Fin 3) : Fin 3 → ZMod 2 := Pi.single i 1

theorem unitVec3_ne_zero (i : Fin 3) : unitVec3 i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [unitVec3] at this

theorem trv0_zero_eq_one (h : (0 : Fin 3 → ZMod 2) 0 = 0) : trv0 0 h = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨v, w, rfl⟩ : ∃ v w, x = mk v w := ⟨_, _, eq_mk x⟩
  simp [trv0_apply, MulAut.one_apply]

theorem trv0_ne_one {φ : Fin 3 → ZMod 2} (h : φ 0 = 0) (hφ : φ ≠ 0) : trv0 φ h ≠ 1 :=
  fun e => hφ (trv0_injective (ψ := 0) h rfl (e.trans (trv0_zero_eq_one rfl).symm))

theorem trv0_fix_mk {φ : Fin 3 → ZMod 2} (h : φ 0 = 0) (v w : Fin 3 → ZMod 2)
    (hv : φ ⬝ᵥ v = 0) (hw : w 0 = 0) : trv0 φ h (mk v w) = mk v w := by
  simp [trv0_apply, hv, hw]

theorem xi_eq_wSet {B : Subgroup (MulAut PV)}
    (hB : ∀ y ∈ B, ∃ φ : Fin 3 → ZMod 2, ∃ h : φ 0 = 0, y = trv0 φ h)
    (hB' : ∀ (φ : Fin 3 → ZMod 2) (h : φ 0 = 0), trv0 φ h ∈ B) : xi B = wSet := by
  apply le_antisymm
  · apply xi_le
    intro a ha ha1
    obtain ⟨φ, h, rfl⟩ := hB a ha
    have hφ : φ ≠ 0 := by
      rintro rfl
      exact ha1 (trv0_zero_eq_one h)
    intro x hx
    have hx' : trv0 φ h x = x := mem_fixV_zpowers_iff_apply.mp hx
    obtain ⟨v, w, rfl⟩ : ∃ v w, x = mk v w := ⟨_, _, eq_mk x⟩
    rw [trv0_apply, mk_inj] at hx'
    obtain ⟨-, hw⟩ := hx'
    have h1 : w 0 • φ = 0 := add_eq_left.mp hw
    refine mem_wSet.mpr ?_
    show w 0 = 0
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (w 0) with h0 | h0
    · exact h0
    · rw [h0, one_smul] at h1
      exact absurd h1 hφ
  · intro x hx
    have hx0 : Multiplicative.toAdd x.2 0 = 0 := mem_wSet.mp hx
    obtain ⟨v, w, rfl⟩ : ∃ v w, x = mk v w := ⟨_, _, eq_mk x⟩
    have hw : w 0 = 0 := hx0
    have hp1 : unitVec3 1 0 = 0 := by simp [unitVec3, Pi.single_apply]
    have hp2 : unitVec3 2 0 = 0 := by simp [unitVec3, Pi.single_apply]
    have ht1 : trv0 (unitVec3 1) hp1 ∈ B := hB' (unitVec3 1) hp1
    have ht2 : trv0 (unitVec3 2) hp2 ∈ B := hB' (unitVec3 2) hp2
    have ht1ne : trv0 (unitVec3 1) hp1 ≠ 1 := trv0_ne_one hp1 (unitVec3_ne_zero 1)
    have ht2ne : trv0 (unitVec3 2) hp2 ≠ 1 := trv0_ne_one hp2 (unitVec3_ne_zero 2)
    have hdotA : unitVec3 2 ⬝ᵥ (v 0 • e0 + v 1 • unitVec3 1) = 0 := by
      simp [unitVec3, e0, single_dotProduct, Pi.single_apply]
    have hdotB : unitVec3 1 ⬝ᵥ (v 2 • unitVec3 2) = 0 := by
      simp [unitVec3, single_dotProduct, Pi.single_apply]
    have hdot0 : unitVec3 1 ⬝ᵥ (0 : Fin 3 → ZMod 2) = 0 := by
      simp
    have hfixA : mk (v 0 • e0 + v 1 • unitVec3 1) 0 ∈
        fixV (Subgroup.zpowers (trv0 (unitVec3 2) hp2)) :=
      mem_fixV_zpowers_iff_apply.mpr
        (trv0_fix_mk hp2 (v 0 • e0 + v 1 • unitVec3 1) 0 hdotA rfl)
    have hfixB : mk (v 2 • unitVec3 2) 0 ∈
        fixV (Subgroup.zpowers (trv0 (unitVec3 1) hp1)) :=
      mem_fixV_zpowers_iff_apply.mpr
        (trv0_fix_mk hp1 (v 2 • unitVec3 2) 0 hdotB rfl)
    have hfixC : mk 0 w ∈ fixV (Subgroup.zpowers (trv0 (unitVec3 1) hp1)) :=
      mem_fixV_zpowers_iff_apply.mpr (trv0_fix_mk hp1 0 w hdot0 hw)
    have key : mk v w =
        mk (v 0 • e0 + v 1 • unitVec3 1) 0 * mk (v 2 • unitVec3 2) 0 * mk 0 w := by
      simp only [mk_mul, mk_inj]
      refine ⟨?_, by simp⟩
      funext j
      fin_cases j <;> simp [e0, unitVec3, Pi.single_apply]
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (fixV_le_xi ht2 ht2ne hfixA)
      (fixV_le_xi ht1 ht1ne hfixB)) (fixV_le_xi ht1 ht1ne hfixC)

theorem wSet_eq_sup : wSet = v1R ⊔ cTarget := by
  apply le_antisymm
  · intro x hx
    have hx0 : Multiplicative.toAdd x.2 0 = 0 := mem_wSet.mp hx
    have hx' : x = (x.1, 1) * (1, x.2) := Prod.ext (by simp) (by simp)
    have h1 : (x.1, 1) ∈ v1R := mem_v1R.mpr rfl
    have h2 : (1, x.2) ∈ cTarget := mem_cTarget.mpr ⟨by simp, by simp, hx0⟩
    have h3 : (x.1, 1) * (1, x.2) ∈ v1R ⊔ cTarget :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2)
    rwa [← hx'] at h3
  · refine sup_le ?_ ?_
    · intro x hx
      have hx0 : x.2 = 1 := mem_v1R.mp hx
      exact mem_wSet.mpr (by simp [hx0])
    · intro x hx
      have hx0 := mem_cTarget.mp hx
      exact mem_wSet.mpr hx0.2.2

theorem q3_pi_add_self (x : Fin 3 → ZMod 2) : x + x = 0 := by
  have h2 : ∀ t : ZMod 2, t + t = 0 := by decide
  funext i
  exact h2 (x i)

theorem q3_add_cancel (a b : Fin 3 → ZMod 2) : a + b + a = b := by
  rw [add_comm (a + b) a, ← add_assoc, q3_pi_add_self a, zero_add]

theorem q3_trv0_mul_inv {φ : Fin 3 → ZMod 2} (h : φ 0 = 0) (v w : Fin 3 → ZMod 2)
    (hw : w 0 = 0) :
    trv0 φ h (mk v w) * (mk v w)⁻¹ = mk ((φ ⬝ᵥ v) • e0) 0 := by
  rw [trv0_apply, hw, zero_smul, add_zero, mk_inv, mk_mul, q3_pi_add_self w,
    q3_add_cancel v]

theorem q3_mk_smul_e0_mem (s : ZMod 2) : mk (s • e0) 0 ∈ Subgroup.zpowers (b1R 0) := by
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) s with rfl | rfl
  · rw [zero_smul, mk_zero]
    exact Subgroup.one_mem _
  · rw [one_smul]
    exact Subgroup.mem_zpowers _

theorem commOn_eq {B : Subgroup (MulAut PV)}
    (hB : ∀ y ∈ B, ∃ φ : Fin 3 → ZMod 2, ∃ h : φ 0 = 0, y = trv0 φ h)
    (hB' : ∀ (φ : Fin 3 → ZMod 2) (h : φ 0 = 0), trv0 φ h ∈ B) :
    commOnR wSet B = Subgroup.zpowers (b1R 0) := by
  apply le_antisymm
  · unfold commOnR
    apply (Subgroup.closure_le _).mpr
    rintro u ⟨a, ha, w, hw, rfl⟩
    obtain ⟨φ, h, rfl⟩ := hB a ha
    obtain ⟨v, w', rfl⟩ : ∃ v w', w = mk v w' :=
      ⟨Multiplicative.toAdd w.1, Multiplicative.toAdd w.2, eq_mk w⟩
    have hw0 : w' 0 = 0 := mem_wSet.mp hw
    rw [q3_trv0_mul_inv h v w' hw0]
    exact q3_mk_smul_e0_mem _
  · rw [Subgroup.zpowers_le]
    unfold commOnR
    have h1 : (Pi.single 1 1 : Fin 3 → ZMod 2) 0 = 0 := by decide
    have hdot : (Pi.single 1 1 : Fin 3 → ZMod 2) ⬝ᵥ Pi.single 1 1 = 1 := by
      rw [dotProduct_single, Pi.single_eq_same, mul_one]
    have hmk : mk e0 0 = b1R 0 := rfl
    have hgen : b1R 0 = trv0 (Pi.single 1 1) h1 (mk (Pi.single 1 1) 0) *
        (mk (Pi.single 1 1) 0)⁻¹ := by
      rw [q3_trv0_mul_inv h1 (Pi.single 1 1) 0 rfl, hdot, one_smul, hmk]
    exact Subgroup.subset_closure ⟨trv0 (Pi.single 1 1) h1, hB' _ h1, mk (Pi.single 1 1) 0,
      mem_wSet.mpr rfl, hgen⟩

theorem core2 {B : Subgroup (MulAut PV)} (hB4 : Nat.card B = 4)
    (hB : ∀ y ∈ B, ∃ φ : Fin 3 → ZMod 2, ∃ h : φ 0 = 0, y = trv0 φ h) :
    fixV B = Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV) ∧ rk ↥(fixV B) = 3 ∧
      xi B = v1R ⊔ fixV B ∧ rk ↥(xi B) = 5 ∧ commOnR (xi B) B = Subgroup.zpowers (b1R 0) := by
  have hB' : ∀ (φ : Fin 3 → ZMod 2) (h : φ 0 = 0), trv0 φ h ∈ B := fun φ h => trv0_mem hB4 hB h
  have h1 := fixV_eq_cTarget hB hB'
  have h2 := xi_eq_wSet hB hB'
  refine ⟨h1.trans closure_eq_cTarget.symm, ?_, ?_, ?_, ?_⟩
  · exact rk_of_card (k := 3) ((congrArg (fun S : Subgroup PV => Nat.card ↥S) h1).trans
      (by rw [card_cTarget]; norm_num))
  · rw [h2, h1]
    exact wSet_eq_sup
  · exact rk_of_card (k := 5) ((congrArg (fun S : Subgroup PV => Nat.card ↥S) h2).trans
      (by rw [card_wSet]; norm_num))
  · rw [h2]
    exact commOn_eq hB hB'

theorem part2 {M A : Subgroup (MulAut PV)} (hLM : pairSL (ZMod 2) ≤ M)
    (hsM : swapAut (ZMod 2) ∈ M) (hA2 : IsElemAbelian2 A) (hA4 : Nat.card A = 4)
    (hAL : A ≤ pairSL (ZMod 2)) :
    ∃ g ∈ M, fixV (conjR g A) = Subgroup.closure ({b1R 0, b2R 1, b2R 2} : Set PV) ∧
      rk ↥(fixV (conjR g A)) = 3 ∧ xi (conjR g A) = v1R ⊔ fixV (conjR g A) ∧
      rk ↥(xi (conjR g A)) = 5 ∧
      commOnR (xi (conjR g A)) (conjR g A) = Subgroup.zpowers (b1R 0) := by
  obtain ⟨g, hgM, hcard, hdesc⟩ := reduce2 hLM hsM hA2 hA4 hAL
  exact ⟨g, hgM, core2 hcard hdesc⟩

end CFSG.Quasithin.RonanH43
