module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bBase

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.LocalAnalysis.ComponentInitial

section Flag

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem finrank_flag_fin3 (b : Module.Basis (Fin 3) (ZMod 2) V) (k : Fin 4) :
    Module.finrank (ZMod 2) (b.flag k) = (k : ℕ) := by
  have hb' : LinearIndependent (ZMod 2)
      (fun i : {i : Fin 3 // i.castSucc < k} => b i.1) :=
    b.linearIndependent.comp _ Subtype.val_injective
  have hset : b.flag k = Submodule.span (ZMod 2)
      (Set.range (fun i : {i : Fin 3 // i.castSucc < k} => b i.1)) := by
    unfold Module.Basis.flag
    congr 1
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
  rw [hset, finrank_span_eq_card hb']
  fin_cases k <;> decide

end Flag

section Witt

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_witt_basis_of_MTS [FiniteDimensional (ZMod 2) W] (q : W → ZMod 2)
    (B : LinearMap.BilinForm (ZMod 2) W) (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0) (hdim : Module.finrank (ZMod 2) W = 6)
    (S : Submodule (ZMod 2) W) (hS3 : Module.finrank (ZMod 2) S = 3) (hSs : ∀ s ∈ S, q s = 0) :
    ∃ b : Module.Basis (Fin 3 ⊕ Fin 3) (ZMod 2) W,
      (∀ i, q (b (.inl i)) = 0 ∧ q (b (.inr i)) = 0) ∧
      (∀ i j, B (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) ∧
      (∀ i j, B (b (.inl i)) (b (.inl j)) = 0 ∧ B (b (.inr i)) (b (.inr j)) = 0) ∧
      (∀ x y : Fin 3 → ZMod 2, q (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) =
        ∑ i, x i * y i) ∧
      (∀ v, v ∈ S ↔ ∀ j, b.repr v (.inr j) = 0) := by
  classical
  have hq0 : q 0 = 0 := q_zero q B hq
  let Q : QuadraticForm (ZMod 2) W :=
    { toFun := q
      toFun_smul := fun a v => by
        rcases zmod2_cases a with rfl | rfl <;> simp [hq0]
      exists_companion' := ⟨B, fun x y => hq x y⟩ }
  have hQ : ∀ v, Q v = q v := fun v => rfl
  have hpolarq : ∀ x y, q (x + y) - q x - q y = B x y := fun x y => by
    linear_combination hq x y
  have hpolar : ∀ x y, QuadraticMap.polar Q x y = B x y := fun x y => by
    show q (x + y) - q x - q y = B x y
    exact hpolarq x y
  have hV : Module.finrank (ZMod 2) W = 2 * 3 := by rw [hdim]
  have hT : ∃ T : Submodule (ZMod 2) W, Module.finrank (ZMod 2) T = 3 ∧
      ∀ x ∈ T, Q x = 0 := ⟨S, hS3, fun x hx => by rw [hQ]; exact hSs x hx⟩
  let bS : Module.Basis (Fin 3) (ZMod 2) S := Module.finBasisOfFinrankEq (ZMod 2) S hS3
  let Wf : ℕ → Submodule (ZMod 2) W := fun i =>
    (bS.flag ⟨min i 3, Nat.lt_succ_of_le (min_le_right _ _)⟩).map S.subtype
  have hWd : ∀ i ≤ 3, Module.finrank (ZMod 2) (Wf i) = i := by
    intro i hi
    have h1 : Module.finrank (ZMod 2) (Wf i) =
        Module.finrank (ZMod 2) (bS.flag ⟨min i 3, Nat.lt_succ_of_le (min_le_right _ _)⟩) :=
      Submodule.finrank_map_subtype_eq S _
    rw [h1, finrank_flag_fin3]
    exact min_eq_left hi
  have hWm : ∀ i < 3, Wf i ≤ Wf (i + 1) := by
    intro i hi
    refine Submodule.map_mono (bS.flag_mono ?_)
    rw [Fin.le_def]
    simp only
    omega
  have hW3 : Wf 3 = S := by
    show (bS.flag ⟨min 3 3, _⟩).map S.subtype = S
    rw [show (⟨min 3 3, _⟩ : Fin 4) = Fin.last 3 from rfl, Module.Basis.flag_last,
      Submodule.map_subtype_top]
  have hWs : ∀ x ∈ Wf 3, q x = 0 := fun x hx => hSs x (hW3 ▸ hx)
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5⟩ :=
    (orthogonal_geometry_split_Witt_flags (K := ZMod 2) (V := W) (Q := Q) (by
      unfold LinearMap.Nondegenerate
      refine ⟨fun m hm => hB m (fun w => ?_), fun n hn => hB n (fun w => ?_)⟩
      · have h2 := hm w
        rw [QuadraticMap.polarBilin_apply_apply] at h2
        have h1 : q (m + w) - q m - q w = 0 := h2
        linear_combination h1 - hpolarq m w
      · have h2 := hn w
        rw [QuadraticMap.polarBilin_apply_apply] at h2
        have h1 : q (w + n) - q w - q n = 0 := h2
        rw [B_symm q B hq]
        linear_combination h1 - hpolarq w n) hV hT).1 3 (by norm_num) Wf hWd hWm hWs
  refine ⟨b, fun i => ⟨hb1 i |>.1, hb1 i |>.2⟩, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact (hpolar _ _).symm.trans (hb2 i j)
  · intro i j
    obtain ⟨h1, h2⟩ := hb3 i j
    exact ⟨(hpolar _ _).symm.trans h1, (hpolar _ _).symm.trans h2⟩
  · intro x y
    exact hb5 x y
  ·
    have hS' : S = Submodule.span (ZMod 2) (b '' (Sum.inl '' {j : Fin 3 | (j : ℕ) < 3})) :=
      hW3.symm.trans (hb4 3 (by norm_num))
    intro v
    rw [hS', Module.Basis.mem_span_image]
    constructor
    · intro hsup j
      by_contra hne
      have hmem : (Sum.inr j : Fin 3 ⊕ Fin 3) ∈ (b.repr v).support :=
        Finsupp.mem_support_iff.2 hne
      obtain ⟨j', _, hj'⟩ := hsup (Finset.mem_coe.2 hmem)
      cases hj'
    · intro hv k hk
      have hk' := Finsupp.mem_support_iff.1 (Finset.mem_coe.1 hk)
      rcases k with j | j
      · exact ⟨j, j.isLt, rfl⟩
      · exact absurd (hv j) hk'

end Witt

end CFSG.Quasithin.H13.C1294

end
