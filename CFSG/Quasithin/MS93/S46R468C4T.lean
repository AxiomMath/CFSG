module

public import CFSG.Quasithin.MS93.S46R468LvA
public import CFSG.Quasithin.MS93.S46SL2Sec

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement Matrix MatrixGroups

section Diag

variable {F : Type} [Field F]

@[expose] noncomputable def diagTwo (t : Fˣ) : SL(2, F) :=
  ⟨!![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

theorem coe_diagTwo (t : Fˣ) :
    ((diagTwo t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] :=
  rfl

end Diag

section SL2

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def ordThree : SL(2, F) :=
  ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩

theorem coe_ordThree : ((ordThree : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 1] :=
  rfl

theorem ordThree_pow_three : (ordThree : SL(2, F)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_ordThree, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem odd_orderOf_ordThree : Odd (orderOf (ordThree : SL(2, F))) :=
  (show Odd 3 by decide).of_dvd_nat (orderOf_dvd_of_pow_eq_one ordThree_pow_three)

theorem odd_orderOf_diagTwo [Fintype F] (t : Fˣ) : Odd (orderOf (diagTwo t : SL(2, F))) := by
  classical
  have hodd : Odd (Fintype.card F - 1) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    rw [hn]
    have : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
    rcases (n : ℕ).eq_zero_or_pos with h0 | hpos
    · simp [h0] at hn
      have := Fintype.one_lt_card (α := F)
      omega
    · exact Nat.Even.sub_odd this (Nat.even_pow.mpr ⟨even_two, hpos.ne'⟩) odd_one
  have hpow : (diagTwo t : SL(2, F)) ^ (Fintype.card F - 1) = 1 := by
    have ht : (t : F) ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ t.ne_zero
    have ht' : ((t⁻¹ : Fˣ) : F) ^ (Fintype.card F - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one _ (t⁻¹).ne_zero
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagTwo, Matrix.SpecialLinearGroup.coe_one]
    have e : (!![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F) =
        Matrix.diagonal ![(t : F), ((t⁻¹ : Fˣ) : F)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [e, Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k
    · exact ht
    · exact ht'
  exact hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hpow)

theorem exists_closure_odd_mulVec_eq_zero [Fintype F] (u : Fin 2 → F) :
    ∃ B ∈ Subgroup.closure {g : SL(2, F) | Odd (orderOf g)},
      ((B : Matrix (Fin 2) (Fin 2) F) *ᵥ u) 1 = 0 := by
  have hmem3 : (ordThree : SL(2, F)) ∈ Subgroup.closure {g : SL(2, F) | Odd (orderOf g)} :=
    Subgroup.subset_closure odd_orderOf_ordThree
  by_cases h1 : u 1 = 0
  · exact ⟨1, Subgroup.one_mem _, by simp [h1]⟩
  by_cases h0 : u 0 = 0
  · refine ⟨ordThree ^ 2, Subgroup.pow_mem _ hmem3 2, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_pow, coe_ordThree]
    simp [sq, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0,
      CharTwo.add_self_eq_zero]
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (u 1 / u 0)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hs
    exact hs.elim h1 h0
  have hu1 : u 1 = s * s * u 0 := (div_eq_iff h0).mp hs
  refine ⟨ordThree * diagTwo (Units.mk0 s hs0), Subgroup.mul_mem _ hmem3
    (Subgroup.subset_closure (odd_orderOf_diagTwo _)), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_ordThree, coe_diagTwo]
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu1]
  field_simp
  ring_nf
  rw [show (2 : F) = 0 from CharTwo.two_eq_zero]
  ring

end SL2

section Lin

variable {F : Type} [Field F]

theorem mulVec_succ_of_mem_stabE0 {A : SL3 F} (hA : A ∈ stabE0) (v : Fin 3 → F) (i : Fin 2) :
    ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ v) i.succ =
      (((blockE0 ⟨A, hA⟩ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ fun j => v j.succ) i := by
  have h0 : (A : Matrix (Fin 3) (Fin 3) F) i.succ 0 = 0 := by
    rw [col_zero_of_mem_stabE0 hA]
    simp [Fin.succ_ne_zero]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, blockE0_apply, h0, zero_mul,
    zero_add]

theorem map_mulVecLin_mul (A B : SL3 F) (W : Submodule F (Fin 3 → F)) :
    W.map (Matrix.mulVecLin ((A * B : SL3 F) : Matrix (Fin 3) (Fin 3) F)) =
      (W.map (Matrix.mulVecLin ((B : SL3 F) : Matrix (Fin 3) (Fin 3) F))).map
        (Matrix.mulVecLin ((A : SL3 F) : Matrix (Fin 3) (Fin 3) F)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVecLin_mul, Submodule.map_comp]

theorem map_mulVecLin_one (W : Submodule F (Fin 3 → F)) :
    W.map (Matrix.mulVecLin ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F)) = W := by
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.mulVecLin_one, Submodule.map_id]

theorem map_eq_ln01_of_mem [Finite F] {A : SL3 F} (hA : A ∈ stabE0)
    {W : Submodule F (Fin 3 → F)} (hW : Module.finrank F W = 2)
    (he : (Pi.single 0 1 : Fin 3 → F) ∈ W) {w : Fin 3 → F} (hw : w ∈ W) (hw0 : w ∉ pt0)
    (hAw : ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ w) 2 = 0) :
    W.map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) = ln01 := by
  set e : Fin 3 → F := Pi.single 0 1 with hedef
  have he0 : e ≠ 0 := fun h => by
    have := congrFun h 0
    simp [hedef] at this
  have hli : LinearIndependent F ![e, w] := by
    refine (LinearIndependent.pair_iff' he0).mpr fun a ha => hw0 ?_
    rw [← ha, mem_pt0]
    simp [hedef]
  have hspan : Submodule.span F (Set.range ![e, w]) = W := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact he
      · exact hw
    · rw [finrank_span_eq_card hli, hW, Fintype.card_fin]
  have hle : W.map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F)) ≤ ln01 := by
    rw [← hspan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · show ((A : Matrix (Fin 3) (Fin 3) F) *ᵥ e) 2 = 0
      rw [mem_stabE0.mp hA]
      simp
    · exact hAw
  have hlin : (Matrix.SpecialLinearGroup.toLin' A : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) =
      Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) F) := by
    refine LinearMap.ext fun v => ?_
    rw [LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVecLin_apply]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [← hlin, LinearEquiv.finrank_map_eq, hW, finrank_ln01]

end Lin

section Lift

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}
  {F : Type} [Field F]

theorem exists_closure_odd_ptTheta_eq {x : Vtx X} {ψ : ↥(stab X x) →* ↥(StatedSL 3 F)}
    [Finite ↥(ptL X x ψ)] (hψs : Function.Surjective ψ) {B : SL(2, F)}
    (hB : B ∈ Subgroup.closure {g : SL(2, F) | Odd (orderOf g)}) :
    ∃ k : ↥(ptL X x ψ),
      (k : X.Universal) ∈ Subgroup.closure {g | g ∈ ptL X x ψ ∧ Odd (orderOf g)} ∧
        ptTheta ψ k = B := by
  induction hB using Subgroup.closure_induction with
  | mem B hB =>
    obtain ⟨a, ha, hao⟩ := exists_odd_preimage_of_surjective (ptTheta_surjective hψs) hB
    exact ⟨a, Subgroup.subset_closure ⟨a.2, by rwa [Subgroup.orderOf_coe]⟩, ha⟩
  | one => exact ⟨1, Subgroup.one_mem _, map_one _⟩
  | mul B₁ B₂ _ _ ih₁ ih₂ =>
    obtain ⟨k₁, hk₁, he₁⟩ := ih₁
    obtain ⟨k₂, hk₂, he₂⟩ := ih₂
    exact ⟨k₁ * k₂, Subgroup.mul_mem _ hk₁ hk₂, by rw [map_mul, he₁, he₂]⟩
  | inv B _ ih =>
    obtain ⟨k, hk, he⟩ := ih
    exact ⟨k⁻¹, Subgroup.inv_mem _ hk, by rw [map_inv, he]⟩

end Lift

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem exists_closure_odd_map_eq_ln01 (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x ℓ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    (he : (Pi.single 0 1 : Fin 3 → F) ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ))) :
    ∃ k : ↥(ptL (puAmalgam c.pu.le) x ψ),
      (k : (puAmalgam c.pu.le).Universal) ∈
          Subgroup.closure {g | g ∈ ptL (puAmalgam c.pu.le) x ψ ∧ Odd (orderOf g)} ∧
        (fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ))).map
          (Matrix.mulVecLin ((toSL3 ψ ⟨k, ptL_le_stab ψ k.2⟩ : SL3 F) :
            Matrix (Fin 3) (Fin 3) F)) = ln01 := by
  have : CharP F 2 := charP_two_of_isSL3FullVia c.via
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have : Finite ↥(stab (puAmalgam c.pu.le) x) := finite_stab c.pu hx
  have : Finite ↥(ptL (puAmalgam c.pu.le) x ψ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (ptL_le_stab ψ))
  set W := fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) with hWdef
  have hW2 : Module.finrank F W = 2 := (I466b.fixN_natImage_qv c.pu c.via h464' hsq hx hxℓ hψU).1
  obtain ⟨w, hwW, hw0⟩ : ∃ w ∈ W, w ∉ pt0 := by
    by_contra hno
    push Not at hno
    have h1 := Submodule.finrank_mono (show W ≤ pt0 from hno)
    rw [hW2, finrank_pt0] at h1
    omega
  obtain ⟨B, hB, hBu⟩ := exists_closure_odd_mulVec_eq_zero fun j : Fin 2 => w j.succ
  obtain ⟨k, hk, hkB⟩ := exists_closure_odd_ptTheta_eq hψs hB
  refine ⟨k, hk, map_eq_ln01_of_mem (mem_ptL_iff.mp k.2).snd hW2 he hwW hw0 ?_⟩
  have h2 := mulVec_succ_of_mem_stabE0 (mem_ptL_iff.mp k.2).snd w 1
  rw [show (Fin.succ (1 : Fin 2) : Fin 3) = 2 from rfl] at h2
  rw [h2, ← ptTheta_apply, hkB]
  exact hBu

theorem exists_closure_odd_smul (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {x : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    {ψ : ↥(stab (puAmalgam c.pu.le) x) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψU : IsSumOfNaturalModulesVia (stab _ x) (Uloc c.pu.le L x) ⊥ ψ false 1)
    {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hPc : ∀ u : ↥(Uloc c.pu.le L x), (u : (puAmalgam c.pu.le).Universal) ∈ P ↔
      natVec hψU u ∈ pt0)
    {ℓ ℓ' : Vtx (puAmalgam c.pu.le)} (hxℓ : (puAmalgam c.pu.le).treeGraph.Adj x ℓ)
    (hxℓ' : (puAmalgam c.pu.le).treeGraph.Adj x ℓ') (hPℓ : P ≤ Usup (puAmalgam c.pu.le) x ℓ)
    (hPℓ' : P ≤ Usup (puAmalgam c.pu.le) x ℓ') :
    ∃ k ∈ Subgroup.closure {g | g ∈ ptL (puAmalgam c.pu.le) x ψ ∧ Odd (orderOf g)},
      Usup (puAmalgam c.pu.le) x (k • ℓ) = Usup _ x ℓ' := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have hm := mem_usup_iff c.pu c.via h464' hsq hx hxℓ hψU
  have hm' := mem_usup_iff c.pu c.via h464' hsq hx hxℓ' hψU
  obtain ⟨u₀, hu₀⟩ := natVec_surjective hψU (Pi.single 0 1 : Fin 3 → F)
  have hu₀P : (u₀ : (puAmalgam c.pu.le).Universal) ∈ P :=
    (hPc u₀).mpr (by rw [hu₀, mem_pt0]; simp)
  have he : (Pi.single 0 1 : Fin 3 → F) ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ)) := by
    rw [← hu₀]; exact (hm u₀).mp (hPℓ hu₀P)
  have he' : (Pi.single 0 1 : Fin 3 → F) ∈ fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ')) := by
    rw [← hu₀]; exact (hm' u₀).mp (hPℓ' hu₀P)
  obtain ⟨k₁, hk₁, he₁⟩ := exists_closure_odd_map_eq_ln01 h464 h465 c hx hxℓ hψs hψU he
  obtain ⟨k₂, hk₂, he₂⟩ := exists_closure_odd_map_eq_ln01 h464 h465 c hx hxℓ' hψs hψU he'
  set k : ↥(ptL (puAmalgam c.pu.le) x ψ) := k₂⁻¹ * k₁ with hkdef
  have hks : (k : (puAmalgam c.pu.le).Universal) ∈ stab (puAmalgam c.pu.le) x :=
    ptL_le_stab ψ k.2
  have hkC : (k : (puAmalgam c.pu.le).Universal) ∈
      Subgroup.closure {g | g ∈ ptL (puAmalgam c.pu.le) x ψ ∧ Odd (orderOf g)} := by
    rw [hkdef, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₂) hk₁
  refine ⟨k, hkC, ?_⟩
  have hψk : toSL3 ψ ⟨k, hks⟩ =
      (toSL3 ψ ⟨k₂, ptL_le_stab ψ k₂.2⟩)⁻¹ * toSL3 ψ ⟨k₁, ptL_le_stab ψ k₁.2⟩ := by
    rw [← map_inv, ← map_mul]
    rfl
  have hWW : (fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ))).map
      (Matrix.mulVecLin ((toSL3 ψ ⟨k, hks⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F)) =
      fixN (natImage ψ (Qv (puAmalgam c.pu.le) ℓ')) := by
    rw [hψk, map_mulVecLin_mul, he₁, ← he₂, ← map_mulVecLin_mul, inv_mul_cancel,
      map_mulVecLin_one]
  have hkx : (k : (puAmalgam c.pu.le).Universal) • x = x := MulAction.mem_stabilizer_iff.mp hks
  have hU : Usup (puAmalgam c.pu.le) x ((k : (puAmalgam c.pu.le).Universal) • ℓ) =
      (Usup (puAmalgam c.pu.le) x ℓ).map
        (MulAut.conj (k : (puAmalgam c.pu.le).Universal)).toMonoidHom := by
    have h1 := usup_smul (puAmalgam c.pu.le) (k : (puAmalgam c.pu.le).Universal) x ℓ
    rwa [hkx] at h1
  rw [hU]
  exact map_conj_eq_of_coord hψU (usup_le_uloc' c.pu hfull hx hxℓ)
    (usup_le_uloc' c.pu hfull hx hxℓ') hm hm' ⟨k, hks⟩ hWW

end CFSG.Quasithin.MS93.S46R
