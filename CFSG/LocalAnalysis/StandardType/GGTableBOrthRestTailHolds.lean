module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailMain

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.SeitzReduction.OmegaPilot

namespace OrthRestTail

section Proj

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

theorem exists_R_of_torusConcl {Q₀ : (ι → K) → K}
    (hsc : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q₀) = ⊥) {p r : ℕ}
    (h : TorusConcl Q₀ p r) :
    ∃ U E : Subgroup (LargeEvenProj (LargeEvenOmega Q₀)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set (LargeEvenProj (LargeEvenOmega Q₀))) ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ r := by
  obtain ⟨U, E, hU, hE, hU1, hU2, hEU, hEab, hEc⟩ := h
  set H := LargeEvenOmega Q₀
  set φ := (TableBOrth.projMkEquiv hsc).toMonoidHom
  have hφ : Function.Injective φ := (TableBOrth.projMkEquiv hsc).injective
  have hEab' : IsElemAbelian p (E.subgroupOf H) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact TableB.IsElemAbelian.comm hEab a.2 b.2
    · rw [Subgroup.coe_pow]
      exact hEab.2 _ hx
  refine ⟨(U.subgroupOf H).map φ, (E.subgroupOf H).map φ, ?_, ?_, ?_,
    TableB.isElemAbelian_map hEab' φ, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hφ]
    intro hb
    apply hU1
    rw [eq_bot_iff]
    intro g hg
    have hg' : (⟨g, hU hg⟩ : H) ∈ U.subgroupOf H := hg
    rw [hb, Subgroup.mem_bot] at hg'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hg')
  · rintro ⟨_, x, hx, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hx2 : x ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hU2 _ hx)
    rw [pow_one, Subgroup.coe_pow]
    change φ x ^ 2 = 1
    rw [← map_pow, hx2, map_one]
  · refine le_trans (Subgroup.map_mono fun h hh => ?_) (Subgroup.le_normalizer_map φ)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    exact Subgroup.mem_normalizer_iff.mp (hEU hh) g
  · rw [Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv, hEc]

end Proj

section Minus

variable {K : Type} [Field K] {m : ℕ}

@[expose] def minusFrame (b c : K) : HypFrame (TableBOrth.qMinusForm K m b c) m where
  X := ⟨Sum.inl ∘ Sum.inl, Sum.inl_injective.comp Sum.inl_injective⟩
  Y := ⟨Sum.inl ∘ Sum.inr, Sum.inl_injective.comp Sum.inr_injective⟩
  X_ne_Y _ _ h := Sum.inl_ne_inr (Sum.inl_injective h)
  hyp i := TableBOrth.isHypCoord_qMinusForm b c i

@[expose] def planePos (m : ℕ) : Fin 2 ↪ LargeEvenMinusIdx m := ⟨Sum.inr, Sum.inr_injective⟩

@[expose] noncomputable def planeGL :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL (LargeEvenMinusIdx m) K :=
  (posGL (planePos m)).comp Matrix.SpecialLinearGroup.toGL

theorem planeGL_injective : Function.Injective (planeGL (K := K) (m := m)) :=
  (posGL_injective _).comp Matrix.SpecialLinearGroup.toGL_injective

theorem planeGL_mem_suppSub (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    planeGL (m := m) A ∈ suppSub K (Set.range (planePos m)) :=
  posGL_mem_suppSub _ _

theorem map_planeGL (b c : K) {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : ∀ x, binF b c ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x) = binF b c x)
    (v : LargeEvenMinusIdx m → K) :
    LargeEvenQMinus m b c (((planeGL (m := m) A : GL (LargeEvenMinusIdx m) K) :
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ v) = LargeEvenQMinus m b c v := by
  rw [planeGL, MonoidHom.comp_apply, posGL_mulVec]
  have h1 : ∀ k, posLin (planePos m) ((Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) v (Sum.inl k) = v (Sum.inl k) := fun k =>
    posLin_apply_of_not_mem _ _ _ (by rintro ⟨i, hi⟩; exact Sum.inr_ne_inl hi)
  have h2 : ∀ i, posLin (planePos m) ((Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) v (Sum.inr i) =
        ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ (v ∘ planePos m)) i := fun i =>
    posLin_apply_pos (planePos m) _ v i
  have h3 := hA (v ∘ planePos m)
  simp only [binF, Function.comp_apply, planePos, Function.Embedding.coeFn_mk] at h3
  simp only [LargeEvenQMinus, h1, h2]
  simp only [planePos, Function.Embedding.coeFn_mk] at h3 ⊢
  linear_combination h3

theorem disjoint_planePos (b c : K) :
    Disjoint (Set.range (planePos m)) ((minusFrame (m := m) b c).pairSet 0 m) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, -, -, h | h⟩ <;>
    simp [planePos, minusFrame, Function.Embedding.coeFn_mk] at h

theorem torus_minus [Finite K] [CharP K 2] {n p : ℕ} (b c : K) (hK : Nat.card K = 2 ^ n)
    (hm : 3 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ U E : Subgroup (OrthRest.RMinus K m b c), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set (OrthRest.RMinus K m b c)) ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ m := by
  obtain ⟨M, σ, hM, hσ, hMF, hσF⟩ := exists_rot hK hirr hp hp2 hpn
  have hMp : M ^ p = 1 := hM ▸ pow_orderOf_eq_one M
  have hPΩ : planeGL (m := m) M ∈ LargeEvenOmega ⇑(TableBOrth.qMinusForm K m b c) := by
    rw [TableBOrth.coe_qMinusForm]
    refine mem_omega_of_conj_inv (w := planeGL σ)
      (TableBSymp.mem_orthGroup_of_isometry (map_planeGL b c hMF))
      (TableBSymp.mem_orthGroup_of_isometry (map_planeGL b c hσF)) ?_ (hp.odd_of_ne_two hp2)
      (by rw [← map_pow, hMp, map_one])
    rw [← map_inv, ← map_mul, ← map_mul, hσ, map_inv]
  have hP := torusConcl_of_frame (minusFrame (m := m) b c) hp hp2 hM hσ hm
    (P := Subgroup.zpowers (planeGL M)) (SP := Set.range (planePos m))
    (Subgroup.zpowers_le.mpr (planeGL_mem_suppSub M)) (disjoint_planePos b c)
    (isElemAbelian_zpowers' (by rw [← map_pow, hMp, map_one])) (Subgroup.zpowers_le.mpr hPΩ)
    (e := 1) (by rw [Nat.card_zpowers, orderOf_injective _ planeGL_injective, hM, pow_one])
  rw [TableBOrth.coe_qMinusForm, show m - 1 + 1 = m by omega] at hP
  exact exists_R_of_torusConcl (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot b c) hP

end Minus

section Plus

variable {K : Type} [Field K]

variable (K) in
@[expose] def plusFrame (m : ℕ) : HypFrame (TableBOrth.qPlusForm K m) m where
  X := ⟨Sum.inl, Sum.inl_injective⟩
  Y := ⟨Sum.inr, Sum.inr_injective⟩
  X_ne_Y _ _ h := Sum.inl_ne_inr h
  hyp i := TableBOrth.isHypCoord_qPlusForm i

theorem torus_plus [Finite K] {m : ℕ} (hK : Nat.card K = 2) (hm : 4 ≤ m) :
    ∃ U E : Subgroup (OrthRest.RPlus K m), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      E ≤ Subgroup.normalizer (U : Set (OrthRest.RPlus K m)) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ (m - 1) := by
  have hK' : Nat.card K = 2 ^ 1 := hK.trans (pow_one 2).symm
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hK'
  have hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0 := by
    intro s
    have := Fintype.ofFinite K
    have hs : s ^ 2 = s := by
      have h := FiniteField.pow_card s
      rwa [Fintype.card_eq_nat_card, hK] at h
    rw [hs, one_mul, CharTwo.add_self_eq_zero, zero_add]
    exact one_ne_zero
  obtain ⟨M, σ, hM, hσ, -, -⟩ := exists_rot hK' hirr Nat.prime_three (by norm_num) (by norm_num)
  have hP := torusConcl_of_frame (plusFrame K m) Nat.prime_three (by norm_num) hM hσ (by omega)
    (P := ⊥) (SP := ∅) bot_le (Set.empty_disjoint _) isElemAbelian_bot' bot_le (e := 0)
    (by rw [Subgroup.card_bot, pow_zero])
  rw [TableBOrth.coe_qPlusForm, add_zero] at hP
  exact exists_R_of_torusConcl (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (by omega)) hP

end Plus

end OrthRestTail

theorem ggOrthRestTorusInput_holds : GGOrthRestTorusInput := by
  refine ⟨fun K _ _ n m p b c hK hm hp hpn hbc => ?_, fun K _ _ m hK hm => ?_⟩
  · have hn : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · have h1 : 1 < Nat.card K := Finite.one_lt_card
        rw [hK, h0, pow_zero] at h1
        omega
      · exact h0
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        hn hK
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    exact OrthRestTail.torus_minus b c hK hm hp hp2 hpn hbc
  · exact OrthRestTail.torus_plus hK hm

end CFSG.StandardType
