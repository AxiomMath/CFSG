module

public import CFSG.RankThree.SubgroupLists.SymplecticReducible
public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup Module
open CFSG.RankThree.SubgroupLists (spForm IsIrreducibleOn orth mem_orth finrank_orth
  spForm_mulVec gl_mulVec_mul gl_mulVec_inv_mulVec)
open scoped Matrix

variable {q : ℕ} [Fact q.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]

theorem exists_fixed_mem {F : Subgroup (GL σ (ZMod q))} (hF : IsPGroup q F)
    {U : Submodule (ZMod q) (σ → ZMod q)}
    (hU : ∀ f ∈ F, ∀ u ∈ U, (f : Matrix σ σ (ZMod q)) *ᵥ u ∈ U) (hne : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 0 ∧ ∀ f ∈ F, (f : Matrix σ σ (ZMod q)) *ᵥ u = u := by
  let _ : MulAction F U :=
    { smul := fun f u => ⟨((f : GL σ (ZMod q)) : Matrix σ σ (ZMod q)) *ᵥ u, hU f f.2 u u.2⟩
      one_smul := fun u => Subtype.ext (by
        change ((1 : GL σ (ZMod q)) : Matrix σ σ (ZMod q)) *ᵥ (u : σ → ZMod q) = u
        rw [Units.val_one, Matrix.one_mulVec])
      mul_smul := fun f g u => Subtype.ext (by
        change (((f * g : F) : GL σ (ZMod q)) : Matrix σ σ (ZMod q)) *ᵥ (u : σ → ZMod q) =
          ((f : GL σ (ZMod q)) : Matrix σ σ (ZMod q)) *ᵥ
            (((g : GL σ (ZMod q)) : Matrix σ σ (ZMod q)) *ᵥ (u : σ → ZMod q))
        rw [Subgroup.coe_mul, gl_mulVec_mul]) }
  have hcard : q ∣ Nat.card U := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
    exact dvd_pow_self q fun h => hne (Submodule.finrank_eq_zero.1 h)
  have h0 : (0 : U) ∈ MulAction.fixedPoints F U := fun f => Subtype.ext (by
    change ((f : GL σ (ZMod q)) : Matrix σ σ (ZMod q)) *ᵥ 0 = 0
    exact Matrix.mulVec_zero _)
  obtain ⟨v, hv, hne'⟩ := hF.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hcard h0
  refine ⟨v, v.2, fun h => hne' (Subtype.ext h.symm), fun f hf => ?_⟩
  have hfv : (⟨f, hf⟩ : F) • v = v := hv ⟨f, hf⟩
  exact congrArg Subtype.val hfv

theorem eq_neg_one_of_commute {K : Type} [Field K] {P : Subgroup (GL σ K)}
    (hirr : IsIrreducibleOn P) {z : GL σ K} (hzP : ∀ g ∈ P, g * z = z * g) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : z = -1 := by
  obtain ⟨Vm, hmem⟩ : ∃ Vm : Submodule K (σ → K), ∀ v, v ∈ Vm ↔ (z : Matrix σ σ K) *ᵥ v = -v :=
    ⟨{ carrier := {v | (z : Matrix σ σ K) *ᵥ v = -v}
       add_mem' := by
         intro a b ha hb
         simp only [Set.mem_setOf_eq] at ha hb ⊢
         rw [Matrix.mulVec_add, ha, hb, neg_add]
       zero_mem' := by simp
       smul_mem' := by
         intro c v hv
         simp only [Set.mem_setOf_eq] at hv ⊢
         rw [Matrix.mulVec_smul, hv, smul_neg] }, fun _ => Iff.rfl⟩
  have hinv : ∀ g ∈ P, ∀ v ∈ Vm, (g : Matrix σ σ K) *ᵥ v ∈ Vm := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    rw [← gl_mulVec_mul, ← hzP g hg, gl_mulVec_mul, hv, Matrix.mulVec_neg]
  rcases hirr Vm hinv with h | h
  · exfalso
    apply hz1
    have hfix : ∀ v, (z : Matrix σ σ K) *ᵥ v = v := by
      intro v
      have hw : (z : Matrix σ σ K) *ᵥ v - v ∈ Vm := by
        rw [hmem, Matrix.mulVec_sub, ← gl_mulVec_mul, hz2, Units.val_one, Matrix.one_mulVec,
          neg_sub]
      rw [h, Submodule.mem_bot, sub_eq_zero] at hw
      exact hw
    apply Units.ext
    rw [Units.val_one]
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hfix, Matrix.one_mulVec])
  · have hneg : ∀ v, (z : Matrix σ σ K) *ᵥ v = -v := by
      intro v
      have hv : v ∈ Vm := by
        rw [h]
        exact Submodule.mem_top
      exact (hmem v).1 hv
    apply Units.ext
    rw [Units.val_neg, Units.val_one]
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hneg, Matrix.neg_mulVec, Matrix.one_mulVec])

theorem even_finrank_of_pow_eq_neg_one (hq2 : q ≠ 2) {h : GL σ (ZMod q)}
    (hh : h ^ (q ^ 2 / 2) = -1) {U : Submodule (ZMod q) (σ → ZMod q)}
    (hU : ∀ u ∈ U, (h : Matrix σ σ (ZMod q)) *ᵥ u ∈ U) : Even (finrank (ZMod q) U) := by
  have hq : q.Prime := Fact.out
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  obtain ⟨j, hj⟩ := hq.odd_of_ne_two hq2
  have hN : q ^ 2 / 2 = (q - 1) * (j + 1) := by
    rw [hj, Nat.add_sub_cancel, show (2 * j + 1) ^ 2 = 1 + 2 * (2 * j * (j + 1)) by ring,
      Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
    norm_num
  have hNpos : q ^ 2 / 2 ≠ 0 := by
    have h2 := hq.two_le
    rw [hN]
    exact Nat.mul_ne_zero (by omega) (by omega)
  let r : U →ₗ[ZMod q] U :=
    (Matrix.toLin' (h : Matrix σ σ (ZMod q))).restrict fun u hu => by
      rw [Matrix.toLin'_apply]
      exact hU u hu
  have hr1 : ∀ x : U, ((r x : U) : σ → ZMod q) = (h : Matrix σ σ (ZMod q)) *ᵥ (x : σ → ZMod q) :=
    fun _ => rfl
  have hpow : ∀ (n : ℕ) (x : U), ((r ^ n) x : σ → ZMod q) =
      ((h ^ n : GL σ (ZMod q)) : Matrix σ σ (ZMod q)) *ᵥ (x : σ → ZMod q) := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, pow_zero, Module.End.one_apply, Units.val_one, Matrix.one_mulVec]
    | succ n ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, hr1, pow_succ, gl_mulVec_mul]
  have hr : r ^ (q ^ 2 / 2) = (-1 : ZMod q) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [hpow, hh, Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
    simp
  have hdet : LinearMap.det r ^ (q ^ 2 / 2) = (-1) ^ finrank (ZMod q) U := by
    rw [← map_pow, hr, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hne : LinearMap.det r ≠ 0 := by
    intro h0
    rw [h0, zero_pow hNpos] at hdet
    exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) hdet.symm
  rw [hN, pow_mul, ZMod.pow_card_sub_one_eq_one hne, one_pow] at hdet
  exact (neg_one_pow_eq_one_iff_even (Ring.neg_one_ne_one_of_char_ne_two hchar)).1 hdet.symm

theorem exists_flag (hq2 : q ≠ 2) {F : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod q))}
    (hFS : F ≤ CFSG.Open.StatedSp 2 (ZMod q)) (hFq : IsPGroup q F) (hF1 : F ≠ ⊥)
    {h : GL (Fin 2 ⊕ Fin 2) (ZMod q)} (hhS : h ∈ CFSG.Open.StatedSp 2 (ZMod q))
    (hhF : h ∈ normalizer (F : Set (GL (Fin 2 ⊕ Fin 2) (ZMod q))))
    (hh : h ^ (q ^ 2 / 2) = -1) :
    ∃ W : Submodule (ZMod q) (Fin 2 ⊕ Fin 2 → ZMod q), Nat.card W = q ^ 2 ∧
      (∀ v ∈ W, ∀ w ∈ W, spForm 2 (ZMod q) v w = 0) ∧
      ∀ f ∈ F, ∀ w ∈ W, (f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ w = w := by
  obtain ⟨W, hmemW⟩ : ∃ W : Submodule (ZMod q) (Fin 2 ⊕ Fin 2 → ZMod q), ∀ v, v ∈ W ↔
      ∀ f ∈ F, (f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ v = v :=
    ⟨{ carrier := {v | ∀ f ∈ F, (f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ v = v}
       add_mem' := by
         intro a b ha hb f hf
         rw [Matrix.mulVec_add, ha f hf, hb f hf]
       zero_mem' := by
         intro f _
         exact Matrix.mulVec_zero _
       smul_mem' := by
         intro c v hv f hf
         rw [Matrix.mulVec_smul, hv f hf] }, fun _ => Iff.rfl⟩
  have hconj : ∀ g ∈ normalizer (F : Set (GL (Fin 2 ⊕ Fin 2) (ZMod q))), ∀ v ∈ W,
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ v ∈ W := by
    intro g hg v hv
    rw [hmemW] at hv ⊢
    intro f hf
    have hf' : g⁻¹ * f * g ∈ F := (mem_normalizer_iff.1 hg _).2 (by
      rw [show g * (g⁻¹ * f * g) * g⁻¹ = f by group]
      exact hf)
    rw [← gl_mulVec_mul, show f * g = g * (g⁻¹ * f * g) by group, gl_mulVec_mul, hv _ hf']
  have hW0 : W ≠ ⊥ := by
    obtain ⟨v, -, hv0, hvf⟩ :=
      exists_fixed_mem hFq (U := ⊤) (fun _ _ _ _ => Submodule.mem_top) top_ne_bot
    intro hbot
    have hvW : v ∈ W := (hmemW v).2 hvf
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv0 hvW
  have hWtop : W ≠ ⊤ := by
    intro htop
    apply hF1
    rw [eq_bot_iff]
    intro f hf
    rw [Subgroup.mem_bot]
    have hfix : ∀ v, (f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ v = v := by
      intro v
      have hvW : v ∈ W := by
        rw [htop]
        exact Submodule.mem_top
      exact (hmemW v).1 hvW f hf
    apply Units.ext
    rw [Units.val_one]
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec, hfix])
  have hW2 : finrank (ZMod q) W = 2 := by
    obtain ⟨k, hk⟩ := even_finrank_of_pow_eq_neg_one hq2 hh (hconj h hhF)
    have hpos : finrank (ZMod q) W ≠ 0 := fun h0 => hW0 (Submodule.finrank_eq_zero.1 h0)
    have hlt := Submodule.finrank_lt hWtop
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hlt
    omega
  have hcard : Nat.card W = q ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod, hW2]
  have horth : ∀ g ∈ normalizer (F : Set (GL (Fin 2 ⊕ Fin 2) (ZMod q))),
      g ∈ CFSG.Open.StatedSp 2 (ZMod q) → ∀ v ∈ orth W,
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ v ∈ orth W := by
    intro g hg hgS v hv
    rw [mem_orth] at hv ⊢
    intro u hu
    rw [← gl_mulVec_inv_mulVec g u, spForm_mulVec hgS]
    exact hv _ (hconj g⁻¹ (inv_mem hg) u hu)
  obtain ⟨k, hk⟩ := even_finrank_of_pow_eq_neg_one hq2 hh (U := W ⊓ orth W) fun u hu =>
    Submodule.mem_inf.2 ⟨hconj h hhF u (Submodule.mem_inf.1 hu).1,
      horth h hhF hhS u (Submodule.mem_inf.1 hu).2⟩
  have hUle : finrank (ZMod q) (W ⊓ orth W : Submodule (ZMod q) _) ≤ 2 :=
    (Submodule.finrank_mono (inf_le_left : W ⊓ orth W ≤ W)).trans hW2.le
  rcases (by omega : finrank (ZMod q) (W ⊓ orth W : Submodule (ZMod q) _) = 0 ∨
      finrank (ZMod q) (W ⊓ orth W : Submodule (ZMod q) _) = 2) with h0 | h2
  ·
    exfalso
    have hOinv : ∀ f ∈ F, ∀ v ∈ orth W,
        (f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod q)) *ᵥ v ∈ orth W := by
      intro f hf v hv
      rw [mem_orth] at hv ⊢
      intro u hu
      rw [← (hmemW u).1 hu f hf, spForm_mulVec (hFS hf)]
      exact hv u hu
    have hO0 : orth W ≠ ⊥ := by
      intro hbot
      have h4 := finrank_orth W
      rw [hbot, finrank_bot, hW2] at h4
      omega
    obtain ⟨v, hvO, hv0, hvf⟩ := exists_fixed_mem hFq hOinv hO0
    have hvU : v ∈ W ⊓ orth W := Submodule.mem_inf.2 ⟨(hmemW v).2 hvf, hvO⟩
    rw [Submodule.finrank_eq_zero.1 h0, Submodule.mem_bot] at hvU
    exact hv0 hvU
  ·
    have hUW : W ⊓ orth W = W := Submodule.eq_of_le_of_finrank_eq inf_le_left (h2.trans hW2.symm)
    refine ⟨W, hcard, fun v hv w hw => ?_, fun f hf w hw => (hmemW w).1 hw f hf⟩
    have hw' : w ∈ W ⊓ orth W := by
      rw [hUW]
      exact hw
    exact mem_orth.1 (Submodule.mem_inf.1 hw').2 v hv

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
