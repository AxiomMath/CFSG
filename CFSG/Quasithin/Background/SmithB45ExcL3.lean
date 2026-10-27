module

public import CFSG.Quasithin.Background.SmithB45ExcBlocks
public import CFSG.Quasithin.Background.SmithB45ExcL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Top

public section

namespace CFSG.Quasithin.B45Exc

open Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank CFSG.Quasithin
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family

section Inner

variable {K : Type} [Field K] [Fintype K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E] (ρ₀ : SpecialLinearGroup (Fin 3) K →* (E ≃ₗ[ZMod 2] E))

theorem negD_rank2 (h2 : (2 : K) ≠ 0) (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k)
    (hodd : Odd (Fintype.card K)) (hpr : (Fintype.card K).Prime) (hp5 : 5 ≤ Fintype.card K)
    (hρ : ∀ g, ρ₀ g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    8 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ₀ negD))) := by
  classical
  have hV := isVAct_vRep ρ₀
  have hall := lineProj_ne_zero_of_trans hV hodd (vRep_faithful ρ₀ hρ) (vRep_trans ρ₀)
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  have hm1 : (-1 : K) ≠ 0 := neg_ne_zero.2 h1
  have h11 : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have hA : (-1 : K) - 1 ≠ 0 := by
    intro h
    apply h2
    linear_combination -h
  have hB : (1 : K) + 1 ≠ 0 := by
    rw [one_add_one_eq_two]; exact h2
  set U : Finset (K × K) := {(1, 0), (0, 1), (1, 1), (1, -1)} with hU
  have hmem : ∀ u ∈ U, u = (1, 0) ∨ u = (0, 1) ∨ u = (1, 1) ∨ u = (1, -1) := by
    intro u hu
    simpa [hU] using hu
  have hU0 : ∀ u ∈ U, u ≠ 0 := by
    intro u hu
    rcases hmem u hu with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff]
  have hUind : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0 := by
    intro u hu v hv huv
    rcases hmem u hu with rfl | rfl | rfl | rfl <;> rcases hmem v hv with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl huv
      | simp [det2, hm1, hA, hB]
  have hcard : U.card = 4 := by
    rw [hU, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [Prod.ext_iff, h11]
    · simp [Prod.ext_iff]
    · simp [Prod.ext_iff]
  have hs : ρ₀ negD * ρ₀ negD = 1 := by rw [← map_mul, negD_mul_self, map_one]
  have hsρ : ∀ x, ρ₀ negD * vRep ρ₀ x * ρ₀ negD = vRep ρ₀ (-x) := by
    intro x
    have := congrArg ρ₀ (negD_mul_uSL x)
    rw [map_mul, map_mul] at this
    calc ρ₀ negD * vRep ρ₀ x * ρ₀ negD = ρ₀ (uSL (-x)) * ρ₀ negD * ρ₀ negD := by
          simp only [vRep]; rw [this]
      _ = vRep ρ₀ (-x) := by rw [mul_assoc, hs, mul_one]; rfl
  have := two_mul_card_le_finrank_range_sub1 hV hodd hpr hp5 hK hs hsρ U hU0 hUind
    (fun u hu => hall u (hU0 u hu))
  rw [hcard] at this
  exact this

theorem inner_rank_ge_eight (h2 : (2 : K) ≠ 0) (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k)
    (hodd : Odd (Fintype.card K)) (hpr : (Fintype.card K).Prime) (hp5 : 5 ≤ Fintype.card K)
    (hρ : ∀ g, ρ₀ g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K))
    {t : SpecialLinearGroup (Fin 3) K} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    8 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ₀ t))) := by
  obtain ⟨P, hP⟩ := exists_conj_negD h2 ht2 ht1
  have : ρ₀ t = ρ₀ P * ρ₀ negD * (ρ₀ P)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← map_mul, ← map_mul, hP]
  rw [this, finrank_range_sub1_conj]
  exact negD_rank2 ρ₀ h2 hK hodd hpr hp5 hρ

end Inner

section Outer

variable {W : Type} [CommGroup W] {K : Type} [Field K]
  {L : Subgroup (MulAut W)} (D : CoverData3 K L)

open CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear

theorem outer_rank2 [Fintype K] [DecidableEq K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [Finite W] [Fact (∀ w : W, w * w = 1)] (h2 : (2 : K) ≠ 0)
    (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k) (hodd : Odd (Fintype.card K))
    (hpr : (Fintype.card K).Prime) (hp5 : 5 ≤ Fintype.card K)
    (hperf : Group.IsPerfect (SpecialLinearGroup (Fin 3) K)) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) (A : GL (Fin 3) K)
    (hA : (A : Matrix (Fin 3) (Fin 3) K)ᵀ = A) (hβ : D.beta hb = conjAut 3 K A * dualAut 3 K) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin b))) := by
  obtain ⟨v, hv0, hvadd, hvinv, hvfaith⟩ := exists_inverted_vgroup (p := p) h2 A hA
  let σA : MulAut (SpecialLinearGroup (Fin 3) K) :=
    CatalogueBHigherLinearAction.slConjugation 3 K A * CatalogueBGraphForm.slGraphAut 3 K
  have hdesc : descendAut 3 K σA = conjAut 3 K A * dualAut 3 K := by
    simp only [σA, map_mul]; rfl
  have hrel := D.conj_eq hperf hb σA (hβ.trans hdesc.symm)
  have hσv : ∀ a, σA (v a) = (v a)⁻¹ := by
    intro a
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have := hvinv a
    simp only [σA, MulAut.mul_apply]
    rw [CatalogueBHigherLinearAction.slConjugation_matrix,
      CatalogueBGraphForm.slGraphAut_matrix]
    exact congrFun (congrFun this i) j
  have hvneg : ∀ a, v (-a) = (v a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_right
    rw [← hvadd, add_neg_cancel, hv0]
  let ρ' : K × K → (Additive W ≃ₗ[ZMod 2] Additive W) := fun a =>
    binaryLin ((D.φ (v a) : ↥L) : MulAut W)
  have hV : IsVAct ρ' := ⟨by simp [ρ', hv0], fun x y => by simp [ρ', hvadd]⟩
  have hfaith : ∀ x, ρ' x = 1 → x = 0 := by
    intro x hx
    have h1 : ((D.φ (v x) : ↥L) : MulAut W) = 1 :=
      binaryLin_injective (by rw [map_one]; exact hx)
    have h2' : D.φ (v x) = 1 := Subtype.ext h1
    exact hvfaith x (D.ker_central _ (MonoidHom.mem_ker.2 h2'))
  have hs : binaryLin b * binaryLin b = 1 := by rw [← map_mul, hb2, map_one]
  have hsρ : ∀ a, binaryLin b * ρ' a * binaryLin b = ρ' (-a) := by
    intro a
    have h1 : b * ((D.φ (v a) : ↥L) : MulAut W) * b = ((D.φ (v (-a)) : ↥L) : MulAut W) := by
      have := hrel (v a)
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      rw [hσv, hbinv] at this
      rw [this, hvneg, map_inv, Subgroup.coe_inv]
    show binaryLin b * binaryLin ((D.φ (v a) : ↥L) : MulAut W) * binaryLin b =
      binaryLin ((D.φ (v (-a)) : ↥L) : MulAut W)
    rw [← map_mul, ← map_mul, h1]
  obtain ⟨o, o', hne, ho, ho'⟩ := exists_two_lines hV hodd hfaith
  have hdet : det2 (lineRep o) (lineRep o') ≠ 0 := det2_lineRep hne
  have hdet' : det2 (lineRep o') (lineRep o) ≠ 0 := det2_lineRep hne.symm
  have hne' : lineRep o ≠ lineRep o' := fun h => hdet (by rw [h]; simp [det2]; ring)
  classical
  have := two_mul_card_le_finrank_range_sub1 hV hodd hpr hp5 hK hs hsρ {lineRep o, lineRep o'}
    (by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact lineRep_ne_zero _
      · rw [Finset.mem_singleton.1 hu]; exact lineRep_ne_zero _)
    (by
      intro u hu w hw huw
      rcases Finset.mem_insert.1 hu with rfl | hu <;>
        rcases Finset.mem_insert.1 hw with rfl | hw
      · exact absurd rfl huw
      · rw [Finset.mem_singleton.1 hw]; exact hdet
      · rw [Finset.mem_singleton.1 hu]
        exact hdet'
      · rw [Finset.mem_singleton.1 hu, Finset.mem_singleton.1 hw] at huw
        exact absurd rfl huw)
    (by
      intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact ho
      · rw [Finset.mem_singleton.1 hu]; exact ho')
  rw [Finset.card_pair hne'] at this
  exact this

end Outer

theorem primeLinearThreeExclusion2F (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (W : Type)
    [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) (Lb : Subgroup (MulAut W))
    (hperf : Group.IsPerfect ↥Lb) (hirr : X1.IsIrrOn Lb)
    (hmod : StatedClassicalModel (CQ Lb) .PSL 3 p 1) (B : Subgroup (MulAut W))
    (hBN : B ≤ Subgroup.normalizer (Lb : Set (MulAut W))) (hB1 : B ≠ ⊥)
    (hB2 : IsElemAbelian2 B) : Nat.card B ^ 2 * Nat.card (fixV B) < Nat.card W := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (∀ w : W, w * w = 1) := ⟨hW⟩
  have : Nontrivial W := hirr.1
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hodd := odd_card_center_of_irreducible hW hirr.2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hKp : Nat.card K = p := by rw [hK, pow_one]
  have : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = p := by rw [← Nat.card_eq_fintype_card]; exact hKp
  have : CharP K p := charP_of_card_eq_prime_pow (p := p) (f := 1) (by rw [pow_one]; exact hKcard)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hoddK : Odd (Fintype.card K) := by rw [hKcard]; exact hpodd
  have hprK : (Fintype.card K).Prime := by rw [hKcard]; exact hp
  have hp5K : 5 ≤ Fintype.card K := by rw [hKcard]; exact hp5
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hKprime : ∀ k : K, ∃ n : ℕ, (n : K) = k := exists_natCast_of_card_prime hKp
  have hσ : ∀ σ : K ≃+* K, σ = 1 := fun σ => RingEquiv.ext fun k => by
    obtain ⟨n, rfl⟩ := hKprime k
    simp
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  obtain ⟨D⟩ := exists_coverData3 hp hp2 hperf hodd hKp e
  have hkerodd : Odd (Nat.card D.φ.ker) :=
    odd_card_of_pow_three fun g => Subtype.ext (by simpa using center_cube (D.ker_central g.1 g.2))
  let ρ₀ : SpecialLinearGroup (Fin 3) K →* (Additive W ≃ₗ[ZMod 2] Additive W) :=
    binaryLin.comp (Lb.subtype.comp D.φ)
  have hρ : ∀ g, ρ₀ g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro g hg
    have h1 : (D.φ g : MulAut W) = 1 := binaryLin_injective (by rw [map_one]; exact hg)
    exact D.ker_central g (MonoidHom.mem_ker.2 (Subtype.ext h1))
  have hB2' : ∀ a ∈ B, a * a = 1 := fun a ha => by
    have := hB2.2 a ha
    rwa [pow_two] at this
  have hbN : ∀ a ∈ B, a ∈ Subgroup.normalizer (Lb : Set (MulAut W)) := fun a ha => hBN ha
  have hin : ∀ t ∈ B, t ∈ Lb → t ≠ 1 →
      7 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin t))) := by
    intro t htB htL ht1
    obtain ⟨g, hg2, hgt⟩ := exists_involution_lift D.φ hkerodd (t := (⟨t, htL⟩ : ↥Lb))
      (Subtype.ext (hB2' t htB)) (MonoidHom.mem_range.2 (D.surj _))
    have hg1 : g ≠ 1 := fun h => ht1 (by
      have := hgt
      rw [h, map_one] at this
      exact congrArg Subtype.val this.symm)
    have h8 := inner_rank_ge_eight ρ₀ h2 hKprime hoddK hprK hp5K hρ hg2 hg1
    have e1 : ρ₀ g = binaryLin t := by simp [ρ₀, hgt]
    rw [e1] at h8
    omega
  have hcard : ∀ T : Subgroup (MulAut W), T ≤ B → T ≤ Lb → Nat.card T ≤ 4 := by
    intro T hTB hTL
    have hcT : Nat.card (T.subgroupOf Lb) ≤ 4 := by
      refine card_le_of_lifts D.φ (fun g hg h => ?_) hkerodd 4
        (fun T' hT' => card_le_four_SL3 h2 T' hT') (T.subgroupOf Lb)
        (fun x _ => MonoidHom.mem_range.2 (D.surj x)) (fun x hx => ?_) (fun x hx y hy => ?_)
      · exact (Subgroup.mem_center_iff.1 (D.ker_central g hg) h).symm
      · exact Subtype.ext (hB2' _ (hTB hx))
      · exact Subtype.ext (hB2.1 _ (hTB hx) _ (hTB hy))
    have : Nat.card (T.subgroupOf Lb) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
    omega
  have hout : ∀ a ∈ B, a ∉ Lb →
      3 ≤ Module.finrank (ZMod 2) (LinearMap.range (sub1 (binaryLin a))) := by
    intro a haB haL
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a haB) (hB2' a haB) with h | ⟨A, hA, hβ⟩
    · exact absurd h haL
    · have h4 := outer_rank2 D h2 hKprime hoddK hprK hp5K hperfSL (hbN a haB) (hB2' a haB) A hA
        hβ
      omega
  have hidx : ∀ a ∈ B, ∀ a' ∈ B, a ∉ Lb → a' ∉ Lb → a * a' ∈ Lb := by
    intro a haB a' ha'B haL ha'L
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a haB) (hB2' a haB) with h | ⟨A, -, hβ⟩
    · exact absurd h haL
    rcases D.dichotomy h2 hσ hperfSL hW hirr.2 hodd (hbN a' ha'B) (hB2' a' ha'B) with
      h' | ⟨A', -, hβ'⟩
    · exact absurd h' ha'L
    have hsq : a * a' * (a * a') = 1 := by
      calc a * a' * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [hB2.1 a' ha'B a haB]
        _ = (a * a) * (a' * a') := by group
        _ = 1 := by rw [hB2' a haB, hB2' a' ha'B, one_mul]
    exact D.mul_mem_of_dual hperfSL hW hirr.2 hodd (hbN a haB) (hbN a' ha'B) hβ hβ' hsq
  by_contra hne
  push Not at hne
  let F : Submodule (ZMod 2) (Additive W) :=
    { carrier := {x | ∀ a ∈ B, binaryLin a x = x}
      add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
      zero_mem' := fun a _ => map_zero _
      smul_mem' := fun c x hx a ha => by rw [map_smul, hx a ha] }
  have hfix : Nat.card F = Nat.card (fixV B) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨Additive.toMul x.1, fun a ha => congrArg Additive.toMul (x.2 a ha)⟩
        invFun := fun w => ⟨Additive.ofMul w.1, fun a ha => congrArg Additive.ofMul (w.2 a ha)⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun w => Subtype.ext rfl }
  have hpgrp : IsPGroup 2 B := fun a => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hB2.2 a a.2)⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hpgrp
  have hcardE : Nat.card (Additive W) = Nat.card W := Nat.card_congr Additive.toMul
  have hoff : Module.finrank (ZMod 2) (Additive W) - Module.finrank (ZMod 2) F ≤
      2 * Nat.log 2 (Nat.card B) := by
    refine finrank_sub_le_two_log_of_card_le F hk ?_
    rw [hcardE, hfix]
    exact hne
  exact no_offender2_of_ranks binaryLin Lb B hB1 F (fun a ha x hx => hx a ha) hin hcard hout hidx
    hoff

end CFSG.Quasithin.B45Exc
