module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthStatements
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCent

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem otm_aniso {K : Type} [Field K] [CharP K 2] [Finite K] (hK : Nat.card K = 2)
    (p q r s x y : K) (hdet : p * s - q * r = 1) :
    (p * x + q * y) * (r * x + s * y) + ((p * x + q * y) ^ 2 + (r * x + s * y) ^ 2) =
      x * y + (x ^ 2 + y ^ 2) := by
  have hxx : ∀ z : K, z * z = z := by
    intro z
    rcases SpBlocks.eq_zero_or_eq_one hK z with h | h <;> rw [h] <;> simp
  rcases SpBlocks.eq_zero_or_eq_one hK p with hp | hp
  · have hqr : q * r = 1 := by
      rw [hp, zero_mul, zero_sub] at hdet
      rwa [CharTwo.neg_eq (q * r)] at hdet
    have hq : q = 1 := by
      rcases SpBlocks.eq_zero_or_eq_one hK q with h | h
      · rw [h, zero_mul] at hqr
        exact absurd hqr (by simp)
      · exact h
    have hr : r = 1 := by
      rcases SpBlocks.eq_zero_or_eq_one hK r with h | h
      · rw [h, mul_zero] at hqr
        exact absurd hqr (by simp)
      · exact h
    subst hp; subst hq; subst hr
    rcases SpBlocks.eq_zero_or_eq_one hK s with hs | hs <;>
    rw [hs] <;>
    rcases SpBlocks.eq_zero_or_eq_one hK x with hx | hx <;>
    rcases SpBlocks.eq_zero_or_eq_one hK y with hy | hy <;>
    rw [hx, hy] <;> simp [hxx, CharTwo.add_self_eq_zero]
  · have hs : s = 1 + q * r := by
      rw [hp, one_mul] at hdet
      linear_combination hdet
    subst hp; subst hs
    rcases SpBlocks.eq_zero_or_eq_one hK q with hq | hq <;>
    rcases SpBlocks.eq_zero_or_eq_one hK r with hr | hr <;>
    rw [hq, hr] <;>
    rcases SpBlocks.eq_zero_or_eq_one hK x with hx | hx <;>
    rcases SpBlocks.eq_zero_or_eq_one hK y with hy | hy <;>
    rw [hx, hy] <;> simp [hxx, CharTwo.add_self_eq_zero]

private theorem otm_planeMat_apply_of_ne {K : Type} [Field K] {n : ℕ}
    (N : Fin n → Matrix (Fin 2) (Fin 2) K) {a b : Fin n ⊕ Fin n}
    (h : WitSpNs.plane a ≠ WitSpNs.plane b) : WitSpNs.planeMat N a b = 0 := by
  rw [WitSpNs.planeMat_apply, if_neg h]

private theorem otm_planeMat_mulVec_inl {K : Type} [Field K] {n : ℕ}
    (N : Fin n → Matrix (Fin 2) (Fin 2) K) (v : (Fin n ⊕ Fin n) → K) (j : Fin n) :
    (WitSpNs.planeMat N *ᵥ v) (Sum.inl j) =
      N j 0 0 * v (Sum.inl j) + N j 0 1 * v (Sum.inr j) := by
  rw [Matrix.mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Sum.inl j))]
  have h2 : ∑ b ∈ (Finset.univ : Finset (Fin n ⊕ Fin n)).erase (Sum.inl j),
      WitSpNs.planeMat N (Sum.inl j) b * v b =
      WitSpNs.planeMat N (Sum.inl j) (Sum.inr j) * v (Sum.inr j) := by
    refine Finset.sum_eq_single (Sum.inr j) ?_ ?_
    · intro b hb hbne
      have hb0 : b ≠ Sum.inl j := (Finset.mem_erase.mp hb).1
      have hzero : WitSpNs.planeMat N (Sum.inl j) b = 0 := by
        refine otm_planeMat_apply_of_ne N ?_
        rcases b with i | i
        · simp only [WitSpNs.plane_inl]
          exact fun h => hb0 (by rw [h])
        · simp only [WitSpNs.plane_inl, WitSpNs.plane_inr]
          exact fun h => hbne (by rw [h])
      rw [hzero, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩) hmem
  rw [h2]
  have e0 : (Sum.inl j : Fin n ⊕ Fin n) = WitSpNs.coord 0 j := rfl
  have e1 : (Sum.inr j : Fin n ⊕ Fin n) = WitSpNs.coord 1 j := rfl
  rw [e0, e1, WitSpNs.planeMat_coord, WitSpNs.planeMat_coord]

private theorem otm_planeMat_mulVec_inr {K : Type} [Field K] {n : ℕ}
    (N : Fin n → Matrix (Fin 2) (Fin 2) K) (v : (Fin n ⊕ Fin n) → K) (j : Fin n) :
    (WitSpNs.planeMat N *ᵥ v) (Sum.inr j) =
      N j 1 0 * v (Sum.inl j) + N j 1 1 * v (Sum.inr j) := by
  rw [Matrix.mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Sum.inl j))]
  have h2 : ∑ b ∈ (Finset.univ : Finset (Fin n ⊕ Fin n)).erase (Sum.inl j),
      WitSpNs.planeMat N (Sum.inr j) b * v b =
      WitSpNs.planeMat N (Sum.inr j) (Sum.inr j) * v (Sum.inr j) := by
    refine Finset.sum_eq_single (Sum.inr j) ?_ ?_
    · intro b hb hbne
      have hb0 : b ≠ Sum.inl j := (Finset.mem_erase.mp hb).1
      have hzero : WitSpNs.planeMat N (Sum.inr j) b = 0 := by
        refine otm_planeMat_apply_of_ne N ?_
        rcases b with i | i
        · simp only [WitSpNs.plane_inr, WitSpNs.plane_inl]
          exact fun h => hb0 (by rw [h])
        · simp only [WitSpNs.plane_inr]
          exact fun h => hbne (by rw [h])
      rw [hzero, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_erase.mpr ⟨by simp, Finset.mem_univ _⟩) hmem
  rw [h2]
  have e0 : (Sum.inl j : Fin n ⊕ Fin n) = WitSpNs.coord 0 j := rfl
  have e1 : (Sum.inr j : Fin n ⊕ Fin n) = WitSpNs.coord 1 j := rfl
  rw [e0, e1, WitSpNs.planeMat_coord, WitSpNs.planeMat_coord]

private theorem otm_planeQ_planeMat {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {t : ℕ} {δ : Fin 2} (i₀ : Fin (t + δ.val))
    (hi₀ : (i₀ : ℕ) < t) (a : SpecialLinearGroup (Fin 2) K)
    (v : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K) :
    planeQ (K := K) t δ
        (WitSpNs.planeMat (fun j => if j = i₀ then (a : Matrix (Fin 2) (Fin 2) K) else 1) *ᵥ v) =
      planeQ (K := K) t δ v := by
  have h0 := otm_planeMat_mulVec_inl
    (fun j => if j = i₀ then (a : Matrix (Fin 2) (Fin 2) K) else 1) v
  have h1 := otm_planeMat_mulVec_inr
    (fun j => if j = i₀ then (a : Matrix (Fin 2) (Fin 2) K) else 1) v
  have hdet : (a : Matrix (Fin 2) (Fin 2) K) 0 0 * (a : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (a : Matrix (Fin 2) (Fin 2) K) 0 1 * (a : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (A := a)
    rwa [Matrix.det_fin_two] at h
  simp only [planeQ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h0 i, h1 i]
  by_cases hi : i = i₀
  · rw [hi, if_pos rfl]
    split_ifs
    exact otm_aniso hK _ _ _ _ _ _ hdet
  · rw [if_neg hi]
    simp

private theorem otm_lam_mem_orthGroup {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {t : ℕ} {δ : Fin 2} (i : Fin (t + δ.val)) (hi : (i : ℕ) < t)
    (a : SpecialLinearGroup (Fin 2) K) :
    ((lam i a : ↥(Open.StatedSp (t + δ.val) K)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
      LargeEvenOrthGroup (planeQ (K := K) t δ) := by
  rw [largeEvenOrthGroup_def]
  refine Subgroup.subset_closure ?_
  intro v
  rw [SpBlocks.coe_lam_eq_planeMat]
  exact otm_planeQ_planeMat hK i hi a v

private theorem otm_sl2W_commutator {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {h : SpecialLinearGroup (Fin 2) K} (h3 : h ^ 3 = 1) :
    h = ⁅(sl2W : SpecialLinearGroup (Fin 2) K), h⁆ := by
  by_cases h1 : h = 1
  · subst h1
    simp [commutatorElement_def]
  · rw [commutatorElement_def, SpBlocks.sl2W_conj_eq_inv hK h3 h1]
    calc h = h⁻¹ * h⁻¹ * h ^ 3 := by group
      _ = h⁻¹ * h⁻¹ := by rw [h3, mul_one]

private theorem otm_lam_commutator_mem {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {t : ℕ} {δ : Fin 2} (i : Fin (t + δ.val)) (hi : (i : ℕ) < t)
    (a : SpecialLinearGroup (Fin 2) K) (ha : a ^ 3 = 1) :
    ((lam i a : ↥(Open.StatedSp (t + δ.val) K)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈ omegaQ (K := K) t δ := by
  have hcomm : a = ⁅(sl2W : SpecialLinearGroup (Fin 2) K), a⁆ := otm_sl2W_commutator hK ha
  have hmap : ((lam i a : ↥(Open.StatedSp (t + δ.val) K)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      ((⁅lam i (sl2W : SpecialLinearGroup (Fin 2) K), lam i a⁆ :
          ↥(Open.StatedSp (t + δ.val) K)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
    conv_lhs => rw [hcomm]
    rw [map_commutatorElement]
  have hsub : ((⁅lam i (sl2W : SpecialLinearGroup (Fin 2) K), lam i a⁆ :
        ↥(Open.StatedSp (t + δ.val) K)) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      ⁅((lam i (sl2W : SpecialLinearGroup (Fin 2) K) : ↥(Open.StatedSp (t + δ.val) K)) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K),
        ((lam i a : ↥(Open.StatedSp (t + δ.val) K)) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)⁆ :=
    map_commutatorElement (Open.StatedSp (t + δ.val) K).subtype (lam i sl2W) (lam i a)
  rw [hmap, hsub]
  exact Subgroup.commutator_mem_commutator (otm_lam_mem_orthGroup hK i hi _)
    (otm_lam_mem_orthGroup hK i hi a)

theorem orthTauMemOmega_holds : OrthTauMemOmega := by
  intro K _ _ _ ζ t δ hK u
  let f : Fin (t + δ.val) → Multiplicative (ZMod 3) :=
    fun i => Multiplicative.ofAdd (liftV t δ u i)
  have hmem : f ∈ (omegaQ (K := K) t δ).comap
      ((Open.StatedSp (t + δ.val) K).subtype.comp (SpJoin.spPlaneTorus (t + δ.val) ζ)) := by
    rw [← Finset.univ_prod_mulSingle f]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [Subgroup.mem_comap]
    change ((SpJoin.spPlaneTorus (t + δ.val) ζ (Pi.mulSingle i (f i)) :
        ↥(Open.StatedSp (t + δ.val) K)) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ∈
      omegaQ (K := K) t δ
    rw [SpJoin.spPlaneTorus_mulSingle]
    by_cases hi : (i : ℕ) < t
    · refine otm_lam_commutator_mem hK i hi (ζ (f i)) ?_
      simpa [f] using SpBlocks.zeta_pow_three (ζ := ζ) (liftV t δ u i)
    · have hzero : liftV t δ u i = 0 := by
        have hle : t ≤ (i : ℕ) := Nat.le_of_not_lt hi
        have hrange : i ∈ Set.range (Fin.natAdd t : Fin δ.val → Fin (t + δ.val)) := by
          rw [Fin.range_natAdd]
          exact hle
        obtain ⟨j, rfl⟩ := hrange
        simp [liftV]
      simp [f, hzero]
  exact hmem

end CFSG.StandardType.GGQ2Frame.OrthBlocks
