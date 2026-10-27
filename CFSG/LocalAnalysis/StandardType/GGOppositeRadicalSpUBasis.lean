module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUOpp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank GGOppRad
open CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem perp_map_natRep (g : StatedSp n K) (Y : Submodule K (Fin n ⊕ Fin n → K)) :
    (spForm n K).perp (Y.map (natRep (StatedSp n K) g)) =
      ((spForm n K).perp Y).map (natRep (StatedSp n K) g) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact (isIsometric_natRep_statedSp n K).apply_mem_perp g ha
  · have h1 := (spForm n K).finrank_perp (Y.map (natRep (StatedSp n K) g))
    have h2 := (spForm n K).finrank_perp Y
    have e1 : Module.finrank K (Y.map (natRep (StatedSp n K) g)) = Module.finrank K Y :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
        (natRep_injective_apply n K g) _)).symm
    have e2 : Module.finrank K (((spForm n K).perp Y).map (natRep (StatedSp n K) g)) =
        Module.finrank K ((spForm n K).perp Y) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
        (natRep_injective_apply n K g) _)).symm
    omega

theorem pairedSympForm_eq (u v : Fin n ⊕ Fin n → K) :
    pairedSympForm K n u v = (spForm n K).β u v := by
  rw [pairedSympForm_apply, spForm_β, dotProduct_spJ_mulVec]

theorem exists_isoFlag_eq_flagMap (R : Subgroup (StatedSp n K)) :
    ∃ (g : StatedSp n K) (ℓ : Fin n ⊕ Fin n → ℕ),
      IsSpLevel (2 * Module.finrank K (Fin n ⊕ Fin n → K)) ℓ ∧
      isoFlag (spForm n K) (natRep (StatedSp n K)) R =
        GGOppRad.flagMap (natRep (StatedSp n K)) g (stdFlag ℓ) := by
  classical
  set d := Module.finrank K (Fin n ⊕ Fin n → K) with hd
  set ρ := natRep (StatedSp n K)
  set W := isoSeq (spForm n K) ρ R with hW
  have hWmono : Monotone W := isoSeq_mono (spForm n K) ρ R
  have hWle : ∀ j, W j ≤ W d := fun j => by
    rcases le_total j d with h | h
    · exact hWmono h
    · exact (isoSeq_eq_of_le (spForm n K) ρ R h).le
  obtain ⟨X, hX0, hXmono, hXrank, hXtop, hXW⟩ :=
    exists_finrank_chain_forall_exists_eq hWmono hWle ⟨d, rfl⟩
  set m := Module.finrank K (W d)
  have hWiso : SymplecticFlag.IsTotallyIsotropic (pairedSympForm K n) (W d) := by
    intro x hx y hy
    rw [pairedSympForm_eq]
    exact isoSeq_isTotallyIsotropic (spForm n K) ρ R d hy x hx
  have hmn : m ≤ n := SymplecticFlag.finrank_le_of_isTotallyIsotropic
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
    SymplecticFlag.finrank_standard hWiso
  obtain ⟨b, hb, hbX⟩ := SymplecticFlag.exists_symplecticBasis_of_flag
    SymplecticFlag.pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
    SymplecticFlag.finrank_standard hmn X (fun i hi => hXrank i hi)
    (fun i _ => hXmono (Nat.le_succ i))
    (by rw [hXtop m le_rfl]; exact hWiso)
  obtain ⟨g, hg⟩ := SymplecticFlag.exists_statedSp_mulVec_basis
    (b := Pi.basisFun K (Fin n ⊕ Fin n)) SymplecticFlag.toMatrix_pairedSympForm hb
  set D : ℕ → ℕ := fun k => Module.finrank K (W k) with hD
  have hDmono : Monotone D := fun _ _ h => Submodule.finrank_mono (hWmono h)
  have hDm : ∀ k, D k ≤ m := fun k => Submodule.finrank_mono (hWle k)
  have hWX : ∀ k, W k = X (D k) := by
    intro k
    obtain ⟨j, hj⟩ := hXW k
    rcases le_total j m with hjm | hjm
    · rw [hj, hD]
      simp only
      rw [hj, hXrank j hjm]
    · have h1 : W k = W d := by rw [hj, hXtop j hjm]
      rw [hD]
      simp only
      rw [h1, hXtop m le_rfl]
  have hex : ∀ t : Fin n, ∃ k, (t : ℕ) < D (k + 1) ∨ d ≤ k := fun _ => ⟨d, Or.inr le_rfl⟩
  set ℓ : Fin n ⊕ Fin n → ℕ := Sum.elim (fun t => Nat.find (hex t))
    (fun t => 2 * d - Nat.find (hex t)) with hℓ
  have hℓd : ∀ t, Nat.find (hex t) ≤ d := fun t => Nat.find_min' (hex t) (Or.inr le_rfl)
  have hℓsp : IsSpLevel (2 * d) ℓ := fun t => by
    simp only [hℓ, Sum.elim_inl, Sum.elim_inr]
    have := hℓd t
    omega
  have hinl : ∀ t k, k ≤ d → (ℓ (Sum.inl t) < k ↔ (t : ℕ) < D k) := by
    intro t k hk
    simp only [hℓ, Sum.elim_inl]
    constructor
    · intro h
      have hs := Nat.find_spec (hex t)
      rcases hs with hs | hs
      · exact lt_of_lt_of_le hs (hDmono (by omega))
      · omega
    · intro h
      have hD0 : D 0 = 0 := by
        change Module.finrank K (isoSeq (spForm n K) ρ R 0) = 0
        rw [isoSeq_zero, finrank_bot]
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [hD0] at h
        exact Nat.not_lt_zero _ h
      have : Nat.find (hex t) ≤ k - 1 :=
        Nat.find_min' (hex t) (Or.inl (by rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]))
      omega
  have hinr : ∀ t k, k ≤ d → ¬ ℓ (Sum.inr t) < k := by
    intro t k hk
    simp only [hℓ, Sum.elim_inr]
    have := hℓd t
    omega
  have hiso : ∀ k ≤ d, W k = (stdFlag ℓ k).map (ρ g) := by
    intro k hk
    rw [hWX k, hbX (D k) (hDm k), stdFlag_eq_span, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext v
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨⟨Sum.inl t, (hinl t k hk).mpr ht⟩, ?_⟩
      simp only [Function.comp_apply, ρ, natRep_apply]
      have := hg (Sum.inl t)
      rwa [Pi.basisFun_apply] at this
    · rintro ⟨⟨a, ha⟩, rfl⟩
      rcases a with t | t
      · refine ⟨Sum.inl t, ⟨t, (hinl t k hk).mp ha, rfl⟩, ?_⟩
        simp only [Function.comp_apply, ρ, natRep_apply]
        have := hg (Sum.inl t)
        rw [Pi.basisFun_apply] at this
        exact this.symm
      · exact absurd ha (hinr t k hk)
  refine ⟨g, ℓ, hℓsp, funext fun k => ?_⟩
  have hsd := isSelfDual_stdFlag (K := K) hℓsp
  change isoFlag (spForm n K) ρ R k = (stdFlag ℓ k).map (ρ g)
  by_cases hk1 : k ≤ d
  · rw [isoFlag, ite_eq_left hk1]
    exact hiso k hk1
  by_cases hk2 : k ≤ 2 * d + 1
  · rw [isoFlag, ite_eq_right hk1, ite_eq_left hk2, ← hW, ← hd, hiso _ (by omega),
      perp_map_natRep, hsd.perp _ (by omega)]
    congr 2
    omega
  · rw [isoFlag, ite_eq_right hk1, ite_eq_right hk2, hsd.top k (by omega), Submodule.map_top,
      LinearMap.range_eq_top.mpr]
    intro v
    exact ⟨ρ g⁻¹ v, rep_apply_rep_inv ρ g v⟩

end GGOppRadSpU

end CFSG.StandardType
