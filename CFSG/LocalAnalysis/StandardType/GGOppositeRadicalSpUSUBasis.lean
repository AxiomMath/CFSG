module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalSpUSU

public section

namespace CFSG.StandardType

namespace GGOppRadSpU

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary GGOppRad

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

variable (F f) in
@[expose] def GGSUWittChainAt (n : ℕ) (hF : Nat.card F = (2 ^ f) ^ 2) : Prop :=
  ∀ (m : ℕ) (X : ℕ → Submodule F (Fin n → F)), Monotone X →
    (∀ i ≤ m, Module.finrank F (X i) = i) →
    (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).IsTotallyIsotropic
      (X m) →
    ∃ g : SU (unitaryInvolution F 2 f) n, ∀ i ≤ m,
      X i = (stdFlag (fun a : Fin n => a.val) i).map (natRep (SU (unitaryInvolution F 2 f) n) g)

omit [Finite F] [CharP F 2] in
theorem stdFlag_congr {ι : Type*} {ℓ ℓ' : ι → ℕ} {k k' : ℕ}
    (h : ∀ a, ℓ a < k ↔ ℓ' a < k') : stdFlag (K := F) ℓ k = stdFlag ℓ' k' := by
  ext v
  simp only [mem_stdFlag]
  constructor
  · intro hv a ha
    exact hv a (not_lt.mp fun h' => not_lt.mpr ha ((h a).mp h'))
  · intro hv a ha
    exact hv a (not_lt.mp fun h' => not_lt.mpr ha ((h a).mpr h'))

theorem perp_map_natRep_su (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    (g : SU (unitaryInvolution F 2 f) n) (Y : Submodule F (Fin n → F)) :
    (suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).perp
        (Y.map (natRep (SU (unitaryInvolution F 2 f) n) g)) =
      ((suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n).perp Y).map
        (natRep (SU (unitaryInvolution F 2 f) n) g) := by
  set B := suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact (isIsometric_natRep_SU _ (unitaryInvolution_involutive hF) n).apply_mem_perp g ha
  · have h1 := B.finrank_perp (Y.map (natRep (SU (unitaryInvolution F 2 f) n) g))
    have h2 := B.finrank_perp Y
    have e1 : Module.finrank F (Y.map (natRep (SU (unitaryInvolution F 2 f) n) g)) =
        Module.finrank F Y :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
        (natRep_injective_apply_su g) _)).symm
    have e2 : Module.finrank F ((B.perp Y).map (natRep (SU (unitaryInvolution F 2 f) n) g)) =
        Module.finrank F (B.perp Y) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
        (natRep_injective_apply_su g) _)).symm
    omega

theorem ggSUIsoFlagStdAt_of_wittChain (hF : Nat.card F = (2 ^ f) ^ 2) {n : ℕ}
    (hWitt : GGSUWittChainAt F f n hF) : GGSUIsoFlagStdAt F f n hF := by
  classical
  intro R
  set d := Module.finrank F (Fin n → F) with hd
  set ρ := natRep (SU (unitaryInvolution F 2 f) n)
  set B := suForm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) n with hB
  set W := isoSeq B ρ R with hW
  have hWmono : Monotone W := isoSeq_mono B ρ R
  have hWle : ∀ j, W j ≤ W d := fun j => by
    rcases le_total j d with h | h
    · exact hWmono h
    · exact (isoSeq_eq_of_le B ρ R h).le
  obtain ⟨X, hX0, hXmono, hXrank, hXtop, hXW⟩ :=
    exists_finrank_chain_forall_exists_eq hWmono hWle ⟨d, rfl⟩
  set m := Module.finrank F (W d)
  have hWiso : B.IsTotallyIsotropic (W d) := isoSeq_isTotallyIsotropic B ρ R d
  have hdn : d = n := by rw [hd, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h2m : 2 * m ≤ n := by
    have h1 := B.finrank_perp (W d)
    have h2 := Submodule.finrank_mono hWiso
    omega
  obtain ⟨g, hg⟩ := hWitt m X hXmono (fun i hi => hXrank i hi) (by rw [hXtop m le_rfl]; exact hWiso)
  set D : ℕ → ℕ := fun k => Module.finrank F (W k) with hD
  have hDmono : Monotone D := fun _ _ h => Submodule.finrank_mono (hWmono h)
  have hDm : ∀ k, D k ≤ m := fun k => Submodule.finrank_mono (hWle k)
  have hD0 : D 0 = 0 := by
    change Module.finrank F (isoSeq B ρ R 0) = 0
    rw [isoSeq_zero, finrank_bot]
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
  have hex : ∀ a : Fin n, ∃ k, a.val < D (k + 1) ∨ d ≤ k := fun _ => ⟨d, Or.inr le_rfl⟩
  have hℓd : ∀ a, Nat.find (hex a) ≤ d := fun a => Nat.find_min' (hex a) (Or.inr le_rfl)
  set ℓ : Fin n → ℕ := fun a => if a.val < (Fin.rev a).val then Nat.find (hex a)
    else if a = Fin.rev a then d else 2 * d - Nat.find (hex (Fin.rev a)) with hℓ
  have hℓsu : IsSULevel (2 * d) ℓ := by
    intro a
    have h1 := hℓd a
    have h2 := hℓd (Fin.rev a)
    have hv := Fin.val_rev a
    have hv' := Fin.val_rev (Fin.rev a)
    simp only [hℓ, Fin.rev_rev]
    by_cases ha : a.val < (Fin.rev a).val
    · have hne : ¬ (Fin.rev a).val < a.val := by omega
      have hne' : Fin.rev a ≠ a := fun h => by rw [h] at ha; exact lt_irrefl _ ha
      rw [ite_eq_left ha, ite_eq_right hne, ite_eq_right hne']
      omega
    · by_cases hb : a = Fin.rev a
      · have hc : ¬ (Fin.rev a).val < a.val := by
          rw [← hb]
          exact lt_irrefl _
        rw [ite_eq_right ha, ite_eq_left hb, ite_eq_right hc, ite_eq_left hb.symm]
        omega
      · have hlt : (Fin.rev a).val < a.val := by
          rcases lt_trichotomy a.val (Fin.rev a).val with h | h | h
          · exact absurd h ha
          · exact absurd (Fin.ext h) hb
          · exact h
        rw [ite_eq_right ha, ite_eq_right hb, ite_eq_left hlt]
        omega
  have key : ∀ a k, k ≤ d → (ℓ a < k ↔ a.val < D k) := by
    intro a k hk
    have hv := Fin.val_rev a
    by_cases ha : a.val < (Fin.rev a).val
    · simp only [hℓ, ha, ↓reduceIte]
      constructor
      · intro h
        rcases Nat.find_spec (hex a) with hs | hs
        · exact lt_of_lt_of_le hs (hDmono (by omega))
        · omega
      · intro h
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [hD0] at h
          exact Nat.not_lt_zero _ h
        have : Nat.find (hex a) ≤ k - 1 :=
          Nat.find_min' (hex a) (Or.inl (by rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]))
        omega
    · have hge : d ≤ ℓ a := by
        simp only [hℓ, ha, ↓reduceIte]
        split_ifs
        · exact le_rfl
        · have := hℓd (Fin.rev a)
          omega
      have hDk := hDm k
      constructor
      · intro h
        omega
      · intro h
        omega
  have hiso : ∀ k ≤ d, W k = (stdFlag ℓ k).map (ρ g) := by
    intro k hk
    rw [hWX k, hg (D k) (hDm k)]
    congr 1
    exact stdFlag_congr fun a => (key a k hk).symm
  refine ⟨g, ℓ, hℓsu, funext fun k => ?_⟩
  have hsd := isSelfDual_stdFlag_su (unitaryInvolution F 2 f) (unitaryInvolution_involutive hF) hℓsu
  change isoFlag B ρ R k = (stdFlag ℓ k).map (ρ g)
  by_cases hk1 : k ≤ d
  · rw [isoFlag, ite_eq_left hk1]
    exact hiso k hk1
  by_cases hk2 : k ≤ 2 * d + 1
  · rw [isoFlag, ite_eq_right hk1, ite_eq_left hk2, ← hW, ← hd, hiso _ (by omega),
      perp_map_natRep_su hF, hsd.perp _ (by omega)]
    congr 2
    omega
  · rw [isoFlag, ite_eq_right hk1, ite_eq_right hk2, hsd.top k (by omega), Submodule.map_top,
      LinearMap.range_eq_top.mpr]
    intro v
    exact ⟨ρ g⁻¹ v, rep_apply_rep_inv ρ g v⟩

end GGOppRadSpU

end CFSG.StandardType
