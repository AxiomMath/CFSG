module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4Weyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4Line
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4Plane
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93TorusLift
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93AC1
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TMain
public import CFSG.RankThree.GF2n.Stroth80.HeringSec97F3D

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.ComponentClassification
open scoped Matrix MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem not_isPGroup_two_sl2 (hK : 8 ≤ Nat.card K) :
    ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK' : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hf2 : 2 ≤ (f : ℕ) := by
    by_contra h
    have : (f : ℕ) ≤ 1 := by omega
    have : 2 ^ (f : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  exact not_isPGroup_two_of_isL2 hf2
    (uc22p22d_isL2_of_statedSL hf2 hK' (specialLinearGroupEquivStatedSL 2 K))

theorem pCore_sl2_eq_bot (hK : 8 ≤ Nat.card K) :
    CFSG.pCore 2 (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := K) (by omega)
  exact eq_bot_of_normal_isPGroup_of_simple (not_isPGroup_two_sl2 hK)
    (CFSG.pCore_normal (p := 2)) CFSG.pCore_isPGroup

theorem not_isPGroup_two_of_isQuasisimple_bar2 {G : Type*} [Group G]
    (hq : CFSG.IsQuasisimple (G ⧸ CFSG.pCore 2 G)) : ¬ IsPGroup 2 G := by
  intro h2
  have htop : CFSG.pCore 2 G = ⊤ :=
    le_antisymm le_top (le_sSup ⟨inferInstance, h2.to_subgroup ⊤⟩)
  have hsub : ∀ u v : G ⧸ CFSG.pCore 2 G, u = v := by
    intro u v
    induction u using QuotientGroup.induction_on with | H x => ?_
    induction v using QuotientGroup.induction_on with | H y => ?_
    rw [QuotientGroup.eq, htop]
    exact Subgroup.mem_top _
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  rw [hsub x y]

theorem nonempty_bar2_sl2_of_psi (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H))
    (ψ : ↥H →* Matrix.SpecialLinearGroup (Fin 2) K) (hψ : ψ.range = ⊥ ∨ ψ.range = ⊤)
    (hk : IsPGroup 2 ψ.ker) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  rcases hψ with h | h
  · exfalso
    apply not_isPGroup_two_of_isQuasisimple_bar2 hq
    have hker : ψ.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [MonoidHom.mem_ker]
      have : ψ x ∈ ψ.range := ⟨x, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [hker] at hk
    exact IsPGroup.of_equiv hk Subgroup.topEquiv
  · have hsurj : Function.Surjective ψ := MonoidHom.range_eq_top.mp h
    obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker ψ hsurj hk
    exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq (pCore_sl2_eq_bot hK)).trans
      QuotientGroup.quotientBot)⟩

theorem nonempty_bar2_map_conj {G : Type*} [Group G] (H : Subgroup G) (n : G) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* (↥(H.map (MulAut.conj n).toMonoidHom) ⧸
      CFSG.pCore 2 ↥(H.map (MulAut.conj n).toMonoidHom))) := by
  set e := H.equivMapOfInjective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective
  refine CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker e.toMonoidHom
    e.surjective ?_
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
  exact IsPGroup.of_bot

omit [Finite K] [CharP K 2] in
theorem nonempty_bar2_sl2_of_conj {n : StatedSp 2 K}
    {π : Equiv.Perm (Fin 2 ⊕ Fin 2)} (hn : IsPermSp n π) (hπ : π ∈ signedPermGroup 2)
    {H : Subgroup (StatedSp 2 K)} (hHH : ⁅H, H⁆ = H)
    (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H))
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    {P : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → Prop} (hP : ∀ h ∈ H, ∀ k j, P k j → (spMat h) k j = 0)
    (hcase : ∀ H' : Subgroup (StatedSp 2 K), ⁅H', H'⁆ = H' →
      CFSG.IsQuasisimple (↥H' ⧸ CFSG.pCore 2 ↥H') →
      torus 2 K ≤ Subgroup.normalizer (H' : Set (StatedSp 2 K)) →
      (∀ h ∈ H', ∀ k j, P (π⁻¹ k) (π⁻¹ j) → (spMat h) k j = 0) →
      Nonempty ((↥H' ⧸ CFSG.pCore 2 ↥H') ≃* SL(2, K))) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* SL(2, K)) := by
  obtain ⟨e⟩ := nonempty_bar2_map_conj H n
  obtain ⟨f⟩ := hcase _ (by rw [← Subgroup.map_commutator, hHH]) (hq.of_mulEquiv e.symm)
    (hn.torus_le_normalizer_map hπ hT) (hn.entry_map hP)
  exact ⟨e.trans f⟩



theorem not_isQuasisimple_bar2_lam_sup (hK : 8 ≤ Nat.card K) :
    ¬ CFSG.IsQuasisimple (↥((lam 0 : SL(2, K) →* StatedSp 2 K).range ⊔
      (lam 1 : SL(2, K) →* StatedSp 2 K).range) ⧸ CFSG.pCore 2 ↥((lam 0 : SL(2, K) →*
        StatedSp 2 K).range ⊔ (lam 1 : SL(2, K) →* StatedSp 2 K).range)) := by
  intro hq
  obtain ⟨e⟩ := nonempty_lam_sup_equiv_prod (K := K)
  have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := K) (by omega)
  have hO : CFSG.pCore 2 (SL(2, K) × SL(2, K)) = ⊥ :=
    eq_bot_of_normal_isPGroup_prod (not_isPGroup_two_sl2 hK) (not_isPGroup_two_sl2 hK)
      (CFSG.pCore_normal (p := 2)) CFSG.pCore_isPGroup
  obtain ⟨f⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (p := 2)
    e.toMonoidHom e.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact IsPGroup.of_bot)
  have e2 := f.trans ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)
  exact not_isQuasisimple_prod CFSG.CGT.Timmesfeld75.center_sl2_eq_bot
    CFSG.CGT.Timmesfeld75.center_sl2_eq_bot
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (hq.of_mulEquiv e2.symm)))

theorem nonempty_bar2_sl2_of_equiv (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H)) (e : ↥H ≃* SL(2, K)) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* SL(2, K)) :=
  nonempty_bar2_sl2_of_psi hK hq e.toMonoidHom (Or.inr (MonoidHom.range_eq_top.mpr e.surjective))
    (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]; exact IsPGroup.of_bot)

theorem nonempty_bar2_sl2_of_stab_line_at (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H))
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K))) (x : Fin 2 ⊕ Fin 2)
    (hx : ∀ h ∈ H, ∀ k, k ≠ x → (spMat h) k x = 0) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* SL(2, K)) := by
  obtain ⟨n, π, hn, hπ, hπx⟩ := exists_isPermSp_apply_eq_inl_zero (K := K) x
  have hπx' : π⁻¹ (Sum.inl 0) = x := by
    rw [← hπx]
    simp
  refine nonempty_bar2_sl2_of_conj hn hπ hHH hq hT (P := fun k j => j = x ∧ k ≠ x)
    (fun h hh k j hkj => by obtain ⟨rfl, hk⟩ := hkj; exact hx h hh k hk)
    fun H' hHH' hq' hT' hP' => ?_
  obtain ⟨ψ, hψ, hk⟩ := exists_sl2_of_stab_line hK hHH' hT' fun h hh i hi =>
    hP' h hh i (Sum.inl 0) ⟨hπx', fun h' => hi (by rw [← hπx, ← h']; simp)⟩
  exact nonempty_bar2_sl2_of_psi hK hq' ψ hψ hk

theorem nonempty_bar2_sl2_of_stab_lag (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H))
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hW : ∀ h ∈ H, ∀ i j : Fin 2, (spMat h) (Sum.inr i) (Sum.inl j) = 0) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* SL(2, K)) := by
  obtain ⟨ψ, hψ, hk⟩ := exists_sl2_of_stab_lagrangian hK hHH hT hW
  exact nonempty_bar2_sl2_of_psi hK hq ψ hψ hk

theorem nonempty_bar2_sl2_of_stab_nondeg (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H))
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    (hW : ∀ h ∈ H, ∀ i j : Fin 2 ⊕ Fin 2, (i = Sum.inl 1 ∨ i = Sum.inr 1) →
      (j = Sum.inl 0 ∨ j = Sum.inr 0) → (spMat h) i j = 0) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* SL(2, K)) := by
  rcases eq_of_stab_plane hK hHH hT hW with h | h | h | h <;> subst h
  · exact absurd IsPGroup.of_bot (not_isPGroup_two_of_isQuasisimple_bar2 hq)
  · exact nonempty_bar2_sl2_of_equiv hK hq (Burgoyne.Sp.longRootEquiv K 0)
  · exact nonempty_bar2_sl2_of_equiv hK hq (Burgoyne.Sp.longRootEquiv K 1)
  · exact absurd hq (not_isQuasisimple_bar2_lam_sup hK)

theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

theorem sum_fin_two_cases (x : Fin 2 ⊕ Fin 2) :
    x = Sum.inl 0 ∨ x = Sum.inl 1 ∨ x = Sum.inr 0 ∨ x = Sum.inr 1 := by
  rcases x with x | x <;> rcases fin_two_cases x with rfl | rfl <;> simp

theorem nonempty_bar2_sl2_of_pattern_inl0 (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H))
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    {s : Fin 2 ⊕ Fin 2 → Prop} (hs : ∀ h ∈ H, ∀ k j, s j ∧ ¬ s k → (spMat h) k j = 0)
    (h0 : s (Sum.inl 0)) (hne : ∃ k, ¬ s k) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* SL(2, K)) := by
  by_cases h1 : s (Sum.inr 0) <;> by_cases h2 : s (Sum.inl 1) <;> by_cases h3 : s (Sum.inr 1)
  · obtain ⟨k, hk⟩ := hne
    rcases sum_fin_two_cases k with rfl | rfl | rfl | rfl <;> contradiction
  · refine nonempty_bar2_sl2_of_stab_line_at hK hHH hq hT _ (line_of_triple (y := Sum.inr 1) ?_)
    intro h hh j hj
    refine hs h hh _ _ ⟨?_, h3⟩
    rcases sum_fin_two_cases j with rfl | rfl | rfl | rfl <;>
      first | assumption | exact absurd rfl hj
  · refine nonempty_bar2_sl2_of_stab_line_at hK hHH hq hT _ (line_of_triple (y := Sum.inl 1) ?_)
    intro h hh j hj
    refine hs h hh _ _ ⟨?_, h2⟩
    rcases sum_fin_two_cases j with rfl | rfl | rfl | rfl <;>
      first | assumption | exact absurd rfl hj
  · refine nonempty_bar2_sl2_of_stab_nondeg hK hHH hq hT fun h hh i j hi hj => hs h hh _ _ ⟨?_, ?_⟩
    · rcases hj with rfl | rfl <;> assumption
    · rcases hi with rfl | rfl <;> assumption
  · refine nonempty_bar2_sl2_of_stab_line_at hK hHH hq hT _ (line_of_triple (y := Sum.inr 0) ?_)
    intro h hh j hj
    refine hs h hh _ _ ⟨?_, h1⟩
    rcases sum_fin_two_cases j with rfl | rfl | rfl | rfl <;>
      first | assumption | exact absurd rfl hj
  · refine nonempty_bar2_sl2_of_stab_lag hK hHH hq hT fun h hh i j => hs h hh _ _ ⟨?_, ?_⟩
    · rcases fin_two_cases j with rfl | rfl <;> assumption
    · rcases fin_two_cases i with rfl | rfl <;> assumption
  · refine nonempty_bar2_sl2_of_conj (isPermSp_lam_sl2W 1) (mem_signedPermGroup.mpr (by decide))
      hHH hq hT (P := fun k j => s j ∧ ¬ s k) hs fun H' hHH' hq' hT' hP' => ?_
    refine nonempty_bar2_sl2_of_stab_lag hK hHH' hq' hT' fun h hh i j => hP' h hh _ _ ⟨?_, ?_⟩
    · rcases fin_two_cases j with rfl | rfl
      · rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact h0
      · rw [Equiv.swap_inv, Equiv.swap_apply_left]
        exact h3
    · rcases fin_two_cases i with rfl | rfl
      · rw [Equiv.swap_inv, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
        exact h1
      · rw [Equiv.swap_inv, Equiv.swap_apply_right]
        exact h2
  · refine nonempty_bar2_sl2_of_stab_line_at hK hHH hq hT (Sum.inl 0) fun h hh k hk =>
      hs h hh _ _ ⟨h0, ?_⟩
    rcases sum_fin_two_cases k with rfl | rfl | rfl | rfl <;>
      first | assumption | exact absurd rfl hk

theorem nonempty_bar2_sl2_of_pattern (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H))
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    {s : Fin 2 ⊕ Fin 2 → Prop} (hs : ∀ h ∈ H, ∀ k j, s j ∧ ¬ s k → (spMat h) k j = 0)
    (hex : ∃ j, s j) (hne : ∃ k, ¬ s k) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* SL(2, K)) := by
  obtain ⟨x, hx⟩ := hex
  obtain ⟨k₀, hk₀⟩ := hne
  obtain ⟨n, π, hn, hπ, hπx⟩ := exists_isPermSp_apply_eq_inl_zero (K := K) x
  refine nonempty_bar2_sl2_of_conj hn hπ hHH hq hT (P := fun k j => s j ∧ ¬ s k) hs
    fun H' hHH' hq' hT' hP' => ?_
  refine nonempty_bar2_sl2_of_pattern_inl0 hK hHH' hq' hT' (s := fun j => s (π⁻¹ j)) hP' ?_
    ⟨π k₀, ?_⟩
  · show s (π⁻¹ (Sum.inl 0))
    rw [← hπx]
    simpa using hx
  · show ¬ s (π⁻¹ (π k₀))
    simpa using hk₀

theorem nonempty_bar2_sl2_of_reducible (hK : 8 ≤ Nat.card K) {H : Subgroup (StatedSp 2 K)}
    (hHH : ⁅H, H⁆ = H) (hq : CFSG.IsQuasisimple (↥H ⧸ CFSG.pCore 2 ↥H))
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)))
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hWt : ∀ d ∈ torus 2 K, ∀ w ∈ W, (spMat d) *ᵥ w ∈ W)
    (hWH : ∀ h ∈ H, ∀ w ∈ W, (spMat h) *ᵥ w ∈ W) (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) :
    Nonempty ((↥H ⧸ CFSG.pCore 2 ↥H) ≃* SL(2, K)) := by
  refine nonempty_bar2_sl2_of_pattern hK hHH hq hT (s := fun j => Pi.single j 1 ∈ W)
    (fun h hh k j hkj => entry_eq_zero_of_invariant hK hWt (hWH h hh) hkj.1 hkj.2) ?_ ?_
  · obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
    exact ⟨j, single_mem_of_torus_invariant hK hWt hw hj⟩
  · by_contra hall
    have hall' : ∀ k, Pi.single k (1 : K) ∈ W := fun k => by_contra fun hk => hall ⟨k, hk⟩
    apply hW1
    rw [eq_top_iff, ← (Pi.basisFun K (Fin 2 ⊕ Fin 2)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simpa using hall' j

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
