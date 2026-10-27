module

public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniMaschke
public import CFSG.RankThree.GroupTheory.SteinbergBMTwoCommutatorLift
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG.LocalAnalysis.ComponentInitial

variable {A : Type*} [Group A]

theorem actionCommutator_actionCommutator_of_isPGroup {l : ℕ} (hl : l.Prime) {X : Type*}
    [Group X] [Finite X] [Finite A] [MulDistribMulAction A X] {W : Subgroup X}
    (hWl : IsPGroup l W) (hA : ¬ l ∣ Nat.card A) (hW : ∀ a : A, ∀ x ∈ W, a • x ∈ W) :
    actionCommutator A (actionCommutator A W) = actionCommutator A W := by
  have : CFSG.IsInvariant A X W := ⟨fun a g => ⟨fun hg => hW a g hg, fun hg => by
    have := hW a⁻¹ _ hg
    rwa [inv_smul_smul] at this⟩⟩
  have hfact := (coprime_pgroup_commutator_factorization (A := A) (Q := W) hl hWl hA).2
  have hsub : ∀ (a : A) (x : W), W.subtype (a • x) = a • W.subtype x := fun _ _ => rfl
  have hWtop : (⊤ : Subgroup W).map W.subtype = W := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  rw [← hWtop, ← map_actionCommutator W.subtype hsub, ← map_actionCommutator W.subtype hsub,
    hfact]

theorem actionCommutator_eq_of_fixed_eq_bot {l : ℕ} (hl : l.Prime) {X : Type*} [Group X]
    [Finite X] [Finite A] [MulDistribMulAction A X] {V : Subgroup X} (hVl : IsPGroup l V)
    (hA : ¬ l ∣ Nat.card A) (hV : ∀ a : A, ∀ x ∈ V, a • x ∈ V)
    (hfix : ∀ x ∈ V, (∀ a : A, a • x = x) → x = 1) : actionCommutator A V = V := by
  refine le_antisymm (actionCommutator_le_of_invariant hV) fun x hx => ?_
  have : CFSG.IsInvariant A X V := ⟨fun a g => ⟨fun hg => hV a g hg, fun hg => by
    have := hV a⁻¹ _ hg
    rwa [inv_smul_smul] at this⟩⟩
  obtain ⟨d, hd, c, hc, hdc⟩ :=
    (coprime_pgroup_commutator_factorization (A := A) (Q := V) hl hVl hA).1 ⟨x, hx⟩
  have hc1 : c = 1 := Subtype.ext (hfix _ c.2 fun a => congrArg Subtype.val (hc a))
  rw [hc1, mul_one] at hdc
  have hsub : ∀ (a : A) (y : V), V.subtype (a • y) = a • V.subtype y := fun _ _ => rfl
  have hVtop : (⊤ : Subgroup V).map V.subtype = V := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  rw [← hVtop, ← map_actionCommutator V.subtype hsub]
  exact ⟨d, hd, by rw [← hdc]; rfl⟩

theorem relative_minimal_action_frattini_irreducibility {l : ℕ} (hl : l.Prime) {P : Type*}
    [Group P] [Finite A] [Finite P] [MulDistribMulAction A P] (hP : IsPGroup l P)
    [Nontrivial P] (hA : ¬ l ∣ Nat.card A) (K : Subgroup P) (hKP : K < ⊤)
    (hKinv : ∀ a : A, ∀ x ∈ K, a • x ∈ K) (hPA : actionCommutator A (⊤ : Subgroup P) = ⊤)
    (hU : ∀ U : Subgroup P, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) →
      actionCommutator A U = U → U ≤ K) :
    letI : MulDistribMulAction A (P ⧸ frattini P) :=
      CFSG.quotientMulDistribMulAction (A := A) (G := P) (frattini P)
        (CFSG.isInvariant_of_characteristic (A := A) (G := P) (frattini P))
    (∃ a : A, ∃ v : P ⧸ frattini P, a • v ≠ v) ∧
      (∀ W : Subgroup (P ⧸ frattini P), (∀ a : A, ∀ v ∈ W, a • v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      (∀ U : Subgroup P, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) → U ≤ frattini P) ∧
      K ≤ frattini P := by
  have : Fact l.Prime := ⟨hl⟩
  have : Fact (IsPGroup l P) := ⟨hP⟩
  let : MulDistribMulAction A (P ⧸ frattini P) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := P) (frattini P)
      (CFSG.isInvariant_of_characteristic (A := A) (G := P) (frattini P))
  set Φ := frattini P with hΦdef
  have hΦinv : CFSG.IsInvariant A P Φ :=
    CFSG.isInvariant_of_characteristic (A := A) (G := P) Φ
  let : MulAction.QuotientAction A Φ := CFSG.quotientAction_of_isInvariant (A := A) Φ hΦinv
  set π := QuotientGroup.mk' Φ with hπdef
  have hπA : ∀ (a : A) (x : P), π (a • x) = a • π x := fun a x =>
    (MulAction.Quotient.smul_coe (H := Φ) a x).symm
  have hΦinv' : ∀ a : A, ∀ x ∈ Φ, a • x ∈ Φ := fun a x hx => (hΦinv.invariant a x).1 hx
  have hcop : Nat.Coprime l (Nat.card A) := (Nat.Prime.coprime_iff_not_dvd hl).mpr hA
  have hΦtop : Φ ≠ ⊤ := by
    intro h
    have hbot : (⊥ : Subgroup P) = ⊤ := frattini_nongenerating (by rw [← hΦdef, h, sup_top_eq])
    exact hKP.ne (eq_top_iff.mpr (hbot ▸ bot_le))
  have hFl : IsPGroup l (P ⧸ Φ) := hP.to_quotient Φ
  have hFA : actionCommutator A (⊤ : Subgroup (P ⧸ Φ)) = ⊤ := by
    rw [← map_top_of_surjective π (QuotientGroup.mk'_surjective Φ), ← map_actionCommutator π hπA,
      hPA]
  have hFcomm : IsMulCommutative (P ⧸ Φ) :=
    (CFSG.isElementaryAbelian_quotient_frattini (p := l) (R := P)).toIsMulCommutative
  have hFfix : ∀ v : P ⧸ Φ, (∀ a : A, a • v = v) → v = 1 := by
    have hcomm_eq : CFSG.commutatorAction (A := A) (G := P ⧸ Φ) =
        actionCommutator A (⊤ : Subgroup (P ⧸ Φ)) := by
      unfold CFSG.commutatorAction CFSG.commutatorSubgroup actionCommutator
      congr 1
      ext x
      constructor
      · rintro ⟨a, h, hh, rfl⟩
        exact ⟨h, hh, a, rfl⟩
      · rintro ⟨h, hh, a, rfl⟩
        exact ⟨a, h, hh, rfl⟩
    have hcopF : Nat.Coprime (Nat.card A) (Nat.card (P ⧸ Φ)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hFl
      rw [hk]
      exact Nat.Coprime.pow_right _ hcop.symm
    have hcompl :=
      CFSG.isCompl_fixedPointSubgroup_commutatorAction_of_sup_eq_top_of_coprime_of_isMulCommutative
        (A := A) (G := P ⧸ Φ) (by rw [hcomm_eq, hFA, sup_top_eq]) hcopF hFcomm
    intro v hv
    have hmem : v ∈ CFSG.fixedPointSubgroup A (P ⧸ Φ) ⊓ CFSG.commutatorAction (A := A)
        (G := P ⧸ Φ) := ⟨hv, by rw [hcomm_eq, hFA]; exact mem_top v⟩
    rw [hcompl.inf_eq_bot, mem_bot] at hmem
    exact hmem
  have hFinvcomm : ∀ V : Subgroup (P ⧸ Φ), (∀ a : A, ∀ v ∈ V, a • v ∈ V) →
      actionCommutator A V = V := fun V hV =>
    actionCommutator_eq_of_fixed_eq_bot hl (hFl.to_subgroup V) hA hV fun v _ hv => hFfix v hv
  have hirr : ∀ W : Subgroup (P ⧸ Φ), (∀ a : A, ∀ v ∈ W, a • v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_contra hne
    push Not at hne
    obtain ⟨hW1, hWt⟩ := hne
    set W₁ := W.comap π with hW₁def
    have hΦW₁ : Φ ≤ W₁ := fun x hx => by
      show π x ∈ W
      rw [show π x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
      exact W.one_mem
    have hW₁inv : ∀ a : A, ∀ x ∈ W₁, a • x ∈ W₁ := fun a x hx => by
      show π (a • x) ∈ W
      rw [hπA]
      exact hW a _ hx
    obtain ⟨W₂, hΦW₂, hW₂inv, hsup, hinf⟩ := exists_invariant_complement_section (p := l)
      hcop hΦW₁ (fun x => CFSG.pth_power_mem_frattini_of_isPGroup (p := l) x)
      (fun x y => CFSG.commutator_le_frattini_of_isPGroup (p := l)
        (commutator_mem_commutator (mem_top x) (mem_top y)))
      hΦinv' hW₁inv
    have hW₁map : W₁.map π = W := map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Φ) W
    have hW₁t : W₁ ≠ ⊤ := fun h => hWt (by rw [← hW₁map, h, map_top_of_surjective _
      (QuotientGroup.mk'_surjective Φ)])
    have hW₂t : W₂ ≠ ⊤ := fun h => hW1 (by
      rw [h, inf_top_eq] at hinf
      rw [← hW₁map, hinf]
      exact QuotientGroup.map_mk'_self Φ)
    set U₁ := actionCommutator A W₁
    set U₂ := actionCommutator A W₂
    have hU₁K : U₁ ≤ K := hU U₁ (lt_of_le_of_lt (actionCommutator_le_of_invariant hW₁inv)
      (lt_top_iff_ne_top.mpr hW₁t))
      (fun a x hx => smul_mem_actionCommutator_of_invariant hW₁inv a hx)
      (actionCommutator_actionCommutator_of_isPGroup hl (hP.to_subgroup W₁) hA hW₁inv)
    have hU₂K : U₂ ≤ K := hU U₂ (lt_of_le_of_lt (actionCommutator_le_of_invariant hW₂inv)
      (lt_top_iff_ne_top.mpr hW₂t))
      (fun a x hx => smul_mem_actionCommutator_of_invariant hW₂inv a hx)
      (actionCommutator_actionCommutator_of_isPGroup hl (hP.to_subgroup W₂) hA hW₂inv)
    have hWimg : ∀ X : Subgroup P, (∀ a : A, ∀ x ∈ X, a • x ∈ X) →
        (actionCommutator A X).map π = X.map π := fun X hX => by
      rw [map_actionCommutator π hπA]
      refine hFinvcomm _ fun a v hv => ?_
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨a • x, hX a x hx, hπA a x⟩
    have htop : (U₁ ⊔ U₂).map π = ⊤ := by
      rw [Subgroup.map_sup, hWimg W₁ hW₁inv, hWimg W₂ hW₂inv, ← Subgroup.map_sup, hsup,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective Φ)]
    have hUtop : U₁ ⊔ U₂ = ⊤ := by
      apply frattini_nongenerating
      have h := congrArg (Subgroup.comap π) htop
      rwa [comap_map_eq, comap_top, hπdef, QuotientGroup.ker_mk'] at h
    exact hKP.ne (eq_top_iff.mpr (hUtop ▸ sup_le hU₁K hU₂K))
  have hprop : ∀ U : Subgroup P, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) → U ≤ Φ := by
    intro U hUt hUinv
    rcases hirr (U.map π) (fun a v hv => by
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨a • x, hUinv a x hx, hπA a x⟩) with h | h
    · rw [← QuotientGroup.ker_mk' Φ]
      exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      apply hUt.ne
      apply frattini_nongenerating
      have h' := congrArg (Subgroup.comap π) h
      rwa [comap_map_eq, comap_top, hπdef, QuotientGroup.ker_mk'] at h'
  refine ⟨?_, hirr, hprop, hprop K hKP hKinv⟩
  by_contra htriv
  simp only [not_exists, not_not] at htriv
  apply hΦtop
  rw [eq_top_iff, ← hPA]
  refine (closure_le _).2 ?_
  rintro _ ⟨x, -, a, rfl⟩
  show _ ∈ Φ
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have h := htriv a (π x)
  rw [← hπA] at h
  change ((x : P ⧸ Φ))⁻¹ * ((a • x : P) : P ⧸ Φ) = 1
  rw [show ((a • x : P) : P ⧸ Φ) = π (a • x) from rfl, h]
  exact inv_mul_cancel _

end CFSG.RankThree.GroupTheory.SteinbergBM
