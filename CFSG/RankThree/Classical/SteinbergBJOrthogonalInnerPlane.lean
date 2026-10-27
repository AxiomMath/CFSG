module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalAveraging
public import CFSG.RankThree.Classical.SteinbergBJCharacterSpaces
public import CFSG.RankThree.Classical.SteinbergBJCentralCoprimeLift
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.RankThree.Classical

open Module TensorProduct QuadraticMap CFSG.Assembly CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)
open scoped IsMulCommutative commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

@[expose] def fixSpace (S : Subgroup (V ≃ₗ[K] V)) : Submodule K V where
  carrier := {v | ∀ g ∈ S, g v = v}
  add_mem' {u v} hu hv g hg := by rw [map_add, hu g hg, hv g hg]
  zero_mem' g _ := map_zero g
  smul_mem' c v hv g hg := by rw [map_smul, hv g hg]

theorem mem_fixSpace {S : Subgroup (V ≃ₗ[K] V)} {v : V} : v ∈ fixSpace S ↔ ∀ g ∈ S, g v = v :=
  Iff.rfl

variable {Q : QuadraticForm K V}

@[expose] def planeFixSpace (Ã : Subgroup (orthDerived Q)) : Submodule K V :=
  fixSpace (Ã.map (orthDerived Q).subtype)

@[expose] def lineFixSpace {Ã : Subgroup (orthDerived Q)} (M : Subgroup Ã) : Submodule K V :=
  fixSpace ((M.map Ã.subtype).map (orthDerived Q).subtype)

@[expose] def lineSpace {Ã : Subgroup (orthDerived Q)} (M : Subgroup Ã) : Submodule K V :=
  lineFixSpace M ⊓ LinearMap.BilinForm.orthogonal (polarBilin Q) (planeFixSpace Ã)

@[expose] def innerSummand (p : ℕ) (Ã : Subgroup (orthDerived Q)) :
    Option {M : Subgroup Ã // Nat.card M = p} → Submodule K V
  | none => planeFixSpace Ã
  | some M => lineSpace M.1

@[expose] def orthRep (Ã : Subgroup (orthDerived Q)) : Ã →* Module.End K V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ((orthDerived Q).subtype.comp Ã.subtype)

theorem orthRep_apply (Ã : Subgroup (orthDerived Q)) (x : Ã) (v : V) :
    orthRep Ã x v = ((x : orthDerived Q) : V ≃ₗ[K] V) v :=
  rfl

@[expose] noncomputable def bcRep (L : Type) [Field L] [Algebra K L]
    (Ã : Subgroup (orthDerived Q)) : Ã →* Module.End L (L ⊗[K] V) :=
  (Module.End.baseChangeHom K L V).toRingHom.toMonoidHom.comp (orthRep Ã)

theorem bcRep_apply (L : Type) [Field L] [Algebra K L] (Ã : Subgroup (orthDerived Q)) (x : Ã) :
    bcRep L Ã x = (orthRep Ã x).baseChange L :=
  rfl

section Decomposition

open _root_.Classical

variable {Γ : Type*} [Group Γ] {p : ℕ}

@[expose] def fixSub (ρ : Γ →* Module.End K V) (D : Subgroup Γ) : Submodule K V where
  carrier := {v | ∀ d ∈ D, ρ d v = v}
  add_mem' {u v} hu hv d hd := by rw [map_add, hu d hd, hv d hd]
  zero_mem' d _ := map_zero (ρ d)
  smul_mem' c v hv d hd := by rw [map_smul, hv d hd]

variable {ρ : Γ →* Module.End K V}

theorem mem_fixSub {D : Subgroup Γ} {v : V} : v ∈ fixSub ρ D ↔ ∀ d ∈ D, ρ d v = v :=
  Iff.rfl

theorem range_avgOp_eq_fixSub {D : Subgroup Γ} [Fintype D] (hD : (Fintype.card D : K) ≠ 0) :
    LinearMap.range (avgOp ρ D) = fixSub ρ D := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩ d hd
    exact apply_avgOp hd u
  · intro hv
    exact ⟨v, avgOp_apply_of_fixed hD hv⟩

variable [Fintype Γ]

@[expose] noncomputable def lineIdem (ρ : Γ →* Module.End K V) (p : ℕ) :
    Option {M : Subgroup Γ // Nat.card M = p} → Module.End K V
  | none => avgOp ρ ⊤
  | some M => avgOp ρ M.1 - avgOp ρ ⊤

omit [Fintype Γ] in
theorem card_line_ne_zero {M : Subgroup Γ} [Fintype M] (hM : Nat.card M = p)
    (hpK : (p : K) ≠ 0) : (Fintype.card M : K) ≠ 0 := by
  rw [← Nat.card_eq_fintype_card, hM]
  exact hpK

theorem card_top_ne_zero (hΓ : Nat.card Γ = p ^ 2) (hpK : (p : K) ≠ 0) :
    (Fintype.card (⊤ : Subgroup Γ) : K) ≠ 0 := by
  rw [← Nat.card_eq_fintype_card, Subgroup.card_top, hΓ, Nat.cast_pow]
  exact pow_ne_zero 2 hpK

theorem lineIdem_mul_self (hΓ : Nat.card Γ = p ^ 2) (hpK : (p : K) ≠ 0)
    (i : Option {M : Subgroup Γ // Nat.card M = p}) :
    lineIdem ρ p i * lineIdem ρ p i = lineIdem ρ p i := by
  have htop := card_top_ne_zero (K := K) hΓ hpK
  rcases i with _ | ⟨M, hM⟩
  · exact avgOp_mul_avgOp_of_le le_rfl htop
  · have hMK := card_line_ne_zero (K := K) hM hpK
    simp only [lineIdem]
    rw [sub_mul, mul_sub, mul_sub, avgOp_mul_avgOp_of_le le_rfl hMK,
      avgOp_mul_avgOp_of_le le_top hMK, avgOp_mul_avgOp_of_le' le_top hMK,
      avgOp_mul_avgOp_of_le le_rfl htop]
    abel

theorem lineIdem_mul_of_ne (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : Nat.card Γ = p ^ 2)
    (hpK : (p : K) ≠ 0) {i j : Option {M : Subgroup Γ // Nat.card M = p}} (hij : i ≠ j) :
    lineIdem ρ p i * lineIdem ρ p j = 0 := by
  have htop := card_top_ne_zero (K := K) hΓ hpK
  rcases i with _ | ⟨M, hM⟩ <;> rcases j with _ | ⟨M', hM'⟩
  · exact absurd rfl hij
  · have hMK := card_line_ne_zero (K := K) hM' hpK
    simp only [lineIdem]
    rw [mul_sub, avgOp_mul_avgOp_of_le' le_top hMK, avgOp_mul_avgOp_of_le le_rfl htop, sub_self]
  · have hMK := card_line_ne_zero (K := K) hM hpK
    simp only [lineIdem]
    rw [sub_mul, avgOp_mul_avgOp_of_le le_top hMK, avgOp_mul_avgOp_of_le le_rfl htop, sub_self]
  · have hne : M ≠ M' := fun h => hij (by subst h; rfl)
    have hMK := card_line_ne_zero (K := K) hM hpK
    have hMK' := card_line_ne_zero (K := K) hM' hpK
    simp only [lineIdem]
    rw [sub_mul, mul_sub, mul_sub,
      avgOp_mul_avgOp_eq_top (inf_eq_bot_of_natCard_eq_prime hp hexp hM hM' hne)
        (by rw [hM, hM', hΓ, _root_.sq]),
      avgOp_mul_avgOp_of_le le_top hMK, avgOp_mul_avgOp_of_le' le_top hMK',
      avgOp_mul_avgOp_of_le le_rfl htop]
    abel

theorem sum_lineIdem (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : Nat.card Γ = p ^ 2)
    (hpK : (p : K) ≠ 0) :
    ∑ i : Option {M : Subgroup Γ // Nat.card M = p}, lineIdem ρ p i = 1 := by
  rw [Fintype.sum_option]
  simp only [lineIdem]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    (Finset.sum_subtype (Finset.univ.filter fun M : Subgroup Γ => Nat.card M = p)
      (fun M => by simp) (fun M => avgOp ρ M)).symm, sum_avgOp_lines hp hexp hΓ hpK,
    Fintype.card_subtype, card_subgroups_natCard_eq_prime hp hexp hΓ,
    ← Nat.cast_smul_eq_nsmul K, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  abel

variable (B : LinearMap.BilinForm K V)

theorem lineIdem_selfAdjoint (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (i : Option {M : Subgroup Γ // Nat.card M = p}) (u v : V) :
    B (lineIdem ρ p i u) v = B u (lineIdem ρ p i v) := by
  rcases i with _ | ⟨M, hM⟩
  · exact bilin_avgOp B hB ⊤ u v
  · simp only [lineIdem, LinearMap.sub_apply, map_sub]
    rw [bilin_avgOp B hB M u v, bilin_avgOp B hB ⊤ u v]

theorem range_lineIdem_none (hΓ : Nat.card Γ = p ^ 2) (hpK : (p : K) ≠ 0) :
    LinearMap.range (lineIdem ρ p none) = fixSub ρ ⊤ :=
  range_avgOp_eq_fixSub (card_top_ne_zero hΓ hpK)

theorem range_lineIdem_some (hΓ : Nat.card Γ = p ^ 2) (hpK : (p : K) ≠ 0)
    (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w) (hBsymm : ∀ u v, B u v = B v u)
    (hBnd : ∀ u, (∀ v, B u v = 0) → u = 0) (M : {M : Subgroup Γ // Nat.card M = p}) :
    LinearMap.range (lineIdem ρ p (some M)) =
      fixSub ρ M.1 ⊓ LinearMap.BilinForm.orthogonal B (fixSub ρ ⊤) := by
  have htop := card_top_ne_zero (K := K) hΓ hpK
  have hMK := card_line_ne_zero (K := K) M.2 hpK
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    simp only [lineIdem, LinearMap.sub_apply]
    refine ⟨fun d hd => ?_, ?_⟩
    · rw [map_sub, apply_avgOp hd, apply_avgOp (Subgroup.mem_top d)]
    · rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      rw [map_sub, ← bilin_avgOp B hB, ← bilin_avgOp B hB,
        avgOp_apply_of_fixed hMK (fun d _ => hu d (Subgroup.mem_top d)),
        avgOp_apply_of_fixed htop hu, sub_self]
  · rintro ⟨hw1, hw2⟩
    refine ⟨w, ?_⟩
    have h1 : avgOp ρ M.1 w = w := avgOp_apply_of_fixed hMK hw1
    have h2 : avgOp ρ ⊤ w = 0 := by
      apply hBnd
      intro x
      rw [bilin_avgOp B hB ⊤ w x, hBsymm]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hw2) _
        fun d _ => apply_avgOp (Subgroup.mem_top d) x
    simp only [lineIdem, LinearMap.sub_apply, h1, h2, sub_zero]

theorem lineIdem_orthogonal (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1)
    (hΓ : Nat.card Γ = p ^ 2) (hpK : (p : K) ≠ 0) (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    {i j : Option {M : Subgroup Γ // Nat.card M = p}} (hij : i ≠ j) (u v : V) :
    B (lineIdem ρ p i u) (lineIdem ρ p j v) = 0 := by
  rw [lineIdem_selfAdjoint B hB, ← Module.End.mul_apply, lineIdem_mul_of_ne hp hexp hΓ hpK hij,
    LinearMap.zero_apply, map_zero]

theorem lineIdem_restrict_nondegenerate (hΓ : Nat.card Γ = p ^ 2) (hpK : (p : K) ≠ 0)
    (hB : ∀ g u w, B (ρ g u) (ρ g w) = B u w) (hBsymm : ∀ u v, B u v = B v u)
    (hBnd : ∀ u, (∀ v, B u v = 0) → u = 0) (i : Option {M : Subgroup Γ // Nat.card M = p}) :
    (B.restrict (LinearMap.range (lineIdem ρ p i))).Nondegenerate := by
  have key : ∀ x ∈ LinearMap.range (lineIdem ρ p i),
      (∀ y ∈ LinearMap.range (lineIdem ρ p i), B x y = 0) → x = 0 := by
    rintro _ ⟨u, rfl⟩ h
    apply hBnd
    intro v
    have := h (lineIdem ρ p i v) ⟨v, rfl⟩
    rwa [lineIdem_selfAdjoint B hB, ← Module.End.mul_apply, lineIdem_mul_self hΓ hpK,
      ← lineIdem_selfAdjoint B hB] at this
  constructor
  · intro x hx
    exact Subtype.ext (key x x.2 fun y hy => hx ⟨y, hy⟩)
  · intro y hy
    exact Subtype.ext (key y y.2 fun x hx => by rw [hBsymm]; exact hy ⟨x, hx⟩)

end Decomposition

section Characters

open _root_.Classical

variable {Γ : Type*} [Group Γ] [Fintype Γ] {p : ℕ} [NeZero p] {ρ : Γ →* Module.End K V}

@[expose] noncomputable def bcRepOf (L : Type) [Field L] [Algebra K L]
    (ρ : Γ →* Module.End K V) : Γ →* Module.End L (L ⊗[K] V) :=
  (Module.End.baseChangeHom K L V).toRingHom.toMonoidHom.comp ρ

omit [Fintype Γ] [NeZero p] in
theorem bcRepOf_apply (L : Type) [Field L] [Algebra K L] (g : Γ) :
    bcRepOf L ρ g = (ρ g).baseChange L :=
  rfl

omit [Fintype Γ] [NeZero p] in
theorem avgOp_baseChange (L : Type) [Field L] [Algebra K L] (D : Subgroup Γ) [Fintype D] :
    (avgOp ρ D).baseChange L = avgOp (bcRepOf L ρ) D := by
  rw [avgOp, avgOp, LinearMap.baseChange_smul, ← algebraMap_smul L, map_inv₀, map_natCast]
  congr 1
  exact map_sum (LinearMap.baseChangeHom K L V V) _ _

omit [Fintype Γ] in
theorem avgOp_apply_of_mem_charSpace {L : Type} [Field L] [Algebra K L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ p) (D : Subgroup Γ) [Fintype D] (hD : (Fintype.card D : L) ≠ 0)
    {χ : Additive Γ →+ ZMod p} {v : L ⊗[K] V} (hv : v ∈ charSpace (bcRepOf L ρ) ζ χ) :
    avgOp (bcRepOf L ρ) D v = if D ≤ charKer χ then v else 0 := by
  have hv' := mem_charSpace.mp hv
  have hsum : avgOp (bcRepOf L ρ) D v =
      ((Fintype.card D : L)⁻¹ * ∑ d : D, ζ ^ (χ (Additive.ofMul (d : Γ))).val) • v := by
    rw [avgOp, LinearMap.smul_apply, LinearMap.sum_apply,
      Finset.sum_congr rfl fun (d : D) _ => hv' (d : Γ), ← Finset.sum_smul, smul_smul]
  rw [hsum]
  split_ifs with h
  · have h1 : ∀ d : D, ζ ^ (χ (Additive.ofMul (d : Γ))).val = 1 := fun d => by
      rw [mem_charKer.mp (h d.2), ZMod.val_zero, pow_zero]
    rw [Finset.sum_congr rfl fun d _ => h1 d, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, inv_mul_cancel₀ hD, one_smul]
  · set χD : Additive D →+ ZMod p := χ.comp (MonoidHom.toAdditive D.subtype) with hχD
    have hχD0 : χD ≠ 0 := by
      intro h0
      apply h
      intro d hd
      exact DFunLike.congr_fun h0 (Additive.ofMul ⟨d, hd⟩)
    have h2 : ∑ d : D, ζ ^ (χ (Additive.ofMul (d : Γ))).val =
        ∑ d : D, ζ ^ (χD (Additive.ofMul d)).val := rfl
    rw [h2, sum_pow_val_char_eq_zero hζ hχD0, mul_zero, zero_smul]

omit [Fintype Γ] [NeZero p] in
theorem top_le_charKer_iff {χ : Additive Γ →+ ZMod p} : (⊤ : Subgroup Γ) ≤ charKer χ ↔ χ = 0 := by
  constructor
  · intro h
    exact AddMonoidHom.ext fun x => h (Subgroup.mem_top (Additive.toMul x))
  · rintro rfl x _
    exact AddMonoidHom.zero_apply _

end Characters

section CommCharacters

open _root_.Classical

variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] {p : ℕ} [NeZero p] {ρ : Γ →* Module.End K V}

theorem range_lineIdem_baseChange (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1)
    (hΓ : Nat.card Γ = p ^ 2) {L : Type} [Field L] [Algebra K L] (hpL : (p : L) ≠ 0) {ζ : L}
    (hζ : IsPrimitiveRoot ζ p) [Fintype (Additive Γ →+ ZMod p)]
    (M : {M : Subgroup Γ // Nat.card M = p}) :
    LinearMap.range ((lineIdem ρ p (some M)).baseChange L) =
      ⨆ (χ : Additive Γ →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M.1),
        charSpace (bcRepOf L ρ) ζ χ := by
  have hbc : (lineIdem ρ p (some M)).baseChange L =
      avgOp (bcRepOf L ρ) M.1 - avgOp (bcRepOf L ρ) ⊤ := by
    simp only [lineIdem]
    rw [LinearMap.baseChange_sub, avgOp_baseChange, avgOp_baseChange]
  have hML : (Fintype.card M.1 : L) ≠ 0 := card_line_ne_zero (K := L) M.2 hpL
  have htopL : (Fintype.card (⊤ : Subgroup Γ) : L) ≠ 0 := card_top_ne_zero (K := L) hΓ hpL
  have hΓL : (Fintype.card Γ : L) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hΓ, Nat.cast_pow]
    exact pow_ne_zero 2 hpL
  have hterm : ∀ (χ : Additive Γ →+ ZMod p), ∀ v ∈ charSpace (bcRepOf L ρ) ζ χ,
      (avgOp (bcRepOf L ρ) M.1 - avgOp (bcRepOf L ρ) ⊤) v =
        if χ ≠ 0 ∧ charKer χ = M.1 then v else 0 := by
    intro χ v hv
    rw [LinearMap.sub_apply, avgOp_apply_of_mem_charSpace hζ _ hML hv,
      avgOp_apply_of_mem_charSpace hζ _ htopL hv]
    by_cases hχ : χ = 0
    · subst hχ
      have h1 : M.1 ≤ charKer (0 : Additive Γ →+ ZMod p) := fun x _ =>
        AddMonoidHom.zero_apply _
      have h2 : (⊤ : Subgroup Γ) ≤ charKer (0 : Additive Γ →+ ZMod p) := fun x _ =>
        AddMonoidHom.zero_apply _
      rw [ite_eq_left h1, ite_eq_left h2, sub_self, ite_eq_right (fun h => h.1 rfl)]
    · have htop' : ¬(⊤ : Subgroup Γ) ≤ charKer χ := fun h => hχ (top_le_charKer_iff.mp h)
      rw [ite_eq_right htop', sub_zero]
      by_cases hle : M.1 ≤ charKer χ
      · have heq : charKer χ = M.1 := (Subgroup.eq_of_le_of_card_ge hle
          (by rw [natCard_charKer hp hΓ hχ, M.2])).symm
        rw [ite_eq_left hle, ite_eq_left ⟨hχ, heq⟩]
      · have hne : charKer χ ≠ M.1 := fun h => hle (h ▸ le_rfl)
        rw [ite_eq_right hle, ite_eq_right (fun h => hne h.2)]
  rw [hbc]
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    rw [eq_sum_charIdem_apply hp hζ hexp hΓL u, map_sum]
    refine Submodule.sum_mem _ fun χ _ => ?_
    rw [hterm χ _ (charIdem_apply_mem hζ.pow_eq_one χ u)]
    split_ifs with hχ
    · exact Submodule.mem_iSup_of_mem χ
        (Submodule.mem_iSup_of_mem hχ (charIdem_apply_mem hζ.pow_eq_one χ u))
    · exact zero_mem _
  · refine iSup₂_le fun χ hχ v hv => ⟨v, ?_⟩
    rw [hterm χ v hv, ite_eq_left hχ]

end CommCharacters

section Orbits

variable {p : ℕ} {D : Type*} [AddCommGroup D] [Module (ZMod p) D]

theorem smul_invariant_of_mem_closure {q : ℕ} (hcop : Nat.Coprime q p) (m : D → ℕ)
    (hq : ∀ χ, m (q • χ) = m χ) (hneg : ∀ χ, m (-χ) = m χ) :
    ∀ w ∈ Subgroup.closure {ZMod.unitOfCoprime q hcop, -1}, ∀ χ, m ((w : ZMod p) • χ) = m χ := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    rcases hw with rfl | hw
    · intro χ
      rw [ZMod.coe_unitOfCoprime, Nat.cast_smul_eq_nsmul]
      exact hq χ
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      intro χ
      rw [Units.val_neg, Units.val_one, neg_one_smul]
      exact hneg χ
  | one => intro χ; rw [Units.val_one, one_smul]
  | mul w w' _ _ h h' => intro χ; rw [Units.val_mul, mul_smul, h, h']
  | inv w _ h =>
    intro χ
    have := h (((w⁻¹ : (ZMod p)ˣ) : ZMod p) • χ)
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul] at this
    exact this.symm

omit [AddCommGroup D] [Module (ZMod p) D] in
theorem lcm_dvd_natCard_closure (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ} (hcop : Nat.Coprime q p) :
    Nat.lcm (orderOf (q : ZMod p)) 2 ∣
      Nat.card (Subgroup.closure {ZMod.unitOfCoprime q hcop, (-1 : (ZMod p)ˣ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  refine Nat.lcm_dvd ?_ ?_
  · rw [← ZMod.coe_unitOfCoprime q hcop, orderOf_units]
    exact Subgroup.orderOf_dvd_natCard _ (Subgroup.subset_closure (Set.mem_insert _ _))
  · have h2 : orderOf (-1 : (ZMod p)ˣ) = 2 := by
      rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one, ZMod.ringChar_zmod_n,
        ite_eq_right hp2]
    rw [← h2]
    exact Subgroup.orderOf_dvd_natCard _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem lcm_dvd_sum_unit_orbit [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) {q : ℕ} (hpq : ¬p ∣ q)
    (m : D → ℕ) (hq : ∀ χ, m (q • χ) = m χ) (hneg : ∀ χ, m (-χ) = m χ) (χ₀ : D) :
    Nat.lcm (orderOf (q : ZMod p)) 2 ∣ ∑ w : (ZMod p)ˣ, m ((w : ZMod p) • χ₀) := by
  have hcop : Nat.Coprime q p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)
  refine (lcm_dvd_natCard_closure hp hp2 hcop).trans (natCard_dvd_sum_of_invariant _ _ ?_)
  intro h hh w
  rw [Units.val_mul, mul_smul, smul_invariant_of_mem_closure hcop m hq hneg h hh]

theorem exists_not_mem_zmultiples_of_closure_eq_top [Finite D] (hp : p.Prime)
    (hD : Nat.card D = p ^ 2) {S : Set D} (hS : AddSubgroup.closure S = ⊤) :
    ∃ χ₁ ∈ S, ∃ χ₂ ∈ S, χ₂ ∉ AddSubgroup.zmultiples χ₁ := by
  have hp2' := hp.two_le
  have hpχ : ∀ χ : D, p • χ = 0 := fun χ => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  have hzm : ∀ χ : D, Nat.card (AddSubgroup.zmultiples χ) ≤ p := fun χ => by
    rw [Nat.card_zmultiples]
    exact addOrderOf_le_of_nsmul_eq_zero hp.pos (hpχ χ)
  have hp1 : p < p ^ 2 := by nlinarith
  obtain ⟨χ₁, hχ₁⟩ : S.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, AddSubgroup.closure_empty] at hS
    have h1 : Nat.card D ≤ 1 := by
      rw [← AddSubgroup.card_top (G := D), ← hS, AddSubgroup.card_bot]
    omega
  obtain ⟨χ₂, hχ₂, hχ₂'⟩ : ∃ χ ∈ S, χ ∉ AddSubgroup.zmultiples χ₁ := by
    by_contra hcon
    push Not at hcon
    have hle : AddSubgroup.closure S ≤ AddSubgroup.zmultiples χ₁ :=
      (AddSubgroup.closure_le _).mpr hcon
    rw [hS] at hle
    have h1 : Nat.card D ≤ p := by
      rw [← AddSubgroup.card_top (G := D)]
      exact (AddSubgroup.card_le_of_le hle).trans (hzm χ₁)
    omega
  exact ⟨χ₁, hχ₁, χ₂, hχ₂, hχ₂'⟩

end Orbits

section CharOrbits

open _root_.Classical

variable {Γ : Type*} [CommGroup Γ] [Fintype Γ] {p : ℕ}

theorem exists_charKer_ne (hp : p.Prime) (hexp : ∀ g : Γ, g ^ p = 1) (hΓ : Nat.card Γ = p ^ 2)
    {S : Set (Additive Γ →+ ZMod p)} (hS : AddSubgroup.closure S = ⊤) (hS0 : ∀ χ ∈ S, χ ≠ 0) :
    ∃ χ₁ ∈ S, ∃ χ₂ ∈ S, charKer χ₁ ≠ charKer χ₂ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (Additive Γ →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  have hD : Nat.card (Additive Γ →+ ZMod p) = p ^ 2 := by rw [natCard_char hp hexp, hΓ]
  obtain ⟨χ₁, hχ₁, χ₂, hχ₂, hχ₂'⟩ := exists_not_mem_zmultiples_of_closure_eq_top hp hD hS
  refine ⟨χ₁, hχ₁, χ₂, hχ₂, fun h => hχ₂' ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_smul_of_le_charKer hp hΓ (hS0 χ₁ hχ₁) h.le
  rw [hc, ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem_zmultiples _ _

theorem lcm_dvd_sum_filter_charKer [NeZero p] [Fintype (Additive Γ →+ ZMod p)] (hp : p.Prime)
    (hp2 : p ≠ 2) (hΓ : Nat.card Γ = p ^ 2) {q : ℕ} (hpq : ¬p ∣ q)
    (m : (Additive Γ →+ ZMod p) → ℕ) (hq : ∀ χ, m (q • χ) = m χ) (hneg : ∀ χ, m (-χ) = m χ)
    (M : Subgroup Γ) :
    Nat.lcm (orderOf (q : ZMod p)) 2 ∣
      ∑ χ ∈ Finset.univ.filter (fun χ : Additive Γ →+ ZMod p => χ ≠ 0 ∧ charKer χ = M), m χ := by
  by_cases hS' : ∃ χ₀ : Additive Γ →+ ZMod p, χ₀ ≠ 0 ∧ charKer χ₀ = M
  · obtain ⟨χ₀, hχ₀, hχ₀M⟩ := hS'
    have hunit : ∀ (w : (ZMod p)ˣ) (y : ZMod p), (w : ZMod p) * y = 0 ↔ y = 0 := fun w y =>
      ⟨fun h => by
        have := congrArg (fun z => ((w⁻¹ : (ZMod p)ˣ) : ZMod p) * z) h
        simpa [← mul_assoc] using this, fun h => by rw [h, mul_zero]⟩
    have hker : ∀ w : (ZMod p)ˣ, charKer ((w : ZMod p) • χ₀) = charKer χ₀ := by
      intro w
      ext x
      rw [mem_charKer, mem_charKer, AddMonoidHom.smul_apply, smul_eq_mul, hunit]
    have hbij : ∑ χ ∈ Finset.univ.filter (fun χ : Additive Γ →+ ZMod p =>
        χ ≠ 0 ∧ charKer χ = M), m χ = ∑ w : (ZMod p)ˣ, m ((w : ZMod p) • χ₀) := by
      symm
      refine Finset.sum_bij (fun w _ => (w : ZMod p) • χ₀) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro w _
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun h0 => hχ₀ ?_, by rw [hker, hχ₀M]⟩
        have := congrArg (fun ψ => ((w⁻¹ : (ZMod p)ˣ) : ZMod p) • ψ) h0
        simp only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul,
          smul_zero] at this
        exact this
      · intro w _ w' _ h
        obtain ⟨x, hx⟩ : ∃ x : Γ, χ₀ (Additive.ofMul x) ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hχ₀ (AddMonoidHom.ext fun y => hcon (Additive.toMul y))
        have h1 := DFunLike.congr_fun h (Additive.ofMul x)
        simp only [AddMonoidHom.smul_apply, smul_eq_mul] at h1
        have : Fact p.Prime := ⟨hp⟩
        exact Units.ext (mul_right_cancel₀ hx h1)
      · intro χ hχ
        rw [Finset.mem_filter] at hχ
        obtain ⟨c, hc⟩ := exists_eq_smul_of_le_charKer hp hΓ hχ₀ (hχ₀M.trans hχ.2.2.symm).le
        have hc0 : c ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hc
          exact hχ.2.1 hc
        have : Fact p.Prime := ⟨hp⟩
        exact ⟨Units.mk0 c hc0, Finset.mem_univ _, by rw [Units.val_mk0, hc]⟩
    rw [hbij]
    exact lcm_dvd_sum_unit_orbit hp hp2 hpq m hq hneg χ₀
  · push Not at hS'
    rw [Finset.sum_eq_zero fun χ hχ =>
      absurd (Finset.mem_filter.mp hχ).2.2 (hS' χ (Finset.mem_filter.mp hχ).2.1)]
    exact dvd_zero _

end CharOrbits

section OmegaAction

theorem orthDerived_le_orthogonalGroup (Q : QuadraticForm K V) :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem polar_orthRep (Ã : Subgroup (orthDerived Q)) (g : Ã) (u w : V) :
    polarBilin Q (orthRep Ã g u) (orthRep Ã g w) = polarBilin Q u w :=
  polar_map_of_mem (orthDerived_le_orthogonalGroup Q (g : orthDerived Q).2) u w

theorem planeFixSpace_eq_fixSub (Ã : Subgroup (orthDerived Q)) :
    planeFixSpace Ã = fixSub (orthRep Ã) ⊤ := by
  ext v
  constructor
  · intro h x _
    exact h _ ⟨x, x.2, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h ⟨x, hx⟩ trivial

theorem lineFixSpace_eq_fixSub {Ã : Subgroup (orthDerived Q)} (M : Subgroup Ã) :
    lineFixSpace M = fixSub (orthRep Ã) M := by
  ext v
  constructor
  · intro h x hx
    exact h _ ⟨x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro h _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact h x hx

open _root_.Classical in
theorem innerSummand_eq_range {p : ℕ} (hQ : (polarBilin Q).Nondegenerate)
    {Ã : Subgroup (orthDerived Q)} [Fintype Ã] (hΓ : Nat.card Ã = p ^ 2) (hpK : (p : K) ≠ 0)
    (i : Option {M : Subgroup Ã // Nat.card M = p}) :
    innerSummand p Ã i = LinearMap.range (lineIdem (orthRep Ã) p i) := by
  rcases i with _ | ⟨M, hM⟩
  · rw [range_lineIdem_none hΓ hpK]
    exact planeFixSpace_eq_fixSub Ã
  · rw [range_lineIdem_some (polarBilin Q) hΓ hpK (polar_orthRep Ã) (fun u v => polar_comm Q u v)
      (fun u h => hQ.1 u h)]
    change lineSpace M = _
    rw [lineSpace, lineFixSpace_eq_fixSub, planeFixSpace_eq_fixSub]

theorem orthRep_eq_one {Ã : Subgroup (orthDerived Q)} {g : Ã} (hg : orthRep Ã g = 1) : g = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact LinearMap.congr_fun hg v

open _root_.Classical in
theorem orth_bcRep_charSpace_facts {ℓ p : ℕ} [Finite K] (hℓ : ℓ.Prime) [CharP K ℓ]
    (hp : p.Prime) (hpℓ : p ≠ ℓ) [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {Ã : Subgroup (orthDerived Q)} [IsMulCommutative Ã] [Fintype Ã] (hexp : ∀ x : Ã, x ^ p = 1)
    (hΓ : Nat.card Ã = p ^ 2) [NeZero p] [Fintype (Additive Ã →+ ZMod p)] (L : Type) [Field L]
    [Algebra K L] [IsAlgClosed L] {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    (∀ χ : Additive Ã →+ ZMod p, finrank L (charSpace (bcRep L Ã) ζ ((Nat.card K) • χ)) =
        finrank L (charSpace (bcRep L Ã) ζ χ)) ∧
      (∀ χ : Additive Ã →+ ZMod p, finrank L (charSpace (bcRep L Ã) ζ (-χ)) =
        finrank L (charSpace (bcRep L Ã) ζ χ)) ∧
      AddSubgroup.closure {χ : Additive Ã →+ ZMod p |
        χ ≠ 0 ∧ charSpace (bcRep L Ã) ζ χ ≠ ⊥} = ⊤ ∧
      ∑ χ : Additive Ã →+ ZMod p, finrank L (charSpace (bcRep L Ã) ζ χ) = finrank K V ∧
      ∀ M : {M : Subgroup Ã // Nat.card M = p}, (lineSpace M.1).baseChange L =
        ⨆ (χ : Additive Ã →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M.1), charSpace (bcRep L Ã) ζ χ := by
  have := Fintype.ofFinite K
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have hpL : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero _).mpr hpK
  have hΓL : (Fintype.card Ã : L) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hΓ, Nat.cast_pow]
    exact pow_ne_zero 2 hpL
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
  let σ : L ≃+* L := iterateFrobeniusEquiv L ℓ n
  have hσ : ∀ x : L, σ x = x ^ Nat.card K := fun x => by
    rw [Nat.card_eq_fintype_card, hn, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hσK : ∀ c : K, σ (algebraMap K L c) = algebraMap K L c := fun c => by
    rw [hσ, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hfaith : ∀ g : Ã, bcRep L Ã g = 1 → g = 1 := fun g hg =>
    orthRep_eq_one (eq_of_baseChange_eq L (by rw [← bcRep_apply, hg, LinearMap.baseChange_one]))
  have hBL : ∀ (g : Ã) (s t : L ⊗[K] V), LinearMap.BilinForm.baseChange L (polarBilin Q)
      (bcRep L Ã g s) (bcRep L Ã g t) = LinearMap.BilinForm.baseChange L (polarBilin Q) s t :=
    fun g s t => baseChange_apply_baseChange L (polarBilin Q) (orthRep Ã g) (polar_orthRep Ã g) s t
  have hBnd : ∀ s : L ⊗[K] V, (∀ t, LinearMap.BilinForm.baseChange L (polarBilin Q) s t = 0) →
      s = 0 := bilin_baseChange_separatingLeft L (polarBilin Q) hQ
  refine ⟨fun χ => finrank_charSpace_nsmul hζ.pow_eq_one σ (fieldAutTensor L σ hσK)
      (fieldAutTensor_smul σ hσK) (fun g t => fieldAutTensor_baseChange σ hσK _ t) _ (hσ ζ) χ,
    fun χ => finrank_charSpace_neg hp hζ hexp hΓL _ hBL hBnd χ,
    closure_support_charSpace_eq_top hp hζ hexp hΓL hfaith,
    by rw [sum_finrank_charSpace hp hζ hexp hΓL, Module.finrank_baseChange], fun M => ?_⟩
  have hl : lineSpace M.1 = LinearMap.range (lineIdem (orthRep Ã) p (some M)) :=
    innerSummand_eq_range hQ hΓ hpK (some M)
  rw [hl, ← range_baseChange_eq, range_lineIdem_baseChange hp hexp hΓ hpL hζ M]
  rfl

end OmegaAction

open _root_.Classical in
theorem orthogonal_inner_plane_kernel_line_quadratic_decomposition {ℓ p : ℕ} [Finite K]
    (hℓ : ℓ.Prime) [CharP K ℓ] (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    [FiniteDimensional K V] [Nontrivial V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (A : Subgroup (ProjOrthDerived Q))
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    ∃ Ã : Subgroup (orthDerived Q),
      Ã ≤ A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) ∧
      (∀ P : Sylow p (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))),
        (P : Subgroup (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))).map
          (A.comap (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))).subtype = Ã) ∧
      ∃ e : Ã ≃* A, (∀ x : Ã, (e x : ProjOrthDerived Q) =
          QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) ∧
      (∀ a ∈ A, ∃! x : orthDerived Q,
        QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x = a ∧ x ^ p = 1) ∧
      DirectSum.IsInternal (innerSummand p Ã) ∧
      (∀ i j, i ≠ j → ∀ u ∈ innerSummand p Ã i, ∀ v ∈ innerSummand p Ã j,
        polarBilin Q u v = 0) ∧
      (∀ i, (LinearMap.BilinForm.restrict (polarBilin Q) (innerSummand p Ã i)).Nondegenerate) ∧
      (∀ M : Subgroup Ã, Nat.card M = p → ∀ a ∈ M, a ≠ 1 →
        LinearMap.ker (((a : orthDerived Q) : V ≃ₗ[K] V).toLinearMap - LinearMap.id) =
          lineFixSpace M ∧ lineFixSpace M = planeFixSpace Ã ⊔ lineSpace M) ∧
      (∃ M₁ M₂ : Subgroup Ã, Nat.card M₁ = p ∧ Nat.card M₂ = p ∧ M₁ ≠ M₂ ∧
        lineSpace M₁ ≠ ⊥ ∧ lineSpace M₂ ≠ ⊥) ∧
      (∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
        0 < finrank K (lineSpace M) ∧
          Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ∣ finrank K (lineSpace M)) ∧
      2 * Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≤ finrank K V ∧
      finrank (ZMod p) (Additive Ã →+ ZMod p) = 2 ∧
      ∀ ζ : AlgebraicClosure K, IsPrimitiveRoot ζ p →
        Submodule.span (ZMod p) {χ : Additive Ã →+ ZMod p |
          χ ≠ 0 ∧ charSpace (bcRep (AlgebraicClosure K) Ã) ζ χ ≠ ⊥} = ⊤ ∧
        ∀ M : Subgroup Ã, Nat.card M = p →
          (lineSpace M).baseChange (AlgebraicClosure K) =
            ⨆ (χ : Additive Ã →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M),
              charSpace (bcRep (AlgebraicClosure K) Ã) ζ χ := by
  have := Fintype.ofFinite K
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    DFunLike.coe_injective
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  set B : LinearMap.BilinForm K V := polarBilin Q with hBdef
  have hBapp : ∀ u v, B u v = polar Q u v := fun u v => rfl
  have hBsymm : ∀ u v, B u v = B v u := fun u v => polar_comm Q u v
  have hBnd : ∀ u, (∀ v, B u v = 0) → u = 0 := fun u h => hQ.1 u h
  obtain ⟨a₀, ha₀⟩ : ∃ a : V, Q a ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    apply hu
    apply hBnd
    intro v
    rw [hBapp, polar, h, h, h, sub_zero, sub_zero]
  set Ω := orthDerived Q with hΩ
  set Z := (scalars K V).subgroupOf Ω with hZ
  have hΩO : ∀ g ∈ Ω, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun g hg =>
    orthDerived_le_orthogonalGroup Q hg
  have hZc : (QuotientGroup.mk' Z).ker ≤ Subgroup.center Ω := by
    rw [QuotientGroup.ker_mk']
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (commute_of_mem_scalars (Subgroup.mem_subgroupOf.mp hz) g).symm
  have hZsq : ∀ z : Z, z ^ 2 = 1 := by
    intro z
    obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp z.2)
    have h1 := map_of_mem (hΩO _ (z : Ω).2) a₀
    rw [hc, map_smul_eq_sq] at h1
    have hc2 : c ^ 2 = 1 := by
      have : (c ^ 2 - 1) * Q a₀ = 0 := by rw [sub_mul, h1, one_mul, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ha₀)
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [Subgroup.coe_pow, Subgroup.coe_pow, pow_two, LinearEquiv.mul_apply, hc, hc,
      smul_smul, ← pow_two, hc2, one_smul]
    rfl
  have hZp : Nat.Coprime (Nat.card (QuotientGroup.mk' Z).ker) p := by
    rw [QuotientGroup.ker_mk', Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) p hdvd
    have h2 := orderOf_dvd_of_pow_eq_one (hZsq z)
    rw [hz] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hAp : IsPGroup p A := fun a => ⟨1, Subtype.ext (by rw [pow_one]; exact hA.2 a a.2)⟩
  obtain ⟨Ã, hÃM, hÃuniq, e, he⟩ := exists_sylow_lift_of_ker_le_center hp (QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective Z) hZc hZp A hAp
  refine ⟨Ã, hÃM, hÃuniq, e, he,
    existsUnique_lift_pow_eq_one (QuotientGroup.mk' Z) hZc hZp hA.2 e he, ?_⟩
  have : IsMulCommutative A := hA.1
  have : IsMulCommutative Ã := ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  have hexp : ∀ x : Ã, x ^ p = 1 := fun x => e.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hA.2 _ (e x).2))
  have hΓ : Nat.card Ã = p ^ 2 := (Nat.card_congr e.toEquiv).trans hAc
  have : Fintype Ã := Fintype.ofFinite _
  set ρ := orthRep Ã with hρ
  have hρB : ∀ g u w, B (ρ g u) (ρ g w) = B u w := fun g u w =>
    polar_map_of_mem (hΩO _ (g : Ω).2) u w
  have hplane : planeFixSpace Ã = fixSub ρ ⊤ := planeFixSpace_eq_fixSub Ã
  have hline : ∀ M : Subgroup Ã, lineFixSpace M = fixSub ρ M := lineFixSpace_eq_fixSub
  have hsummand : ∀ i, innerSummand p Ã i = LinearMap.range (lineIdem ρ p i) :=
    innerSummand_eq_range hQ hΓ hpK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hfun : innerSummand p Ã = fun i => LinearMap.range (lineIdem ρ p i) :=
      funext hsummand
    rw [hfun]
    exact isInternal_range_of_orthogonal_idempotents _ (lineIdem_mul_self hΓ hpK)
      (fun i j h => lineIdem_mul_of_ne hp hexp hΓ hpK h) (sum_lineIdem hp hexp hΓ hpK)
  · intro i j hij u hu v hv
    rw [hsummand] at hu hv
    obtain ⟨u', rfl⟩ := hu
    obtain ⟨v', rfl⟩ := hv
    exact lineIdem_orthogonal B hp hexp hΓ hpK hρB hij u' v'
  · intro i
    rw [hsummand]
    exact lineIdem_restrict_nondegenerate B hΓ hpK hρB hBsymm hBnd i
  · intro M hM a haM ha1
    have hMeq : M = Subgroup.zpowers a := eq_zpowers_of_natCard_eq_prime_of_mem hp hexp hM ha1 haM
    refine ⟨?_, ?_⟩
    · ext v
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, hline,
        mem_fixSub]
      constructor
      · intro hv
        let S : Subgroup Ã :=
          { carrier := {d | ρ d v = v}
            mul_mem' := fun {x y} hx hy => by
              change ρ (x * y) v = v
              rw [map_mul, Module.End.mul_apply, show ρ y v = v from hy, show ρ x v = v from hx]
            one_mem' := by
              change ρ 1 v = v
              rw [map_one, Module.End.one_apply]
            inv_mem' := fun {x} hx => by
              change ρ x⁻¹ v = v
              conv_lhs => rw [← show ρ x v = v from hx]
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
                Module.End.one_apply] }
        have hle : M ≤ S := hMeq ▸ (Subgroup.zpowers_le).mpr (show ρ a v = v from hv)
        exact fun d hd => hle hd
      · intro h
        exact h a haM
    · have hMK := card_line_ne_zero (K := K) hM hpK
      apply le_antisymm
      · rw [hline, ← range_avgOp_eq_fixSub hMK]
        have hsum : avgOp ρ M = lineIdem ρ p none + lineIdem ρ p (some ⟨M, hM⟩) := by
          simp only [lineIdem]
          abel
        rw [hsum]
        refine (LinearMap.range_add_le _ _).trans (sup_le_sup ?_ ?_)
        · rw [← hsummand]
          rfl
        · rw [← hsummand]
          rfl
      · refine sup_le ?_ inf_le_left
        rw [hplane, hline]
        exact fun v hv d _ => hv d trivial
  ·
    have : NeZero p := ⟨hp.ne_zero⟩
    have : Finite (Additive Ã →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
    have : Fintype (Additive Ã →+ ZMod p) := Fintype.ofFinite _
    have hDcard : Nat.card (Additive Ã →+ ZMod p) = p ^ 2 := by rw [natCard_char hp hexp, hΓ]
    have hq : ¬p ∣ Nat.card K := by
      obtain ⟨n, -, hn⟩ := FiniteField.card K ℓ
      rw [Nat.card_eq_fintype_card, hn]
      exact fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h))
    have hpL : (p : AlgebraicClosure K) ≠ 0 := by
      rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
      exact (map_ne_zero _).mpr hpK
    have hΓL : (Fintype.card Ã : AlgebraicClosure K) ≠ 0 := by
      rw [← Nat.card_eq_fintype_card, hΓ, Nat.cast_pow]
      exact pow_ne_zero 2 hpL
    have : NeZero (p : K) := ⟨hpK⟩
    obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
    obtain ⟨hfrob, hneg, hcl, hsum, hlines⟩ :=
      orth_bcRep_charSpace_facts hℓ hp hpℓ hQ hexp hΓ (AlgebraicClosure K) hζ₀
    have hS : AddSubgroup.closure {χ : Additive Ã →+ ZMod p | χ ≠ 0 ∧
        finrank (AlgebraicClosure K) (charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ) ≠ 0} = ⊤ := by
      have hset : {χ : Additive Ã →+ ZMod p | χ ≠ 0 ∧
          finrank (AlgebraicClosure K) (charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ) ≠ 0} =
          {χ | χ ≠ 0 ∧ charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ ≠ ⊥} := by
        ext χ
        exact and_congr_right fun _ => not_congr Submodule.finrank_eq_zero
      rw [hset]
      exact hcl
    have hdim : ∀ M : {M : Subgroup Ã // Nat.card M = p}, finrank K (lineSpace M.1) =
        ∑ χ ∈ Finset.univ.filter (fun χ : Additive Ã →+ ZMod p => χ ≠ 0 ∧ charKer χ = M.1),
          finrank (AlgebraicClosure K) (charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ) := by
      intro M
      have h1 := finrank_biSup_of_iSupIndep
        (iSupIndep_charSpace (ρ := bcRep (AlgebraicClosure K) Ã) hζ₀ hΓL)
        (Finset.univ.filter fun χ : Additive Ã →+ ZMod p => χ ≠ 0 ∧ charKer χ = M.1)
      have h2 : (⨆ (χ : Additive Ã →+ ZMod p) (_ : χ ≠ 0 ∧ charKer χ = M.1),
          charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ) =
          ⨆ χ ∈ Finset.univ.filter (fun χ : Additive Ã →+ ZMod p => χ ≠ 0 ∧ charKer χ = M.1),
            charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ :=
        iSup_congr fun χ => iSup_congr_Prop (by rw [Finset.mem_filter]; simp) fun _ => rfl
      rw [← finrank_submodule_baseChange (AlgebraicClosure K), hlines M, h2, h1]
    have hnebot : ∀ χ : Additive Ã →+ ZMod p, χ ≠ 0 →
        charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ ≠ ⊥ → lineSpace (charKer χ) ≠ ⊥ := by
      intro χ hχ hV hbot
      apply hV
      have h1 := hlines ⟨charKer χ, natCard_charKer hp hΓ hχ⟩
      rw [hbot, Submodule.baseChange_bot] at h1
      exact eq_bot_iff.mpr ((le_iSup₂_of_le (f := fun (ψ : Additive Ã →+ ZMod p)
        (_ : ψ ≠ 0 ∧ charKer ψ = charKer χ) => charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ ψ)
        χ ⟨hχ, rfl⟩ le_rfl).trans h1.symm.le)
    refine ⟨?_, ?_, ?_, finrank_zmod_eq_of_natCard hp hDcard, ?_⟩
    · obtain ⟨χ₁, hχ₁, χ₂, hχ₂, hne⟩ := exists_charKer_ne hp hexp hΓ hcl fun χ hχ => hχ.1
      exact ⟨charKer χ₁, charKer χ₂, natCard_charKer hp hΓ hχ₁.1, natCard_charKer hp hΓ hχ₂.1,
        hne, hnebot χ₁ hχ₁.1 hχ₁.2, hnebot χ₂ hχ₂.1 hχ₂.2⟩
    · intro M hM hne
      refine ⟨Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h), ?_⟩
      rw [hdim ⟨M, hM⟩]
      exact lcm_dvd_sum_filter_charKer hp hp2 hΓ hq
        (fun χ => finrank (AlgebraicClosure K) (charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ))
        hfrob hneg M
    · calc 2 * Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 ≤
            ∑ χ : Additive Ã →+ ZMod p,
              finrank (AlgebraicClosure K) (charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ) :=
          two_mul_lcm_le_sum hp hp2 hDcard hq
            (fun χ => finrank (AlgebraicClosure K) (charSpace (bcRep (AlgebraicClosure K) Ã) ζ₀ χ))
            hfrob hneg hS
        _ = finrank K V := hsum
    · intro ζ hζ
      obtain ⟨-, -, hcl', -, hlines'⟩ :=
        orth_bcRep_charSpace_facts hℓ hp hpℓ hQ hexp hΓ (AlgebraicClosure K) hζ
      exact ⟨span_zmod_eq_top_of_closure_eq_top hcl', fun M hM => hlines' ⟨M, hM⟩⟩

end CFSG.RankThree.Classical
