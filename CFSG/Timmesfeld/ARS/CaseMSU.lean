module

public import CFSG.Timmesfeld.ARS.CaseMSp
public import CFSG.Timmesfeld.LieEmbed.UnitaryWitt
public import CFSG.Timmesfeld.ARS.CaseMLevi

public section

namespace CFSG.Timmesfeld.ARS

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Timmesfeld.LieEmbed
open scoped commutatorElement

namespace CaseMSU

theorem commuting_map {K H : Type*} [Group K] [Group H] (Φ : K →* H) {X Y : Subgroup K}
    (h : Commuting X Y) : Commuting (X.map Φ) (Y.map Φ) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (h x hx y hy).map Φ

theorem commutator_mem_center {K H : Type*} [Group K] [Group H] {Φ : K →* H}
    (hker : Φ.ker ≤ Subgroup.center K) {X Y : Subgroup K} (h : Commuting (X.map Φ) (Y.map Φ)) :
    ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ Subgroup.center K := fun x hx y hy => hker (by
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩)

theorem ker_comp_conj_le_center {K H : Type*} [Group K] [Group H] {Φ : K →* H}
    (hker : Φ.ker ≤ Subgroup.center K) (g : K) :
    (Φ.comp (MulAut.conj g).toMonoidHom).ker ≤ Subgroup.center K := by
  intro x hx
  have h1 : (MulAut.conj g).toMonoidHom x ∈ Subgroup.center K := hker hx
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have h2 : g * x * g⁻¹ = x := by
    have := Subgroup.mem_center_iff.1 h1 g
    rw [inv_mul_cancel_right] at this
    exact mul_left_cancel this
  rw [← h2]
  exact h1

set_option maxRecDepth 100000 in
theorem toStd_six_longC3 : ∀ i : Fin 3, Unitary.toStd 6 (CaseM.longC3 i) = 2 • weight 6 (c6 i) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem toStd_six_neg_longC3 :
    ∀ i : Fin 3, Unitary.toStd 6 (-CaseM.longC3 i) = 2 • weight 6 (c6' i) := by
  decide +kernel

theorem c6_ne_rev : ∀ i : Fin 3, c6 i ≠ Fin.rev (c6 i) := by decide

theorem c6'_ne_rev : ∀ i : Fin 3, c6' i ≠ Fin.rev (c6' i) := by decide

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

theorem isUTransGroup_pos (i : Fin 3) :
    IsUTransGroup (unitaryInvolution F p f) (Pi.single (c6 i) 1)
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6
        (CaseM.longC3 i)) :=
  isUTransGroup_rootGroup_long _ (c6 i) (toStd_six_longC3 i)

theorem isUTransGroup_neg (i : Fin 3) :
    IsUTransGroup (unitaryInvolution F p f) (Pi.single (c6' i) 1)
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6
        (-CaseM.longC3 i)) :=
  isUTransGroup_rootGroup_long _ (c6' i) (toStd_six_neg_longC3 i)

theorem isUTransGroup_alpha :
    IsUTransGroup (unitaryInvolution F p f) (Pi.single (c6 2) 1)
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6
        (Pi.single (2 : Fin 3) 1)) := by
  rw [← CaseM.longC3_two]
  exact isUTransGroup_pos hF 2

theorem exists_isUTransGroup_of_mem (g : SU (unitaryInvolution F p f) 6) :
    ∃ v : Fin 6 → F, v ≠ 0 ∧ uForm (unitaryInvolution F p f) v v = 0 ∧
      IsUTransGroup (unitaryInvolution F p f) v (conjSub (Unitary.rootGroup
        (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6 (Pi.single (2 : Fin 3) 1))
          g) :=
  ⟨_, suMat_mulVec_ne_zero _ g (single_one_ne_zero (c6 2)),
    (uForm_mulVec _ g _ _).trans (uForm_single_self (c6_ne_rev 2)),
    (isUTransGroup_alpha hF).conjSub g⟩

theorem exists_aligned {G : Type*} [Group G] (Φ : SU (unitaryInvolution F p f) 6 →* G)
    (hker : Φ.ker ≤ Subgroup.center _) {P Q : Fin 3 → Subgroup G}
    (hP : ∀ i, ∃ g, P i = (conjSub (Unitary.rootGroup (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) 6 (Pi.single (2 : Fin 3) 1)) g).map Φ)
    (hQ : ∀ i, ∃ g, Q i = (conjSub (Unitary.rootGroup (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) 6 (Pi.single (2 : Fin 3) 1)) g).map Φ)
    (hopp : ∀ i, ¬ Commuting (P i) (Q i))
    (hcomm : ∀ i j, i ≠ j → Commuting (P i ⊔ Q i) (P j ⊔ Q j)) :
    ∃ g : SU (unitaryInvolution F p f) 6, ∀ i,
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6
        (CaseM.longC3 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) = P i ∧
      (Unitary.rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) 6
        (-CaseM.longC3 i)).map (Φ.comp (MulAut.conj g).toMonoidHom) = Q i := by
  have hσ : ∀ c, unitaryInvolution F p f (unitaryInvolution F p f c) = c :=
    unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hζ' : (ζ : F) + unitaryInvolution F p f ζ = 0 := ζ.2
  choose h hh using hP
  choose k hk using hQ
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀, X₀ = Unitary.rootGroup (unitaryInvolution F p f)
      (unitaryInvolution_involutive hF) 6 (Pi.single (2 : Fin 3) 1) := ⟨_, rfl⟩
  rw [← hX₀def] at hh hk
  have hX₀ : IsUTransGroup (unitaryInvolution F p f) (Pi.single (c6 2) 1) X₀ :=
    hX₀def ▸ isUTransGroup_alpha hF
  obtain ⟨u, hudef⟩ : ∃ u : Fin 3 → Fin 6 → F,
      u = fun i => suMat _ 6 (h i) *ᵥ Pi.single (c6 2) 1 := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : Fin 3 → Fin 6 → F,
      w = fun i => suMat _ 6 (k i) *ᵥ Pi.single (c6 2) 1 := ⟨_, rfl⟩
  have huT : ∀ i, IsUTransGroup (unitaryInvolution F p f) (u i) (conjSub X₀ (h i)) := fun i => by
    rw [hudef]; exact hX₀.conjSub (h i)
  have hwT : ∀ i, IsUTransGroup (unitaryInvolution F p f) (w i) (conjSub X₀ (k i)) := fun i => by
    rw [hwdef]; exact hX₀.conjSub (k i)
  have hu0 : ∀ i, u i ≠ 0 := fun i => by
    rw [hudef]; exact suMat_mulVec_ne_zero _ (h i) (single_one_ne_zero _)
  have hw0 : ∀ i, w i ≠ 0 := fun i => by
    rw [hwdef]; exact suMat_mulVec_ne_zero _ (k i) (single_one_ne_zero _)
  have huu : ∀ i, uForm (unitaryInvolution F p f) (u i) (u i) = 0 := fun i => by
    rw [hudef]; exact (uForm_mulVec _ _ _ _).trans (uForm_single_self (c6_ne_rev 2))
  have hww : ∀ i, uForm (unitaryInvolution F p f) (w i) (w i) = 0 := fun i => by
    rw [hwdef]; exact (uForm_mulVec _ _ _ _).trans (uForm_single_self (c6_ne_rev 2))
  have hc : ∀ {X Y : Subgroup G}, Commuting X Y →
      ∀ {A B : Subgroup (SU (unitaryInvolution F p f) 6)}, X = A.map Φ → Y = B.map Φ →
        ∀ x ∈ A, ∀ y ∈ B, ⁅x, y⁆ ∈ Subgroup.center _ := fun hXY A B hA hB =>
    commutator_mem_center hker (hA ▸ hB ▸ hXY)
  have hprop : ∀ {v v' : Fin 6 → F} {X Y : Subgroup (SU (unitaryInvolution F p f) 6)},
      IsUTransGroup (unitaryInvolution F p f) v X → IsUTransGroup (unitaryInvolution F p f) v' Y →
        v' ≠ 0 → (∃ l : F, v' = l • v) → Y = X := by
    rintro v v' X Y hX hY hv' ⟨l, rfl⟩
    have hl : l ≠ 0 := fun hl => hv' (by rw [hl, zero_smul])
    exact (hY.of_smul hσ hl).eq hX
  have hBuw : ∀ i, uForm (unitaryInvolution F p f) (u i) (w i) ≠ 0 := fun i hB =>
    hopp i (by rw [hh i, hk i]; exact commuting_map Φ ((huT i).commuting hσ (hwT i) hB))
  have hBuu : ∀ i j, uForm (unitaryInvolution F p f) (u i) (u j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact huu j
    rcases (huT i).uForm_eq_zero_of_center hσ hζ hζ' (huT j) (hu0 i) (huu i) (huu j)
        (hc ((hcomm i j hij).mono le_sup_left le_sup_left) (hh i) (hh j)) with h0 | hl
    · exact h0
    · exfalso
      have hPji : P j = P i := by rw [hh i, hh j, hprop (huT i) (huT j) (hu0 j) hl]
      exact hopp i (by rw [← hPji]; exact ((hcomm i j hij).mono le_sup_right le_sup_left).symm)
  have hBww : ∀ i j, uForm (unitaryInvolution F p f) (w i) (w j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij]; exact hww j
    rcases (hwT i).uForm_eq_zero_of_center hσ hζ hζ' (hwT j) (hw0 i) (hww i) (hww j)
        (hc ((hcomm i j hij).mono le_sup_right le_sup_right) (hk i) (hk j)) with h0 | hl
    · exact h0
    · exfalso
      have hQji : Q j = Q i := by rw [hk i, hk j, hprop (hwT i) (hwT j) (hw0 j) hl]
      exact hopp i (by rw [← hQji]; exact ((hcomm i j hij).mono le_sup_left le_sup_right))
  have hBuw' : ∀ i j, i ≠ j → uForm (unitaryInvolution F p f) (u i) (w j) = 0 := by
    intro i j hij
    rcases (huT i).uForm_eq_zero_of_center hσ hζ hζ' (hwT j) (hu0 i) (huu i) (hww j)
        (hc ((hcomm i j hij).mono le_sup_left le_sup_right) (hh i) (hk j)) with h0 | hl
    · exact h0
    · exfalso
      have hQP : Q j = P i := by rw [hh i, hk j, hprop (huT i) (hwT j) (hw0 j) hl]
      exact hopp j (by rw [hQP]; exact ((hcomm i j hij).mono le_sup_left le_sup_left).symm)
  have hw'T : ∀ i, IsUTransGroup (unitaryInvolution F p f)
      ((uForm (unitaryInvolution F p f) (u i) (w i))⁻¹ • w i) (conjSub X₀ (k i)) := fun i =>
    (hwT i).smul hσ (inv_ne_zero (hBuw i))
  obtain ⟨g, l, hl0, hg⟩ := exists_su6_mulVec hF (P := u)
    (Q := fun i => (uForm (unitaryInvolution F p f) (u i) (w i))⁻¹ • w i) hBuu
    (fun i j => by rw [uForm_smul_left, uForm_smul_right, hBww, mul_zero, mul_zero])
    (fun i j => by
      rw [uForm_smul_right]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, inv_mul_cancel₀ (hBuw i)]
      · rw [ite_eq_right hij, hBuw' i j hij, mul_zero])
  refine ⟨g, fun i => ⟨?_, ?_⟩⟩
  · rw [← Subgroup.map_map, hh i]
    congr 1
    have := (isUTransGroup_pos hF i).conjSub g
    rw [(hg i).1] at this
    have hl' : (if i = 0 then l else 1) ≠ 0 := by
      split_ifs
      exacts [hl0, one_ne_zero]
    exact (this.of_smul hσ hl').eq (huT i)
  · rw [← Subgroup.map_map, hk i]
    congr 1
    have := (isUTransGroup_neg hF i).conjSub g
    rw [(hg i).2] at this
    have hl' : (if i = 0 then (unitaryInvolution F p f l)⁻¹ else 1) ≠ 0 := by
      split_ifs
      exacts [inv_ne_zero ((map_ne_zero _).2 hl0), one_ne_zero]
    exact (this.of_smul hσ hl').eq (hw'T i)

end CaseMSU

variable {G : Type*} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}

theorem Sec12.exists_aligned_su_dict (hS : Sec12 R A A₀) {E C : Subgroup G}
    {P Q : Fin 3 → Subgroup G} (hfr : Sec12.IsSubframe R A A₀ E C P Q) {f : ℕ} (hf : 1 ≤ f)
    (Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →* G)
    (hker : Φ.ker ≤ Subgroup.center _) (hrange : Φ.range = levi R A A₀)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔ ∃ g, X = (conjSub
      ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
        (Pi.single (2 : Fin 3) 1)) g).map Φ) :
    ∃ Φ' : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →* G,
      Φ'.ker ≤ Subgroup.center _ ∧ Φ'.range = levi R A A₀ ∧
      (∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔ ∃ g, X = (conjSub
        ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
          (Pi.single (2 : Fin 3) 1)) g).map Φ') ∧
      (∀ i : Fin 3, ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
        (CaseM.longC3 i)).map Φ' = P i) ∧
      (∀ i : Fin 3, ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
        (-CaseM.longC3 i)).map Φ' = Q i) := by
  obtain ⟨g, hg⟩ := CaseMSU.exists_aligned (CaseM.card_galoisField_two_mul hf) Φ hker
    (fun i => (hΔ (P i)).1 (hfr.memP i).1) (fun i => (hΔ (Q i)).1 (hfr.memQ i).1)
    (fun i => (hfr.opposite i).not_commuting (hS.hyp.root.ne_bot _ (hfr.memP i).1.1.1))
    hfr.commuting
  have e : ∀ (X₀ : Subgroup (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6))
      (g' : Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6),
      (conjSub X₀ g').map (Φ.comp (MulAut.conj g).toMonoidHom) = (conjSub X₀ (g * g')).map Φ :=
    fun X₀ g' => by rw [← Subgroup.map_map, conjSub_mul]
  refine ⟨Φ.comp (MulAut.conj g).toMonoidHom, CaseMSU.ker_comp_conj_le_center hker g, ?_,
    fun X => ?_, fun i => (hg i).1, fun i => (hg i).2⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj g).surjective,
      ← MonoidHom.range_eq_map, hrange]
  · rw [hΔ X]
    constructor
    · rintro ⟨g', rfl⟩
      exact ⟨g⁻¹ * g', by rw [e, mul_inv_cancel_left]⟩
    · rintro ⟨g', rfl⟩
      exact ⟨g * g', by rw [e]⟩

end CFSG.Timmesfeld.ARS
