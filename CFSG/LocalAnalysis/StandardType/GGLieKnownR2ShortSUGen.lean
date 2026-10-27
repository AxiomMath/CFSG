module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSUDefs
public import CFSG.Timmesfeld.Transvection.ModelSUGen
public import CFSG.Timmesfeld.Transvection.ModelSUTransvLe
public import CFSG.Timmesfeld.Transvection.ModelSUTheta

public section

namespace CFSG.StandardType.LieKnownR2.Short

open Matrix CFSG.StandardType CFSG.StandardType.GGOppRadSpU CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary CFSG.QuasithinUnique.B113Lie.Sp CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection.ModelRank

private theorem suH_β_eq_uForm {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (x y : Fin n → F) :
    (suH hc n).β x y = uForm (unitaryInvolution F 2 f) x y := by
  unfold suH
  rw [suForm_β_eq]
  rfl

private theorem suH_symm {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) {n : ℕ} (u v : Fin n → F) :
    (suH hc n).β v u = unitaryInvolution F 2 f ((suH hc n).β u v) := by
  unfold suH
  exact suForm_symm (unitaryInvolution F 2 f) (unitaryInvolution_involutive hc) u v

private theorem suH_σ {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) :
    (suH hc n).σ = unitaryInvolution F 2 f := rfl

private theorem sigma_trace_fixed {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (u : F) :
    unitaryInvolution F 2 f (u + unitaryInvolution F 2 f u) =
      u + unitaryInvolution F 2 f u := by
  rw [map_add, unitaryInvolution_involutive hc]
  ring

private theorem suFrame_pairings {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    (suH hc n).β v w' = 1 ∧ (suH hc n).β w' v = 1 ∧
    (suH hc n).β w v' = 1 ∧ (suH hc n).β v' w = 1 ∧
    (suH hc n).β v v = 0 ∧ (suH hc n).β w w = 0 ∧
    (suH hc n).β v' v' = 0 ∧ (suH hc n).β w' w' = 0 ∧
    (suH hc n).β v w = 0 ∧ (suH hc n).β w v = 0 ∧
    (suH hc n).β v v' = 0 ∧ (suH hc n).β v' v = 0 ∧
    (suH hc n).β w w' = 0 ∧ (suH hc n).β w' w = 0 ∧
    (suH hc n).β v' w' = 0 ∧ (suH hc n).β w' v' = 0 := by
  refine ⟨hfr.1, ?_, hfr.2.1, ?_, hfr.2.2.1.1, hfr.2.2.1.2.1, hfr.2.2.1.2.2.1,
    hfr.2.2.1.2.2.2, hfr.2.2.2.1, ?_, hfr.2.2.2.2.1, ?_, hfr.2.2.2.2.2.1, ?_,
    hfr.2.2.2.2.2.2, ?_⟩
  · rw [suH_symm hc, hfr.1, map_one]
  · rw [suH_symm hc, hfr.2.1, map_one]
  · rw [suH_symm hc, hfr.2.2.2.1, map_zero]
  · rw [suH_symm hc, hfr.2.2.2.2.1, map_zero]
  · rw [suH_symm hc, hfr.2.2.2.2.2.1, map_zero]
  · rw [suH_symm hc, hfr.2.2.2.2.2.2, map_zero]

private noncomputable def suProjW {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hc : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) (v w v' w' : Fin n → F) (y : Fin n → F) :
    Fin n → F :=
  y - (suH hc n).β w' y • v - (suH hc n).β v' y • w -
    (suH hc n).β w y • v' - (suH hc n).β v y • w'

private theorem projW_mem {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') (y : Fin n → F) :
    suProjW hc n v w v' w' y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
  obtain ⟨hvw', hw'v, hwv', hv'w, hvv, hww, hv'v', hw'w', hvw, hwv, hvv', hv'v, hww',
    hw'w, hv'w', hw'v'⟩ := suFrame_pairings hfr
  rw [ReflForm.mem_perp]
  intro f hf
  refine Submodule.span_induction
    (p := fun x _ => (suH hc n).β x (suProjW hc n v w v' w' y) = 0)
    (fun x hx => ?_) ?_ (fun x z _ _ ihx ihz => ?_) (fun a x _ ih => ?_) hf
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [suProjW, (suH hc n).β_sub_right, (suH hc n).smul_right, hvv, hvw, hvv', hvw']
      ring
    · simp only [suProjW, (suH hc n).β_sub_right, (suH hc n).smul_right, hwv, hww, hwv', hww']
      ring
    · simp only [suProjW, (suH hc n).β_sub_right, (suH hc n).smul_right, hv'v, hv'w, hv'v', hv'w']
      ring
    · simp only [suProjW, (suH hc n).β_sub_right, (suH hc n).smul_right, hw'v, hw'w, hw'v', hw'w']
      ring
  · rw [(suH hc n).β_zero_left]
  · rw [(suH hc n).add_left, ihx, ihz, add_zero]
  · rw [(suH hc n).smul_left, ih, mul_zero]

private theorem su_vec_add_self_eq_zero {F : Type} [Field F] [CharP F 2] {n : ℕ}
    (v : Fin n → F) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem su_vec_sub_eq_add {F : Type} [Field F] [CharP F 2] {n : ℕ}
    (v w : Fin n → F) : v - w = v + w := by
  funext i
  exact CharTwo.sub_eq_add (v i) (w i)

private theorem natRep_apply_suMat {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}
    (g : SU σ n) (y : Fin n → F) :
    natRep (SU σ n) g y = suMat σ n g *ᵥ y := by
  rw [natRep_apply]
  rfl

private theorem uTrans_zero_vec {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ} (c : F) :
    uTrans σ (0 : Fin n → F) c = 1 := by
  ext i j
  simp [uTrans, uNil, Matrix.vecMulVec]

private theorem uTransLe_zero {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}
    {L : Subgroup (SU σ n)} : UTransLe L (0 : Fin n → F) := by
  intro c x hc hx
  have h1 : suMat σ n x = 1 := by rw [hx, uTrans_zero_vec]
  have hx1 : x = 1 := suMat_injective σ (by rw [h1, map_one])
  rw [hx1]
  exact L.one_mem

private theorem uTransLe_of_mem_span {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w : Fin n → F}
    (hW : (suH hc n).IsTotallyIsotropic (Submodule.span F {v, w}))
    {L : Subgroup ↥(SU (unitaryInvolution F 2 f) n)}
    (hrad : suStabRad hc n (Submodule.span F {v, w}) hW ≤ L)
    {u : Fin n → F} (hu : u ∈ Submodule.span F {v, w}) : UTransLe L u := by
  intro c x hc' hx
  apply hrad
  unfold suStabRad
  rw [mem_rad]
  constructor
  · intro a ha
    rw [natRep_apply_suMat, hx, uTrans_mulVec]
    have hua : uForm (unitaryInvolution F 2 f) u a = 0 := by
      rw [← suH_β_eq_uForm hc]
      exact (ReflForm.mem_perp (F := suH hc n)).mp (hW ha) u hu
    rw [hua, mul_zero, zero_smul, add_zero]
  · intro y hy
    rw [natRep_apply_suMat, hx, uTrans_mulVec, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hu

theorem suStabRad_sup_suPair_eq_top {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    {hc : Nat.card F = (2 ^ f) ^ 2} {n : ℕ} {v w v' w' : Fin n → F}
    (hfr : SUFrame hc n v w v' w') :
    suStabRad hc n (Submodule.span F {v, w}) (suFrame_isTotallyIsotropic hfr) ⊔
      (suPair (unitaryInvolution F 2 f) n v w ⊔ suPair (unitaryInvolution F 2 f) n v' w') = ⊤ := by
  let A : Submodule F (Fin n → F) := Submodule.span F {v, w}
  let hA : (suH hc n).IsTotallyIsotropic A := suFrame_isTotallyIsotropic hfr
  let L : Subgroup ↥(SU (unitaryInvolution F 2 f) n) :=
    suStabRad hc n A hA ⊔
      (suPair (unitaryInvolution F 2 f) n v w ⊔ suPair (unitaryInvolution F 2 f) n v' w')
  change L = ⊤
  have hrad : suStabRad hc n A hA ≤ L := le_sup_left
  have hpairw' : suPair (unitaryInvolution F 2 f) n v' w' ≤ L :=
    le_sup_right.trans le_sup_right
  have hmemA : ∀ u ∈ A, UTransLe L u := by
    intro u hu
    exact uTransLe_of_mem_span hA hrad hu
  have hmove : ∀ x : Fin n → F, uForm (unitaryInvolution F 2 f) x x = 0 → x ≠ 0 →
      ∃ g ∈ L, natRep (SU (unitaryInvolution F 2 f) n) g x ∈ A := by
    intro x hx hx0
    have hxβ : (suH hc n).β x x = 0 := by rw [suH_β_eq_uForm hc]; exact hx
    obtain ⟨hvw', hw'v, hwv', hv'w, hvv, hww, hv'v', hw'w', hvw, hwv, hvv', hv'v,
      hww', hw'w, hv'w', hw'v'⟩ := suFrame_pairings hfr
    have case1 : ∀ y : Fin n → F, (suH hc n).β y y = 0 →
        ((suH hc n).β v y ≠ 0 ∨ (suH hc n).β w y ≠ 0) →
        ∃ g ∈ L, natRep (SU (unitaryInvolution F 2 f) n) g y ∈ A := by
      intro y hy hyvis
      let β₁ : F := (suH hc n).β w y
      let β₂ : F := (suH hc n).β v y
      let α : Fin n → F := β₁ • v + β₂ • w
      let b : Fin n → F := β₁ • v' + β₂ • w'
      let d : Fin n → F := α + (y - b)
      have hαA : α ∈ A :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have hαperp : α ∈ (suH hc n).perp A := hA hαA
      have hvb : (suH hc n).β v b = (suH hc n).β v y := by
        simp only [b, β₁, β₂, (suH hc n).add_right, (suH hc n).smul_right, hvv', hvw',
          mul_zero, mul_one, add_zero, zero_add]
      have hwb : (suH hc n).β w b = (suH hc n).β w y := by
        simp only [b, β₁, β₂, (suH hc n).add_right, (suH hc n).smul_right, hwv', hww',
          mul_one, mul_zero, add_zero, zero_add]
      have hybperp : y - b ∈ (suH hc n).perp A := by
        rw [ReflForm.mem_perp]
        intro a ha
        refine Submodule.span_induction
          (p := fun a _ => (suH hc n).β a (y - b) = 0)
          (fun a ha => ?_) ?_ (fun a₁ a₂ _ _ ih₁ ih₂ => ?_) (fun c a _ ih => ?_) ha
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl
          · rw [(suH hc n).β_sub_right, hvb, sub_self]
          · rw [(suH hc n).β_sub_right, hwb, sub_self]
        · rw [(suH hc n).β_zero_left]
        · rw [(suH hc n).add_left, ih₁, ih₂, add_zero]
        · rw [(suH hc n).smul_left, ih, mul_zero]
      have hdperp : d ∈ (suH hc n).perp A := by
        change α + (y - b) ∈ (suH hc n).perp A
        exact Submodule.add_mem _ hαperp hybperp
      obtain ⟨x₀, hx0A, hx0y⟩ : ∃ x₀ ∈ A, (suH hc n).β x₀ y = 1 := by
        rcases hyvis with h2 | h1
        · refine ⟨((suH hc n).σ).symm ((suH hc n).β v y)⁻¹ • v, ?_, ?_⟩
          · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
          · rw [(suH hc n).smul_left, RingEquiv.apply_symm_apply, inv_mul_cancel₀ h2]
        · refine ⟨((suH hc n).σ).symm ((suH hc n).β w y)⁻¹ • w, ?_, ?_⟩
          · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
          · rw [(suH hc n).smul_left, RingEquiv.apply_symm_apply, inv_mul_cancel₀ h1]
      have hx0d : (suH hc n).β x₀ d = 0 :=
        (ReflForm.mem_perp (F := suH hc n)).mp hdperp x₀ hx0A
      have hx0self : (suH hc n).β x₀ x₀ = 0 :=
        (ReflForm.mem_perp (F := suH hc n)).mp (hA hx0A) x₀ hx0A
      have hαb : (suH hc n).β α b =
          unitaryInvolution F 2 f β₁ * β₂ + unitaryInvolution F 2 f β₂ * β₁ := by
        simp only [α, b, (suH hc n).add_left, (suH hc n).add_right, (suH hc n).smul_left,
          (suH hc n).smul_right, suH_σ hc, hvv', hvw', hwv', hww']
        ring
      have hαb_fixed : (suH hc n).σ ((suH hc n).β α b) = (suH hc n).β α b := by
        have h1 : (suH hc n).β α b = (unitaryInvolution F 2 f β₁ * β₂) +
            unitaryInvolution F 2 f (unitaryInvolution F 2 f β₁ * β₂) := by
          rw [hαb, map_mul, unitaryInvolution_involutive hc]
          ring
        rw [suH_σ hc, h1, sigma_trace_fixed hc]
      have hαb_trace : (suH hc n).β α b + (suH hc n).σ ((suH hc n).β α b) = 0 := by
        rw [hαb_fixed, CharTwo.add_self_eq_zero]
      have hbb : (suH hc n).β b b = 0 := by
        simp only [b, (suH hc n).add_left, (suH hc n).add_right, (suH hc n).smul_left,
          (suH hc n).smul_right, hv'v', hv'w', hw'v', hw'w', mul_zero, mul_one, add_zero,
          zero_add]
      have hαb_self : (suH hc n).β (α + b) (α + b) = 0 := by
        have e1 : (suH hc n).β (α + b) (α + b) =
            (suH hc n).β α (α + b) + (suH hc n).β b (α + b) :=
          (suH hc n).add_left α b (α + b)
        have e2 : (suH hc n).β α (α + b) =
            (suH hc n).β α α + (suH hc n).β α b := (suH hc n).add_right α α b
        have e3 : (suH hc n).β b (α + b) =
            (suH hc n).β b α + (suH hc n).β b b := (suH hc n).add_right b α b
        rw [e1, e2, e3, hA hαA α hαA, hbb, zero_add, add_zero, suH_symm hc α b]
        exact hαb_trace
      let c : F := (suH hc n).β d y
      have hydx : y + d = α + b := by
        change y + (α + (y - b)) = α + b
        rw [su_vec_sub_eq_add]
        have h : y + (α + (y + b)) = α + (y + y) + b := by abel
        rw [h, su_vec_add_self_eq_zero, add_zero]
      have hdd : c + unitaryInvolution F 2 f c = (suH hc n).β d d := by
        have e1 : (suH hc n).β (y + d) (y + d) =
            (suH hc n).β y (y + d) + (suH hc n).β d (y + d) :=
          (suH hc n).add_left y d (y + d)
        have e2 : (suH hc n).β y (y + d) = (suH hc n).β y y + (suH hc n).β y d :=
          (suH hc n).add_right y y d
        have e3 : (suH hc n).β d (y + d) = (suH hc n).β d y + (suH hc n).β d d :=
          (suH hc n).add_right d y d
        have h1 : (suH hc n).β (y + d) (y + d) =
            unitaryInvolution F 2 f c + c + (suH hc n).β d d := by
          rw [e1, e2, e3, hy, suH_symm hc d y]
          ring
        have h2 : (suH hc n).β (y + d) (y + d) = 0 := by rw [hydx, hαb_self]
        have h3 : unitaryInvolution F 2 f c + c + (suH hc n).β d d = 0 := by rw [← h1, h2]
        rw [add_comm (unitaryInvolution F 2 f c) c] at h3
        rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h3
      obtain ⟨E, hE⟩ := exists_SU_eichler (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hc) hx0self hx0d hdd
      have hE' : ∀ v : Fin n → F, natRep (SU (unitaryInvolution F 2 f) n) E v =
          v + (suH hc n).β x₀ v • (d + c • x₀) + (suH hc n).β d v • x₀ := hE
      have hErad : E ∈ suStabRad hc n A hA := by
        unfold suStabRad
        rw [mem_rad]
        constructor
        · intro a ha
          have hx0a : (suH hc n).β x₀ a = 0 := by
            rw [suH_symm hc a x₀, (ReflForm.mem_perp (F := suH hc n)).mp (hA hx0A) a ha,
              map_zero]
          have hda : (suH hc n).β d a = 0 := by
            rw [suH_symm hc a d, (ReflForm.mem_perp (F := suH hc n)).mp hdperp a ha, map_zero]
          rw [hE' a, hx0a, hda, zero_smul, zero_smul, add_zero, add_zero]
        · intro z hz
          have hx0z : (suH hc n).β x₀ z = 0 :=
            (ReflForm.mem_perp (F := suH hc n)).mp hz x₀ hx0A
          rw [hE' z, hx0z, zero_smul, add_zero, add_sub_cancel_left]
          exact Submodule.smul_mem _ _ hx0A
      have hEy : natRep (SU (unitaryInvolution F 2 f) n) E y = α + b := by
        rw [hE' y, hx0y, one_smul]
        change y + (d + c • x₀) + c • x₀ = α + b
        rw [← add_assoc y d (c • x₀), add_assoc (y + d) (c • x₀) (c • x₀),
          ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero, hydx]
      obtain ⟨T', hT'pair, hT'⟩ := exists_mem_suPair_mulVec hc hv'v' hw'w' hv'w' (1 : F)
      have hT'L : T' ∈ L := hpairw' hT'pair
      have hw'αb : (suH hc n).β w' (α + b) = β₁ := by
        simp only [α, b, β₁, β₂, (suH hc n).add_left, (suH hc n).add_right,
          (suH hc n).smul_left, (suH hc n).smul_right, hw'v, hw'w, hw'v', hw'w', mul_zero,
          mul_one, add_zero, zero_add]
      have hv'αb : (suH hc n).β v' (α + b) = β₂ := by
        simp only [α, b, β₁, β₂, (suH hc n).add_left, (suH hc n).add_right,
          (suH hc n).smul_left, (suH hc n).smul_right, hv'v, hv'w, hv'v', hv'w', mul_zero,
          mul_one, add_zero, zero_add]
      have hT'αb : natRep (SU (unitaryInvolution F 2 f) n) T' (α + b) = α := by
        rw [hT' (α + b), hw'αb, hv'αb, one_mul, map_one, one_mul]
        rw [add_assoc (α + b) (β₁ • v') (β₂ • w')]
        change (α + b) + b = α
        rw [add_assoc, su_vec_add_self_eq_zero b, add_zero]
      refine ⟨T' * E, L.mul_mem hT'L (hrad hErad), ?_⟩
      rw [map_mul, Module.End.mul_apply, hEy, hT'αb]
      exact hαA
    have case2 : ∀ y : Fin n → F, (suH hc n).β y y = 0 → (suH hc n).β v y = 0 →
        (suH hc n).β w y = 0 → ((suH hc n).β v' y ≠ 0 ∨ (suH hc n).β w' y ≠ 0) →
        ∃ g ∈ L, natRep (SU (unitaryInvolution F 2 f) n) g y ∈ A := by
      intro y hy hyv hyw hyvis
      obtain ⟨T', hT'pair, hT'⟩ := exists_mem_suPair_mulVec hc hv'v' hw'w' hv'w' (1 : F)
      have hT'L : T' ∈ L := hpairw' hT'pair
      let z : Fin n → F := natRep (SU (unitaryInvolution F 2 f) n) T' y
      have hzv : (suH hc n).β v z = (suH hc n).β v' y := by
        change (suH hc n).β v (natRep (SU (unitaryInvolution F 2 f) n) T' y) = _
        rw [hT' y]
        simp only [(suH hc n).add_right, (suH hc n).smul_right, hyv, hvv', hvw', mul_zero,
          mul_one, map_one, one_mul, zero_add, add_zero]
      have hzw : (suH hc n).β w z = (suH hc n).β w' y := by
        change (suH hc n).β w (natRep (SU (unitaryInvolution F 2 f) n) T' y) = _
        rw [hT' y]
        simp only [(suH hc n).add_right, (suH hc n).smul_right, hyw, hwv', hww', mul_zero,
          mul_one, map_one, one_mul, zero_add, add_zero]
      have hzvis : (suH hc n).β v z ≠ 0 ∨ (suH hc n).β w z ≠ 0 := by
        rcases hyvis with h | h
        · exact Or.inl (by rw [hzv]; exact h)
        · exact Or.inr (by rw [hzw]; exact h)
      have hzβ : (suH hc n).β z z = 0 := by
        have h : (suH hc n).β (natRep (SU (unitaryInvolution F 2 f) n) T' y)
            (natRep (SU (unitaryInvolution F 2 f) n) T' y) = (suH hc n).β y y :=
          isIsometric_natRep_SU (unitaryInvolution F 2 f)
            (unitaryInvolution_involutive hc) n T' y y
        rw [hy] at h
        exact h
      obtain ⟨g, hgL, hgz⟩ := case1 z hzβ hzvis
      refine ⟨g * T', L.mul_mem hgL hT'L, ?_⟩
      rw [map_mul, Module.End.mul_apply]
      exact hgz
    have case3 : ∀ y : Fin n → F, (suH hc n).β y y = 0 → (suH hc n).β v y = 0 →
        (suH hc n).β w y = 0 → (suH hc n).β v' y = 0 → (suH hc n).β w' y = 0 →
        y ≠ 0 → ∃ g ∈ L, natRep (SU (unitaryInvolution F 2 f) n) g y ∈ A := by
      intro y hy hyv hyw hyv' hyw' hy0
      have hyW : y ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := by
        rw [ReflForm.mem_perp]
        intro a ha
        refine Submodule.span_induction
          (p := fun a _ => (suH hc n).β a y = 0)
          (fun a ha => ?_) ?_ (fun a₁ a₂ _ _ ih₁ ih₂ => ?_) (fun c a _ ih => ?_) ha
        · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · exact hyv
          · exact hyw
          · exact hyv'
          · exact hyw'
        · rw [(suH hc n).β_zero_left]
        · rw [(suH hc n).add_left, ih₁, ih₂, add_zero]
        · rw [(suH hc n).smul_left, ih, mul_zero]
      obtain ⟨u₀, hu₀⟩ :=
        CFSG.QuasithinUnique.B113Lie.Sp.exists_β_eq_one (F := suH hc n) hy0
      let d : Fin n → F := suProjW hc n v w v' w' u₀
      have hdW : d ∈ (suH hc n).perp (Submodule.span F {v, w, v', w'}) := projW_mem hfr u₀
      have hyv0 : (suH hc n).β y v = 0 := by rw [suH_symm hc v y, hyv, map_zero]
      have hyw0 : (suH hc n).β y w = 0 := by rw [suH_symm hc w y, hyw, map_zero]
      have hyv0' : (suH hc n).β y v' = 0 := by rw [suH_symm hc v' y, hyv', map_zero]
      have hyw0' : (suH hc n).β y w' = 0 := by rw [suH_symm hc w' y, hyw', map_zero]
      have hyd : (suH hc n).β y d = 1 := by
        have h : (suH hc n).β y d = (suH hc n).β y u₀ := by
          simp only [d, suProjW, (suH hc n).β_sub_right, (suH hc n).smul_right, hyv0, hyw0,
            hyv0', hyw0', mul_zero, sub_zero]
        rw [h, hu₀]
      have hdd_fixed : unitaryInvolution F 2 f ((suH hc n).β d d) = (suH hc n).β d d :=
        (suH_symm hc d d).symm
      obtain ⟨c, hcE⟩ := exists_add_unitaryInvolution_eq hc hdd_fixed
      obtain ⟨E, hE⟩ := exists_SU_eichler (unitaryInvolution F 2 f)
        (unitaryInvolution_involutive hc) hvv (hdW v (Submodule.subset_span (by simp))) hcE
      have hE' : ∀ w : Fin n → F, natRep (SU (unitaryInvolution F 2 f) n) E w =
          w + (suH hc n).β v w • (d + c • v) + (suH hc n).β d w • v := hE
      have hErad : E ∈ suStabRad hc n A hA := by
        unfold suStabRad
        rw [mem_rad]
        constructor
        · intro a ha
          have hva : (suH hc n).β v a = 0 :=
            (ReflForm.mem_perp (F := suH hc n)).mp (hA ha) v
              (Submodule.subset_span (by simp))
          have ha' : a ∈ Submodule.span F {v, w, v', w'} := by
            refine Submodule.span_mono ?_ ha
            intro x hx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
            tauto
          have hda : (suH hc n).β d a = 0 := by
            rw [suH_symm hc a d, (ReflForm.mem_perp (F := suH hc n)).mp hdW a ha', map_zero]
          rw [hE' a, hva, hda, zero_smul, zero_smul, add_zero, add_zero]
        · intro z hz
          have hvz : (suH hc n).β v z = 0 :=
            (ReflForm.mem_perp (F := suH hc n)).mp hz v (Submodule.subset_span (by simp))
          rw [hE' z, hvz, zero_smul, add_zero, add_sub_cancel_left]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      have hEy : natRep (SU (unitaryInvolution F 2 f) n) E y = y + v := by
        rw [hE' y, hyv, zero_smul, add_zero]
        have hdy : (suH hc n).β d y = 1 := by rw [suH_symm hc y d, hyd, map_one]
        rw [hdy, one_smul]
      let z : Fin n → F := natRep (SU (unitaryInvolution F 2 f) n) E y
      have hzv : (suH hc n).β v z = 0 := by
        change (suH hc n).β v (natRep (SU (unitaryInvolution F 2 f) n) E y) = 0
        rw [hEy, (suH hc n).add_right, hyv, hvv, add_zero]
      have hzw : (suH hc n).β w z = 0 := by
        change (suH hc n).β w (natRep (SU (unitaryInvolution F 2 f) n) E y) = 0
        rw [hEy, (suH hc n).add_right, hyw, hwv, add_zero]
      have hzv' : (suH hc n).β v' z = 0 := by
        change (suH hc n).β v' (natRep (SU (unitaryInvolution F 2 f) n) E y) = 0
        rw [hEy, (suH hc n).add_right, hyv', hv'v, add_zero]
      have hzw' : (suH hc n).β w' z = 1 := by
        change (suH hc n).β w' (natRep (SU (unitaryInvolution F 2 f) n) E y) = 1
        rw [hEy, (suH hc n).add_right, hyw', hw'v, zero_add]
      have hzβ : (suH hc n).β z z = 0 := by
        have h : (suH hc n).β (natRep (SU (unitaryInvolution F 2 f) n) E y)
            (natRep (SU (unitaryInvolution F 2 f) n) E y) = (suH hc n).β y y :=
          isIsometric_natRep_SU (unitaryInvolution F 2 f)
            (unitaryInvolution_involutive hc) n E y y
        rw [hy] at h
        exact h
      obtain ⟨g, hgL, hgz⟩ :=
        case2 z hzβ hzv hzw (Or.inr (by rw [hzw']; exact one_ne_zero))
      refine ⟨g * E, L.mul_mem hgL (hrad hErad), ?_⟩
      rw [map_mul, Module.End.mul_apply]
      exact hgz
    by_cases hvis : (suH hc n).β v x ≠ 0 ∨ (suH hc n).β w x ≠ 0
    · exact case1 x hxβ hvis
    · push Not at hvis
      obtain ⟨hvx0, hwx0⟩ := hvis
      by_cases hvis' : (suH hc n).β v' x ≠ 0 ∨ (suH hc n).β w' x ≠ 0
      · exact case2 x hxβ hvx0 hwx0 hvis'
      · push Not at hvis'
        obtain ⟨hv'x0, hw'x0⟩ := hvis'
        exact case3 x hxβ hvx0 hwx0 hv'x0 hw'x0 hx0
  apply eq_top_of_forall_isUTransGroup_le hc (four_le_of_suFrame hfr)
  intro x X hx hX
  rw [← uTransLe_iff hX]
  by_cases hx0 : x = 0
  · rw [hx0]
    exact uTransLe_zero
  · obtain ⟨g, hgL, hgx⟩ := hmove x hx hx0
    have h1 : UTransLe L (natRep (SU (unitaryInvolution F 2 f) n) g x) := hmemA _ hgx
    have h2 := uTransLe_conj h1 (L.inv_mem hgL)
    rw [natRep_apply_suMat] at h2
    rwa [show suMat (unitaryInvolution F 2 f) n g⁻¹ *ᵥ
          (suMat (unitaryInvolution F 2 f) n g *ᵥ x) = x by
        rw [mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, one_mulVec]] at h2

end CFSG.StandardType.LieKnownR2.Short
