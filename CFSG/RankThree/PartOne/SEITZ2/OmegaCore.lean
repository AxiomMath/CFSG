module

public import CFSG.RankThree.PartOne.SEITZ2.OmegaFrame
public import CFSG.RankThree.PartOne.SEITZ2.OmegaDickson
public import CFSG.ClassicalGroups.Orthogonal.RootCenters

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Rationality

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {b c : K} {F : OmegaFrame Q b c} {k : Subfield K}

theorem OmegaFrame.isRat_eichler (hb : b ∈ k) {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0)
    (hΦ : ∀ x y, F.IsRat k x → F.IsRat k y → Phi Q u w x y ∈ k) {v : V} (hv : F.IsRat k v) :
    F.IsRat k (eichler Q u w v) := by
  have hbi : b⁻¹ ∈ k := k.inv_mem hb
  rw [eichler_ts_apply hu hw huw]
  intro α
  rcases α with i | i | s
  · have h := hΦ v (F.f i) hv (F.isRat_f i)
    have : F.coef (v + polar Q v u • w + polar Q v w • u) (Sum.inl i) =
        F.coef v (Sum.inl i) + Phi Q u w v (F.f i) := by
      simp only [OmegaFrame.coef, Sum.elim_inl, polar_add_left, polar_smul_left_eq, Phi]
      rw [polar_comm Q w (F.f i), polar_comm Q u (F.f i)]
      ring
    rw [this]
    exact k.add_mem (hv _) h
  · have h := hΦ v (F.e i) hv (F.isRat_e i)
    have : F.coef (v + polar Q v u • w + polar Q v w • u) (Sum.inr (Sum.inl i)) =
        F.coef v (Sum.inr (Sum.inl i)) + Phi Q u w v (F.e i) := by
      simp only [OmegaFrame.coef, Sum.elim_inl, Sum.elim_inr, polar_add_left,
        polar_smul_left_eq, Phi]
      rw [polar_comm Q w (F.e i), polar_comm Q u (F.e i)]
      ring
    rw [this]
    exact k.add_mem (hv _) h
  · revert s
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have h := hΦ v (F.t 1) hv (F.isRat_t 1)
      have : F.coef (v + polar Q v u • w + polar Q v w • u) (Sum.inr (Sum.inr 0)) =
          F.coef v (Sum.inr (Sum.inr 0)) + b⁻¹ * Phi Q u w v (F.t 1) := by
        simp only [OmegaFrame.coef, Sum.elim_inr, polar_add_left,
          polar_smul_left_eq, Phi, Matrix.cons_val_zero]
        rw [polar_comm Q w (F.t 1), polar_comm Q u (F.t 1)]
        ring
      rw [this]
      exact k.add_mem (hv _) (k.mul_mem hbi h)
    · have h := hΦ v (F.t 0) hv (F.isRat_t 0)
      have : F.coef (v + polar Q v u • w + polar Q v w • u) (Sum.inr (Sum.inr 1)) =
          F.coef v (Sum.inr (Sum.inr 1)) + b⁻¹ * Phi Q u w v (F.t 0) := by
        simp only [OmegaFrame.coef, Sum.elim_inr, polar_add_left,
          polar_smul_left_eq, Phi, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [polar_comm Q w (F.t 0), polar_comm Q u (F.t 0)]
        ring
      rw [this]
      exact k.add_mem (hv _) (k.mul_mem hbi h)

end Rationality

section Data

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {b c : K}

structure RatGroupData (F : OmegaFrame Q b c) (k : Subfield K)
    (Rat : Subgroup (V ≃ₗ[K] V)) : Prop where
  le_elementary : Rat ≤ elementaryGroup Q
  eichler_mem : ∀ u w, F.IsRat k u → F.IsRat k w → Q u = 0 → polar Q u w = 0 →
    eichler Q u w ∈ Rat
  mem_of_rat : ∀ X ∈ elementaryGroup Q, (∀ v, F.IsRat k v → F.IsRat k (X v)) → X ∈ Rat
  le_closure : ∀ X ∈ Rat, X ∈ Subgroup.closure {Y | ∃ u w, F.IsRat k u ∧ F.IsRat k w ∧
    Q u = 0 ∧ Q w = 0 ∧ polar Q u w = 0 ∧ eichler Q u w = Y}
  trans : ∀ x y, F.IsRat k x → F.IsRat k y → Q x = 0 → Q y = 0 → polar Q x y = 0 → x ≠ 0 →
    (∀ a : K, y ≠ a • x) → ∃ r ∈ Rat, r x = F.e 0 ∧ ∃ a : K, r y = a • F.e 0 + F.e 1

end Data

section Steps

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {b c : K} {F : OmegaFrame Q b c} {k : Subfield K}
  {Rat : Subgroup (V ≃ₗ[K] V)}

theorem OmegaFrame.finite [Finite K] (F : OmegaFrame Q b c) : Finite V :=
  Finite.of_surjective (fun a : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K => ∑ α, a α • F.vec α)
    fun v => ⟨F.coef v, (F.expand' v).symm⟩

theorem exists_rat_pair_not_mem [Finite K] (R : RatGroupData F k Rat) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hne : Rat.map (MulAut.conj g).toMonoidHom ≠ Rat) :
    ∃ u w, F.IsRat k u ∧ F.IsRat k w ∧ Q u = 0 ∧ Q w = 0 ∧ polar Q u w = 0 ∧
      eichler Q (g u) (g w) ∉ Rat := by
  by_contra hall
  push Not at hall
  apply hne
  have key : ∀ X ∈ Subgroup.closure {Y | ∃ u w, F.IsRat k u ∧ F.IsRat k w ∧ Q u = 0 ∧ Q w = 0 ∧
      polar Q u w = 0 ∧ eichler Q u w = Y}, (MulAut.conj g).toMonoidHom X ∈ Rat := by
    intro X hX'
    induction hX' using Subgroup.closure_induction with
    | mem Y hY =>
      obtain ⟨u, w, hu, hw, hQu, hQw, huw, rfl⟩ := hY
      show g * eichler Q u w * g⁻¹ ∈ Rat
      rw [eichler_conj hg]
      exact hall u w hu hw hQu hQw huw
    | one =>
      rw [map_one]
      exact Rat.one_mem
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact Rat.mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact Rat.inv_mem hx
  have hle : Rat.map (MulAut.conj g).toMonoidHom ≤ Rat := by
    rintro _ ⟨X, hX, rfl⟩
    exact key X (R.le_closure X hX)
  have : Finite V := F.finite
  have : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun f : V ≃ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem exists_good_line [Finite K] [CharP K 2] (hb : b ∈ k) (hc : c ∈ k)
    (R : RatGroupData F k Rat) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hne : Rat.map (MulAut.conj g).toMonoidHom ≠ Rat) :
    ∃ u' w' x y : V, Q u' = 0 ∧ Q w' = 0 ∧ polar Q u' w' = 0 ∧
      (∀ t ∈ k, eichler Q u' (t • w') ∈ Rat.map (MulAut.conj g).toMonoidHom) ∧
      F.IsRat k x ∧ F.IsRat k y ∧ Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 0 ∧
      Phi Q u' w' x y ∉ k := by
  obtain ⟨u, w, hu, hw, hQu, hQw, huw, hnot⟩ := exists_rat_pair_not_mem R hg hne
  have hQu' : Q (g u) = 0 := by rw [map_of_mem hg, hQu]
  have hQw' : Q (g w) = 0 := by rw [map_of_mem hg, hQw]
  have huw' : polar Q (g u) (g w) = 0 := by rw [polar_map_of_mem hg, huw]
  refine ⟨g u, g w, ?_⟩
  by_cases hcon : ∃ x y, F.IsRat k x ∧ F.IsRat k y ∧ Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 0 ∧
      Phi Q (g u) (g w) x y ∉ k
  · obtain ⟨x, y, hx, hy, hQx, hQy, hxy, hΦ⟩ := hcon
    refine ⟨x, y, hQu', hQw', huw', ?_, hx, hy, hQx, hQy, hxy, hΦ⟩
    intro t ht
    have h1 : eichler Q (g u) (t • g w) = g * eichler Q u (t • w) * g⁻¹ := by
      rw [eichler_conj hg, map_smul]
    rw [h1]
    exact ⟨eichler Q u (t • w), R.eichler_mem u (t • w) hu (hw.smul ht) hQu
      (by rw [polar_smul_right_eq, huw, mul_zero]), rfl⟩
  · exfalso
    push Not at hcon
    have hfr := phi_frame_mem (F := F) hb hc huw' hcon
    exact hnot (R.mem_of_rat _ (eichler_mem_elementaryGroup Q _ _) fun v hv =>
      F.isRat_eichler hb hQu' hQw' huw' (fun x y hx hy => Phi_mem_of_frame (F := F) _ _ hfr hx hy)
        hv)

theorem eichler_std_conj {r : V ≃ₗ[K] V} (hr : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {x y e e' : V} (hx : Q x = 0) {a : K} (hrx : r x = e) (hry : r y = a • e + e') (t : K) :
    eichler Q e (t • e') = r * eichler Q x (t • y) * r⁻¹ := by
  have hQe : Q e = 0 := by rw [← hrx, map_of_mem hr, hx]
  rw [eichler_conj hr, hrx, map_smul, hry]
  have : t • (a • e + e') = t • e' + (t * a) • e := by module
  rw [this, eichler_add_smul_self hQe]

theorem std_full [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) (hk4 : 4 ∣ Nat.card k) (hb : b ∈ k)
    (hc : c ∈ k)
    (R : RatGroupData F k Rat) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hne : Rat.map (MulAut.conj g).toMonoidHom ≠ Rat) (t : K) :
    eichler Q (F.e 0) (t • F.e 1) ∈
      Subgroup.closure ((Rat : Set (V ≃ₗ[K] V)) ∪
        (Rat.map (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[K] V))) := by
  set M := Subgroup.closure ((Rat : Set (V ≃ₗ[K] V)) ∪
    (Rat.map (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[K] V))) with hMdef
  obtain ⟨u', w', x, y, hQu', hQw', huw', hMu, hx, hy, hQx, hQy, hxy, hΦ⟩ :=
    exists_good_line hb hc R hg hne
  have hRM : ∀ X ∈ Rat, X ∈ M := fun X hX => Subgroup.subset_closure (Or.inl hX)
  have hM₁ : ∀ t ∈ k, eichler Q x (t • y) ∈ M := fun t ht =>
    hRM _ (R.eichler_mem x (t • y) hx (hy.smul ht) hQx
      (by rw [polar_smul_right_eq, hxy, mul_zero]))
  have hM₂ : ∀ t ∈ k, eichler Q u' (t • w') ∈ M := fun t ht =>
    Subgroup.subset_closure (Or.inr (hMu t ht))
  have hfull := fullRoot_of_pairing hp hp2 hK hk4 hQx hQy hxy hQu' hQw' huw' hΦ hM₁ hM₂
  have hx0 : x ≠ 0 := fun h0 => hΦ (by
    have : Phi Q u' w' x y = 0 := by
      simp [Phi, h0, polar_zero_left]
    rw [this]
    exact k.zero_mem)
  have hy' : ∀ a : K, y ≠ a • x := fun a h => hΦ (by
    have : Phi Q u' w' x y = 0 := by
      rw [h, Phi_smul_right, Phi_self, mul_zero]
    rw [this]
    exact k.zero_mem)
  obtain ⟨r, hrR, hrx, a, hry⟩ := R.trans x y hx hy hQx hQy hxy hx0 hy'
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (R.le_elementary hrR)
  rw [eichler_std_conj hrO hQx hrx hry t]
  exact M.mul_mem (M.mul_mem (hRM _ hrR) (hfull t)) (M.inv_mem (hRM _ hrR))

theorem isRootCenter_of_span6 {M : Subgroup (V ≃ₗ[K] V)} {a₀ : V} (ha₀ : a₀ ≠ 0) (hQa : Q a₀ = 0)
    (X : Fin 6 → V) (hX : ∀ j, polar Q a₀ (X j) = 0)
    (hfull : ∀ j (t : K), eichler Q a₀ (t • X j) ∈ M)
    (hdec : ∀ w, polar Q a₀ w = 0 → ∃ (α : K) (β : Fin 6 → K), w = α • a₀ + ∑ j, β j • X j) :
    IsRootCenter Q M a₀ := by
  refine IsRootCenter.of_span ha₀ hQa
    {v | (∃ (t : K) (j : Fin 6), v = t • X j) ∨ ∃ t : K, v = t • a₀} ?_ ?_
  · rintro v (⟨t, j, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨by rw [polar_smul_right_eq, hX, mul_zero], hfull j t⟩
    · refine ⟨by rw [polar_smul_right_eq, polar_self_eq_zero hQa, mul_zero], ?_⟩
      have := eichler_add_smul_self hQa 0 t
      rw [zero_add, eichler_zero_right] at this
      rw [this]
      exact M.one_mem
  · intro w hw
    obtain ⟨α, β, rfl⟩ := hdec w hw
    refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure (Or.inl (Or.inr ⟨α, rfl⟩))) ?_
    exact AddSubgroup.sum_mem _ fun j _ =>
      AddSubgroup.subset_closure (Or.inl (Or.inl ⟨β j, j, rfl⟩))

@[expose] def OmegaFrame.six (F : OmegaFrame Q b c) : Fin 6 → V :=
  ![F.e 1, F.e 2, F.f 1, F.f 2, F.tau 0, F.tau 1]

theorem OmegaFrame.six_Q [CharP K 2] (j : Fin 6) : Q (F.six j) = 0 := by
  fin_cases j <;> simp [OmegaFrame.six, F.Q_e, F.Q_f, F.tau_Q]

theorem OmegaFrame.six_isRat [CharP K 2] (hc : c ∈ k) (j : Fin 6) : F.IsRat k (F.six j) := by
  fin_cases j
  · exact F.isRat_e 1
  · exact F.isRat_e 2
  · exact F.isRat_f 1
  · exact F.isRat_f 2
  · exact F.tau_isRat hc 0
  · exact F.tau_isRat hc 1

theorem OmegaFrame.polar_e0_six (j : Fin 6) : polar Q (F.e 0) (F.six j) = 0 := by
  fin_cases j
  · simp [OmegaFrame.six, F.polar_ee]
  · simp [OmegaFrame.six, F.polar_ee]
  · simp [OmegaFrame.six, F.polar_ef]
  · simp [OmegaFrame.six, F.polar_ef]
  · exact F.polar_e_tau 0 (by decide) 0
  · exact F.polar_e_tau 0 (by decide) 1

theorem OmegaFrame.polar_f0_six (j : Fin 6) : polar Q (F.f 0) (F.six j) = 0 := by
  fin_cases j
  · simp [OmegaFrame.six, F.polar_fe]
  · simp [OmegaFrame.six, F.polar_fe]
  · simp [OmegaFrame.six, F.polar_ff]
  · simp [OmegaFrame.six, F.polar_ff]
  · exact F.polar_f_tau 0 (by decide) 0
  · exact F.polar_f_tau 0 (by decide) 1

@[expose] def OmegaFrame.zt (F : OmegaFrame Q b c) : Fin 6 → V :=
  ![F.f 1, F.f 2, F.e 1, F.e 2, F.e 1, F.e 1]

theorem OmegaFrame.polar_zt_six (j : Fin 6) : polar Q (F.zt j) (F.six j) = 1 := by
  fin_cases j
  · simp [OmegaFrame.zt, OmegaFrame.six, F.polar_fe]
  · simp [OmegaFrame.zt, OmegaFrame.six, F.polar_fe]
  · simp [OmegaFrame.zt, OmegaFrame.six, F.polar_ef]
  · simp [OmegaFrame.zt, OmegaFrame.six, F.polar_ef]
  · exact F.polar_e1_tau 0
  · exact F.polar_e1_tau 1

theorem OmegaFrame.polar_zt_e0 (j : Fin 6) : polar Q (F.zt j) (F.e 0) = 0 := by
  fin_cases j <;> simp [OmegaFrame.zt, F.polar_fe, F.polar_ee]

theorem OmegaFrame.polar_zt_f0 (j : Fin 6) : polar Q (F.zt j) (F.f 0) = 0 := by
  fin_cases j <;> simp [OmegaFrame.zt, F.polar_ff, F.polar_ef]

theorem OmegaFrame.perp_decomp_e0 (w : V) (hw : polar Q (F.e 0) w = 0) :
    ∃ (α : K) (β : Fin 6 → K), w = α • F.e 0 + ∑ j, β j • F.six j := by
  have hB0 : polar Q w (F.e 0) = 0 := by rw [polar_comm]; exact hw
  refine ⟨polar Q w (F.f 0), ![polar Q w (F.f 1) - b⁻¹ * polar Q w (F.t 1) -
    b⁻¹ * polar Q w (F.t 0) * c, polar Q w (F.f 2), polar Q w (F.e 1) - b⁻¹ * polar Q w (F.t 1) -
    b⁻¹ * polar Q w (F.t 0), polar Q w (F.e 2), b⁻¹ * polar Q w (F.t 1),
    b⁻¹ * polar Q w (F.t 0)], ?_⟩
  conv_lhs => rw [F.expand w]
  simp only [Fin.sum_univ_three, Fin.sum_univ_six, OmegaFrame.six, OmegaFrame.tau, hB0,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  module

theorem OmegaFrame.perp_decomp_f0 (w : V) (hw : polar Q (F.f 0) w = 0) :
    ∃ (α : K) (β : Fin 6 → K), w = α • F.f 0 + ∑ j, β j • F.six j := by
  have hA0 : polar Q w (F.f 0) = 0 := by rw [polar_comm]; exact hw
  refine ⟨polar Q w (F.e 0), ![polar Q w (F.f 1) - b⁻¹ * polar Q w (F.t 1) -
    b⁻¹ * polar Q w (F.t 0) * c, polar Q w (F.f 2), polar Q w (F.e 1) - b⁻¹ * polar Q w (F.t 1) -
    b⁻¹ * polar Q w (F.t 0), polar Q w (F.e 2), b⁻¹ * polar Q w (F.t 1),
    b⁻¹ * polar Q w (F.t 0)], ?_⟩
  conv_lhs => rw [F.expand w]
  simp only [Fin.sum_univ_three, Fin.sum_univ_six, OmegaFrame.six, OmegaFrame.tau, hA0,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  module

theorem full_all {M : Subgroup (V ≃ₗ[K] V)} (R : RatGroupData F k Rat) (hRM : Rat ≤ M)
    (hstd : ∀ t : K, eichler Q (F.e 0) (t • F.e 1) ∈ M) {x y : V} (hx : F.IsRat k x)
    (hy : F.IsRat k y) (hQx : Q x = 0) (hQy : Q y = 0) (hxy : polar Q x y = 0) (hx0 : x ≠ 0)
    (hya : ∀ a : K, y ≠ a • x) (t : K) : eichler Q x (t • y) ∈ M := by
  obtain ⟨r, hrR, hrx, a, hry⟩ := R.trans x y hx hy hQx hQy hxy hx0 hya
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (R.le_elementary hrR)
  have h := eichler_std_conj hrO hQx hrx hry t
  have h' : eichler Q x (t • y) = r⁻¹ * eichler Q (F.e 0) (t • F.e 1) * r := by
    calc eichler Q x (t • y) = r⁻¹ * (r * eichler Q x (t • y) * r⁻¹) * r := by group
      _ = r⁻¹ * eichler Q (F.e 0) (t • F.e 1) * r := by rw [← h]
  rw [h']
  exact M.mul_mem (M.mul_mem (M.inv_mem (hRM hrR)) (hstd t)) (hRM hrR)

theorem core_pair [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = Nat.card k ^ p) (hk4 : 4 ∣ Nat.card k) (hb : b ∈ k)
    (hc : c ∈ k)
    (hQnd : (polarBilin Q).Nondegenerate) (R : RatGroupData F k Rat) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hne : Rat.map (MulAut.conj g).toMonoidHom ≠ Rat) :
    Subgroup.closure ((Rat : Set (V ≃ₗ[K] V)) ∪
      (Rat.map (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[K] V))) = elementaryGroup Q := by
  set M := Subgroup.closure ((Rat : Set (V ≃ₗ[K] V)) ∪
    (Rat.map (MulAut.conj g).toMonoidHom : Set (V ≃ₗ[K] V))) with hMdef
  have hRM : Rat ≤ M := fun X hX => Subgroup.subset_closure (Or.inl hX)
  have hMle : M ≤ elementaryGroup Q := by
    rw [hMdef, Subgroup.closure_le]
    rintro _ (hX | ⟨X, hX, rfl⟩)
    · exact R.le_elementary hX
    · exact conj_mem_elementaryGroup hg (R.le_elementary hX)
  refine le_antisymm hMle ?_
  have hMO : M ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hMle.trans (elementaryGroup_le_orthogonalGroup Q)
  have hstd : ∀ t : K, eichler Q (F.e 0) (t • F.e 1) ∈ M := fun t =>
    std_full hp hp2 hK hk4 hb hc R hg hne t
  have he00 : F.e 0 ≠ 0 := fun h0 => by
    have := F.polar_ef 0 0
    rw [h0, polar_zero_left] at this
    simp at this
  have hf00 : F.f 0 ≠ 0 := fun h0 => by
    have := F.polar_ef 0 0
    rw [h0, polar_zero_right] at this
    simp at this
  have he0 : IsRootCenter Q M (F.e 0) :=
    isRootCenter_of_span6 he00 (F.Q_e 0) F.six F.polar_e0_six
      (fun j t => full_all R hRM hstd (F.isRat_e 0) (F.six_isRat hc j) (F.Q_e 0) (F.six_Q j)
        (F.polar_e0_six j) he00 (fun a h => by
          have := F.polar_zt_six j
          rw [h, polar_smul_right_eq, F.polar_zt_e0, mul_zero] at this
          exact zero_ne_one this) t)
      F.perp_decomp_e0
  have hf0 : IsRootCenter Q M (F.f 0) :=
    isRootCenter_of_span6 hf00 (F.Q_f 0) F.six F.polar_f0_six
      (fun j t => full_all R hRM hstd (F.isRat_f 0) (F.six_isRat hc j) (F.Q_f 0) (F.six_Q j)
        (F.polar_f0_six j) hf00 (fun a h => by
          have := F.polar_zt_six j
          rw [h, polar_smul_right_eq, F.polar_zt_f0, mul_zero] at this
          exact zero_ne_one this) t)
      F.perp_decomp_f0
  exact elementaryGroup_le_of_hypPair hQnd hMO
    ⟨F.e 0, F.f 0, F.Q_e 0, F.Q_f 0, by simpa using F.polar_ef 0 0⟩ he0 hf0

end Steps

end CFSG.RankThree.PartOne.SEITZ2
