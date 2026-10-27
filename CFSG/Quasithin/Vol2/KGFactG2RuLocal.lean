module

public import CFSG.Quasithin.Vol2.KGFactG2RuNorm
public import Certificates.Certificate7164

public noncomputable section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native

section Tests


theorem normalizer_W_of_g2NormW {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : g2NormW t = true) : g ∈ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) := by
  rw [g2NormW, allLt_iff] at h
  refine mem_normalizer_of_closure fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := hx
  exact mem_g2W_of_g2InW (rep_compA (rep_compA ht (rep_g2WGenA hk)) (rep_invCand' ht)) (h k hk)

theorem conj_eq_of_closure {s : Set (Equiv.Perm (Fin 4060))} {g g' : Equiv.Perm (Fin 4060)}
    (h : ∀ x ∈ s, g * x * g⁻¹ = g' * x * g'⁻¹) {x : Equiv.Perm (Fin 4060)}
    (hx : x ∈ Subgroup.closure s) : g * x * g⁻¹ = g' * x * g'⁻¹ := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => simp
  | mul a b _ _ iha ihb =>
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g' * a * g'⁻¹) * (g' * b * g'⁻¹) := by rw [iha, ihb]
      _ = g' * (a * b) * g'⁻¹ := by group
  | inv a _ iha =>
    calc g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      _ = (g' * a * g'⁻¹)⁻¹ := by rw [iha]
      _ = g' * a⁻¹ * g'⁻¹ := by group

theorem comm_of_g2CentV {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : g2CentV t = true) {v : Equiv.Perm (Fin 4060)} (hv : v ∈ g2V) : g * v = v * g := by
  rw [g2CentV, allLt_iff] at h
  have key : g * v * g⁻¹ = 1 * v * 1⁻¹ := by
    refine conj_eq_of_closure (fun x hx => ?_) hv
    obtain ⟨k, hk, rfl⟩ := hx
    rw [one_mul, inv_one, mul_one]
    exact eq_of_eqA (rep_ruConjA ht (rep_g2VGenA hk)) (rep_g2VGenA hk) (h k hk)
  rw [one_mul, inv_one, mul_one] at key
  calc g * v = g * v * g⁻¹ * g := by group
    _ = v * g := by rw [key]

theorem conj_eq_of_g2SameW {t u : Array ℕ} {g h : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hu : Rep 4060 u h) (hs : g2SameW t u = true) {w : Equiv.Perm (Fin 4060)} (hw : w ∈ g2W) :
    g * w * g⁻¹ = h * w * h⁻¹ := by
  rw [g2SameW, allLt_iff] at hs
  refine conj_eq_of_closure (fun x hx => ?_) hw
  obtain ⟨k, hk, rfl⟩ := hx
  exact eq_of_eqA (rep_ruConjA ht (rep_g2WGenA hk)) (rep_ruConjA hu (rep_g2WGenA hk)) (hs k hk)

theorem conj_eq_of_g2CentW {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hs : g2CentW t = true) {w : Equiv.Perm (Fin 4060)} (hw : w ∈ g2W) : g * w * g⁻¹ = w := by
  rw [g2CentW, allLt_iff] at hs
  have key : g * w * g⁻¹ = 1 * w * 1⁻¹ := by
    refine conj_eq_of_closure (fun x hx => ?_) hw
    obtain ⟨k, hk, rfl⟩ := hx
    rw [one_mul, inv_one, mul_one]
    exact eq_of_eqA (rep_ruConjA ht (rep_g2WGenA hk)) (rep_g2WGenA hk) (hs k hk)
  rwa [one_mul, inv_one, mul_one] at key

end Tests

section XN


theorem g2X_mem : g2X ∈ ruP := ruC_le (g2CElt_mem _)

theorem g2X_comm {v : Equiv.Perm (Fin 4060)} (hv : v ∈ g2V) : g2X * v = v * g2X :=
  comm_of_g2CentV rep_g2XA Certificates.certificate7164.1 hv

theorem g2X_not_mem :
    g2X ∉ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) := fun h => by
  have := g2NormW_of_mem rep_g2XA h
  rw [Certificates.certificate7164.2.1] at this
  exact Bool.noConfusion this

theorem g2N_spec {j : ℕ} (hj : j < 2) :
    g2N j ∈ ruP ∧ g2N j ∈ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) ∧
      g2N j ∈ Subgroup.normalizer (g2V : Set (Equiv.Perm (Fin 4060))) ∧
      g2N j * g2X * (g2N j)⁻¹ * g2X⁻¹ ∈
        Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) := by
  obtain ⟨h1, h2, h3⟩ := Certificates.certificate7164.2.2.1 j hj
  refine ⟨ruC_le (g2CElt_mem _), normalizer_W_of_g2NormW (rep_g2NA hj) h1,
    normalizer_V_of_g2NormV (rep_g2NA hj) h2, normalizer_W_of_g2NormW ?_ h3⟩
  exact rep_compA (rep_ruConjA (rep_g2NA hj) rep_g2XA) (rep_invCand' rep_g2XA)

@[expose] def g2D (m : ℕ) : Equiv.Perm (Fin 4060) :=
  g2VGen (g2DIdx.getD m (0, 0)).2 * ((g2N (g2DIdx.getD m (0, 0)).1)⁻¹ *
    g2VGen (g2DIdx.getD m (0, 0)).2 * g2N (g2DIdx.getD m (0, 0)).1)

theorem rep_g2DA {m : ℕ} (hm : m < 3) : Rep 4060 (g2DA m) (g2D m) := by
  have hj : (g2DIdx.getD m (0, 0)).1 < 2 := by interval_cases m <;> decide
  have hk : (g2DIdx.getD m (0, 0)).2 < 3 := by interval_cases m <;> decide
  have h := rep_ruConjA (rep_invCand' (rep_g2NA hj)) (rep_g2VGenA hk)
  rw [inv_inv] at h
  exact rep_compA (rep_g2VGenA hk) h

@[expose] def g2DElt (e : ℕ) : Equiv.Perm (Fin 4060) :=
  g2D 0 ^ (e % 2) * (g2D 1 ^ (e / 2 % 2) * g2D 2 ^ (e / 4 % 2))

theorem rep_g2DProd (e : ℕ) : Rep 4060 (g2DProd e) (g2DElt e) :=
  rep_compA (rep_powA (rep_g2DA (by norm_num)) _) (rep_compA
    (rep_powA (rep_g2DA (by norm_num)) _) (rep_powA (rep_g2DA (by norm_num)) _))

theorem g2V_le_closure :
    g2V ≤ Subgroup.closure {u | ∃ v ∈ g2V, ∃ n ∈ [g2N 0, g2N 1], u = v * (n⁻¹ * v * n)} := by
  set D := Subgroup.closure {u | ∃ m < 3, g2D m = u} with hD
  have hDmem : ∀ m < 3, g2D m ∈ D := fun m hm => Subgroup.subset_closure ⟨m, hm, rfl⟩
  have hDV : D ≤ g2V := by
    rw [hD, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact mem_g2V_of_g2InV (rep_g2DA hm) (Certificates.certificate7164.2.2.2.1 m hm)
  have hDcl : D ≤ Subgroup.closure {u | ∃ v ∈ g2V, ∃ n ∈ [g2N 0, g2N 1],
      u = v * (n⁻¹ * v * n)} := by
    rw [hD, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    refine Subgroup.subset_closure ⟨g2VGen (g2DIdx.getD m (0, 0)).2, g2VGen_mem ?_,
      g2N (g2DIdx.getD m (0, 0)).1, ?_, rfl⟩
    · interval_cases m <;> decide
    · interval_cases m <;> simp [g2DIdx]
  have hDelt : ∀ e, g2DElt e ∈ D := fun e =>
    D.mul_mem (D.pow_mem (hDmem 0 (by norm_num)) _) (D.mul_mem
      (D.pow_mem (hDmem 1 (by norm_num)) _) (D.pow_mem (hDmem 2 (by norm_num)) _))
  have hinj : ∀ i < 8, ∀ j < 8, g2DElt i = g2DElt j → i = j := by
    intro i hi j hj h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := Certificates.certificate7164.2.2.2.2.1 i hi j hj hlt
      rw [(eqA_iff (rep_g2DProd i) (rep_g2DProd j)).2 h] at this
      exact Bool.noConfusion this
    · have := Certificates.certificate7164.2.2.2.2.1 j hj i hi hlt
      rw [(eqA_iff (rep_g2DProd j) (rep_g2DProd i)).2 h.symm] at this
      exact Bool.noConfusion this
  have hcard : 8 ≤ Nat.card D := by
    let f : Fin 8 → D := fun e => ⟨g2DElt e, hDelt e⟩
    have hf : Function.Injective f := fun a b h =>
      Fin.ext (hinj a a.2 b b.2 (congrArg Subtype.val h))
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  have hDeq : D = g2V := Subgroup.eq_of_le_of_card_ge hDV (by rw [card_g2V]; exact hcard)
  exact hDeq.symm.le.trans hDcl

end XN

section A


@[expose] def g2AElt (e : ℕ) : Equiv.Perm (Fin 4060) :=
  g2A 0 ^ (e % 2) * (g2A 1 ^ (e / 2 % 2) * g2A 2 ^ (e / 4 % 2))

theorem rep_g2AProd (e : ℕ) : Rep 4060 (g2AProd e) (g2AElt e) :=
  rep_compA (rep_powA (rep_g2AA (by norm_num)) _) (rep_compA
    (rep_powA (rep_g2AA (by norm_num)) _) (rep_powA (rep_g2AA (by norm_num)) _))

theorem g2A_spec {i : ℕ} (hi : i < 3) :
    g2A i ∈ ruP ⊓ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) ∧
      (∀ v ∈ g2V, g2A i * v = v * g2A i) ∧
      ∀ w ∈ g2W, (g2A i * g2A i) * w * (g2A i * g2A i)⁻¹ = w := by
  obtain ⟨h1, h2, h3⟩ := Certificates.certificate7164.2.2.2.2.2.1 i hi
  exact ⟨⟨ruC_le (g2CElt_mem _), normalizer_W_of_g2NormW (rep_g2AA hi) h1⟩,
    fun v hv => comm_of_g2CentV (rep_g2AA hi) h2 hv,
    fun w hw => conj_eq_of_g2CentW (rep_compA (rep_g2AA hi) (rep_g2AA hi)) h3 hw⟩

theorem g2A_comm {i j : ℕ} (hi : i < 3) (hj : j < 3) {w : Equiv.Perm (Fin 4060)}
    (hw : w ∈ g2W) :
    (g2A i * g2A j) * w * (g2A i * g2A j)⁻¹ = (g2A j * g2A i) * w * (g2A j * g2A i)⁻¹ :=
  conj_eq_of_g2SameW (rep_compA (rep_g2AA hi) (rep_g2AA hj))
    (rep_compA (rep_g2AA hj) (rep_g2AA hi)) (Certificates.certificate7164.2.2.2.2.2.2.1 i hi
      j hj) hw

theorem g2AElt_ne {e e' : ℕ} (he : e < 8) (he' : e' < 8) (hne : e ≠ e') :
    ∃ w ∈ g2W, g2AElt e * w * (g2AElt e)⁻¹ ≠ g2AElt e' * w * (g2AElt e')⁻¹ := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  have key : ∀ e e' : ℕ, e < 8 → e' < 8 → e < e' →
      (∀ w ∈ g2W, g2AElt e * w * (g2AElt e)⁻¹ = g2AElt e' * w * (g2AElt e')⁻¹) → False := by
    intro e e' he he' hlt hw
    have h := Certificates.certificate7164.2.2.2.2.2.2.2 e he e' he' hlt
    have h2 : g2SameW (g2AProd e) (g2AProd e') = true := by
      rw [g2SameW, allLt_iff]
      exact fun k hk => (eqA_iff (rep_ruConjA (rep_g2AProd e) (rep_g2WGenA hk))
        (rep_ruConjA (rep_g2AProd e') (rep_g2WGenA hk))).2 (hw _ (g2WGen_mem hk))
    rw [h] at h2
    exact Bool.noConfusion h2
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact key e e' he he' hlt hall
  · exact key e' e he' he hlt fun w hw => (hall w hw).symm

end A

end CFSG.Quasithin.H13.Ch4.G2Ru
