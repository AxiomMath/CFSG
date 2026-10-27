module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WWb

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open CFSG.Quasithin

variable {W W₁ : Type*} [CommGroup W] [CommGroup W₁]

@[expose] def dmap (c : MulAut W) : W →* W where
  toFun w := c w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    ac_rfl

theorem dmap_apply (c : MulAut W) (w : W) : dmap c w = c w * w⁻¹ := rfl

theorem dmap_eq_one {c : MulAut W} {w : W} : dmap c w = 1 ↔ c w = w := mul_inv_eq_one

theorem dmap_comm {Λ : Subgroup (MulAut W)} {c : MulAut W} (hc : ∀ x ∈ Λ, c * x = x * c) :
    ∀ x ∈ Λ, ∀ w, dmap c (x w) = x (dmap c w) := fun x hx w => by
  rw [dmap_apply, dmap_apply, map_mul, map_inv, ← MulAut.mul_apply, hc x hx, MulAut.mul_apply]

theorem dmap_dmap (hW : ∀ w : W, w ^ 2 = 1) {c : MulAut W} (hc2 : c * c = 1) (w : W) :
    dmap c (dmap c w) = 1 := by
  have hcc : c (c w) = w := by rw [← MulAut.mul_apply, hc2, MulAut.one_apply]
  have hinv : ∀ v : W, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (by rw [← sq, hW])
  rw [dmap_apply, dmap_apply, map_mul, map_inv, hcc, hinv, hinv, hinv]
  calc w * c w * (c w * w) = (w * w) * (c w * c w) := by ac_rfl
    _ = 1 := by rw [← sq, ← sq, hW, hW, one_mul]

theorem exists_compl_of_centralizes [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Λ : Subgroup (MulAut W)} {j₁ j₂ : W₁ →* W} {b : W₁ → L3.Vec} (h₁ : L3Emb Λ j₁ b)
    (h₂ : L3Emb Λ j₂ b) (hsup : j₁.range ⊔ j₂.range = ⊤) (hcard : Nat.card W = 64)
    {c : MulAut W} (hc : ∀ x ∈ Λ, c * x = x * c) (hc2 : c * c = 1) (hc1 : c ≠ 1) :
    ∃ j : W₁ →* W, L3Emb Λ j b ∧ (∀ w, dmap c (j w) = 1 → w = 1) ∧
      Nat.card (dmap c).ker = 8 ∧ (dmap c).range = (dmap c).ker ∧
      ((dmap c).comp j).range = (dmap c).ker := by
  have hKinv : ∀ x ∈ Λ, ∀ w ∈ (dmap c).ker, x w ∈ (dmap c).ker := fun x hx w hw => by
    rw [MonoidHom.mem_ker, dmap_comm hc x hx, MonoidHom.mem_ker.mp hw, map_one]
  have hex : ∃ j : W₁ →* W, L3Emb Λ j b ∧ ∀ w, dmap c (j w) = 1 → w = 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨w₁, hw₁, hw₁1⟩ := hne j₁ h₁
    obtain ⟨w₂, hw₂, hw₂1⟩ := hne j₂ h₂
    apply hc1
    have htop : (⊤ : Subgroup W) ≤ (dmap c).ker := by
      rw [← hsup, sup_le_iff]
      constructor
      · rintro _ ⟨w, rfl⟩
        exact mem_of_L3Emb h₁ hKinv hw₁ hw₁1 w
      · rintro _ ⟨w, rfl⟩
        exact mem_of_L3Emb h₂ hKinv hw₂ hw₂1 w
    exact MulEquiv.ext fun w => dmap_eq_one.mp (htop (Subgroup.mem_top w))
  obtain ⟨j, hj, hjK⟩ := hex
  have hinj : Function.Injective ((dmap c).comp j) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    exact hjK w hw
  have hYcard : Nat.card ((dmap c).comp j).range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_of_L3Emb hj]
  have hYR : ((dmap c).comp j).range ≤ (dmap c).range := by
    rintro _ ⟨w, rfl⟩
    exact ⟨j w, rfl⟩
  have hRK : (dmap c).range ≤ (dmap c).ker := by
    rintro _ ⟨w, rfl⟩
    exact dmap_dmap hW hc2 w
  have h1 := Subgroup.card_le_of_le hYR
  have h2 := Subgroup.card_le_of_le hRK
  have h3 := Subgroup.card_ker_mul_card_range (dmap c)
  rw [hcard] at h3
  have hR8 : Nat.card (dmap c).range = 8 := by nlinarith
  have hK8 : Nat.card (dmap c).ker = 8 := by nlinarith
  have hRK' : (dmap c).range = (dmap c).ker := Subgroup.eq_of_le_of_card_ge hRK (by omega)
  refine ⟨j, hj, hjK, hK8, hRK', ?_⟩
  rw [← hRK']
  exact Subgroup.eq_of_le_of_card_ge hYR (by omega)

theorem card_eq_sixtyfour [Finite W] {Λ : Subgroup (MulAut W)} {j₁ j₂ : W₁ →* W}
    {b : W₁ → L3.Vec} (h₁ : L3Emb Λ j₁ b) (h₂ : L3Emb Λ j₂ b) (hsup : j₁.range ⊔ j₂.range = ⊤)
    (hinf : j₁.range ⊓ j₂.range = ⊥) : Nat.card W = 64 := by
  have hc : Subgroup.IsComplement' j₁.range j₂.range :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf) (by
      rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top])
  rw [← hc.card_mul_card, ← Nat.card_congr (MonoidHom.ofInjective h₁.1).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective h₂.1).toEquiv, card_of_L3Emb h₁]

theorem eq_of_centralizes_L3 [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Λ : Subgroup (MulAut W)}
    {j₁ j₂ : W₁ →* W} {b : W₁ → L3.Vec} (h₁ : L3Emb Λ j₁ b) (h₂ : L3Emb Λ j₂ b)
    (hsup : j₁.range ⊔ j₂.range = ⊤) (hinf : j₁.range ⊓ j₂.range = ⊥) {c c' : MulAut W}
    (hc : ∀ x ∈ Λ, c * x = x * c) (hc' : ∀ x ∈ Λ, c' * x = x * c') (hcc' : c * c' = c' * c)
    (hc2 : c * c = 1) (hc'2 : c' * c' = 1) (hc1 : c ≠ 1) (hc'1 : c' ≠ 1) : c = c' := by
  have hcard := card_eq_sixtyfour h₁ h₂ hsup hinf
  obtain ⟨j, hj, hjK, hK8, hRK, hYK⟩ :=
    exists_compl_of_centralizes hW h₁ h₂ hsup hcard hc hc2 hc1
  obtain ⟨-, -, -, hK8', hRK', -⟩ := exists_compl_of_centralizes hW h₁ h₂ hsup hcard hc' hc'2 hc'1
  have hc'Λ : ∀ x ∈ Λ, ∀ w, c' (x w) = x (c' w) := fun x hx w => by
    rw [← MulAut.mul_apply, hc' x hx, MulAut.mul_apply]
  have hmemY : ∀ v ∈ (dmap c).ker, ∃ w, v = dmap c (j w) := fun v hv => by
    rw [← hYK] at hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, hw.symm⟩
  have hfix : ∀ w, dmap c (j w) = c' (dmap c (j w)) :=
    eq_on_of_L3Emb (g := (c' : MulAut W).toMonoidHom.comp (dmap c)) hj (dmap_comm hc)
      (fun x hx w => by
        change c' (dmap c (x w)) = x (c' (dmap c w))
        rw [dmap_comm hc x hx, hc'Λ x hx]) hjK
      (fun w hw => hjK w ((map_eq_one_iff _ (c' : MulAut W).injective).mp hw))
      (fun w => by
        have hv : c' (dmap c (j w)) ∈ (dmap c).ker := by
          have h0 : dmap c (j w) ∈ (dmap c).ker := hRK ▸ ⟨j w, rfl⟩
          rw [MonoidHom.mem_ker, dmap_apply, ← MulAut.mul_apply, hcc', MulAut.mul_apply,
            dmap_eq_one.mp h0, mul_inv_cancel]
        obtain ⟨w', hw'⟩ := hmemY _ hv
        exact ⟨w', hw'⟩)
  have hKK' : (dmap c).ker = (dmap c').ker := by
    refine Subgroup.eq_of_le_of_card_ge (fun v hv => ?_) (by rw [hK8, hK8'])
    obtain ⟨w, rfl⟩ := hmemY v hv
    exact dmap_eq_one.mpr (hfix w).symm
  have hY : ∀ w, dmap c (j w) = dmap c' (j w) :=
    eq_on_of_L3Emb hj (dmap_comm hc) (dmap_comm hc') hjK
      (fun w hw => hjK w (by rw [← MonoidHom.mem_ker, hKK']; exact hw))
      (fun w => by
        have hv : dmap c' (j w) ∈ (dmap c).ker := by
          rw [hKK', ← hRK']
          exact ⟨j w, rfl⟩
        obtain ⟨w', hw'⟩ := hmemY _ hv
        exact ⟨w', hw'⟩)
  have hcompl : Subgroup.IsComplement' (dmap c).ker j.range := by
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · rw [hK8, ← Nat.card_congr (MonoidHom.ofInjective hj.1).toEquiv, card_of_L3Emb hj, hcard]
    · rw [disjoint_iff, eq_bot_iff]
      rintro v ⟨hv, w, rfl⟩
      rw [hjK w hv, map_one]
      exact Subgroup.one_mem _
  have htop : (⊤ : Subgroup W) ≤ MonoidHom.eqLocus (c : MulAut W).toMonoidHom
      (c' : MulAut W).toMonoidHom := by
    rw [← hcompl.sup_eq_top, sup_le_iff]
    constructor
    · intro v hv
      have hv' : v ∈ (dmap c').ker := hKK' ▸ hv
      change c v = c' v
      rw [dmap_eq_one.mp hv, dmap_eq_one.mp hv']
    · rintro _ ⟨w, rfl⟩
      have h1 := hY w
      rw [dmap_apply, dmap_apply] at h1
      exact mul_right_cancel h1
  exact MulEquiv.ext fun w => htop (Subgroup.mem_top w)

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
