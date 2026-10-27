module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin1

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.Fin

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

@[expose] def zStd : Perm (Fin 5) := swap 0 2 * swap 1 3

theorem isFixPt_std_iff (q : Fin 5) : IsFixPt S5Syl q ↔ q = 4 := by
  have h : ∀ q : Fin 5, (∀ d ∈ S5SylF, d q = q) ↔ q = 4 := by decide +kernel
  rw [← h q]
  exact ⟨fun hq d hd => hq d ((mem_S5Syl_iff d).mpr hd),
    fun hq d hd => hq d ((mem_S5Syl_iff d).mp hd)⟩

theorem isCentInv_std_iff (y : Perm (Fin 5)) : IsCentInv S5Syl y ↔ y = zStd := by
  have h : ∀ y : Perm (Fin 5), (y ∈ S5SylF ∧ y ≠ 1 ∧ ∀ d ∈ S5SylF, d * y = y * d) ↔ y = zStd := by
    unfold zStd; decide +kernel
  rw [← h y]
  refine and_congr (mem_S5Syl_iff y) (and_congr Iff.rfl ?_)
  exact ⟨fun hq d hd => hq d ((mem_S5Syl_iff d).mpr hd),
    fun hq d hd => hq d ((mem_S5Syl_iff d).mp hd)⟩

theorem isFixPt_cj_iff {D : Subgroup (Perm (Fin 5))} {g : Perm (Fin 5)} {p : Fin 5} :
    IsFixPt (cj g D) p ↔ IsFixPt D (g⁻¹ p) := by
  constructor
  · intro h b hb
    have h1 := h (g * b * g⁻¹) (mem_cj_conj.mpr hb)
    simp only [Perm.mul_apply] at h1
    have h2 : b (g⁻¹ p) = g⁻¹ p := by
      apply g.injective
      rw [h1]; simp
    exact h2
  · intro h σ hσ
    have hb := h _ (mem_cj.mp hσ)
    simp only [Perm.mul_apply] at hb
    have h2 : g (g⁻¹ (σ (g (g⁻¹ p)))) = g (g⁻¹ p) := congrArg g hb
    simpa using h2

theorem isCentInv_cj_iff {D : Subgroup (Perm (Fin 5))} {g z : Perm (Fin 5)} :
    IsCentInv (cj g D) z ↔ IsCentInv D (g⁻¹ * z * g) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨mem_cj.mp h1, ?_, fun d hd => ?_⟩
    · intro h; apply h2
      have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [this, h]; group
    · have h4 := h3 (g * d * g⁻¹) (mem_cj_conj.mpr hd)
      calc d * (g⁻¹ * z * g) = g⁻¹ * ((g * d * g⁻¹) * z) * g := by group
        _ = g⁻¹ * (z * (g * d * g⁻¹)) * g := by rw [h4]
        _ = (g⁻¹ * z * g) * d := by group
  · rintro ⟨h1, h2, h3⟩
    refine ⟨mem_cj.mpr h1, ?_, fun d hd => ?_⟩
    · intro h; apply h2
      rw [h]; group
    · have h4 := h3 (g⁻¹ * d * g) (mem_cj.mp hd)
      calc d * z = g * ((g⁻¹ * d * g) * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * (g⁻¹ * d * g)) * g⁻¹ := by rw [h4]
        _ = z * d := by group

theorem isFixPt_cj_std_iff {g : Perm (Fin 5)} {p : Fin 5} :
    IsFixPt (cj g S5Syl) p ↔ p = g 4 := by
  rw [isFixPt_cj_iff, isFixPt_std_iff]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

theorem isCentInv_cj_std_iff {g z : Perm (Fin 5)} :
    IsCentInv (cj g S5Syl) z ↔ z = g * zStd * g⁻¹ := by
  rw [isCentInv_cj_iff, isCentInv_std_iff]
  constructor
  · intro h
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h]
  · intro h; rw [h]; group

theorem exists_isFixPt {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    ∃ p, IsFixPt D p := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  exact ⟨g 4, isFixPt_cj_std_iff.mpr rfl⟩

theorem IsFixPt.unique {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {p q : Fin 5}
    (hp : IsFixPt D p) (hq : IsFixPt D q) : p = q := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [isFixPt_cj_std_iff.mp hp, isFixPt_cj_std_iff.mp hq]

theorem exists_isCentInv {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    ∃ z, IsCentInv D z := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  exact ⟨g * zStd * g⁻¹, isCentInv_cj_std_iff.mpr rfl⟩

theorem IsCentInv.unique {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z w : Perm (Fin 5)}
    (hz : IsCentInv D z) (hw : IsCentInv D w) : z = w := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  rw [isCentInv_cj_std_iff.mp hz, isCentInv_cj_std_iff.mp hw]

noncomputable def fixPt (D : Subgroup (Perm (Fin 5))) : Fin 5 := Classical.epsilon (IsFixPt D)

noncomputable def zc (D : Subgroup (Perm (Fin 5))) : Perm (Fin 5) :=
  Classical.epsilon (IsCentInv D)

theorem isFixPt_fixPt {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    IsFixPt D (fixPt D) := Classical.epsilon_spec (exists_isFixPt hD)

theorem isCentInv_zc {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    IsCentInv D (zc D) := Classical.epsilon_spec (exists_isCentInv hD)

theorem fixPt_eq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {p : Fin 5}
    (hp : IsFixPt D p) : fixPt D = p := IsFixPt.unique hD (isFixPt_fixPt hD) hp

theorem zc_eq {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
    (hz : IsCentInv D z) : zc D = z := IsCentInv.unique hD (isCentInv_zc hD) hz

theorem cj_alternatingGroup (g : Perm (Fin 5)) :
    cj g (alternatingGroup (Fin 5)) = alternatingGroup (Fin 5) := by
  ext σ
  rw [mem_cj]
  have : Perm.sign (g⁻¹ * σ * g) = Perm.sign σ := by
    rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm, ← mul_assoc, Int.units_mul_self,
      one_mul]
  simp only [Perm.mem_alternatingGroup, this]

theorem cj_Tsub (g : Perm (Fin 5)) (D : Subgroup (Perm (Fin 5))) :
    cj g (Tsub D) = Tsub (cj g D) := by
  unfold Tsub
  rw [cj_inf, cj_alternatingGroup]

theorem isSwap_conj (g : Perm (Fin 5)) {x : Perm (Fin 5)} :
    (g * x * g⁻¹).IsSwap ↔ x.IsSwap := by
  have key : ∀ (g x : Perm (Fin 5)), x.IsSwap → (g * x * g⁻¹).IsSwap := by
    rintro g x ⟨a, b, hab, rfl⟩
    exact ⟨g a, g b, g.injective.ne hab, (swap_apply_apply g a b).symm⟩
  refine ⟨fun h => ?_, key g x⟩
  have := key g⁻¹ _ h
  simpa [mul_assoc] using this

theorem cj_closure (g : Perm (Fin 5)) (S : Set (Perm (Fin 5))) :
    cj g (Subgroup.closure S) = Subgroup.closure ((fun x => g * x * g⁻¹) '' S) :=
  MonoidHom.map_closure _ _

theorem cj_That (g : Perm (Fin 5)) (D : Subgroup (Perm (Fin 5))) :
    cj g (That D) = That (cj g D) := by
  unfold That
  rw [cj_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
    exact ⟨mem_cj_conj.mpr hx, (isSwap_conj g).mpr hs⟩
  · rintro ⟨hy, hs⟩
    refine ⟨g⁻¹ * y * g, ⟨mem_cj.mp hy, ?_⟩, by simp [mul_assoc]⟩
    have := (isSwap_conj g⁻¹).mpr hs
    simpa [mul_assoc] using this

theorem cj_Cfour (g : Perm (Fin 5)) (D : Subgroup (Perm (Fin 5))) :
    cj g (Cfour D) = Cfour (cj g D) := by
  unfold Cfour
  rw [cj_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  have hsq : ∀ x : Perm (Fin 5), (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := fun x => conj_pow
  constructor
  · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
    refine ⟨mem_cj_conj.mpr hx, ?_⟩
    show (g * x * g⁻¹) ^ 2 ≠ 1
    rw [hsq]
    intro h; apply hs
    have : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
    rw [this, h]; group
  · rintro ⟨hy, hs⟩
    refine ⟨g⁻¹ * y * g, ⟨mem_cj.mp hy, ?_⟩, by simp [mul_assoc]⟩
    intro h; apply hs
    have : y ^ 2 = g * (g⁻¹ * y * g) ^ 2 * g⁻¹ := by
      rw [← conj_pow]; simp [mul_assoc]
    rw [this, h]; group

theorem Tsub_std : Tsub S5Syl = S5T := rfl

theorem That_std : That S5Syl = S5That := by
  unfold That S5That
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have h : ∀ y : Perm (Fin 5), (y ∈ S5SylF ∧ (y ≠ 1 ∧ y ^ 2 = 1 ∧ Perm.sign y ≠ 1)) ↔
      (y = swap 0 2 ∨ y = swap 1 3) := by decide +kernel
  rw [isSwap_iff, mem_S5Syl_iff]
  exact h y

theorem Cfour_std : Cfour S5Syl = Subgroup.zpowers S5g := by
  unfold Cfour
  have h : ∀ y : Perm (Fin 5), (y ∈ S5SylF ∧ y ^ 2 ≠ 1) ↔ (y = S5g ∨ y = S5g ^ 3) := by
    decide +kernel
  have hs : {g | g ∈ S5Syl ∧ g ^ 2 ≠ 1} = ({S5g, S5g ^ 3} : Set (Perm (Fin 5))) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [mem_S5Syl_iff]
    exact h y
  rw [hs, Subgroup.zpowers_eq_closure]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    have h1 : S5g ∈ Subgroup.closure ({S5g} : Set (Perm (Fin 5))) :=
      Subgroup.subset_closure (Set.mem_singleton S5g)
    rintro y (rfl | rfl)
    · exact h1
    · exact Subgroup.pow_mem _ h1 3
  · rw [Subgroup.closure_le]
    rintro y rfl
    exact Subgroup.subset_closure (Set.mem_insert _ _)

end CFSG.Quasithin.F53.Stellmacher.S35.Fin
