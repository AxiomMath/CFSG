module

public import CFSG.LocalAnalysis.StandardType.GGPresentationTypeAMain

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits SpecialLinear
  CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable (m : ℕ) (F : Type) [Field F]

@[expose] def typeALeviJ (k : ℕ) : Finset (Fin m) := Finset.univ.filter fun j => j.val + 1 < k

theorem typeALeviJ_self : typeALeviJ m m = typeAJ₁ m := rfl

theorem typeALevi_mem_lattice {k : ℕ} {v : Fin m → ℤ}
    (h : ∀ a : Fin (m + 1), k ≤ a.val → toStd m v a = 0) :
    v ∈ ggSuppLattice (rootDatum m F) (typeALeviJ m k) := by
  have key : ∀ d : ℕ, ∀ i : Fin m, i.val + d + 1 = m → k ≤ i.val + 1 → v i = 0 := by
    intro d
    induction d with
    | zero =>
      intro i hi hk
      have h0 := h (Fin.last m) (by simp only [Fin.val_last]; omega)
      have hm : 0 < m := by omega
      simp only [toStd, Fin.val_last, lt_irrefl, dite_false, zero_sub, hm, dite_true,
        neg_eq_zero] at h0
      have e : (⟨m - 1, by omega⟩ : Fin m) = i := Fin.ext (by simp only; omega)
      rw [← e]
      exact h0
    | succ d ih =>
      intro i hi hk
      have h1 : i.val + 1 < m := by omega
      have h2 := ih ⟨i.val + 1, h1⟩ (by simp only; omega) (by simp only; omega)
      have h3 := h ⟨i.val + 1, by omega⟩ (by simp only; omega)
      simp only [toStd, h1, dite_true, Nat.succ_pos, add_tsub_cancel_right, Fin.eta, h2,
        zero_sub, neg_eq_zero] at h3
      exact h3
  rintro ⟨i, hi_lt⟩ hi
  change i < m at hi_lt
  have hi' : ¬ (i + 1 < k) := fun h' => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩)
  exact key (m - 1 - i) ⟨i, hi_lt⟩ (by simp only; omega) (by simp only; omega)

theorem typeALevi_toStd_eq_zero {k : ℕ} {v : Fin m → ℤ}
    (hv : ∀ i ∉ typeALeviJ m k, v i = 0) (a : Fin (m + 1)) (ha : k ≤ a.val) :
    toStd m v a = 0 := by
  have e1 : (if h : a.val < m then v ⟨a.val, h⟩ else 0) = 0 := by
    split_ifs with h
    · exact hv _ fun hmem => by
        have := (Finset.mem_filter.mp hmem).2
        simp only at this
        omega
    · rfl
  have e2 : (if h : 0 < a.val then v ⟨a.val - 1, by omega⟩ else 0) = 0 := by
    split_ifs with h
    · exact hv _ fun hmem => by
        have := (Finset.mem_filter.mp hmem).2
        simp only at this
        omega
    · rfl
  simp only [toStd, e1, e2, sub_zero]

theorem exists_perm_lt {k : ℕ} (hk : k ≤ m + 1) (E : Finset (Fin (m + 1))) (hE : E.card ≤ k) :
    ∃ π : Equiv.Perm (Fin (m + 1)), ∀ e ∈ E, (π e).val < k := by
  induction E using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a E₀ ha ih =>
    rw [Finset.card_insert_of_notMem ha] at hE
    obtain ⟨π₀, hπ₀⟩ := ih (by omega)
    by_cases hlt : (π₀ a).val < k
    · refine ⟨π₀, fun e he => ?_⟩
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hlt
      · exact hπ₀ e he
    · have hcard : (E₀.image π₀).card < (Finset.univ.map (Fin.castLEEmb hk)).card := by
        rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
        exact lt_of_le_of_lt Finset.card_image_le (by omega)
      obtain ⟨c, hc, hcE⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      obtain ⟨c', -, rfl⟩ := Finset.mem_map.mp hc
      refine ⟨Equiv.swap (π₀ a) (Fin.castLEEmb hk c') * π₀, fun e he => ?_⟩
      rcases Finset.mem_insert.mp he with rfl | he
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        simp
      · have h1 : π₀ e ≠ π₀ a := fun h => ha (π₀.injective h ▸ he)
        have h2 : π₀ e ≠ Fin.castLEEmb hk c' := fun h => hcE (h ▸ Finset.mem_image_of_mem π₀ he)
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact hπ₀ e he

theorem typeALevi_orbit {k : ℕ} (hk : 4 ≤ k) (hkm : k ≤ m) :
    GGOrbit (rootDatum m F) (fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k)) := by
  refine ggOrbit_of_pairs (fun _ => ggSuppLattice (rootDatum m F) (typeALeviJ m k))
    (fun _ γ hγ hγM => ⟨hγ, hγM⟩) ?_
  intro J hJ
  let J' : Finset (Fin m) := J
  have h4 : J'.card ≤ 2 := hJ
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Fin (m + 1)),
      E = J'.image Fin.castSucc ∪ J'.image Fin.succ := ⟨_, rfl⟩
  have hE : E.card ≤ k := by
    have h1 := Finset.card_union_le (J'.image Fin.castSucc) (J'.image Fin.succ)
    have h2 := Finset.card_image_le (s := J') (f := Fin.castSucc)
    have h3 := Finset.card_image_le (s := J') (f := Fin.succ)
    rw [hEdef]
    omega
  obtain ⟨π, hπ⟩ := exists_perm_lt m (by omega) E hE
  obtain ⟨w, hw⟩ := exists_weyl_toStd m π
  refine ⟨w, (), fun j hj => typeALevi_mem_lattice m F fun a ha => ?_⟩
  let j' : Fin m := j
  have hj' : j' ∈ J' := hj
  have hc1 : π.symm a ≠ j'.castSucc := fun h => by
    have := hπ _ (hEdef ▸ Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j', hj', rfl⟩))
    rw [← h, Equiv.apply_symm_apply] at this
    omega
  have hc2 : π.symm a ≠ j'.succ := fun h => by
    have := hπ _ (hEdef ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j', hj', rfl⟩))
    rw [← h, Equiv.apply_symm_apply] at this
    omega
  change toStd m (weylAction (isFiniteType_A m) w (Pi.single j' 1)) a = 0
  rw [hw]
  change toStd m (Pi.single j' 1) (π.symm a) = 0
  rw [toStd_single]
  simp [hc1, hc2]

@[expose] def typeALeviW (k : ℕ) : Subgroup (coxeterMatrix (isFiniteType_A m)).Group :=
  Subgroup.closure ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
    (typeALeviJ m k : Set (Fin m)))

theorem exists_typeALeviW_swap_adj {k : ℕ} (x y : Fin (m + 1)) (hxy : y.val = x.val + 1)
    (hy : y.val < k) : ∃ w ∈ typeALeviW m k, TypeARealizes m w (Equiv.swap x y) := by
  have hj : x.val < m := by have := y.isLt; omega
  let j : Fin m := ⟨x.val, hj⟩
  have hjJ : j ∈ typeALeviJ m k :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [j]; omega⟩
  refine ⟨(coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j,
    Subgroup.subset_closure ⟨j, hjJ, rfl⟩, ?_⟩
  have e1 : j.castSucc = x := Fin.ext (by simp [j])
  have e2 : j.succ = y := Fin.ext (by simp only [j, Fin.val_succ]; omega)
  rw [← e1, ← e2]
  exact typeARealizes_simple m j

theorem exists_typeALeviW_swap_of_lt {k : ℕ} : ∀ (d : ℕ) (x y : Fin (m + 1)),
    y.val = x.val + d + 1 → y.val < k →
      ∃ w ∈ typeALeviW m k, TypeARealizes m w (Equiv.swap x y) := by
  intro d
  induction d with
  | zero => exact fun x y hxy hy => exists_typeALeviW_swap_adj m x y (by omega) hy
  | succ d ih =>
    intro x y hxy hy
    have hyl := y.isLt
    let y' : Fin (m + 1) := ⟨x.val + d + 1, by omega⟩
    obtain ⟨w₁, hw₁, h₁⟩ := ih x y' rfl (by simp only [y']; omega)
    obtain ⟨w₂, hw₂, h₂⟩ := exists_typeALeviW_swap_adj m y' y (by simp only [y']; omega) hy
    have hx1 : x ≠ y' := fun h => by
      have := congrArg Fin.val h
      simp only [y'] at this
      omega
    have hx2 : x ≠ y := fun h => by
      have := congrArg Fin.val h
      omega
    have key : Equiv.swap x y = Equiv.swap y' y * Equiv.swap x y' * Equiv.swap y' y := by
      have := Equiv.swap_apply_apply (Equiv.swap y' y) x y'
      rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2, Equiv.swap_apply_left, Equiv.swap_inv] at this
      exact this
    refine ⟨w₂ * w₁ * w₂, mul_mem (mul_mem hw₂ hw₁) hw₂, ?_⟩
    rw [key]
    exact typeARealizes_mul m (typeARealizes_mul m h₂ h₁) h₂

theorem exists_typeALeviW_swap {k : ℕ} (x y : Fin (m + 1)) (hx : x.val < k) (hy : y.val < k) :
    ∃ w ∈ typeALeviW m k, TypeARealizes m w (Equiv.swap x y) := by
  rcases lt_trichotomy x.val y.val with h | h | h
  · exact exists_typeALeviW_swap_of_lt m (y.val - x.val - 1) x y (by omega) hy
  · obtain rfl : x = y := Fin.ext h
    exact ⟨1, one_mem _, by rw [Equiv.swap_self]; exact typeARealizes_one m⟩
  · obtain ⟨w, hw, hw'⟩ := exists_typeALeviW_swap_of_lt m (x.val - y.val - 1) y x (by omega) hx
    exact ⟨w, hw, by rw [Equiv.swap_comm]; exact hw'⟩

theorem typeALevi_root_of_mem {k : ℕ} {γ : Fin m → ℤ}
    (hγ : γ ∈ ggSupp (rootDatum m F) (typeALeviJ m k)) :
    ∃ a b : Fin (m + 1), a ≠ b ∧ a.val < k ∧ b.val < k ∧
      toStd m γ = Pi.single a 1 - Pi.single b 1 := by
  have hroot : γ ∈ roots (isFiniteType_A m) ∅ := hγ.1
  rw [roots_eq] at hroot
  obtain ⟨a, b, hab, hγab⟩ := hroot
  have hz := typeALevi_toStd_eq_zero m (k := k) (v := γ) hγ.2
  refine ⟨a, b, hab, ?_, ?_, hγab⟩
  · by_contra h
    have := hz a (by omega)
    rw [hγab] at this
    simp [hab] at this
  · by_contra h
    have := hz b (by omega)
    rw [hγab] at this
    simp [Ne.symm hab] at this

theorem typeALevi_transitive {k : ℕ} {α β : Fin m → ℤ}
    (hα : α ∈ ggSupp (rootDatum m F) (typeALeviJ m k))
    (hβ : β ∈ ggSupp (rootDatum m F) (typeALeviJ m k)) :
    ∃ w ∈ typeALeviW m k, weylAction (isFiniteType_A m) w α = β := by
  obtain ⟨a, b, hab, ha, hb, hαab⟩ := typeALevi_root_of_mem m F hα
  obtain ⟨a', b', hab', ha', hb', hβab⟩ := typeALevi_root_of_mem m F hβ
  let b'' := Equiv.swap a a' b
  have hb''k : b''.val < k := by
    simp only [b'', Equiv.swap_apply_def]
    split_ifs <;> assumption
  have hb''a' : b'' ≠ a' := fun h => hab (by
    have := congrArg (Equiv.swap a a') h
    simpa [b''] using this.symm)
  obtain ⟨w₁, hw₁, h₁⟩ := exists_typeALeviW_swap m a a' ha ha'
  obtain ⟨w₂, hw₂, h₂⟩ := exists_typeALeviW_swap m b'' b' hb''k hb'
  refine ⟨w₂ * w₁, mul_mem hw₂ hw₁, toStd_injective m ?_⟩
  rw [typeARealizes_mul m h₂ h₁ α, hαab, hβab]
  have hπa : (Equiv.swap b'' b' * Equiv.swap a a') a = a' := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hb''a') hab'
  have hπb : (Equiv.swap b'' b' * Equiv.swap a a') b = b' := by
    simp only [Equiv.Perm.mul_apply]
    exact Equiv.swap_apply_left _ _
  funext x
  simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq, hπa, hπb]

theorem typeALevi_refl_mem {k : ℕ} (w : (coxeterMatrix (isFiniteType_A m)).Group) (j : Fin m)
    (hj : weylAction (isFiniteType_A m) w (Pi.single j 1) ∈
      ggSupp (rootDatum m F) (typeALeviJ m k)) :
    w * (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j * w⁻¹ ∈ typeALeviW m k := by
  obtain ⟨π, hπ⟩ := exists_typeARealizes m w
  obtain ⟨a, b, hab, ha, hb, hγab⟩ := typeALevi_root_of_mem m F hj
  rw [hπ, toStd_single] at hγab
  have hπa : π j.castSucc = a := by
    by_contra h
    have := congrFun hγab a
    simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq] at this
    split_ifs at this <;> simp_all
  have hπb : π j.succ = b := by
    by_contra h
    have := congrFun hγab b
    simp only [Pi.sub_apply, Pi.single_apply, Equiv.symm_apply_eq] at this
    split_ifs at this <;> simp_all
  obtain ⟨w', hw', h'⟩ := exists_typeALeviW_swap m a b ha hb
  have hinv : TypeARealizes m w⁻¹ π⁻¹ := fun γ => by
    have := hπ (weylAction (isFiniteType_A m) w⁻¹ γ)
    rw [weylAction_apply_inv_apply] at this
    funext x
    have h2 := congrFun this (π x)
    simp only [Equiv.symm_apply_apply] at h2
    rw [← h2]
    rfl
  have hconj := typeARealizes_mul m (typeARealizes_mul m hπ (typeARealizes_simple m j)) hinv
  rw [← Equiv.swap_apply_apply, hπa, hπb] at hconj
  rw [typeARealizes_inj m hconj h']
  exact hw'

theorem ggPresentation_typeALevi {m k : ℕ} (hk : 4 ≤ k) (hkm : k ≤ m) {F : Type} [Field F]
    [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) {X : Type} [Group X]
    (φ : ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeALeviJ m k)) →* X)
    {R : Subgroup X} {δ : R →* (coxeterMatrix (isFiniteType_A m)).Group}
    (hδ : Function.Surjective δ)
    (hspecial : ∀ j ∈ typeALeviJ m k, ∃ c : R, (c : X) = ggExt φ (weylRep m F j) ∧
      δ c = (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j)
    (hcent : ∀ (r : R), ∀ α ∈ ggSupp (rootDatum m F) (typeALeviJ m k),
      weylAction (isFiniteType_A m) (δ r) α = α →
        ∀ z ∈ rootGroup m F α, (r : X) * ggExt φ z * (r : X)⁻¹ = ggExt φ z)
    (hnt : ∃ γ ∈ ggSupp (rootDatum m F) (typeALeviJ m k), ∃ z ∈ rootGroup m F γ, ggExt φ z ≠ 1) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* X,
      (∀ x : ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeALeviJ m k)), ψ x = φ x) ∧
      (∀ (r : R) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F),
        ψ (slWeylLift m (two_eq_zero_of_card hF hf) (δ r) * u *
          (slWeylLift m (two_eq_zero_of_card hF hf) (δ r))⁻¹) = r * ψ u * (r : X)⁻¹) ∧
      (∀ w : (coxeterMatrix (isFiniteType_A m)).Group, ∃ r : R,
        (r : X) = ψ (slWeylLift m (two_eq_zero_of_card hF hf) w) ∧ δ r = w) ∧
      ψ.range = ggClosure (rootDatum m F)
        (fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k)) (fun _ => φ) R ∧
      ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) ∧
      IsQuasisimple (ggClosure (rootDatum m F)
        (fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k)) (fun _ => φ) R) ∧
      LieModel (ggClosure (rootDatum m F)
          (fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k)) (fun _ => φ) R ⧸
          Subgroup.center (ggClosure (rootDatum m F)
            (fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k)) (fun _ => φ) R))
        .PSL (m + 1) 2 f := by
  have h2 : (2 : F) = 0 := two_eq_zero_of_card hF hf
  have hν : GGWeylLift (rootDatum m F) (slWeylLift m h2) := slWeylLift_spec m h2
  have hS : ∀ i : Unit, (fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k)) i ⊆
      (rootDatum m F).roots := fun _ γ hγ => hγ.1
  have hT : ∀ t ∈ (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
      (typeALeviJ m k : Set (Fin m)),
      slWeylLift m h2 t ∈ ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeALeviJ m k)) := by
    rintro _ ⟨j, hj, rfl⟩
    have h := hν.simple_mem j
    exact sup_le (rootGroup_le_ggSub (single_mem_ggSupp hj))
      (rootGroup_le_ggSub (neg_single_mem_ggSupp hj)) h
  have hWk : ∀ v ∈ typeALeviW m k, slWeylLift m h2 v ∈
      ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeALeviJ m k)) :=
    fun v hv => ggWeylLift_mem_of_closure hT hv
  have hgen : ∀ t ∈ (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
      (typeALeviJ m k : Set (Fin m)),
      ∃ c : R, (c : X) = ggExt φ (slWeylLift m h2 t) ∧ δ c = t := by
    rintro _ ⟨j, hj, rfl⟩
    rw [slWeylLift_simple]
    exact hspecial j hj
  have hall := exists_mem_R_of_closure
    (S := fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k))
    (φ := fun _ => φ) (ν := slWeylLift m h2) (δ := δ) (k := ()) hWk hgen
  have hC : GGActsLike (rootDatum m F) (fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k))
      (fun _ => φ) (slWeylLift m h2) R δ := by
    refine ggActsLike_of_transitive hν hS (fun _ _ _ _ _ _ _ => rfl) ?_
      (fun r _ α hα hfix z hz => hcent r α hα hfix z hz)
      (fun w α hα hfix z hz => slWeylLift_fix m h2 w hα hfix hz)
    intro r _ _ α hα hαr
    obtain ⟨v₂, hv₂, hv₂α⟩ := typeALevi_transitive m F hα hαr
    obtain ⟨c₂, hc₂, hcδ₂⟩ := hall v₂ hv₂
    obtain ⟨c₁, hc₁, hcδ₁⟩ := hall 1 (one_mem _)
    refine ⟨α, 1, v₂, c₁, c₂, hα, hα, ?_, hv₂α, hWk 1 (one_mem _), hc₁, hcδ₁, hWk v₂ hv₂, hc₂,
      hcδ₂⟩
    change weylAction (isFiniteType_A m) 1 α = α
    rw [map_one]
    rfl
  have hW : GGWeylInR (rootDatum m F) (fun _ : Unit => ggSupp (rootDatum m F) (typeALeviJ m k))
      (fun _ => φ) (slWeylLift m h2) R δ :=
    ggWeylInR_of_subgroup (fun _ => typeALeviW m k) (fun _ => hWk)
      (fun _ => (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
        (typeALeviJ m k : Set (Fin m))) (fun _ => rfl) (fun _ => hgen)
      (fun _ w j hj => typeALevi_refl_mem m F w j hj)
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun h => by simp at h; omega, fun h => by simp at h; omega⟩
  have hCT : CurtisTitsConclusion.{0} (rootDatum m F) .PSL (m + 1) 2 f :=
    curtisTitsConclusion_specialLinear hadm hF (by omega)
  obtain ⟨ψ, h1, h2', h3, h4, h5, h6, h7⟩ := ggPresentation hCT hν hS (fun _ => φ) hδ hC hW
    (typeALevi_orbit m F hk hkm) ⟨(), hnt⟩
  exact ⟨ψ, h1 (), h2', h3, h4, h5, h6, h7⟩

end CFSG.StandardType
