module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltAut
import CFSG.LargeExtraspecial.AS35YFSymAut

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {m : ℕ}

private lemma p9uRMAP_sum_basis (v : DVec m) : (∑ i : Fin m, v i • dBasis m i) = v := by
  conv_rhs => rw [← Module.Basis.sum_repr (dBasis m) v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.basisFun_repr]

private lemma p9uRMAP_one_eq_sum : (1 : DVec m) = ∑ i, dBasis m i := by
  funext k
  rw [Finset.sum_apply, Finset.sum_eq_single k]
  · simp [dBasis, Pi.basisFun_apply]
  · intro i _ hi
    simp [dBasis, Pi.basisFun_apply, Pi.single_apply, hi]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma p9uRMAP_dPerm_eval (σ : Equiv.Perm (Fin m)) (v : DVec m) (i : Fin m) :
    dPerm m σ v i = v (σ.symm i) := by
  have hlin : (LinearMap.proj i).comp (dPerm m σ : DVec m →ₗ[ZMod 3] DVec m) =
      LinearMap.proj (σ.symm i) := by
    refine (dBasis m).ext fun k => ?_
    change (dPerm m σ (dBasis m k)) i = (dBasis m k) (σ.symm i)
    rw [dPerm_apply]
    simp only [dBasis, Pi.basisFun_apply]
    by_cases h : σ k = i
    · have hk : σ.symm i = k := by rw [← h, Equiv.symm_apply_apply]
      rw [h, hk, Pi.single_eq_same, Pi.single_eq_same]
    · have hk : σ.symm i ≠ k := fun hh => h (by rw [← hh]; exact Equiv.apply_symm_apply σ i)
      rw [Pi.single_eq_of_ne (show i ≠ σ k from fun hh => h hh.symm),
        Pi.single_eq_of_ne hk]
  have := congrArg (fun f : DVec m →ₗ[ZMod 3] ZMod 3 => f v) hlin
  simpa [LinearMap.comp_apply, LinearMap.proj_apply] using this

theorem qtwoDRMStab_dPerm_const (σ : Equiv.Perm (Fin m)) (c : ZMod 3) :
    dPerm m σ (fun _ => c) = fun _ => c := by
  funext j
  rw [p9uRMAP_dPerm_eval]

private lemma p9uRMAP_dPerm_inv (ρ : Equiv.Perm (Fin m)) :
    (dPerm m ρ)⁻¹ = dPerm m ρ⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← dPerm_mul, mul_inv_cancel, dPerm_one]

private lemma p9uRMAP_dPerm_injective :
    Function.Injective (dPerm m : Equiv.Perm (Fin m) → _) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have h1 := congrArg (fun (g : DVec m ≃ₗ[ZMod 3] DVec m) => g (dBasis m i)) h
  rw [dPerm_apply, dPerm_apply] at h1
  have h2 := congrArg (fun v : DVec m => v (σ i)) h1
  simpa [dBasis, Pi.basisFun_apply, Pi.single_apply] using h2

theorem qtwoDRMStab_eq_dPerm_of_fix {w : DVec m ≃ₗ[ZMod 3] DVec m}
    (hw : w ∈ dEven m) (h1 : w (1 : DVec m) = 1) :
    ∃ σ : Equiv.Perm (Fin m), w = dPerm m σ := by
  classical
  obtain ⟨σ, c, -, -, hact⟩ := hw
  refine ⟨σ, (dBasis m).ext' fun i => ?_⟩
  have hci : c i = 1 := by
    have h : w (1 : DVec m) (σ i) = (1 : DVec m) (σ i) := congrFun h1 (σ i)
    rw [p9uRMAP_one_eq_sum, map_sum, Finset.sum_apply] at h
    simp only [hact, Pi.smul_apply, smul_eq_mul] at h
    simpa [dBasis, Pi.basisFun_apply, Pi.single_apply, σ.injective.eq_iff] using h
  rw [hact i, hci, one_smul, dPerm_apply]

theorem qtwoDRMStab_mem_dEvenStab_one_iff (w : DVec m ≃ₗ[ZMod 3] DVec m) :
    w ∈ dEvenStab m (1 : DVec m) ↔ ∃ σ : Equiv.Perm (Fin m), dPerm m σ = w := by
  constructor
  · intro hw
    obtain ⟨σ, hσ⟩ := qtwoDRMStab_eq_dPerm_of_fix hw.1 hw.2
    exact ⟨σ, hσ.symm⟩
  · rintro ⟨σ, rfl⟩
    exact ⟨dPerm_mem_dEven m σ, qtwoDRMStab_dPerm_const σ 1⟩

private lemma p9uRMAP_entry_rel {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m), b * dPerm m σ = dPerm m σ * b)
    (σ : Equiv.Perm (Fin m)) (a k : Fin m) :
    (b (dBasis m (σ a))) k = (b (dBasis m a)) (σ.symm k) := by
  have h := congrArg (fun (g : DVec m ≃ₗ[ZMod 3] DVec m) => g (dBasis m a)) (hb σ)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  have h2 := congrArg (fun v : DVec m => v k) h
  rw [dPerm_apply, p9uRMAP_dPerm_eval] at h2
  exact h2

private lemma p9uRMAP_entry_diag {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m), b * dPerm m σ = dPerm m σ * b)
    {i j : Fin m} (hij : i ≠ j) :
    (b (dBasis m i)) i = (b (dBasis m j)) j := by
  have h := p9uRMAP_entry_rel hb (Equiv.swap i j) j i
  simpa [Equiv.symm_swap, Equiv.swap_apply_right, Equiv.swap_apply_left] using h

private lemma p9uRMAP_entry_symm {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m), b * dPerm m σ = dPerm m σ * b)
    {i j : Fin m} (hij : i ≠ j) :
    (b (dBasis m i)) j = (b (dBasis m j)) i := by
  have h := p9uRMAP_entry_rel hb (Equiv.swap i j) j j
  simpa [Equiv.symm_swap, Equiv.swap_apply_right, Equiv.swap_apply_left] using h

private lemma p9uRMAP_entry_col {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m), b * dPerm m σ = dPerm m σ * b)
    {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    (b (dBasis m i)) k = (b (dBasis m j)) k := by
  have h := p9uRMAP_entry_rel hb (Equiv.swap i j) j k
  simpa [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hki hkj] using h

private lemma p9uRMAP_centralizer_form (hm2 : 2 ≤ m) {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m), b * dPerm m σ = dPerm m σ * b) :
    ∃ p q : ZMod 3, ∀ v : DVec m, b v = p • v + q • (∑ i, v i) • (1 : DVec m) := by
  classical
  set i0 : Fin m := ⟨0, by omega⟩ with hi0
  set i1 : Fin m := ⟨1, by omega⟩ with hi1
  have h01 : i0 ≠ i1 := by rw [hi0, hi1]; simp [Fin.ext_iff]
  set d : ZMod 3 := (b (dBasis m i0)) i0 with hd
  set q : ZMod 3 := (b (dBasis m i1)) i0 with hq
  have hdiag : ∀ i, (b (dBasis m i)) i = d := by
    intro i
    by_cases h : i = i0
    · subst h; rfl
    · rw [hd]; exact p9uRMAP_entry_diag hb h
  have hsym01 : (b (dBasis m i0)) i1 = q := by
    rw [hq]; exact p9uRMAP_entry_symm hb h01
  have hcol0 : ∀ k, k ≠ i0 → (b (dBasis m i0)) k = q := by
    intro k hk
    by_cases hk1 : k = i1
    · subst hk1; exact hsym01
    · rw [p9uRMAP_entry_col hb h01 hk hk1,
        p9uRMAP_entry_symm hb (Ne.symm hk1),
        p9uRMAP_entry_col hb hk (Ne.symm hk1) (Ne.symm h01), hsym01]
  have hoff : ∀ i j, i ≠ j → (b (dBasis m i)) j = q := by
    intro i j hij
    by_cases hi0 : i = i0
    · subst hi0; exact hcol0 j (Ne.symm hij)
    · by_cases hj0 : j = i0
      · subst hj0; rw [p9uRMAP_entry_symm hb hij]; exact hcol0 i hi0
      · rw [p9uRMAP_entry_col hb hi0 (Ne.symm hij) hj0]; exact hcol0 j hj0
  refine ⟨d - q, q, fun v => ?_⟩
  have hb_i : ∀ i, b (dBasis m i) = (d - q) • dBasis m i + q • (1 : DVec m) := by
    intro i
    funext k
    by_cases hk : k = i
    · subst k
      rw [hdiag i]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
      rw [show (dBasis m i) i = 1 from by simp [dBasis, Pi.basisFun_apply]]
      ring
    · rw [hoff i k (Ne.symm hk)]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
      rw [show (dBasis m i) k = 0 from by
        simp [dBasis, Pi.basisFun_apply, Pi.single_apply, hk]]
      ring
  calc b v = b (∑ i, v i • dBasis m i) := by rw [p9uRMAP_sum_basis v]
    _ = ∑ i, v i • b (dBasis m i) := by rw [map_sum]; simp only [map_smul]
    _ = ∑ i, v i • ((d - q) • dBasis m i + q • (1 : DVec m)) :=
          Finset.sum_congr rfl fun i _ => by rw [hb_i i]
    _ = (d - q) • v + q • (∑ i, v i) • (1 : DVec m) := by
          simp only [smul_add, Finset.sum_add_distrib]
          congr 1
          · calc ∑ i, v i • ((d - q) • dBasis m i)
                = ∑ i, (d - q) • (v i • dBasis m i) := by
                    apply Finset.sum_congr rfl; intro i _
                    rw [smul_smul, smul_smul, mul_comm (v i) (d - q)]
                _ = (d - q) • ∑ i, v i • dBasis m i := by rw [Finset.smul_sum]
                _ = (d - q) • v := by rw [p9uRMAP_sum_basis v]
          · calc ∑ i, v i • (q • (1 : DVec m))
                = ∑ i, q • (v i • (1 : DVec m)) := by
                    apply Finset.sum_congr rfl; intro i _
                    rw [smul_smul, smul_smul, mul_comm (v i) q]
                _ = q • ∑ i, v i • (1 : DVec m) := by rw [Finset.smul_sum]
                _ = q • (∑ i, v i) • (1 : DVec m) := by rw [Finset.sum_smul]

private noncomputable def p9uRMAP_conjPerm {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m),
      ∃ τ : Equiv.Perm (Fin m), dPerm m τ = b * dPerm m σ * b⁻¹)
    (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin m) :=
  Classical.choose (hb σ)

private lemma p9uRMAP_conjPerm_spec {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m),
      ∃ τ : Equiv.Perm (Fin m), dPerm m τ = b * dPerm m σ * b⁻¹)
    (σ : Equiv.Perm (Fin m)) :
    dPerm m (p9uRMAP_conjPerm hb σ) = b * dPerm m σ * b⁻¹ :=
  Classical.choose_spec (hb σ)

private noncomputable def p9uRMAP_psi {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m),
      ∃ τ : Equiv.Perm (Fin m), dPerm m τ = b * dPerm m σ * b⁻¹) :
    Equiv.Perm (Fin m) →* Equiv.Perm (Fin m) where
  toFun := p9uRMAP_conjPerm hb
  map_one' := by
    refine p9uRMAP_dPerm_injective ?_
    simp only [p9uRMAP_conjPerm_spec, dPerm_one]
    group
  map_mul' := fun σ τ => by
    refine p9uRMAP_dPerm_injective ?_
    simp only [p9uRMAP_conjPerm_spec, dPerm_mul]
    group

private lemma p9uRMAP_psi_injective {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m),
      ∃ τ : Equiv.Perm (Fin m), dPerm m τ = b * dPerm m σ * b⁻¹) :
    Function.Injective (p9uRMAP_psi hb) := by
  intro σ τ h
  have h1 : b * dPerm m σ * b⁻¹ = b * dPerm m τ * b⁻¹ := by
    have h' : dPerm m (p9uRMAP_conjPerm hb σ) = dPerm m (p9uRMAP_conjPerm hb τ) :=
      congrArg (dPerm m) (show p9uRMAP_conjPerm hb σ = p9uRMAP_conjPerm hb τ from h)
    rwa [p9uRMAP_conjPerm_spec hb σ, p9uRMAP_conjPerm_spec hb τ] at h'
  have h2 : dPerm m σ = dPerm m τ := by
    have h3 := mul_right_cancel h1
    exact mul_left_cancel h3
  exact p9uRMAP_dPerm_injective h2

private noncomputable def p9uRMAP_conjAut {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m),
      ∃ τ : Equiv.Perm (Fin m), dPerm m τ = b * dPerm m σ * b⁻¹) :
    MulAut (Equiv.Perm (Fin m)) :=
  MulEquiv.ofBijective (p9uRMAP_psi hb)
    ⟨p9uRMAP_psi_injective hb, Finite.injective_iff_surjective.mp (p9uRMAP_psi_injective hb)⟩

private lemma p9uRMAP_dPerm_swap_sub {a₀ b₀ : Fin m} (hab : a₀ ≠ b₀) (u : DVec m) :
    dPerm m (Equiv.swap a₀ b₀) u - u = (u b₀ - u a₀) • (Pi.single a₀ 1 - Pi.single b₀ 1) := by
  funext i
  rw [Pi.sub_apply, p9uRMAP_dPerm_eval, Equiv.symm_swap, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul]
  by_cases hia : i = a₀
  · subst hia
    rw [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne hab]
    ring
  · by_cases hib : i = b₀
    · subst hib
      rw [Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_of_ne hia]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]
      ring

private lemma p9uRMAP_conjPerm_isSwap {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m),
      ∃ τ : Equiv.Perm (Fin m), dPerm m τ = b * dPerm m σ * b⁻¹)
    {σ : Equiv.Perm (Fin m)} (hσ : σ.IsSwap) : (p9uRMAP_conjPerm hb σ).IsSwap := by
  obtain ⟨a₀, b₀, hab, rfl⟩ := hσ
  set τ := p9uRMAP_conjPerm hb (Equiv.swap a₀ b₀) with hτdef
  have hτ : dPerm m τ = b * dPerm m (Equiv.swap a₀ b₀) * b⁻¹ := p9uRMAP_conjPerm_spec hb _
  have hs : dPerm m (Equiv.swap a₀ b₀) * dPerm m (Equiv.swap a₀ b₀) = 1 := by
    rw [← dPerm_mul, Equiv.swap_mul_self, dPerm_one]
  have hτ2 : ∀ i, τ (τ i) = i := by
    have h : τ * τ = 1 := by
      apply p9uRMAP_dPerm_injective
      rw [dPerm_mul, hτ, dPerm_one]
      calc b * dPerm m (Equiv.swap a₀ b₀) * b⁻¹ * (b * dPerm m (Equiv.swap a₀ b₀) * b⁻¹)
          = b * (dPerm m (Equiv.swap a₀ b₀) * dPerm m (Equiv.swap a₀ b₀)) * b⁻¹ := by group
        _ = 1 := by rw [hs, mul_one, mul_inv_cancel]
    exact fun i => congrArg (fun π : Equiv.Perm (Fin m) => π i) h
  have hτ1 : τ ≠ 1 := by
    intro h1
    rw [h1, dPerm_one] at hτ
    have h2 : dPerm m (Equiv.swap a₀ b₀) = 1 := by
      calc dPerm m (Equiv.swap a₀ b₀) = b⁻¹ * (b * dPerm m (Equiv.swap a₀ b₀) * b⁻¹) * b := by
            group
        _ = 1 := by rw [← hτ]; group
    have h3 := p9uRMAP_dPerm_injective (h2.trans (dPerm_one m).symm)
    have h4 := congrArg (fun π : Equiv.Perm (Fin m) => π a₀) h3
    simp only [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h4
    exact hab h4.symm
  have hmove : ∀ v, ∃ k : ZMod 3,
      dPerm m τ v - v = k • b (Pi.single a₀ 1 - Pi.single b₀ 1) := by
    intro v
    set u := b⁻¹ v with hu
    have hv : b u = v := by
      rw [hu, ← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    refine ⟨u b₀ - u a₀, ?_⟩
    rw [hτ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hu]
    rw [← hv]
    rw [← map_sub, p9uRMAP_dPerm_swap_sub hab, map_smul]
  by_contra hns
  have hcard : 3 ≤ τ.support.card := by
    have h0 : τ.support.card ≠ 0 := by
      rw [Ne, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff]
      exact hτ1
    have h1 : τ.support.card ≠ 1 := Equiv.Perm.card_support_ne_one τ
    have h2 : τ.support.card ≠ 2 := fun h => hns (Equiv.Perm.card_support_eq_two.mp h)
    omega
  obtain ⟨a, ha⟩ : τ.support.Nonempty := Finset.card_pos.mp (by omega)
  have ha' : τ a ≠ a := Equiv.Perm.mem_support.mp ha
  obtain ⟨c, hc⟩ : ((τ.support.erase a).erase (τ a)).Nonempty := by
    apply Finset.card_pos.mp
    have hτa : τ a ∈ τ.support.erase a := by
      refine Finset.mem_erase.mpr ⟨ha', Equiv.Perm.mem_support.mpr ?_⟩
      rw [hτ2]
      exact ha'.symm
    rw [Finset.card_erase_of_mem hτa, Finset.card_erase_of_mem ha]
    omega
  obtain ⟨hca', hc1⟩ := Finset.mem_erase.mp hc
  obtain ⟨hca, hc2⟩ := Finset.mem_erase.mp hc1
  have hc' : τ c ≠ c := Equiv.Perm.mem_support.mp hc2
  obtain ⟨k₁, hk₁⟩ := hmove (Pi.single a 1)
  obtain ⟨k₂, hk₂⟩ := hmove (Pi.single c 1)
  have hPa : dPerm m τ (Pi.single a 1) = Pi.single (τ a) 1 := by
    simpa only [dBasis, Pi.basisFun_apply] using dPerm_apply m τ a
  have hPc : dPerm m τ (Pi.single c 1) = Pi.single (τ c) 1 := by
    simpa only [dBasis, Pi.basisFun_apply] using dPerm_apply m τ c
  rw [hPa] at hk₁
  rw [hPc] at hk₂
  have hk₁0 : k₁ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, sub_eq_zero] at hk₁
    have h := congrFun hk₁ a
    rw [Pi.single_eq_same, Pi.single_eq_of_ne ha'.symm] at h
    exact one_ne_zero h.symm
  have h1c := congrFun hk₁ c
  have h2c := congrFun hk₂ c
  rw [Pi.sub_apply, Pi.single_eq_of_ne hca', Pi.single_eq_of_ne hca, sub_zero, Pi.smul_apply,
    smul_eq_mul] at h1c
  rw [Pi.sub_apply, Pi.single_eq_of_ne hc'.symm, Pi.single_eq_same, Pi.smul_apply,
    smul_eq_mul] at h2c
  have hW : b (Pi.single a₀ 1 - Pi.single b₀ 1) c = 0 :=
    (show ∀ x y : ZMod 3, x ≠ 0 → x * y = 0 → y = 0 by decide) _ _ hk₁0 h1c.symm
  rw [hW, mul_zero] at h2c
  exact absurd h2c (by decide)

theorem qtwoDRMStab_normalizer_dPerm (hm2 : 2 ≤ m)
    {b : DVec m ≃ₗ[ZMod 3] DVec m}
    (hb : ∀ σ : Equiv.Perm (Fin m),
      ∃ τ : Equiv.Perm (Fin m), dPerm m τ = b * dPerm m σ * b⁻¹) :
    ∃ (β : Equiv.Perm (Fin m)) (p q : ZMod 3),
      ∀ v : DVec m, b v = dPerm m β (p • v + q • (∑ i, v i) • (1 : DVec m)) := by
  obtain ⟨β, hβ⟩ : ∃ β : Equiv.Perm (Fin m), ∀ σ, p9uRMAP_conjAut hb σ = β * σ * β⁻¹ := by
    by_cases hm5 : 5 ≤ m
    · exact CFSG.LargeExtraspecial.AS35YF.perm_aut_eq_conj_of_isSwap (p9uRMAP_conjAut hb)
        (fun σ hσ => p9uRMAP_conjPerm_isSwap hb hσ) hm5
    · exact CFSG.ComponentClassification.RankTwoAlt.mulAut_perm_fin_inner (by omega)
        (p9uRMAP_conjAut hb)
  have hpi : ∀ σ, p9uRMAP_conjPerm hb σ = β * σ * β⁻¹ := fun σ => hβ σ
  have hb_eq : ∀ σ, b * dPerm m σ = dPerm m β * dPerm m σ * (dPerm m β)⁻¹ * b := by
    intro σ
    have h := p9uRMAP_conjPerm_spec hb σ
    rw [hpi σ] at h
    have h4 : dPerm m (β * σ * β⁻¹) = dPerm m β * dPerm m σ * (dPerm m β)⁻¹ := by
      rw [dPerm_mul, dPerm_mul, p9uRMAP_dPerm_inv]
    rw [h4] at h
    calc b * dPerm m σ = (b * dPerm m σ * b⁻¹) * b := by group
      _ = (dPerm m β * dPerm m σ * (dPerm m β)⁻¹) * b := by rw [← h]
  have hcomm : ∀ σ, ((dPerm m β)⁻¹ * b) * dPerm m σ = dPerm m σ * ((dPerm m β)⁻¹ * b) := by
    intro σ
    calc ((dPerm m β)⁻¹ * b) * dPerm m σ
        = (dPerm m β)⁻¹ * (b * dPerm m σ) := by group
      _ = (dPerm m β)⁻¹ * (dPerm m β * dPerm m σ * (dPerm m β)⁻¹ * b) := by rw [hb_eq σ]
      _ = dPerm m σ * ((dPerm m β)⁻¹ * b) := by group
  obtain ⟨p, q, hpq⟩ := p9uRMAP_centralizer_form hm2 hcomm
  refine ⟨β, p, q, fun v => ?_⟩
  have hL : ((dPerm m β)⁻¹ * b) v = p • v + q • (∑ i, v i) • (1 : DVec m) := hpq v
  have hb_decomp : b = dPerm m β * ((dPerm m β)⁻¹ * b) := by
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  calc b v = (dPerm m β * ((dPerm m β)⁻¹ * b)) v := by conv_lhs => rw [hb_decomp]
    _ = dPerm m β (((dPerm m β)⁻¹ * b) v) := by rw [LinearEquiv.mul_apply]
    _ = dPerm m β (p • v + q • (∑ i, v i) • (1 : DVec m)) := by rw [hL]

end CFSG.StandardType.QTwo

end
