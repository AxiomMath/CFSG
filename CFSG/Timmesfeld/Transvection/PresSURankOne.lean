module

public import CFSG.Timmesfeld.Transvection.PresSUHalf
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.RootSystem CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.SpecialLinear (signedPerm)
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open CFSG.LieType.Universal.Symplectic (stdVec)
open scoped commutatorElement

variable {m : ℕ} {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

section Short

variable {i : Fin (m / 2)} (hk : i.val + 1 < m / 2)

theorem idx_short : idx (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inr ⟨i.val + 1, hk⟩) :=
  fun h => by simp [idx, Fin.ext_iff] at h

theorem idx_short' :
    idx (Sum.inl ⟨i.val + 1, hk⟩ : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inr i) :=
  fun h => by simp [idx, Fin.ext_iff] at h

theorem suElt_short_eq (c : F) :
    suElt σ hσ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) c =
      rootHom σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _)
        (Multiplicative.ofAdd c) := by
  rw [suElt, dite_eq_left (idx_short hk)]
  rfl

theorem suElt_short_eq' (c : F) :
    suElt σ hσ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) c =
      rootHom σ hσ (lowIdx_ne_succ hk).symm (lowIdx_ne_rev _ _) (lowIdx_ne_rev i i)
        (Multiplicative.ofAdd c) := by
  rw [suElt, dite_eq_left (idx_short' hk)]
  rfl

theorem shortWeyl_eq (t : F) :
    suElt σ hσ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t *
        suElt σ hσ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) (-t⁻¹) *
        suElt σ hσ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t =
      shortWeyl σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _) t := by
  rw [suElt_short_eq hσ hk, suElt_short_eq' hσ hk, shortWeyl_def]

theorem coe_shortWeyl_level {t : F} (ht : t ≠ 0) :
    ((shortWeyl σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _) t :
      GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      signedPerm (levelPerm i) (shortSign σ (lowIdx i) (lowIdx ⟨i.val + 1, hk⟩) t) := by
  rw [coe_shortWeyl σ hσ _ _ _ (lowIdx_ne_rev _ _) ht, levelPerm, dite_eq_left hk]

theorem shortWeyl_conj_mem {t : F} (ht : t ≠ 0) {γ : Fin (m / 2) → ℤ} {x : SU σ m}
    (hx : x ∈ rootGroup σ hσ m γ) :
    shortWeyl σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _) t * x *
        (shortWeyl σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _) t)⁻¹ ∈
      rootGroup σ hσ m ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i γ) := by
  have h := conj_mem_rootGroup hσ _ (coe_shortWeyl_level hσ hk ht) (levelPerm_rev i)
    (shortSign_unitary hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _)
      (lowIdx_ne_rev _ _) ht) (weight_levelPerm i) (stdRefl_sub i) (stdRefl_nsmul i 2)
    (γ' := (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i γ)
    (by rw [← Unitary.toStd_reflection]; rfl) x hx
  exact h

theorem shortWeyl_conj_x {t : F} (ht : t ≠ 0) (a : F) :
    shortWeyl σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _) t *
        suElt σ hσ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) a *
        (shortWeyl σ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _) t)⁻¹ =
      suElt σ hσ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) (-(t ^ 2)⁻¹ * a) := by
  apply conj_eq_of_coe
  rw [coe_shortWeyl_level hσ hk ht, suElt_short_eq hσ hk, suElt_short_eq' hσ hk, coe_rootHom,
    coe_rootHom, toAdd_ofAdd, toAdd_ofAdd,
    signedPerm_mul_rootMatrix (levelPerm_rev i)
      (shortSign_unitary hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev i i) (lowIdx_ne_rev _ _)
        (lowIdx_ne_rev _ _) ht)]
  have hab := lowIdx_ne_succ (n := m) hk
  have h1 : lowIdx (n := m) i ≠ Fin.rev (lowIdx i) := lowIdx_ne_rev i i
  have h2 : lowIdx (n := m) i ≠ Fin.rev (lowIdx ⟨i.val + 1, hk⟩) := lowIdx_ne_rev _ _
  have h3 : lowIdx (n := m) ⟨i.val + 1, hk⟩ ≠ Fin.rev (lowIdx i) := lowIdx_ne_rev _ _
  have h4 : lowIdx (n := m) ⟨i.val + 1, hk⟩ ≠ Fin.rev (lowIdx ⟨i.val + 1, hk⟩) := lowIdx_ne_rev _ _
  have hπa : levelPerm (n := m) i (lowIdx i) = lowIdx ⟨i.val + 1, hk⟩ := by
    rw [levelPerm, dite_eq_left hk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_left]
  have hπb : levelPerm (n := m) i (lowIdx ⟨i.val + 1, hk⟩) = lowIdx i := by
    rw [levelPerm, dite_eq_left hk, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne h3 h4, Equiv.swap_apply_right]
  have hda : shortSign σ (lowIdx (n := m) i) (lowIdx ⟨i.val + 1, hk⟩) t (lowIdx i) = -t⁻¹ := by
    simp [shortSign]
  have hdb : shortSign σ (lowIdx (n := m) i) (lowIdx ⟨i.val + 1, hk⟩) t
      (lowIdx ⟨i.val + 1, hk⟩) = t := by
    simp [shortSign, Ne.symm hab]
  rw [hπa, hπb, hda, hdb]
  congr 2
  field_simp

end Short

section Long

variable {i : Fin (m / 2)} (hk : ¬i.val + 1 < m / 2)

theorem suLong_last_eq {c : F} (hc : c + σ c = 0) :
    suLong σ (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) c =
      longRootHom σ (lowIdx_ne_rev i i) (Multiplicative.ofAdd ⟨c, hc⟩) := by
  rw [suLong, dite_eq_left hc]
  rfl

theorem suLong_last_eq' {c : F} (hc : c + σ c = 0) :
    suLong σ (Sum.inr i : Fin (m / 2) ⊕ Fin (m / 2)) c =
      longRootHom σ (rev_ne_rev_rev (lowIdx_ne_rev i i)) (Multiplicative.ofAdd ⟨c, hc⟩) := by
  rw [suLong, dite_eq_left hc]
  rfl

theorem longWeyl_eq {z : F} (hz : z + σ z = 0) :
    suLong σ (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) z * suLong σ (Sum.inr i) (-z⁻¹) *
        suLong σ (Sum.inl i) z = longWeyl σ (lowIdx_ne_rev i i) ⟨z, hz⟩ := by
  rw [suLong_last_eq hz, suLong_last_eq' (neg_inv_add_map_eq_zero σ hz), longWeyl_def]

include hk in
theorem coe_longWeyl_level {z : traceZero σ} (hz : (z : F) ≠ 0) :
    ((longWeyl σ (lowIdx_ne_rev i i) z : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      signedPerm (levelPerm i) (longSign (lowIdx i) (z : F)) := by
  rw [coe_longWeyl σ _ hz, levelPerm, dite_eq_right hk]

include hk in
theorem longWeyl_conj_mem {z : traceZero σ} (hz : (z : F) ≠ 0) {γ : Fin (m / 2) → ℤ}
    {x : SU σ m} (hx : x ∈ rootGroup σ hσ m γ) :
    longWeyl σ (lowIdx_ne_rev i i) z * x * (longWeyl σ (lowIdx_ne_rev i i) z)⁻¹ ∈
      rootGroup σ hσ m ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i γ) :=
  conj_mem_rootGroup hσ _ (coe_longWeyl_level hk hz) (levelPerm_rev i)
    (longSign_unitary (lowIdx_ne_rev i i) z.2 hz) (weight_levelPerm i) (stdRefl_sub i)
    (stdRefl_nsmul i 2) (γ' := (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i γ)
    (by rw [← Unitary.toStd_reflection]; rfl) x hx

include hk in
theorem longWeyl_conj_x {z : traceZero σ} (hz : (z : F) ≠ 0) {a : F} (ha : a + σ a = 0) :
    longWeyl σ (lowIdx_ne_rev i i) z * suLong σ (Sum.inl i) a *
        (longWeyl σ (lowIdx_ne_rev i i) z)⁻¹ =
      suLong σ (Sum.inr i) (-((z : F) ^ 2)⁻¹ * a) := by
  have hc : -((z : F) ^ 2)⁻¹ * a + σ (-((z : F) ^ 2)⁻¹ * a) = 0 := by
    have hz0 : (z : F) + σ (z : F) = 0 := z.2
    have hz' : σ (z : F) = -(z : F) := by linear_combination hz0
    have ha' : σ a = -a := by linear_combination ha
    rw [map_mul, map_neg, map_inv₀, map_pow, hz', ha']
    ring
  apply conj_eq_of_coe
  rw [coe_longWeyl_level hk hz, suLong_last_eq ha, suLong_last_eq' hc, coe_longRootHom,
    coe_longRootHom, toAdd_ofAdd, toAdd_ofAdd,
    signedPerm_mul_longRootMatrix (levelPerm_rev i) (longSign_unitary (lowIdx_ne_rev i i) z.2 hz)]
  have h1 : lowIdx (n := m) i ≠ Fin.rev (lowIdx i) := lowIdx_ne_rev i i
  have hπ : levelPerm (n := m) i (lowIdx i) = Fin.rev (lowIdx i) := by
    rw [levelPerm, dite_eq_right hk, Equiv.swap_apply_left]
  have hd1 : longSign (lowIdx (n := m) i) (z : F) (lowIdx i) = -(z : F)⁻¹ := by
    simp [longSign]
  have hd2 : longSign (lowIdx (n := m) i) (z : F) (Fin.rev (lowIdx i)) = (z : F) := by
    simp [longSign, Ne.symm h1]
  rw [hπ, hd1, hd2]
  congr 2
  field_simp

end Long

section Roots

omit [Field F] in
theorem toStd_even (he : Even m) (v : Fin (m / 2) → ℤ) :
    toStd m v = Symplectic.toStd (m / 2) v := by
  simp only [Unitary.toStd, ite_eq_left he]

omit [Field F] in
theorem exists_root_of_rt (he : Even m) {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : b ≠ Sum.swap a) :
    ∃ β ∈ roots (isFiniteType_cartan m) (divisible m), toStd m β = rt a b := by
  obtain ⟨β, -, hβ⟩ := CFSG.LieType.Steinberg.Sp.exists_root_of_stdVec (n := m / 2) (rtIdx a b)
  have e : toStd m β = rt a b := by rw [toStd_even he, hβ, stdVec_rtIdx hab]
  exact ⟨β, (mem_roots_iff_su he β).2 (e ▸ rt_mem hab), e⟩

omit [Field F] in
theorem linIndepPair_of_toStd {α β : Fin (m / 2) → ℤ}
    (h : LinIndepPair (toStd m α) (toStd m β)) : LinIndepPair α β := fun a b hab =>
  h a b (by rw [← toStd_zsmul, ← toStd_zsmul, ← toStd_add', hab, toStd_zero'])

omit [Field F] in
theorem linIndepPair_refl (i : Fin (m / 2)) {δ γ : Fin (m / 2) → ℤ} (h : LinIndepPair δ γ) :
    LinIndepPair ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i δ)
      ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i γ) := fun a b hab => by
  refine h a b ?_
  have := congrArg ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i) hab
  rwa [map_add, map_zsmul, map_zsmul, RootSystem.refl_refl, RootSystem.refl_refl, map_zero]
    at this

omit [Field F] in
theorem apply_refl_of_eq_zero {f : (Fin (m / 2) → ℤ) →+ ℤ} {i : Fin (m / 2)}
    (hf : f (Pi.single i 1) = 0) (v : Fin (m / 2) → ℤ) :
    f ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i v) = f v := by
  change f (reflection (cartan m) i v) = f v
  rw [reflection_apply_coroot, map_sub, map_zsmul, hf, smul_zero, sub_zero]

omit [Field F] in
theorem linIndepPair_of_det {ι : Type*} {u v : ι → ℤ} (j₁ j₂ : ι)
    (hdet : u j₁ * v j₂ - u j₂ * v j₁ ≠ 0) : LinIndepPair u v := fun x y h => by
  have h1 := congrFun h j₁
  have h2 := congrFun h j₂
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2
  constructor
  · by_contra hx
    apply hdet
    have : x * (u j₁ * v j₂ - u j₂ * v j₁) = 0 := by linear_combination v j₂ * h1 - v j₁ * h2
    exact (mul_eq_zero.1 this).resolve_left hx
  · by_contra hy
    apply hdet
    have : y * (u j₁ * v j₂ - u j₂ * v j₁) = 0 := by
      linear_combination -(u j₂ * h1) + u j₁ * h2
    exact (mul_eq_zero.1 this).resolve_left hy

section Short

variable {i : Fin (m / 2)} (hk : i.val + 1 < m / 2)

omit [Field F] in
theorem toStd_single_short :
    toStd m (Pi.single i 1) = rt (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) := by
  rw [toStd_single_of_lt m hk, rt_inl_inr]

omit [Field F] in
theorem exists_short_roots (he : Even m) :
    ∃ δ ∈ roots (isFiniteType_cartan m) (divisible m),
      ∃ γ ∈ roots (isFiniteType_cartan m) (divisible m),
        ∃ ε ∈ roots (isFiniteType_cartan m) (divisible m),
          toStd m δ = rt (Sum.inl i) (Sum.inl ⟨i.val + 1, hk⟩) ∧
          toStd m γ = rt (Sum.inr ⟨i.val + 1, hk⟩) (Sum.inr ⟨i.val + 1, hk⟩) ∧
          toStd m ε = rt (Sum.inl i) (Sum.inl i) ∧ Pi.single i 1 = δ + γ ∧ ε = 2 • δ + γ ∧
          LinIndepPair (Pi.single i 1) δ ∧ LinIndepPair (Pi.single i 1) γ ∧
          LinIndepPair (Pi.single i 1) ε ∧ LinIndepPair δ γ := by
  have hii' : i ≠ ⟨i.val + 1, hk⟩ := Fin.ne_of_val_ne (by simp)
  have hpp' : idx (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inl ⟨i.val + 1, hk⟩) :=
    fun h => by simp [idx, Fin.ext_iff] at h
  obtain ⟨δ, hδ, hδe⟩ := exists_root_of_rt he (ne_swap_of_idx_ne hpp')
  obtain ⟨γ, hγ, hγe⟩ := exists_root_of_rt he
    (swap_ne_self (Sum.inr ⟨i.val + 1, hk⟩ : Fin (m / 2) ⊕ Fin (m / 2))).symm
  obtain ⟨ε, hε, hεe⟩ := exists_root_of_rt he
    (swap_ne_self (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2))).symm
  have hαe := toStd_single_short (m := m) hk
  refine ⟨δ, hδ, γ, hγ, ε, hε, hδe, hγe, hεe, toStd_injective m ?_, toStd_injective m ?_,
    linIndepPair_of_toStd (linIndepPair_of_det i ⟨i.val + 1, hk⟩ ?_),
    linIndepPair_of_toStd (linIndepPair_of_det i ⟨i.val + 1, hk⟩ ?_),
    linIndepPair_of_toStd (linIndepPair_of_det i ⟨i.val + 1, hk⟩ ?_),
    linIndepPair_of_toStd (linIndepPair_of_det i ⟨i.val + 1, hk⟩ ?_)⟩
  · rw [toStd_add', hδe, hγe, hαe]
    simp only [rt, Symplectic.SpExtras.wt]
    abel
  · rw [toStd_add', toStd_nsmul, hδe, hγe, hεe]
    simp only [rt, Symplectic.SpExtras.wt]
    abel
  · rw [hαe, hδe]
    simp [rt, Symplectic.SpExtras.wt, hii', Ne.symm hii']
  · rw [hαe, hγe]
    simp [rt, Symplectic.SpExtras.wt, hii', Ne.symm hii']
  · rw [hαe, hεe]
    simp [rt, Symplectic.SpExtras.wt, hii', Ne.symm hii']
  · rw [hδe, hγe]
    simp [rt, Symplectic.SpExtras.wt, hii', Ne.symm hii']

end Short

section Long

variable {i : Fin (m / 2)} (hk : ¬i.val + 1 < m / 2)

omit [Field F] in
include hk in
theorem toStd_single_last_even (he : Even m) :
    toStd m (Pi.single i 1) = rt (Sum.inl i) (Sum.inl i) := by
  rw [toStd_single_of_even he hk, rt_inl_inl]

omit [Field F] in
include hk in
theorem exists_long_roots (he : Even m) {j : Fin (m / 2)} (hj : j.val + 1 = i.val) :
    ∃ δ ∈ roots (isFiniteType_cartan m) (divisible m),
      ∃ δ₂ ∈ roots (isFiniteType_cartan m) (divisible m),
        toStd m δ = rt (Sum.inl i) (Sum.inl j) ∧ toStd m δ₂ = rt (Sum.inl i) (Sum.inr j) ∧
          Pi.single i 1 = δ + δ₂ ∧ LinIndepPair (Pi.single i 1) δ ∧
          LinIndepPair (Pi.single i 1) δ₂ ∧ LinIndepPair δ δ₂ := by
  have hij : i ≠ j := fun h => by rw [h] at hj; omega
  have hij₁ : idx (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inl j) := hij
  have hij₂ : idx (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inr j) := hij
  obtain ⟨δ, hδ, hδe⟩ := exists_root_of_rt he (ne_swap_of_idx_ne hij₁)
  obtain ⟨δ₂, hδ₂, hδ₂e⟩ := exists_root_of_rt he (ne_swap_of_idx_ne hij₂)
  have hαe := toStd_single_last_even hk he
  refine ⟨δ, hδ, δ₂, hδ₂, hδe, hδ₂e, toStd_injective m ?_,
    linIndepPair_of_toStd (linIndepPair_of_det i j ?_),
    linIndepPair_of_toStd (linIndepPair_of_det i j ?_),
    linIndepPair_of_toStd (linIndepPair_of_det i j ?_)⟩
  · rw [toStd_add', hδe, hδ₂e, hαe]
    simp only [rt, Symplectic.SpExtras.wt]
    abel
  · rw [hαe, hδe]
    simp [rt, Symplectic.SpExtras.wt, hij, Ne.symm hij]
  · rw [hαe, hδ₂e]
    simp [rt, Symplectic.SpExtras.wt, hij, Ne.symm hij]
  · rw [hδe, hδ₂e]
    simp [rt, Symplectic.SpExtras.wt, hij, Ne.symm hij]

end Long

end Roots

section Relation

variable [Finite F] [CharP F 2] {G : Type*} [Group G] (R : SURelations (m / 2) σ G)
  (he : Even m)

section Short

variable {i : Fin (m / 2)} (hk : i.val + 1 < m / 2)

include he in
theorem SURelations.conj_short {t : F} (ht : t ≠ 0) {β : Fin (m / 2) → ℤ}
    (hβ : β ∈ roots (isFiniteType_cartan m) (divisible m)) (hlin : LinIndepPair (Pi.single i 1) β)
    (z : rootGroup σ hσ m β) :
    R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t *
        R.ξ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) (-t⁻¹) *
        R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t * suPsi hσ R he β z *
        (R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t *
          R.ξ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) (-t⁻¹) *
          R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t)⁻¹ =
      suPsi hσ R he ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i β)
        ⟨_, shortWeyl_conj_mem hσ hk ht z.2⟩ := by
  obtain ⟨f, hf0, hfβ⟩ := exists_addHom_eq_zero_pos hlin
  have hα : Pi.single i 1 ∈ (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).roots :=
    (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).single_mem i
  have hαe := toStd_single_short hk
  have hαe' : toStd m (-Pi.single i 1) = rt (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) := by
    rw [toStd_neg, hαe, rt_inl_inr, rt_inl_inr, neg_sub]
  have hv : RElValid σ (Sum.inl i, Sum.inr ⟨i.val + 1, hk⟩, t) :=
    relValid_short (idx_short hk) t
  have hv' : RElValid σ (Sum.inl ⟨i.val + 1, hk⟩, Sum.inr i, -t⁻¹) :=
    relValid_short (idx_short' hk) _
  have e1 := suPsi_eval hσ R he hv hαe
  have e2 := suPsi_eval hσ R he hv' hαe'
  rw [R.eval_short (ne_of_idx_ne (idx_short hk))] at e1
  rw [R.eval_short (ne_of_idx_ne (idx_short' hk))] at e2
  have hβ' : (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i β ∈
      halfSpace (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)) f :=
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_mem i β hβ, by
      rw [apply_refl_of_eq_zero hf0]; exact hfβ⟩
  have key := conj_eq_of_halfSpace (commCompat_suPsi hσ R he)
    (extendsToHom_halfSpace_su hσ R he f) hα hf0
    ⟨_, eval_mem_rootGroup hσ hv hαe⟩ ⟨_, eval_mem_rootGroup hσ hv hαe⟩
    ⟨_, eval_mem_rootGroup hσ hv' hαe'⟩ ⟨hβ, hfβ⟩ hβ' z ⟨_, shortWeyl_conj_mem hσ hk ht z.2⟩
    (by
      simp only [SURelations.eval_short _ (ne_of_idx_ne (idx_short hk)),
        SURelations.eval_short _ (ne_of_idx_ne (idx_short' hk)), suRelationsModel_ξ]
      rw [shortWeyl_eq hσ hk])
  rw [e1, e2] at key
  exact key

include hσ he in
theorem SURelations.shortB {t : F} (ht : t ≠ 0) (a : F) :
    R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t *
        R.ξ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) (-t⁻¹) *
        R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t * R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) a *
        (R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t *
          R.ξ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) (-t⁻¹) *
          R.ξ (Sum.inl i) (Sum.inr ⟨i.val + 1, hk⟩) t)⁻¹ =
      R.ξ (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) (-(t ^ 2)⁻¹ * a) := by
  have hpp' : idx (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inl ⟨i.val + 1, hk⟩) :=
    fun h => by simp [idx, Fin.ext_iff] at h
  obtain ⟨δ, hδ, γ, hγ, ε, hε, hδe, hγe, hεe, hαδγ, hεδγ, hαδ, hαγ, hαε, hδγ⟩ :=
    exists_short_roots hk he
  have hαe' : toStd m (-Pi.single i 1) = rt (Sum.inl ⟨i.val + 1, hk⟩) (Sum.inr i) := by
    rw [toStd_neg, toStd_single_short hk, rt_inl_inr, rt_inl_inr, neg_sub]
  have hfix : σ (σ a * a) = σ a * a := by rw [map_mul, hσ, mul_comm]
  have hv₁ : RElValid σ (Sum.inl i, Sum.inl ⟨i.val + 1, hk⟩, a) := relValid_short hpp' a
  have hv₂ : RElValid σ (Sum.inr ⟨i.val + 1, hk⟩, Sum.inr ⟨i.val + 1, hk⟩, (1 : F)) :=
    relValid_long _ (map_one σ)
  have hv₃ : RElValid σ (Sum.inl i, Sum.inl i, σ a * a) := relValid_long _ hfix
  have hv₄ : RElValid σ (Sum.inl ⟨i.val + 1, hk⟩, Sum.inr i, -(t ^ 2)⁻¹ * a) :=
    relValid_short (idx_short' hk) _
  have e₁ := suPsi_eval hσ R he hv₁ hδe
  have e₂ := suPsi_eval hσ R he hv₂ hγe
  have e₃ := suPsi_eval hσ R he hv₃ hεe
  have e₄ := suPsi_eval hσ R he hv₄ hαe'
  rw [R.eval_short (ne_of_idx_ne hpp')] at e₁
  rw [R.eval_long] at e₂ e₃
  rw [R.eval_short (ne_of_idx_ne (idx_short' hk))] at e₄
  have hx := R.eq_commutator_shortLong hσ hpp' a
  rw [Sum.swap_inl] at hx
  rw [hx, conj_commutator_mul, ← e₁, ← e₂, ← e₃, ← e₄, R.conj_short hσ he hk ht hδ hαδ,
    R.conj_short hσ he hk ht hγ hαγ, R.conj_short hσ he hk ht hε hαε]
  obtain ⟨f, hfδ, hfγ⟩ := exists_addHom_pos_pos (linIndepPair_refl i hδγ)
  have hrε : (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i ε =
      2 • (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i δ +
        (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i γ := by
    rw [hεδγ, map_add, map_nsmul]
  have hrα : -Pi.single i 1 =
      (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i δ +
        (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i γ := by
    rw [← (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_single, hαδγ, map_add]
  refine commutator_mul_eq_of_extendsToHom (extendsToHom_halfSpace_su hσ R he f)
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_mem i δ hδ, hfδ⟩
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_mem i γ hγ, hfγ⟩
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_mem i ε hε, ?_⟩
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).neg_mem _
      ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).single_mem i), ?_⟩ _ _ _ _ ?_
  · rw [hrε, map_add, map_nsmul, nsmul_eq_mul]
    push_cast
    linarith
  · rw [hrα, map_add]
    linarith
  ·
    dsimp only
    have hxM := (suRelationsModel hσ m).eq_commutator_shortLong hσ hpp' a
    rw [Sum.swap_inl] at hxM
    rw [← conj_commutator_mul, SURelations.eval_short _ (ne_of_idx_ne hpp'),
      SURelations.eval_long, SURelations.eval_long,
      SURelations.eval_short _ (ne_of_idx_ne (idx_short' hk)), ← hxM, suRelationsModel_ξ]
    exact shortWeyl_conj_x hσ hk ht a

end Short

section Long

variable {i : Fin (m / 2)} (hk : ¬i.val + 1 < m / 2)

include he in
theorem SURelations.conj_long {z : F} (hz : σ z = z) (hz0 : z ≠ 0) {β : Fin (m / 2) → ℤ}
    (hβ : β ∈ roots (isFiniteType_cartan m) (divisible m)) (hlin : LinIndepPair (Pi.single i 1) β)
    (u : rootGroup σ hσ m β) :
    R.ξL (Sum.inl i) z * R.ξL (Sum.inr i) (-z⁻¹) * R.ξL (Sum.inl i) z * suPsi hσ R he β u *
        (R.ξL (Sum.inl i) z * R.ξL (Sum.inr i) (-z⁻¹) * R.ξL (Sum.inl i) z)⁻¹ =
      suPsi hσ R he ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i β)
        ⟨_, longWeyl_conj_mem hσ hk (z := ⟨z, add_map_eq_zero_iff.2 hz⟩) hz0 u.2⟩ := by
  obtain ⟨f, hf0, hfβ⟩ := exists_addHom_eq_zero_pos hlin
  have hα : Pi.single i 1 ∈ (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).roots :=
    (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).single_mem i
  have hαe := toStd_single_last_even hk he
  have hαe' : toStd m (-Pi.single i 1) = rt (Sum.inr i) (Sum.inr i) := by
    rw [toStd_neg, hαe, rt_inl_inl, rt_inr_inr]
  have hv : RElValid σ (Sum.inl i, Sum.inl i, z) := relValid_long _ hz
  have hv' : RElValid σ (Sum.inr i, Sum.inr i, -z⁻¹) :=
    relValid_long _ (by rw [map_neg, map_inv₀, hz])
  have e1 := suPsi_eval hσ R he hv hαe
  have e2 := suPsi_eval hσ R he hv' hαe'
  rw [R.eval_long] at e1 e2
  have hβ' : (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i β ∈
      halfSpace (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)) f :=
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_mem i β hβ, by
      rw [apply_refl_of_eq_zero hf0]; exact hfβ⟩
  have key := conj_eq_of_halfSpace (commCompat_suPsi hσ R he)
    (extendsToHom_halfSpace_su hσ R he f) hα hf0
    ⟨_, eval_mem_rootGroup hσ hv hαe⟩ ⟨_, eval_mem_rootGroup hσ hv hαe⟩
    ⟨_, eval_mem_rootGroup hσ hv' hαe'⟩ ⟨hβ, hfβ⟩ hβ' u
    ⟨_, longWeyl_conj_mem hσ hk (z := ⟨z, add_map_eq_zero_iff.2 hz⟩) hz0 u.2⟩
    (by
      simp only [SURelations.eval_long, suRelationsModel_ξL]
      rw [longWeyl_eq (add_map_eq_zero_iff.2 hz)])
  rw [e1, e2] at key
  exact key

include hσ he hk in
theorem SURelations.longB (hm : 4 ≤ m) (htr : ∀ c, σ c = c → ∃ s, s + σ s = c) {z : F}
    (hz : σ z = z) (hz0 : z ≠ 0) {c : F} (hc : σ c = c) :
    R.ξL (Sum.inl i) z * R.ξL (Sum.inr i) (-z⁻¹) * R.ξL (Sum.inl i) z * R.ξL (Sum.inl i) c *
        (R.ξL (Sum.inl i) z * R.ξL (Sum.inr i) (-z⁻¹) * R.ξL (Sum.inl i) z)⁻¹ =
      R.ξL (Sum.inr i) (-(z ^ 2)⁻¹ * c) := by
  have hi := i.isLt
  obtain ⟨j, hj⟩ : ∃ j : Fin (m / 2), j.val + 1 = i.val := ⟨⟨i.val - 1, by omega⟩, by
    simp only
    omega⟩
  have hij : i ≠ j := fun h => by rw [h] at hj; omega
  have hij₁ : idx (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inl j) := hij
  have hij₂ : idx (Sum.inl i : Fin (m / 2) ⊕ Fin (m / 2)) ≠ idx (Sum.inr j) := hij
  obtain ⟨δ, hδ, δ₂, hδ₂, hδe, hδ₂e, hαδδ, hαδ, hαδ₂, hδδ₂⟩ := exists_long_roots hk he hj
  obtain ⟨s, hs⟩ := htr c hc
  have hαe' : toStd m (-Pi.single i 1) = rt (Sum.inr i) (Sum.inr i) := by
    rw [toStd_neg, toStd_single_last_even hk he, rt_inl_inl, rt_inr_inr]
  have hfix : σ (-(z ^ 2)⁻¹ * c) = -(z ^ 2)⁻¹ * c := by
    rw [map_mul, map_neg, map_inv₀, map_pow, hz, hc]
  have hv₁ : RElValid σ (Sum.inl i, Sum.inl j, s) := relValid_short hij₁ s
  have hv₂ : RElValid σ (Sum.inl i, Sum.inr j, (1 : F)) := relValid_short hij₂ 1
  have hv₄ : RElValid σ (Sum.inr i, Sum.inr i, -(z ^ 2)⁻¹ * c) := relValid_long _ hfix
  have e₁ := suPsi_eval hσ R he hv₁ hδe
  have e₂ := suPsi_eval hσ R he hv₂ hδ₂e
  have e₄ := suPsi_eval hσ R he hv₄ hαe'
  rw [R.eval_short (ne_of_idx_ne hij₁)] at e₁
  rw [R.eval_short (ne_of_idx_ne hij₂)] at e₂
  rw [R.eval_long] at e₄
  have hx := R.eq_commutator_trace hij₁ s
  rw [hs, Sum.swap_inl] at hx
  rw [hx, conj_commutator, ← e₁, ← e₂, ← e₄, R.conj_long hσ he hk hz hz0 hδ hαδ,
    R.conj_long hσ he hk hz hz0 hδ₂ hαδ₂]
  obtain ⟨f, hf₁, hf₂⟩ := exists_addHom_pos_pos (linIndepPair_refl i hδδ₂)
  have hrα : -Pi.single i 1 =
      (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i δ +
        (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i δ₂ := by
    rw [← (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_single, hαδδ, map_add]
  refine commutator_eq_of_extendsToHom (extendsToHom_halfSpace_su hσ R he f)
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_mem i δ hδ, hf₁⟩
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl_mem i δ₂ hδ₂, hf₂⟩
    ⟨(RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).neg_mem _
      ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).single_mem i), ?_⟩ _ _ _ ?_
  · rw [hrα, map_add]
    linarith
  ·
    dsimp only
    have hxM := (suRelationsModel hσ m).eq_commutator_trace hij₁ s
    rw [hs, Sum.swap_inl] at hxM
    rw [← conj_commutator, SURelations.eval_short _ (ne_of_idx_ne hij₁),
      SURelations.eval_short _ (ne_of_idx_ne hij₂), SURelations.eval_long, ← hxM,
      suRelationsModel_ξL]
    exact longWeyl_conj_x hk (z := ⟨z, add_map_eq_zero_iff.2 hz⟩) hz0
      (add_map_eq_zero_iff.2 hc)

end Long

end Relation

end CFSG.Timmesfeld.Transvection
