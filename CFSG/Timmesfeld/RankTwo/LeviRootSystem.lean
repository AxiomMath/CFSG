module

public import CFSG.LieType.Steinberg.OfCartan

public section

namespace CFSG.Timmesfeld.Levi

open CFSG.LieType CFSG.LieType.Steinberg

section Coordinates

variable {ι : Type*} (J : Finset ι)

@[expose] def proj : (ι → ℤ) →+ (J → ℤ) where
  toFun v k := v k
  map_zero' := rfl
  map_add' _ _ := rfl

variable {J} in
@[simp] theorem proj_apply (v : ι → ℤ) (k : J) : proj J v k = v k := rfl

variable {J} in
theorem exists_map_val {w : List ι} (hw : ∀ l ∈ w, l ∈ J) :
    ∃ w' : List J, w'.map Subtype.val = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons a w ih =>
    obtain ⟨w', hw'⟩ := ih fun l hl => hw l (List.mem_cons_of_mem a hl)
    exact ⟨⟨a, hw a List.mem_cons_self⟩ :: w', by simp [hw']⟩

variable [DecidableEq ι]

@[expose] def incl : (J → ℤ) →+ (ι → ℤ) where
  toFun v k := if h : k ∈ J then v ⟨k, h⟩ else 0
  map_zero' := by
    funext k
    simp
  map_add' v w := by
    funext k
    by_cases h : k ∈ J <;> simp [h]

variable {J}

@[simp] theorem incl_apply_coe (v : J → ℤ) (k : J) : incl J v k = v k := by
  simp [incl]

theorem incl_apply_of_notMem (v : J → ℤ) {k : ι} (hk : k ∉ J) : incl J v k = 0 := by
  simp [incl, hk]

@[simp] theorem proj_incl (v : J → ℤ) : proj J (incl J v) = v :=
  funext fun k => incl_apply_coe v k

theorem incl_proj {v : ι → ℤ} (hv : ∀ k ∉ J, v k = 0) : incl J (proj J v) = v := by
  funext k
  by_cases hk : k ∈ J
  · exact incl_apply_coe _ ⟨k, hk⟩
  · rw [incl_apply_of_notMem _ hk, hv k hk]

theorem incl_injective : Function.Injective (incl J) := fun v w h => by
  rw [← proj_incl v, h, proj_incl]

theorem incl_apply_eq_zero (v : J → ℤ) : ∀ k ∉ J, incl J v k = 0 :=
  fun _ hk => incl_apply_of_notMem v hk

@[simp] theorem incl_single (j : J) : incl J (Pi.single j 1) = Pi.single (j : ι) 1 := by
  funext k
  by_cases hk : k ∈ J
  · rw [show k = ((⟨k, hk⟩ : J) : ι) from rfl, incl_apply_coe]
    simp only [Pi.single_apply, Subtype.ext_iff]
  · rw [incl_apply_of_notMem _ hk, Pi.single_eq_of_ne]
    rintro rfl
    exact hk j.2

@[simp] theorem proj_single (j : J) : proj J (Pi.single (j : ι) 1) = Pi.single j 1 := by
  rw [← incl_single, proj_incl]

theorem ht_incl [Fintype ι] (v : J → ℤ) : ht (incl J v) = ht v := by
  simp only [ht]
  rw [← Finset.sum_subset (Finset.subset_univ J) (fun k _ hk => incl_apply_of_notMem v hk),
    ← Finset.sum_coe_sort J]
  exact Finset.sum_congr rfl fun k _ => incl_apply_coe v k

end Coordinates

section Subsystem

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : Steinberg.RootSystem ι) (J : Finset ι)

@[expose] def HasParabolicWords : Prop :=
  ∀ γ ∈ Φ.roots, (∀ k ∉ J, γ k = 0) → Φ.IsIndiv γ →
    ∃ (w : List ι) (i : ι), (∀ l ∈ w, l ∈ J) ∧ i ∈ J ∧ γ = wordAct Φ.refl w (Pi.single i 1)

@[expose] def subRefl (j : J) : (J → ℤ) →+ (J → ℤ) := (proj J).comp ((Φ.refl j).comp (incl J))

variable {Φ J}

theorem refl_apply_eq_zero {v : ι → ℤ} (hv : ∀ k ∉ J, v k = 0) (j : J) :
    ∀ k ∉ J, Φ.refl j v k = 0 := fun k hk => by
  rw [Φ.refl_apply_of_ne _ _ _ (fun h => hk (by rw [h]; exact j.2)), hv k hk]

theorem incl_subRefl (j : J) (v : J → ℤ) : incl J (subRefl Φ J j v) = Φ.refl j (incl J v) :=
  incl_proj (refl_apply_eq_zero (incl_apply_eq_zero v) j)

theorem incl_wordAct (w : List J) (v : J → ℤ) :
    incl J (wordAct (subRefl Φ J) w v) = wordAct Φ.refl (w.map Subtype.val) (incl J v) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [wordAct, List.map_cons]
    rw [incl_subRefl, ih]

theorem forall_ne_two_smul_iff (γ : J → ℤ) :
    (∀ δ, incl J δ ∈ Φ.roots → γ ≠ 2 • δ) ↔ Φ.IsIndiv (incl J γ) := by
  constructor
  · intro h δ hδ he
    have hδs : ∀ k ∉ J, δ k = 0 := fun k hk => by
      have := congrFun he k
      rw [incl_apply_of_notMem _ hk, Pi.smul_apply, nsmul_eq_mul] at this
      omega
    refine h (proj J δ) (by rwa [incl_proj hδs]) (incl_injective ?_)
    rw [map_nsmul, incl_proj hδs, he]
  · intro h δ hδ he
    exact h _ hδ (by rw [he, map_nsmul])

omit [Fintype ι] in
theorem linIndepPair_incl {γ δ : J → ℤ} (h : LinIndepPair γ δ) :
    LinIndepPair (incl J γ) (incl J δ) := fun a b hab =>
  h a b (incl_injective (by rw [map_add, map_zsmul, map_zsmul, hab, map_zero]))

@[expose] def subsystem (hJ : HasParabolicWords Φ J) : Steinberg.RootSystem J where
  roots := {v | incl J v ∈ Φ.roots}
  finite_roots := Φ.finite_roots.preimage incl_injective.injOn
  zero_notMem := by simpa using Φ.zero_notMem
  neg_mem γ hγ := by simpa using Φ.neg_mem _ hγ
  sign γ hγ := (Φ.sign _ hγ).imp (fun h k => by simpa using h k) (fun h k => by simpa using h k)
  single_mem j := by simpa using Φ.single_mem (j : ι)
  proportional γ hγ δ hδ h := by
    have h' : ¬ LinIndepPair (incl J γ) (incl J δ) := fun hl => h fun a b hab =>
      hl a b (by rw [← map_zsmul, ← map_zsmul, ← map_add, hab, map_zero])
    rcases Φ.proportional _ hγ _ hδ h' with e | e | e | e | e | e
    · exact Or.inl (incl_injective e)
    · exact Or.inr (Or.inl (incl_injective (by rw [e, map_neg])))
    · exact Or.inr (Or.inr (Or.inl (incl_injective (by rw [e, map_nsmul]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (incl_injective (by rw [e, map_neg, map_nsmul])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (incl_injective (by rw [e, map_nsmul]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (incl_injective (by rw [e, map_neg, map_nsmul]))))))
  refl := subRefl Φ J
  refl_apply_of_ne j v k hk := by
    change Φ.refl j (incl J v) k = v k
    rw [Φ.refl_apply_of_ne _ _ _ (fun h => hk (Subtype.ext h)), incl_apply_coe]
  refl_single j := by
    change proj J (Φ.refl j (incl J (Pi.single j 1))) = -Pi.single j 1
    rw [incl_single, Φ.refl_single, map_neg, proj_single]
  refl_refl j v := by
    change proj J (Φ.refl j (incl J (subRefl Φ J j v))) = v
    rw [incl_subRefl, Φ.refl_refl, proj_incl]
  refl_mem j γ hγ := by
    change incl J (subRefl Φ J j γ) ∈ Φ.roots
    rw [incl_subRefl]
    exact Φ.refl_mem _ _ hγ
  exists_word γ hγ hind := by
    obtain ⟨w, i, hw, hi, he⟩ := hJ _ hγ (incl_apply_eq_zero γ) ((forall_ne_two_smul_iff γ).mp hind)
    obtain ⟨w', rfl⟩ := exists_map_val hw
    refine ⟨w', ⟨i, hi⟩, incl_injective ?_⟩
    rw [he, incl_wordAct, incl_single]
  sum_ne_two_smul δ hδ δ' hδ' ε hε hht hhtd hne hi hi' hsum := by
    refine Φ.sum_ne_two_smul _ hδ _ hδ' _ hε (by rwa [ht_incl]) (by rw [ht_incl, ht_incl, hhtd])
      (fun h => hne (incl_injective h)) ((forall_ne_two_smul_iff δ).mp hi)
      ((forall_ne_two_smul_iff δ').mp hi') ?_
    rw [← map_add, hsum, map_nsmul]

variable (hJ : HasParabolicWords Φ J)

@[simp] theorem mem_subsystem_roots {γ : J → ℤ} :
    γ ∈ (subsystem hJ).roots ↔ incl J γ ∈ Φ.roots :=
  Iff.rfl

theorem incl_subsystem_refl (j : J) (v : J → ℤ) :
    incl J ((subsystem hJ).refl j v) = Φ.refl j (incl J v) := incl_subRefl j v

theorem mem_subsystem_pos {γ : J → ℤ} : γ ∈ (subsystem hJ).pos ↔ incl J γ ∈ Φ.pos := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [ht_incl]
  rfl

theorem mem_subsystem_neg {γ : J → ℤ} : γ ∈ (subsystem hJ).neg ↔ incl J γ ∈ Φ.neg := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [ht_incl]
  rfl

theorem subsystem_isIndiv {γ : J → ℤ} : (subsystem hJ).IsIndiv γ ↔ Φ.IsIndiv (incl J γ) :=
  forall_ne_two_smul_iff γ

end Subsystem

open CFSG.LieType.RootSystem in
theorem hasParabolicWords_ofCartan {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) (Dv : Set I) (J : Finset I) :
    HasParabolicWords (Steinberg.RootSystem.ofCartan hA Dv) J := by
  intro γ hγ hsupp hind
  obtain ⟨w, i, rfl⟩ := OfCartan.exists_eq_of_indiv hA hγ hind
  obtain ⟨z, hz, m, hm, hzm⟩ := exists_parabolic_of_support hA (J : Set I) w i hsupp
  obtain ⟨ω, hω, hωz⟩ :=
    (coxeterMatrix hA).toCoxeterSystem.exists_wordProd_eq_of_mem_parabolic (inv_mem hz)
  refine ⟨ω, m, hω, hm, ?_⟩
  have h := OfCartan.weylAction_wordProd hA ω (Pi.single m 1)
  rw [hωz] at h
  change _ = wordAct (fun i => (reflection A i).toAddMonoidHom) ω (Pi.single m 1)
  rw [← h, ← hzm, weylAction_inv_apply_apply]

end CFSG.Timmesfeld.Levi
