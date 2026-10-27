module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJSpParabolicAut
public import CFSG.Permutation.SupportedAdjacent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative

namespace TypeBDatum

private def tbSh_permAutHom (m p : ℕ) :
    Equiv.Perm (Fin m) →* MulAut (Fin m → Multiplicative (ZMod p)) where
  toFun := permAut
  map_one' := MulEquiv.ext fun f => rfl
  map_mul' _ _ := MulEquiv.ext fun f => rfl

private theorem tbSh_permAut_mem {p m : ℕ} {S : Finset (Fin m)} {π : Equiv.Perm (Fin m)}
    (hπ : ∀ i ∉ S, π i = i) : permAut (p := p) π ∈ permSupportedAut m p S := by
  classical
  have hmem : π ∈ fixingSubgroup (Equiv.Perm (Fin m)) ((S : Set (Fin m))ᶜ) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    exact hπ y (by simpa using hy)
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    have h1 : π = 1 := Equiv.ext fun i => hπ i (Finset.notMem_empty i)
    have h2 : (permAut (p := p) (1 : Equiv.Perm (Fin m))) = 1 := MulEquiv.ext fun f => rfl
    rw [h1, h2]
    exact (permSupportedAut m p ∅).one_mem
  · obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by have := hS.card_pos; omega⟩
    let e : Fin (k + 1) ≃ S := (finCongr hk.symm).trans S.equivFin.symm
    rw [CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_closure_adjacent S e]
      at hmem
    have hle : Subgroup.closure (Set.range fun j : Fin k =>
        Equiv.swap (e j.castSucc : Fin m) (e j.succ : Fin m)) ≤
        (permSupportedAut m p S).comap (tbSh_permAutHom m p) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      refine Subgroup.subset_closure ⟨(e j.castSucc : Fin m), (e j.castSucc).2,
        (e j.succ : Fin m), (e j.succ).2, ?_, rfl⟩
      intro h
      have h' : e j.castSucc = e j.succ := Subtype.ext h
      exact (Fin.castSucc_lt_succ : j.castSucc < j.succ).ne (e.injective h')
    exact hle hmem

private theorem tbSh_perm_le {p m : ℕ} (S : Finset (Fin m)) :
    permSupportedAut m p S ≤ signedSupportedAut m p S := by
  unfold permSupportedAut signedSupportedAut
  exact Subgroup.closure_mono Set.subset_union_right

private theorem tbSh_diag_mem {p m : ℕ} (S₀ : Finset (Fin m)) :
    ∀ (S : Finset (Fin m)), S ⊆ S₀ →
      ∀ (u : MulAut (Fin m → Multiplicative (ZMod p))) (ε : Fin m → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) → (∀ i, i ∉ S → ε i = 1) →
        (∀ f i, toAdd (u f i) = ε i * toAdd (f i)) → u ∈ signedSupportedAut m p S₀ := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ u ε _ hS hu
    have h1 : u = 1 := by
      refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
      rw [hu, hS i (Finset.notMem_empty i), one_mul]
      rfl
    rw [h1]
    exact (signedSupportedAut m p S₀).one_mem
  | insert a S ha ih =>
    intro hsub u ε hε hS hu
    have haS₀ : a ∈ S₀ := hsub (Finset.mem_insert_self a S)
    have hsub' : S ⊆ S₀ := fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rcases hε a with hεa | hεa
    · refine ih hsub' u ε hε (fun i hi => ?_) hu
      by_cases hia : i = a
      · rw [hia, hεa]
      · exact hS i (by simp [hia, hi])
    · have h1 : u * sgnAut a ∈ signedSupportedAut m p S₀ := by
        refine ih hsub' _ (Function.update ε a 1) (fun i => ?_) (fun i hi => ?_) (fun f i => ?_)
        · by_cases hia : i = a
          · subst hia
            simp
          · rw [Function.update_of_ne hia]
            exact hε i
        · by_cases hia : i = a
          · subst hia
            simp
          · rw [Function.update_of_ne hia]
            exact hS i (by simp [hia, hi])
        · rw [MulAut.mul_apply, hu, sgnAut_apply]
          by_cases hia : i = a
          · subst hia
            simp [hεa]
          · rw [Function.update_of_ne hia, Function.update_of_ne hia]
      have hsa : sgnAut a ∈ signedSupportedAut m p S₀ :=
        Subgroup.subset_closure (Or.inl ⟨a, haS₀, rfl⟩)
      have h2 := (signedSupportedAut m p S₀).mul_mem h1
        ((signedSupportedAut m p S₀).inv_mem hsa)
      rwa [mul_inv_cancel_right] at h2

private theorem tbSh_isSignedPerm {p m : ℕ} {σ : MulAut (Fin m → Multiplicative (ZMod p))}
    (hσ : σ ∈ signedAut m p) : IsSignedPerm ⇑σ := by
  unfold signedAut signedSupportedAut at hσ
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hσ
  · rintro x (⟨i, -, rfl⟩ | ⟨a, -, b, -, -, rfl⟩)
    · exact isSignedPerm_sgnAut i
    · exact isSignedPerm_permAut _
  · exact ⟨1, fun _ => 1, fun _ => Or.inl rfl, fun f i => by simp⟩
  · intro x y _ _ hx hy
    exact hx.mul hy
  · intro x _ hx
    exact hx.inv

private theorem tbSh_fix_data {p m : ℕ} (hp : p.Prime) {S : Finset (Fin m)}
    {σ : MulAut (Fin m → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin m)} {ε : Fin m → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (σ f (π i)) = ε i * toAdd (f i))
    (hfix : ∀ i ∉ S, σ (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle i (ofAdd 1)) :
    ∀ i ∉ S, π i = i ∧ ε i = 1 := by
  intro i hi
  have h := IsSignedPerm.apply_mulSingle hu i (1 : ZMod p)
  rw [hfix i hi, mul_one] at h
  have h' := mulSingle_ofAdd_eq_iff (coord_zero_ne_one hp).symm h
  exact ⟨h'.1.symm, h'.2.symm⟩

private theorem tbSh_form {p m : ℕ} {σ : MulAut (Fin m → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin m)} {ε : Fin m → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hu : ∀ f i, toAdd (σ f (π i)) = ε i * toAdd (f i)) :
    σ = permAut π * diagAut ε (fun i => coord_sign_mul_self (hε i)) := by
  apply MulEquiv.ext
  intro f
  apply eq_of_toAdd_perm_eq π
  intro i
  simpa [MulAut.mul_apply, permAut_apply, diagAut_apply] using hu f i

theorem mem_signedSupportedAut_of_fix {p m : ℕ} (hp : p.Prime)
    {σ : MulAut (Fin m → Multiplicative (ZMod p))} (hσ : σ ∈ signedAut m p)
    (S : Finset (Fin m))
    (hfix : ∀ i ∉ S, σ (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle i (ofAdd 1)) :
    σ ∈ signedSupportedAut m p S := by
  classical
  obtain ⟨π, ε, hε, hu⟩ := tbSh_isSignedPerm hσ
  have hdata := tbSh_fix_data hp hε hu hfix
  rw [tbSh_form hε hu]
  refine (signedSupportedAut m p S).mul_mem ?_ ?_
  · exact tbSh_perm_le S (tbSh_permAut_mem (fun i hi => (hdata i hi).1))
  · exact tbSh_diag_mem S S subset_rfl _ ε hε (fun i hi => (hdata i hi).2)
      (fun f i => by rw [diagAut_apply, toAdd_ofAdd])

theorem mem_permSupportedAut_of_fix {p m : ℕ} (hp : p.Prime)
    {σ : MulAut (Fin m → Multiplicative (ZMod p))} (hσ : σ ∈ signedAut m p)
    (S : Finset (Fin m))
    (hfix : ∀ i ∉ S, σ (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle i (ofAdd 1))
    (hdiag : σ (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) =
      fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) :
    σ ∈ permSupportedAut m p S := by
  classical
  obtain ⟨π, ε, hε, hu⟩ := tbSh_isSignedPerm hσ
  have hdata := tbSh_fix_data hp hε hu hfix
  have hπS : ∀ i ∈ S, π i ∈ S := by
    intro i hi
    by_contra hπi
    have h1 : π (π i) = π i := (hdata (π i) hπi).1
    have h2 : π i = i := π.injective h1
    exact hπi (by rw [h2]; exact hi)
  have hε1 : ∀ i, ε i = 1 := by
    intro i
    by_cases hi : i ∈ S
    · have h := hu (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) i
      rw [hdiag] at h
      simp only [hπS i hi, hi, if_true, ↓reduceIte, toAdd_ofAdd, mul_one] at h
      exact h.symm
    · exact (hdata i hi).2
  have hσπ : σ = permAut π := by
    rw [tbSh_form hε hu]
    have h1 : diagAut ε (fun i => coord_sign_mul_self (hε i)) = 1 := by
      refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
      rw [diagAut_apply, toAdd_ofAdd, hε1 i, one_mul]
      rfl
    rw [h1, mul_one]
  rw [hσπ]
  exact tbSh_permAut_mem (fun i hi => (hdata i hi).1)

theorem mem_signedAut_of_isSignedPerm {p m : ℕ}
    {σ : MulAut (Fin m → Multiplicative (ZMod p))} (hσ : IsSignedPerm ⇑σ) :
    σ ∈ signedAut m p := by
  refine mem_of_isSignedPerm (fun i => ?_) (fun a b hab => ?_) hσ
  · unfold signedAut signedSupportedAut
    exact Subgroup.subset_closure (Or.inl ⟨i, Finset.mem_univ i, rfl⟩)
  · unfold signedAut signedSupportedAut
    exact Subgroup.subset_closure (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩)

theorem mem_twistedPermAut_of_fix {p m : ℕ} (hp : p.Prime)
    {σ : MulAut (Fin m → Multiplicative (ZMod p))} (hσ : σ ∈ signedAut m p)
    (S : Finset (Fin m)) (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1)
    (hsgn : ∀ i, s i = 1 ∨ s i = -1)
    (hfix : ∀ i ∉ S, σ (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle i (ofAdd 1))
    (hvec : σ (fun j => if j ∈ S then ofAdd (s j) else 1) =
      fun j => if j ∈ S then ofAdd (s j) else 1) :
    σ ∈ twistedPermAut m p S s hs := by
  classical
  have hD : diagAut s hs ∈ signedAut m p :=
    mem_signedAut_of_isSignedPerm (isSignedPerm_diagAut s hsgn)
  have hconj : ∀ x, σ (diagAut s hs x) = diagAut s hs x →
      (((diagAut s hs)⁻¹ * σ * diagAut s hs : MulAut (Fin m → Multiplicative (ZMod p))) x) =
        x := by
    intro x hx
    rw [MulAut.mul_apply, MulAut.mul_apply, hx, MulAut.inv_apply_self]
  have hw : (diagAut s hs)⁻¹ * σ * diagAut s hs ∈ permSupportedAut m p S := by
    refine mem_permSupportedAut_of_fix hp ((signedAut m p).mul_mem
      ((signedAut m p).mul_mem ((signedAut m p).inv_mem hD) hσ) hD) S (fun i hi => ?_) ?_
    · apply hconj
      have hDi : diagAut s hs (Pi.mulSingle i (ofAdd 1)) = Pi.mulSingle i (ofAdd (s i)) := by
        rw [diagAut_mulSingle, mul_one]
      rw [hDi]
      rcases hsgn i with h | h
      · rw [h]
        exact hfix i hi
      · rw [h, ofAdd_neg, Pi.mulSingle_inv, map_inv, hfix i hi]
    · apply hconj
      have hDv : diagAut s hs (fun j => if j ∈ S then ofAdd (1 : ZMod p) else 1) =
          fun j => if j ∈ S then ofAdd (s j) else 1 := by
        funext j
        rw [diagAut_apply]
        by_cases hj : j ∈ S <;> simp [hj]
      rw [hDv]
      exact hvec
  refine Subgroup.mem_map.mpr ⟨(diagAut s hs)⁻¹ * σ * diagAut s hs, hw, ?_⟩
  change diagAut s hs * ((diagAut s hs)⁻¹ * σ * diagAut s hs) * (diagAut s hs)⁻¹ = σ
  group

theorem signedSupportedAut_le {p m : ℕ} {H : Subgroup (MulAut (Fin m → Multiplicative (ZMod p)))}
    (S : Finset (Fin m)) (hs : ∀ i ∈ S, sgnAut i ∈ H)
    (ht : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → permAut (Equiv.swap a b) ∈ H) :
    signedSupportedAut m p S ≤ H := by
  rw [signedSupportedAut, Subgroup.closure_le]
  rintro _ (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
  · exact hs i hi
  · exact ht a ha b hb hab

theorem twistedPermAut_le {p m : ℕ} {H : Subgroup (MulAut (Fin m → Multiplicative (ZMod p)))}
    (S : Finset (Fin m)) (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1)
    (hgen : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      diagAut s hs * permAut (Equiv.swap a b) * (diagAut s hs)⁻¹ ∈ H) :
    twistedPermAut m p S s hs ≤ H := by
  rw [twistedPermAut, permSupportedAut, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨σ, ⟨a, ha, b, hb, hab, rfl⟩, rfl⟩
  exact hgen a ha b hb hab

end TypeBDatum

end CFSG.StandardType

end
