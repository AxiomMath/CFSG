module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def
public import CFSG.Quasithin.EmptyFaithful.SzN28PTwGrp

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace SzN28P

section Fin5

theorem tw12_exists_perm_three :
    ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 → w ≠ 0 →
      ∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ permAct σ w = w := by
  decide +kernel

theorem tw12_exists_three_fixing (w : ↥(permCore 5)) (hw : w ≠ 0) :
    ∃ σ : ↥(alternatingGroup (Fin 5)), σ ≠ 1 ∧ σ ^ 3 = 1 ∧
      permAct (σ : Equiv.Perm (Fin 5)) (w : Fin 5 → ZMod 2) = (w : Fin 5 → ZMod 2) := by
  have hsum : ∑ i, (w : Fin 5 → ZMod 2) i = 0 := w.2
  have hw0 : (w : Fin 5 → ZMod 2) ≠ 0 := fun h => hw (Subtype.ext h)
  obtain ⟨σ, h3, h1, hfix⟩ := tw12_exists_perm_three _ hsum hw0
  have hsign : Equiv.Perm.sign σ = 1 := by
    have h := congrArg (fun τ => Equiv.Perm.sign τ) h3
    simp only [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h'
    · exact h'
    · rw [h'] at h
      exact absurd h (by decide)
  refine ⟨⟨σ, (Equiv.Perm.mem_alternatingGroup).mpr hsign⟩, ?_, ?_, hfix⟩
  · intro h
    exact h1 (congrArg Subtype.val h)
  · exact Subtype.ext h3

end Fin5

section Lin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

variable {L L₁ L₂ : Subgroup (V ≃ₗ[ZMod 2] V)}

theorem tw12_sub_mem_commSpanOf {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ L) (v : V) :
    γ v - v ∈ commSpanOf L :=
  Submodule.subset_span ⟨γ, hγ, v, rfl⟩

theorem tw12_apply_mem_commSpanOf {γ : V ≃ₗ[ZMod 2] V} (hγ : γ ∈ L) {u : V}
    (hu : u ∈ commSpanOf L) : γ u ∈ commSpanOf L := by
  have := Submodule.add_mem _ (tw12_sub_mem_commSpanOf hγ u) hu
  simpa using this

theorem tw12_apply_eq_of_mem_commSpanOf (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hdisj : Disjoint (commSpanOf L₁) (commSpanOf L₂)) {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ L₁)
    {w : V} (hw : w ∈ commSpanOf L₂) : a w = w := by
  have hle : commSpanOf L₂ ≤ LinearMap.ker (a.toLinearMap - LinearMap.id) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, v, rfl⟩
    have h1 : a (b v - v) - (b v - v) ∈ commSpanOf L₁ := tw12_sub_mem_commSpanOf ha _
    have h2 : a (b v - v) - (b v - v) ∈ commSpanOf L₂ := by
      have hab : a (b v) = b (a v) := by
        have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) (hcomm a ha b hb)
        simpa using this
      have : a (b v - v) - (b v - v) = (b (a v) - a v) - (b v - v) := by
        rw [map_sub, hab]
      rw [this]
      exact Submodule.sub_mem _ (tw12_sub_mem_commSpanOf hb _) (tw12_sub_mem_commSpanOf hb _)
    have h0 := (Submodule.disjoint_def.mp hdisj) _ h1 h2
    simpa [sub_eq_zero] using h0
  have := hle hw
  simpa [sub_eq_zero] using this

theorem tw12_conj_apply (x γ : V ≃ₗ[ZMod 2] V) :
    ((MulAut.conj x).toMonoidHom γ) = x * γ * x⁻¹ := rfl

theorem tw12_conj_apply_mem {x : V ≃ₗ[ZMod 2] V} (hx2 : x * x = 1) {w : V}
    (hw : w ∈ commSpanOf (L.map (MulAut.conj x).toMonoidHom)) : x w ∈ commSpanOf L := by
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hle : commSpanOf (L.map (MulAut.conj x).toMonoidHom) ≤
      (commSpanOf L).comap (x : V →ₗ[ZMod 2] V) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, ⟨γ, hγ, rfl⟩, v, rfl⟩
    have h : x (((MulAut.conj x).toMonoidHom γ) v - v) = γ (x v) - x v := by
      have h1 : (x * γ * x) v = x (γ (x v)) := rfl
      have h2 : x (x (γ (x v))) = γ (x v) := by
        have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (γ (x v))) hx2
        simpa using this
      rw [tw12_conj_apply, hinv, map_sub, h1, h2]
    show x (((MulAut.conj x).toMonoidHom γ) v - v) ∈ commSpanOf L
    rw [h]
    exact tw12_sub_mem_commSpanOf hγ _
  exact hle hw

theorem tw12_exists_decomp {x : V ≃ₗ[ZMod 2] V} (hx2 : x * x = 1) {v₁ : V} (hv₁ : v₁ ≠ 0)
    (hxv : x v₁ = v₁)
    (hc : IsCompl (commSpanOf L) (commSpanOf (L.map (MulAut.conj x).toMonoidHom))) :
    ∃ u ∈ commSpanOf L, ∃ u' ∈ commSpanOf (L.map (MulAut.conj x).toMonoidHom),
      u + u' = v₁ ∧ u ≠ 0 := by
  have hv : v₁ ∈ commSpanOf L ⊔ commSpanOf (L.map (MulAut.conj x).toMonoidHom) := by
    rw [hc.sup_eq_top]
    trivial
  obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.mp hv
  refine ⟨u, hu, u', hu', hsum, ?_⟩
  rintro rfl
  rw [zero_add] at hsum
  subst hsum
  have h1 : x u' ∈ commSpanOf L := tw12_conj_apply_mem hx2 hu'
  rw [hxv] at h1
  exact hv₁ ((Submodule.disjoint_def.mp hc.disjoint) _ h1 hu')

theorem tw12_exists_three_of_mem
    (hφψ : ∃ (φ : ↥L ≃* ↥(alternatingGroup (Fin 5))) (ψ : ↥(commSpanOf L) ≃ₗ[ZMod 2] ↥(permCore 5)),
      ∀ (γ : ↥L) (v w : ↥(commSpanOf L)), (w : V) = (γ : V ≃ₗ[ZMod 2] V) (v : V) →
        (ψ w : Fin 5 → ZMod 2) = permAct ((φ γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          (ψ v))
    {u : V} (hu : u ∈ commSpanOf L) (hu0 : u ≠ 0) :
    ∃ t ∈ L, t ≠ 1 ∧ t ^ 3 = 1 ∧ t u = u := by
  obtain ⟨φ, ψ, hψ⟩ := hφψ
  set v : ↥(commSpanOf L) := ⟨u, hu⟩ with hv
  have hv0 : v ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hw0 : ψ v ≠ 0 := fun h => hv0 (by simpa using h)
  obtain ⟨σ, hσ1, hσ3, hσfix⟩ := tw12_exists_three_fixing (ψ v) hw0
  refine ⟨((φ.symm σ : ↥L) : V ≃ₗ[ZMod 2] V), (φ.symm σ).2, ?_, ?_, ?_⟩
  · intro h
    apply hσ1
    have h' : φ.symm σ = 1 := Subtype.ext h
    simpa using congrArg φ h'
  · have : (φ.symm σ) ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
    exact congrArg Subtype.val this
  · set t := φ.symm σ with ht
    have hmem : (t : V ≃ₗ[ZMod 2] V) u ∈ commSpanOf L := tw12_apply_mem_commSpanOf t.2 hu
    have h1 := hψ t v ⟨(t : V ≃ₗ[ZMod 2] V) u, hmem⟩ rfl
    rw [show φ t = σ from φ.apply_symm_apply σ] at h1
    have h2 : ψ ⟨(t : V ≃ₗ[ZMod 2] V) u, hmem⟩ = ψ v := Subtype.ext (h1.trans hσfix)
    exact congrArg Subtype.val (ψ.injective h2)

theorem tw12_exists_E {x : V ≃ₗ[ZMod 2] V} (hx2 : x * x = 1)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj x).toMonoidHom, a * b = b * a)
    (hdisj : L ⊓ L.map (MulAut.conj x).toMonoidHom = ⊥)
    (hc : IsCompl (commSpanOf L) (commSpanOf (L.map (MulAut.conj x).toMonoidHom)))
    (hφψ : ∃ (φ : ↥L ≃* ↥(alternatingGroup (Fin 5))) (ψ : ↥(commSpanOf L) ≃ₗ[ZMod 2] ↥(permCore 5)),
      ∀ (γ : ↥L) (v w : ↥(commSpanOf L)), (w : V) = (γ : V ≃ₗ[ZMod 2] V) (v : V) →
        (ψ w : Fin 5 → ZMod 2) = permAct ((φ γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
          (ψ v))
    {v₁ : V} (hv₁ : v₁ ≠ 0) (hxv : x v₁ = v₁) :
    ∃ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ L ⊔ L.map (MulAut.conj x).toMonoidHom ∧
      Nat.card E = 9 ∧ (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) ∧ (∀ e ∈ E, e ^ 3 = 1) ∧
      ∀ e ∈ E, e v₁ = v₁ := by
  obtain ⟨u, hu, u', hu', hsum, hu0⟩ := tw12_exists_decomp hx2 hv₁ hxv hc
  obtain ⟨t, htL, ht1, ht3, htu⟩ := tw12_exists_three_of_mem hφψ hu hu0
  have htu' : t u' = u' := tw12_apply_eq_of_mem_commSpanOf hcomm hc.disjoint htL hu'
  have htv : t v₁ = v₁ := by rw [← hsum, map_add, htu, htu']
  have hinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  set s : V ≃ₗ[ZMod 2] V := x * t * x⁻¹ with hs_def
  have hsL' : s ∈ L.map (MulAut.conj x).toMonoidHom := ⟨t, htL, rfl⟩
  have hs3 : s ^ 3 = 1 := by
    rw [hs_def, ← tw12_conj_apply, ← map_pow, ht3, map_one]
  have hs1 : s ≠ 1 := by
    intro h
    apply ht1
    have : (MulAut.conj x) t = 1 := h
    simpa using this
  have hts : Commute t s := hcomm t htL s hsL'
  have hsv : s v₁ = v₁ := by
    have h1 : s v₁ = x (t (x⁻¹ v₁)) := rfl
    rw [h1, hinv, hxv, htv, hxv]
  have hd : Disjoint (Subgroup.zpowers t) (Subgroup.zpowers s) :=
    Disjoint.mono (Subgroup.zpowers_le.mpr htL) (Subgroup.zpowers_le.mpr hsL')
      (disjoint_iff.mpr hdisj)
  have hstab : Subgroup.zpowers t ⊔ Subgroup.zpowers s ≤
      MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁ :=
    sup_le (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr htv))
      (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hsv))
  refine ⟨Subgroup.zpowers t ⊔ Subgroup.zpowers s,
    sup_le_sup (Subgroup.zpowers_le.mpr htL) (Subgroup.zpowers_le.mpr hsL'),
    tw12_card_sup ht3 ht1 hs3 hs1 hts hd, fun e he f hf => tw12_sup_comm hts he hf,
    fun e he => tw12_sup_pow ht3 hs3 hts he, fun e he => ?_⟩
  exact MulAction.mem_stabilizer_iff.mp (hstab he)

end Lin

end SzN28P

end CFSG.Quasithin
