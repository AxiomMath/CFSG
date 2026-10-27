module

public import CFSG.Quasithin.Recognition.SzVBOdd

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G]

theorem conjSub_conjClosure (g : G) (V P : Subgroup G) :
    conjSub g (conjClosure V P) = conjClosure (conjSub g V) (conjSub g P) := by
  unfold conjClosure
  rw [conjSub_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨h, hh, v, hv, rfl⟩, rfl⟩
    exact ⟨g * h * g⁻¹, mul_mem_conjSub hh, g * v * g⁻¹, mul_mem_conjSub hv, by group⟩
  · rintro ⟨h, hh, v, hv, rfl⟩
    rw [mem_conjSub] at hh hv
    exact ⟨_, ⟨g⁻¹ * h * g, hh, g⁻¹ * v * g, hv, rfl⟩, by group⟩

theorem KleinData.conj {P V : Subgroup G} {z : G} (h : KleinData P V z) (g : G) :
    KleinData (conjSub g P) (conjSub g V) (g * z * g⁻¹) where
  V_le := conjSub_mono g h.V_le
  elemAbelian := F7.isElemAbelian_conjSub h.elemAbelian
  card_eq := by
    rw [← h.card_eq]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
  z_mem := mul_mem_conjSub h.z_mem
  z_ne_one hz := h.z_ne_one (conj_eq_one_iff.mp hz)
  z_cent x hx := by
    have hx' := h.z_cent _ (mem_conjSub.mp hx)
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx']
      _ = g * z * g⁻¹ * x := by group

@[expose] def conjSubIso (g : G) (P : Subgroup G) : ↥P ≃* ↥(conjSub g P) where
  toFun x := ⟨g * (x : G) * g⁻¹, mul_mem_conjSub x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g, mem_conjSub.mp x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_conjSubIso (g : G) (P : Subgroup G) (x : ↥P) :
    ((conjSubIso g P x : ↥(conjSub g P)) : G) = g * (x : G) * g⁻¹ := rfl

theorem coe_conjSubIso_symm (g : G) (P : Subgroup G) (x : ↥(conjSub g P)) :
    (((conjSubIso g P).symm x : ↥P) : G) = g⁻¹ * (x : G) * g := rfl

namespace ConjSet

@[expose] def conj (g : G) (P V : Subgroup G) :
    ConjSet P V ≃ ConjSet (conjSub g P) (conjSub g V) where
  toFun U := ⟨conjSub g U.1, by
    obtain ⟨x, hx, hU⟩ := U.2
    refine ⟨g * x * g⁻¹, mul_mem_conjSub hx, ?_⟩
    rw [hU, ← conjSub_mul g x V, ← conjSub_mul (g * x * g⁻¹) g V, inv_mul_cancel_right]⟩
  invFun U := ⟨conjSub g⁻¹ U.1, by
    obtain ⟨x, hx, hU⟩ := U.2
    refine ⟨g⁻¹ * x * g, mem_conjSub.mp hx, ?_⟩
    rw [hU, ← conjSub_mul g⁻¹ x (conjSub g V), ← conjSub_mul (g⁻¹ * x) g V]⟩
  left_inv U := Subtype.ext (conjSub_conjSub_inv g U.1)
  right_inv U := Subtype.ext (conjSub_inv_conjSub g U.1)

theorem conj_base (g : G) (P V : Subgroup G) :
    conj g P V (base P V) = base (conjSub g P) (conjSub g V) := rfl

theorem conj_smul (g : G) (P V : Subgroup G) (x : ↥P) (U : ConjSet P V) :
    conj g P V (x • U) = conjSubIso g P x • conj g P V U := by
  apply Subtype.ext
  show conjSub g (conjSub (x : G) U.1) = conjSub (g * (x : G) * g⁻¹) (conjSub g U.1)
  rw [← conjSub_mul g (x : G) U.1, ← conjSub_mul (g * (x : G) * g⁻¹) g U.1,
    inv_mul_cancel_right]

end ConjSet

theorem conjSubIso_mem_kerAct_iff (g : G) (P V : Subgroup G) (x : ↥P) :
    conjSubIso g P x ∈ kerAct (conjSub g P) (conjSub g V) ↔ x ∈ kerAct P V := by
  rw [OddAux.mem_kerAct, OddAux.mem_kerAct]
  constructor
  · intro hx U
    apply (ConjSet.conj g P V).injective
    rw [ConjSet.conj_smul]
    exact hx _
  · intro hx U'
    obtain ⟨U, rfl⟩ := (ConjSet.conj g P V).surjective U'
    rw [← ConjSet.conj_smul, hx U]

theorem kerAct_eq_comap_conjSubIso (g : G) (P V : Subgroup G) :
    kerAct P V = (kerAct (conjSub g P) (conjSub g V)).comap (conjSubIso g P).toMonoidHom := by
  ext x
  exact (conjSubIso_mem_kerAct_iff g P V x).symm

theorem BenderLocalFacts.conj {P S V : Subgroup G} (h : BenderLocalFacts P S V) (g : G) :
    BenderLocalFacts (conjSub g P) (conjSub g S) (conjSub g V) := by
  obtain ⟨e, he, hbase⟩ : ∃ e : ConjSet P V ≃ ConjSet (conjSub g P) (conjSub g V),
      (∀ (x : ↥P) (U : ConjSet P V), e (x • U) = conjSubIso g P x • e U) ∧
      e (ConjSet.base P V) = ConjSet.base (conjSub g P) (conjSub g V) :=
    ⟨ConjSet.conj g P V, ConjSet.conj_smul g P V, ConjSet.conj_base g P V⟩
  refine
    { card_odd := ?_
      five_le := ?_
      S_le := conjSub_mono g h.S_le
      S_pGroup := F7.isPGroup_conjSub h.S_pGroup
      S_le_normalizer := conjSub_le_normalizer h.S_le_normalizer
      ker_inv_le := ?_
      S_transitive := ?_
      orbit_le_four := ?_
      four_cycles := ?_ }
  · rw [← Nat.card_congr e]
    exact h.card_odd
  · rw [← Nat.card_congr e]
    exact h.five_le
  · intro x' hsq hker
    have hsq' : (conjSubIso g P).symm x' * (conjSubIso g P).symm x' = 1 := by
      rw [← map_mul, hsq, map_one]
    have hker' : (conjSubIso g P).symm x' ∈ kerAct P V := by
      refine (conjSubIso_mem_kerAct_iff g P V _).mp ?_
      rwa [MulEquiv.apply_symm_apply]
    have hcore := h.ker_inv_le _ hsq' hker'
    have hcoe : (x' : G) = g * (((conjSubIso g P).symm x' : ↥P) : G) * g⁻¹ := by
      rw [coe_conjSubIso_symm]
      group
    rw [pCoreOf_conjSub, hcoe]
    exact mul_mem_conjSub hcore
  · intro U₁' U₂' h₁ h₂
    obtain ⟨U₁, rfl⟩ := e.surjective U₁'
    obtain ⟨U₂, rfl⟩ := e.surjective U₂'
    obtain ⟨s, hsS, hs⟩ := h.S_transitive U₁ U₂ (fun hh => h₁ (by rw [hh, hbase]))
      (fun hh => h₂ (by rw [hh, hbase]))
    refine ⟨conjSubIso g P s, ?_, ?_⟩
    · rw [coe_conjSubIso]
      exact mul_mem_conjSub hsS
    · rw [← he, hs]
  · intro E' hE'
    have hE : ∀ x ∈ E'.comap (conjSubIso g P).toMonoidHom,
        ∀ x' ∈ E'.comap (conjSubIso g P).toMonoidHom, ∀ U : ConjSet P V,
        x • U = U ∨ x' • U = U ∨ x • U = x' • U := by
      intro x hx x' hx' U
      have key := hE' (conjSubIso g P x) (Subgroup.mem_comap.mp hx)
        (conjSubIso g P x') (Subgroup.mem_comap.mp hx') (e U)
      simp only [← he] at key
      simpa only [e.injective.eq_iff] using key
    have h4 := h.orbit_le_four _ hE
    rw [kerAct_eq_comap_conjSubIso g P V, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (f := (conjSubIso g P).toMonoidHom)
        (conjSubIso g P).surjective] at h4
    exact h4
  · intro y' hsq hker
    have hsq' : (conjSubIso g P).symm y' * (conjSubIso g P).symm y' = 1 := by
      rw [← map_mul, hsq, map_one]
    have hker' : (conjSubIso g P).symm y' ∉ kerAct P V := fun hmem => hker (by
      have := (conjSubIso_mem_kerAct_iff g P V _).mpr hmem
      rwa [MulEquiv.apply_symm_apply] at this)
    obtain ⟨R, hR4, hR⟩ := h.four_cycles _ hsq' hker'
    have hc : conjSubIso g P ((conjSubIso g P).symm y') = y' :=
      (conjSubIso g P).apply_symm_apply y'
    refine ⟨R.map e.toEmbedding, ?_, ?_⟩
    · rw [Finset.card_map]
      exact hR4
    · intro U' hU'
      rw [Finset.mem_map_equiv] at hU'
      obtain ⟨hne, hnot⟩ := hR (e.symm U') hU'
      have key : y' • U' = e ((conjSubIso g P).symm y' • e.symm U') := by
        rw [he, hc, Equiv.apply_symm_apply]
      refine ⟨fun hh => hne ?_, ?_⟩
      · apply e.injective
        rw [← key, hh, Equiv.apply_symm_apply]
      · rw [Finset.mem_map_equiv, key, Equiv.symm_apply_apply]
        exact hnot

end CFSG.Quasithin.SzVB
