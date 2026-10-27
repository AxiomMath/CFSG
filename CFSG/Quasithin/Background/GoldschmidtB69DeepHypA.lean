module

public import CFSG.Quasithin.Background.SmithB42HatA6Norm

public section

namespace CFSG.Quasithin.B69.Hyp

open CFSG.Quasithin.HatA6 CFSG.CharacterTheory.SteinbergBY

variable {V : Type} [CommGroup V] {hsq : ∀ v : V, v * v = 1} {z : MulAut V} {u : Fin 3 → V}
  (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)

include hzz in
theorem mem_subOf_span {c : Fin 3 → FieldFour} {w : V} :
    w ∈ subOf hb (FieldFour ∙ c) ↔ ∃ k : FieldFour,
      w = fsmul z k (coordEquiv hb (Multiplicative.ofAdd c)) := by
  rw [mem_subOf]
  constructor
  · intro hw
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.1 hw
    refine ⟨k, ?_⟩
    rw [← coordEquiv_smul hb hzz, hk, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  · rintro ⟨k, rfl⟩
    rw [coordEquiv_symm_fsmul hb hzz, MulEquiv.symm_apply_apply, toAdd_ofAdd]
    exact Submodule.mem_span_singleton.2 ⟨k, rfl⟩

include hzz in
theorem z_mem_subOf (p : Submodule FieldFour (Fin 3 → FieldFour)) {v : V} (hv : v ∈ subOf hb p) :
    z v ∈ subOf hb p := by
  rw [mem_subOf] at hv ⊢
  rw [← fsmul_ω z v, coordEquiv_symm_fsmul hb hzz, toAdd_ofAdd]
  exact p.smul_mem _ hv

include hzz in
theorem zpow_mem_subOf (p : Submodule FieldFour (Fin 3 → FieldFour)) {v : V} (hv : v ∈ subOf hb p)
    (n : ℕ) : (z ^ n) v ∈ subOf hb p := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [pow_succ']
    exact z_mem_subOf hb hzz p ih

theorem subOf_injective : Function.Injective (fun p : Submodule FieldFour (Fin 3 → FieldFour) =>
    (subOf hb p : Subgroup V)) := by
  intro p q h
  ext c
  have h1 := mem_subOf hb (W := p) (v := coordEquiv hb (Multiplicative.ofAdd c))
  have h2 := mem_subOf hb (W := q) (v := coordEquiv hb (Multiplicative.ofAdd c))
  rw [MulEquiv.symm_apply_apply, toAdd_ofAdd] at h1 h2
  have h3 : coordEquiv hb (Multiplicative.ofAdd c) ∈ subOf hb p ↔
      coordEquiv hb (Multiplicative.ofAdd c) ∈ subOf hb q := by
    simp only at h
    rw [h]
  exact h1.symm.trans (h3.trans h2)

theorem subOf_map_linL {L : Subgroup (MulAut V)} (hLz : ∀ x ∈ L, ∀ w, x (z w) = z (x w)) (l : ↥L)
    (p : Submodule FieldFour (Fin 3 → FieldFour)) :
    subOf hb (p.map (linL hb hzz hLz l)) = (subOf hb p).map (l : MulAut V).toMonoidHom := by
  ext w
  rw [mem_subOf, Subgroup.mem_map]
  constructor
  · intro hw
    obtain ⟨c, hc, hcw⟩ := Submodule.mem_map.1 hw
    refine ⟨coordEquiv hb (Multiplicative.ofAdd c), ?_, ?_⟩
    · rw [mem_subOf, MulEquiv.symm_apply_apply, toAdd_ofAdd]
      exact hc
    · show (l : MulAut V) (coordEquiv hb (Multiplicative.ofAdd c)) = w
      rw [← coordEquiv_linL hb hzz hLz, hcw, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    rw [mem_subOf] at hy
    refine Submodule.mem_map.2 ⟨_, hy, ?_⟩
    show linL hb hzz hLz l (Multiplicative.toAdd ((coordEquiv hb).symm y)) = _
    rw [← toAdd_ofAdd (linL hb hzz hLz l _), ← MulEquiv.symm_apply_apply (coordEquiv hb)
      (Multiplicative.ofAdd (linL hb hzz hLz l _)), coordEquiv_linL hb hzz hLz, ofAdd_toAdd,
      MulEquiv.apply_symm_apply]
    rfl

theorem card_span_ff {c : Fin 3 → FieldFour} (hc : c ≠ 0) : Nat.card (FieldFour ∙ c) = 4 := by
  rw [← Nat.card_congr (LinearEquiv.toSpanNonzeroSingleton FieldFour (Fin 3 → FieldFour) c
    hc).toEquiv]
  exact FieldFour.natCard_eq

variable [Finite V] in
include hzz in
theorem map_subOf_eq {x : MulAut V} {n : ℕ} (hxz : ∀ w, x (z w) = (z ^ n) (x w)) {O : Set V}
    (h1O : (1 : V) ∉ O) {c : Fin 3 → FieldFour} (hc : coordEquiv hb (Multiplicative.ofAdd c) ∈ O)
    (hxc : x (coordEquiv hb (Multiplicative.ofAdd c)) ∈ O) :
    (subOf hb (FieldFour ∙ c)).map x.toMonoidHom =
      subOf hb (FieldFour ∙ Multiplicative.toAdd
        ((coordEquiv hb).symm (x (coordEquiv hb (Multiplicative.ofAdd c))))) := by
  set v := coordEquiv hb (Multiplicative.ofAdd c) with hv
  set c' := Multiplicative.toAdd ((coordEquiv hb).symm (x v)) with hc'
  have hv' : coordEquiv hb (Multiplicative.ofAdd c') = x v := by
    rw [hc', ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h1O
    have : v = 1 := by rw [hv]; exact map_one _
    rwa [this] at hc
  have hc'0 : c' ≠ 0 := by
    intro h0
    apply h1O
    rw [h0] at hv'
    have : coordEquiv hb (Multiplicative.ofAdd (0 : Fin 3 → FieldFour)) = 1 := map_one _
    rw [this] at hv'
    rw [hv']
    exact hxc
  have hxv : x v ∈ subOf hb (FieldFour ∙ c') := by
    rw [mem_subOf_span hb hzz]
    exact ⟨1, by rw [hv', fsmul_one]⟩
  have hxzv : x (z v) ∈ subOf hb (FieldFour ∙ c') := by
    rw [hxz]
    exact zpow_mem_subOf hb hzz _ hxv n
  have hle : (subOf hb (FieldFour ∙ c)).map x.toMonoidHom ≤ subOf hb (FieldFour ∙ c') := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, rfl⟩ := (mem_subOf_span hb hzz).1 hw
    show x (fsmul z k v) ∈ _
    unfold fsmul
    rw [map_mul]
    refine Subgroup.mul_mem _ ?_ ?_
    · split_ifs
      · exact hxv
      · rw [map_one]
        exact Subgroup.one_mem _
    · split_ifs
      · exact hxzv
      · rw [map_one]
        exact Subgroup.one_mem _
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective x.injective, card_subOf, card_subOf, card_span_ff hc0,
    card_span_ff hc'0]

end CFSG.Quasithin.B69.Hyp
