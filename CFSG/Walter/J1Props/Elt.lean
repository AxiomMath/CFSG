module

public import CFSG.Walter.J1Recog.Inj

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1Recog CFSG.Open Word

abbrev mat (g : walterJ1) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  ((g : GL (Fin 7) (ZMod 11)) : Matrix (Fin 7) (Fin 7) (ZMod 11))

theorem mat_mul (g h : walterJ1) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem mat_pow (g : walterJ1) (k : ℕ) : mat (g ^ k) = mat g ^ k := by
  simp [mat, Units.val_pow_eq_pow_val]

theorem mat_injective : Function.Injective mat := fun _ _ e => Subtype.ext (Units.ext e)

theorem mat_inj {g h : walterJ1} : mat g = mat h ↔ g = h := mat_injective.eq_iff

theorem ev_unit_mem (w : Word 5) : ev unit w ∈ walterJ1 := by
  rw [← toMat_range_eq]
  exact ⟨ev PresentedGroup.of w, toMat_ev w⟩

@[expose] noncomputable def elt (w : Word 5) : walterJ1 := ⟨ev unit w, ev_unit_mem w⟩

theorem coe_elt (w : Word 5) : ((elt w : walterJ1) : GL (Fin 7) (ZMod 11)) = ev unit w := rfl

theorem mat_elt (w : Word 5) : mat (elt w) = matWord w := val_ev_unit w

theorem elt_append (v w : Word 5) : elt (v ++ w) = elt v * elt w :=
  Subtype.ext (ev_append unit v w)

theorem elt_inv (w : Word 5) : elt (Word.inv w) = (elt w)⁻¹ :=
  Subtype.ext (ev_inv unit w)

theorem elt_nil : elt [] = 1 := Subtype.ext (ev_nil unit)

theorem elt_pow (w : Word 5) (j : ℕ) : elt (Word.pow w j) = elt w ^ j :=
  Subtype.ext (by rw [Subgroup.coe_pow]; exact ev_pow unit w j)

theorem elt_conj (x y : Word 5) : elt (Word.conj x y) = (elt y)⁻¹ * elt x * elt y := by
  rw [Word.conj, elt_append, elt_append, elt_inv]

theorem mat_elt_inv (w : Word 5) : mat (elt w)⁻¹ = matWord (Word.inv w) := by
  rw [← elt_inv, mat_elt]

noncomputable abbrev tJ : walterJ1 := elt wt

noncomputable abbrev nJ : walterJ1 := elt wn

noncomputable abbrev mJ : walterJ1 := elt wm

noncomputable abbrev sJ : walterJ1 := elt ws

noncomputable abbrev uJ : walterJ1 := elt wu

theorem mat_tJ : mat tJ = matT := by rw [mat_elt]; decide +kernel

theorem mat_nJ : mat nJ = matN := by rw [mat_elt]; decide +kernel

theorem mat_mJ : mat mJ = matM := by rw [mat_elt]; decide +kernel

theorem mat_sJ : mat sJ = matL := by rw [mat_elt]; decide +kernel

theorem mat_uJ : mat uJ = matU := by rw [mat_elt]; decide +kernel

theorem mat_nJ_inv : mat nJ⁻¹ = matNi := by rw [mat_elt_inv]; decide +kernel

theorem mat_mJ_inv : mat mJ⁻¹ = matMi := by rw [mat_elt_inv]; decide +kernel

theorem tJ_inv : tJ⁻¹ = tJ := by
  rw [← mat_inj, mat_elt_inv, mat_tJ]
  decide +kernel

theorem sJ_inv : sJ⁻¹ = sJ := by
  rw [← mat_inj, mat_elt_inv, mat_sJ]
  decide +kernel

theorem uJ_inv : uJ⁻¹ = uJ := by
  rw [← mat_inj, mat_elt_inv, mat_uJ]
  decide +kernel

theorem card_walterJ1 : Nat.card walterJ1 = 175560 := by
  rw [← Nat.card_congr presEquiv.toEquiv, card_pres]

instance : Finite walterJ1 := Nat.finite_of_card_ne_zero (by rw [card_walterJ1]; norm_num)

theorem walterJ1_perfect : commutator walterJ1 = ⊤ := by
  have h := map_commutator_eq (Pres .O1a) presEquiv.toMonoidHom
  rw [pres_perfect, MonoidHom.range_eq_top.mpr presEquiv.surjective] at h
  rw [commutator_def, ← h, Subgroup.map_top_of_surjective _ presEquiv.surjective]

theorem index_ne_of_perfect {X : Type*} [Group X] (hX : commutator X = ⊤) (H : Subgroup X)
    [hH : H.Normal] {p : ℕ} (hp : p.Prime) : H.index ≠ p := by
  intro hidx
  have : Fact p.Prime := ⟨hp⟩
  have hcyc : IsCyclic (X ⧸ H) := isCyclic_of_prime_card (p := p) (by
    rw [← Subgroup.index_eq_card, hidx])
  have hle : commutator X ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_commute]
    exact mul_comm' _ _
  rw [hX, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hidx
  exact hp.one_lt.ne hidx

theorem walterJ1_index_ne_two (H : Subgroup walterJ1) : H.index ≠ 2 := by
  intro h2
  have : H.Normal := Subgroup.normal_of_index_eq_two h2
  exact index_ne_of_perfect walterJ1_perfect H Nat.prime_two h2

end CFSG.Walter.J1Props
