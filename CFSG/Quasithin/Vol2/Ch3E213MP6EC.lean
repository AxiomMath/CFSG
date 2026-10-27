module

public import CFSG.Quasithin.Vol2.Ch3E213MP6EB
public import CFSG.Quasithin.Vol2.Ch3E213MP5C
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Enc
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open Equiv CFSG.QuasithinUnique.Borel252.A6

theorem enc_witness : R6.enc (swap 2 3 * swap 4 5) ∈ saL ∧ R6.enc (swap 2 3 * swap 4 5) ∉ sbL := by
  decide +kernel

theorem not_Ka_le_Kb : ¬ Ka ≤ Kb := by
  intro h
  have hev : swap (2 : Fin 6) 3 * swap 4 5 ∈ A6s := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide
  have hmem : (⟨swap 2 3 * swap 4 5, hev⟩ : M6) ∈ Ka := (mem_Sa _).2 enc_witness.1
  exact enc_witness.2 ((mem_Sb _).1 (h hmem))

theorem Ka_covBy : Ka ⋖ ⊤ := by
  refine ⟨Ka_lt_top, fun Y hKY hY => ?_⟩
  rcases only_A6 Y (by rw [normalizer_U6]; exact U6_lt_Ka.trans hKY) hY with h | h
  · exact hKY.ne h.symm
  · exact not_Ka_le_Kb (h ▸ hKY.le)

theorem swap_of_moves (γ : MulAut M6) (hU : U6.map γ.toMonoidHom = U6)
    (hK : Ka.map γ.toMonoidHom ≠ Ka) : Ka.map γ.toMonoidHom = Kb ∧ Kb.map γ.toMonoidHom = Ka := by
  have hover : ∀ X : Subgroup M6, U6 < X → X < ⊤ → X.map γ.toMonoidHom = Ka ∨
      X.map γ.toMonoidHom = Kb := by
    intro X h1 h2
    refine only_A6 _ ?_ ?_
    · rw [normalizer_U6, ← hU]
      exact lt_of_le_of_ne (Subgroup.map_mono h1.le)
        fun h => h1.ne (Subgroup.map_injective γ.injective h)
    · refine lt_top_iff_ne_top.2 fun h => h2.ne ?_
      rw [← P5.map_symm_map γ X, h, ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 γ.symm.surjective
  have ha := (hover Ka U6_lt_Ka Ka_lt_top).resolve_left hK
  refine ⟨ha, (hover Kb U6_lt_Kb Kb_lt_top).resolve_right fun h => ?_⟩
  exact not_Ka_le_Kb (Subgroup.map_injective γ.injective (ha.trans h.symm)).le

theorem map_Ra_le (γ : MulAut M6) (hU : U6.map γ.toMonoidHom = U6)
    (hK : Ka.map γ.toMonoidHom = Kb) : Ra.map γ.toMonoidHom ≤ Rb := by
  rintro _ ⟨r, hr, rfl⟩
  have hrU : γ r ∈ U6 := hU ▸ ⟨r, Ra_le_U6 hr, rfl⟩
  refine core_VB hrU fun g hg => ?_
  set g' : M6 := ⟨g, Sb_le_A6 hg⟩
  have hg' : γ.symm g' ∈ Ka := by
    have hgK : g' ∈ Kb := hg
    rw [← hK] at hgK
    obtain ⟨y, hy, hyg⟩ := hgK
    rw [← hyg]
    simpa using hy
  have h1 : γ.symm g' * r * (γ.symm g')⁻¹ ∈ Ra := by
    rw [← normalizer_Ra] at hg'
    exact (Subgroup.mem_normalizer_iff.1 hg' r).1 hr
  have h2 : γ (γ.symm g' * r * (γ.symm g')⁻¹) ∈ U6 := hU ▸ ⟨_, Ra_le_U6 h1, rfl⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem map_Rb_le (γ : MulAut M6) (hU : U6.map γ.toMonoidHom = U6)
    (hK : Kb.map γ.toMonoidHom = Ka) : Rb.map γ.toMonoidHom ≤ Ra := by
  rintro _ ⟨r, hr, rfl⟩
  have hrU : γ r ∈ U6 := hU ▸ ⟨r, Rb_le_U6 hr, rfl⟩
  refine core_VA hrU fun g hg => ?_
  set g' : M6 := ⟨g, Sa_le_A6 hg⟩
  have hg' : γ.symm g' ∈ Kb := by
    have hgK : g' ∈ Ka := hg
    rw [← hK] at hgK
    obtain ⟨y, hy, hyg⟩ := hgK
    rw [← hyg]
    simpa using hy
  have h1 : γ.symm g' * r * (γ.symm g')⁻¹ ∈ Rb := by
    rw [← normalizer_Rb] at hg'
    exact (Subgroup.mem_normalizer_iff.1 hg' r).1 hr
  have h2 : γ (γ.symm g' * r * (γ.symm g')⁻¹) ∈ U6 := hU ▸ ⟨_, Rb_le_U6 h1, rfl⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
  exact h2

theorem map_Ra_Rb (γ : MulAut M6) (hU : U6.map γ.toMonoidHom = U6)
    (hK : Ka.map γ.toMonoidHom = Kb ∧ Kb.map γ.toMonoidHom = Ka) :
    Ra.map γ.toMonoidHom = Rb ∧ Rb.map γ.toMonoidHom = Ra := by
  have hU' : U6.map γ.symm.toMonoidHom = U6 := by
    conv_lhs => rw [← hU]
    exact P5.map_symm_map γ U6
  have hKa' : Kb.map γ.symm.toMonoidHom = Ka := by rw [← hK.1]; exact P5.map_symm_map γ Ka
  have hKb' : Ka.map γ.symm.toMonoidHom = Kb := by rw [← hK.2]; exact P5.map_symm_map γ Kb
  refine ⟨le_antisymm (map_Ra_le γ hU hK.1) ?_, le_antisymm (map_Rb_le γ hU hK.2) ?_⟩
  · calc Rb = (Rb.map γ.symm.toMonoidHom).map γ.toMonoidHom := (P5.map_map_symm γ Rb).symm
      _ ≤ Ra.map γ.toMonoidHom := Subgroup.map_mono (map_Rb_le γ.symm hU' hKa')
  · calc Ra = (Ra.map γ.symm.toMonoidHom).map γ.toMonoidHom := (P5.map_map_symm γ Ra).symm
      _ ≤ Rb.map γ.toMonoidHom := Subgroup.map_mono (map_Ra_le γ.symm hU' hKb')

theorem le_Ra_inf_Rb (γ : MulAut M6)
    (hab : Ra.map γ.toMonoidHom = Rb ∧ Rb.map γ.toMonoidHom = Ra) {W : Subgroup M6}
    (hWU : W ≤ U6) (h2 : ∀ w ∈ W, w * w = 1) (hW : W.map γ.toMonoidHom = W) :
    W ≤ Ra ⊓ Rb := by
  have hW' : W.map A6s.subtype ≤ D0 := by
    rintro _ ⟨w, hw, rfl⟩
    exact hWU hw
  rcases le_or_le_D0 hW' (by
      rintro _ ⟨w, hw, rfl⟩
      exact congrArg Subtype.val (h2 w hw)) with h | h
  · have hR : W ≤ Ra := fun w hw => h ⟨w, hw, rfl⟩
    refine le_inf hR ?_
    rw [← hW, ← hab.1]
    exact Subgroup.map_mono hR
  · have hR : W ≤ Rb := fun w hw => h ⟨w, hw, rfl⟩
    refine le_inf ?_ hR
    rw [← hW, ← hab.2]
    exact Subgroup.map_mono hR

theorem card_Ra_inf_Rb_le : Nat.card ↥(Ra ⊓ Rb) ≤ 2 := by
  have hzA : zA ∈ A6s := VA_le_A6 zA_mem_VA
  let f : Fin 2 → M6 := ![1, ⟨zA, hzA⟩]
  have hf : ∀ x ∈ Ra ⊓ Rb, ∃ i, f i = x := by
    intro x hx
    rcases mem_inf_VA_VB (x := (x : P6)) hx with h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩
  have hsurj : Function.Surjective
      (fun i : {i : Fin 2 // f i ∈ Ra ⊓ Rb} => (⟨f i, i.2⟩ : ↥(Ra ⊓ Rb))) := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi⟩ := hf x hx
    exact ⟨⟨i, hi ▸ hx⟩, Subtype.ext hi⟩
  calc Nat.card ↥(Ra ⊓ Rb) ≤ Nat.card {i : Fin 2 // f i ∈ Ra ⊓ Rb} :=
        Nat.card_le_card_of_surjective _ hsurj
    _ ≤ Nat.card (Fin 2) := Finite.card_subtype_le _
    _ = 2 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 2)

theorem card_U6 : Nat.card U6 = 8 := by
  rw [U6, card_sub D0_le_A6, card_D0]

end CFSG.Quasithin.Ch3E213M.P6E
