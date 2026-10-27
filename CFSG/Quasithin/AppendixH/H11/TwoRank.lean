module

public import CFSG.Quasithin.AppendixH.H11.NativeAction
public import CFSG.Quasithin.AppendixH.H11.AutomorphismGroup
public import CFSG.Quasithin.Background.GoldschmidtM12SylowTData
public import CFSG.Quasithin.Background.GoldschmidtAutM12TData
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem card_le_eight_of_le_of_isElemAbelian2
    (c : NativeCoords L) {B : Subgroup (MulAut V)} (hBL : B ≤ L)
    (hB : IsElemAbelian2 B) : Nat.card B ≤ 8 := by
  have hB' : CFSG.Open.IsElemAbelian 2
      ((B.subgroupOf L).map c.mulEquiv.symm.toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map
      (CFSG.Open.IsElemAbelian.subgroupOf (isElemAbelian2_iff.mp hB) L)
      c.mulEquiv.symm.toMonoidHom
  have hcard : Nat.card B =
      Nat.card ((B.subgroupOf L).map c.mulEquiv.symm.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective c.mulEquiv.symm.injective]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv).symm
  have h8 := CFSG.QuasithinUnique.Setup.X1.m12_rank_le
    ((B.subgroupOf L).map c.mulEquiv.symm.toMonoidHom)
    (fun x hx y hy => CFSG.Open.IsElemAbelian.comm hB' hx hy) (fun x hx => hB'.2 x hx)
  rw [hcard]
  simpa using h8

theorem exists_isElemAbelian2_card_eight (c : NativeCoords L) :
    ∃ B : Subgroup (MulAut V), B ≤ L ∧ IsElemAbelian2 B ∧ Nat.card B = 8 := by
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥CFSG.Blueprint.NativeSporadic.M12))
  obtain ⟨B₀, hB₀e, hB₀c⟩ := (CFSG.Quasithin.F6.M12Sylow.tProps64_sylow Q).hasE8
  let f : ↥(Q : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12) →* MulAut V :=
    L.subtype.comp (c.π.comp (Q : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12).subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    exact (Q : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12).subtype_injective
      (c.injective (L.subtype_injective hxy))
  refine ⟨B₀.map f, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_range f B₀).trans (by
      rintro y ⟨x, rfl⟩
      exact (c.π ((Q : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12).subtype x)).2)
  · exact isElemAbelian2_iff.mpr (CFSG.Open.IsElemAbelian.map hB₀e f)
  · rw [Subgroup.card_map_of_injective hf, hB₀c]

theorem pRank_eq_three [Finite (MulAut V)]
    (c : NativeCoords L) : CFSG.Open.pRank 2 L = 3 := by
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (p := 2) (by norm_num) ?_
    intro E hEL hE
    have h8 := card_le_eight_of_le_of_isElemAbelian2 c hEL (isElemAbelian2_iff.mpr hE)
    simpa only [show (2 : ℕ) ^ 3 = 8 by norm_num] using h8
  · obtain ⟨B, hBL, hBe, hBc⟩ := exists_isElemAbelian2_card_eight c
    exact CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hBL (isElemAbelian2_iff.mp hBe)
      (by rw [hBc]; norm_num)

theorem exists_isElemAbelian2_card_sixteen_of_ne [Finite (MulAut V)]
    (hLM : IsOver L M) (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥)
    (θ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M12) (hne : M ≠ L) :
    ∃ B : Subgroup (MulAut V), B ≤ M ∧ IsElemAbelian2 B ∧ Nat.card B = 16 := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_mulAut_of_ne hLM hC θ hne
  obtain ⟨ψ⟩ := autM12PermModel
  obtain ⟨B₀, hB₀e, hB₀c⟩ := (CFSG.Quasithin.F6.AutM12Recog.tProps_autT).hasE16
  let f : ↥CFSG.Quasithin.M12AmalAut.autData.T →* MulAut V :=
    M.subtype.comp ((φ.symm.toMonoidHom.comp ψ.toMonoidHom).comp
      CFSG.Quasithin.M12AmalAut.autData.T.subtype)
  have hf : Function.Injective f := by
    intro x y hxy
    exact CFSG.Quasithin.M12AmalAut.autData.T.subtype_injective
      (ψ.injective (φ.symm.injective (M.subtype_injective hxy)))
  refine ⟨B₀.map f, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_range f B₀).trans (by
      rintro y ⟨x, rfl⟩
      exact (φ.symm (ψ (CFSG.Quasithin.M12AmalAut.autData.T.subtype x))).2)
  · exact isElemAbelian2_iff.mpr (CFSG.Open.IsElemAbelian.map hB₀e f)
  · rw [Subgroup.card_map_of_injective hf, hB₀c]

theorem pRank_eq_four_of_ne [Finite (MulAut V)]
    (hLM : IsOver L M) (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥)
    (θ : ↥L ≃* ↥CFSG.Blueprint.NativeSporadic.M12) (h : M12Ten L ⊤ ⊥) (hne : M ≠ L) :
    CFSG.Open.pRank 2 M = 4 := by
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (p := 2) (by norm_num) ?_
    intro E hEM hE
    obtain ⟨k, hk⟩ := exists_card_eq_two_pow_of_isElemAbelian (G := MulAut V) hE
    calc Nat.card E = 2 ^ k := hk
      _ ≤ 2 ^ 4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr
        (CFSG.Quasithin.H13.A5.M12.m12_card_le hLM h hEM (isElemAbelian2_iff.mpr hE) hk)
  · obtain ⟨B, hBM, hBe, hBc⟩ := exists_isElemAbelian2_card_sixteen_of_ne hLM hC θ hne
    exact CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hBM (isElemAbelian2_iff.mp hBe)
      (by rw [hBc]; norm_num)

end CFSG.Quasithin.AppendixH.H11
