module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34ModDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolTrace

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open Equiv

namespace S34

theorem fixW_orth_S5Syl_le_S4pt : fixW orth S5Syl ≤ fixW orth S4pt := by
  intro w hw σ hσ
  have hσ4 : σ 4 = 4 := by simpa [S4pt, MulAction.mem_stabilizer_iff] using hσ
  have key : ∀ (w : orth.W), (∀ b ∈ S5SylF, orth.act b w = w) →
      ∀ σ : Perm (Fin 5), σ 4 = 4 → orth.act σ w = w := by decide +kernel
  exact key w (fun b hb => hw b ((mem_S5Syl_iff b).mpr hb)) σ hσ4

theorem S5Syl_le_S4pt : S5Syl ≤ S4pt := by
  intro σ hσ
  have key : ∀ σ ∈ S5SylF, σ 4 = 4 := by decide +kernel
  simpa [S4pt, MulAction.mem_stabilizer_iff] using key σ ((mem_S5Syl_iff σ).mp hσ)

theorem fixW_S4pt_le (M : Model 5) : fixW M S4pt ≤ fixW M S5Syl :=
  fun _ hw b hb => hw b (S5Syl_le_S4pt hb)

theorem card_S4pt : Nat.card S4pt = 24 := by
  have h : ∀ σ : Perm (Fin 5), σ ∈ S4pt ↔
      σ ∈ (Finset.univ.filter fun σ : Perm (Fin 5) => σ 4 = 4) := by
    intro σ
    simp [S4pt, MulAction.mem_stabilizer_iff]
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_finsetCard]
  decide +kernel

theorem odd_relIndex_S5Syl_S4pt : Odd (S5Syl.relIndex S4pt) := by
  have h1 := Subgroup.relIndex_mul_index S5Syl_le_S4pt
  have h2 := Subgroup.index_mul_card S5Syl
  have h3 := Subgroup.index_mul_card S4pt
  have h120 : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
  rw [card_S5Syl, h120] at h2
  rw [card_S4pt, h120] at h3
  have i1 : S5Syl.index = 15 := by omega
  have i2 : S4pt.index = 5 := by omega
  rw [i1, i2] at h1
  have : S5Syl.relIndex S4pt = 3 := by omega
  rw [this]; decide

theorem fixW_S4pt_eq_of_iso_orth {N : Model 5} (e : N.Iso orth) :
    fixW N S5Syl = fixW N S4pt := by
  refine le_antisymm ?_ (fixW_S4pt_le N)
  have hinj : Function.Injective e.toMulEquiv.toMonoidHom := e.toMulEquiv.injective
  rw [← Subgroup.map_le_map_iff_of_injective hinj, ← e.fixW_eq, ← e.fixW_eq]
  exact fixW_orth_S5Syl_le_S4pt

theorem exists_trace_S4pt (M : Model 5) (U : Subgroup M.W) {v : M.W} (hv : v ∈ fixW M S5Syl)
    (hN : ∀ a ∈ S4pt, M.act a v * v⁻¹ ∈ U) :
    ∃ f ∈ fixW M S4pt, f * v⁻¹ ∈ U := by
  let ρ : ↥S4pt →* MulAut M.W := M.act.comp S4pt.subtype
  let S : Subgroup ↥S4pt := S5Syl.subgroupOf S4pt
  have : Fintype (↥S4pt ⧸ S) := Fintype.ofFinite _
  have hcard : Odd (Fintype.card (↥S4pt ⧸ S)) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact odd_relIndex_S5Syl_S4pt
  have hc : ∀ s ∈ S, ρ s v = v := fun s hs => hv _ hs
  refine ⟨∏ q : ↥S4pt ⧸ S, ρ q.out v, fun b hb => ?_, ?_⟩
  · exact trace_fixed ρ S hc ⟨b, hb⟩
  · have : (∏ q : ↥S4pt ⧸ S, ρ q.out v) * v⁻¹ =
        ∏ q : ↥S4pt ⧸ S, (ρ q.out v * v⁻¹) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        pow_odd_eq_self M.sq hcard]
    rw [this]
    exact Subgroup.prod_mem _ fun q _ => hN _ q.out.2

theorem fixW_S4pt_eq_of_ext {M : Model 5}
    (hext : ∃ (U : Subgroup M.W) (hU : IsInvSub M ⊤ U),
      Nonempty ((M.restrict U hU).Iso orth) ∧ Nonempty ((M.quot U hU).Iso orth)) :
    fixW M S5Syl = fixW M S4pt := by
  obtain ⟨U, hU, ⟨e1⟩, ⟨e2⟩⟩ := hext
  refine le_antisymm ?_ (fixW_S4pt_le M)
  intro v hv
  have hq : M.projQuot U hU v ∈ fixW (M.quot U hU) S5Syl :=
    (M.projQuot_mem_fixW_iff U hU _ v).mpr (fun b hb => by
      show M.act b v * v⁻¹ ∈ U
      rw [hv b hb, mul_inv_cancel]; exact U.one_mem)
  rw [fixW_S4pt_eq_of_iso_orth e2] at hq
  have hq' := (M.projQuot_mem_fixW_iff U hU _ v).mp hq
  obtain ⟨f, hf, hfU⟩ := exists_trace_S4pt M U hv (fun a ha => hq' a ha)
  have hu : v * f⁻¹ ∈ U := by
    have := U.inv_mem hfU
    rwa [mul_inv_rev, inv_inv] at this
  have hfD : f ∈ fixW M S5Syl := fixW_S4pt_le M hf
  have hu8 : M.restrictMk U hU (v * f⁻¹) hu ∈ fixW (M.restrict U hU) S5Syl :=
    (M.restrictMk_mem_fixW U hU _ _ hu).mpr (Subgroup.mul_mem _ hv (Subgroup.inv_mem _ hfD))
  rw [fixW_S4pt_eq_of_iso_orth e1] at hu8
  have hu4 := (M.restrictMk_mem_fixW U hU _ _ hu).mp hu8
  have := Subgroup.mul_mem _ hu4 hf
  simpa using this

theorem index_fixW_orth_That (g : Perm (Fin 5)) :
    (fixW orth (S5That.map (MulAut.conj g).toMonoidHom)).index = 4 := by
  have hc : Nat.card (fixW orth S5That) = 4 := congrArg (fun p => p.2.1) profile_orth.2.2.1
  have h := Subgroup.index_mul_card (fixW orth (S5That.map (MulAut.conj g).toMonoidHom))
  rw [card_fixW_conj, hc, card_orth] at h
  omega

theorem sixteen_le_index_of_ext {M : Model 5}
    (hext : ∃ (U : Subgroup M.W) (hU : IsInvSub M ⊤ U),
      Nonempty ((M.restrict U hU).Iso orth) ∧ Nonempty ((M.quot U hU).Iso orth))
    (g : Perm (Fin 5)) : 16 ≤ (fixW M (S5That.map (MulAut.conj g).toMonoidHom)).index := by
  obtain ⟨U, hU, ⟨e1⟩, ⟨e2⟩⟩ := hext
  set B := S5That.map (MulAut.conj g).toMonoidHom
  have h := bf4_index (M := M) (B := B) (U := U) (fun b _ u hu => hU b (Subgroup.mem_top b) u hu)
  have h1 : (fixW M B).relIndex U = 4 := by
    rw [← index_fixW_orth_That g, e1.index_fixW_eq, fixW_restrict]
    rfl
  have h2 : (fixQ M B U).index = 4 := by
    rw [← index_fixW_quot M U hU B, ← e2.index_fixW_eq B, index_fixW_orth_That g]
  rw [h1, h2] at h
  omega

theorem shapeMod2_of_CEMod {M : Model 5} (_h : CEMod M) (h1 : ShapeMod1 M) : ShapeMod2 M :=
  ⟨fixW_S4pt_eq_of_ext h1.ext, sixteen_le_index_of_ext h1.ext⟩

end S34

end F53.Stellmacher

end CFSG.Quasithin
