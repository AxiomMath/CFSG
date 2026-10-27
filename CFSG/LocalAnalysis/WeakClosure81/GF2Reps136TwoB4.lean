module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136TwoB3
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136McLaughlinOrder
import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocSimple
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15412Module
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SevenSq

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_stableUnder_commSub_top (H : Subgroup (MulAut W)) :
    StableUnder H (commSub ⊤ H) := by
  intro x hx c hc
  rw [commSub] at hc ⊢
  induction hc using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨y, hy, u, -, rfl⟩ := hz
      refine Subgroup.subset_closure
        ⟨x * y * x⁻¹, H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx), x u, trivial, ?_⟩
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, ← map_inv, map_mul]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact (commSub ⊤ H).mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact (commSub ⊤ H).inv_mem ha

theorem swap_l3 (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {g : MulAut W} (S : Swap136 Y t L g)
    (hW : Wd (Lc L g) = Wd L) (hC : Cd L = ⊥) (hC' : Cd (Lc L g) = ⊥) (hS : Strong3 L (Lc L g))
    (hT : SwapT Y L g) :
    IsL3 ↥L 1 ∧ IsL3 ↥(Lc L g) 1 ∧ Nat.card ↥(Wd L) = 2 ^ 9 ∧
      ∀ a ∈ L ⊔ Lc L g, (∀ u ∈ Wd L, a u = u) → a = 1 := by
  let L' : Subgroup (MulAut W) := L ⊔ Lc L g
  have hL'_eq : commSub ⊤ L' = Wd L := by
    change commSub ⊤ (L ⊔ Lc L g) = Wd L
    rw [CFSG.Quasithin.EmptyFaithfulMultiple.L15412.commSub_sup_eq]
    rw [show commSub ⊤ (Lc L g) = Wd L from hW]
    exact sup_idem _
  have hL'_stab : StableUnder L' (Wd L) := by
    rw [← hL'_eq]
    exact w1369_stableUnder_commSub_top L'
  have hfaith : ∀ a ∈ L ⊔ Lc L g, (∀ u ∈ Wd L, a u = u) → a = 1 := by
    intro a ha hfix
    have hfix_conj : ∀ y ∈ Y, ∀ v ∈ (Wd L).map y.toMonoidHom, a v = v := by
      intro y hy v hv
      rcases Subgroup.mem_map.mp hv with ⟨u, hu, rfl⟩
      by_cases hN : y ∈ Subgroup.normalizer (L' : Set (MulAut W))
      · have hN_inv : y⁻¹ ∈ Subgroup.normalizer (L' : Set (MulAut W)) :=
          (Subgroup.normalizer (L' : Set (MulAut W))).inv_mem hN
        have h_inv_mem : y⁻¹ * a * y ∈ L' := by
          have h' := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hN_inv
          have ha_conj : (MulAut.conj y⁻¹).toMonoidHom a ∈ L' := by
            rw [← h']
            exact Subgroup.mem_map_of_mem _ ha
          simpa [MulAut.conj_apply] using ha_conj
        have hy_fix : ∀ w ∈ Wd L, (y⁻¹ * a * y) w = w := by
          intro w hw
          have hN_y : y ∈ Subgroup.normalizer (L' : Set (MulAut W)) := hN
          have h' := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hN_y
          have h_eq : (Wd L).map y.toMonoidHom = Wd L := by
            rw [← hL'_eq, ← w1369_commSub_top_map_conj L' y]
            simpa using congrArg (commSub ⊤) h'
          have hyw : y w ∈ Wd L := by
            rw [← h_eq]
            exact Subgroup.mem_map_of_mem _ hw
          have h1 : a (y w) = y w := hfix (y w) hyw
          calc (y⁻¹ * a * y) w = y⁻¹ (a (y w)) := by rfl
            _ = y⁻¹ (y w) := by rw [h1]
            _ = w := by simp
        calc a (y u) = y (y⁻¹ (a (y u))) := by simp
          _ = y ((y⁻¹ * a * y) u) := by rfl
          _ = y u := by rw [hy_fix u hu]
      · have hN_inv : y⁻¹ ∉ Subgroup.normalizer (L' : Set (MulAut W)) := by
          intro h
          exact hN ((Subgroup.normalizer (L' : Set (MulAut W))).inv_mem h)
        have hcomm := (hT y⁻¹ (Y.inv_mem hy) hN_inv).2
        have h_inv_mem : y⁻¹ * a * y ∈ L'.map (MulAut.conj y⁻¹).toMonoidHom := by
          have ha_conj : (MulAut.conj y⁻¹).toMonoidHom a ∈
              L'.map (MulAut.conj y⁻¹).toMonoidHom :=
            Subgroup.mem_map_of_mem _ ha
          simpa [MulAut.conj_apply] using ha_conj
        have hbot : commSub (Wd L) (L'.map (MulAut.conj y⁻¹).toMonoidHom) = ⊥ := by
          rw [← hL'_eq]
          exact hcomm
        have hy_fix : ∀ w ∈ Wd L, (y⁻¹ * a * y) w = w := by
          intro w hw
          have h2 : (y⁻¹ * a * y) w * w⁻¹ ∈
              commSub (Wd L) (L'.map (MulAut.conj y⁻¹).toMonoidHom) :=
            Subgroup.subset_closure ⟨y⁻¹ * a * y, h_inv_mem, w, hw, rfl⟩
          rw [hbot, Subgroup.mem_bot] at h2
          calc (y⁻¹ * a * y) w = ((y⁻¹ * a * y) w * w⁻¹) * w := by group
            _ = 1 * w := by rw [h2]
            _ = w := by simp
        calc a (y u) = y (y⁻¹ (a (y u))) := by simp
          _ = y ((y⁻¹ * a * y) u) := by rfl
          _ = y u := by rw [hy_fix u hu]
    have hspan : (⨆ X ∈ conjSubs Y (Wd L), X) = ⊤ :=
      lemmaS S.ctx.comp.1 (comm_top_of_component S.ctx.std hw2 S.ctx.comp)
    let Fixa : Subgroup W :=
      { carrier := { w | a w = w },
        one_mem' := map_one a,
        mul_mem' := by
          intro x y hx hy
          show a (x * y) = x * y
          rw [map_mul, hx, hy],
        inv_mem' := by
          intro x hx
          show a x⁻¹ = x⁻¹
          rw [map_inv, hx] }
    have hX_le : ∀ X ∈ conjSubs Y (Wd L), X ≤ Fixa := by
      intro X hX
      rcases hX with ⟨y, hy, rfl⟩
      intro v hv
      exact hfix_conj y hy v hv
    have htop_le : (⊤ : Subgroup W) ≤ Fixa := by
      rw [← hspan]
      exact iSup₂_le hX_le
    ext w
    exact htop_le (Subgroup.mem_top w)
  have hfaith_Lc : FaithOn (Lc L g) (Wd L) ⊥ := by
    intro a ha hfix
    apply hfaith a
    · exact Subgroup.mem_sup_right ha
    · intro u hu
      have h := hfix u hu
      rw [Subgroup.mem_bot] at h
      calc a u = (a u * u⁻¹) * u := by group
        _ = 1 * u := by rw [h]
        _ = u := by simp
  have hsec_card : Nat.card (secSub (Wd L) ⊥ (Lc L g)) = 168 := by
    have h := hS.1.2.2.2.2
    rw [hC] at h
    exact h
  have hstab : StabPair (Lc L g) (Wd L) ⊥ := by
    intro a ha
    constructor
    · exact hL'_stab a (Subgroup.mem_sup_right ha)
    · intro z hz
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one]
  have hcard_X : Nat.card ↥(Lc L g) = 168 := by
    obtain ⟨e⟩ := mulEquiv_secSub hstab hfaith_Lc
    rw [Nat.card_congr e.toEquiv, hsec_card]
  have hperf_X : commutator ↥(Lc L g) = ⊤ := by
    have h := (swap_comp S).2.2.2.1
    have h1 : (commutator ↥(Lc L g)).map (Lc L g).subtype = ⁅Lc L g, Lc L g⁆ := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [h] at h1
    apply Subgroup.map_injective (f := (Lc L g).subtype) (Lc L g).subtype_injective
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  have hnt_X : Nontrivial ↥(Lc L g) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard_X]
    norm_num
  have hd_X : Nat.card ↥(Lc L g) ∣ 168 := by
    rw [hcard_X]
  have hsimple_X : IsSimpleGroup ↥(Lc L g) :=
    (CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Seven.perfect_dvd_168 hperf_X hnt_X hd_X).1
  have hL3_Lc : IsL3 ↥(Lc L g) 1 := by
    haveI := hsimple_X
    have hPSL := CFSG.Quasithin.HSRuLoc.Mod.isPSL_three_two_of_simple_card_168
      (H := ↥(Lc L g)) hcard_X
    change LieModel ↥(Lc L g) .PSL 3 2 1
    exact (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (n := 3) (p := 2) (f := 1)
      (by decide)).2 hPSL
  have hL3_L : IsL3 ↥L 1 := by
    have e : ↥L ≃* ↥(Lc L g) :=
      L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    change LieModel ↥L .PSL 3 2 1
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      (show LieModel ↥(Lc L g) .PSL 3 2 1 from hL3_Lc)
  have hcard_L : Nat.card ↥L = 168 := by
    have e : ↥L ≃* ↥(Lc L g) :=
      L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    rw [Nat.card_congr e.toEquiv, hcard_X]
  obtain ⟨J, hCdJ, hJW, hirr, hcard_J, hMcL, hfaith_J⟩ := hS.2
  have hsec_bot : Nat.card (Sect J ⊥) = Nat.card J := by
    change Nat.card (↥J ⧸ (⊥ : Subgroup W).subgroupOf J) = Nat.card ↥J
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥J)).toEquiv
  have hsec_bot_W : Nat.card (Sect (Wd L) ⊥) = Nat.card (Wd L) := by
    change Nat.card (↥(Wd L) ⧸ (⊥ : Subgroup W).subgroupOf (Wd L)) = Nat.card ↥(Wd L)
    rw [Subgroup.bot_subgroupOf]
    exact Nat.card_congr (QuotientGroup.quotientBot (G := ↥(Wd L))).toEquiv
  have hstab_L_J : StabPair L J ⊥ := by
    intro l hl
    constructor
    · exact hirr.2.1 l hl
    · intro z hz
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one]
  have hfaith_L_J : FaithOn L J ⊥ := by
    intro l hl hfix
    apply hfaith l
    · exact Subgroup.mem_sup_left hl
    · intro u hu
      have hmem : ∀ v ∈ J, l v * v⁻¹ ∈ Cd L := by
        intro v hv
        rw [hC]
        exact hfix v hv
      have h := hfaith_J l hl hmem u hu
      rw [hC, Subgroup.mem_bot] at h
      calc l u = (l u * u⁻¹) * u := by group
        _ = 1 * u := by rw [h]
        _ = u := by simp
  have hcard_secJ : Nat.card ↥(secSub J ⊥ L) = 168 := by
    obtain ⟨e⟩ := mulEquiv_secSub hstab_L_J hfaith_L_J
    rw [← Nat.card_congr e.toEquiv, hcard_L]
  have hMcL' : McLShape (secSub J ⊥ L) := by
    rw [← hC]
    exact hMcL
  have hcard_J8 : Nat.card J = 8 := by
    have h := w1369_mcl_nat_card (H := secSub J ⊥ L) hMcL' hcard_secJ
    rw [hsec_bot] at h
    exact h
  have hcard : Nat.card ↥(Wd L) = 2 ^ 9 := by
    have h := hcard_J
    rw [hC] at h
    rw [hsec_bot, hsec_bot_W] at h
    rw [← h]
    rw [hcard_J8]
    norm_num
  exact ⟨hL3_L, hL3_Lc, hcard, hfaith⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
