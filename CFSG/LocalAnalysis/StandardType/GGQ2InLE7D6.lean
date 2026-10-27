module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLE7Datum
public import CFSG.LocalAnalysis.StandardType.GGQ2InLD6NormAt

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

private theorem qe7f_reindex_D6 :
    ggCoxeterMatrixD 6 = (ggCoxeterMatrixD 6).reindex (Equiv.refl (Fin 6)) := by
  ext i j
  rfl

theorem ggQ2InL_automizer_ne_bot {G : Type} [Group G] [Finite G] {H Bs J : Subgroup G}
    (real : Realization H Bs (excRaw 4)) {j : (excRaw 4).Code}
    (hjadm : (excRaw 4).admissible j) (hjcomp : real.component j = J)
    (e : Fin 6 → (excRaw 4).Root) (b : Fin 6) (hb : b ≠ 0)
    (hnormj : (excRaw 4).normalizerGroup j =
      Subgroup.closure ((excRaw 4).reflection '' (e '' {i | i ≠ b}))) :
    ggAutomizer J Bs ≠ ⊥ := by
  intro hbot
  have hmem : (excRaw 4).reflection (e 0) ∈ (excRaw 4).normalizerGroup j := by
    rw [hnormj]
    exact Subgroup.subset_closure ⟨e 0, ⟨0, fun h0 => hb h0.symm, rfl⟩, rfl⟩
  have h1 : (ggAutomizer J Bs).map (ggLin (p := 3) real.coord) =
      (excRaw 4).normalizerGroup j := by
    have h := real.normalizer_eq j hjadm
    rwa [hjcomp] at h
  rw [← h1, hbot, Subgroup.map_bot, Subgroup.mem_bot] at hmem
  have h2 := LinearEquiv.congr_fun hmem ((excRaw 4).coroot (e 0))
  have h3 : (excRaw 4).root (e 0) ((excRaw 4).coroot (e 0)) = 2 := by
    rw [(excRaw 4).pairing_eq, (excRaw 4).pairing_self]
    norm_num
  rw [(excRaw 4).reflection_apply, h3] at h2
  have h4 : (2 : ZMod 3) • (excRaw 4).coroot (e 0) = 0 := by
    have h5 : (excRaw 4).coroot (e 0) - (2 : ZMod 3) • (excRaw 4).coroot (e 0) =
        (excRaw 4).coroot (e 0) := h2
    exact sub_eq_self.mp h5
  rcases smul_eq_zero.mp h4 with h6 | h6
  · exact absurd h6 (by decide)
  · rw [h6, map_zero] at h3
    exact absurd h3 (by decide)

theorem ggQ2InL_selD6_of_raw (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) {G : Type}
    [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J)
    (real : Realization (ggG0 3 B x L D J) Bs (excRaw 4)) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hy : y ∈ Bs) {j k : Finset (ExcRaw.Root 4)}
    (hjadm : (excRaw 4).admissible j) (hjcomp : real.component j = J)
    (hkadm : (excRaw 4).admissible k)
    (hkcent : (excRaw 4).cent k =
      Submodule.span (ZMod 3) {real.coord (Additive.ofMul (⟨y, hy⟩ : ↥Bs))})
    (hkcomp : real.component k = K) (h : InLSelD6Raw (excRaw 4) j k) :
    GGQ2SelD6 G 3 Bs y J K := by
  obtain ⟨e, ε, b, hb, hpair, hnormk, hnormj⟩ := h
  have hb0 : b ≠ 0 := by rcases hb with rfl | rfl <;> decide
  have hAJ := ggQ2InL_automizer_ne_bot real hjadm hjcomp e b hb0 hnormj
  have hK1 := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  have hfix : ∀ v, v ∈ ggFixedSubmodule (p := 3) real.coord (ggAutomizer K Bs) ↔
      v ∈ Submodule.span (ZMod 3) {real.coord (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} :=
    fun v => (ggQ2_fixed_excRaw_four real hkadm hkcomp v).trans (by rw [hkcent])
  have hZ := ggQ2_fixedZK_of_K1 hnb hK1 hy real.coord hfix
  have hW : GGIsWeylMatrix (ggCoxeterMatrixD 6) :=
    Or.inl ⟨6, Equiv.refl _, by norm_num, Or.inr (Or.inr ⟨by norm_num, qe7f_reindex_D6⟩)⟩
  let N := inLNbrDatum real hkadm hkcomp e ε (ggCoxeterMatrixD 6) (CartanMatrix.D 6) hW
    (ggIntCartan_D 6) hpair hnormk hZ
  have hfork : N.IsD6Fork b := ⟨Equiv.refl _, qe7f_reindex_D6, hb⟩
  refine ⟨N, b, hfork, ?_, Or.inr ?_,
    QTwoD6.ggQ2_normAt_of_d6Datum hLB hP hS hI1 hAJ hnb hy N b hfork⟩
  · have h1 : (ggAutomizer J Bs).map (ggLin (p := 3) real.coord) =
        (excRaw 4).normalizerGroup j := by
      have h := real.normalizer_eq j hjadm
      rwa [hjcomp] at h
    have h2 := eq_closure_ggLinInv_of_map_eq (p := 3) real.coord (h1.trans hnormj)
    rw [h2, Set.image_image, Set.image_image]
    rfl
  · show Module.finrank (ZMod 3) (Fin 7 → ZMod 3) = Fintype.card (Fin 6) + 1
    simp

end CFSG.StandardType.GGQ2Frame

end
