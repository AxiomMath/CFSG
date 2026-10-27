module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLE7Datum

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

private theorem qe7d_reindex_E6 :
    CoxeterMatrix.E₆ = CoxeterMatrix.E₆.reindex (Equiv.refl (Fin 6)) := by
  ext i j
  rfl

theorem ggQ2InL_selDet_of_raw (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) {G : Type}
    [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J)
    (real : Realization (ggG0 3 B x L D J) Bs (excRaw 4)) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hy : y ∈ Bs) {k : Finset (ExcRaw.Root 4)}
    (hkadm : (excRaw 4).admissible k)
    (hkcent : (excRaw 4).cent k =
      Submodule.span (ZMod 3) {real.coord (Additive.ofMul (⟨y, hy⟩ : ↥Bs))})
    (hkcomp : real.component k = K) (h : InLSelDetRaw (excRaw 4) k) :
    GGQ2SelDet G 3 Bs y J K := by
  obtain ⟨e, hpair, hnorm⟩ := h
  have hK1 := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  have hfix : ∀ v, v ∈ ggFixedSubmodule (p := 3) real.coord (ggAutomizer K Bs) ↔
      v ∈ Submodule.span (ZMod 3) {real.coord (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} :=
    fun v => (ggQ2_fixed_excRaw_four real hkadm hkcomp v).trans (by rw [hkcent])
  have hZ := ggQ2_fixedZK_of_K1 hnb hK1 hy real.coord hfix
  have hpair1 : ∀ i i', (((1 : Fin 6 → ℤˣ) i : ℤ) * (1 : Fin 6 → ℤˣ) i') *
      (excRaw 4).pairing (e i) (e i') = CartanMatrix.E 6 i i' := fun i i' => by
    simpa using hpair i i'
  refine ggQ2_selE6_imp_selDet rfl ⟨inLNbrDatum real hkadm hkcomp e 1 CoxeterMatrix.E₆
    (CartanMatrix.E 6) (Or.inr (Or.inl ⟨Equiv.refl _, qe7d_reindex_E6⟩)) ggIntCartan_E₆ hpair1
    hnorm hZ, ⟨Equiv.refl _, ?_⟩, Or.inr ?_⟩
  · exact qe7d_reindex_E6
  · show Module.finrank (ZMod 3) (Fin 7 → ZMod 3) = Fintype.card (Fin 6) + 1
    simp

end CFSG.StandardType.GGQ2Frame

end
