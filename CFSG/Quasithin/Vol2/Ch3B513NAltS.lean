module

public import CFSG.Quasithin.Vol2.Ch3B513NAltB
public import CFSG.Quasithin.Background.SmithB51P5Fix

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {W : Type} [CommGroup W] [Finite W]

theorem hasGood_of_altNatural (hW : ∀ w : W, w ^ 2 = 1) {G L : Subgroup (MulAut W)} (hLG : L ≤ G)
    (hU : commV L ∈ IrrPlus L ⊤) {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (hA : AlternatingNatural L (commV L) (fixV L ⊓ commV L) n) : HasGood G := by
  obtain ⟨π, hπ⟩ := hA
  obtain ⟨a, haL, ha1, ha2, hcard⟩ := exists_inv_alt hW hn hπ hU.2.2.1
  exact HasGood.of_zpowers hW (hLG haL) ha1 ha2 hcard

theorem altNatural_of_symNatural {G L : Subgroup (MulAut W)} (h : B51Hyp G L)
    {T : Subgroup (MulAut W)} (hT : IsSylowTwoOf T G) (hGT : G = L ⊔ T) {n : ℕ}
    {U Z : Subgroup W} (hS : SymmetricNatural G U Z n) : AlternatingNatural L U Z n := by
  obtain ⟨π', hπ⟩ := hS
  let π : Equiv.Perm (Fin n) →* ↥G := π'
  have hLG : L ≤ G := h.2.2.2.1
  have hsub : ∀ σ ∈ alternatingGroup (Fin n), ((π σ : ↥G) : MulAut W) ∈ L := by
    intro σ hσ
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating] at hσ
    induction hσ using Subgroup.closure_induction with
    | mem c hc =>
      have h3 : ((π c : ↥G) : MulAut W) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, ← map_pow, ← hc.orderOf, pow_orderOf_eq_one, map_one,
          Subgroup.coe_one]
      have hmem : ((π c : ↥G) : MulAut W) ∈ L ⊔ T := hGT ▸ (π c).2
      exact B5.P5.mem_of_pow_three_eq_one h hT.1 hT.2.1 hmem h3
    | one => rw [map_one]; exact L.one_mem
    | mul x y _ _ hx hy => rw [map_mul, Subgroup.coe_mul]; exact L.mul_mem hx hy
    | inv x _ hx => rw [map_inv, Subgroup.coe_inv]; exact L.inv_mem hx
  let πL : ↥(alternatingGroup (Fin n)) →* ↥L :=
    (G.subtype.comp (π.comp (alternatingGroup (Fin n)).subtype)).codRestrict L
      (fun σ => hsub σ σ.2)
  have hπL : ∀ σ, ((πL σ : ↥L) : MulAut W) = ((π σ : ↥G) : MulAut W) := fun σ => rfl
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp h.2.1.1
  have hsurj : Function.Surjective πL := by
    rintro ⟨l, hl⟩
    rw [← hperf] at hl
    have hGG : ⁅L, L⁆ ≤ ((alternatingGroup (Fin n)).map (G.subtype.comp π)) := by
      refine (Subgroup.commutator_mono hLG hLG).trans ?_
      have hG : G = (⊤ : Subgroup (Equiv.Perm (Fin n))).map (G.subtype.comp π) := by
        rw [Subgroup.map_top, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (show
          Function.Surjective π from hπ.1),
          Subgroup.map_top, Subgroup.range_subtype]
      conv_lhs => rw [hG]
      rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono (by
        rw [← commutator_def]
        exact alternatingGroup.commutator_perm_le)
    obtain ⟨σ, hσ, hσl⟩ := hGG hl
    exact ⟨⟨σ, hσ⟩, Subtype.ext hσl⟩
  obtain ⟨-, hZU, hks, hGU, hGZ, hsec, hker, β, hβs, hβk, hβe⟩ := hπ
  refine ⟨πL, hsurj, hZU, hks, fun x u hu => hGU ⟨x, hLG x.2⟩ u hu,
    fun x z hz => hGZ ⟨x, hLG x.2⟩ z hz, fun γ m hm => hsec γ.1 m hm,
    fun γ m hm => hker γ.1 m hm, β, hβs, hβk, fun γ u m hu hm hβ => ?_⟩
  exact hβe γ.1 u m hu hm hβ

theorem hasGood_of_symNatural (hW : ∀ w : W, w ^ 2 = 1) {G L : Subgroup (MulAut W)}
    (h : B51Hyp G L) (hU : commV L ∈ IrrPlus L ⊤) {T : Subgroup (MulAut W)}
    (hT : IsSylowTwoOf T G) (hGT : G = L ⊔ T) {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (hS : SymmetricNatural G (commV L) (fixV L ⊓ commV L) n) : HasGood G :=
  hasGood_of_altNatural hW h.2.2.2.1 hU (by omega)
    (altNatural_of_symNatural h hT hGT hS)

end CFSG.Quasithin.B513N
