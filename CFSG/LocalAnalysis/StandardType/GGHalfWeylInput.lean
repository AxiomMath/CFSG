module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylFrame
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylReindex
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylReindexLast
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylLevi
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylLeviPerf
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockEmbed

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

theorem ggTypeAHalfLeviInput_of_torusFrame (hstep1 : ∀ {G : Type} [Group G] [Finite G] {B Bs X :
    Subgroup G} {p : ℕ}, p = 3 → GGBstar p B Bs → ∀ {N : ℕ}, 5 ≤ N + 1 → Bs ≤ Subgroup.normalizer (X
    : Set G) → ∀ φ : SpecialLinearGroup (Fin (N + 1)) F2 →* G, φ.range = X → Function.Injective φ →
    ∃ A : SpecialLinearGroup (Fin (N + 1)) F2, GGHalfTorusFrame Bs X (halfTorus N) (φ.comp
    (MulAut.conj A).toMonoidHom)) :
    GGTypeAHalfLeviInput := by
  intro G _ _ p B Bs x L D J m y K hcfg hInn hN hJK
  have h : GGHalfWeylCtx p B Bs x L D J m y K := ⟨hcfg, hInn, hN, hJK⟩
  have hm : 3 ≤ m := by
    have := h.five_le
    omega
  obtain ⟨-, -, -, -, -, -, -, -, hxKn, -⟩ := h.basic
  obtain ⟨ψL, ψK, hL, hK⟩ := h.exists_frames hstep1
  obtain ⟨⟨PL, hPL, tL, htL, hyact⟩, ⟨PK, hPK, tK, htK, hxact⟩⟩ := h.exists_support hL hK
  obtain ⟨cL, hcL1, hcL2, hcL3⟩ := exists_conj_front m hm PL hPL
  obtain ⟨cK, hcK1, hcK2, hcK3⟩ := exists_conj_last m hm PK hPK
  have hJcomp := h.component_J
  have htL1 : tL ≠ 1 := by
    intro h1
    apply h.not_centralizes_L
    intro l hl
    have h2 := hyact l hl
    rw [h1, map_one] at h2
    simp only [one_mul, inv_one, mul_one] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  have htK1 : tK ≠ 1 := by
    intro h1
    apply hxKn
    intro k hk
    have h2 := hxact k hk
    rw [h1, map_one] at h2
    simp only [one_mul, inv_one, mul_one] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  have hJL : J = (slOn (m + 1 + 1 + 1) {i | i ≠ PL.castSucc ∧ i ≠ PL.succ}).map ψL := by
    refine eq_map_slOn_of_component (y := y) hm hL.inj htL htL1 ?_ ?_
    · rw [hL.range]
      exact hyact
    · rw [hL.range]
      exact hJcomp
  have hlevi₁ : ((ψL.comp (MulAut.conj cL).toMonoidHom).comp (slLower2Hom m)).range = J := by
    rw [range_comp_conj ψL cL (slLower2Hom m) _ hcL3]
    exact hJL.symm
  have hcardJ : Nat.card J = Nat.card (SpecialLinearGroup (Fin (m + 1)) F2) := by
    have hinj : Function.Injective
        ((ψL.comp (MulAut.conj cL).toMonoidHom).comp (slLower2Hom m)) :=
      (hL.inj.comp (MulAut.conj cL).injective).comp (slLower2Hom_injective m)
    rw [← hlevi₁]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hJK' : J = (slOn (m + 1 + 1 + 1) {i | i ≠ PK.castSucc ∧ i ≠ PK.succ}).map ψK := by
    obtain ⟨-, -, -, -, -, -, hLx, -, -, -⟩ := h.basic
    refine eq_map_slOn_of_perfect (x := x) hm hK.inj htK htK1 ?_ ?_ ?_ hJcomp.2.2.1 hcardJ
    · rw [hK.range]
      exact hxact
    · rw [hK.range]
      exact hJK
    · intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hLx g (hJcomp.1 hg).1).symm
  have hlevi₂ : ((ψK.comp (MulAut.conj cK).toMonoidHom).comp (slUpper2Hom m)).range = J := by
    rw [range_comp_conj ψK cK (slUpper2Hom m) _ hcK3]
    exact hJK'.symm
  have hsuppY : ∃ t ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩),
      ∀ l ∈ L, y * l * y⁻¹ = (ψL.comp (MulAut.conj cL).toMonoidHom) t * l *
        ((ψL.comp (MulAut.conj cL).toMonoidHom) t)⁻¹ := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp htL
    refine ⟨cL⁻¹ * tL * cL, ?_, fun l hl => ?_⟩
    · rw [Subgroup.mem_zpowers_iff]
      refine ⟨j, ?_⟩
      have h0 : omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ =
          cL⁻¹ * omegaBlock (m + 1 + 1) PL * cL := by
        rw [← hcL2]
        group
      rw [h0, conj_inv_zpow, hj]
    · rw [comp_conj_apply]
      exact hyact l hl
  have hsuppX : ∃ t ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨m + 1, Nat.lt_succ_self _⟩),
      ∀ k ∈ K, x * k * x⁻¹ = (ψK.comp (MulAut.conj cK).toMonoidHom) t * k *
        ((ψK.comp (MulAut.conj cK).toMonoidHom) t)⁻¹ := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp htK
    refine ⟨cK⁻¹ * tK * cK, ?_, fun k hk => ?_⟩
    · rw [Subgroup.mem_zpowers_iff]
      refine ⟨j, ?_⟩
      have h0 : omegaBlock (m + 1 + 1) ⟨m + 1, Nat.lt_succ_self _⟩ =
          cK⁻¹ * omegaBlock (m + 1 + 1) PK * cK := by
        rw [← hcK2]
        group
      rw [h0, conj_inv_zpow, hj]
    · rw [comp_conj_apply]
      exact hxact k hk
  exact ⟨ψL.comp (MulAut.conj cL).toMonoidHom, ψK.comp (MulAut.conj cK).toMonoidHom,
    hL.conj_of_mem_iff cL hcL1, hK.conj_of_mem_iff cK hcK1, hlevi₁, hlevi₂, hsuppY, hsuppX⟩

end CFSG.StandardType

end
