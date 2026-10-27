module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpBlockRank

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)

theorem ggTBJ_sp_core {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK4 : 4 ≤ Nat.card K) {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (f₀ : Fin m → Multiplicative (ZMod p)) {J : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({TableBSymp.spTorusSp hζ f₀} : Set (StatedSp m K))))
    (hcount : p ^ 2 * Nat.card {f : Fin m → Multiplicative (ZMod p) //
        ∀ j ∈ J, TableBSymp.spTorusSp hζ f * j = j * TableBSymp.spTorusSp hζ f} ≤ p ^ m) :
    ∃ (n₁ n₂ : StatedSp m K) (s₁ s₂ : MulAut (Fin m → Multiplicative (ZMod p))),
      n₁ ∈ J ∧ n₂ ∈ J ∧
      (∀ f, n₁ * TableBSymp.spTorusSp hζ f * n₁⁻¹ = TableBSymp.spTorusSp hζ (s₁ f)) ∧
      (∀ f, n₂ * TableBSymp.spTorusSp hζ f * n₂⁻¹ = TableBSymp.spTorusSp hζ (s₂ f)) ∧
      s₁ ^ 2 = 1 ∧ s₂ ^ 2 = 1 ∧
      Nat.card {f : Fin m → Multiplicative (ZMod p) // s₁ f = f} * p = p ^ m ∧
      Nat.card {f : Fin m → Multiplicative (ZMod p) // s₂ f = f} * p = p ^ m ∧
      s₁ * s₂ ≠ s₂ * s₁ := by
  classical
  haveI : Fact p.Prime := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let t : Fin m → Kˣ := fun i => TableBSymp.zmodPowHom hζ (f₀ i)
  have hJ' : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({diagSp K m t} : Set (StatedSp m K))) := by
    simpa only [t, ggTBJSpC_spTorusSp_eq_diagSp hζ f₀] using hJ
  obtain ⟨lam, hperm, hmixed, hswap, _hcentral, hIzero, hIpaired⟩ :=
    ggTBJ_sp_blockData_with_card hp hK4 hζ t hJ' hcount
  by_cases hlam1 : lam = 1
  ·
    let I : Finset (Fin m) := Finset.univ.filter (fun i => t i = 1)
    have hIcard : 2 ≤ I.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, I] using hIzero hlam1
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
    have hti : t i = 1 := (Finset.mem_filter.mp hi).2
    have htj : t j = 1 := (Finset.mem_filter.mp hj).2
    refine ⟨permSp K (Equiv.swap i j), TableBSymp.spSwapSp i,
      SpCoord.permAut (Equiv.swap i j), SpCoord.sgnAut i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hperm i j hij (hti.trans htj.symm) (Or.inl (hti.trans hlam1.symm))
    · exact hswap hlam1 i hti
    · intro f
      exact ggTBJSpC_conj_permSp hζ (Equiv.swap i j) f
    · intro f
      exact ggTBJSpC_conj_spSwapSp hζ i f
    · exact SpCoord.permAut_swap_sq i j
    · exact SpCoord.sgnAut_sq i
    · have hcard := SpCoord.card_fix_permAut_swap (p := p) (k := m) hp hp2 hij
      rwa [ggTBJSpC_card_coord] at hcard
    · have hcard := SpCoord.card_fix_sgnAut (p := p) (k := m) hp hp2 i
      rwa [ggTBJSpC_card_coord] at hcard
    · intro hconj
      let f₀' : Fin m → Multiplicative (ZMod p) :=
        Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod p))
      have h := congrFun (congrArg (fun s : MulAut (Fin m → Multiplicative (ZMod p)) =>
        s f₀') hconj) j
      simp only [MulAut.mul_apply] at h
      simp only [SpCoord.permAut_apply, SpCoord.sgnAut_apply, Function.comp_apply,
        Equiv.swap_inv, Equiv.swap_apply_right, Function.update_self,
        Function.update_of_ne (Ne.symm hij), f₀', Pi.mulSingle_eq_same] at h
      exact ggTBJSpC_ofAdd_one_inv_ne_self hp hp2 h
  ·
    let Ipos : Finset (Fin m) := Finset.univ.filter (fun i => t i = lam)
    let Ineg : Finset (Fin m) := Finset.univ.filter (fun i => t i = lam⁻¹)
    let I : Finset (Fin m) := Ipos ∪ Ineg
    have hIcard : 3 ≤ I.card := by
      have h := hIpaired hlam1
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      have hI : (Finset.univ.filter fun i => t i = lam ∨ t i = lam⁻¹) = I := by
        ext i
        simp [I, Ipos, Ineg]
      rwa [hI] at h
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
      Finset.two_lt_card.mp (by omega : 2 < I.card)
    have hpart : ∀ {i : Fin m}, i ∈ I → t i = lam ∨ t i = lam⁻¹ := by
      intro i hi
      rcases Finset.mem_union.mp hi with h | h
      · exact Or.inl (Finset.mem_filter.mp h).2
      · exact Or.inr (Finset.mem_filter.mp h).2
    have hreflElt_mem : ∀ {u w : Fin m}, u ∈ I → w ∈ I → u ≠ w →
        ggTBJSpC_reflElt t u w ∈ J := by
      intro u w hu hw huw
      exact ggTBJSpC_reflElt_mem_of_paired hlam1 hperm hmixed (hpart hu) (hpart hw) huw
    refine ⟨ggTBJSpC_reflElt t a b, ggTBJSpC_reflElt t b c,
      ggTBJSpC_reflAut p m t a b, ggTBJSpC_reflAut p m t b c,
      hreflElt_mem ha hb hab, hreflElt_mem hb hc hbc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro f
      by_cases h : t a = t b
      · exact ggTBJSpC_reflElt_conj_same hζ h f
      · exact ggTBJSpC_reflElt_conj_mixed hζ h f
    · intro f
      by_cases h : t b = t c
      · exact ggTBJSpC_reflElt_conj_same hζ h f
      · exact ggTBJSpC_reflElt_conj_mixed hζ h f
    · exact ggTBJSpC_reflAut_sq hab
    · exact ggTBJSpC_reflAut_sq hbc
    · exact ggTBJSpC_reflAut_card_fix hp hp2 hab
    · exact ggTBJSpC_reflAut_card_fix hp hp2 hbc
    · exact ggTBJSpC_reflAut_noncomm hp hab hbc hac

end CFSG.StandardType

end
