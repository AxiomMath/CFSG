module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcInduced
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylNormAdjoint

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover Multiplicative


namespace NbrTableBExc

variable {τ : Tag} {K : Type} [Field K]

theorem ggTorusInduced_chevTorus_le {p : ℕ} [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hrange : (chevTorus τ ζ hζ).range = TableBExc.torusPow τ K p)
    (hinj : Function.Injective (chevTorus τ ζ hζ)) :
    ggTorusInduced (chevTorus τ ζ hζ) ≤ Subgroup.closure (Set.range fun i : Fin τ.rank =>
      torusReflAut (cartanFunctional τ p i) (Pi.single i 1) (cartanFunctional_single i)) := by
  intro u hu
  obtain ⟨h, hh⟩ := mem_ggTorusInduced.mp hu
  have hV : ∀ x, x ∈ (chevTorus τ ζ hζ).range ↔ h * x * h⁻¹ ∈ (chevTorus τ ζ hζ).range := by
    intro x
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨u f, (hh f).symm⟩
    · rintro ⟨f', hf'⟩
      refine ⟨u⁻¹ f', ?_⟩
      have h1 := hh (u⁻¹ f')
      rw [MulAut.apply_inv_self] at h1
      exact mul_left_cancel (mul_right_cancel (h1.trans hf'))
  rw [hrange] at hV
  obtain ⟨u₀, hu₀, hconj⟩ :=
    ExcWeylGen.exists_mem_closure_reflections_of_normalizes ζ hζ hrange hV
  have hu : u = u₀ := MulEquiv.ext fun f => hinj ((hh f).symm.trans (hconj f))
  exact hu ▸ hu₀

theorem ggTorusInducedReflElt_adjoint [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank) (hT : GGExcToralRankInput τ K p) :
    GGTorusInducedReflElt p τ.rank (adjointGroup τ K) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hrange : (chevTorus τ ζ hζ).range = TableBExc.torusPow τ K p :=
    TableBExc.range_chevTorus_eq_torusPow hζo hζ hdet hV
  have hχinj : Function.Injective (chevTorus τ ζ hζ) := chevTorus_injective hζo hζ hdet
  have hgen : (Set.range fun i : Fin τ.rank =>
        torusReflAut (cartanFunctional τ p i) (Pi.single i 1) (cartanFunctional_single i)) ⊆
      ggTorusInvolSet p (chevTorus τ ζ hζ) := by
    rintro s ⟨i, rfl⟩
    refine ⟨?_, card_fix_torusReflAut hp hp2 (cartanFunctional τ p i) (Pi.single i 1)
      (cartanFunctional_single i), ?_⟩
    · rw [sq]
      exact torusReflAut_mul_self (cartanFunctional τ p i) (Pi.single i 1)
        (cartanFunctional_single i)
    · refine ⟨⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩, fun f => ?_⟩
      have h1 := weylElt_conj_chevTorus (K := K) ζ hζ i (toAdd f)
      rw [ofAdd_toAdd] at h1
      rw [h1, ← ofAdd_toAdd f, torusReflAut_apply]
      simp
  have hleχ : ggTorusInduced (chevTorus τ ζ hζ) ≤
      Subgroup.closure (ggTorusInvolSet p (chevTorus τ ζ hζ)) :=
    (ggTorusInduced_chevTorus_le ζ hζ hrange hχinj).trans (Subgroup.closure_mono hgen)
  intro E hE hr _ k τ' hτ' hτ'E
  obtain ⟨g, hg⟩ := hT E hE hr
  set τ'' : Multiplicative (Fin k → ZMod p) →* adjointGroup τ K :=
    (MulAut.conj g).toMonoidHom.comp τ' with hτ''
  have hτ''inj : Function.Injective τ'' := (MulAut.conj g).injective.comp hτ'
  have hτ''range : τ''.range = (chevTorus τ ζ hζ).range := by
    rw [hτ'', MonoidHom.range_comp, hτ'E, hg, hrange]
  obtain ⟨γ, hγ⟩ := ExcWeylOuter.exists_mulEquiv_comp_eq hτ''inj hχinj hτ''range
  rw [← ggTorusInduced_comp_mulEquiv (MulAut.conj g) τ',
    ← ggTorusInvolSet_comp_mulEquiv (MulAut.conj g) τ', ← hτ'', ← hγ]
  have hmap : Subgroup.closure (ggTorusInvolSet p (chevTorus τ ζ hζ)) ≤
      (Subgroup.closure (ggTorusInvolSet p
        ((chevTorus τ ζ hζ).comp γ.toMonoidHom))).map (MulAut.congr γ).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr fun s hs => ?_
    refine Subgroup.mem_map.mpr ⟨(MulAut.congr γ).symm s, ?_, ?_⟩
    · have h2 : MulAut.congr γ ((MulAut.congr γ).symm s) = s :=
        MulEquiv.apply_symm_apply (MulAut.congr γ) s
      exact Subgroup.subset_closure ((mem_ggTorusInvolSet_comp_equiv γ (chevTorus τ ζ hζ)
        ((MulAut.congr γ).symm s)).mpr (by rw [h2]; exact hs))
    · exact (MulAut.congr γ).apply_symm_apply s
  intro u hu
  have huχ : MulAut.congr γ u ∈ ggTorusInduced (chevTorus τ ζ hζ) :=
    (ExcWeylOuter.mem_ggTorusInduced_comp_equiv γ (chevTorus τ ζ hζ) u).mp hu
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp (hmap (hleχ huχ))
  have hvu' : v = u := (MulAut.congr γ).injective hvu
  rwa [← hvu']

theorem ggTorusInducedCardElt_adjoint [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank) (hT : GGExcToralRankInput τ K p)
    (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i) :
    GGTorusInducedCardElt p τ.rank (adjointGroup τ K) (Nat.card (WeylGroup τ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  have hrange : (chevTorus τ ζ hζ).range = TableBExc.torusPow τ K p :=
    TableBExc.range_chevTorus_eq_torusPow hζo hζ hdet hV
  have hχinj : Function.Injective (chevTorus τ ζ hζ) := chevTorus_injective hζo hζ hdet
  intro E hE hr _ k τ' hτ' hτ'E
  obtain ⟨g, hg⟩ := hT E hE hr
  set τ'' : Multiplicative (Fin k → ZMod p) →* adjointGroup τ K :=
    (MulAut.conj g).toMonoidHom.comp τ' with hτ''
  have hτ''inj : Function.Injective τ'' := (MulAut.conj g).injective.comp hτ'
  have hτ''range : τ''.range = (chevTorus τ ζ hζ).range := by
    rw [hτ'', MonoidHom.range_comp, hτ'E, hg, hrange]
  obtain ⟨γ, hγ⟩ := ExcWeylOuter.exists_mulEquiv_comp_eq hτ''inj hχinj hτ''range
  have hcard1 : Nat.card (ggTorusInduced ((chevTorus τ ζ hζ).comp γ.toMonoidHom)) =
      Nat.card (ggTorusInduced (chevTorus τ ζ hζ)) :=
    Nat.card_congr (Equiv.subtypeEquiv (MulAut.congr γ).toEquiv
      (fun u => ExcWeylOuter.mem_ggTorusInduced_comp_equiv γ (chevTorus τ ζ hζ) u))
  have hcard2 : Nat.card (ggTorusInduced (chevTorus τ ζ hζ)) = Nat.card (WeylGroup τ) := by
    rw [ExcWeylOuter.ggTorusInduced_chevTorus hsymm ζ hζ hrange hχinj]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (ExcWeylOuter.torusMulAut_injective hp2)).toEquiv).symm
  rw [← ggTorusInduced_comp_mulEquiv (MulAut.conj g) τ', ← hτ'', ← hγ, hcard1, hcard2]

end NbrTableBExc

end CFSG.StandardType

end
