module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylGenRefl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSylow
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover Multiplicative

namespace ExcWeylGen

variable {τ : Tag} {K : Type} [Field K]

theorem exists_mem_closure_reflections_of_normalizes {p : ℕ} [NeZero p] (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (hrange : (chevTorus τ ζ hζ).range = TableBExc.torusPow τ K p) {a : adjointGroup τ K}
    (ha : ∀ x : adjointGroup τ K, x ∈ TableBExc.torusPow τ K p ↔
      a * x * a⁻¹ ∈ TableBExc.torusPow τ K p) :
    ∃ u ∈ Subgroup.closure (Set.range fun i : Fin τ.rank =>
        torusReflAut (cartanFunctional τ p i) (Pi.single i 1) (cartanFunctional_single i)),
      ∀ f, a * chevTorus τ ζ hζ f * a⁻¹ = chevTorus τ ζ hζ (u f) := by
  obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes (p := p) ha
  set T : Multiplicative (Fin τ.rank → ZMod p) →* ModGL τ K :=
    (adjointGroup τ K).subtype.comp (chevTorus τ ζ hζ) with hT
  have hx : ∀ (i : Fin τ.rank) v, weylElt τ K i 1 * T v * (weylElt τ K i 1)⁻¹ =
      T (torusReflAut (cartanFunctional τ p i) (Pi.single i 1) (cartanFunctional_single i) v) := by
    intro i v
    have h1 := congrArg Subtype.val (weylElt_conj_chevTorus (K := K) ζ hζ i (toAdd v))
    rw [ofAdd_toAdd] at h1
    rw [← ofAdd_toAdd v, torusReflAut_apply]
    simpa [hT] using h1
  obtain ⟨u, hu, huw⟩ := exists_mem_closure_of_conj_mem_closure T (fun i => weylElt τ K i 1)
    (fun i => torusReflAut (cartanFunctional τ p i) (Pi.single i 1) (cartanFunctional_single i))
    hx (canonicalRep_mem_closure (coxeterSystem τ) K w)
  refine ⟨u, hu, fun f => Subtype.ext ?_⟩
  have hfV : chevTorus τ ζ hζ f ∈ TableBExc.torusPow τ K p := hrange ▸ ⟨f, rfl⟩
  have h1 := hw _ (ExcFrames.mem_torusPow_iff_coe.mp hfV)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h1]
  exact huw f

theorem ggTorusWeylGenElt_adjoint [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (TableBExc.torusPow τ K p) = p ^ τ.rank) (hT : GGExcToralRankInput τ K p) :
    GGTorusWeylGenElt p τ.rank (adjointGroup τ K) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  intro E hE hr _
  obtain ⟨g, hg⟩ := hT E hE hr
  have hrange := TableBExc.range_chevTorus_eq_torusPow hζo hζ hdet hV
  have hmemE : ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ (chevTorus τ ζ hζ).range := by
    intro x
    rw [hrange, ← hg]
    constructor
    · intro hx
      exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rintro ⟨y, hy, hyx⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : y = x := mul_left_cancel (mul_right_cancel hyx)
      exact this ▸ hy
  set e : Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (chevTorus τ ζ hζ) with he
  have heapp : ∀ x, e x = g⁻¹ * chevTorus τ ζ hζ x * g := fun x => by
    rw [he, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  set n : Fin τ.rank → adjointGroup τ K := fun i =>
    g⁻¹ * ⟨weylElt τ K i 1, weylElt_mem_adjointGroup i 1⟩ * g with hn
  have hrefl : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ =
      e (.ofAdd (v - cartanFunctional τ p i v • Pi.single i 1)) := by
    intro i v
    rw [heapp, heapp, ← weylElt_conj_chevTorus ζ hζ i v, hn]
    group
  have heE : e.range = E := by
    ext x
    rw [MonoidHom.mem_range, hmemE]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [heapp]; group⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [heapp, hy]; group⟩
  refine ⟨τ.rank, e, (MulAut.conj g⁻¹).injective.comp (chevTorus_injective hζo hζ hdet), heE,
    fun L' _ ψ hψ hker => exists_torus_section_of_reflections hp hp2 e (cartanFunctional τ p)
      (fun i => cartanFunctional_single i) n hrefl hψ hker, fun h hh => ?_⟩
  have hha : ∀ x, x ∈ E ↔ h * x * h⁻¹ ∈ E := Subgroup.mem_set_normalizer_iff.mp hh
  have ha : ∀ x : adjointGroup τ K, x ∈ TableBExc.torusPow τ K p ↔
      g * h * g⁻¹ * x * (g * h * g⁻¹)⁻¹ ∈ TableBExc.torusPow τ K p := by
    intro x
    rw [← hrange]
    have e1 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    have e2 : g * (h * (g⁻¹ * x * g) * h⁻¹) * g⁻¹ = g * h * g⁻¹ * x * (g * h * g⁻¹)⁻¹ := by group
    have k1 := hmemE (g⁻¹ * x * g)
    have k2 := hmemE (h * (g⁻¹ * x * g) * h⁻¹)
    rw [e1] at k1
    rw [e2] at k2
    rw [← k1, ← k2]
    exact hha _
  obtain ⟨u, hu, hconj⟩ := exists_mem_closure_reflections_of_normalizes ζ hζ hrange ha
  refine ⟨u, Subgroup.closure_mono ?_ hu, fun f => ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact torusReflAut_mem_inducedReflSet hp hp2 e (cartanFunctional τ p i) (Pi.single i 1)
      (cartanFunctional_single i) (n i) (hrefl i)
  · rw [heapp, heapp, ← hconj f]
    group

theorem ggTorusWeylGenElt_adjointF4 [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hT : GGF4ToralRankInput K p) :
    GGTorusWeylGenElt p 4 (adjointGroup .F4 K) :=
  ggTorusWeylGenElt_adjoint (τ := .F4) hp hp2 hpq
    (by rw [det_cartan_F4, Int.cast_one]; exact isUnit_one)
    (TableBF4.card_torusPow hp hpq) hT

end ExcWeylGen

end CFSG.StandardType

end
