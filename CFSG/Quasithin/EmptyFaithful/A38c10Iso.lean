module

public import CFSG.Quasithin.EmptyFaithful.A38c10Fix
public import CFSG.Quasithin.EmptyFaithful.LRed4Alt
public import CFSG.Quasithin.Background.FLc2Fix
public import CFSG.Quasithin.Background.FLc2Sum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open Matrix CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem fixed_elem_eq_zero (v : Fin 4 → ZMod 2)
    (h : ∀ i j : Fin 4, i ≠ j → ((1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + Matrix.single i j 1) *ᵥ v = v) :
    v = 0 := by
  revert v
  decide

theorem det_elem (i j : Fin 4) (hij : i ≠ j) :
    ((1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + Matrix.single i j 1).det = 1 := by
  revert i j
  decide

@[expose] def trv (i j : Fin 4) (hij : i ≠ j) : SLt 4 :=
  ⟨(1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) + Matrix.single i j 1, det_elem i j hij⟩

theorem fixed_nat_eq_one (a : Multiplicative (Vt 4)) (h : ∀ g : SLt 4, actM g a = a) : a = 1 := by
  apply Multiplicative.toAdd.injective
  show Multiplicative.toAdd a = 0
  apply fixed_elem_eq_zero
  intro i j hij
  have := congrArg Multiplicative.toAdd (h (trv i j hij))
  rw [toAdd_actM] at this
  exact this

theorem false_of_sl5 {K : Type} [Group K] [Finite K] (hK : Nat.card K = 20160)
    (π : ↥(StatedSL 5 (ZMod 2)) →* K) (hπ : Function.Surjective π) : False :=
  LRed4.no_epi_sl5 hK π hπ

section Iso

variable {V : Type} [CommGroup V]

theorem iso_package [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {Λ B : Subgroup (MulAut V)} {U : Subgroup V} {k : ℕ}
    (hne : Λ ≠ ⊥) (hB : IsSylowTwoOf B Λ) (hk : 1 ≤ k)
    (hdir : DirectSumOfCopies Λ U ⊥ (FFModel.nat (StatedSL 4 (ZMod 2))) k) :
    ∃ D : BorelIso 4 Λ B,
      (∀ u ∈ U, (∀ b ∈ B, (b : MulAut V) u = u) → D.cutsOf (Λ ⊓ fixSub u) ⊆ {1}) ∧
      fixV Λ ⊓ U = ⊥ := by
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := hdir
  have D : ∀ j, VModel 4 (rhoOf π) (I j) ⊥ (Multiplicative (Vt 4)) (fun g a => actM g a) :=
    fun j => Classical.choice
      (vmodelNat (hreal j) (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g))
  have hindep : iSupIndep I := by
    intro i
    have := hind i
    rw [bot_sup_eq] at this
    exact disjoint_iff.2 this
  have hsup' : U = ⨆ j, I j := by rw [← hsup, bot_sup_eq]
  have hfix : ∀ g : SLt 4, ∀ v ∈ U, (∀ s ∈ Ut 4, (rhoOf π (g * s * g⁻¹)) v = v) →
      ∀ i, ∀ hi : IsNode 4 i, i ∈ {i | i ≠ 1} →
        (rhoOf π (g * reflection 4 (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v := by
    intro g v hv hvf i hi hic
    rw [hsup'] at hv
    exact fix_reflection_sum hindep D hV2 (by omega) (fun a ha i hi hic => fix_nat a ha i hi hic) g hv hvf hi hic
  obtain ⟨g, D', -, -, hcuts⟩ := exists_borelIso_of_rho (by norm_num : 3 ≤ 4) (rhoOf_mem π)
    (rhoOf_surj (hreal ⟨0, hk⟩).1) hfix hne hB
  refine ⟨D', fun u hu huB => ?_, ?_⟩
  · intro i hi
    obtain ⟨hin, hiR⟩ := hcuts u hu huB hi
    have hi1 : i = 1 := by
      by_contra h
      exact hiR h
    exact hi1
  ·
    rw [eq_bot_iff]
    intro x ⟨hxF, hxU⟩
    have hcomm : Pairwise fun i j : Fin k => ∀ x y : V, x ∈ I i → y ∈ I j → Commute x y :=
      fun _ _ _ x y _ _ => Commute.all x y
    have hrange := Subgroup.noncommPiCoprod_range (hcomm := hcomm)
    have hx' : x ∈ (Subgroup.noncommPiCoprod hcomm).range := by rw [hrange, ← hsup']; exact hxU
    obtain ⟨f, hfx⟩ := hx'
    rw [noncommPiCoprod_eq_prod] at hfx
    have hcomp : ∀ g : SLt 4, ∀ j, (rhoOf π g) (f j : V) = (f j : V) := by
      intro g
      refine fixed_components hindep (rhoOf π g) (fun j u hu => (D j).inv _ u hu) f ?_
      rw [hfx]
      exact hxF _ (rhoOf_mem π g)
    have hfj : ∀ j, (f j : V) = 1 := by
      intro j
      have hβ : ∀ g : SLt 4, actM g ((D j).β (f j)) = (D j).β (f j) := by
        intro g
        have hu : (rhoOf π g) ((f j : ↥(I j)) : V) ∈ I j := (D j).inv g _ (f j).2
        have h1 := (D j).equiv g (f j) hu
        have e : (⟨(rhoOf π g) (f j : V), hu⟩ : ↥(I j)) = f j := Subtype.ext (hcomp g j)
        rw [e] at h1
        exact h1.symm
      have h2 := fixed_nat_eq_one _ hβ
      have h3 : ((f j : ↥(I j)) : V) ∈ (⊥ : Subgroup V) := (D j).ker (f j) h2
      exact Subgroup.mem_bot.1 h3
    rw [← hfx]
    exact Finset.prod_eq_one fun j _ => hfj j

theorem orth_package [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {Λ B : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hne : Λ ≠ ⊥) (hB : IsSylowTwoOf B Λ) (hZ : Z ≤ fixV Λ) (hext : SLExteriorTwo Λ U Z 4) :
    ∃ D : BorelIso 4 Λ B,
      ∀ u ∈ U, (∀ b ∈ B, (b : MulAut V) u = u) → D.cutsOf (Λ ⊓ fixSub u) ⊆ {2} := by
  obtain ⟨π, hπ⟩ := hext
  obtain ⟨D⟩ := vmodelExtSq hπ (fun g hg z hz => hZ hz g hg)
  have hfix : ∀ g : SLt 4, ∀ v ∈ U, (∀ s ∈ Ut 4, (rhoOf π (g * s * g⁻¹)) v = v) →
      ∀ i, ∀ hi : IsNode 4 i, i ∈ {i | i ≠ 2} →
        (rhoOf π (g * reflection 4 (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v := by
    intro g v hv hvf i hi hic
    exact D.fix_reflection_conj hV2 (by norm_num) fix_extSq4 g hv hvf hi hic
  obtain ⟨g, D', -, -, hcuts⟩ := exists_borelIso_of_rho (by norm_num : 3 ≤ 4) (rhoOf_mem π)
    (rhoOf_surj hπ.1) hfix hne hB
  refine ⟨D', fun u hu huB i hi => ?_⟩
  obtain ⟨hin, hiR⟩ := hcuts u hu huB hi
  have hi2 : i = 2 := by
    by_contra h
    exact hiR h
  exact hi2

end Iso

end CFSG.Quasithin.A38c10
