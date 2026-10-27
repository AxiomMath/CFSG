module

public import CFSG.Quasithin.Background.FLc2Fix
public import CFSG.Quasithin.Background.FLc2Sum
public import CFSG.Quasithin.Background.B5Statement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def MLConcl {V : Type} [CommGroup V] (Ls : Subgroup (MulAut V)) (UL' : Subgroup V) : Prop :=
  ∃ (n c : ℕ) (ρ : SLt n →* MulAut V), 3 ≤ n ∧ IsNode n c ∧ (∀ g, ρ g ∈ Ls) ∧
    (∀ k ∈ Ls, ∃ g, ρ g = k) ∧ UL' ≠ ⊥ ∧
    ∀ g : SLt n, ∀ v ∈ UL', (∀ s ∈ Ut n, (ρ (g * s * g⁻¹)) v = v) →
      ∀ i, ∀ hi : IsNode n i, i ≠ c →
        (ρ (g * reflection n (ZMod 2) i hi.1 hi.2 * g⁻¹)) v = v

theorem exists_ne_one_nat {n : ℕ} (hn : 1 ≤ n) : ∃ a : Multiplicative (Vt n), a ≠ 1 := by
  refine ⟨Multiplicative.ofAdd (Pi.single (⟨0, by omega⟩ : Fin n) 1), fun h => ?_⟩
  have := congrFun (congrArg Multiplicative.toAdd h) ⟨0, by omega⟩
  simp at this

theorem exists_ne_one_wedge4 : ∃ a : Multiplicative (⋀[ZMod 2]^2 (Fin 4 → ZMod 2)), a ≠ 1 := by
  obtain ⟨x, hx⟩ := (B5FinWedge.wedgeCoord4_bijective (K := ZMod 2)).2 (Pi.single 0 1)
  refine ⟨Multiplicative.ofAdd x, fun h => ?_⟩
  have h0 : x = 0 := h
  rw [h0, map_zero] at hx
  have := congrFun hx 0
  simp at this

theorem exists_ne_one_wedge5 : ∃ a : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)), a ≠ 1 := by
  obtain ⟨x, hx⟩ := (JonesParshall.wedgeCoord_bijective (K := ZMod 2)).2 (Pi.single 0 1)
  refine ⟨Multiplicative.ofAdd x, fun h => ?_⟩
  have h0 : x = 0 := h
  rw [h0, map_zero] at hx
  have := congrFun hx 0
  simp at this

theorem ne_bot_of_surj {V A : Type} [CommGroup V] [CommGroup A] {U' : Subgroup V} (β : ↥U' →* A)
    (hβ : Function.Surjective β) (a : A) (ha : a ≠ 1) : U' ≠ ⊥ := by
  intro h
  obtain ⟨u, hu⟩ := hβ a
  apply ha
  rw [← hu]
  have : (u : V) ∈ (⊥ : Subgroup V) := h ▸ u.2
  have hu1 : u = 1 := Subtype.ext (Subgroup.mem_bot.1 this)
  rw [hu1, map_one]

theorem ml_case_ext4 {V : Type} [CommGroup V] (hV2 : ∀ w : V, w ^ 2 = 1)
    {Ls : Subgroup (MulAut V)} {UL' Z : Subgroup V} (hZ : Z ≤ CFSG.Quasithin.fixV Ls)
    (h : SLExteriorTwo Ls UL' Z 4) : MLConcl Ls UL' := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨D⟩ := vmodelExtSq hπ (fun g hg z hz => hZ hz g hg)
  refine ⟨4, 2, rhoOf π, by norm_num, ⟨by norm_num, by norm_num⟩, rhoOf_mem π,
    rhoOf_surj hπ.1, ?_, fun g v hv hvf i hi hic => ?_⟩
  · obtain ⟨a, ha⟩ := exists_ne_one_wedge4
    exact ne_bot_of_surj D.β D.surj a ha
  · exact D.fix_reflection_conj hV2 (by norm_num) fix_extSq4 g hv hvf hi hic

theorem ml_case_ext5 {V : Type} [CommGroup V] (hV2 : ∀ w : V, w ^ 2 = 1)
    {Ls : Subgroup (MulAut V)} {UL' : Subgroup V} (h : SLExteriorTwo Ls UL' ⊥ 5) :
    MLConcl Ls UL' := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨D⟩ := vmodelExtSq hπ (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  refine ⟨5, 2, rhoOf π, by norm_num, ⟨by norm_num, by norm_num⟩, rhoOf_mem π,
    rhoOf_surj hπ.1, ?_, fun g v hv hvf i hi hic => ?_⟩
  · obtain ⟨a, ha⟩ := exists_ne_one_wedge5
    exact ne_bot_of_surj D.β D.surj a ha
  · exact D.fix_reflection_conj hV2 (by norm_num) fix_extSq5 g hv hvf hi hic

theorem ml_case_nat {V : Type} [CommGroup V] (hV2 : ∀ w : V, w ^ 2 = 1)
    {Ls : Subgroup (MulAut V)} {UL' : Subgroup V} {n k : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k)
    (h : DirectSumOfCopies Ls UL' ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k) : MLConcl Ls UL' := by
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := h
  have D : ∀ j, VModel n (rhoOf π) (I j) ⊥ (Multiplicative (Vt n)) (fun g a => actM g a) :=
    fun j => Classical.choice
      (vmodelNat (hreal j) (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g))
  have hindep : iSupIndep I := by
    intro i
    have := hind i
    rw [bot_sup_eq] at this
    exact disjoint_iff.2 this
  have hsup' : UL' = ⨆ j, I j := by rw [← hsup, bot_sup_eq]
  refine ⟨n, 1, rhoOf π, by omega, ⟨le_rfl, by omega⟩, rhoOf_mem π, rhoOf_surj (hreal ⟨0, hk⟩).1, ?_,
    fun g v hv hvf i hi hic => ?_⟩
  · obtain ⟨a, ha⟩ := exists_ne_one_nat (by omega : 1 ≤ n)
    have h0 : I ⟨0, hk⟩ ≠ ⊥ := ne_bot_of_surj (D ⟨0, hk⟩).β (D ⟨0, hk⟩).surj a ha
    intro hbot
    apply h0
    rw [eq_bot_iff]
    exact (le_iSup I ⟨0, hk⟩).trans (hsup' ▸ hbot).le
  · rw [hsup'] at hv
    exact fix_reflection_sum hindep D hV2 (by omega) (fun a ha i hi hic => fix_nat a ha i hi hic) g hv hvf hi hic

end CFSG.Quasithin.FLc
