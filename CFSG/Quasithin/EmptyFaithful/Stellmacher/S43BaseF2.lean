module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseC
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseF
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModF

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem Wn_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Wn (g • δ) = conjSub (g : G) (Wn δ) := by
  unfold Wn
  apply le_antisymm
  · refine iSup₂_le fun l hl => ?_
    obtain ⟨l', rfl⟩ : ∃ l', l = g • l' := ⟨g⁻¹ • l, by simp⟩
    have hl' : dist l' δ = 2 := by rw [← CosetGeom.dist_smul g l' δ]; exact hl
    rw [Zv_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (l : Geo H M) (_ : dist l δ = 2) => Zv l)
      l' hl' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun l hl => ?_
    rw [← conjSub_le_iff, ← Zv_smul]
    exact le_iSup₂_of_le (f := fun (l : Geo H M) (_ : dist l (g • δ) = 2) => Zv l) (g • l)
      (by rw [CosetGeom.dist_smul]; exact hl) le_rfl

omit [Finite G] in
theorem stab_le_normalizer_Wn (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Wn δ : Set G) := by
  intro x hx
  obtain ⟨hmem, hfix⟩ := mem_stab.mp hx
  apply mem_normalizer_of_conjSub_eq
  have := Wn_smul (⟨x, hmem⟩ : ↥(H ⊔ M)) δ
  rw [hfix] at this
  exact this.symm

namespace Sit43

variable {α : Geo H M}

theorem dist_eq_two_of_nbr (hA : F53Amalgam H M S) (hs : Sit43 α) {μ l : Geo H M}
    (hμ : μ ∈ nbrs α) (hl : l ∈ nbrs μ) (hne : l ≠ α) : dist l α = 2 := by
  have hμv : vtype μ = true := vtype_true_of_adj hs.vα hμ
  have hlμ : dist l μ = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hl)
  have hμα : dist μ α = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hμ)
  have h1 := dist_triangle hA.amalgam.gen l μ α
  have h0 : dist l α ≠ 0 := fun h => hne ((dist_eq_zero_iff hA.amalgam.gen).mp h)
  have h1' : dist l α ≠ 1 := by
    intro h
    have hadj := dist_eq_one_iff_adj.mp h
    have hlv : vtype l = false := vtype_false_of_adj hμv hl
    exact vtype_ne_of_adj hadj (hlv.trans hs.vα.symm)
  omega

theorem Vn_le_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ : Geo H M}
    (hδ : δ ∈ nbrs α) : Vn δ ≤ Wn α := by
  refine iSup₂_le fun l hl => ?_
  by_cases h : l = α
  · rw [h]; exact hs.Zv_le_Wn hA h26
  · exact Zv_le_Wn_of_dist (hs.dist_eq_two_of_nbr hA hδ hl h)

theorem w17Hyp (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 4 ≤ bMin H M) : W17Hyp α :=
  ⟨hs.Wn_le_Qv hA (by omega), fun _ hδ => hs.Vn_le_Wn hA h26 hδ, hs.comm_Wn_le hA h26 hb,
    hs.sq_mem_Zv hA h26 hb, stab_le_normalizer_Wn α⟩

theorem S17' (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) (hb : 4 ≤ bMin H M)
    {δ : Geo H M} {E F : Subgroup G} (hδ : δ ∈ nbrs α)
    (hE : stab α ≤ Subgroup.normalizer (E : Set G)) (hF : stab α ≤ Subgroup.normalizer (F : Set G))
    (hZE : Zv α ≤ E) (hEF : E < F) (hFW : F ≤ Wn α)
    (hchief : IsChiefStep (stab α) (Wn α) E F) (hnc : ¬ IsCentralStep (stab α) E F)
    (hC : ∀ w ∈ Wn α, (∀ g ∈ stab α, g * w * g⁻¹ * w⁻¹ ∈ E) → w ∈ E)
    (hVF : Vn δ ⊔ F = Wn α) :
    (∀ q ∈ Qv α, ∀ w ∈ Wn α, q * w * q⁻¹ * w⁻¹ ∈ E) ∧
    (∀ x ∈ Qst δ, ∀ v ∈ Vn δ, x * v * x⁻¹ * v⁻¹ ∈ E) ∧
    E.relIndex (Vn δ ⊔ E) ≤ 4 ∧
    ((IsOrthSec (stab α) E F ∧ F = Wn α) ∨
      (IsNatSec (stab α) E F ∧ F.relIndex (Wn α) ≤ 2 ∧
        E.relIndex ((Vn δ ⊔ E) ⊓ F) ≤ 2)) :=
  hs.S17 hA h26 (hs.w17Hyp hA h26 hb) m17_orth m17_nat hδ hE hF hZE hEF hFW hchief hnc hC hVF

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
