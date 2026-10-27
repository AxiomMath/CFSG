module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AModRankLe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.FFC CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem c23a_bridger_mQuot_centralizer_eq_rk_barSub {V E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hE : E ≤ normalizer (V : Set G)) :
    E3.mQuot E (centralizer (V : Set G)) = rk ↥(barSub (⊥ : Subgroup G) V hV E) := by
  classical
  have hE₀ : E ≤ normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hEs : E ≤ stabTil (⊥ : Subgroup G) V := le_stabTil hE hE₀
  let f : ↥E →* MulAut (Vtil (⊥ : Subgroup G) V hV) :=
    (actTil (⊥ : Subgroup G) V hV).comp (Subgroup.inclusion hEs)
  have hrange : f.range = barSub (⊥ : Subgroup G) V hV E := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨⟨(e : G), hEs e.2⟩, e.2, rfl⟩
    · rintro ⟨g, hgE, rfl⟩
      exact ⟨⟨(g : G), hgE⟩, rfl⟩
  have hker : f.ker = (centralizer (V : Set G)).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h v hv
      have h1 : (e : G) * v * (e : G)⁻¹ * v⁻¹ = 1 :=
        Subgroup.mem_bot.1
          ((actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨(e : G), hEs e.2⟩).1 h v hv)
      have h2 : (e : G) * v = v * (e : G) := by
        rw [← mul_inv_eq_one]
        simpa [mul_inv_rev, mul_assoc] using h1
      exact h2.symm
    · intro h
      exact (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨(e : G), hEs e.2⟩).2 fun v hv => by
        rw [Subgroup.mem_bot, ← h v hv]
        group
  have hcard : Nat.card ↥(barSub (⊥ : Subgroup G) V hV E) = f.ker.index := by
    rw [Subgroup.index_ker f, hrange]
  unfold E3.mQuot rk
  rw [hcard, hker, Subgroup.relIndex]

theorem c23a_bridge_rankLe {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G))
    {L₁ L₂ : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV))}
    {E₁ E₂ Z₁ Z₂ : Subgroup (Vtil (⊥ : Subgroup G) V hV)}
    (hP : C23AModPair (barSub (⊥ : Subgroup G) V hV M) L₁ L₂ E₁ E₂ Z₁ Z₂) :
    ∀ E : Subgroup G, E ≤ M → IsElemAbelian 2 E →
      (∀ e ∈ E, e ∈ normalizer (preTil (⊥ : Subgroup G) V hV E₁ : Set G)) →
      (∀ e ∈ E, ∀ y ∈ preTil (⊥ : Subgroup G) V hV E₂, e * y = y * e) →
        E3.mQuot E (centralizer (V : Set G)) ≤ 2 := by
  intro E hEM hel hnorm hcent
  have hE₀ : E ≤ normalizer (⊥ : Subgroup G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hEs : E ≤ stabTil (⊥ : Subgroup G) V := le_stabTil (hEM.trans hM) hE₀
  let A : Subgroup (MulAut (Vtil (⊥ : Subgroup G) V hV)) := barSub (⊥ : Subgroup G) V hV E
  have hA : A ≤ barSub (⊥ : Subgroup G) V hV M := barSub_mono (⊥) V hV hEM
  have hAel : IsElemAbelian 2 A := by
    change IsElemAbelian 2 ((E.subgroupOf (stabTil (⊥ : Subgroup G) V)).map
      (actTil (⊥ : Subgroup G) V hV))
    exact (hel.subgroupOf (stabTil (⊥ : Subgroup G) V)).map (actTil (⊥ : Subgroup G) V hV)
  have hnorm' : ∀ a ∈ A, ∀ u ∈ E₁, a u ∈ E₁ := by
    intro a ha u hu
    obtain ⟨g, hgE, hga⟩ := (mem_barSub (⊥ : Subgroup G) V hV E a).1 ha
    rw [← hga]
    obtain ⟨z, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV u
    have hzpre : z.val ∈ preTil (⊥ : Subgroup G) V hV E₁ :=
      (mem_preTil (⊥ : Subgroup G) V hV E₁).2 ⟨z, rfl, hu⟩
    have hgz : (g : G) * z.val * (g : G)⁻¹ ∈ preTil (⊥ : Subgroup G) V hV E₁ :=
      (Subgroup.mem_normalizer_iff.1 (hnorm (g : G) hgE) z.val).1 hzpre
    have h2 : mkTil (⊥) V hV (actStab (⊥) V hV g z) ∈ E₁ := by
      obtain ⟨x, hxval, hxmem⟩ := (mem_preTil (⊥) V hV E₁).1 hgz
      have hxz : x = actStab (⊥) V hV g z := by
        apply IntMod.val_injective
        rw [actStab_apply_val, hxval]
      rwa [← hxz]
    rw [actTil_mk]
    exact h2
  have hcent' : ∀ a ∈ A, ∀ y ∈ E₂, a y = y := by
    intro a ha y hy
    obtain ⟨g, hgE, hga⟩ := (mem_barSub (⊥ : Subgroup G) V hV E a).1 ha
    rw [← hga]
    obtain ⟨z, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV y
    have hzpre : z.val ∈ preTil (⊥ : Subgroup G) V hV E₂ :=
      (mem_preTil (⊥ : Subgroup G) V hV E₂).2 ⟨z, rfl, hy⟩
    have hcomm : (g : G) * z.val = z.val * (g : G) := hcent (g : G) hgE z.val hzpre
    have heq : actStab (⊥ : Subgroup G) V hV g z = z := by
      apply IntMod.val_injective
      rw [actStab_apply_val, hcomm]
      group
    rw [actTil_mk, heq]
  have hle : rk ↥A ≤ 2 := c23a_modPair_rankLe hP hA hAel hnorm' hcent'
  rw [c23a_bridger_mQuot_centralizer_eq_rk_barSub hV (hEM.trans hM)]
  exact hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
