module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD

variable {V : Type} [CommGroup V]

theorem card_points_ch611 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (W : Subgroup V) :
    Nat.card {X : Subgroup V // X ≤ W ∧ Nat.card X = 2} + 1 = Nat.card W := by
  classical
  have hex : ∀ X : {X : Subgroup V // X ≤ W ∧ Nat.card X = 2}, ∃ x ∈ (X : Subgroup V), x ≠ 1 := by
    rintro ⟨X, -, hX2⟩
    by_contra hcon
    push Not at hcon
    have : X = ⊥ := (Subgroup.eq_bot_iff_forall X).mpr hcon
    rw [this, Subgroup.card_bot] at hX2
    omega
  have hzp : ∀ X : {X : Subgroup V // X ≤ W ∧ Nat.card X = 2},
      Subgroup.zpowers (hex X).choose = X := by
    intro X
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr (hex X).choose_spec.1)
    rw [X.2.2, card_zpowers_of_sq (hV _) (hex X).choose_spec.2]
  let e : {X : Subgroup V // X ≤ W ∧ Nat.card X = 2} ≃ {w : ↥W // ¬ w = 1} :=
    { toFun := fun X => ⟨⟨(hex X).choose, X.2.1 (hex X).choose_spec.1⟩,
        fun h => (hex X).choose_spec.2 (congrArg Subtype.val h)⟩
      invFun := fun w => ⟨Subgroup.zpowers (w : V), (Subgroup.zpowers_le).mpr w.1.2,
        card_zpowers_of_sq (hV _) (fun h => w.2 (Subtype.ext h))⟩
      left_inv := fun X => Subtype.ext (hzp X)
      right_inv := fun w => by
        apply Subtype.ext
        apply Subtype.ext
        set X : {X : Subgroup V // X ≤ W ∧ Nat.card X = 2} :=
          ⟨Subgroup.zpowers (w : V), (Subgroup.zpowers_le).mpr w.1.2,
            card_zpowers_of_sq (hV _) (fun h => w.2 (Subtype.ext h))⟩ with hXdef
        have h1 := (hex X).choose_spec
        rcases (mem_zpowers_iff_of_sq (hV (w : V))).mp h1.1 with h2 | h2
        · exact absurd h2 h1.2
        · exact h2 }
  rw [Nat.card_congr e]
  have h2 := Nat.card_congr (Equiv.sumCompl (fun w : ↥W => w = 1))
  rw [Nat.card_sum] at h2
  have h3 : Nat.card {w : ↥W // w = 1} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩, ⟨⟨1, rfl⟩⟩⟩
  rw [h3] at h2
  omega

theorem card_of_mem_orbitCh611 {Gm : Subgroup (MulAut V)} {X₀ : Subgroup V}
    (hX₀ : Nat.card X₀ = 2) {X : Subgroup V} (hX : X ∈ orbitCh611 Gm X₀) : Nat.card X = 2 := by
  obtain ⟨g, -, rfl⟩ := hX
  rw [← hX₀]
  exact Subgroup.card_map_of_injective (MulEquiv.injective g)

namespace G31Out

variable {Gm : Subgroup (MulAut V)} {X₀ : Subgroup V} (D : G31Out Gm X₀)

theorem V_inf_V {i j : Fin D.s} (hij : i ≠ j) : g31V (D.Δ i) ⊓ g31V (D.Δ j) = ⊥ := by
  have h := D.indV.pairwiseDisjoint hij
  exact disjoint_iff.mp h

theorem Δ_eq_points (hX₀ : Nat.card X₀ = 2) (i : Fin D.s) :
    D.Δ i = {X | X ≤ g31V (D.Δ i) ∧ Nat.card X = 2} ∧ Nat.card (g31V (D.Δ i)) = Nat.card D.V0 := by
  obtain ⟨g, hg, hgV, -⟩ := D.trans ⟨0, D.hs⟩ i
  refine ⟨?_, ?_⟩
  · ext X
    constructor
    · intro hX
      exact ⟨le_g31V hX, card_of_mem_orbitCh611 hX₀ (D.mem_orbit_of_mem hX)⟩
    · rintro ⟨hXV, hX2⟩
      set X' := X.map (g⁻¹ : MulAut V).toMonoidHom with hX'
      have hX'V : X' ≤ D.V0 := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        have hxV := hXV hx
        rw [← hgV] at hxV
        obtain ⟨y, hy, rfl⟩ := hxV
        simpa using hy
      have hX'2 : Nat.card X' = 2 := by
        rw [← hX2]
        exact Subgroup.card_map_of_injective (MulEquiv.injective _)
      have hX'0 : X' ∈ D.Δ ⟨0, D.hs⟩ := by
        rw [D.pts]
        exact ⟨hX'V, hX'2⟩
      have hXo : X ∈ orbitCh611 Gm X₀ := by
        have := map_mem_orbitCh611 (D.mem_orbit_of_mem hX'0) hg
        rwa [hX', map_mul_mulAut, mul_inv_cancel, map_one_mulAut] at this
      rw [← D.union] at hXo
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hXo
      by_cases hki : k = i
      · exact hki ▸ hk
      · exfalso
        have hle : X ≤ g31V (D.Δ k) ⊓ g31V (D.Δ i) := le_inf (le_g31V hk) hXV
        rw [D.V_inf_V hki, le_bot_iff] at hle
        rw [hle, Subgroup.card_bot] at hX2
        omega
  · rw [← hgV]
    exact Subgroup.card_map_of_injective (MulEquiv.injective g)

theorem card_orbit [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hX₀ : Nat.card X₀ = 2)
    (h8 : Nat.card D.V0 = 8) : Nat.card (orbitCh611 Gm X₀) = 7 * D.s := by
  have hdisj : Pairwise (fun i j => Disjoint (D.Δ i) (D.Δ j)) := fun i j hij => D.disj i j hij
  have e := Set.unionEqSigmaOfDisjoint hdisj
  rw [D.union] at e
  rw [Nat.card_congr e, Nat.card_sigma]
  have hi : ∀ i, Nat.card (D.Δ i) = 7 := by
    intro i
    obtain ⟨hΔ, hcard⟩ := D.Δ_eq_points hX₀ i
    have := card_points_ch611 hV (g31V (D.Δ i))
    rw [hcard, h8] at this
    have e2 : Nat.card ↥(D.Δ i) = Nat.card {X : Subgroup V // X ≤ g31V (D.Δ i) ∧
        Nat.card X = 2} := congrArg (fun S : Set (Subgroup V) => Nat.card S) hΔ
    omega
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem odd_s_of_odd [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hX₀ : Nat.card X₀ = 2)
    (h8 : Nat.card D.V0 = 8) (hodd : Odd (Nat.card (orbitCh611 Gm X₀))) : Odd D.s := by
  rw [D.card_orbit hV hX₀ h8] at hodd
  exact (Nat.odd_mul.mp hodd).2

theorem eq_top_of_s_eq_one (htop : g31V (orbitCh611 Gm X₀) = ⊤) (hs1 : D.s = 1) :
    D.V0 = ⊤ ∧ Gm = ⊤ := by
  have hV0 : D.V0 = ⊤ := by
    rw [← htop, ← D.supV]
    apply le_antisymm (le_iSup (fun i => g31V (D.Δ i)) ⟨0, D.hs⟩)
    refine iSup_le fun i => ?_
    have : i = ⟨0, D.hs⟩ := Fin.ext (by have := i.2; omega)
    rw [this]
  refine ⟨hV0, ?_⟩
  rw [eq_top_iff]
  intro ψ _
  have hψ : ψ ∈ stabSubCh611 D.V0 := fun w _ => by
    rw [hV0]
    exact ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩
  obtain ⟨g, hg, hgψ⟩ := D.aut (restrictCh611 ψ hψ)
  have : g = ψ := by
    ext v
    have hv : v ∈ D.V0 := hV0 ▸ Subgroup.mem_top v
    exact hgψ ⟨v, hv⟩
  rw [← this]
  exact D.g31G_le_Gm _ hg

end G31Out

end CFSG.Quasithin.H13
