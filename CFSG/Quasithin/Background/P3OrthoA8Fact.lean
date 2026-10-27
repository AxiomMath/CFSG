module

public import CFSG.Quasithin.Background.G117Inputs
public import CFSG.Quasithin.Background.P3OrthoA8Main
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin

namespace G11

open P3Ortho

theorem a8OrthogonalFact : A8OrthogonalFact := by
  intro V _ _ _ B H Γ hdim hperm hB0 hBnd hBΓ hHΓ hnorm
  obtain ⟨D⟩ := P3Ortho.Data.of_isPermCoreModule hperm
  have hFD : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hBH : ∀ γ : ↥H, ∀ u v, B ((γ : GLV V) u) ((γ : GLV V) v) = B u v :=
    fun γ u v => hBΓ γ (hHΓ γ.2) u v
  obtain ⟨c, hc⟩ := D.eq_smul_B0 B hB0 hBH
  have hc1 : c = 1 := by
    by_contra hne
    have h0 : c = 0 := by
      have : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
      exact this c hne
    have hz : ∀ u v, B u v = 0 := fun u v => by
      have := LinearMap.congr_fun₂ hc u v
      simpa [h0] using this
    exact D.w_ne_zero (hBnd _ (hz _))
  have hBeq : B = D.B0 := by rw [hc, hc1, one_smul]
  subst hBeq
  have hΓO : Γ ≤ orthogonalSubgroupOf D.q := fun γ hγ v =>
    D.q_comp_eq γ (fun v w => hBΓ γ hγ v w) (fun h hh => hnorm γ hγ h hh) v
  have hsmul : ∀ (a : ZMod 2) (x : V), D.q (a • x) = (a * a) • D.q x := fun a x => by
    rw [D.q_smul, smul_eq_mul]
  have hpolar : ∀ x y, QuadraticMap.polar D.q x y = D.B0 x y := D.q_polar
  let Q : QuadraticForm (ZMod 2) V := QuadraticMap.ofPolar D.q hsmul
    (fun x x' y => by rw [hpolar, hpolar, hpolar]; exact LinearMap.map_add₂ D.B0 x x' y)
    (fun a x y => by rw [hpolar, hpolar]; exact LinearMap.map_smul₂ D.B0 a x y)
  have hQ : ∀ x, Q x = D.q x := fun x => rfl
  have hpolarQ : QuadraticMap.polarBilin Q = D.B0 := by
    ext x y
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hQ, hQ, hQ, ← hpolar]
    rfl
  have hnd : (QuadraticMap.polarBilin Q).Nondegenerate := by
    rw [hpolarQ]
    exact D.B0_nondegenerate
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
    ⟨D.sing3, by rw [D.finrank_sing3, hdim], fun x hx => by rw [hQ]; exact D.sing3_q x hx⟩
  have hOeq : orthogonalSubgroupOf D.q = TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.ext fun γ => by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      exact Iff.rfl
  have hO : Nat.card (orthogonalSubgroupOf D.q) = 40320 := by
    obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hnd (n := 3)
      (by rw [hdim]) hplus
    have h1 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_congr e
    have h2 := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := ZMod 2) 2
    rw [← h1] at h2
    rw [hOeq]
    have h3 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) = 40320 := by
      rw [h2]
      simp [Finset.prod_Icc_succ_top]
    exact_mod_cast h3
  have hH : Nat.card H = 20160 := by
    rw [Nat.card_congr D.φ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hHO : H ≤ orthogonalSubgroupOf D.q := hHΓ.trans hΓO
  have hrel : H.relIndex (orthogonalSubgroupOf D.q) = 2 := by
    have h := (H.subgroupOf (orthogonalSubgroupOf D.q)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHO).toEquiv, hH, hO] at h
    change 20160 * H.relIndex (orthogonalSubgroupOf D.q) = 40320 at h
    omega
  have hmul := Subgroup.relIndex_mul_relIndex H Γ (orthogonalSubgroupOf D.q) hHΓ hΓO
  rw [hrel] at hmul
  exact ⟨hdim, D.q, D.q_add, D.q_smul, ⟨D.sing3, D.finrank_sing3, D.sing3_q⟩, hΓO,
    Nat.le_of_dvd (by norm_num) (Dvd.intro_left _ hmul)⟩

end G11

end CFSG.Quasithin
