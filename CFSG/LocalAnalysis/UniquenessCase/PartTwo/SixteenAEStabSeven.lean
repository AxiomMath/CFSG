module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4Aut
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16ae_eq_bot_of_stab_seven {T : Type} [CommGroup T] [Finite T] (hT : ∀ t : T, t ^ 2 = 1)
    {X : Subgroup (MulAut T)} {ι : Type} {Y : ι → Subgroup T} (hsup : ⨆ i, Y i = ⊤)
    (hrk : ∀ i, rk ↥(Y i) = 3) (htrans : ∀ i j, ∃ g ∈ X, (Y i).map g.toMonoidHom = Y j)
    {Q : Subgroup (MulAut T)} (hQX : Q ≤ X) (hQ : IsPGroup 7 ↥Q) (hQ1 : Q ≠ ⊥)
    (hQn : ∀ φ ∈ X, Q.map (MulAut.conj φ).toMonoidHom = Q)
    (hQY : ∀ q ∈ Q, ∀ i, (Y i).map q.toMonoidHom = Y i) {A : Subgroup (MulAut T)} (hAX : A ≤ X)
    (hA : IsElemAbelian2 A) (hstab : ∀ a ∈ A, ∀ i, (Y i).map a.toMonoidHom = Y i) :
    A = ⊥ := by
  classical
  have hfix_triv : ∀ φ : MulAut T, (∀ i, ∀ y ∈ Y i, φ y = y) → φ = 1 := by
    intro φ hφ
    apply MulEquiv.ext
    intro v
    have hv : v ∈ fixV (Subgroup.zpowers φ) := by
      have htop : (⊤ : Subgroup T) ≤ fixV (Subgroup.zpowers φ) := by
        rw [← hsup]
        refine iSup_le fun i => ?_
        intro y hy
        exact mem_fixV_zpowers_iff_apply.mpr (hφ i y hy)
      exact htop (Subgroup.mem_top v)
    simpa using mem_fixV_zpowers_iff_apply.mp hv
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  by_contra hane
  have hmove : ∃ i, ∃ y ∈ Y i, a y ≠ y := by
    by_contra h
    exact hane (hfix_triv a fun i y hy => by
      by_contra hne
      exact h ⟨i, y, hy, hne⟩)
  obtain ⟨i₀, y₀, hy₀, hmove₀⟩ := hmove
  have horder : ∃ k : ℕ, orderOf a = 2 ^ k := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (hA.2 a ha)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  have hcent₀ : ∀ q ∈ Q, ∀ y ∈ Y i₀, q y = y :=
    s16n9b_case4_aut_norm7 hT (hrk i₀) hQ (fun q hq => hQY q hq i₀) horder
      (hstab a ha i₀) (hQn a (hAX ha)) ⟨y₀, hy₀, hmove₀⟩
  have hcent_all : ∀ q ∈ Q, ∀ j, ∀ y ∈ Y j, q y = y := by
    intro q hq j y hy
    obtain ⟨g, hgX, hgY⟩ := htrans i₀ j
    have hy' : y ∈ (Y i₀).map g.toMonoidHom := by rw [hgY]; exact hy
    obtain ⟨y', hy'Y, hy'y⟩ := Subgroup.mem_map.1 hy'
    have hgy : g y' = y := by simpa using hy'y
    have hq'Q : MulAut.conj g⁻¹ q ∈ Q := by
      have hmem : (MulAut.conj g⁻¹).toMonoidHom q ∈ Q.map (MulAut.conj g⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hq
      rwa [hQn g⁻¹ (X.inv_mem hgX)] at hmem
    have h1 : g⁻¹ (q y) = y' := by
      have h2 := hcent₀ (MulAut.conj g⁻¹ q) hq'Q y' hy'Y
      rw [MulAut.conj_apply, inv_inv, MulAut.mul_apply, MulAut.mul_apply] at h2
      rw [hgy] at h2
      exact h2
    calc q y = g (g⁻¹ (q y)) := (MulAut.apply_inv_self T g (q y)).symm
      _ = g y' := by rw [h1]
      _ = y := hgy
  refine hQ1 ?_
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  exact hfix_triv q fun i y hy => hcent_all q hq i y hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
