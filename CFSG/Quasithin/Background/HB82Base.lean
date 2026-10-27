module

public import CFSG.Quasithin.Background.HZ82Base

public section

namespace CFSG.Quasithin.H.ZTrans

open CFSG.Open

variable {V W : Type*} [CommGroup V] [CommGroup W]

@[expose] def HBConcl (H X : Subgroup (MulAut V)) (z : V) : Prop :=
  vZ H z ≤ commV (perfectCore (H ⊓ stabSub (fixV X))) ∧ ¬ vZ H z ≤ fixV X

theorem map_inf_stab_congrHom (e : V ≃* W) (H X : Subgroup (MulAut V)) :
    (H ⊓ stabSub (fixV X)).map (congrHom e) =
      H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e))) := by
  rw [Subgroup.map_inf _ _ _ (congrHom_injective e), fixV_map_congrHom, stabSub_map_congrHom]

theorem HBConcl.of_map [Finite V] [Finite W] (e : V ≃* W) {H X : Subgroup (MulAut V)} {z : V}
    (h : HBConcl (H.map (congrHom e)) (X.map (congrHom e)) (e z)) : HBConcl H X z := by
  obtain ⟨h1, h2⟩ := h
  unfold HBConcl
  have hW := vZ_map e H z
  have hB : (commV (perfectCore (H ⊓ stabSub (fixV X)))).map e.toMonoidHom =
      commV (perfectCore (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e))))) := by
    rw [← map_inf_stab_congrHom, perfectCore_map_congrHom, commV_map_congrHom]
  have hF := fixV_map_congrHom e X
  refine ⟨?_, fun h3 => h2 ?_⟩
  · rw [← Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective, hW, hB]
    exact h1
  · rw [← hW, hF]
    exact Subgroup.map_mono h3

theorem mem_stabSub_of_maps {g : MulAut V} {U : Subgroup V} (hg : ∀ u ∈ U, g u ∈ U)
    (hg' : ∀ u ∈ U, g⁻¹ u ∈ U) : g ∈ stabSub U := by
  intro u
  constructor
  · intro h
    have h2 := hg' (g u) h
    rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h2
  · exact hg u

theorem mem_fixV_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) (w : W) :
    w ∈ fixV (X.map (congrHom e)) ↔ e.symm w ∈ fixV X := by
  rw [fixV_map_congrHom, Subgroup.mem_map_equiv]

theorem map_congrHom_trans (e : V ≃* W) (f : W ≃* W) (H : Subgroup (MulAut V)) :
    H.map (congrHom (e.trans f)) = (H.map (congrHom e)).map (congrHom f) := by
  have hc : congrHom (e.trans f) = (congrHom f).comp (congrHom e) := by
    ext x w
    rfl
  rw [hc, Subgroup.map_map]

theorem factorization_two_eq {G : Type*} [Group G] [Finite G] {S N H : Subgroup G} (hSN : S ≤ N)
    (hNH : N ≤ H) (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) :
    (Nat.card ↥N).factorization 2 = (Nat.card ↥H).factorization 2 := by
  have h1 : Nat.card ↥S ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hSN
  have h2 : Nat.card ↥N ∣ Nat.card ↥H := Subgroup.card_dvd_of_le hNH
  have hN0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  have hH0 : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  refine le_antisymm ((Nat.factorization_le_iff_dvd hN0 hH0).2 h2 2) ?_
  rw [hS] at h1
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hN0).1 h1

theorem hbConcl_of_std [Finite W] {H₀ K₀ P₀ : Subgroup (MulAut W)} {U₀ : Subgroup W} {z₀ : W}
    (hK : K₀ ≤ H₀ ⊓ stabSub U₀) (hKp : IsPGroup 2 ↥K₀) (hfix : ∀ w ∈ fixV K₀, w = 1 ∨ w = z₀)
    (hP : P₀ ≤ H₀ ⊓ stabSub U₀) (hPp : ⁅P₀, P₀⁆ = P₀) (hW : vZ H₀ z₀ ≤ commV P₀)
    (hWU : ¬ vZ H₀ z₀ ≤ U₀) {X : Subgroup (MulAut W)} (hX : fixV X = U₀) {z : W} (hz1 : z ≠ 1)
    {S : Subgroup (MulAut W)} (hSH : S ≤ H₀ ⊓ stabSub U₀)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H₀).factorization 2) (hzS : z ∈ fixV S) :
    HBConcl H₀ X z := by
  have : Finite (MulAut W) := finite_mulAut_z (V := W)
  have hS' : Nat.card ↥S = 2 ^ (Nat.card ↥(H₀ ⊓ stabSub U₀)).factorization 2 := by
    rw [factorization_two_eq hSH inf_le_left hS]
    exact hS
  obtain ⟨g, hg, hgz⟩ := exists_conj_eq_of_fixV hSH hS' hK hKp hfix hzS hz1
  refine HBConcl.of_map g ?_
  have hH : H₀.map (congrHom g) = H₀ := map_congrHom_self hg.1
  have hU : (fixV X).map g.toMonoidHom = fixV X := by
    rw [hX]
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ((hg.2 u).2 hu)
    · intro hw
      refine ⟨g⁻¹ w, (hg.2 _).1 ?_, ?_⟩
      · show g (g⁻¹ w) ∈ U₀
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        exact hw
      · show g (g⁻¹ w) = w
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hXg : fixV (X.map (congrHom g)) = U₀ := by
    rw [fixV_map_congrHom, hU, hX]
  rw [hH, hgz]
  unfold HBConcl
  refine ⟨?_, ?_⟩
  · rw [hXg]
    refine hW.trans (commV_le_iff.2 ?_)
    exact (le_perfectCore_of_perfect hP hPp).trans (commV_le_iff.1 le_rfl)
  · rw [hXg]
    exact hWU

theorem hbConcl_of_equiv [Finite V] [Finite W] (e : V ≃* W) {H X : Subgroup (MulAut V)}
    {H₀ : Subgroup (MulAut W)} {U₀ : Subgroup W} (hH : H.map (congrHom e) = H₀)
    (hXU : fixV (X.map (congrHom e)) = U₀)
    (hstd : ∀ {X' : Subgroup (MulAut W)}, fixV X' = U₀ → ∀ {z' : W}, z' ≠ 1 →
      ∀ {S' : Subgroup (MulAut W)}, S' ≤ H₀ ⊓ stabSub U₀ →
        Nat.card ↥S' = 2 ^ (Nat.card ↥H₀).factorization 2 → z' ∈ fixV S' → HBConcl H₀ X' z')
    {z : V} (hz1 : z ≠ 1) {S : Subgroup (MulAut V)} (hSH : S ≤ H ⊓ stabSub (fixV X))
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hzS : z ∈ fixV S) :
    HBConcl H X z := by
  refine HBConcl.of_map e ?_
  rw [hH]
  have hcH : Nat.card ↥H₀ = Nat.card ↥H := by
    rw [← hH]
    exact card_map_congrHom e H
  refine hstd hXU (z' := e z) (fun h' => hz1 (e.injective (h'.trans (map_one e).symm)))
    (S' := S.map (congrHom e)) ?_ ?_ ?_
  · have h1 := Subgroup.map_mono (f := congrHom e) hSH
    rw [map_inf_stab_congrHom, hXU, hH] at h1
    exact h1
  · rw [hcH, ← hS]
    exact card_map_congrHom e S
  · rintro _ ⟨y, hy, rfl⟩
    show e (y (e.symm (e z))) = e z
    rw [MulEquiv.symm_apply_apply, hzS y hy]

end CFSG.Quasithin.H.ZTrans
