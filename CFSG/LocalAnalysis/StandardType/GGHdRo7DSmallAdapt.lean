module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmAdaptAux_equivFun_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) V) (i : Fin m) :
    b.equivFun (b i) = (Pi.single i (1 : ZMod 3) : Fin m → ZMod 3) := by
  ext j
  rw [Module.Basis.equivFun_self, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (fun hj => h hj.symm)]

private lemma hdRo7DSmAdaptAux_equivFun_basis_dStd {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (i : Fin (n + 1)) : b.equivFun (b i) = dStd n i := by
  rw [hdRo7DSmAdaptAux_equivFun_basis, dStd, Pi.basisFun_apply]

private lemma hdRo7DSmAdaptAux_coord_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (x : V) :
    (dStd n).coord 0 (b.equivFun x) = b.coord 0 x := by
  simp [dStd, Module.Basis.coord_apply, Module.Basis.equivFun_apply]

private lemma hdRo7DSmAdaptAux_dsp_symm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {g : DGL n}
    (hg : DSP 3 (dStd n) g) : DSP 3 b ((ggLinConj b.equivFun).symm g) := by
  obtain ⟨σ, c, hσ0, hc0, hc, hprod, hg⟩ := hg
  refine ⟨σ, c, hσ0, hc0, hc, hprod, fun i => ?_⟩
  rw [show (ggLinConj b.equivFun).symm g (b i) =
    b.equivFun.symm (g (b.equivFun (b i))) from rfl]
  rw [hdRo7DSmAdaptAux_equivFun_basis_dStd b i, hg i, map_smul]
  rw [show b.equivFun.symm (dStd n (σ i)) = b (σ i) from by
    rw [← hdRo7DSmAdaptAux_equivFun_basis_dStd b (σ i), LinearEquiv.symm_apply_apply]]

private lemma hdRo7DSmAdaptAux_dsp_map {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {u : V ≃ₗ[ZMod 3] V}
    (hu : DSP 3 b u) : DSP 3 (dStd n) (ggLinConj b.equivFun u) := by
  obtain ⟨σ, c, hσ0, hc0, hc, hprod, hu⟩ := hu
  refine ⟨σ, c, hσ0, hc0, hc, hprod, fun i => ?_⟩
  rw [ggLinConj_apply]
  rw [show b.equivFun.symm (dStd n i) = b i from by
    rw [← hdRo7DSmAdaptAux_equivFun_basis_dStd b i, LinearEquiv.symm_apply_apply]]
  rw [hu i, map_smul, hdRo7DSmAdaptAux_equivFun_basis_dStd b (σ i)]

private lemma hdRo7DSmAdaptAux_move {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) :
    ggLinMove (ggLinConj τ g) = (ggLinMove g).map (τ : V →ₗ[ZMod p] V') := by
  have hcomp : ((ggLinConj τ g : V' →ₗ[ZMod p] V') - LinearMap.id) =
      (τ : V →ₗ[ZMod p] V').comp
        (((g : V →ₗ[ZMod p] V) - LinearMap.id).comp (τ.symm : V' →ₗ[ZMod p] V)) := by
    ext v
    simp [ggLinConj_apply, map_sub]
  rw [ggLinMove, ggLinMove, hcomp, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr τ.symm.surjective, Submodule.map_top]

private lemma hdRo7DSmAdaptAux_ggLinRefl_conj {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') {r : V ≃ₗ[ZMod p] V} (hr : GGLinRefl r) :
    GGLinRefl (ggLinConj τ r) := by
  obtain ⟨h2, hdim⟩ := hr
  refine ⟨?_, ?_⟩
  · rw [← map_mul, h2, map_one]
  · rw [hdRo7DSmAdaptAux_move, LinearEquiv.finrank_map_eq]
    exact hdim

private lemma hdRo7DSmAdaptAux_c2transv_conj {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (a : V ≃ₗ[ZMod p] V) :
    C2Transv p (ggLinConj τ a) ↔ C2Transv p a := by
  have hmove := hdRo7DSmAdaptAux_move τ a
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← LinearEquiv.finrank_map_eq τ (ggLinMove a), ← hmove]
      exact h1
    · intro w
      have hw := h2 (τ w)
      have hw' : τ (a (a w - w)) = τ (a w - w) := by
        simpa [ggLinConj_apply, map_sub] using hw
      exact τ.injective hw'
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hmove, LinearEquiv.finrank_map_eq]
      exact h1
    · intro w
      obtain ⟨v, rfl⟩ := τ.surjective w
      have hw : a (a v - v) = a v - v := h2 v
      have h1' : ggLinConj τ a (τ v) = τ (a v) := by
        rw [ggLinConj_apply, LinearEquiv.symm_apply_apply]
      have h2' : ggLinConj τ a (τ (a v - v)) = τ (a (a v - v)) := by
        rw [ggLinConj_apply, LinearEquiv.symm_apply_apply]
      have hsub : τ (a v) - τ v = τ (a v - v) := (map_sub τ (a v) v).symm
      calc ggLinConj τ a (ggLinConj τ a (τ v) - τ v)
          = ggLinConj τ a (τ (a v - v)) := by rw [h1', hsub]
        _ = τ (a (a v - v)) := h2'
        _ = τ (a v - v) := by rw [hw]
        _ = τ (a v) - τ v := by rw [map_sub]
        _ = ggLinConj τ a (τ v) - τ v := by rw [h1']

private lemma hdRo7DSmAdaptAux_transport_connected {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (S : Set (V ≃ₗ[ZMod p] V)) {r s : V ≃ₗ[ZMod p] V}
    (h : Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ ¬ Commute a b) r s) :
    Relation.ReflTransGen
      (fun x y : V' ≃ₗ[ZMod p] V' => x ∈ ((ggLinConj τ).toMonoidHom '' S) ∧
        y ∈ ((ggLinConj τ).toMonoidHom '' S) ∧ ¬ Commute x y)
      (ggLinConj τ r) (ggLinConj τ s) :=
  (Relation.ReflTransGen.lift (ggLinConj τ) (fun x y hxy =>
    ⟨⟨x, hxy.1, rfl⟩, ⟨y, hxy.2.1, rfl⟩,
      fun hc => hxy.2.2 (hc.of_map (ggLinConj τ).injective)⟩)) r s h

theorem d_linSmall_of_target : (∀ (n : ℕ), (n = 6 ∨ n = 7) → ∀ (H A : Subgroup (DGL n)), DLinData 3
    n (DV n) (dStd n) H A → (∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker ((dStd n).coord
    0)) → ZS.LinWeyl 3 H) → DLinSmallLeaf := by
  intro hT p hpFact n V hAdd hMod b H A hdata hn hm _
  have hp3 : p = 3 := hdata.hp
  subst p
  let τ : V ≃ₗ[ZMod 3] (DV n) := b.equivFun
  let Hc : Subgroup (DGL n) := H.map (ggLinConj τ).toMonoidHom
  let Ac : Subgroup (DGL n) := A.map (ggLinConj τ).toMonoidHom
  have hτb : ∀ i : Fin (n + 1), τ (b i) = dStd n i := fun i =>
    hdRo7DSmAdaptAux_equivFun_basis_dStd b i
  have hτ0 : τ (b 0) = dStd n 0 := hτb 0
  have hdataC : DLinData 3 n (DV n) (dStd n) Hc Ac := by
    refine ⟨rfl, hdata.hn, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      exact Subgroup.mem_map.mpr ⟨(ggLinConj τ).symm a,
        hdata.hPH ((ggLinConj τ).symm a) (hdRo7DSmAdaptAux_dsp_symm b ha),
        (ggLinConj τ).apply_symm_apply a⟩
    · exact Subgroup.map_mono hdata.hHA
    · intro a ha hafix s hs
      obtain ⟨a₀, ha₀A, rfl⟩ := Subgroup.mem_map.mp ha
      have hafix₀ : a₀ (b 0) = b 0 := by
        apply τ.injective
        have h := hafix
        rw [← hτ0] at h
        change ggLinConj τ a₀ (τ (b 0)) = τ (b 0) at h
        rw [ggLinConj_apply, LinearEquiv.symm_apply_apply] at h
        exact h
      have hstab := hdata.hStab a₀ ha₀A hafix₀ ((ggLinConj τ).symm s)
        (hdRo7DSmAdaptAux_dsp_symm b hs)
      have himg : ggLinConj τ (a₀ * (ggLinConj τ).symm s * a₀⁻¹) =
          ggLinConj τ a₀ * s * (ggLinConj τ a₀)⁻¹ := by
        rw [map_mul, map_mul, map_inv, (ggLinConj τ).apply_symm_apply]
      change DSP 3 (dStd n) (ggLinConj τ a₀ * s * (ggLinConj τ a₀)⁻¹)
      rw [← himg]
      exact hdRo7DSmAdaptAux_dsp_map b hstab
    · intro a ha hconj
      obtain ⟨a₀, ha₀A, rfl⟩ := Subgroup.mem_map.mp ha
      exact hdata.hNoT a₀ ha₀A ((hdRo7DSmAdaptAux_c2transv_conj τ a₀).mp hconj)
    · obtain ⟨S, hS, hHcl, hconn⟩ := hdata.hgen
      refine ⟨(ggLinConj τ).toMonoidHom '' S, ?_, ?_, ?_⟩
      · intro s hs
        obtain ⟨s₀, hs₀, rfl⟩ := hs
        exact ⟨Subgroup.mem_map.mpr ⟨s₀, (hS s₀ hs₀).1, rfl⟩,
          hdRo7DSmAdaptAux_ggLinRefl_conj τ (hS s₀ hs₀).2⟩
      · dsimp only [Hc]
        rw [hHcl, MonoidHom.map_closure]
      · intro s hs t ht
        obtain ⟨s₀, hs₀, rfl⟩ := hs
        obtain ⟨t₀, ht₀, rfl⟩ := ht
        exact hdRo7DSmAdaptAux_transport_connected τ S (hconn s₀ hs₀ t₀ ht₀)
  have hmC : ∃ r ∈ Hc, GGLinRefl r ∧
      ¬ ggLinMove r ≤ LinearMap.ker ((dStd n).coord 0) := by
    obtain ⟨r, hrH, hrRefl, hrmove⟩ := hm
    refine ⟨ggLinConj τ r, Subgroup.mem_map.mpr ⟨r, hrH, rfl⟩,
      hdRo7DSmAdaptAux_ggLinRefl_conj τ hrRefl, ?_⟩
    intro hle
    apply hrmove
    intro x hx
    have hx' : τ x ∈ ggLinMove (ggLinConj τ r) := by
      rw [hdRo7DSmAdaptAux_move τ r]
      exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    have h0 : b.coord 0 x = 0 := by
      rw [← hdRo7DSmAdaptAux_coord_zero b x]
      exact hle hx'
    exact h0
  exact linWeyl_of_map_ggLinConj τ H (hT n hn Hc Ac hdataC hmC)

end CFSG.StandardType.HdRo7D.Small

end
