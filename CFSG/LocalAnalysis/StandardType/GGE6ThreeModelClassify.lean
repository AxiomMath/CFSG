module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelFrame

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

theorem adRefl_mem_hypE6 {x : Fin Tag.E6.rank → ZMod 3} (hx : x ∈ NoOffRest.hypE6) (i : Fin 6) :
    adRefl .E6 3 i x ∈ NoOffRest.hypE6 := by
  have h := NoOffRest.adAct_mem_hypE6 (simple .E6 i) hx
  have e : adAct .E6 3 (simple .E6 i) x = adRefl .E6 3 i x := adAct_simple (τ := .E6) (p := 3) i x
  exact e ▸ h

theorem rho_conj {R : Type} [Group R] {L' : Type} [Group L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) {ρ : MulAut L' →* MulAut R}
    (hρ : ∀ a l, ρ a (ψ l) = ψ (a l)) (l : L') : ρ (MulAut.conj l) = MulAut.conj (ψ l) := by
  refine MulEquiv.ext fun s => ?_
  obtain ⟨m, rfl⟩ := hψ s
  rw [hρ]
  simp [map_mul, map_inv]

variable {R : Type} [Group R] [Finite R] {L' : Type} [Group L'] [Finite L'] (D : FrameData R)

theorem FrameData.mem_V0 {R : Type} [Group R] (D : FrameData R) {r : R} :
    r ∈ D.V0 ↔ r ∈ D.Tor ∧ ∃ v ∈ NoOffRest.hypE6, MulAut.conj r = D.ad v :=
  Iff.rfl

theorem FrameData.V0_le_Tor {R : Type} [Group R] (D : FrameData R) : D.V0 ≤ D.Tor :=
  fun _ hr => hr.1

private theorem three_smul_eq_zero (x : Fin Tag.E6.rank → ZMod 3) : x + x + x = 0 := by
  funext i
  have h3 : (3 : ZMod 3) = 0 := by decide
  calc (x + x + x) i = 3 * x i := by simp only [Pi.add_apply]; ring
    _ = 0 := by rw [h3, zero_mul]

private theorem pow_three_eq_one_of_mem_V0 (hD : D.Good) {v : R} (hv : v ∈ D.V0) : v ^ 3 = 1 := by
  obtain ⟨-, x, -, hx⟩ := (FrameData.mem_V0 D).1 hv
  have h3 : MulAut.conj (v ^ 3) = 1 := by
    rw [map_pow, hx, pow_three', ← D.ad_add, ← D.ad_add, three_smul_eq_zero, D.ad_zero]
  have hcen : v ^ 3 ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := DFunLike.congr_fun h3 g
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  have := hD.center ▸ hcen
  simpa using this

theorem abelianLift_apply (hAL : GGAbelianLift) (hD : D.Good)
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    {A : Subgroup (MulAut L')} (hA : IsPGroup 3 A) (hal : ∀ a ∈ A, ρ a ∈ D.diag.range)
    {w : Fin 6 → L'} (hw : ∀ i, ψ (w i) = D.nb i) :
    (∀ x ∈ D.Tor.comap ψ, ∀ y ∈ D.Tor.comap ψ, x * y = y * x) ∧
      (∀ a ∈ A, ∀ x ∈ D.Tor.comap ψ, a x = x) ∧ ∀ t : L', ψ t ∈ D.V0 → t ^ 3 = 1 := by
  obtain ⟨hTab, -, hTfix⟩ := hD.torus
  obtain ⟨hnb2, hnbT, hnbact, hcob⟩ := hD.weyl
  obtain ⟨hF, hAlt, hF0⟩ := hD.modules ψ (Set.range w) (fun i => ⟨w i, ⟨i, rfl⟩, hw i⟩)
  have hNT : ∀ n ∈ Set.range w, ∀ t ∈ D.Tor, ψ n * t * (ψ n)⁻¹ ∈ D.Tor := by
    rintro _ ⟨i, rfl⟩ t ht
    rw [hw]
    exact hnbT i t ht
  have hfix : ∀ a ∈ A, ∀ l : L', ψ l ∈ D.Tor → ψ (a l) = ψ l := by
    intro a ha l hl
    obtain ⟨x, hx⟩ := hal a ha
    rw [← hρ a l, ← hx]
    exact hTfix (Multiplicative.toAdd x) _ hl
  have hcobT : ∀ a ∈ A, ∀ n ∈ Set.range w, ψ (n⁻¹ * a n) ∈ D.Tor := by
    rintro a ha _ ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hal a ha
    have h1 : ψ ((w i)⁻¹ * a (w i)) =
        (D.nb i)⁻¹ * D.ad (Multiplicative.toAdd x) (D.nb i) := by
      rw [map_mul, map_inv, hw, ← hρ a (w i), ← hx, hw]
      rfl
    rw [h1]
    have hy : D.ad (Multiplicative.toAdd x) (D.nb i) * D.ad (Multiplicative.toAdd x) (D.nb i) = 1 := by
      rw [← map_mul, hnb2, map_one]
    have hyi : (D.ad (Multiplicative.toAdd x) (D.nb i))⁻¹ = D.ad (Multiplicative.toAdd x) (D.nb i) :=
      inv_eq_of_mul_eq_one_right hy
    have h2 := D.V0_le_Tor (hcob i (Multiplicative.toAdd x))
    rw [hyi] at h2
    rwa [inv_eq_of_mul_eq_one_right (hnb2 i)]
  obtain ⟨ha, hb, hc⟩ := hAL L' R ψ hψ hker hcard D.Tor (Set.range w) hTab hNT hF hAlt A hA hfix
    hcobT
  refine ⟨ha, hb, fun t ht => hc D.V0 D.V0_le_Tor (fun v hv => pow_three_eq_one_of_mem_V0 D hD hv)
    ?_ hF0 t ht⟩
  rintro _ ⟨i, rfl⟩ v hv
  obtain ⟨hvT, x, hx, hvx⟩ := (FrameData.mem_V0 D).1 hv
  rw [hw, FrameData.mem_V0]
  refine ⟨hnbT i v hvT, adRefl .E6 3 i x, ?_, ?_⟩
  · exact adRefl_mem_hypE6 hx i
  · rw [map_mul, map_mul, map_inv, hvx]
    exact hnbact i x

theorem innerPoints_realized (hAL : GGAbelianLift) (hD : D.Good)
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcard : Nat.card ψ.ker = 1 ∨ Nat.card ψ.ker = 3)
    {ρ : MulAut L' →* MulAut R} (hρ : ∀ a l, ρ a (ψ l) = ψ (a l))
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) (hsc : GGTorusSelfCent 3 A)
    (hal : ∀ a ∈ A, ρ a ∈ D.diag.range) {w : Fin 6 → L'} (hw : ∀ i, ψ (w i) = D.nb i) :
    ∀ v ∈ NoOffRest.hypE6, ∃ t : L', ψ t ∈ D.Tor ∧ t ^ 3 = 1 ∧ (∀ a ∈ A, a t = t) ∧
      ∃ a ∈ A, MulAut.conj t = a ∧ ρ a = D.ad v := by
  intro v hv
  obtain ⟨r, hrT, hr3, hrv⟩ := hD.inner v hv
  obtain ⟨t, rfl⟩ := hψ r
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
  obtain ⟨-, hfixA, hcube⟩ := abelianLift_apply D hAL hD hψ hker hcard hρ hAp hal hw
  have ht3 : t ^ 3 = 1 := hcube t ((FrameData.mem_V0 D).2 ⟨hrT, v, hv, hrv⟩)
  have htfix : ∀ a ∈ A, a t = t := fun a ha => hfixA a ha t hrT
  refine ⟨t, hrT, ht3, htfix, MulAut.conj t, hsc t htfix ht3, rfl, ?_⟩
  rw [rho_conj hψ hρ, hrv]

end CFSG.StandardType.E6ThreeModel
