module

public import CFSG.RankThree.GF2n.Smith81.S81YUDef
public import CFSG.RankThree.GF2n.Smith81.S81UTrans
public import CFSG.RankThree.GF2n.Smith81.S81YGenDef
public import CFSG.RankThree.GF2n.Smith81.S81YPure

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  Matrix exteriorPower
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.RootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {K : Type} [Field K]

private theorem isTransvec_mul_self_U {g : GL (Fin 6) F} (hg : IsTransvec F g) : g * g = 1 := by
  apply Units.ext
  have h := hg.1
  set A : Matrix (Fin 6) (Fin 6) F := (g : Matrix (Fin 6) (Fin 6) F)
  have e : (A - 1) * (A - 1) = A * A - (A + A) + 1 := by noncomm_ring
  have h2 : A + A = 0 := by rw [← two_smul F A, CharTwo.two_eq_zero, zero_smul]
  have h1 : (1 : Matrix (Fin 6) (Fin 6) F) + 1 = 0 := by
    rw [← two_smul F (1 : Matrix (Fin 6) (Fin 6) F), CharTwo.two_eq_zero, zero_smul]
  rw [e, h2, sub_zero] at h
  rw [Units.val_mul, Units.val_one]
  calc A * A = (A * A + 1) + 1 := by rw [add_assoc, h1, add_zero]
    _ = 1 := by rw [h, zero_add]

private abbrev wv {σ : F ≃+* F} {e : K ≃+* Fσ σ} (w : E3UWspace σ e) : Cube F :=
  ((show Wform σ from w : Wform σ) : Cube F)

private theorem wv_sub {σ : F ≃+* F} {e : K ≃+* Fσ σ} (a b : E3UWspace σ e) :
    wv (a - b) = wv a - wv b := rfl

private theorem wv_smul {σ : F ≃+* F} {e : K ≃+* Fσ σ} (c : K) (w : E3UWspace σ e) :
    wv (c • w) = ((e c : Fσ σ) : F) • wv w := rfl

private theorem wv_act {σ : F ≃+* F} {e : K ≃+* Fσ σ} (g : SUid σ 6) (w : E3UWspace σ e) :
    wv (e3uWact σ e g w) = rho F (g : GL (Fin 6) F) (wv w) := rfl

private theorem wv_P0 {σ : F ≃+* F} {e : K ≃+* Fσ σ} : wv (e3uP0 σ e) = pt0 F := rfl

theorem isRtU_mul_self {σ : F ≃+* F} (e : K ≃+* Fσ σ) {r : E3UWspace σ e ≃ₗ[K] E3UWspace σ e}
    (hr : IsRtU σ e r) : r * r = 1 := by
  obtain ⟨g, hg, rfl⟩ := hr
  have hgg : g * g = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact isTransvec_mul_self_U hg
  rw [← map_mul (e3uWact σ e), hgg, map_one]

theorem u6_pure_sub {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
    (e : K ≃+* Fσ (unitaryInvolution F 2 f))
    {r : E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K] E3UWspace (unitaryInvolution F 2 f) e}
    (hr : IsRtU (unitaryInvolution F 2 f) e r) {p : E3UWspace (unitaryInvolution F 2 f) e}
    (hp : IsPurePt (e3uGam (unitaryInvolution F 2 f) e) (e3uP0 (unitaryInvolution F 2 f) e) p) :
    r p - p = 0 ∨
      IsPurePt (e3uGam (unitaryInvolution F 2 f) e) (e3uP0 (unitaryInvolution F 2 f) e) (r p - p) := by
  obtain ⟨g, hgt, rfl⟩ := hr
  obtain ⟨g₁, hg₁, c, hc0, hpc⟩ := hp
  obtain ⟨h, rfl⟩ := hg₁
  have hpv : wv p = ((e c : Fσ (unitaryInvolution F 2 f)) : F) •
      rho F (h : GL (Fin 6) F) (pt0 F) := by
    rw [hpc, wv_smul, wv_act, wv_P0]
  have hc₀ := mem_Fσ_iff.mp (e c).2
  have hc₀0 : ((e c : Fσ (unitaryInvolution F 2 f)) : F) ≠ 0 := by
    intro h0
    apply hc0
    have h1 : e c = 0 := Subtype.ext h0
    exact e.injective (h1.trans (map_zero e).symm)
  have hwp : wv p ∈ RootPt (unitaryInvolution F 2 f) := by
    rw [hpv]
    exact smul_mem_RootPt hc₀ hc₀0 (rho_mem_RootPt h.2 pt0_mem_RootPt)
  have key : wv (e3uWact (unitaryInvolution F 2 f) e g p - p) =
      (rho F (g : GL (Fin 6) F) - 1) (wv p) := by
    rw [wv_sub, wv_act, LinearMap.sub_apply, Module.End.one_apply]
  rcases rho_sub_one_mem_RootPt_or_eq_zero g.2 hgt hwp with hR | hR
  · right
    obtain ⟨g', c', hc'0, hσc', hξ'⟩ := u6RootTransStatement_holds F f hF _ hR
    have hmem : c' ∈ Fσ (unitaryInvolution F 2 f) := mem_Fσ_iff.mpr hσc'
    have hcc : ((e (e.symm ⟨c', hmem⟩) : Fσ (unitaryInvolution F 2 f)) : F) = c' :=
      congrArg Subtype.val (e.apply_symm_apply ⟨c', hmem⟩)
    refine ⟨e3uWact (unitaryInvolution F 2 f) e g', MonoidHom.mem_range.mpr ⟨g', rfl⟩,
      e.symm ⟨c', hmem⟩, ?_, ?_⟩
    · intro h0
      apply hc'0
      have h1 : (⟨c', hmem⟩ : Fσ (unitaryInvolution F 2 f)) = 0 := by
        rw [← e.apply_symm_apply ⟨c', hmem⟩, h0, map_zero]
      exact congrArg Subtype.val h1
    · apply Subtype.ext
      have hfin : wv (e3uWact (unitaryInvolution F 2 f) e g p - p) =
          wv (e.symm ⟨c', hmem⟩ •
            e3uWact (unitaryInvolution F 2 f) e g' (e3uP0 (unitaryInvolution F 2 f) e)) := by
        rw [key, hξ', wv_smul, hcc, wv_act, wv_P0]
      exact hfin
  · left
    exact Subtype.ext (key.trans hR)

end CFSG.RankThree.GF2n.Smith81.RootGenU
