module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClScalar
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClIrred
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClGraph
public import CFSG.RankThree.GF2n.Stroth80.Sec311OmegaOrbit

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

private theorem le_sympSubgroup_of_le_orth {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {F : LinearMap.BilinForm K V}
    {Qf : QuadraticForm K V} (hQF : Qf.polarBilin = F) {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ orthSubgroup Qf) : H ≤ sympSubgroup F := by
  intro g hg
  have hQg : ∀ v : V, Qf (g v) = Qf v := hH hg
  show IsIsom F g
  intro a b
  have h1 := qf_add hQF (g a) (g b)
  have h2 := qf_add hQF a b
  have h3 : Qf (g a + g b) = Qf (a + b) := by
    rw [← map_add g a b]
    exact hQg (a + b)
  rw [h3, h2, hQg a, hQg b] at h1
  linear_combination -h1

theorem orbit_transitive_omega
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (F : LinearMap.BilinForm K V) (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 4 ≤ Module.finrank K V) {Qf : QuadraticForm K V} (hQF : Qf.polarBilin = F)
    (H : Subgroup (V ≃ₗ[K] V)) (hH : H ≤ orthSubgroup Qf)
    (P : Set V) (hP0 : ∀ e ∈ P, e ≠ 0) (hPsing : ∀ e ∈ P, Qf e = 0)
    (hspan : Submodule.span K P = ⊤)
    (hfull : ∀ e ∈ P, ElationFull F ((H : Set (V ≃ₗ[K] V)) ∩ pointRad F e) e)
    {x y : V} (hx : x ∈ P) (hy : y ∈ P) :
    ∃ h ∈ H, ∃ c : K, c ≠ 0 ∧ h x = c • y := by
  have hdim3 : 3 ≤ Module.finrank K V := by omega
  have hHs : H ≤ sympSubgroup F := le_sympSubgroup_of_le_orth hQF hH
  have hQH : ∀ g ∈ H, ∀ v : V, Qf (g v) = Qf v := fun g hg => hH hg
  obtain ⟨S, hS⟩ : ∃ S : Set V, ∀ v, v ∈ S ↔
      ∃ c : K, ∃ g ∈ H, ∃ e ∈ P, c ≠ 0 ∧ v = c • g e :=
    ⟨{v | ∃ c : K, ∃ g ∈ H, ∃ e ∈ P, c ≠ 0 ∧ v = c • g e}, fun v => Iff.rfl⟩
  have hPS : ∀ e ∈ P, e ∈ S := fun e he =>
    (hS e).mpr ⟨1, 1, H.one_mem, e, he, one_ne_zero, by simp⟩
  have hS0 : ∀ v ∈ S, v ≠ 0 := by
    intro v hv
    obtain ⟨c, g, hg, e, he, hc, rfl⟩ := (hS v).mp hv
    have hge : g e ≠ 0 := fun h0 => hP0 e he (g.injective (h0.trans (map_zero g).symm))
    exact smul_ne_zero hc hge
  have hSsing : ∀ v ∈ S, Qf v = 0 := by
    intro v hv
    obtain ⟨c, g, hg, e, he, hc, rfl⟩ := (hS v).mp hv
    rw [qf_smul, hQH g hg e, hPsing e he, mul_zero]
  have hSinv : ∀ g ∈ H, ∀ v ∈ S, g v ∈ S := by
    intro g hg v hv
    obtain ⟨c, h, hh, e, he, hc, rfl⟩ := (hS v).mp hv
    refine (hS _).mpr ⟨c, g * h, H.mul_mem hg hh, e, he, hc, ?_⟩
    rw [map_smul, LinearEquiv.mul_apply]
  have hSfull : ∀ v ∈ S, ElationFull F ((H : Set (V ≃ₗ[K] V)) ∩ pointRad F v) v := by
    intro v hv
    obtain ⟨c, g, hg, e, he, hc, rfl⟩ := (hS v).mp hv
    have hpr : pointRad F (c • g e) = pointRad F (g e) := by
      unfold pointRad
      rw [pointRad_smul hc]
    rw [hpr, elationFull_smul hc]
    exact elationFull_conj hHs (hfull e he) hg
  have hSspan : Submodule.span K S = ⊤ := by
    rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono (fun e he => hPS e he)
  obtain ⟨O, hO⟩ : ∃ O : Set V, ∀ v, v ∈ O ↔ ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ v = c • g x :=
    ⟨{v | ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ v = c • g x}, fun v => Iff.rfl⟩
  have hxO : x ∈ O := (hO x).mpr ⟨1, H.one_mem, 1, one_ne_zero, by simp⟩
  have hOS : ∀ v ∈ O, v ∈ S := by
    intro v hv
    obtain ⟨g, hg, c, hc, rfl⟩ := (hO v).mp hv
    exact (hS _).mpr ⟨c, g, hg, x, hx, hc, rfl⟩
  have hOinv : ∀ g ∈ H, ∀ v ∈ O, g v ∈ O := by
    intro g hg v hv
    obtain ⟨h, hh, c, hc, rfl⟩ := (hO v).mp hv
    refine (hO _).mpr ⟨g * h, H.mul_mem hg hh, c, hc, ?_⟩
    rw [map_smul, LinearEquiv.mul_apply]
  have hOsmul : ∀ c : K, c ≠ 0 → ∀ v ∈ O, c • v ∈ O := by
    intro c hc v hv
    obtain ⟨g, hg, d, hd, rfl⟩ := (hO v).mp hv
    refine (hO _).mpr ⟨g, hg, c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_smul]
  have claimA : ∀ a ∈ O, ∀ b ∈ S, F b a ≠ 0 → b ∈ O := by
    intro a ha b hb hba
    have haS : a ∈ S := hOS a ha
    have ha0 : a ≠ 0 := hS0 a haS
    have hUinv : ∀ g ∈ H, ∀ u ∈ Submodule.span K O, g u ∈ Submodule.span K O := by
      intro g hg u hu
      induction hu using Submodule.span_induction with
      | mem v hv => exact Submodule.subset_span (hOinv g hg v hv)
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add u₁ u₂ _ _ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
      | smul c u _ h => rw [map_smul]; exact Submodule.smul_mem _ c h
    have hUne : Submodule.span K O ≠ ⊥ := by
      intro hbot
      have hxU : x ∈ Submodule.span K O := Submodule.subset_span hxO
      rw [hbot, Submodule.mem_bot] at hxU
      exact hP0 x hx hxU
    have hUtop : Submodule.span K O = ⊤ :=
      eq_top_of_invariant hnd halt hdim3 hHs hS0 hSfull hSspan (Submodule.span K O) hUinv hUne
    obtain ⟨v₀, hv₀O, hv₀a⟩ : ∃ v₀ ∈ O, F v₀ a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hsub : Submodule.span K O ≤ LinearMap.ker (F.flip a) :=
        Submodule.span_le.mpr fun v hv => LinearMap.mem_ker.mpr (hcon v hv)
      rw [hUtop] at hsub
      have hall' : ∀ v : V, v ∈ LinearMap.ker (F.flip a) := fun v => hsub Submodule.mem_top
      exact ha0 (hnd.2 a fun v => LinearMap.mem_ker.mp (hall' v))
    obtain ⟨c', hc'⟩ : ∃ c' : K, c' = F b a * (F v₀ a)⁻¹ := ⟨_, rfl⟩
    have hc'0 : c' ≠ 0 := by
      rw [hc']
      exact mul_ne_zero hba (inv_ne_zero hv₀a)
    have hv : c' • v₀ ∈ O := hOsmul c' hc'0 v₀ hv₀O
    have hQv : Qf (c' • v₀) = 0 := by
      rw [qf_smul, hSsing v₀ (hOS v₀ hv₀O), mul_zero]
    have hFv : F (c' • v₀) a = F b a := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hc', mul_assoc,
        inv_mul_cancel₀ hv₀a, mul_one]
    obtain ⟨g, hg, hgb⟩ := exists_apply_eq_of_elationFull_orth hnd halt hQF hH
      (hSsing a haS) (hSfull a haS) (hSsing b hb) hQv hba hFv
    have hbg : (g⁻¹) (c' • v₀) = b := by
      rw [← hgb]
      simp
    have hmem := hOinv (g⁻¹) (H.inv_mem hg) _ hv
    rw [hbg] at hmem
    exact hmem
  have hconn := connected_of_elationFull hnd halt hHs S hS0 hSinv hSspan (hPS x hx) (hfull x hx)
  have hall : ∀ z, Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ F a b ≠ 0) x z →
      z ∈ O := by
    intro z hz
    induction hz with
    | refl => exact hxO
    | tail _ hstep ih =>
      obtain ⟨_, hcS, hbc⟩ := hstep
      exact claimA _ ih _ hcS (by rw [form_comm halt]; exact hbc)
  obtain ⟨h, hh, c, hc, hyc⟩ := (hO y).mp (hall y (hconn y (hPS y hy)))
  refine ⟨h, hh, c⁻¹, inv_ne_zero hc, ?_⟩
  rw [hyc, smul_smul, inv_mul_cancel₀ hc, one_smul]

end CFSG.RankThree.GF2n.Stroth80.Classify
