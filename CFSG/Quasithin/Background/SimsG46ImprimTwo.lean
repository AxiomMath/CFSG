module

public import CFSG.Quasithin.Background.SimsG4Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import CFSG.Quasithin.Background.SimsG46ImprimPerm
import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

namespace G46Imprim

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem transv_not_disjoint_map [FiniteDimensional F V] {d : V ≃ₗ[F] V} (hd : IsTransv d)
    {U : Submodule F V} (hU : 2 ≤ Module.finrank F U)
    (hdisj : Disjoint U (U.map (d : V →ₗ[F] V))) : False := by
  obtain ⟨h1, -⟩ := hd
  have hinj : Function.Injective (((d : V →ₗ[F] V) - LinearMap.id) ∘ₗ U.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hdx : d (x : V) = x := by
      simpa [sub_eq_zero] using hx
    have hmem : (x : V) ∈ U.map (d : V →ₗ[F] V) := by
      rw [← hdx]
      exact Submodule.mem_map_of_mem x.2
    exact Subtype.ext (Submodule.disjoint_def.mp hdisj x x.2 hmem)
  have h2 := LinearMap.finrank_range_of_inj hinj
  have h3 := Submodule.finrank_mono
    (LinearMap.range_comp_le_range U.subtype ((d : V →ₗ[F] V) - LinearMap.id))
  omega

theorem transv_centralizes_of_invariant (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {d : V ≃ₗ[F] V} (hdSp : d ∈ spGroup B)
    (hd : IsTransv d) {U₀ U₁ : Submodule F V} (hdisj : Disjoint U₀ U₁)
    (h₀ : ∀ x ∈ U₀, d x ∈ U₀) (h₁ : ∀ x ∈ U₁, d x ∈ U₁) :
    (∀ x ∈ U₀, d x = x) ∨ ∀ x ∈ U₁, d x = x := by
  obtain ⟨u, hu, c, hc, hform, -⟩ := SimsG45.exists_transv_form B halt hnd d hdSp hd.1
  have key : ∀ U : Submodule F V, (∀ x ∈ U, d x ∈ U) → ∀ x ∈ U, d x ≠ x → u ∈ U := by
    intro U hU x hx hne
    have hcoef : c * B x u ≠ 0 := by
      intro h0
      apply hne
      rw [hform x, h0, zero_smul, add_zero]
    have h1 : (c * B x u) • u ∈ U := by
      have heq : (c * B x u) • u = d x - x := by
        rw [hform x]
        abel
      rw [heq]
      exact U.sub_mem (hU x hx) hx
    have h2 := U.smul_mem (c * B x u)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at h2
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x₀, hx₀, hne₀⟩, ⟨x₁, hx₁, hne₁⟩⟩ := hcon
  exact hu (Submodule.disjoint_def.mp hdisj u (key U₀ h₀ x₀ hx₀ hne₀) (key U₁ h₁ x₁ hx₁ hne₁))

theorem not_connected_of_two_summands (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty) {W : Fin 2 → Submodule F V} (hne : ∀ i, W i ≠ ⊥)
    (hind : iSupIndep W) (htop : (⨆ i, W i) = ⊤)
    (hmap : ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j)
    (hW2 : ∀ i, Module.finrank F (W i) = 2) : ¬ (advGraph G₀).Connected := by
  haveI : FiniteDimensional F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  have hWinj := summand_injective hne hind
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hfin2 : ∀ i : Fin 2, i ≠ 0 → i = 1 := by decide
  have hdisj : Disjoint (W 0) (W 1) := hind.pairwiseDisjoint h01
  have htop' : W 0 ⊔ W 1 = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hfix0 : ∀ d ∈ transvSet G₀, sumPerm W d 0 = 0 := by
    intro d hd
    by_contra h
    apply transv_not_disjoint_map hd.2 (U := W 0) (le_of_eq (hW2 0).symm)
    rw [map_sumPerm hmap hd.1, hfin2 _ h]
    exact hdisj
  have hfix1 : ∀ d ∈ transvSet G₀, sumPerm W d 1 = 1 := by
    intro d hd
    apply hfin2
    intro h
    exact h01 (sumPerm_injective hWinj hmap hd.1 (h.trans (hfix0 d hd).symm)).symm
  have hpres : ∀ d ∈ transvSet G₀, (∀ x ∈ W 0, d x ∈ W 0) ∧ ∀ x ∈ W 1, d x ∈ W 1 := by
    intro d hd
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have hdx := apply_mem_sumPerm hmap hd.1 hx
      rwa [hfix0 d hd] at hdx
    · have hdx := apply_mem_sumPerm hmap hd.1 hx
      rwa [hfix1 d hd] at hdx
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ G₀, sumPerm W g 0 = 1 := by
    by_contra hcon
    push Not at hcon
    have hinv : ∀ g ∈ G₀, ∀ w ∈ W 0, g w ∈ W 0 := by
      intro g hg w hw
      have hgw := apply_mem_sumPerm hmap hg hw
      have h0 : sumPerm W g 0 = 0 := by
        by_contra h
        exact hcon g hg (hfin2 _ h)
      rwa [h0] at hgw
    rcases hirr (W 0) hinv with h | h
    · exact hne 0 h
    · apply hne 1
      rw [h, top_disjoint] at hdisj
      exact hdisj
  have hg1 : sumPerm W g 1 = 0 := by
    by_contra h
    exact h01 (sumPerm_injective hWinj hmap hg (hg0.trans (hfin2 _ h).symm))
  refine not_connected_of_two_blocks hdisj htop' hD hpres (fun d hd => ?_) hg (fun x hx => ?_)
    (fun x hx => ?_)
  · exact transv_centralizes_of_invariant B halt hnd (hSp hd.1) hd.2 hdisj (hpres d hd).1
      (hpres d hd).2
  · have hgx := apply_mem_sumPerm hmap hg hx
    rwa [hg0] at hgx
  · have hgx := apply_mem_sumPerm hmap hg hx
    rwa [hg1] at hgx

end G46Imprim

end CFSG.Quasithin.SimsG4
