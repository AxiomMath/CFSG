module

public import CFSG.Monster.B.E6.StdF4Cells
public import CFSG.Monster.B.E6.StdF4HeckeData

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical

@[expose] def ptIdx
    (w : NW) : Fin 24 := E6Folded.ι.symm (weylPerm w E6Folded.θΛ)

theorem ι_ptIdx
    (w : NW) : E6Folded.ι (ptIdx w) = weylPerm w E6Folded.θΛ :=
  Equiv.apply_symm_apply _ _

theorem ptIdx_mul_of_mem
    {w u : NW} (hu : u ∈ ncs.parabolic firstJ) : ptIdx (w * u) = ptIdx w := by
  rw [firstJ_eq_J] at hu
  rw [ptIdx, ptIdx, map_mul, Equiv.Perm.mul_apply,
    E6Folded.apply_θΛ_of_mem_WJ ((mem_parabolic_J_iff' u).1 hu)]

theorem val_ptIdx_simple_mul
    (i : Fin 4) (w : NW) :
    (ptIdx (ncs.simple i * w) : ℕ) = E6Folded.gidx i (ptIdx w) := by
  have h : weylPerm (ncs.simple i * w) E6Folded.θΛ = E6Folded.gen i (E6Folded.ι (ptIdx w)) := by
    rw [map_mul, weylPerm_simple, Equiv.Perm.mul_apply, ι_ptIdx]
  rw [E6Folded.gen_ι] at h
  rw [ptIdx, h, Equiv.symm_apply_apply]

theorem lidx_ptIdx_mul_of_mem
    {w u : NW} (hu : u ∈ ncs.parabolic firstJ) :
    lidx (ptIdx (u * w)) = lidx (ptIdx w) := by
  rw [firstJ_eq_J] at hu
  have h := E6Folded.level_apply_of_mem_WJ ((mem_parabolic_J_iff' u).1 hu)
    (weylPerm w E6Folded.θΛ)
  have e : weylPerm u (weylPerm w E6Folded.θΛ) = E6Folded.ι (ptIdx (u * w)) := by
    rw [ι_ptIdx, map_mul, Equiv.Perm.mul_apply]
  rw [e, ← ι_ptIdx w, E6Folded.form_θ_ι, E6Folded.form_θ_ι] at h
  rw [lidx, lidx, h]

theorem length_eq_certLength
    (w : NW) : ncs.length w = E6Folded.certLength (weylPerm w) := by
  rw [← wordLength_weylPerm, E6Folded.length_certificate.1 _ (mem_W_weylPerm w)]

theorem certLength_tElt {a : ℕ} (ha : a < 24) : E6Folded.certLength (E6Folded.tElt a) = plen a := by
  have h := E6Folded.certLength_eq ha (by norm_num : 0 < 48)
  rw [E6Folded.jElt_zero, mul_one, E6Folded.pairLength, E6Folded.jWords_zero] at h
  exact h

theorem exists_weylPerm_eq
    (w : NW) : ∃ i < 48,
    weylPerm w = E6Folded.tElt (ptIdx w) * E6Folded.jElt i ∧
      ncs.length w = plen (ptIdx w) + (E6Folded.jWords.getD i []).length := by
  obtain ⟨a, ha, i, hi, h⟩ := (E6Folded.mem_W_iff_elt _).1 (mem_W_weylPerm w)
  have hpt : (ptIdx w : ℕ) = a := by
    have e : weylPerm w E6Folded.θΛ = E6Folded.ι ⟨a, ha⟩ := by
      rw [h, E6Folded.elt_apply_θΛ ha hi]
    rw [ptIdx, e, Equiv.symm_apply_apply]
  refine ⟨i, hi, by rw [h, hpt], ?_⟩
  rw [length_eq_certLength, h, E6Folded.certLength_eq ha hi, E6Folded.pairLength, hpt, plen]

theorem plen_le_length
    (w : NW) : plen (ptIdx w) ≤ ncs.length w := by
  obtain ⟨i, -, -, h⟩ := exists_weylPerm_eq w
  omega

theorem weylPerm_surjective_W
    {v : Equiv.Perm E6Folded.Λ} (hv : v ∈ E6Folded.W) :
    ∃ u : NW, weylPerm u = v := by
  rw [← range_weylPerm] at hv
  exact hv

theorem weylPerm_eq_tElt_of_min
    {w : NW} (hw : ncs.IsMinimalCosetRep firstJ w) :
    weylPerm w = E6Folded.tElt (ptIdx w) ∧ ncs.length w = plen (ptIdx w) := by
  obtain ⟨i, hi, h, hl⟩ := exists_weylPerm_eq w
  obtain ⟨u, hu⟩ := weylPerm_surjective_W
    (E6Folded.WJ_le_W (inv_mem (E6Folded.jElt_mem hi)))
  have huJ : u ∈ ncs.parabolic firstJ := by
    rw [firstJ_eq_J, mem_parabolic_J_iff', hu]
    exact inv_mem (E6Folded.jElt_mem hi)
  have hle := ncs.length_mul_of_isMinimalCosetRep hw huJ
  have hwu : weylPerm (w * u) = E6Folded.tElt (ptIdx w) := by
    rw [map_mul, h, hu, mul_inv_cancel_right]
  rw [length_eq_certLength (w * u), hwu, certLength_tElt (ptIdx w).2, hl] at hle
  have h0 : (E6Folded.jWords.getD i []).length = 0 := by omega
  have hj : E6Folded.jElt i = 1 := by
    rw [E6Folded.jElt, List.length_eq_zero_iff.1 h0]
    rfl
  exact ⟨by rw [h, hj, mul_one], by rw [hl, h0, add_zero]⟩

@[expose] def rho
    (x y : stdChamber) : Fin 24 := ptIdx (stdDistance x y)

theorem rho_eq_of_mem_residue
    {x y y' : stdChamber}
    (h : y' ∈ residue ncs stdDistance firstJ y) : rho x y' = rho x y := by
  obtain ⟨v, hv, e⟩ := exists_dist_eq_mul_of_mem_residue hδ (x := x) h
  rw [rho, rho, e, ptIdx_mul_of_mem hv]

theorem lidx_rho_eq_of_mem_residue
    {x x' y : stdChamber}
    (h : x' ∈ residue ncs stdDistance firstJ x) : lidx (rho x' y) = lidx (rho x y) := by
  obtain ⟨u, hu, e⟩ := exists_dist_eq_mul_left_of_mem_residue hδ h y
  rw [rho, rho, e, lidx_ptIdx_mul_of_mem hu]

theorem rho_eq_23_iff
    (x y : stdChamber) :
    (rho x y : ℕ) = 23 ↔ y ∈ residue ncs stdDistance firstJ x := by
  rw [mem_residue_iff_mem_parabolic hδ, firstJ_eq_J, mem_parabolic_J_iff',
    E6Folded.mem_WJ_iff_stabilizer]
  have h23 : (rho x y : ℕ) = 23 ↔ weylPerm (stdDistance x y) E6Folded.θΛ = E6Folded.θΛ := by
    rw [rho, ptIdx]
    constructor
    · intro h
      have e : E6Folded.ι.symm (weylPerm (stdDistance x y) E6Folded.θΛ) = 23 := Fin.ext h
      rw [Equiv.symm_apply_eq, E6Folded.ι_23] at e
      exact e
    · intro h
      rw [h, ← E6Folded.ι_23, Equiv.symm_apply_apply]
      rfl
  rw [h23]
  exact ⟨fun h => ⟨mem_W_weylPerm _, h⟩, fun h => h.2⟩

theorem mem_panel_of_dist
    {a c : stdChamber} {i : Fin 4} (h : stdDistance a c = ncs.simple i) :
    c ∈ panel ncs stdDistance i a :=
  (mem_panel_iff hδ).2 (Or.inr h)

theorem rho_panel
    (a b : stdChamber) (i : Fin 4) :
    (E6Folded.gidx i (rho a b) = rho a b → ∀ c ∈ panel ncs stdDistance i a, rho c b = rho a b) ∧
    (E6Folded.gidx i (rho a b) ≠ rho a b →
      plen (E6Folded.gidx i (rho a b)) = plen (rho a b) + 1 →
      ∀ c ∈ panel ncs stdDistance i a, c ≠ a → (rho c b : ℕ) = E6Folded.gidx i (rho a b)) ∧
    (E6Folded.gidx i (rho a b) ≠ rho a b →
      plen (E6Folded.gidx i (rho a b)) + 1 = plen (rho a b) →
      ∃ c₀ ∈ panel ncs stdDistance i a, c₀ ≠ a ∧
        (rho c₀ b : ℕ) = E6Folded.gidx i (rho a b) ∧
        ∀ c ∈ panel ncs stdDistance i a, c ≠ a → c ≠ c₀ → rho c b = rho a b) := by
  obtain ⟨p, hp⟩ := exists_isProjection hδ firstJ b a
  set w := stdDistance a p with hw
  have hmin : ncs.IsMinimalCosetRep firstJ w := by
    refine isMinimalCosetRep_of_forall_le hδ hp.1 fun q hq => ?_
    by_cases h : q = p
    · rw [h]
    · exact (hp.2 q hq h).le
  obtain ⟨hwt, hlw⟩ := weylPerm_eq_tElt_of_min hmin
  have hrho : ∀ c, rho c b = ptIdx (stdDistance c p) := fun c =>
    (rho_eq_of_mem_residue hp.1).symm
  set γ := rho a b with hγ
  have hγw : γ = ptIdx w := hrho a
  have hgen : weylPerm (ncs.simple i * w) = E6Folded.gen i * E6Folded.tElt γ := by
    rw [map_mul, weylPerm_simple, hwt, ← hγw]
  have hsγ : (ptIdx (ncs.simple i * w) : ℕ) = E6Folded.gidx i γ := by
    rw [val_ptIdx_simple_mul, ← hγw]
  have hpa : stdDistance p a = w⁻¹ := dist_inv hδ a p
  have hlinv : ncs.length (w⁻¹ * ncs.simple i) = ncs.length (ncs.simple i * w) := by
    rw [← ncs.length_inv, mul_inv_rev, inv_inv, ncs.inv_simple]
  have hcp : ∀ c, stdDistance p c = w⁻¹ * ncs.simple i → stdDistance c p = ncs.simple i * w :=
    fun c h => by rw [dist_inv hδ p c, h, mul_inv_rev, inv_inv, ncs.inv_simple]
  rcases ncs.length_simple_mul w i with hA | hB
  ·
    have hnear : ∀ c ∈ panel ncs stdDistance i a, c ≠ a →
        (rho c b : ℕ) = E6Folded.gidx i γ := by
      intro c hc hne
      have hac := dist_eq_simple_of_mem_panel hδ hc hne
      have h := (hδ.mul_simple p a c i hac).2 (by rw [hpa, hlinv, hA, ← ncs.length_inv])
      rw [hpa] at h
      rw [hrho c, hcp c h, hsγ]
    have hplen : E6Folded.gidx i γ ≠ γ → plen (E6Folded.gidx i γ) = plen γ + 1 := by
      intro hne
      rcases E6Folded.gen_mul_tElt i γ.2 with ⟨h1, -⟩ | ⟨h2, -⟩
      · have e1 : ncs.length (ncs.simple i * w) = plen (E6Folded.gidx i γ) := by
          rw [length_eq_certLength, hgen, h1, certLength_tElt (E6Folded.gidx_lt i γ.2)]
        rw [← e1, hA, hlw, ← hγw]
      · exact absurd h2 hne
    refine ⟨fun hfix c hc => ?_, fun _ _ => hnear, fun hne hfar => ?_⟩
    · by_cases hca : c = a
      · rw [hca]
      · exact Fin.ext ((hnear c hc hca).trans hfix)
    · exfalso
      have := hplen hne
      omega
  ·
    obtain ⟨c₀, hac₀, hpc₀⟩ := hδ.exists_simple p a i
    rw [hpa] at hpc₀
    have hc₀ : c₀ ∈ panel ncs stdDistance i a := mem_panel_of_dist hac₀
    have hc₀a : c₀ ≠ a := fun h => by
      rw [h, (hδ.eq_one_iff a a).2 rfl] at hac₀
      exact ncs.simple_ne_one i hac₀.symm
    have hlγ : ncs.length w = plen γ := by rw [hlw, hγw]
    have hfar : ¬(E6Folded.gidx i γ = γ) ∧ plen (E6Folded.gidx i γ) + 1 = plen γ := by
      rcases E6Folded.gen_mul_tElt i γ.2 with ⟨h1, -⟩ | ⟨h2, -⟩
      · have hl : ncs.length (ncs.simple i * w) = plen (E6Folded.gidx i γ) := by
          rw [length_eq_certLength, hgen, h1, certLength_tElt (E6Folded.gidx_lt i γ.2)]
        refine ⟨fun h => ?_, by omega⟩
        rw [h] at hl
        omega
      · exfalso
        have hle := plen_le_length (ncs.simple i * w)
        rw [show (ptIdx (ncs.simple i * w)) = γ from Fin.ext (hsγ.trans h2)] at hle
        omega
    have hothers : ∀ c ∈ panel ncs stdDistance i a, c ≠ a → c ≠ c₀ → rho c b = γ := by
      intro c hc hca hcc₀
      have hc' : c ∈ panel ncs stdDistance i c₀ := by
        change c ∈ residue ncs stdDistance {i} c₀
        rw [residue_eq_of_mem hδ hc₀]
        exact hc
      have hc₀c := dist_eq_simple_of_mem_panel hδ hc' hcc₀
      have hlen : ncs.length (stdDistance p c₀ * ncs.simple i) =
          ncs.length (stdDistance p c₀) + 1 := by
        rw [hpc₀, mul_assoc, ncs.simple_mul_simple_self, mul_one, hlinv, ncs.length_inv]
        omega
      have h := (hδ.mul_simple p c₀ c i hc₀c).2 hlen
      rw [hpc₀, mul_assoc, ncs.simple_mul_simple_self, mul_one] at h
      rw [hrho c, dist_inv hδ p c, h, inv_inv, hγw]
    refine ⟨fun h => absurd h hfar.1, fun _ hn => ?_, fun _ _ => ⟨c₀, hc₀, hc₀a, ?_, hothers⟩⟩
    · exfalso
      have := hfar.2
      omega
    rw [hrho c₀, hcp c₀ hpc₀, hsγ]

end CFSG.Monster.B.E6.StdF4
