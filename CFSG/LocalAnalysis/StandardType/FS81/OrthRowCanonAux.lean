module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.StandardType.FS81.OrthMaxTorus
public import CFSG.LocalAnalysis.StandardType.FS81.RowFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCSub

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem maps_planeSpan_of_commute_rot {p : V × V} (hp : MinusPair Q p.1 p.2)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : Commute g (rot Q p.1 p.2)) :
    ∀ y ∈ planeSpan p, g y ∈ planeSpan p := by
  intro y hy
  obtain ⟨x, rfl⟩ := exists_rot_sub_eq hp hy
  have hgrot : g ((rot Q p.1 p.2) x) = (rot Q p.1 p.2) (g x) := by
    have h := congrArg (fun z : V ≃ₗ[ZMod 2] V => z x) hcomm.eq
    rwa [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  rw [map_sub, hgrot]
  exact rot_sub_mem_span hp (g x)

theorem exists_pow_of_commute_rot_of_plane {p : V × V} (hp : MinusPair Q p.1 p.2)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : Commute g (rot Q p.1 p.2))
    (hgP : ∀ y ∈ planeSpan p, g y ∈ planeSpan p) :
    ∃ k : ℕ, ∀ y ∈ planeSpan p, g y = ((rot Q p.1 p.2) ^ k) y := by
  obtain ⟨α, β, hαβ⟩ := (mem_planeSpan_iff p (g p.1)).1 (hgP p.1 (left_mem_planeSpan p))
  have hga : g p.1 = α • p.1 + β • p.2 := hαβ.symm
  have hgb : g p.2 = rot Q p.1 p.2 (g p.1) := by
    have h := congrArg (fun z : V ≃ₗ[ZMod 2] V => z p.1) hcomm.eq
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, rot_apply_left hp] at h
    exact h
  rcases zmod_two_cases α with rfl | rfl <;> rcases zmod_two_cases β with rfl | rfl
  · exfalso
    have h0 : g p.1 = 0 := by rw [hga, zero_smul, zero_smul, add_zero]
    have h1 : g p.1 = g 0 := by rw [h0, map_zero]
    have h2 : p.1 = 0 := g.injective h1
    exact hp.ne_zero_left h2
  · refine ⟨1, ?_⟩
    intro y hy
    obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p y).1 hy
    rw [map_add, map_smul, map_smul]
    have hg1 : g p.1 = p.2 := by rw [hga, zero_smul, zero_add, one_smul]
    have hg2 : g p.2 = p.1 + p.2 := by rw [hgb, hg1, rot_apply_right hp]
    rw [hg1, hg2, pow_one, map_add, map_smul, map_smul, rot_apply_left hp, rot_apply_right hp]
  · refine ⟨0, ?_⟩
    intro y hy
    obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p y).1 hy
    rw [map_add, map_smul, map_smul]
    have hg1 : g p.1 = p.1 := by rw [hga, one_smul, zero_smul, add_zero]
    have hg2 : g p.2 = p.2 := by rw [hgb, hg1, rot_apply_left hp]
    rw [hg1, hg2, pow_zero]
    simp
  · refine ⟨2, ?_⟩
    intro y hy
    obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p y).1 hy
    rw [map_add, map_smul, map_smul]
    have hg1 : g p.1 = p.1 + p.2 := by rw [hga, one_smul, one_smul]
    have hg2 : g p.2 = p.1 := by
      rw [hgb, hg1, map_add, rot_apply_left hp, rot_apply_right hp]
      rw [add_comm p.1 p.2, ← add_assoc, vec_add_self, zero_add]
    have hrot2 : (rot Q p.1 p.2) ((rot Q p.1 p.2) (c • p.1 + d • p.2)) =
        c • (p.1 + p.2) + d • p.1 := by
      rw [map_add, map_smul, map_smul]
      rw [rot_apply_left hp, rot_apply_right hp]
      simp only [map_add, map_smul]
      rw [rot_apply_left hp, rot_apply_right hp]
      have h : p.2 + (p.1 + p.2) = p.1 := by
        rw [add_comm p.1 p.2, ← add_assoc, vec_add_self, zero_add]
      rw [h]
    rw [hg1, hg2, pow_two, LinearEquiv.mul_apply, hrot2]

theorem centralizer_torus_le_of_commute_rot {l : List (V × V)} (hl : IsFrame Q l)
    {c : V ≃ₗ[ZMod 2] V} (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ p ∈ l, Commute c (rot Q p.1 p.2)) :
    ∃ t ∈ torus Q l, ∀ y ∈ Wspan l, c y = t y := by
  induction l with
  | nil =>
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    intro y hy
    rw [Wspan_nil, Submodule.mem_bot] at hy
    rw [hy, map_zero]
    simp
  | cons p l ih =>
    obtain ⟨hp, hperp, hl'⟩ := isFrame_cons.1 hl
    have hcomm_p : Commute c (rot Q p.1 p.2) := hcomm p (List.mem_cons_self)
    have hcomm_l' : ∀ q ∈ l, Commute c (rot Q q.1 q.2) := fun q hq =>
      hcomm q (List.mem_cons_of_mem _ hq)
    have hcP : ∀ y ∈ planeSpan p, c y ∈ planeSpan p :=
      maps_planeSpan_of_commute_rot hp hc hcomm_p
    obtain ⟨k, hk⟩ := exists_pow_of_commute_rot_of_plane hp hc hcomm_p hcP
    obtain ⟨t', ht'mem, ht'⟩ := ih hl' hcomm_l'
    refine ⟨(rot Q p.1 p.2)^k * t', ?_, ?_⟩
    · rw [torus_cons]
      exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k) ht'mem
    · intro y hy
      rw [Wspan_cons] at hy
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add, LinearEquiv.mul_apply, map_add, map_add]
      rw [hk u hu, ht' v hv]
      have htu : t' u = u := by
        apply torus_fixes hl' (x := u) _ t' ht'mem
        intro q hq
        have hpq := hperp q hq
        obtain ⟨c1, c2, hc12⟩ := (mem_planeSpan_iff p u).1 hu
        rw [← hc12]
        constructor
        · rw [polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
            hpq.1, hpq.2.2.1]
          simp
        · rw [polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
            hpq.2.1, hpq.2.2.2]
          simp
      rw [htu]
      have hrot_fix : ∀ n : ℕ, ((rot Q p.1 p.2) ^ n) (t' v) = t' v := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ, LinearEquiv.mul_apply]
          have ht'v_mem : t' v ∈ Wspan l := by
            apply map_mem_Wspan_of_commute hl' (g := t')
            · intro q hq
              exact torus_commute hl' ht'mem (rot_mem_torus hq)
            · exact hv
          have hperp_p : polar Q (t' v) p.1 = 0 ∧ polar Q (t' v) p.2 = 0 := by
            obtain ⟨h1, h2⟩ := polar_Wspan_eq_zero hperp ht'v_mem
            exact ⟨by rw [polar_comm, h1], by rw [polar_comm, h2]⟩
          rw [rot_apply_of_perp hp hperp_p.1 hperp_p.2]
          exact ih
      rw [hrot_fix k]

theorem centralizer_torus_eq_self_of_frame {l : List (V × V)} (hl : IsFrame Q l)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hfull : finrank (ZMod 2) V = 2 * l.length) :
    Subgroup.centralizer (torus Q l : Set (V ≃ₗ[ZMod 2] V)) ⊓
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      torus Q l := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hc_cent, hc_comm⟩ := hc
    have hc_orth : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self _ hc_comm
    have hcomm : ∀ p ∈ l, Commute c (rot Q p.1 p.2) := fun p hp =>
      (Subgroup.mem_centralizer_iff.mp hc_cent _ (rot_mem_torus hp)).symm
    obtain ⟨t, ht_mem, ht_eq⟩ := centralizer_torus_le_of_commute_rot hl hc_orth hcomm
    have hfin : finrank (ZMod 2) (Wspan l) = finrank (ZMod 2) V := by
      rw [IsFrame.finrank_Wspan hl, hfull]
    have htop : Wspan l = ⊤ := Submodule.eq_top_of_finrank_eq hfin
    have hct : c = t := by
      apply LinearEquiv.ext
      intro y
      exact ht_eq y (by rw [htop]; exact Submodule.mem_top)
    rw [hct]
    exact ht_mem
  · intro c hc
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (torus_commute hl hc ht).eq.symm
    · exact torus_le_commutator hl hc

end CFSG.StandardType.FrameRoute.FS81

end
