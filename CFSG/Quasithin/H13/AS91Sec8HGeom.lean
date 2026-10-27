module

public import CFSG.Quasithin.H13.AS91Sec5PlaneCount
public import CFSG.Quasithin.H13.AS91Sec7Smul
public import CFSG.GroupTheory.MulEquivTransport

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem mem_nbrP_of_mem_ptsL {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0) :
    y ∈ c.nbrP := by
  have hl0 : c.OnL c.x0 c.l0 := cInc_mk c.G1 c.G2 1
  have hl0P : c.LnP c.l0 c.pi0 := cInc_mk c.G2 c.G3 1
  exact ⟨c.inc_pt_plane hy hl0P, c.adj_of_onL (Ne.symm hyx) hl0 hy⟩

variable {G' : Type} [Group G'] [Finite G'] {z' : G'} (c' : Loc49 G' z')

theorem exists_mulEquiv_sylow_thompson (ζ₀ : ↥c.G3 ≃* ↥c'.G3) :
    ∃ ζ : ↥c.G3 ≃* ↥c'.G3,
      (c.T.subgroupOf c.G3).map ζ.toMonoidHom = c'.T.subgroupOf c'.G3 ∧
      (c.E.subgroupOf c.G3).map ζ.toMonoidHom = c'.E.subgroupOf c'.G3 ∧
      (c.G1.subgroupOf c.G3).map ζ.toMonoidHom = c'.G1.subgroupOf c'.G3 := by
  classical
  have hT3 : (c.T : Subgroup G) ≤ c.G3 := c.T_le.trans c.G13_le
  have hT3' : (c'.T : Subgroup G') ≤ c'.G3 := c'.T_le.trans c'.G13_le
  let P : Sylow 2 ↥c.G3 := c.T.comapOfInjective c.G3.subtype c.G3.subtype_injective
    (by rwa [Subgroup.range_subtype])
  let Q : Sylow 2 ↥c'.G3 := c'.T.comapOfInjective c'.G3.subtype c'.G3.subtype_injective
    (by rwa [Subgroup.range_subtype])
  have hsurj : Function.Surjective ⇑ζ₀.toMonoidHom := ζ₀.surjective
  let P' : Sylow 2 ↥c'.G3 := Sylow.mapSurjective (f := ζ₀.toMonoidHom) hsurj P
  have hpre := Sylow.isPretransitive_of_finite (p := 2) (G := ↥c'.G3)
  obtain ⟨i', hi'⟩ := hpre.exists_smul_eq P' Q
  have hP : (↑P : Subgroup ↥c.G3) = c.T.subgroupOf c.G3 := by
    rw [Sylow.coe_comapOfInjective]
    rfl
  have hQ : (↑Q : Subgroup ↥c'.G3) = c'.T.subgroupOf c'.G3 := by
    rw [Sylow.coe_comapOfInjective]
    rfl
  have hP' : (↑P' : Subgroup ↥c'.G3) = (c.T.subgroupOf c.G3).map ζ₀.toMonoidHom := by
    change (↑(Sylow.mapSurjective (f := ζ₀.toMonoidHom) hsurj P) :
      Subgroup ↥c'.G3) = _
    rw [Sylow.coe_mapSurjective, hP]
  have hconj : (↑P' : Subgroup ↥c'.G3).map
      (MulDistribMulAction.toMonoidHom (↥c'.G3) (MulAut.conj i')) =
      c'.T.subgroupOf c'.G3 := by
    have h := congrArg (fun S : Sylow 2 ↥c'.G3 => (S : Subgroup ↥c'.G3)) hi'
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    rw [hQ] at h
    simpa using h
  have hT : (c.T.subgroupOf c.G3).map (ζ₀.trans (MulAut.conj i')).toMonoidHom =
      c'.T.subgroupOf c'.G3 := by
    have h := hconj
    rw [hP'] at h
    rw [Subgroup.map_map] at h
    rw [show (MulDistribMulAction.toMonoidHom (↥c'.G3) (MulAut.conj i')).comp ζ₀.toMonoidHom =
      (ζ₀.trans (MulAut.conj i')).toMonoidHom from rfl] at h
    exact h
  have hEsub : CFSG.ambientMaxCardThompson (c.T.subgroupOf c.G3) = c.E.subgroupOf c.G3 := by
    apply Subgroup.map_injective c.G3.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le c.E_le_G3]
    rw [CFSG.map_ambientMaxCardThompson_of_injective c.G3.subtype (c.T.subgroupOf c.G3)
      (fun x y h => Subtype.ext (by simpa using h))]
    rw [Subgroup.map_subgroupOf_eq_of_le hT3]
    exact c.E_eq.symm
  have hE : (c.E.subgroupOf c.G3).map (ζ₀.trans (MulAut.conj i')).toMonoidHom =
      c'.E.subgroupOf c'.G3 := by
    apply Subgroup.map_injective c'.G3.subtype_injective
    rw [Subgroup.map_map, ← hEsub]
    rw [CFSG.map_ambientMaxCardThompson_of_injective
      (c'.G3.subtype.comp (ζ₀.trans (MulAut.conj i')).toMonoidHom) (c.T.subgroupOf c.G3)
      (fun x y h => Subtype.ext (by simpa using h))]
    rw [Subgroup.map_subgroupOf_eq_of_le c'.E_le_G3]
    rw [show (c.T.subgroupOf c.G3).map
        (c'.G3.subtype.comp (ζ₀.trans (MulAut.conj i')).toMonoidHom) = c'.T from by
      rw [← Subgroup.map_map, hT, Subgroup.map_subgroupOf_eq_of_le hT3']]
    exact c'.E_eq.symm
  refine ⟨ζ₀.trans (MulAut.conj i'), hT, hE, ?_⟩
  have hnorm : Subgroup.normalizer (c.E.subgroupOf c.G3) = c.G1.subgroupOf c.G3 := by
    rw [← Subgroup.subgroupOf_normalizer_eq (H := c.E) (N := c.G3) c.E_le_G3]
  have hnorm' : Subgroup.normalizer (c'.E.subgroupOf c'.G3) = c'.G1.subgroupOf c'.G3 := by
    rw [← Subgroup.subgroupOf_normalizer_eq (H := c'.E) (N := c'.G3) c'.E_le_G3]
  rw [← hnorm, Subgroup.map_equiv_normalizer_eq (c.E.subgroupOf c.G3)
    (ζ₀.trans (MulAut.conj i')), hE]
  exact hnorm'

end Loc49

theorem Loc49.ncard_nbrP {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)
    (ρ : ResM24 c)
    (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z) :
    c.nbrP.ncard = 60 := by
  simpa [Loc49.nbrP, Loc49.ptsP, objOf, CInc] using ρ.ncard_adj_onP hLU hG2 hJ c.x0_mem_ptsP

theorem Loc49.ncard_ptsP {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)
    (ρ : ResM24 c)
    (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z) :
    c.ptsP.ncard = 77 := by
  simpa [Loc49.ptsP, objOf, CInc] using ρ.ncard_onP hLU hG2 hJ c.pi0

theorem Loc49.orbit_subgroupOf_G1_eq_nbrP {G : Type} [Group G] [Finite G] {z : G}
    (c : Loc49 G z) (hG2 : Stmt5_Gamma2) (hJ : HypJ4 G z) {y : G ⧸ c.G1}
    (hy : y ∈ c.nbrP) :
    MulAction.orbit ↥(c.G1.subgroupOf c.G3) y = c.nbrP := by
  apply Set.Subset.antisymm
  · intro b hb
    obtain ⟨i, rfl⟩ := hb
    change i • y ∈ c.nbrP
    rw [Subgroup.smul_def (S := c.G1.subgroupOf c.G3), Subgroup.smul_def (S := c.G3)]
    have hiG1 : ((i : ↥c.G3) : G) ∈ c.G1 := i.2
    have hiG3 : ((i : ↥c.G3) : G) ∈ c.G3 := (i : ↥c.G3).2
    have hfix : ((i : ↥c.G3) : G) • c.x0 = c.x0 := c.smul_x0_of_mem hiG1
    have hfixP : ((i : ↥c.G3) : G) • c.pi0 = c.pi0 := c.G3_smul_pi0 hiG3
    refine ⟨?_, ?_⟩
    · have h := (c.onP_smul_iff ((i : ↥c.G3) : G)).mpr hy.1
      rwa [hfixP] at h
    · have h := (c.adj_smul_iff ((i : ↥c.G3) : G)).mpr hy.2
      rwa [hfix] at h
  · intro b hb
    obtain ⟨g, hg, hgy⟩ := (stmt5_3_1u_of_gamma2 hG2) G z hJ c y hy b hb
    let i : ↥(c.G1.subgroupOf c.G3) := ⟨⟨g, (Subgroup.mem_inf.mp hg).2⟩, by
      rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_inf.mp hg).1⟩
    refine ⟨i, ?_⟩
    change i • y = b
    rw [Subgroup.smul_def (S := c.G1.subgroupOf c.G3), Subgroup.smul_def (S := c.G3)]
    simpa [i] using hgy

namespace Loc49

theorem exists_stmt8_3_of_mulEquiv (hLU : Stmt5_LineU) (hG2 : Stmt5_Gamma2)
    {G : Type} [Group G] [Finite G] {z : G}
    (hJ : HypJ4 G z) (c : Loc49 G z) (ρ : ResM24 c)
    {G' : Type} [Group G'] [Finite G'] {z' : G'} (hJ' : HypJ4 G' z') (c' : Loc49 G' z')
    (ρ' : ResM24 c') (ζ₀ : ↥c.G3 ≃* ↥c'.G3)
    {y : G ⧸ c.G1} {y' : G' ⧸ c'.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0)
    (hy' : y' ∈ c'.ptsL) (hyx' : y' ≠ c'.x0) :
    ∃ ζ : ↥c.G3 ≃* ↥c'.G3,
      ((stabilizer G c.x0).subgroupOf c.G3).map ζ.toMonoidHom =
        (stabilizer G' c'.x0).subgroupOf c'.G3 ∧
      ((stabilizer G ({c.x0, y} : Set (G ⧸ c.G1))).subgroupOf c.G3).map ζ.toMonoidHom =
        (stabilizer G' ({c'.x0, y'} : Set (G' ⧸ c'.G1))).subgroupOf c'.G3 := by
  classical
  obtain ⟨ζ₁, hT₁, hE₁, hI₁⟩ := c.exists_mulEquiv_sylow_thompson c' ζ₀
  have hstab : (MulAction.stabilizer ↥c.G3 c.x0).map ζ₁.toMonoidHom =
      MulAction.stabilizer ↥c'.G3 c'.x0 := by
    rw [← MulAction.stabilizer_subgroupOf c.G3 c.x0,
      ← MulAction.stabilizer_subgroupOf c'.G3 c'.x0, c.stab_x0, c'.stab_x0]
    exact hI₁
  let Φ : ↥(MulAction.orbit ↥c.G3 c.x0) ≃ ↥(MulAction.orbit ↥c'.G3 c'.x0) :=
    orbitEquivOfStabilizerMap ζ₁ c.x0 c'.x0 hstab
  let Φα : G ⧸ c.G1 → G' ⧸ c'.G1 := fun a =>
    if h : a ∈ MulAction.orbit ↥c.G3 c.x0 then (Φ ⟨a, h⟩ : G' ⧸ c'.G1) else c'.x0
  have hΦα_of_mem : ∀ {a : G ⧸ c.G1} (ha : a ∈ MulAction.orbit ↥c.G3 c.x0),
      Φα a = (Φ ⟨a, ha⟩ : G' ⧸ c'.G1) := by
    intro a ha
    simp [Φα, ha]
  have hΦα_x0 : Φα c.x0 = c'.x0 := by
    rw [hΦα_of_mem (MulAction.mem_orbit_self c.x0)]
    exact congrArg Subtype.val (orbitEquivOfStabilizerMap_self ζ₁ c.x0 c'.x0 hstab)
  have hΦα_smul : ∀ (g : ↥c.G3) {a : G ⧸ c.G1}, a ∈ MulAction.orbit ↥c.G3 c.x0 →
      Φα (g • a) = ζ₁ g • Φα a := by
    intro g a ha
    have hga : g • a ∈ MulAction.orbit ↥c.G3 c.x0 := by
      obtain ⟨h, rfl⟩ := ha
      simpa [mul_smul] using MulAction.mem_orbit c.x0 (g * h)
    rw [hΦα_of_mem hga, hΦα_of_mem ha]
    have hsub : (⟨g • a, hga⟩ : ↥(MulAction.orbit ↥c.G3 c.x0)) = g • ⟨a, ha⟩ :=
      Subtype.ext rfl
    rw [hsub]
    simpa using congrArg Subtype.val
      (orbitEquivOfStabilizerMap_smul ζ₁ c.x0 c'.x0 hstab g ⟨a, ha⟩)
  have hinj : Set.InjOn Φα (MulAction.orbit ↥c.G3 c.x0) := by
    intro a ha b hb hab
    rw [hΦα_of_mem ha, hΦα_of_mem hb] at hab
    exact congrArg Subtype.val (Φ.injective (Subtype.ext hab))
  have hyP : y ∈ c.nbrP := c.mem_nbrP_of_mem_ptsL hy hyx
  have hyOrb : y ∈ MulAction.orbit ↥c.G3 c.x0 := by
    rw [← c.ptsP_eq_orbit]
    exact hyP.1
  have hy'P : y' ∈ c'.nbrP := c'.mem_nbrP_of_mem_ptsL hy' hyx'
  have hy'Orb : y' ∈ MulAction.orbit ↥c'.G3 c'.x0 := by
    rw [← c'.ptsP_eq_orbit]
    exact hy'P.1
  let y'' : ↥(MulAction.orbit ↥c'.G3 c'.x0) := Φ ⟨y, hyOrb⟩
  have hΦα_y : Φα y = (y'' : G' ⧸ c'.G1) := hΦα_of_mem hyOrb
  have horb : MulAction.orbit ↥(c.G1.subgroupOf c.G3) y = c.nbrP :=
    c.orbit_subgroupOf_G1_eq_nbrP hG2 hJ hyP
  have hsub : MulAction.orbit ↥(c.G1.subgroupOf c.G3) y ⊆
      MulAction.orbit ↥c.G3 c.x0 := by
    rw [horb]
    intro a ha
    rw [← c.ptsP_eq_orbit]
    exact ha.1
  have himage : Φα '' MulAction.orbit ↥(c.G1.subgroupOf c.G3) y =
      MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) (y'' : G' ⧸ c'.G1) := by
    have h := image_orbit_of_map_eq ζ₁ Φα (a := c.x0) (y := y)
      (K := c.G1.subgroupOf c.G3) (L := c'.G1.subgroupOf c'.G3) hI₁ hΦα_smul hinj hyOrb
    rwa [hΦα_y] at h
  have hOcard : (MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) (y'' : G' ⧸ c'.G1)).ncard = 60 := by
    rw [← himage, Set.InjOn.ncard_image (hinj.mono hsub), horb]
    exact c.ncard_nbrP ρ hLU hG2 hJ
  have hOsub : MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) (y'' : G' ⧸ c'.G1) ⊆
      c'.ptsP \ {c'.x0} := by
    rw [← himage]
    rintro z ⟨a, ha, rfl⟩
    have ha' : a ∈ MulAction.orbit ↥c.G3 c.x0 := hsub ha
    refine ⟨?_, ?_⟩
    · change Φα a ∈ {b : G' ⧸ c'.G1 | c'.OnP b c'.pi0}
      rw [c'.ptsP_eq_orbit, hΦα_of_mem ha']
      exact (Φ ⟨a, ha'⟩).2
    · intro hz
      have hx0orb : c.x0 ∈ MulAction.orbit ↥c.G3 c.x0 := MulAction.mem_orbit_self c.x0
      have hax : a = c.x0 := hinj ha' hx0orb (hz.trans hΦα_x0.symm)
      have hmem : a ∈ c.nbrP := by rw [← horb]; exact ha
      exact hmem.2.1 hax.symm
  have horb' : MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) y' = c'.nbrP :=
    c'.orbit_subgroupOf_G1_eq_nbrP hG2 hJ' hy'P
  have hNsub : c'.nbrP ⊆ c'.ptsP \ {c'.x0} := by
    intro z hz
    exact ⟨hz.1, fun h => hz.2.1 h.symm⟩
  have hNcard : c'.nbrP.ncard = 60 := c'.ncard_nbrP ρ' hLU hG2 hJ'
  have h76 : (c'.ptsP \ {c'.x0}).ncard = 76 := by
    rw [Set.ncard_sdiff_singleton_of_mem c'.x0_mem_ptsP, c'.ncard_ptsP ρ' hLU hG2 hJ']
  have hinter : (MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) (y'' : G' ⧸ c'.G1) ∩
      c'.nbrP).Nonempty := by
    let O : Set (G' ⧸ c'.G1) :=
      MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) (y'' : G' ⧸ c'.G1)
    let N : Set (G' ⧸ c'.G1) := c'.nbrP
    let U : Set (G' ⧸ c'.G1) := c'.ptsP \ {c'.x0}
    have hOU : O ⊆ U := hOsub
    have hNU : N ⊆ U := hNsub
    have hOc : O.ncard = 60 := hOcard
    have hNc : N.ncard = 60 := hNcard
    have hUc : U.ncard = 76 := h76
    let O' : Set ↥U := {x | (x : G' ⧸ c'.G1) ∈ O}
    let N' : Set ↥U := {x | (x : G' ⧸ c'.G1) ∈ N}
    have hO' : O'.ncard = O.ncard := by
      refine Set.ncard_congr (fun x _ => (x : G' ⧸ c'.G1)) (fun x hx => hx) ?_ ?_
      · exact fun x y _ _ hxy => Subtype.ext hxy
      · intro b hb
        exact ⟨⟨b, hOU hb⟩, hb, rfl⟩
    have hN' : N'.ncard = N.ncard := by
      refine Set.ncard_congr (fun x _ => (x : G' ⧸ c'.G1)) (fun x hx => hx) ?_ ?_
      · exact fun x y _ _ hxy => Subtype.ext hxy
      · intro b hb
        exact ⟨⟨b, hNU hb⟩, hb, rfl⟩
    have hcard : Nat.card ↥U = U.ncard := Nat.card_coe_set_eq U
    have hlt : Nat.card ↥U < O'.ncard + N'.ncard := by
      rw [hcard, hO', hN', hUc, hOc, hNc]
      norm_num
    obtain ⟨x, hx⟩ := Set.nonempty_inter_of_lt_ncard_add_ncard hlt
    have hnon : (O ∩ N).Nonempty := ⟨x.1, hx.1, hx.2⟩
    simpa [O, N] using hnon
  obtain ⟨z, hzO, hzN⟩ := hinter
  have hzy' : z ∈ MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) y' := by
    rw [horb']
    exact hzN
  have heq : MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) (y'' : G' ⧸ c'.G1) =
      MulAction.orbit ↥(c'.G1.subgroupOf c'.G3) y' := by
    rw [← MulAction.orbit_eq_iff.mpr hzO, MulAction.orbit_eq_iff.mpr hzy']
  obtain ⟨i', hi'⟩ : ∃ i' : ↥(c'.G1.subgroupOf c'.G3),
      i' • (y'' : G' ⧸ c'.G1) = y' := MulAction.orbit_eq_iff.mp heq.symm
  let ζ : ↥c.G3 ≃* ↥c'.G3 := ζ₁.trans (MulAut.conj (i' : ↥c'.G3))
  have hζ1 : ((stabilizer G c.x0).subgroupOf c.G3).map ζ.toMonoidHom =
      (stabilizer G' c'.x0).subgroupOf c'.G3 := by
    rw [c.stab_x0, c'.stab_x0]
    rw [show ζ.toMonoidHom =
      ((MulAut.conj (i' : ↥c'.G3) : ↥c'.G3 →* ↥c'.G3)).comp ζ₁.toMonoidHom from rfl]
    rw [← Subgroup.map_map, hI₁]
    change (c'.G1.subgroupOf c'.G3).map
      ((MulDistribMulAction.toMonoidEnd (MulAut ↥c'.G3) ↥c'.G3)
        (MulAut.conj (i' : ↥c'.G3))) = c'.G1.subgroupOf c'.G3
    rw [← Subgroup.pointwise_smul_def]
    exact Subgroup.conj_smul_eq_self_of_mem (H := c'.G1.subgroupOf c'.G3) i'.2
  let Ψα : G ⧸ c.G1 → G' ⧸ c'.G1 := fun a => (i' : ↥c'.G3) • Φα a
  have hΨα_smul : ∀ (g : ↥c.G3) {a : G ⧸ c.G1}, a ∈ MulAction.orbit ↥c.G3 c.x0 →
      Ψα (g • a) = ζ g • Ψα a := by
    intro g a ha
    have h1 : Ψα (g • a) = (i' : ↥c'.G3) • (ζ₁ g • Φα a) := by
      simp only [Ψα]
      rw [hΦα_smul g ha]
    rw [h1]
    show (i' : ↥c'.G3) • (ζ₁ g • Φα a) = ζ g • ((i' : ↥c'.G3) • Φα a)
    rw [MulEquiv.trans_apply, MulAut.conj_apply, mul_smul, inv_smul_smul, mul_smul]
  have hinjΨ : Set.InjOn Ψα (MulAction.orbit ↥c.G3 c.x0) := by
    intro a ha b hb hab
    apply hinj ha hb
    exact smul_left_cancel (i' : ↥c'.G3) hab
  have hΨ_x0 : Ψα c.x0 = c'.x0 := by
    show (i' : ↥c'.G3) • Φα c.x0 = c'.x0
    rw [hΦα_x0, Subgroup.smul_def]
    exact c'.smul_x0_of_mem (Subgroup.mem_subgroupOf.mp i'.2)
  have hΨ_y : Ψα y = y' := by
    show (i' : ↥c'.G3) • Φα y = y'
    rw [hΦα_y, ← Subgroup.smul_def]
    exact hi'
  have hS : ({c.x0, y} : Set (G ⧸ c.G1)) ⊆ MulAction.orbit ↥c.G3 c.x0 := by
    intro a ha
    rcases ha with rfl | rfl
    · exact MulAction.mem_orbit_self c.x0
    · exact hyOrb
  have hpair : (MulAction.stabilizer ↥c.G3 ({c.x0, y} : Set (G ⧸ c.G1))).map ζ.toMonoidHom =
      MulAction.stabilizer ↥c'.G3 ({c'.x0, y'} : Set (G' ⧸ c'.G1)) := by
    have h := map_stabilizer_eq_of_equivariantOn ζ Ψα c.x0 hΨα_smul hinjΨ
      ({c.x0, y} : Set (G ⧸ c.G1)) hS
    rwa [Set.image_pair, hΨ_x0, hΨ_y] at h
  refine ⟨ζ, hζ1, ?_⟩
  rw [MulAction.stabilizer_subgroupOf c.G3 ({c.x0, y} : Set (G ⧸ c.G1)),
    MulAction.stabilizer_subgroupOf c'.G3 ({c'.x0, y'} : Set (G' ⧸ c'.G1))]
  exact hpair

end Loc49

end CFSG.Quasithin.H13.AS91
