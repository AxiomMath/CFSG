module

public import CFSG.Quasithin.H13.AS91Sec5Eltr

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem G12_transitive {a b : G ⧸ c.G1} (ha : a ∈ c.ptsL) (hb : b ∈ c.ptsL)
    (hax : a ≠ c.x0) (hbx : b ≠ c.x0) :
    ∃ g ∈ c.G1 ⊓ c.G2, g • a = b := by
  obtain ⟨e, he, heb⟩ := c.E_transitive ha hb hax hbx
  exact ⟨e, Subgroup.mem_inf.mpr ⟨c.E_le_G1 he, c.E_le_G2 he⟩, heb⟩

theorem relIndex_stab {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) (hyx : y ≠ c.x0) :
    (c.G1 ⊓ c.G2 ⊓ stabilizer G y).relIndex (c.G1 ⊓ c.G2) = 4 := by
  let H : Subgroup G := c.G1 ⊓ c.G2
  have hH1 : H ≤ c.G1 := inf_le_left
  have hH2 : H ≤ c.G2 := inf_le_right
  have horb : MulAction.orbit ↥H y = c.ptsL \ {c.x0} := by
    ext p
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨smul_mem_objOf_base (hH2 h.2) hy, fun hpx => ?_⟩
      have hx : (h : G) • c.x0 = c.x0 := by
        have hmem : (h : G) ∈ stabilizer G c.x0 := by
          rw [c.stab_x0]
          exact hH1 h.2
        exact mem_stabilizer_iff.mp hmem
      exact hyx (smul_left_cancel (h : G) (hpx.trans hx.symm))
    · rintro ⟨hp, hpx⟩
      obtain ⟨g, hg, hgp⟩ := c.G12_transitive hp hy hpx hyx
      refine ⟨⟨g⁻¹, inv_mem hg⟩, ?_⟩
      show g⁻¹ • y = p
      rw [inv_smul_eq_iff]
      exact hgp.symm
  have hstab : MulAction.stabilizer ↥H y = (H ⊓ stabilizer G y).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      and_iff_right h.2]
    exact Iff.rfl
  calc (H ⊓ stabilizer G y).relIndex H
      = ((H ⊓ stabilizer G y).subgroupOf H).index := rfl
    _ = (MulAction.stabilizer ↥H y).index := by rw [hstab]
    _ = (MulAction.orbit ↥H y).ncard := MulAction.index_stabilizer ↥H y
    _ = 4 := by
      rw [horb, Set.ncard_sdiff_singleton_of_mem c.x0_mem_ptsL, ← Nat.card_coe_set_eq,
        c.card_ptsL]

theorem K_le_G12_stab {y : G ⧸ c.G1} (hy : y ∈ c.ptsL) :
    c.K ≤ c.G1 ⊓ c.G2 ⊓ stabilizer G y :=
  le_inf (le_inf c.K_le_G1 c.K_le_G2) (c.K_le_stab hy)

theorem relIndex_K_G12 : c.K.relIndex (c.G1 ⊓ c.G2) = 24 := by
  classical
  let X0 : ↥c.ptsL := ⟨c.x0, c.x0_mem_ptsL⟩
  let ρ : ↥(c.G1 ⊓ c.G2) →* Equiv.Perm ↥c.ptsL :=
    (residuePerm c.G1 c.G2).comp (Subgroup.inclusion (inf_le_right : c.G1 ⊓ c.G2 ≤ c.G2))
  have hρ : ∀ (m : ↥(c.G1 ⊓ c.G2)) (p : ↥c.ptsL),
      ((ρ m p : ↥c.ptsL) : G ⧸ c.G1) = (m : G) • (p : G ⧸ c.G1) := fun m p =>
    residuePerm_apply c.G1 c.G2 (Subgroup.inclusion inf_le_right m) p
  have hker : ρ.ker = c.K.subgroupOf (c.G1 ⊓ c.G2) := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hm
      refine (c.kernel_ptsL m m.2.2).mp fun p hp => ?_
      have h := congrArg (fun f : Equiv.Perm ↥c.ptsL =>
        ((f ⟨p, hp⟩ : ↥c.ptsL) : G ⧸ c.G1)) hm
      simpa only [Equiv.Perm.coe_one, id_eq] using hρ m ⟨p, hp⟩ ▸ h
    · intro hk
      apply Equiv.Perm.ext
      intro p
      apply Subtype.ext
      change (((ρ m) p : ↥c.ptsL) : G ⧸ c.G1) = ((p : ↥c.ptsL) : G ⧸ c.G1)
      rw [hρ m p]
      exact c.K_fix hk p.2
  have hrange : ρ.range = MulAction.stabilizer (Equiv.Perm ↥c.ptsL) X0 := by
    ext σ
    rw [MonoidHom.mem_range, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨m, rfl⟩
      change (ρ m) X0 = X0
      apply Subtype.ext
      change (((ρ m) X0 : ↥c.ptsL) : G ⧸ c.G1) = ((X0 : ↥c.ptsL) : G ⧸ c.G1)
      rw [hρ m X0]
      have hm : (m : G) ∈ stabilizer G c.x0 := by
        rw [c.stab_x0]
        exact m.2.1
      show (m : G) • c.x0 = c.x0
      exact mem_stabilizer_iff.mp hm
    · intro hσ
      obtain ⟨s, hsCZ, hs⟩ := c.exists_CZ_perm σ
      have hσ' : σ X0 = X0 := by
        simpa only [Equiv.Perm.smul_def] using hσ
      have hsx : s • c.x0 = c.x0 := by
        have := hs X0
        rw [hσ'] at this
        exact this
      have hsG1 : s ∈ c.G1 := by
        have hmem : s ∈ stabilizer G c.x0 := mem_stabilizer_iff.mpr hsx
        rwa [c.stab_x0] at hmem
      refine ⟨⟨s, Subgroup.mem_inf.mpr ⟨hsG1, c.CZ_le_G2 hsCZ⟩⟩, ?_⟩
      apply Equiv.Perm.ext
      intro p
      apply Subtype.ext
      change (((ρ ⟨s, _⟩) p : ↥c.ptsL) : G ⧸ c.G1) = ((σ p : ↥c.ptsL) : G ⧸ c.G1)
      rw [hρ]
      exact hs p
  have hpts : Nat.card ↥c.ptsL = 5 := c.card_ptsL
  have hindex : (MulAction.stabilizer (Equiv.Perm ↥c.ptsL) X0).index = 5 := by
    rw [MulAction.index_stabilizer_of_transitive, hpts]
  have hcardperm : Nat.card (Equiv.Perm ↥c.ptsL) = 120 := by
    rw [Nat.card_perm, hpts]
    norm_num [Nat.factorial]
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer (Equiv.Perm ↥c.ptsL) X0)
  rw [hindex, hcardperm] at hmul
  have hcardstab : Nat.card (MulAction.stabilizer (Equiv.Perm ↥c.ptsL) X0) = 24 := by
    omega
  have hindexK : (c.K.subgroupOf (c.G1 ⊓ c.G2)).index = 24 := by
    rw [← hker, Subgroup.index_ker, hrange]
    exact hcardstab
  exact hindexK

theorem exists_eq_stab_of_relIndex_four {U : Subgroup G}
    (hU : U ≤ c.G1 ⊓ c.G2) (hKU : c.K ≤ U)
    (hidx : U.relIndex (c.G1 ⊓ c.G2) = 4) :
    ∃ y ∈ c.ptsL, y ≠ c.x0 ∧ U = c.G1 ⊓ c.G2 ⊓ stabilizer G y := by
  classical
  have hKU6 : c.K.relIndex U = 6 := by
    have h := Subgroup.relIndex_mul_relIndex c.K U (c.G1 ⊓ c.G2) hKU hU
    rw [c.relIndex_K_G12, hidx] at h
    omega
  let Ω : Set (G ⧸ c.G1) := {p | p ∈ c.ptsL ∧ p ≠ c.x0}
  have hΩcard : Ω.ncard = 4 := by
    have hΩ : Ω = c.ptsL \ {c.x0} := by
      ext p
      simp [Ω]
    rw [hΩ, Set.ncard_sdiff_singleton_of_mem c.x0_mem_ptsL, ← Nat.card_coe_set_eq,
      c.card_ptsL]
  have hU1 : U ≤ c.G1 := hU.trans inf_le_left
  have hU2 : U ≤ c.G2 := hU.trans inf_le_right
  have hfixx0 : ∀ u ∈ U, u • c.x0 = c.x0 := by
    intro u hu
    have hm : u ∈ stabilizer G c.x0 := by
      rw [c.stab_x0]
      exact hU1 hu
    exact mem_stabilizer_iff.mp hm
  have hsubΩ : ∀ p ∈ Ω, MulAction.orbit ↥U p ⊆ Ω := by
    intro p hp q hq
    obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.mp hq
    refine ⟨smul_mem_objOf_base (hU2 u.2) hp.1, fun h => hp.2 ?_⟩
    exact smul_left_cancel (u : G)
      (show (u : G) • p = (u : G) • c.x0 from h.trans (hfixx0 u u.2).symm)
  have hstabU : ∀ p : G ⧸ c.G1, MulAction.stabilizer ↥U p =
      (U ⊓ stabilizer G p).subgroupOf U := by
    intro p
    ext u
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      and_iff_right u.2]
    exact Iff.rfl
  have horbindex : ∀ p : G ⧸ c.G1,
      (MulAction.orbit ↥U p).ncard = (U ⊓ stabilizer G p).relIndex U := by
    intro p
    rw [← MulAction.index_stabilizer ↥U p, hstabU p]
    rfl
  have horbdvd : ∀ p ∈ Ω, (MulAction.orbit ↥U p).ncard ∣ 6 := by
    intro p hp
    have hKstab : c.K.subgroupOf U ≤ MulAction.stabilizer ↥U p := by
      intro k hk
      rw [Subgroup.mem_subgroupOf] at hk
      rw [MulAction.mem_stabilizer_iff]
      exact c.K_fix hk hp.1
    have h := Subgroup.index_dvd_of_le hKstab
    rw [show (MulAction.orbit ↥U p).ncard = (MulAction.stabilizer ↥U p).index from
      (MulAction.index_stabilizer ↥U p).symm]
    rwa [show (c.K.subgroupOf U).index = 6 from hKU6] at h
  by_cases hfix : ∃ y ∈ Ω, ∀ u ∈ U, u • y = y
  · obtain ⟨y, hy, hyfix⟩ := hfix
    have hUle : U ≤ c.G1 ⊓ c.G2 ⊓ stabilizer G y :=
      le_inf hU (fun u hu => mem_stabilizer_iff.mpr (hyfix u hu))
    have hVle : c.G1 ⊓ c.G2 ⊓ stabilizer G y ≤ c.G1 ⊓ c.G2 := inf_le_left
    have hmul := Subgroup.relIndex_mul_relIndex U
      (c.G1 ⊓ c.G2 ⊓ stabilizer G y) (c.G1 ⊓ c.G2) hUle hVle
    rw [hidx, c.relIndex_stab hy.1 hy.2] at hmul
    have hone : U.relIndex (c.G1 ⊓ c.G2 ⊓ stabilizer G y) = 1 := by omega
    exact ⟨y, hy.1, hy.2, le_antisymm hUle (Subgroup.relIndex_eq_one.mp hone)⟩
  · exfalso
    push Not at hfix
    have hge2 : ∀ p ∈ Ω, 2 ≤ (MulAction.orbit ↥U p).ncard := by
      intro p hp
      by_contra h
      push Not at h
      have hpos : 0 < (MulAction.orbit ↥U p).ncard := by
        rw [Set.ncard_pos]
        exact ⟨p, by simpa using MulAction.mem_orbit p (1 : ↥U)⟩
      have hone : (MulAction.orbit ↥U p).ncard = 1 := by omega
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hone
      obtain ⟨u, hu, hup⟩ := hfix p hp
      have hp_mem : p ∈ MulAction.orbit ↥U p := by
        simpa using MulAction.mem_orbit p (1 : ↥U)
      have hpa : p = a := by
        rw [ha] at hp_mem
        simpa using hp_mem
      have hup_mem : (⟨u, hu⟩ : ↥U) • p ∈ MulAction.orbit ↥U p :=
        MulAction.mem_orbit p (⟨u, hu⟩ : ↥U)
      rw [ha] at hup_mem
      have hupa : u • p = a := by simpa using hup_mem
      exact hup (hupa.trans hpa.symm)
    obtain ⟨p, hpΩ⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hΩcard]; norm_num)
    have hle4 : (MulAction.orbit ↥U p).ncard ≤ 4 := by
      rw [← hΩcard]
      exact Set.ncard_le_ncard (hsubΩ p hpΩ)
    have hge2p := hge2 p hpΩ
    have hdvd := horbdvd p hpΩ
    have hn23 : (MulAction.orbit ↥U p).ncard = 2 ∨
        (MulAction.orbit ↥U p).ncard = 3 := by
      interval_cases h : (MulAction.orbit ↥U p).ncard
      · exact Or.inl rfl
      · exact Or.inr rfl
      · norm_num at hdvd
    rcases hn23 with hn | hn3
    ·
      obtain ⟨q, hqO, hqp⟩ :=
        Set.exists_ne_of_one_lt_ncard (by omega : 1 < (MulAction.orbit ↥U p).ncard) p
      have hqΩ : q ∈ Ω := hsubΩ p hpΩ hqO
      have hpair : ({p, q} : Set (G ⧸ c.G1)).ncard = 2 := Set.ncard_pair hqp.symm
      have hOsub : ({p, q} : Set (G ⧸ c.G1)) ⊆ MulAction.orbit ↥U p := by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · simpa using MulAction.mem_orbit p (1 : ↥U)
        · rw [Set.mem_singleton_iff] at hz
          subst hz
          exact hqO
      have hOeq : MulAction.orbit ↥U p = {p, q} := by
        have h := Set.eq_of_subset_of_ncard_le hOsub (by rw [hn, hpair])
        exact h.symm
      have hcomp : (Ω \ MulAction.orbit ↥U p).ncard = 2 := by
        rw [Set.ncard_sdiff (hsubΩ p hpΩ), hΩcard, hn]
      obtain ⟨p', hp'Ω, hp'O⟩ : ∃ p' ∈ Ω, p' ∉ MulAction.orbit ↥U p := by
        obtain ⟨p', hp'⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hcomp]; norm_num)
        exact ⟨p', hp'.1, hp'.2⟩
      have hO'sub : MulAction.orbit ↥U p' ⊆ Ω \ MulAction.orbit ↥U p := by
        intro z hz
        refine ⟨hsubΩ p' hp'Ω hz, ?_⟩
        intro hzO
        obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.mp hz
        have hmem : u • p' ∈ MulAction.orbit ↥U p := hzO
        have h1 : u⁻¹ • (u • p') ∈ MulAction.orbit ↥U p := by
          have := Set.smul_mem_smul_set (a := u⁻¹) hmem
          rwa [MulAction.smul_orbit u⁻¹ p] at this
        exact hp'O (by simpa using h1)
      have hn' : (MulAction.orbit ↥U p').ncard = 2 := by
        have hle : (MulAction.orbit ↥U p').ncard ≤ 2 := by
          rw [← hcomp]
          exact Set.ncard_le_ncard hO'sub
        have := hge2 p' hp'Ω
        omega
      obtain ⟨q', hq'O', hq'p'⟩ :=
        Set.exists_ne_of_one_lt_ncard (by omega : 1 < (MulAction.orbit ↥U p').ncard) p'
      have hq'Ω : q' ∈ Ω := hO'sub hq'O' |>.1
      have hpair' : ({p', q'} : Set (G ⧸ c.G1)).ncard = 2 := Set.ncard_pair hq'p'.symm
      have hO'subset : ({p', q'} : Set (G ⧸ c.G1)) ⊆ MulAction.orbit ↥U p' := by
        intro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · simpa using MulAction.mem_orbit p' (1 : ↥U)
        · rw [Set.mem_singleton_iff] at hz
          subst hz
          exact hq'O'
      have hO'eq : MulAction.orbit ↥U p' = {p', q'} := by
        have h := Set.eq_of_subset_of_ncard_le hO'subset (by rw [hn', hpair'])
        exact h.symm
      have hp_index : (U ⊓ stabilizer G p).relIndex U = 2 := by
        rw [← horbindex p]
        exact hn
      have hp'_index : (U ⊓ stabilizer G p').relIndex U = 2 := by
        rw [← horbindex p']
        exact hn'
      let V : Subgroup G := (U ⊓ stabilizer G p) ⊓ (U ⊓ stabilizer G p')
      have hVindex : V.relIndex U ≤ 4 := by
        have h := Subgroup.relIndex_inf_le (H := U ⊓ stabilizer G p)
          (K := U ⊓ stabilizer G p') (L := U)
        calc V.relIndex U =
              ((U ⊓ stabilizer G p) ⊓ (U ⊓ stabilizer G p')).relIndex U := rfl
          _ ≤ (U ⊓ stabilizer G p).relIndex U *
              (U ⊓ stabilizer G p').relIndex U := h
          _ = 4 := by rw [hp_index, hp'_index]
      have hVU : V ≤ U := le_trans inf_le_left inf_le_left
      have hVp : V ≤ stabilizer G p := le_trans inf_le_left inf_le_right
      have hVp' : V ≤ stabilizer G p' := le_trans inf_le_right inf_le_right
      have hfixp : ∀ v ∈ V, v • p = p := fun v hv =>
        mem_stabilizer_iff.mp (hVp hv)
      have hfixp' : ∀ v ∈ V, v • p' = p' := fun v hv =>
        mem_stabilizer_iff.mp (hVp' hv)
      have hfixq : ∀ v ∈ V, v • q = q := by
        intro v hv
        have hvU : v ∈ U := hVU hv
        have hvqO : v • q ∈ MulAction.orbit ↥U p := by
          have := Set.smul_mem_smul_set (a := (⟨v, hvU⟩ : ↥U)) hqO
          rwa [MulAction.smul_orbit (⟨v, hvU⟩ : ↥U) p] at this
        rw [hOeq, Set.mem_insert_iff, Set.mem_singleton_iff] at hvqO
        rcases hvqO with h | h
        · exfalso
          have hpp : v • p = p := hfixp v hv
          exact hqp (smul_left_cancel v (h.trans hpp.symm))
        · exact h
      have hfixq' : ∀ v ∈ V, v • q' = q' := by
        intro v hv
        have hvU : v ∈ U := hVU hv
        have hvqO : v • q' ∈ MulAction.orbit ↥U p' := by
          have := Set.smul_mem_smul_set (a := (⟨v, hvU⟩ : ↥U)) hq'O'
          rwa [MulAction.smul_orbit (⟨v, hvU⟩ : ↥U) p'] at this
        rw [hO'eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hvqO
        rcases hvqO with h | h
        · exfalso
          have hpp : v • p' = p' := hfixp' v hv
          exact hq'p' (smul_left_cancel v (h.trans hpp.symm))
        · exact h
      have hdisj : Disjoint (MulAction.orbit ↥U p) (MulAction.orbit ↥U p') := by
        rw [Set.disjoint_left]
        intro z hz hz'
        exact (hO'sub hz').2 hz
      have hunion_card : (MulAction.orbit ↥U p ∪ MulAction.orbit ↥U p').ncard = 4 := by
        rw [Set.ncard_union_eq hdisj, hn, hn']
      have hΩunion : Ω = MulAction.orbit ↥U p ∪ MulAction.orbit ↥U p' := by
        have hunion_sub : (MulAction.orbit ↥U p ∪ MulAction.orbit ↥U p') ⊆ Ω := by
          intro z hz
          rw [Set.mem_union] at hz
          rcases hz with h | h
          · exact hsubΩ p hpΩ h
          · exact hsubΩ p' hp'Ω h
        have h := Set.eq_of_subset_of_ncard_le hunion_sub
          (by rw [hΩcard, hunion_card])
        exact h.symm
      have hVfix : ∀ z ∈ c.ptsL, ∀ v ∈ V, v • z = z := by
        intro z hz v hv
        by_cases hzx : z = c.x0
        · rw [hzx]
          exact hfixx0 v (hVU hv)
        · have hzΩ : z ∈ Ω := ⟨hz, hzx⟩
          rw [hΩunion] at hzΩ
          rw [Set.mem_union] at hzΩ
          rcases hzΩ with hzO | hzO'
          · rw [hOeq] at hzO
            rcases Set.mem_insert_iff.mp hzO with rfl | hzq
            · exact hfixp v hv
            · rw [Set.mem_singleton_iff] at hzq
              subst hzq
              exact hfixq v hv
          · rw [hO'eq] at hzO'
            rcases Set.mem_insert_iff.mp hzO' with rfl | hzq
            · exact hfixp' v hv
            · rw [Set.mem_singleton_iff] at hzq
              subst hzq
              exact hfixq' v hv
      have hVK : V ≤ c.K := by
        intro v hv
        exact (c.kernel_ptsL v (hU2 (hVU hv))).mp fun z hz => hVfix z hz v hv
      have hle : V.subgroupOf U ≤ c.K.subgroupOf U := by
        intro v hv
        rw [Subgroup.mem_subgroupOf] at hv ⊢
        exact hVK hv
      have hdvd : 6 ∣ V.relIndex U := by
        have h := Subgroup.index_dvd_of_le hle
        rwa [show (c.K.subgroupOf U).index = 6 from hKU6] at h
      have hpos : 0 < V.relIndex U := by
        rw [Subgroup.relIndex]
        exact Nat.card_pos
      have := Nat.le_of_dvd hpos hdvd
      omega
    ·
      have hcomp3 : (Ω \ MulAction.orbit ↥U p).ncard = 1 := by
        rw [Set.ncard_sdiff (hsubΩ p hpΩ), hΩcard, hn3]
      obtain ⟨q, hq⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hcomp3]; norm_num)
      have hqΩ : q ∈ Ω := hq.1
      have hqO : q ∉ MulAction.orbit ↥U p := hq.2
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hcomp3
      have hqa : q = a := by
        have : q ∈ ({a} : Set (G ⧸ c.G1)) := by
          rw [← ha]
          exact ⟨hqΩ, hqO⟩
        simpa using this
      have hcomp_eq : Ω \ MulAction.orbit ↥U p = {q} := by
        rw [ha, ← hqa]
      have hfixq : ∀ u ∈ U, u • q = q := by
        intro u hu
        have huqΩ : u • q ∈ Ω := hsubΩ q hqΩ (MulAction.mem_orbit q (⟨u, hu⟩ : ↥U))
        have huqO : u • q ∉ MulAction.orbit ↥U p := by
          intro h
          apply hqO
          have h1 : (⟨u, hu⟩ : ↥U)⁻¹ • ((⟨u, hu⟩ : ↥U) • q) ∈
              MulAction.orbit ↥U p := by
            have := Set.smul_mem_smul_set (a := (⟨u, hu⟩ : ↥U)⁻¹) h
            rwa [MulAction.smul_orbit (⟨u, hu⟩ : ↥U)⁻¹ p] at this
          rw [inv_smul_smul] at h1
          exact h1
        have hmem : u • q ∈ ({q} : Set (G ⧸ c.G1)) := by
          rw [← hcomp_eq]
          exact ⟨huqΩ, huqO⟩
        simpa using hmem
      obtain ⟨u, hu, huq⟩ := hfix q hqΩ
      exact huq (hfixq u hu)

theorem inf_stab_eq_of_lineU {y : G ⧸ c.G1}
    (h : c.G1 ⊓ stabilizer G y ≤ c.G2) :
    c.G1 ⊓ stabilizer G y = c.G1 ⊓ c.G2 ⊓ stabilizer G y := by
  calc c.G1 ⊓ stabilizer G y = (c.G1 ⊓ stabilizer G y) ⊓ c.G2 :=
        (inf_eq_left.mpr h).symm
    _ = c.G1 ⊓ c.G2 ⊓ stabilizer G y := by ac_rfl

theorem map_conj_G1 {e : G} (he : e ∈ c.E) :
    c.G1.map (MulAut.conj e).toMonoidHom = c.G1 := by
  have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer (c.E_le_G1 he))
  change c.G1.map (↑(MulAut.conj e)) = c.G1 at h
  exact h

theorem map_conj_G2 {e : G} (he : e ∈ c.E) :
    c.G2.map (MulAut.conj e).toMonoidHom = c.G2 := by
  have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer (c.E_le_G2 he))
  change c.G2.map (↑(MulAut.conj e)) = c.G2 at h
  exact h

theorem map_conj_G31 {e : G} (he : e ∈ c.E) :
    (c.G3 ⊓ c.G1).map (MulAut.conj e).toMonoidHom = c.G3 ⊓ c.G1 := by
  have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer (Subgroup.mem_inf.mpr ⟨c.E_le_G3 he, c.E_le_G1 he⟩))
  change (c.G3 ⊓ c.G1).map (↑(MulAut.conj e)) = c.G3 ⊓ c.G1 at h
  exact h

theorem conj_inf_stab {e : G} (he : e ∈ c.E) {p : G ⧸ c.G1} (hp : p ∈ c.ptsL) :
    (c.G1 ⊓ c.G2 ⊓ stabilizer G p).map (MulAut.conj e).toMonoidHom =
        c.G1 ⊓ c.G2 ⊓ stabilizer G (e • p) ∧
      c.G1.map (MulAut.conj e).toMonoidHom = c.G1 ∧
      c.G2.map (MulAut.conj e).toMonoidHom = c.G2 ∧
      (c.G3 ⊓ c.G1).map (MulAut.conj e).toMonoidHom = c.G3 ⊓ c.G1 := by
  have hinj : Function.Injective (MulAut.conj e).toMonoidHom := (MulAut.conj e).injective
  refine ⟨?_, c.map_conj_G1 he, c.map_conj_G2 he, c.map_conj_G31 he⟩
  rw [Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_inf_eq _ _ _ hinj,
    c.map_conj_G1 he, c.map_conj_G2 he,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj e p]

end Loc49

end CFSG.Quasithin.H13.AS91
