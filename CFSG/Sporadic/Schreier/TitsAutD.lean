module

public import CFSG.Sporadic.Schreier.TitsGraphAut
public import CFSG.Sporadic.Schreier.TitsInv

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.LieType.Chevalley CFSG.ComponentClassification.OuterAutomorphisms

theorem titsD_conj_mem
    {a d : Equiv.Perm (Fin 1755)} (ha : a ∈ titsA) (hd : d ∈ titsD) :
    a * d * a⁻¹ ∈ titsD := by
  have := titsD_normal_A.conj_mem ⟨d, titsD_le_titsA hd⟩ hd ⟨a, ha⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa using this

@[expose] def titsConj : titsA →* MulAut titsD where
  toFun a :=
    { toFun := fun d => ⟨(a : Equiv.Perm (Fin 1755)) * d * (a : Equiv.Perm (Fin 1755))⁻¹,
        titsD_conj_mem a.2 d.2⟩
      invFun := fun d => ⟨(a : Equiv.Perm (Fin 1755))⁻¹ * d * a, by
        simpa using titsD_conj_mem (inv_mem a.2) d.2⟩
      left_inv := fun d => Subtype.ext (by simp [mul_assoc])
      right_inv := fun d => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun d e => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun d => Subtype.ext (by simp)
  map_mul' := fun a b => MulEquiv.ext fun d => Subtype.ext (by simp [mul_assoc])

theorem coe_titsConj_apply (a : titsA) (d : titsD) :
    ((titsConj a d : titsD) : Equiv.Perm (Fin 1755)) =
      (a : Equiv.Perm (Fin 1755)) * d * (a : Equiv.Perm (Fin 1755))⁻¹ :=
  rfl

theorem titsConj_injective :
    Function.Injective titsConj := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hcomm : ∀ d ∈ titsD, (a : Equiv.Perm (Fin 1755)) * d = d * a := by
    intro d hd
    have := congrArg Subtype.val (MulEquiv.congr_fun ha ⟨d, hd⟩)
    rw [coe_titsConj_apply] at this
    simpa [mul_inv_eq_iff_eq_mul] using this
  have hsq : (a : Equiv.Perm (Fin 1755)) ^ 2 = 1 := by
    have hD : (a ^ 2 : titsA) ∈ titsD.subgroupOf titsA := Subgroup.sq_mem_of_index_two titsD_index a
    rw [Subgroup.mem_subgroupOf] at hD
    have hcen : (⟨(a : Equiv.Perm (Fin 1755)) ^ 2, by simpa using hD⟩ : titsD) ∈
        Subgroup.center titsD := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul, sq]
      calc (g : Equiv.Perm (Fin 1755)) * ((a : Equiv.Perm (Fin 1755)) * a)
          = (g * a) * a := (mul_assoc _ _ _).symm
        _ = (a * g) * a := by rw [← hcomm g g.2]
        _ = a * (g * a) := mul_assoc _ _ _
        _ = a * (a * g) := by rw [← hcomm g g.2]
        _ = (a * a) * g := (mul_assoc _ _ _).symm
    rw [titsD_center, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  by_cases h1 : (a : Equiv.Perm (Fin 1755)) = 1
  · exact Subtype.ext h1
  · have hinv : orderOf (a : Equiv.Perm (Fin 1755)) = 2 := orderOf_eq_prime hsq h1
    have haD := titsA_involution_mem_D a.2 hinv
    have hcen : (⟨a, haD⟩ : titsD) ∈ Subgroup.center titsD := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2).symm
    rw [titsD_center, Subgroup.mem_bot] at hcen
    exact Subtype.ext (show (a : Equiv.Perm (Fin 1755)) = 1 from
      congrArg (fun u : titsD => (u : Equiv.Perm (Fin 1755))) hcen)

theorem map_titsConj_titsD :
    (titsD.subgroupOf titsA).map titsConj = inner titsD := by
  ext φ
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : (a : Equiv.Perm (Fin 1755)) ∈ titsD := ha
    refine ⟨⟨a, ha'⟩, MulEquiv.ext fun d => ?_⟩
    rfl
  · rintro ⟨d, rfl⟩
    refine ⟨⟨d, titsD_le_titsA d.2⟩, d.2, MulEquiv.ext fun e => ?_⟩
    rfl

@[expose] def titsDStab (x : Fin 1755) : Subgroup (Equiv.Perm (Fin 1755)) :=
  titsD ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1755)) x

theorem mem_titsDStab {x : Fin 1755} {g : Equiv.Perm (Fin 1755)} :
    g ∈ titsDStab x ↔ g ∈ titsD ∧ g x = x := by
  rw [titsDStab, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

theorem titsDStab_zero :
    titsDStab 0 = titsH := by
  ext g
  rw [mem_titsDStab, mem_titsH_iff]

theorem image_orbit_titsDStab {π : Equiv.Perm (Fin 1755)}
    (hπ : ∀ g, g ∈ titsD ↔ π * g * π⁻¹ ∈ titsD) (x y : Fin 1755) :
    π '' MulAction.orbit (titsDStab x) y = MulAction.orbit (titsDStab (π x)) (π y) := by
  ext w
  constructor
  · rintro ⟨_, ⟨⟨g, hg⟩, rfl⟩, rfl⟩
    obtain ⟨hgD, hgx⟩ := mem_titsDStab.1 hg
    refine ⟨⟨π * g * π⁻¹, mem_titsDStab.2 ⟨(hπ g).1 hgD, ?_⟩⟩, ?_⟩
    · simp [Equiv.Perm.mul_apply, hgx]
    · show (π * g * π⁻¹) (π y) = π (g y)
      simp [Equiv.Perm.mul_apply]
  · rintro ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨hhD, hhx⟩ := mem_titsDStab.1 hh
    have hg : π⁻¹ * h * π ∈ titsD := by
      rw [hπ]
      simpa [mul_assoc] using hhD
    refine ⟨(π⁻¹ * h * π) y, ⟨⟨π⁻¹ * h * π, mem_titsDStab.2 ⟨hg, ?_⟩⟩, rfl⟩, ?_⟩
    · simp only [Equiv.Perm.mul_apply, hhx, perm_inv_apply]
    · show π ((π⁻¹ * h * π) y) = h (π y)
      simp [Equiv.Perm.mul_apply]

theorem ncard_orbit_titsDStab {π : Equiv.Perm (Fin 1755)}
    (hπ : ∀ g, g ∈ titsD ↔ π * g * π⁻¹ ∈ titsD) (x y : Fin 1755) :
    (MulAction.orbit (titsDStab (π x)) (π y)).ncard = (MulAction.orbit (titsDStab x) y).ncard := by
  rw [← image_orbit_titsDStab hπ, Set.ncard_image_of_injective _ π.injective]

theorem titsD_normalizes {d : Equiv.Perm (Fin 1755)} (hd : d ∈ titsD) :
    ∀ g, g ∈ titsD ↔ d * g * d⁻¹ ∈ titsD := by
  intro g
  constructor
  · intro hg
    exact mul_mem (mul_mem hd hg) (inv_mem hd)
  · intro h
    have := mul_mem (mul_mem (inv_mem hd) h) hd
    simpa [mul_assoc] using this

theorem titsH0_le_titsH :
    titsH0 ≤ titsH := by
  intro g hg
  exact mem_titsH_iff.2 ⟨titsH0_le_titsD hg, titsH0_fix g hg⟩

theorem titsH_le_titsGraphAut :
    titsH ≤ titsGraphAut := by
  rw [titsGraphAut_eq]
  exact titsH_le_titsD.trans titsD_le_titsA

theorem orbit_titsH_of_adj
    {y : Fin 1755} (hy : titsPointGraph.Adj 0 y) :
    MulAction.orbit titsH y = titsPointGraph.neighborSet 0 := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    have h := (titsH_le_titsGraphAut g.2 0 y).2 hy
    rw [(mem_titsH_iff.1 g.2).2] at h
    exact h
  · have hy' : y ∈ MulAction.orbit titsH0 (1 : Fin 1755) := by
      rw [← neighborSet_zero]
      exact hy
    rw [neighborSet_zero, ← MulAction.orbit_eq_iff.2 hy']
    rintro _ ⟨g, rfl⟩
    exact ⟨⟨g, titsH0_le_titsH g.2⟩, rfl⟩

theorem titsH0Reps_zero : (finPt 1755 titsH0Reps[0]! : Fin 1755) = 0 := by
  decide

theorem titsH0Reps_one : (finPt 1755 titsH0Reps[1]! : Fin 1755) = 1 := by
  decide

theorem adj_zero_iff_ncard
    {y : Fin 1755} :
    titsPointGraph.Adj 0 y ↔ (MulAction.orbit titsH y).ncard = 10 := by
  constructor
  · intro hy
    rw [orbit_titsH_of_adj hy, ncard_neighborSet]
  · intro h
    obtain ⟨c, hc, hyc⟩ := titsH0_orbit_cover y
    have hsub : MulAction.orbit titsH0 y ⊆ MulAction.orbit titsH y := by
      rintro _ ⟨g, rfl⟩
      exact ⟨⟨g, titsH0_le_titsH g.2⟩, rfl⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [h, MulAction.orbit_eq_iff.2 hyc, titsH0_orbit_ncard hc] at hle
    interval_cases c
    · exfalso
      rw [titsH0Reps_zero] at hyc
      have h1 : (MulAction.orbit titsH0 (0 : Fin 1755)).ncard = 1 := by
        have := titsH0_orbit_ncard (c := 0) (by norm_num)
        rwa [titsH0Reps_zero] at this
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
      have h0 : (0 : Fin 1755) ∈ MulAction.orbit titsH0 (0 : Fin 1755) :=
        MulAction.mem_orbit_self _
      rw [ha] at hyc h0
      have hy : y = 0 := (Set.mem_singleton_iff.1 hyc).trans (Set.mem_singleton_iff.1 h0).symm
      subst hy
      have : MulAction.orbit titsH (0 : Fin 1755) = {0} := by
        ext w
        simp only [Set.mem_singleton_iff]
        constructor
        · rintro ⟨g, rfl⟩
          exact (mem_titsH_iff.1 g.2).2
        · rintro rfl
          exact MulAction.mem_orbit_self _
      rw [this, Set.ncard_singleton] at h
      exact absurd h (by norm_num)
    · rw [titsH0Reps_one, ← neighborSet_zero] at hyc
      exact hyc
    all_goals exact absurd hle (by simp [titsStabSizes])

theorem adj_iff_ncard_orbit
    (x y : Fin 1755) :
    titsPointGraph.Adj x y ↔ (MulAction.orbit (titsDStab x) y).ncard = 10 := by
  obtain ⟨g, hg⟩ := titsDPoint_transitive x
  have hg0 : (g : Equiv.Perm (Fin 1755)) 0 = x := hg
  have hgA : (g : Equiv.Perm (Fin 1755)) ∈ titsGraphAut := by
    rw [titsGraphAut_eq]
    exact titsD_le_titsA g.2
  have e1 : titsPointGraph.Adj x y ↔ titsPointGraph.Adj 0 ((g : Equiv.Perm (Fin 1755))⁻¹ y) := by
    rw [← hgA 0, hg0, perm_apply_inv]
  have e2 := ncard_orbit_titsDStab (titsD_normalizes g.2) 0 ((g : Equiv.Perm (Fin 1755))⁻¹ y)
  rw [hg0, perm_apply_inv, titsDStab_zero] at e2
  rw [e1, adj_zero_iff_ncard, e2]

theorem mem_titsGraphAut_of_normalizes
    {π : Equiv.Perm (Fin 1755)}
    (hπ : ∀ g, g ∈ titsD ↔ π * g * π⁻¹ ∈ titsD) : π ∈ titsGraphAut := by
  intro x y
  rw [adj_iff_ncard_orbit, adj_iff_ncard_orbit, ncard_orbit_titsDStab hπ]

theorem centralizer_titsZD :
    Subgroup.centralizer {titsZD} = titsH.subgroupOf titsD := by
  have h := map_subtype_centralizer titsZD
  rw [show ((titsZD : titsD) : Equiv.Perm (Fin 1755)) = titsZ from rfl,
    titsD_centralizer_z] at h
  rw [← h, map_subgroupOf_titsD]

theorem map_centralizer_mulAut (β : MulAut titsD) (y : titsD) :
    (Subgroup.centralizer {y}).map β.toMonoidHom = Subgroup.centralizer {β y} := by
  ext w
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [← map_mul, hu, map_mul]
  · intro hw
    refine ⟨β.symm w, ?_, β.apply_symm_apply w⟩
    apply β.injective
    rw [map_mul, map_mul, β.apply_symm_apply, hw]

theorem fix_titsZD_of_map
    {β : MulAut titsD}
    (hS : (titsS.subgroupOf titsD).map β.toMonoidHom = titsS.subgroupOf titsD) :
    β titsZD = titsZD := by
  have hzS : titsZD ∈ titsS.subgroupOf titsD := titsZ_mem_titsS
  have hβS : β titsZD ∈ titsS.subgroupOf titsD := hS ▸ ⟨titsZD, hzS, rfl⟩
  have hcen : ∀ s ∈ titsS.subgroupOf titsD, β titsZD * s = s * β titsZD := by
    intro s hs
    rw [← hS] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 titsZ_mem_centralizer_S _ hs').symm
  have hmem : ((β titsZD : titsD) : Equiv.Perm (Fin 1755)) ∈
      (((Subgroup.center titsS).map titsS.subtype : Subgroup (Equiv.Perm (Fin 1755))) :
        Set (Equiv.Perm (Fin 1755))) := by
    refine ⟨⟨(β titsZD : titsD), hβS⟩, Subgroup.mem_center_iff.2 fun s => ?_, rfl⟩
    have hsD : (s : Equiv.Perm (Fin 1755)) ∈ titsD := titsS_le_titsD s.2
    have := hcen ⟨s, hsD⟩ s.2
    exact Subtype.ext (congrArg Subtype.val this).symm
  rw [titsS_center] at hmem
  rcases hmem with h | h
  · exfalso
    have h1 : β titsZD = 1 := Subtype.ext h
    rw [map_eq_one_iff _ β.injective] at h1
    exact titsZ_ne_one (congrArg Subtype.val h1)
  · exact Subtype.ext h

theorem mem_titsH_subgroupOf_iff
    {g : titsD} :
    g ∈ titsH.subgroupOf titsD ↔ (g : Equiv.Perm (Fin 1755)) 0 = 0 := by
  rw [Subgroup.mem_subgroupOf, mem_titsH_iff]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem apply_zero_eq_iff
    {β : MulAut titsD}
    (hβ : (titsH.subgroupOf titsD).map β.toMonoidHom = titsH.subgroupOf titsD) (g h : titsD) :
    (β g : Equiv.Perm (Fin 1755)) 0 = (β h : Equiv.Perm (Fin 1755)) 0 ↔
      (g : Equiv.Perm (Fin 1755)) 0 = (h : Equiv.Perm (Fin 1755)) 0 := by
  have key : ∀ u v : titsD, (u : Equiv.Perm (Fin 1755)) 0 = (v : Equiv.Perm (Fin 1755)) 0 ↔
      u⁻¹ * v ∈ titsH.subgroupOf titsD := by
    intro u v
    rw [mem_titsH_subgroupOf_iff]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
    constructor
    · intro e
      rw [← e, perm_inv_apply]
    · intro e
      have := congrArg (u : Equiv.Perm (Fin 1755)) e
      rwa [perm_apply_inv, eq_comm] at this
  rw [key, key, ← map_inv, ← map_mul]
  constructor
  · intro hm
    rw [← hβ] at hm
    obtain ⟨w, hw, e⟩ := hm
    rw [MulEquiv.coe_toMonoidHom] at e
    rwa [β.injective e] at hw
  · intro hm
    rw [← hβ]
    exact ⟨_, hm, rfl⟩

theorem exists_perm_of_mulAut
    {β : MulAut titsD}
    (hβ : (titsH.subgroupOf titsD).map β.toMonoidHom = titsH.subgroupOf titsD) :
    ∃ π : Equiv.Perm (Fin 1755), ∀ g : titsD,
      π * (g : Equiv.Perm (Fin 1755)) = (β g : Equiv.Perm (Fin 1755)) * π := by
  choose gx hgx using titsDPoint_transitive
  have hgx' : ∀ x, (gx x : Equiv.Perm (Fin 1755)) 0 = x := hgx
  set f : Fin 1755 → Fin 1755 := fun x => (β (gx x) : Equiv.Perm (Fin 1755)) 0
  have hf : Function.Injective f := by
    intro x y e
    rw [← hgx' x, ← hgx' y]
    exact (apply_zero_eq_iff hβ _ _).1 e
  set π := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  refine ⟨π, fun g => Equiv.ext fun x => ?_⟩
  show f ((g : Equiv.Perm (Fin 1755)) x) = (β g : Equiv.Perm (Fin 1755)) (f x)
  have h1 : (gx ((g : Equiv.Perm (Fin 1755)) x) : Equiv.Perm (Fin 1755)) 0 =
      ((g * gx x : titsD) : Equiv.Perm (Fin 1755)) 0 := by
    rw [hgx', Subgroup.coe_mul, Equiv.Perm.mul_apply, hgx']
  have h2 := (apply_zero_eq_iff hβ _ _).2 h1
  simp only [f, h2, map_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply]

theorem titsConj_surjective :
    Function.Surjective titsConj := by
  intro α
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq titsD titsSylow (α • titsSylow)
  set β : MulAut titsD := (MulAut.conj c)⁻¹ * α with hβdef
  have hβS : β • titsSylow = titsSylow := by
    rw [hβdef, mul_smul, ← hc, Sylow.smul_def, ← mul_smul, inv_mul_cancel, one_smul]
  have hS : (titsS.subgroupOf titsD).map β.toMonoidHom = titsS.subgroupOf titsD := by
    rw [← coe_titsSylow, ← coe_mulAut_smul_sylow, hβS]
  have hH : (titsH.subgroupOf titsD).map β.toMonoidHom = titsH.subgroupOf titsD := by
    rw [← centralizer_titsZD, map_centralizer_mulAut, fix_titsZD_of_map hS]
  obtain ⟨π, hπ⟩ := exists_perm_of_mulAut hH
  have hconj : ∀ g : titsD, π * (g : Equiv.Perm (Fin 1755)) * π⁻¹ = (β g : Equiv.Perm (Fin 1755)) :=
    fun g => by rw [hπ g, mul_inv_cancel_right]
  have hnorm : ∀ g, g ∈ titsD ↔ π * g * π⁻¹ ∈ titsD := by
    intro g
    constructor
    · intro hg
      rw [hconj ⟨g, hg⟩]
      exact (β ⟨g, hg⟩).2
    · intro h
      have e := hconj (β.symm ⟨_, h⟩)
      rw [MulEquiv.apply_symm_apply] at e
      have : ((β.symm ⟨_, h⟩ : titsD) : Equiv.Perm (Fin 1755)) = g :=
        mul_left_cancel (mul_right_cancel e)
      exact this ▸ (β.symm ⟨_, h⟩).2
  have hπA : π ∈ titsA := titsGraphAut_eq ▸ mem_titsGraphAut_of_normalizes hnorm
  refine ⟨⟨c * π, mul_mem (titsD_le_titsA c.2) hπA⟩, MulEquiv.ext fun d => Subtype.ext ?_⟩
  rw [coe_titsConj_apply]
  have hα : α = MulAut.conj c * β := by rw [hβdef, mul_inv_cancel_left]
  rw [hα, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, ← hconj d]
  simp only [mul_inv_rev, mul_assoc]

@[expose] def titsConjEquiv :
    titsA ≃* MulAut titsD :=
  MulEquiv.ofBijective titsConj ⟨titsConj_injective, titsConj_surjective⟩

theorem card_outer_titsD :
    Nat.card (Outer titsD) = 2 := by
  rw [Outer, ← Subgroup.index_eq_card, ← map_titsConj_titsD]
  have := Subgroup.index_map_equiv (titsD.subgroupOf titsA) titsConjEquiv
  rw [show ((titsConjEquiv : titsA →* MulAut titsD)) = titsConj from rfl] at this
  rw [this, titsD_index]

theorem CTUC_Tits_derived_full_automorphism_realization :
    Function.Bijective titsConj ∧
    (∀ (a : titsA) (d : titsD), ((titsConj a d : titsD) : Equiv.Perm (Fin 1755)) =
      (a : Equiv.Perm (Fin 1755)) * d * (a : Equiv.Perm (Fin 1755))⁻¹) ∧
    (titsD.subgroupOf titsA).map titsConj = inner titsD ∧
    Nat.card (Outer titsD) = 2 :=
  ⟨⟨titsConj_injective, titsConj_surjective⟩, coe_titsConj_apply, map_titsConj_titsD,
    card_outer_titsD⟩

end CFSG.Sporadic.Schreier.Tits
