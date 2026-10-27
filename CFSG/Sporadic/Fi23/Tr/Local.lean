module

public import CFSG.Sporadic.Fi22.LH.Tables
public import CFSG.Fischer.Uniq.F24Hyperoval
public import CFSG.Sporadic.Fi23.Centralizer

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer Native CFSG.Sporadic.Th

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def chiD :
    LocalClass D23 d ≃ Fi22.D := ptE.symm.trans Fi22.ptD

theorem chiD_ptE
    (u : Fin 3510) : chiD (ptE u) = Fi22.ptD u := by
  simp [chiD]

theorem chiD_symm_ptD
    (u : Fin 3510) : chiD.symm (Fi22.ptD u) = ptE u := by
  rw [Equiv.symm_apply_eq, chiD_ptE]

theorem starCd_phiP (u : Fin 3510) :
    starCd phiP[u.val]! (phiP_lt u.2) = ofStar (ptE u) := by
  apply Subtype.ext
  rw [starCd_val, ofStar_val, ptE_apply]

theorem ptE_conj_ptE
    (u v : Fin 3510) :
    (ptE u : J) * ptE v * (ptE u : J)⁻¹ = ptE (pi22 (Fi22.conjPt u.val) v) := by
  have h := rho_starCd phiP[u.val]! (phiP_lt u.2)
  rw [phiD_phiP u.2, starCd_phiP] at h
  have h2 : rho (ofStar (ptE u)) v = pi22 (Fi22.conjPt u.val) v := by rw [h]
  rw [rho_apply] at h2
  have h3 : ofStar (ptE u) • ptE v = ptE (pi22 (Fi22.conjPt u.val) v) := by
    rw [← h2, Equiv.apply_symm_apply]
  have h4 := congrArg Subtype.val h3
  rw [starAction_val, ofStar_val] at h4
  exact h4

theorem pi22_ptD (g : Fi22.J) (v : Fin 3510) :
    Fi22.ptD (pi22 g v) = Pair.conjPerm Fi22.pair_D g (Fi22.ptD v) := by
  rw [Fi22.conjPerm_ptD]
  rfl

theorem ptD_val_inv
    (u : Fin 3510) : ((Fi22.ptD u : Fi22.J))⁻¹ = Fi22.ptD u :=
  Pair.inv_eq Fi22.pair_D (Fi22.ptD u).2

theorem chiD_mul_mul
    (f g : LocalClass D23 d) :
    (chiD ⟨(f : J) * g * f, LocalPoints.mul_mul_mem_localClass pair_J f g⟩ : Fi22.J) =
      chiD f * chiD g * chiD f := by
  obtain ⟨u, rfl⟩ := ptE.surjective f
  obtain ⟨v, rfl⟩ := ptE.surjective g
  have hf : ((ptE u : J))⁻¹ = ptE u := Pair.inv_eq pair_J (ptE u).2.1
  have e : (⟨(ptE u : J) * ptE v * ptE u, LocalPoints.mul_mul_mem_localClass pair_J _ _⟩ :
      LocalClass D23 d) = ptE (pi22 (Fi22.conjPt u.val) v) := by
    apply Subtype.ext
    rw [← ptE_conj_ptE, hf]
  rw [e, chiD_ptE, chiD_ptE, chiD_ptE, pi22_ptD, Pair.conjPerm_apply, Fi22.ptD_val]
  rw [← Fi22.ptD_val, ptD_val_inv]

theorem ptE_mul_ptE
    (u v : Fin 3510) :
    (ptE u : J) * ptE v * ptE u = ptE (pi22 (Fi22.conjPt u.val) v) := by
  have h := ptE_conj_ptE u v
  rwa [Pair.inv_eq pair_J (ptE u).2.1] at h

theorem ptD_mul_ptD (u v : Fin 3510) :
    (Fi22.ptD u : Fi22.J) * Fi22.ptD v * Fi22.ptD u = Fi22.ptD (pi22 (Fi22.conjPt u.val) v) := by
  have h := congrArg (fun z : Fi22.D => (z : Fi22.J)) (pi22_ptD (Fi22.conjPt u.val) v)
  have hinv : (Fi22.conjPt u.val)⁻¹ = Fi22.conjPt u.val := by
    rw [← Fi22.ptD_val]
    exact ptD_val_inv u
  rw [Pair.conjPerm_apply, hinv] at h
  rw [Fi22.ptD_val u]
  exact h.symm

theorem ptE_commute_iff'
    (u v : Fin 3510) :
    (ptE u : J) * ptE v = ptE v * ptE u ↔ pi22 (Fi22.conjPt u.val) v = v := by
  rw [← Pair.mul_mul_eq_self_iff pair_J (ptE u).2.1 (ptE v : J), ptE_mul_ptE u v]
  constructor
  · intro h
    exact ptE.injective (Subtype.ext h)
  · intro h
    rw [h]

theorem ptD_commute_iff' (u v : Fin 3510) :
    (Fi22.ptD u : Fi22.J) * Fi22.ptD v = Fi22.ptD v * Fi22.ptD u ↔
      pi22 (Fi22.conjPt u.val) v = v := by
  rw [← Pair.mul_mul_eq_self_iff Fi22.pair_D (Fi22.ptD u).2 (Fi22.ptD v : Fi22.J),
    ptD_mul_ptD u v]
  constructor
  · intro h
    exact Fi22.ptD.injective (Subtype.ext h)
  · intro h
    rw [h]

@[expose] noncomputable def localD :
    LocalPoints (pairModel Fi22.pair_D) D23 d where
  χ := chiD
  comm f g := by
    obtain ⟨u, rfl⟩ := ptE.surjective f
    obtain ⟨v, rfl⟩ := ptE.surjective g
    rw [pairModel_perp, chiD_ptE, chiD_ptE, ptE_commute_iff', ptD_commute_iff']
  tau f g h := by
    apply Subtype.ext
    rw [pairModel_tv, ← chiD_mul_mul]

theorem localD_χ :
    localD.χ = chiD := rfl

theorem chiD_conj
    (h : Cd) (g : Fi22.J) (hg : rho h = pi22 g) (x : LocalClass D23 d) :
    chiD (h • x) = Pair.conjPerm Fi22.pair_D g (chiD x) := by
  have e : ptE.symm (h • x) = pi22 g (ptE.symm x) := by
    rw [← hg, rho_apply, Equiv.apply_symm_apply]
  rw [chiD, Equiv.trans_apply, e, pi22_ptD]
  rfl

@[expose] def chiPre
    (U : Set J) : Set Fi22.D := {p | (chiD.symm p : J) ∈ U}

theorem mem_chiPre
    {U : Set J} {p : Fi22.D} : p ∈ chiPre U ↔ (chiD.symm p : J) ∈ U := Iff.rfl

theorem chiD_mem_chiPre
    {U : Set J} (x : LocalClass D23 d) : chiD x ∈ chiPre U ↔ (x : J) ∈ U := by
  rw [mem_chiPre, Equiv.symm_apply_apply]

theorem val_image_chiPre
    (U : Set J) : Subtype.val '' chiPre U = imgIn chiD U := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨chiD.symm p, hp, by rw [Equiv.apply_symm_apply]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨chiD x, (chiD_mem_chiPre x).2 hx, rfl⟩

theorem chiPre_inj
    {U V : Set J} (hU : U ⊆ LocalClass D23 d) (hV : V ⊆ LocalClass D23 d)
    (h : chiPre U = chiPre V) : U = V := by
  ext z
  constructor
  · intro hz
    have := (chiD_mem_chiPre (U := U) ⟨z, hU hz⟩).2 hz
    rw [h] at this
    exact (chiD_mem_chiPre ⟨z, hU hz⟩).1 this
  · intro hz
    have := (chiD_mem_chiPre (U := V) ⟨z, hV hz⟩).2 hz
    rw [← h] at this
    exact (chiD_mem_chiPre ⟨z, hV hz⟩).1 this

theorem chiPre_inter_star
    (U : Set J) : chiPre (U ∩ LocalClass D23 d) = chiPre U := by
  ext p
  rw [mem_chiPre, mem_chiPre]
  exact ⟨fun h => h.1, fun h => ⟨h, (chiD.symm p).2⟩⟩

theorem mem_localClass_chiD
    (x y : LocalClass D23 d) :
    (y : J) ∈ LocalClass D23 x ↔ (chiD y : Fi22.J) ∈ LocalClass Fi22.D (chiD x) :=
  localD.mem_localClass_iff Fi22.pair_D x y

theorem isLocallyHyperoval_chiPre
    {U : Set J} (hU : IsLocallyHyperoval (LocalClass D23 d) U) :
    IsLocallyHyperoval Fi22.D (Subtype.val '' chiPre U) := by
  rw [val_image_chiPre]
  exact hU.transport chiD localD.comm
    (fun x y => ⟨LocalPoints.mul_mul_mem_localClass pair_J x y,
      (congrArg (fun z : Fi22.D => (z : Fi22.J)) (localD.tau x y _)).trans
        (pairModel_tv Fi22.pair_D _ _)⟩)
    fun x hx => Pair.mul_self pair_J hx.1

theorem chiPre_nonempty
    {U : Set J} (hU : (U ∩ LocalClass D23 d).Nonempty) :
    (chiPre U).Nonempty := by
  obtain ⟨x, hxU, hxd⟩ := hU
  exact ⟨chiD ⟨x, hxd⟩, (chiD_mem_chiPre ⟨x, hxd⟩).2 hxU⟩

theorem mem_image_conj {G : Type*} [Group G] (g : G) (U : Set G) (z : G) :
    z ∈ (fun w => g * w * g⁻¹) '' U ↔ g⁻¹ * z * g ∈ U := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [show g⁻¹ * (g * w * g⁻¹) * g = w by group]
  · intro hz
    exact ⟨_, hz, by group⟩

theorem chiPre_conj
    (h : Cd) (g : Fi22.J) (hg : rho h = pi22 g) (U : Set J) :
    chiPre ((fun z => (h : J)⁻¹ * z * ((h : J)⁻¹)⁻¹) '' U) =
      ⇑(Pair.conjPerm Fi22.pair_D g⁻¹) '' chiPre U := by
  ext p
  have e1 : h • chiD.symm p = chiD.symm (Pair.conjPerm Fi22.pair_D g p) := by
    rw [Equiv.eq_symm_apply, chiD_conj h g hg, Equiv.apply_symm_apply]
  have e2 : ((h • chiD.symm p : LocalClass D23 d) : J) = (h : J) * chiD.symm p * (h : J)⁻¹ :=
    starAction_val h _
  rw [mem_chiPre, mem_image_conj, inv_inv, ← e2, e1, ← mem_chiPre, map_inv,
    Set.mem_image_equiv, Equiv.Perm.inv_def, Equiv.symm_symm]

end CFSG.Sporadic.Fi23
