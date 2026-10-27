
module

public import CFSG.Sporadic.Co2Schreier.Enum

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

section Action

variable {gens conj pis : Array (Array ℕ)} {gs cs : List (Equiv.Perm (Fin 2300))} {m : ℕ}
  {E : LeftEnum}

@[expose] def entryFun (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs}) (k : Fin m) :
    (Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs}) :=
  ⟨⟨eltE E k, hHK (hF.elt_mem hgs k.2)⟩, Subgroup.mem_subgroupOf.2 (hF.elt_mem hgs k.2)⟩

theorem entryFun_val (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs}) (k : Fin m) :
    (((entryFun hF hgs hHK k : Subgroup.closure {x | x ∈ cs})) : Equiv.Perm (Fin 2300)) =
      eltE E k := rfl

theorem entryFun_bijective (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs}) :
    Function.Bijective (entryFun hF hgs hHK) := by
  refine ⟨fun a b hab => Fin.ext (hF.elt_inj a.2 b.2 ?_), fun y => ?_⟩
  · have := congrArg (fun y : (Subgroup.closure {g | g ∈ gs}).subgroupOf
      (Subgroup.closure {x | x ∈ cs}) =>
        ((y : Subgroup.closure {x | x ∈ cs}) : Equiv.Perm (Fin 2300))) hab
    simpa only [entryFun_val] using this
  · obtain ⟨k, hk, hy⟩ := hF.exists_elt hgs (Subgroup.mem_subgroupOf.1 y.2)
    exact ⟨⟨k, hk⟩, Subtype.ext (Subtype.ext hy)⟩

@[expose] def entryEquiv (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs}) :
    Fin m ≃ (Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs}) :=
  Equiv.ofBijective _ (entryFun_bijective hF hgs hHK)

theorem toPerm_injective {G : Type*} [Group G] :
    Function.Injective (MulAut.toPerm G) := by
  intro a b h
  exact MulEquiv.ext fun x => Equiv.congr_fun h x

@[expose] def entryAction (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs})
    [hN : ((Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs})).Normal] :
    Subgroup.closure {x | x ∈ cs} →* Equiv.Perm (Fin m) :=
  ((entryEquiv hF hgs hHK).symm.permCongrHom.toMonoidHom.comp (MulAut.toPerm _)).comp
    MulAut.conjNormal

theorem card_entryAction_range (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs})
    [hN : ((Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs})).Normal] :
    Nat.card (entryAction hF hgs hHK).range =
      Nat.card (MulAut.conjNormal (H := (Subgroup.closure {g | g ∈ gs}).subgroupOf
        (Subgroup.closure {x | x ∈ cs}))).range := by
  rw [entryAction, MonoidHom.range_comp]
  exact Subgroup.card_map_of_injective
    ((entryEquiv hF hgs hHK).symm.permCongrHom.injective.comp toPerm_injective)

theorem entryAction_gen (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs})
    [hN : ((Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs})).Normal]
    (hcs : RepTuple 2300 conj cs) (hcinv : allInv conj = true) (hC : conjOK conj pis m E = true)
    {i : ℕ} (hi : i < cs.length) (hpi : isInvA m pis[i]! (invCand m pis[i]!) = true) :
    entryAction hF hgs hHK ⟨cs.getD i 1, Subgroup.subset_closure (getD_mem hi)⟩ =
      permOfArr m pis[i]! := by
  have hrep := (rep_permOfArr hpi).1
  refine Equiv.ext fun k => ?_
  have hk' : (pis[i]!)[(k : ℕ)]! < m := (conjOK_spec hC (hcs.1 ▸ hi) k.2).1
  have key : MulAut.conjNormal (H := (Subgroup.closure {g | g ∈ gs}).subgroupOf
      (Subgroup.closure {x | x ∈ cs})) ⟨cs.getD i 1, Subgroup.subset_closure (getD_mem hi)⟩
        (entryEquiv hF hgs hHK k) = entryEquiv hF hgs hHK ⟨_, hk'⟩ := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [MulAut.conjNormal_apply]
    exact hF.conj_elt hcs hcinv hC hi k.2
  change (entryEquiv hF hgs hHK).symm (MulAut.conjNormal _ (entryEquiv hF hgs hHK k)) = _
  rw [key, Equiv.symm_apply_apply]
  exact Fin.ext (hrep k)

theorem entryAction_range_eq (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs})
    [hN : ((Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs})).Normal]
    (hcs : RepTuple 2300 conj cs) (hcinv : allInv conj = true) (hC : conjOK conj pis m E = true)
    (hpis : ∀ i < cs.length, isInvA m pis[i]! (invCand m pis[i]!) = true) :
    (entryAction hF hgs hHK).range =
      Subgroup.closure {π | ∃ i < cs.length, permOfArr m pis[i]! = π} := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := {x | x ∈ cs}),
    MonoidHom.map_closure]
  congr 1
  ext π
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, hi, hci⟩ := (mem_iff_exists_getD (d := 1)).1 (show (c : Equiv.Perm (Fin 2300)) ∈
      cs from hc)
    refine ⟨i, hi, ?_⟩
    rw [← entryAction_gen hF hgs hHK hcs hcinv hC hi (hpis i hi)]
    congr 1
    exact Subtype.ext hci
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨cs.getD i 1, Subgroup.subset_closure (getD_mem hi)⟩, getD_mem hi,
      entryAction_gen hF hgs hHK hcs hcinv hC hi (hpis i hi)⟩

theorem card_range_conjNormal (hF : EnumFacts gens m E) (hgs : RepTuple 2300 gens gs)
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs})
    [hN : ((Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs})).Normal]
    (hcs : RepTuple 2300 conj cs) (hcinv : allInv conj = true) (hC : conjOK conj pis m E = true)
    (hpis : ∀ i < cs.length, isInvA m pis[i]! (invCand m pis[i]!) = true) :
    Nat.card (MulAut.conjNormal (H := (Subgroup.closure {g | g ∈ gs}).subgroupOf
      (Subgroup.closure {x | x ∈ cs}))).range =
      Nat.card (Subgroup.closure {π | ∃ i < cs.length, permOfArr m pis[i]! = π}) := by
  rw [← card_entryAction_range hF hgs hHK, entryAction_range_eq hF hgs hHK hcs hcinv hC hpis]

theorem map_ker_conjNormal
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs})
    [hN : ((Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs})).Normal] :
    (MulAut.conjNormal (H := (Subgroup.closure {g | g ∈ gs}).subgroupOf
      (Subgroup.closure {x | x ∈ cs}))).ker.map (Subgroup.closure {x | x ∈ cs}).subtype =
      Subgroup.closure {x | x ∈ cs} ⊓
        Subgroup.centralizer (Subgroup.closure {g | g ∈ gs} : Set (Equiv.Perm (Fin 2300))) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun h hh => ?_⟩
    have h1 := DFunLike.congr_fun (MonoidHom.mem_ker.1 hc)
      (⟨⟨h, hHK hh⟩, Subgroup.mem_subgroupOf.2 hh⟩ :
        (Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs}))
    have h2 := congrArg (fun y : (Subgroup.closure {g | g ∈ gs}).subgroupOf
      (Subgroup.closure {x | x ∈ cs}) =>
        ((y : Subgroup.closure {x | x ∈ cs}) : Equiv.Perm (Fin 2300))) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    have h3 : (c : Equiv.Perm (Fin 2300)) * h * (c : Equiv.Perm (Fin 2300))⁻¹ = h := h2
    show h * (c : Equiv.Perm (Fin 2300)) = (c : Equiv.Perm (Fin 2300)) * h
    conv_lhs => rw [← h3]
    group
  · rintro ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, MonoidHom.mem_ker.2 (MulEquiv.ext fun y => Subtype.ext (Subtype.ext ?_)),
      rfl⟩
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    have := hx _ (Subgroup.mem_subgroupOf.1 y.2)
    change x * ((y : Subgroup.closure {x | x ∈ cs}) : Equiv.Perm (Fin 2300)) * x⁻¹ =
      ((y : Subgroup.closure {x | x ∈ cs}) : Equiv.Perm (Fin 2300))
    rw [← this, mul_inv_cancel_right]

theorem card_inf_centralizer_mul
    (hHK : Subgroup.closure {g | g ∈ gs} ≤ Subgroup.closure {x | x ∈ cs})
    [hN : ((Subgroup.closure {g | g ∈ gs}).subgroupOf (Subgroup.closure {x | x ∈ cs})).Normal] :
    Nat.card ↥(Subgroup.closure {x | x ∈ cs} ⊓
        Subgroup.centralizer (Subgroup.closure {g | g ∈ gs} : Set (Equiv.Perm (Fin 2300)))) *
      Nat.card (MulAut.conjNormal (H := (Subgroup.closure {g | g ∈ gs}).subgroupOf
        (Subgroup.closure {x | x ∈ cs}))).range =
      Nat.card (Subgroup.closure {x | x ∈ cs}) := by
  rw [← map_ker_conjNormal hHK,
    Subgroup.card_map_of_injective (Subgroup.closure {x | x ∈ cs}).subtype_injective,
    ← Subgroup.index_ker, Subgroup.card_mul_index]

end Action

end CFSG.Sporadic.Co2Schreier
