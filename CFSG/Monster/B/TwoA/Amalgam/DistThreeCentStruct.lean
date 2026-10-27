module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentDefs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

section JHom

variable {v : CVert} (ρ : vStab v →* GStar)

@[expose] def nToJStar : jStar.comap ρ →* jStar :=
  (ρ.comp (jStar.comap ρ).subtype).codRestrict jStar fun n => n.2

theorem nToJStar_eq_one_iff (n : jStar.comap ρ) : nToJStar ρ n = 1 ↔ ρ n = 1 :=
  Subtype.ext_iff

@[expose] def jStarEquiv : jStar ≃* groupJ.subgroupOf stdGroup :=
  (Subgroup.equivMapOfInjective (groupJ.subgroupOf stdGroup) SemidirectProduct.inl
    SemidirectProduct.inl_injective).symm

@[expose] def jSubEquiv : groupJ.subgroupOf stdGroup ≃* groupJ :=
  Subgroup.subgroupOfEquivOfLe groupJ_le_stdGroup

@[expose] def jHom : jStar.comap ρ →* groupJ :=
  jSubEquiv.toMonoidHom.comp (jStarEquiv.toMonoidHom.comp (nToJStar ρ))

theorem jHom_apply (n : jStar.comap ρ) : jHom ρ n = jSubEquiv (jStarEquiv (nToJStar ρ n)) := rfl

theorem jHom_eq_one_iff (n : jStar.comap ρ) : jHom ρ n = 1 ↔ ρ n = 1 := by
  rw [jHom_apply, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  exact nToJStar_eq_one_iff ρ n

theorem jHom_surjective (hsurj : Function.Surjective ρ) : Function.Surjective (jHom ρ) := by
  intro j
  obtain ⟨y, hy⟩ := hsurj (jStarEquiv.symm (jSubEquiv.symm j) : GStar)
  have hyN : y ∈ jStar.comap ρ := by
    rw [Subgroup.mem_comap, hy]
    exact (jStarEquiv.symm (jSubEquiv.symm j)).2
  refine ⟨⟨y, hyN⟩, ?_⟩
  rw [jHom_apply]
  have e : nToJStar ρ ⟨y, hyN⟩ = jStarEquiv.symm (jSubEquiv.symm j) := Subtype.ext hy
  rw [e, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem jHom_eq_jHom_iff (a b : jStar.comap ρ) : jHom ρ a = jHom ρ b ↔ ρ a = ρ b := by
  constructor
  · intro h
    have h' : jSubEquiv (jStarEquiv (nToJStar ρ a)) = jSubEquiv (jStarEquiv (nToJStar ρ b)) := h
    exact congrArg Subtype.val (jStarEquiv.injective (jSubEquiv.injective h'))
  · intro h
    show jSubEquiv (jStarEquiv (nToJStar ρ a)) = jSubEquiv (jStarEquiv (nToJStar ρ b))
    rw [show nToJStar ρ a = nToJStar ρ b from Subtype.ext h]

variable {ρ}

theorem cStab_mem_comap
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) :
    cStab v ∈ jStar.comap ρ := by
  rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 (hker ▸ Subgroup.mem_zpowers _)]
  exact one_mem _

theorem zpowers_cStab_le_comap
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) :
    Subgroup.zpowers (cStab v) ≤ jStar.comap ρ :=
  (Subgroup.zpowers_le).2 (cStab_mem_comap hker)

theorem ker_jHom
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) :
    (jHom ρ).ker = (Subgroup.zpowers (cStab v)).subgroupOf (jStar.comap ρ) := by
  ext n
  refine MonoidHom.mem_ker.trans ((jHom_eq_one_iff ρ n).trans ?_)
  have h : (n : vStab v) ∈ ρ.ker ↔ ρ n = 1 := MonoidHom.mem_ker
  rw [hker] at h
  exact h.symm

theorem natCard_comap_jStar
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) :
    Nat.card (jStar.comap ρ) = 6622253206732800 := by
  have h := Subgroup.card_ker_mul_card_of_surjective (jHom_surjective ρ hsurj)
  rw [ker_jHom hker, Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (zpowers_cStab_le_comap hker)).toEquiv,
    natCard_zpowers_cStab, CFSG.Monster.B.E6.FieldInvF4.card_groupJ] at h
  rw [← h]

end JHom

theorem comm_mul_comm {G : Type*} [Group G] (a b s : G) (h1 : Commute a (b * s * b⁻¹ * s⁻¹))
    (h2 : Commute (a * s * a⁻¹ * s⁻¹) (b * s * b⁻¹ * s⁻¹)) :
    a * b * s * (a * b)⁻¹ * s⁻¹ = (a * s * a⁻¹ * s⁻¹) * (b * s * b⁻¹ * s⁻¹) := by
  calc a * b * s * (a * b)⁻¹ * s⁻¹ = a * (b * s * b⁻¹ * s⁻¹) * s * a⁻¹ * s⁻¹ := by group
    _ = (b * s * b⁻¹ * s⁻¹) * a * s * a⁻¹ * s⁻¹ := by rw [h1.eq]
    _ = (b * s * b⁻¹ * s⁻¹) * (a * s * a⁻¹ * s⁻¹) := by group
    _ = (a * s * a⁻¹ * s⁻¹) * (b * s * b⁻¹ * s⁻¹) := h2.symm.eq

theorem comm_eq_one_iff {G : Type*} [Group G] (a s : G) :
    a * s * a⁻¹ * s⁻¹ = 1 ↔ Commute a s := by
  rw [← commutatorElement_def, commutatorElement_eq_one_iff_commute]

section Comm

variable {v : CVert} {ρ : vStab v →* GStar} {s : vStab v}

theorem comm_mem_zpowers
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt)
    {n : vStab v} (hn : n ∈ jStar.comap ρ) :
    n * s * n⁻¹ * s⁻¹ ∈ Subgroup.zpowers (cStab v) := by
  have hc : Commute (ρ n) (ρ s) := hs ▸ commute_betaStarElt_of_mem_jStar hn
  rw [← hker, MonoidHom.mem_ker, ← commutatorElement_def, map_commutatorElement,
    commutatorElement_eq_one_iff_commute]
  exact hc

theorem commute_of_mem_zpowers_cStab
    {x : vStab v} (hx : x ∈ Subgroup.zpowers (cStab v))
    (y : vStab v) : Commute x y :=
  ((Subgroup.mem_center_iff.1 (zpowers_cStab_le_center v hx) y)).symm

@[expose] def commHom
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) :
    jStar.comap ρ →* vStab v :=
  MonoidHom.mk' (fun n => (n : vStab v) * s * (n : vStab v)⁻¹ * s⁻¹) fun a b =>
    comm_mul_comm (a : vStab v) b s
      (commute_of_mem_zpowers_cStab (comm_mem_zpowers hker hs b.2) _).symm
      (commute_of_mem_zpowers_cStab (comm_mem_zpowers hker hs a.2) _)

theorem commHom_apply
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt)
    (n : jStar.comap ρ) : commHom hker hs n = (n : vStab v) * s * (n : vStab v)⁻¹ * s⁻¹ := rfl

theorem range_commHom_le
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) :
    (commHom hker hs).range ≤ Subgroup.zpowers (cStab v) := by
  rintro _ ⟨n, rfl⟩
  rw [commHom_apply]
  exact comm_mem_zpowers hker hs n.2

theorem mem_ker_commHom_iff
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt)
    (n : jStar.comap ρ) : n ∈ (commHom hker hs).ker ↔ Commute (n : vStab v) s :=
  MonoidHom.mem_ker.trans ((comm_eq_one_iff _ _))

theorem index_ker_commHom_le
    (hker : ρ.ker = Subgroup.zpowers (cStab v))
    (hs : ρ s = betaStarElt) : (commHom hker hs).ker.index ≤ 2 := by
  have : Finite (vStab v) := Finite.of_injective _ Subtype.val_injective
  rw [Subgroup.index_ker, ← natCard_zpowers_cStab v]
  exact Subgroup.card_le_of_le (range_commHom_le hker hs)

theorem commute_of_mem
    (hsurj : Function.Surjective ρ) (hker : ρ.ker = Subgroup.zpowers (cStab v))
    (hs : ρ s = betaStarElt) {n : vStab v} (hn : n ∈ jStar.comap ρ) : Commute n s := by
  have : Finite (vStab v) := Finite.of_injective _ Subtype.val_injective
  have hdvd := Subgroup.index_map_dvd (H := (commHom hker hs).ker) (jHom_surjective ρ hsurj)
  have hpos : (commHom hker hs).ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : ((commHom hker hs).ker.map (jHom ρ)).index ≤ 2 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd).trans (index_ker_commHom_le hker hs)
  have htop : (commHom hker hs).ker.map (jHom ρ) = ⊤ := by
    by_contra hne
    have := le_index_of_ne_top hne
    omega
  have hmem : jHom ρ ⟨n, hn⟩ ∈ (commHom hker hs).ker.map (jHom ρ) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkn⟩ := hmem
  have hρ : ρ n = ρ k := ((jHom_eq_jHom_iff ρ k ⟨n, hn⟩).1 hkn).symm
  have h1 : (k : vStab v)⁻¹ * n ∈ ρ.ker := (ρ.eq_iff).1 hρ
  rw [hker] at h1
  have hkc := (mem_ker_commHom_iff hker hs k).1 hk
  have h2 : Commute ((k : vStab v) * ((k : vStab v)⁻¹ * n)) s :=
    hkc.mul_left (commute_of_mem_zpowers_cStab h1 s)
  rwa [mul_inv_cancel_left] at h2

end Comm

theorem inv_mul_eq_mul_inv_of_mul_eq {G : Type*} [Group G] {a b c d : G} (h : a * b = c * d) :
    c⁻¹ * a = d * b⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]

theorem eq_of_mul_eq_mul_left' {G : Type*} [Group G] {a b c d : G} (h : a * b = c * d)
    (hac : a = c) : b = d := by
  rw [hac] at h
  exact mul_left_cancel h

section Cent

variable {v : CVert} {ρ : vStab v →* GStar} {s : vStab v}

theorem not_mem_comap (hs : ρ s = betaStarElt) : s ∉ jStar.comap ρ := fun h =>
  betaStarElt_not_mem_jStar (by rw [← hs]; exact h)

theorem comap_inf_zpowers (hs : ρ s = betaStarElt) (hs2 : orderOf s = 2) :
    jStar.comap ρ ⊓ Subgroup.zpowers s = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rcases (Short.mem_zpowers_iff_of_orderOf_eq_two hs2).1 hx.2 with rfl | rfl
  · exact one_mem _
  · exact absurd hx.1 (not_mem_comap hs)

theorem mul_self_eq_one_of_orderOf (hs2 : orderOf s = 2) : s * s = 1 := by
  rw [← sq, ← hs2, pow_orderOf_eq_one]

theorem mem_or_mul_mem (hs : ρ s = betaStarElt) {x : vStab v}
    (hx : x ∈ Subgroup.centralizer {s}) : x ∈ jStar.comap ρ ∨ x * s ∈ jStar.comap ρ := by
  have hxs : Commute x s := Subgroup.mem_centralizer_singleton_iff.1 hx
  have hc : Commute (ρ x) betaStarElt := hs ▸ hxs.map ρ
  rcases mem_jStar_or_of_commute hc with h | h
  · exact Or.inl h
  · have e : ρ (x * s) = ρ x * betaStarElt := (map_mul ρ x s).trans (congrArg _ hs)
    refine Or.inr ?_
    rw [Subgroup.mem_comap, e]
    exact h

theorem mul_mul_self_eq (hs2 : orderOf s = 2) (x : vStab v) : x * s * s = x := by
  rw [mul_assoc, mul_self_eq_one_of_orderOf hs2, mul_one]

theorem comap_sup_zpowers
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) (hs2 : orderOf s = 2) :
    jStar.comap ρ ⊔ Subgroup.zpowers s = Subgroup.centralizer {s} := by
  refine le_antisymm (sup_le (fun n hn => ?_) ((Subgroup.zpowers_le).2 ?_)) (fun x hx => ?_)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (commute_of_mem hsurj hker hs hn)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (Commute.refl s)
  · refine (mem_or_mul_mem (x := x) hs hx).elim (fun h => Subgroup.mem_sup_left h) (fun h => ?_)
    · have hm := Subgroup.mul_mem _ (Subgroup.mem_sup_left (S := jStar.comap ρ)
        (T := Subgroup.zpowers s) h) (Subgroup.mem_sup_right (S := jStar.comap ρ)
        (T := Subgroup.zpowers s) (Subgroup.mem_zpowers s))
      rwa [mul_mul_self_eq hs2] at hm

theorem commute_comap_zpowers
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt)
    (n : jStar.comap ρ) (z : Subgroup.zpowers s) :
    Commute ((jStar.comap ρ).subtype n) ((Subgroup.zpowers s).subtype z) := by
  have h1 : Subgroup.zpowers s ≤ Subgroup.centralizer {(n : vStab v)} :=
    (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2
      (commute_of_mem hsurj hker hs n.2).symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (h1 z.2)).symm

theorem zpowers_le_centralizer_self (s : vStab v) :
    Subgroup.zpowers s ≤ Subgroup.centralizer {s} :=
  (Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)

@[expose] def prodToStab
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) :
    (jStar.comap ρ) × Subgroup.zpowers s →* vStab v :=
  MonoidHom.noncommCoprod (jStar.comap ρ).subtype (Subgroup.zpowers s).subtype
    (commute_comap_zpowers hsurj hker hs)

theorem prodToStab_apply
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt)
    (x : (jStar.comap ρ) × Subgroup.zpowers s) :
    prodToStab hsurj hker hs x = (x.1 : vStab v) * x.2 := rfl

theorem prodToStab_mem
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt)
    (x : (jStar.comap ρ) × Subgroup.zpowers s) :
    prodToStab hsurj hker hs x ∈ Subgroup.centralizer {s} := by
  have hz : Commute (x.2 : vStab v) s :=
    Subgroup.mem_centralizer_singleton_iff.1 (zpowers_le_centralizer_self s x.2.2)
  have h : Commute ((x.1 : vStab v) * x.2) s := (commute_of_mem hsurj hker hs x.1.2).mul_left hz
  exact Subgroup.mem_centralizer_singleton_iff.2 h

@[expose] def prodToCent
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) :
    (jStar.comap ρ) × Subgroup.zpowers s →* Subgroup.centralizer {s} :=
  (prodToStab hsurj hker hs).codRestrict _ (prodToStab_mem hsurj hker hs)

theorem coe_prodToCent
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt)
    (x : (jStar.comap ρ) × Subgroup.zpowers s) :
    (prodToCent hsurj hker hs x : vStab v) = (x.1 : vStab v) * x.2 := rfl

theorem prodToCent_injective
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) (hs2 : orderOf s = 2) :
    Function.Injective (prodToCent hsurj hker hs) := by
  intro x y hxy
  have h : (x.1 : vStab v) * x.2 = (y.1 : vStab v) * y.2 := congrArg Subtype.val hxy
  have h1 := inv_mul_eq_mul_inv_of_mul_eq h
  have hm1 : (y.1 : vStab v)⁻¹ * x.1 ∈ jStar.comap ρ :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ y.1.2) x.1.2
  have hm2 : (y.1 : vStab v)⁻¹ * x.1 ∈ Subgroup.zpowers s := by
    rw [h1]
    exact Subgroup.mul_mem _ y.2.2 (Subgroup.inv_mem _ x.2.2)
  have hmem : (y.1 : vStab v)⁻¹ * x.1 ∈ jStar.comap ρ ⊓ Subgroup.zpowers s := ⟨hm1, hm2⟩
  rw [comap_inf_zpowers hs hs2, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext (eq_of_mul_eq_mul_left' h hmem.symm))

theorem prodToCent_surjective
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) (hs2 : orderOf s = 2) :
    Function.Surjective (prodToCent hsurj hker hs) := by
  rintro ⟨y, hy⟩
  refine (mem_or_mul_mem (x := y) hs hy).elim (fun h => ?_) (fun h => ?_)
  · refine ⟨(⟨y, h⟩, 1), Subtype.ext ?_⟩
    rw [coe_prodToCent]
    exact mul_one _
  · refine ⟨(⟨y * s, h⟩, ⟨s, Subgroup.mem_zpowers s⟩), Subtype.ext ?_⟩
    rw [coe_prodToCent]
    exact mul_mul_self_eq hs2 _

@[expose] def prodCentralizer
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) (hs2 : orderOf s = 2) :
    (jStar.comap ρ) × Subgroup.zpowers s ≃* Subgroup.centralizer {s} :=
  MulEquiv.ofBijective _ ⟨prodToCent_injective hsurj hker hs hs2,
    prodToCent_surjective hsurj hker hs hs2⟩

theorem coe_prodCentralizer
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) (hs2 : orderOf s = 2)
    (x : (jStar.comap ρ) × Subgroup.zpowers s) :
    (prodCentralizer hsurj hker hs hs2 x : vStab v) = (x.1 : vStab v) * x.2 := rfl

theorem natCard_centralizer_s
    (hsurj : Function.Surjective ρ)
    (hker : ρ.ker = Subgroup.zpowers (cStab v)) (hs : ρ s = betaStarElt) (hs2 : orderOf s = 2) :
    Nat.card (Subgroup.centralizer {s}) = 13244506413465600 := by
  rw [← Nat.card_congr (prodCentralizer hsurj hker hs hs2).toEquiv, Nat.card_prod,
    natCard_comap_jStar hsurj hker, Nat.card_zpowers, hs2]

end Cent

end CFSG.Monster.B.TwoA.Amalgam
