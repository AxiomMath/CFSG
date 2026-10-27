module

public import CFSG.RankThree.S4Free.StellmacherEmbed
public import CFSG.RankThree.S4Free.StellmacherStatement
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.RankThree.S4Free

open Subgroup CFSG.Quasithin CFSG.Open

inductive HostClass : Type
  | solvable
  | szL3
  | sz

namespace HostClass

@[expose] def Holds (𝒦 : HostClass) (X : Type*) [Group X] : Prop :=
  match 𝒦 with
  | solvable => Group.IsSolvable X
  | szL3 => SzL3Sections X
  | sz => SzSections X

theorem Holds.of_mulEquiv {𝒦 : HostClass} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : 𝒦.Holds X) : 𝒦.Holds Y := by
  cases 𝒦 with
  | solvable =>
    have : Group.IsSolvable X := h
    exact solvable_of_surjective (f := e.toMonoidHom) e.surjective
  | szL3 => exact SzL3Sections.of_mulEquiv e h
  | sz => exact SzSections.of_mulEquiv e h

theorem Holds.subgroup {𝒦 : HostClass} {X : Type*} [Group X] (h : 𝒦.Holds X) (Y : Subgroup X) :
    𝒦.Holds Y := by
  cases 𝒦 with
  | solvable =>
    have : Group.IsSolvable X := h
    exact (inferInstance : Group.IsSolvable Y)
  | szL3 => exact SzL3Sections.subgroup h Y
  | sz => exact SzSections.subgroup h Y

theorem Holds.quotient {𝒦 : HostClass} {X : Type*} [Group X] (h : 𝒦.Holds X) (N : Subgroup X)
    [N.Normal] : 𝒦.Holds (X ⧸ N) := by
  cases 𝒦 with
  | solvable =>
    have : Group.IsSolvable X := h
    exact (inferInstance : Group.IsSolvable (X ⧸ N))
  | szL3 => exact SzL3Sections.quotient h N
  | sz => exact SzSections.quotient h N

end HostClass

section Basics

variable {G : Type*} [Group G]

theorem isElemAbelian_closure_of_commute {s : Set G} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (hsq : ∀ a ∈ s, a ^ 2 = 1) : IsElemAbelian 2 (closure s) := by
  have h1 : closure s ≤ centralizer s :=
    (closure_le _).2 fun a ha => mem_centralizer_iff.2 fun b hb => hcomm b hb a ha
  have h2 : ∀ a ∈ closure s, ∀ b ∈ closure s, a * b = b * a := by
    intro a ha b hb
    have h3 : closure s ≤ centralizer ({b} : Set G) := (closure_le _).2 fun c hc =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (h1 hb) c hc)
    exact (mem_centralizer_singleton_iff.1 (h3 ha))
  refine ⟨⟨⟨fun a b => Subtype.ext (h2 _ a.2 _ b.2)⟩⟩, fun a ha => ?_⟩
  induction ha using closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact one_pow 2
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (h2 a ha b hb), iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

theorem omegaOneCenterOf_le_centerOf (X : Subgroup G) : omegaOneCenterOf X ≤ centerOf X :=
  (closure_le _).2 fun _ hx => hx.1

theorem isElemAbelian_omegaOneCenterOf' (X : Subgroup G) : IsElemAbelian 2 (omegaOneCenterOf X) :=
  isElemAbelian_closure_of_commute
    (fun a ha b hb => mem_centralizer_iff.1 (mem_inf.1 hb.1).2 a (mem_inf.1 ha.1).1)
    fun _ ha => ha.2

theorem isElemAbelian_of_le {A B : Subgroup G} (hB : IsElemAbelian 2 B) (hAB : A ≤ B) :
    IsElemAbelian 2 A := by
  obtain ⟨hc, hsq⟩ := hB
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm _ (hAB a.2) _ (hAB b.2))⟩⟩, fun a ha => hsq a (hAB ha)⟩

theorem centerOf_map_of_injective {H : Type*} [Group H] {f : G →* H}
    (hf : Function.Injective f) (X : Subgroup G) : centerOf (X.map f) = (centerOf X).map f := by
  ext y
  simp only [centerOf, mem_inf, mem_map, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, fun x' hx' => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc _ ⟨x', hx', rfl⟩
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul, hc x' hx']

theorem omegaOneCenterOf_map_of_injective' {H : Type*} [Group H] {f : G →* H}
    (hf : Function.Injective f) (X : Subgroup G) :
    omegaOneCenterOf (X.map f) = (omegaOneCenterOf X).map f := by
  rw [omegaOneCenterOf, omegaOneCenterOf, omegaOneOf, omegaOneOf, MonoidHom.map_closure,
    centerOf_map_of_injective hf]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, hf (by rw [map_pow, hy, map_one])⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_pow, hx2, map_one]⟩

theorem normal_omegaOneCenterOf' (N : Subgroup G) [N.Normal] : (omegaOneCenterOf N).Normal := by
  have hZ : (centerOf N).Normal := by
    have : (centralizer (N : Set G)).Normal := Subgroup.normal_centralizer
    exact Subgroup.normal_inf_normal _ _
  refine ⟨fun x hx g => ?_⟩
  have hle : (omegaOneCenterOf N).map (MulAut.conj g).toMonoidHom ≤ omegaOneCenterOf N := by
    rw [omegaOneCenterOf, omegaOneOf, MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨z, ⟨hz, hz2⟩, rfl⟩
    refine ⟨hZ.conj_mem z hz g, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hz2, mul_one, mul_inv_cancel]
  exact hle ⟨x, hx, by simp⟩

theorem map_omegaOneCenterOf_top (α : G ≃* G) :
    (omegaOneCenterOf (⊤ : Subgroup G)).map α.toMonoidHom = omegaOneCenterOf ⊤ := by
  rw [← omegaOneCenterOf_map_of_injective' α.injective, map_top_of_surjective _ α.surjective]

theorem isElemAbelian_map {H : Type*} [Group H] {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (f : G →* H) : IsElemAbelian 2 (A.map f) := by
  obtain ⟨hc, hsq⟩ := hA
  refine ⟨Subgroup.map_isMulCommutative A f, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, hsq a ha, map_one]

theorem isMaxElemAbelian_top_map {A : Subgroup G} (hA : IsMaxElemAbelian (⊤ : Subgroup G) A)
    (α : G ≃* G) : IsMaxElemAbelian (⊤ : Subgroup G) (A.map α.toMonoidHom) := by
  refine ⟨le_top, isElemAbelian_map hA.2.1 _, fun B _ hB => ?_⟩
  rw [Nat.card_congr (A.equivMapOfInjective α.toMonoidHom α.injective).toEquiv.symm,
    Nat.card_congr (B.equivMapOfInjective α.symm.toMonoidHom α.symm.injective).toEquiv]
  exact hA.2.2 _ le_top (isElemAbelian_map hB _)

theorem map_thompsonJ_top (α : G ≃* G) :
    (thompsonJ (⊤ : Subgroup G)).map α.toMonoidHom = thompsonJ ⊤ := by
  have key : ∀ β : G ≃* G, (thompsonJ (⊤ : Subgroup G)).map β.toMonoidHom ≤ thompsonJ ⊤ := by
    intro β
    rw [thompsonJ, Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hA => le_iSup₂_of_le (A.map β.toMonoidHom) (isMaxElemAbelian_top_map hA β)
      le_rfl
  refine le_antisymm (key α) ?_
  have h := map_mono (f := α.toMonoidHom) (key α.symm)
  rwa [map_map, show α.toMonoidHom.comp α.symm.toMonoidHom = MonoidHom.id G by ext; simp,
    map_id] at h

theorem omegaOneCenterOf_top_le_thompsonJ [Finite G] :
    omegaOneCenterOf (⊤ : Subgroup G) ≤ omegaOneCenterOf (thompsonJ (⊤ : Subgroup G)) := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨A, hA, hmax⟩ := Set.exists_max_image {B : Subgroup G | IsElemAbelian 2 B}
    (fun B => Nat.card B) (Set.toFinite _) ⟨⊥, ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩,
      fun x hx => by rw [mem_bot.1 hx, one_pow]⟩⟩
  have hAmax : IsMaxElemAbelian (⊤ : Subgroup G) A := ⟨le_top, hA, fun B _ hB => hmax B hB⟩
  refine closure_mono fun z hz => ?_
  obtain ⟨hzc, hz2⟩ := hz
  have hzcent : ∀ g : G, g * z = z * g := fun g =>
    mem_centralizer_iff.1 (mem_inf.1 hzc).2 g (mem_top g)
  let s : Set G := (A : Set G) ∪ {z}
  have hs : IsElemAbelian 2 (closure s) := by
    refine isElemAbelian_closure_of_commute ?_ ?_
    · rintro a (ha | rfl) b (hb | rfl)
      · exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      · exact hzcent a
      · exact (hzcent b).symm
      · rfl
    · rintro a (ha | rfl)
      · exact hA.2 a ha
      · exact hz2
  have hAs : A ≤ closure s := fun a ha => subset_closure (Or.inl ha)
  have heq : A = closure s := eq_of_le_of_card_ge hAs (hmax _ hs)
  have hzA : z ∈ A := heq ▸ subset_closure (Or.inr rfl)
  have hAJ : A ≤ thompsonJ (⊤ : Subgroup G) := le_iSup₂_of_le A hAmax le_rfl
  refine ⟨mem_inf.2 ⟨hAJ hzA, ?_⟩, hz2⟩
  exact mem_centralizer_iff.2 fun g _ => hzcent g

end Basics

structure F1Host (𝒦 : HostClass) {S : Type*} [Group S] {X : Type*} [Group X] (ι : S →* X) :
    Prop where
  admissible : IsAdmissibleHost ι
  holds : 𝒦.Holds X
  condM : CondM ι
  normal_thompsonJ : ((thompsonJ (⊤ : Subgroup S)).map ι).Normal

structure F2Host (𝒦 : HostClass) {S : Type*} [Group S] {X : Type*} [Group X] (ι : S →* X) :
    Prop where
  admissible : IsAdmissibleHost ι
  holds : 𝒦.Holds X
  condM : CondM ι
  not_normal_thompsonJ : ¬ ((thompsonJ (⊤ : Subgroup S)).map ι).Normal

theorem f1Host_or_f2Host {𝒦 : HostClass} {S : Type*} [Group S] {X : Type*} [Group X]
    {ι : S →* X} (h : IsAdmissibleHost ι) (hK : 𝒦.Holds X) (hM : CondM ι) :
    F1Host 𝒦 ι ∨ F2Host 𝒦 ι := by
  by_cases hJ : ((thompsonJ (⊤ : Subgroup S)).map ι).Normal
  · exact Or.inl ⟨h, hK, hM, hJ⟩
  · exact Or.inr ⟨h, hK, hM, hJ⟩

private theorem range_comp_mulEquiv {S : Type*} [Group S] {X : Type*} [Group X] (ι : S →* X)
    (α : S ≃* S) : (ι.comp α.toMonoidHom).range = ι.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_map, MonoidHom.range_eq_map,
    map_top_of_surjective _ α.surjective]

theorem F1Host.comp_mulEquiv {𝒦 : HostClass} {S : Type*} [Group S] {X : Type*} [Group X]
    {ι : S →* X} (h : F1Host 𝒦 ι) (α : S ≃* S) : F1Host 𝒦 (ι.comp α.toMonoidHom) where
  admissible := h.admissible.comp_mulEquiv α
  holds := h.holds
  condM := by
    intro N hN
    rw [range_comp_mulEquiv]
    exact h.condM N hN
  normal_thompsonJ := by
    rw [← map_map, map_thompsonJ_top]
    exact h.normal_thompsonJ

theorem map_pResidual_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] (p : ℕ)
    (e : X ≃* Y) : (pResidual p X).map e.toMonoidHom = pResidual p Y := by
  have hN := normal_pResidual p X
  have hN' := normal_pResidual p Y
  refine le_antisymm ?_ ?_
  · refine le_iInf fun N => le_iInf fun hNn => le_iInf fun hNp => ?_
    have : (N.comap e.toMonoidHom).Normal := hNn.comap _
    refine map_le_iff_le_comap.2 (pResidual_le fun x => ?_)
    obtain ⟨k, hk⟩ := hNp (e x)
    exact ⟨k, by simpa [mem_comap] using hk⟩
  · have : ((pResidual p X).map e.toMonoidHom).Normal := hN.map _ e.surjective
    refine pResidual_le fun y => ?_
    obtain ⟨k, hk⟩ := exists_pow_mem_pResidual p (e.symm y)
    exact ⟨k, ⟨_, hk, by simp⟩⟩

theorem oTwo_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (oTwo X).map e.toMonoidHom = oTwo Y :=
  CFSG.LocalCores.piCore_map_mulEquiv _ e

theorem IsAdmissibleHost.map_mulEquiv {S : Type*} [Group S] {X Y : Type*} [Group X] [Group Y]
    {ι : S →* X} (h : IsAdmissibleHost ι) (e : X ≃* Y) :
    IsAdmissibleHost (e.toMonoidHom.comp ι) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : (oTwo X).map e.toMonoidHom = oTwo Y := oTwo_map_mulEquiv e
  refine ⟨Finite.of_equiv X e.toEquiv, h.sym4Free.of_mulEquiv e, e.injective.comp h.injective,
    ?_, ?_⟩
  · obtain ⟨P, hP⟩ := h.sylow
    have hsurj : Function.Surjective e.toMonoidHom := e.surjective
    refine ⟨P.mapSurjective hsurj, ?_⟩
    rw [Sylow.coe_mapSurjective, hP, MonoidHom.range_comp]
  · intro y hy
    have hy' : e.symm y ∈ centralizer (oTwo X : Set X) := by
      rw [mem_centralizer_iff] at hy ⊢
      intro q hq
      have hq' : e q ∈ oTwo Y := by
        rw [← hO]
        exact ⟨q, hq, rfl⟩
      have := hy (e q) hq'
      apply e.injective
      simpa using this
    have := h.centralizer_le hy'
    rw [← hO]
    exact ⟨_, this, by simp⟩

theorem F1Host.map_mulEquiv {𝒦 : HostClass} {S : Type*} [Group S] {X Y : Type*} [Group X]
    [Group Y] {ι : S →* X} (h : F1Host 𝒦 ι) (e : X ≃* Y) : F1Host 𝒦 (e.toMonoidHom.comp ι) := by
  have := h.admissible.finite
  have hO : (oTwo X).map e.toMonoidHom = oTwo Y := oTwo_map_mulEquiv e
  refine ⟨h.admissible.map_mulEquiv e, h.holds.of_mulEquiv e, fun N hN => ?_, ?_⟩
  · have hN' : (N.comap e.toMonoidHom).Normal := hN.comap _
    rcases h.condM _ hN' with h1 | h1
    · left
      have := map_mono (f := e.toMonoidHom) h1
      rwa [map_inf _ _ _ e.injective, ← MonoidHom.range_comp,
        map_comap_eq_self_of_surjective e.surjective, hO] at this
    · right
      have := map_mono (f := e.toMonoidHom) h1
      rwa [map_pResidual_mulEquiv, map_comap_eq_self_of_surjective e.surjective] at this
  · rw [← map_map]
    exact h.normal_thompsonJ.map _ e.surjective

universe u v

variable (𝒦 : HostClass) (S : Type u) [Group S]

@[expose] def stellWSet : Set (Subgroup S) :=
  {U | omegaOneCenterOf (⊤ : Subgroup S) ≤ U ∧
    ∀ (X : Type u) [Group X] (ι : S →* X), F1Host 𝒦 ι → (U.map ι).Normal}

@[expose] def stellW : Subgroup S :=
  sInf (stellWSet 𝒦 S)

variable {𝒦 S}

theorem omegaOneCenterOf_thompsonJ_mem_stellWSet [Finite S] :
    omegaOneCenterOf (thompsonJ (⊤ : Subgroup S)) ∈ stellWSet 𝒦 S := by
  refine ⟨omegaOneCenterOf_top_le_thompsonJ, fun X _ ι h => ?_⟩
  have := h.normal_thompsonJ
  rw [← omegaOneCenterOf_map_of_injective' h.admissible.injective]
  exact normal_omegaOneCenterOf' _

theorem omegaOneCenterOf_le_stellW : omegaOneCenterOf (⊤ : Subgroup S) ≤ stellW 𝒦 S :=
  le_sInf fun _ hU => hU.1

theorem stellW_le_omegaOneCenterOf_thompsonJ [Finite S] :
    stellW 𝒦 S ≤ omegaOneCenterOf (thompsonJ (⊤ : Subgroup S)) :=
  sInf_le omegaOneCenterOf_thompsonJ_mem_stellWSet

theorem isElemAbelian_stellW [Finite S] : IsElemAbelian 2 (stellW 𝒦 S) :=
  isElemAbelian_of_le (isElemAbelian_omegaOneCenterOf' _) stellW_le_omegaOneCenterOf_thompsonJ

theorem stellW_normal_of_type [Finite S] {X : Type u} [Group X] {ι : S →* X}
    (h : F1Host 𝒦 ι) : ((stellW 𝒦 S).map ι).Normal := by
  have : Nonempty (stellWSet 𝒦 S) := ⟨⟨_, omegaOneCenterOf_thompsonJ_mem_stellWSet⟩⟩
  rw [stellW, sInf_eq_iInf', map_iInf ι h.admissible.injective]
  refine ⟨fun n hn g => mem_iInf.2 fun U => ?_⟩
  exact (U.2.2 X ι h).conj_mem n (mem_iInf.1 hn U) g

theorem stellW_normal [Finite S] {X : Type v} [Group X] {ι : S →* X} (h : F1Host 𝒦 ι) :
    ((stellW 𝒦 S).map ι).Normal := by
  have := h.admissible.finite
  let e : X ≃* Shrink.{u} X := Shrink.mulEquiv.symm
  have h' := stellW_normal_of_type (h.map_mulEquiv e)
  have h'' := h'.map e.symm.toMonoidHom e.symm.surjective
  rwa [map_map, ← MonoidHom.comp_assoc, show e.symm.toMonoidHom.comp e.toMonoidHom =
    MonoidHom.id X by ext; simp, MonoidHom.id_comp] at h''

theorem stellW_characteristic [Finite S] : (stellW 𝒦 S).Characteristic := by
  refine characteristic_iff_map_le.2 fun α => le_sInf fun U hU => ?_
  refine map_le_iff_le_comap.2 (sInf_le ⟨?_, fun X _ ι h => ?_⟩)
  · rw [← map_le_iff_le_comap, map_omegaOneCenterOf_top]
    exact hU.1
  · have hcm : U.comap α.toMonoidHom = U.map α.symm.toMonoidHom := by
      ext x
      simp only [mem_comap, mem_map]
      constructor
      · intro hx
        exact ⟨α x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [hcm, map_map]
    exact hU.2 X _ (h.comp_mulEquiv α.symm)

theorem stellW_ne_bot [Finite S] [Nontrivial S] (hS : IsPGroup 2 S) : stellW 𝒦 S ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hcn := hS.center_nontrivial
  have h2 : 2 ∣ Nat.card (center S) := by
    obtain ⟨n, hn, hcard⟩ := (hS.to_subgroup (center S)).nontrivial_iff_card.1 hcn
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz1 : (z : S) ≠ 1 := fun h => by
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzW : (z : S) ∈ stellW 𝒦 S := by
    refine omegaOneCenterOf_le_stellW (subset_closure ⟨mem_inf.2 ⟨mem_top _, ?_⟩, ?_⟩)
    · exact mem_centralizer_iff.2 fun g _ => (Subgroup.mem_center_iff.1 z.2 g)
    · have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
  rw [hbot, mem_bot] at hzW
  exact hz1 hzW

theorem stellW_induction [Finite S] (P : Subgroup S → Prop)
    (h0 : P (omegaOneCenterOf (⊤ : Subgroup S)))
    (hstep : ∀ U : Subgroup S, P U → omegaOneCenterOf (⊤ : Subgroup S) ≤ U →
      U ≤ stellW 𝒦 S → ∀ (X : Type u) [Group X] (ι : S →* X), F1Host 𝒦 ι →
      ¬ (U.map ι).Normal → P ((normalClosure ((U.map ι : Subgroup X) : Set X)).comap ι)) :
    P (stellW 𝒦 S) := by
  suffices key : ∀ m : ℕ, ∀ U : Subgroup S, Nat.card S - Nat.card U = m → P U →
      omegaOneCenterOf (⊤ : Subgroup S) ≤ U → U ≤ stellW 𝒦 S → P (stellW 𝒦 S) from
    key _ _ rfl h0 le_rfl omegaOneCenterOf_le_stellW
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro U hm hP h1 h2
  by_cases hall : ∀ (X : Type u) [Group X] (ι : S →* X), F1Host 𝒦 ι → (U.map ι).Normal
  · have : stellW 𝒦 S ≤ U := sInf_le ⟨h1, hall⟩
    rwa [le_antisymm h2 this] at hP
  push Not at hall
  obtain ⟨X, _, ι, hι, hU⟩ := hall
  have hP' := hstep U hP h1 h2 X ι hι hU
  have hKn : (normalClosure ((U.map ι : Subgroup X) : Set X)).Normal := normalClosure_normal
  have hUK' : U.map ι ≤ normalClosure ((U.map ι : Subgroup X) : Set X) := le_normalClosure
  have hKW : normalClosure ((U.map ι : Subgroup X) : Set X) ≤ (stellW 𝒦 S).map ι :=
    have := stellW_normal hι
    normalClosure_le_normal (map_mono h2)
  generalize normalClosure ((U.map ι : Subgroup X) : Set X) = K at hP' hKn hUK' hKW
  have hUK : U ≤ K.comap ι := map_le_iff_le_comap.1 hUK'
  have hKmap : (K.comap ι).map ι = K := by
    rw [map_comap_eq, inf_eq_right]
    exact hKW.trans (map_le_range _ _)
  have hlt : U < K.comap ι := by
    refine lt_of_le_of_ne hUK fun heq => hU ?_
    have : U.map ι = K := by rw [heq, hKmap]
    rw [this]
    exact hKn
  have hcard : Nat.card U < Nat.card (K.comap ι) := card_lt_of_lt hlt
  have hcardS : Nat.card (K.comap ι) ≤ Nat.card S := card_le_card_group _
  refine ih _ (by omega) _ rfl hP' (h1.trans hUK) ?_
  intro x hx
  obtain ⟨w, hw, hwx⟩ := hKW (show ι x ∈ K from hx)
  rwa [hι.admissible.injective hwx] at hw

theorem le_normalizer_of_normal_codRestrict {S : Type*} [Group S] {X : Type*} [Group X]
    {ι : S →* X} (hinj : Function.Injective ι) {K : Subgroup X} (hK : ι.range ≤ K)
    {W : Subgroup S} (hW : (W.map (ι.codRestrict K fun s => hK ⟨s, rfl⟩)).Normal) :
    K ≤ normalizer ((W.map ι : Subgroup X) : Set X) := by
  have key : ∀ k ∈ K, ∀ w ∈ W, k * ι w * k⁻¹ ∈ W.map ι := by
    intro k hk w hw
    obtain ⟨w', hw', h⟩ := hW.conj_mem _ ⟨w, hw, rfl⟩ ⟨k, hk⟩
    exact ⟨w', hw', congrArg Subtype.val h⟩
  intro k hk
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact key k hk w hw
  · intro hx
    obtain ⟨w, hw, hwx⟩ := hx
    have := key k⁻¹ (K.inv_mem hk) w hw
    rwa [hwx, show k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ = x by group] at this

theorem stellW_normal_of_f2 [Finite S]
    (hF2 : ∀ (Y : Type v) [Group Y] (κ : S →* Y), F2Host 𝒦 κ → ((stellW 𝒦 S).map κ).Normal)
    {X : Type v} [Group X] {ι : S →* X} (hι : IsAdmissibleHost ι) (hX : 𝒦.Holds X) :
    ((stellW 𝒦 S).map ι).Normal := by
  have := hι.finite
  refine normal_of_forall_condM hι.sylow _ fun K hK hM => ?_
  refine le_normalizer_of_normal_codRestrict hι.injective hK ?_
  rcases f1Host_or_f2Host (hι.restrict hK) (hX.subgroup K) hM with h | h
  · exact stellW_normal h
  · exact hF2 K _ h

theorem stellmacherClauseSz_of_f2 [Finite S] [Nontrivial S] (hS : IsPGroup 2 S)
    (hF2 : ∀ (Y : Type v) [Group Y] (κ : S →* Y), F2Host .sz κ →
      ((stellW .sz S).map κ).Normal) : StellmacherClauseSz.{u, v} S :=
  ⟨stellW .sz S, stellW_characteristic, stellW_ne_bot hS,
    fun _ _ _ hι hX => stellW_normal_of_f2 hF2 hι hX⟩

end CFSG.RankThree.S4Free
