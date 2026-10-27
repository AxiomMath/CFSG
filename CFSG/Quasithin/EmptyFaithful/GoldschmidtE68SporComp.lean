module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporLift

public section

namespace CFSG.Quasithin.E6.Spor

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.Bar
  CFSG.Quasithin.E6.Inn

@[expose] def Cent2NoComp (X : Type*) [Group X] : Prop :=
  ∀ D : Subgroup X, IsSylowTwoOf D ⊤ → ∀ t ∈ D, orderOf t = 2 → (∀ d ∈ D, d * t = t * d) →
    ∀ B : Subgroup (centralizer ({t} : Set X)), ¬ CFSG.IsComponent B

section Lambda

variable {Λ : Type*} [Group Λ]

theorem false_of_component_of_centralizer_single {y : Λ}
    (hfree : ∀ B : Subgroup (centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} :
      Set (Λ ⧸ center Λ))), ¬ CFSG.IsComponent B)
    {K : Subgroup Λ} (hK : K ≤ centralizer ({y} : Set Λ)) (hq : CFSG.IsQuasisimple ↥K)
    (hsub : (K.subgroupOf (centralizer ({y} : Set Λ))).IsSubnormal) : False := by
  classical
  set π : Λ →* Λ ⧸ center Λ := QuotientGroup.mk' (center Λ) with hπ
  set D : Subgroup Λ := centralizer ({y} : Set Λ) with hD
  set C : Subgroup (Λ ⧸ center Λ) :=
    centralizer ({(QuotientGroup.mk y : Λ ⧸ center Λ)} : Set (Λ ⧸ center Λ)) with hC
  have hDC : D.map π ≤ C := map_centralizer_le y
  have hKD' : K.map π ≤ D.map π := Subgroup.map_mono hK
  have hKC : K.map π ≤ C := hKD'.trans hDC
  have hsub1 : ((K.map π).subgroupOf (D.map π)).IsSubnormal := by
    have h := Subgroup.IsSubnormal.map (MonoidHom.subgroupMap_surjective π D) hsub
    have heq : (K.subgroupOf D).map (π.subgroupMap D) = (K.map π).subgroupOf (D.map π) := by
      ext z
      constructor
      · rintro ⟨⟨d, hdD⟩, hdK, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr ⟨d, Subgroup.mem_subgroupOf.mp hdK, rfl⟩
      · intro hz
        obtain ⟨k, hk, hkz⟩ := Subgroup.mem_subgroupOf.mp hz
        exact ⟨⟨k, hK hk⟩, Subgroup.mem_subgroupOf.mpr hk, Subtype.ext hkz⟩
    rwa [heq] at h
  have hsub2 : ((K.map π).subgroupOf C).IsSubnormal := by
    have hnorm : ((D.map π).subgroupOf C).Normal := map_centralizer_normal y
    have hle : (K.map π).subgroupOf C ≤ (D.map π).subgroupOf C := fun x hx => hKD' hx
    have hsn : (((K.map π).subgroupOf C).subgroupOf ((D.map π).subgroupOf C)).IsSubnormal := by
      have h := hsub1.comap (subgroupOfEquivOfLe hDC).toMonoidHom
      convert h using 1
      ext x
      rfl
    exact Subgroup.IsSubnormal.trans hle hsn (Subgroup.Normal.isSubnormal hnorm)
  obtain ⟨k0, hk0K, hk0⟩ : ∃ k ∈ K, π k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b₀, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have ha : (a₀ : Λ) ∈ center Λ := (QuotientGroup.eq_one_iff (a₀ : Λ)).1 (hcon a₀ a₀.2)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp ha b₀).symm
  have hqB : CFSG.IsQuasisimple ↥((K.map π).subgroupOf C) := by
    refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective
      (φ := ((subgroupOfEquivOfLe hKC).symm.toMonoidHom).comp (π.subgroupMap K)) hq ?_ ?_
    · exact (subgroupOfEquivOfLe hKC).symm.surjective.comp (MonoidHom.subgroupMap_surjective π K)
    · refine ⟨⟨k0, hk0K⟩, fun h1 => hk0 ?_⟩
      have h2 := congrArg (fun z : ↥((K.map π).subgroupOf C) => ((z : C) : Λ ⧸ center Λ)) h1
      exact h2
  exact hfree _ ⟨hqB, hsub2⟩

end Lambda

section Ambient

variable {Y : Type} [Group Y] [Finite Y] {L R : Subgroup Y} {u : Y}

theorem not_isComponentIn_of_cent2 (h : E68CentHyp L R u) (hfix : InvolFixInner (Qbar L))
    (hc : Cent2NoComp (Qbar L)) (K : Subgroup Y) :
    ¬ IsComponentIn K (L ⊓ centralizer ({u} : Set Y)) := by
  rintro ⟨hKH, hcK⟩
  obtain ⟨y₀, hy₀, hact, hyD, hcommD⟩ := exists_inner_lift_central h hfix
  set H : Subgroup Y := L ⊓ centralizer ({u} : Set Y) with hH
  have hKL : K ≤ L := hKH.trans inf_le_left
  have hiff : ∀ x : ↥L, (x : Y) ∈ centralizer ({u} : Set Y) ↔ x ∈ centralizer ({y₀} : Set ↥L) := by
    intro x
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    have h1 := hact x
    constructor
    · intro hxu
      have h2 : u * (x : Y) * u⁻¹ = x := by rw [← hxu]; group
      rw [h2] at h1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      calc (x : Y) * y₀ = (y₀ * x * (y₀ : Y)⁻¹) * y₀ := by rw [← h1]
        _ = y₀ * x := by group
    · intro hxy
      have h2 : (y₀ : Y) * x * (y₀ : Y)⁻¹ = x := by
        have := congrArg Subtype.val hxy
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at this
        rw [← this]
        group
      rw [h2] at h1
      calc (x : Y) * u = (u * (x : Y) * u⁻¹) * u := by rw [h1]
        _ = u * x := by group
  have hKD : K.subgroupOf L ≤ centralizer ({y₀} : Set ↥L) := by
    intro x hx
    exact (hiff x).1 (Subgroup.mem_inf.mp (hKH (Subgroup.mem_subgroupOf.mp hx))).2
  have hq : CFSG.IsQuasisimple ↥(K.subgroupOf L) :=
    isQuasisimple_of_mulEquiv ((subgroupOfEquivOfLe hKH).trans (subgroupOfEquivOfLe hKL).symm)
      hcK.1
  let ψ : ↥(centralizer ({y₀} : Set ↥L)) →* ↥H :=
    { toFun := fun d => ⟨((d : ↥L) : Y), Subgroup.mem_inf.mpr ⟨(d : ↥L).2, (hiff d).2 d.2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hsub : ((K.subgroupOf L).subgroupOf (centralizer ({y₀} : Set ↥L))).IsSubnormal := by
    have h1 := hcK.2.comap ψ
    convert h1 using 1
    ext x
    rfl
  exact false_of_component_of_centralizer_single
    (hc _ (isSylowTwoOf_map_mk h) _ hyD hy₀ hcommD) hKD hq hsub

end Ambient

end CFSG.Quasithin.E6.Spor
