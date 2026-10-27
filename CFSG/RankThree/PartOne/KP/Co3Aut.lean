module

public import CFSG.RankThree.PartOne.KP.InnerTwoCentralizers
public import CFSG.Sporadic.Schreier.Co3Schreier
public import CFSG.Sporadic.Schreier.Co3FirstAut
public import CFSG.Sporadic.Schreier.Co3SecondImage
public import CFSG.Sporadic.Schreier.MathieuSylowAutM12

public section

universe u

namespace CFSG.RankThree.PartOne

open CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem inner_eq_top_of_allInner {G : Type*} [Group G]
    (h : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) : inner G = ⊤ := by
  rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.range_eq_top]
  intro α
  obtain ⟨g, hg⟩ := h α
  exact ⟨g, hg.symm⟩

theorem card_outer_eq_one_of_allInner {G : Type*} [Group G]
    (h : ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g) : Nat.card (Outer G) = 1 := by
  show (inner G).index = 1
  rw [inner_eq_top_of_allInner h, Subgroup.index_top]

@[expose] noncomputable def subgroupOfEquiv {G : Type*} [Group G] {K H : Subgroup G}
    (S : Subgroup K) (h : H.subgroupOf K = S) (hle : H ≤ K) : S ≃* H :=
  (MulEquiv.subgroupCongr h.symm).trans (Subgroup.subgroupOfEquivOfLe hle)

theorem coe_subgroupOfEquiv_symm {G : Type*} [Group G] {K H : Subgroup G} (S : Subgroup K)
    (h : H.subgroupOf K = S) (hle : H ≤ K) (x : H) :
    (((subgroupOfEquiv S h hle).symm x : S) : K).1 = (x : G) := rfl

theorem mem_subgroupOf_of_eq {G : Type*} [Group G] {K H : Subgroup G} {x : K} {y : G}
    (hxy : (x : G) = y) (hy : y ∈ H) : x ∈ H.subgroupOf K := by
  rw [Subgroup.mem_subgroupOf, hxy]
  exact hy

theorem co3TtM1_val :
    ((co3TtM1 : co3M1) : Equiv.Perm (Fin 276)) = co3Tt := rfl

theorem co3ZM1_val :
    ((co3ZM1 : co3M1) : Equiv.Perm (Fin 276)) = co3Z := rfl

theorem co3P_allInner : ∀ α : MulAut co3P, ∃ g : co3P, α = MulAut.conj g := by
  have hzt : co3ZP * co3TtP = co3TtP * co3ZP := by
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.1 (co3M_le_centralizer co3Tt_mem_M)).symm
  have hz1 : co3ZP ≠ 1 := by
    intro h
    have h1 : co3Z = 1 := congrArg Subtype.val h
    have := orderOf_co3Z
    rw [h1, orderOf_one] at this
    omega
  have hZT : ∀ x : co3P, (x ∈ (co3TSylow : Subgroup co3P) ∧
      ∀ y ∈ (co3TSylow : Subgroup co3P), x * y = y * x) ↔ x = 1 ∨ x = co3ZP := by
    intro x
    rw [← co3TSylow_centerIn, CFSG.centerIn, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact and_congr_right fun _ => forall₂_congr fun y _ => eq_comm
  let eM : Subgroup.centralizer ({co3ZP} : Set co3P) ≃* co3M :=
    subgroupOfEquiv _ co3M_subgroupOf_eq co3M_le_P
  let eM1 : Subgroup.centralizer ({co3TtP} : Set co3P) ≃* co3M1 :=
    subgroupOfEquiv _ co3M1_subgroupOf_eq co3M1_le_P
  have hMall := allInner_of_mulEquiv eM co3M_allInner
  have htM1 : co3TtP ∈ Subgroup.centralizer ({co3TtP} : Set co3P) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have heM1t : eM1 ⟨co3TtP, htM1⟩ = co3TtM1 :=
    Subtype.ext ((rfl : ((eM1 ⟨co3TtP, htM1⟩ : co3M1) : Equiv.Perm (Fin 276)) = co3Tt).trans
      co3TtM1_val.symm)
  let κ : Subgroup.centralizer ({co3TtP} : Set co3P) →* NativeSporadic.M12 :=
    (co3Kappa1.comp eM1.toMonoidHom).codRestrict NativeSporadic.M12 (fun x => by
      rw [← co3Kappa1_range]
      exact ⟨eM1 x, rfl⟩)
  have hκsurj : Function.Surjective κ := by
    intro q
    have hq : (q : Equiv.Perm (Fin 12)) ∈ co3Kappa1.range := by
      rw [co3Kappa1_range]
      exact q.2
    obtain ⟨x, hx⟩ := hq
    exact ⟨eM1.symm x, Subtype.ext (by simp [κ, hx])⟩
  have hκker : κ.ker = Subgroup.zpowers (⟨co3TtP, htM1⟩ :
      Subgroup.centralizer ({co3TtP} : Set co3P)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
    have h1 : κ x = 1 ↔ eM1 x ∈ co3Kappa1.ker := by
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1, co3Kappa1_ker, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, eM1.injective ?_⟩
      rw [map_zpow, heM1t, hk]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← heM1t, ← map_zpow, hk]
  let L : Subgroup (Subgroup.centralizer ({co3TtP} : Set co3P)) :=
    co3L1.map eM1.symm.toMonoidHom
  have hLperf : Group.IsPerfect L := by
    have : Group.IsPerfect co3L := co3L_isPerfect
    let f : co3L ≃* L :=
      (Subgroup.subgroupOfEquivOfLe co3L_le_M1).symm.trans
        (co3L1.equivMapOfInjective eM1.symm.toMonoidHom eM1.symm.injective)
    exact Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  have hLsup : L ⊔ Subgroup.zpowers (⟨co3TtP, htM1⟩ :
      Subgroup.centralizer ({co3TtP} : Set co3P)) = ⊤ := by
    have h1 : co3Z1 = Subgroup.zpowers co3TtM1 := rfl
    have h2 : co3L1 ⊔ Subgroup.zpowers co3TtM1 = ⊤ := by
      rw [← h1]
      exact co3L1_sup_Z1
    have h3 := congrArg (Subgroup.map eM1.symm.toMonoidHom) h2
    rw [Subgroup.map_sup, Subgroup.map_top, MonoidHom.map_zpowers,
      MonoidHom.range_eq_top.2 eM1.symm.surjective] at h3
    have h4 : eM1.symm.toMonoidHom co3TtM1 = ⟨co3TtP, htM1⟩ := by
      rw [MulEquiv.coe_toMonoidHom, ← heM1t, MulEquiv.symm_apply_apply]
    rw [h4] at h3
    exact h3
  let D0 : Subgroup co3P := co3D0.subgroupOf co3P
  have hD0M : D0 ≤ Subgroup.centralizer ({co3ZP} : Set co3P) := by
    rw [← co3M_subgroupOf_eq]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (co3D0_le (Subgroup.mem_subgroupOf.1 hx))).1
  have key : ∀ d1 : co3M1, (d1 : Equiv.Perm (Fin 276)) ∈ co3D0 →
      ((eM1.symm d1 : Subgroup.centralizer ({co3TtP} : Set co3P)) : co3P) ∈ D0 := fun d1 h2 =>
    mem_subgroupOf_of_eq (K := co3P) (H := co3D0)
      (x := ((eM1.symm d1 : Subgroup.centralizer ({co3TtP} : Set co3P)) : co3P))
      (y := (d1 : Equiv.Perm (Fin 276)))
      (coe_subgroupOfEquiv_symm (S := Subgroup.centralizer ({co3TtP} : Set co3P))
        (h := co3M1_subgroupOf_eq) (hle := co3M1_le_P) d1) h2
  obtain ⟨V, hVle⟩ := co3D0Img_sylow
  have hV : ∀ v ∈ (V : Subgroup NativeSporadic.M12), ∃ d : Subgroup.centralizer
      ({co3TtP} : Set co3P), (d : co3P) ∈ D0 ∧ κ d = v := by
    intro v hv
    have h1 : (v : Equiv.Perm (Fin 12)) ∈ co3D0Img := hVle ⟨v, hv, rfl⟩
    obtain ⟨d1, hd1, hd1v⟩ := h1
    have h2 : (d1 : Equiv.Perm (Fin 276)) ∈ co3D0 := Subgroup.mem_subgroupOf.1 hd1
    refine ⟨eM1.symm d1, ?_, ?_⟩
    · exact key d1 h2
    · apply Subtype.ext
      show co3Kappa1 (eM1 (eM1.symm d1)) = v
      rw [MulEquiv.apply_symm_apply]
      exact hd1v
  have heM1z : eM1 ⟨co3ZP, Subgroup.mem_centralizer_singleton_iff.2 hzt⟩ = co3ZM1 :=
    Subtype.ext ((rfl : ((eM1 ⟨co3ZP, Subgroup.mem_centralizer_singleton_iff.2 hzt⟩ : co3M1) :
      Equiv.Perm (Fin 276)) = co3Z).trans co3ZM1_val.symm)
  have hQ := CFSG.Sporadic.Schreier.m12_sylow_pointwise_inner
  have hC : ∀ q : NativeSporadic.M12, (∀ d : Subgroup.centralizer ({co3TtP} : Set co3P),
      (d : co3P) ∈ D0 → q * κ d = κ d * q) →
      q = 1 ∨ q = κ ⟨co3ZP, Subgroup.mem_centralizer_singleton_iff.2 hzt⟩ := by
    intro q hq
    have hmem : (q : Equiv.Perm (Fin 12)) ∈ (Subgroup.centralizer (co3D0Img : Set
        (Equiv.Perm (Fin 12))) ⊓ NativeSporadic.M12 : Subgroup (Equiv.Perm (Fin 12))) := by
      refine Subgroup.mem_inf.2 ⟨?_, q.2⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨d1, hd1, rfl⟩
      have := hq (eM1.symm d1) (key d1 (Subgroup.mem_subgroupOf.1 hd1))
      have h2 := congrArg Subtype.val this
      simpa [κ] using h2.symm
    have h3 : (q : Equiv.Perm (Fin 12)) ∈ ({1, co3Kappa1 co3ZM1} : Set (Equiv.Perm (Fin 12))) := by
      rw [← co3D0Img_centralizer]
      exact hmem
    rcases h3 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (by simpa [κ, heM1z] using h))
  have hMM1 : Subgroup.centralizer ({co3ZP} : Set co3P) ⊔
      Subgroup.centralizer ({co3TtP} : Set co3P) = ⊤ := by
    have h := co3_generate
    rwa [co3_intrinsicCentralizer, co3_secondCentralizer, co3M_subgroupOf_eq,
      co3M1_subgroupOf_eq] at h
  exact allInner_of_two_centralizers co3TSylow hz1 hZT hzt hMall htM1 hLperf hLsup κ hκsurj hκker
    hD0M V hV hQ hC hMM1 (Subgroup.mem_centralizer_singleton_iff.2 hzt.symm)

theorem CTUC_Co3_all_automorphisms_inner :
    (∀ α : MulAut co3P, ∃ g : co3P, α = MulAut.conj g) ∧
      (∀ α : MulAut NativeSporadic.Co3, ∃ g : NativeSporadic.Co3, α = MulAut.conj g) ∧
      inner NativeSporadic.Co3 = ⊤ ∧ Nat.card (Outer NativeSporadic.Co3) = 1 ∧
      ∀ (G : Type u) [Group G], Nonempty (G ≃* NativeSporadic.Co3) →
        ∀ α : MulAut G, ∃ g : G, α = MulAut.conj g := by
  have h1 : ∀ α : MulAut NativeSporadic.Co3, ∃ g : NativeSporadic.Co3, α = MulAut.conj g := by
    have := allInner_of_mulEquiv (G := NativeSporadic.Co3) (H := co3P) co3PermEquiv co3P_allInner
    exact this
  exact ⟨co3P_allInner, h1, inner_eq_top_of_allInner h1, card_outer_eq_one_of_allInner h1,
    fun G _ ⟨e⟩ => allInner_of_mulEquiv (G := G) (H := NativeSporadic.Co3) e h1⟩

end CFSG.RankThree.PartOne
