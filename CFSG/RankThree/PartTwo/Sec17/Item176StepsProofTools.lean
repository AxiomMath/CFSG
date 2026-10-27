module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof176Steps

open scoped commutatorElement

@[expose] def HasCommOfZ {X : Type*} [Group X] (Z : Subgroup X) : Prop :=
  ∃ x y : X, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x ∈ Subgroup.centralizer (Z : Set X) ∧
    y ∈ Subgroup.centralizer (Z : Set X) ∧ ⁅x, y⁆ ∈ Z ∧ ⁅x, y⁆ ≠ 1 ∧
    IsPGroup 3 (Subgroup.closure ({x, y} : Set X))

theorem eq_zpowers_of_card_three {X : Type*} [Group X] [Finite X] {Z : Subgroup X}
    (hZ3 : Nat.card Z = 3) {w : X} (hwZ : w ∈ Z) (hw1 : w ≠ 1) : Z = Subgroup.zpowers w := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwZ) ?_
  rw [hZ3, Nat.card_zpowers]
  have hdvd : orderOf w ∣ 3 := by
    rw [← hZ3]
    exact Subgroup.orderOf_dvd_natCard Z hwZ
  have h1 : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h h1
  · omega

theorem exists_ne_one_of_card_three {X : Type*} [Group X] {Z : Subgroup X}
    (hZ3 : Nat.card Z = 3) : ∃ w ∈ Z, w ≠ 1 := by
  by_contra h
  push Not at h
  have : Z = ⊥ := (Subgroup.eq_bot_iff_forall Z).mpr h
  rw [this, Subgroup.card_bot] at hZ3
  omega

theorem hasCommOfZ_of_sylow {X : Type*} [Group X] [Finite X]
    (hP : ∀ P : Sylow 3 X, commutator ↥(P : Subgroup X) = Subgroup.center ↥(P : Subgroup X) ∧
      Nat.card (Subgroup.center ↥(P : Subgroup X)) = 3 ∧ ∀ x ∈ (P : Subgroup X), x ^ 3 = 1)
    {Z : Subgroup X} (hZ3 : Nat.card Z = 3)
    (hwc : ∀ g : X, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) →
      Z.map (MulAut.conj g).toMonoidHom = Z) : HasCommOfZ Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  obtain ⟨hcomm, hcen, hexp⟩ := hP P
  set Q := (P : Subgroup X) with hQ
  obtain ⟨w, hwZ, hw1⟩ := exists_ne_one_of_card_three hZ3
  have hZw : Z = Subgroup.zpowers w := eq_zpowers_of_card_three hZ3 hwZ hw1
  have hwQ : w ∈ Q := hZP hwZ
  have hcomQ : ∀ u ∈ Q, ∀ t ∈ Q, ∀ s ∈ Q, ⁅u, t⁆ * s = s * ⁅u, t⁆ := by
    intro u hu t ht s hs
    have hm : ⁅(⟨u, hu⟩ : ↥Q), ⟨t, ht⟩⁆ ∈ Subgroup.center ↥Q := by
      rw [← hcomm, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have h2 := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hm) ⟨s, hs⟩)
    simpa [commutatorElement_def] using h2.symm
  have hwcen : ∀ u ∈ Q, u * w = w * u := by
    intro u hu
    by_contra hne
    set v := ⁅u, w⁆ with hv
    have hv1 : v ≠ 1 := by
      intro h1
      apply hne
      rw [hv, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hvw : v * w = w * v := hcomQ u hu w hwQ w hwQ
    have hconj : u * w * u⁻¹ = v * w := by rw [hv, commutatorElement_def]; group
    have hZu : Z.map (MulAut.conj u).toMonoidHom = Subgroup.zpowers (u * w * u⁻¹) := by
      rw [hZw, MonoidHom.map_zpowers]
      rfl
    have hle : Z.map (MulAut.conj u).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) := by
      rw [hZu, Subgroup.zpowers_le, hZw]
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcw : (u * w * u⁻¹) * w = w * (u * w * u⁻¹) := by
        rw [hconj]
        calc v * w * w = w * v * w := by rw [hvw]
          _ = w * (v * w) := by group
      rw [SetLike.mem_coe, ← conj_zpow,
        show u * w * u⁻¹ * w * (u * w * u⁻¹)⁻¹ = w by rw [hcw]; group]
      exact Subgroup.zpow_mem_zpowers w k
    have hmem : u * w * u⁻¹ ∈ Z := by
      rw [← hwc u hle, hZu]
      exact Subgroup.mem_zpowers _
    have hvZ : v ∈ Z := by
      have : v = (u * w * u⁻¹) * w⁻¹ := by rw [hconj]; group
      rw [this]
      exact mul_mem hmem (inv_mem hwZ)
    have hwv : w ∈ Subgroup.zpowers v := eq_zpowers_of_card_three hZ3 hvZ hv1 ▸ hwZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwv
    apply hne
    rw [← hk]
    have hvu : Commute v u := hcomQ u hu w hwQ u hu
    exact (hvu.symm.zpow_right k).eq
  obtain ⟨x, hxQ, y, hyQ, hxy⟩ : ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x := by
    by_contra h
    push Not at h
    have hbot : commutator ↥Q = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact Subtype.ext (h _ b.2 _ a.2)
    rw [hcomm] at hbot
    rw [hbot, Subgroup.card_bot] at hcen
    omega
  have hwC : (⟨w, hwQ⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hwcen g g.2)
  have hw1' : (⟨w, hwQ⟩ : ↥Q) ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  have hcenw : Subgroup.center ↥Q = Subgroup.zpowers ⟨w, hwQ⟩ :=
    eq_zpowers_of_card_three hcen hwC hw1'
  have hxyc : ⁅(⟨x, hxQ⟩ : ↥Q), ⟨y, hyQ⟩⁆ ∈ Subgroup.center ↥Q := by
    rw [← hcomm, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [hcenw] at hxyc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxyc
  have hk' : w ^ k = ⁅x, y⁆ := by
    have := congrArg Subtype.val hk
    simpa [commutatorElement_def] using this
  have hcen' : ∀ z ∈ Q, z ∈ Subgroup.centralizer (Z : Set X) := by
    intro z hz
    rw [hZw, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact (hwcen z hz).symm
  refine ⟨x, y, hexp x hxQ, hexp y hyQ, hcen' x hxQ, hcen' y hyQ, ?_, ?_, ?_⟩
  · rw [← hk', hZw]
    exact Subgroup.zpow_mem_zpowers w k
  · rw [Ne, commutatorElement_eq_one_iff_mul_comm]
    exact hxy
  · refine P.isPGroup'.to_le ?_
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hxQ
    · exact hyQ

theorem card_subgroupOf_eq {X : Type*} [Group X] {H Z : Subgroup X} (hZH : Z ≤ H) :
    Nat.card (Z.subgroupOf H) = Nat.card Z :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv

theorem hasCommOfZ_of_subgroupOf {X : Type*} [Group X] {H Z : Subgroup X} (hZH : Z ≤ H)
    (h : HasCommOfZ (Z.subgroupOf H)) : HasCommOfZ Z := by
  obtain ⟨x, y, hx3, hy3, hxc, hyc, hxyZ, hxy1, hp⟩ := h
  have hcen : ∀ u : ↥H, u ∈ Subgroup.centralizer ((Z.subgroupOf H : Subgroup ↥H) : Set ↥H) →
      (u : X) ∈ Subgroup.centralizer (Z : Set X) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := Subgroup.mem_centralizer_iff.mp hu ⟨z, hZH hz⟩
      (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hz)
    exact congrArg Subtype.val h1
  refine ⟨x, y, ?_, ?_, hcen x hxc, hcen y hyc, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]
  · have := Subgroup.mem_subgroupOf.mp hxyZ
    simpa [commutatorElement_def] using this
  · intro h1
    apply hxy1
    apply Subtype.ext
    simpa [commutatorElement_def] using h1
  · have hcl : Subgroup.closure ({(x : X), (y : X)} : Set X) =
        (Subgroup.closure ({x, y} : Set ↥H)).map H.subtype := by
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
      rfl
    rw [hcl]
    exact hp.map _

theorem weaklyClosed_subgroupOf {X : Type*} [Group X] {H Z : Subgroup X} (hZH : Z ≤ H)
    (hwc : ∀ g : X, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) →
      Z.map (MulAut.conj g).toMonoidHom = Z) :
    ∀ h : ↥H, (Z.subgroupOf H).map (MulAut.conj h).toMonoidHom ≤
        Subgroup.normalizer ((Z.subgroupOf H : Subgroup ↥H) : Set ↥H) →
      (Z.subgroupOf H).map (MulAut.conj h).toMonoidHom = Z.subgroupOf H := by
  intro h hle
  have hmap : ((Z.subgroupOf H).map (MulAut.conj h).toMonoidHom).map H.subtype =
      Z.map (MulAut.conj (h : X)).toMonoidHom := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, Subgroup.mem_subgroupOf.mp hz, by simp [MulAut.conj_apply]⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(MulAut.conj h).toMonoidHom ⟨z, hZH hz⟩,
        ⟨⟨z, hZH hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩, ?_⟩
      simp [MulAut.conj_apply]
  have hle' : Z.map (MulAut.conj (h : X)).toMonoidHom ≤ Subgroup.normalizer (Z : Set X) := by
    rw [← hmap]
    rintro _ ⟨t, ht, rfl⟩
    have htN := hle ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 := (Subgroup.mem_normalizer_iff.mp htN ⟨z, hZH hz⟩).mp
        (Subgroup.mem_subgroupOf.mpr hz)
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa using h2
    · intro hz
      have hzH : z ∈ H := by
        have h1 : (t : X) * z * (t : X)⁻¹ ∈ H := hZH hz
        have h2 : (t : X)⁻¹ * ((t : X) * z * (t : X)⁻¹) * (t : X) ∈ H :=
          mul_mem (mul_mem (inv_mem t.2) h1) t.2
        simpa [mul_assoc] using h2
      have h1 : t * ⟨z, hzH⟩ * t⁻¹ ∈ Z.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        simpa using hz
      exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp htN ⟨z, hzH⟩).mpr h1)
  have heq := hwc h hle'
  apply Subgroup.map_injective H.subtype_injective
  rw [hmap, heq, Subgroup.map_subgroupOf_eq_of_le hZH]

theorem exists_isPGroup_map_eq {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (N : Subgroup K) [N.Normal] {F : Subgroup (K ⧸ N)} (hF : IsPGroup p F) :
    ∃ E : Subgroup K, IsPGroup p E ∧ E.map (QuotientGroup.mk' N) = F := by
  set W := F.comap (QuotientGroup.mk' N) with hW
  set f : ↥W →* ↥F := ((QuotientGroup.mk' N).comp W.subtype).codRestrict F (fun w => w.2)
    with hf
  have hfs : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N r
    exact ⟨⟨k, hr⟩, rfl⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥W))
  set P' : Sylow p ↥F := P.mapSurjective hfs with hP'
  have htop : (P' : Subgroup ↥F) = ⊤ := (P'.3 (hF.of_equiv Subgroup.topEquiv.symm) le_top).symm
  refine ⟨(P : Subgroup ↥W).map W.subtype, P.isPGroup'.map _, ?_⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2
  · intro r hr
    have hmem : (⟨r, hr⟩ : ↥F) ∈ (P' : Subgroup ↥F) := htop ▸ Subgroup.mem_top _
    rw [hP', Sylow.coe_mapSurjective] at hmem
    obtain ⟨w, hw, hwr⟩ := hmem
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwr⟩

theorem mulAut_eq_one_of_central {Q : Type*} [Group Q] (hQ : Group.IsPerfect Q) (α : MulAut Q)
    (h : ∀ q, q⁻¹ * α q ∈ Subgroup.center Q) : α = 1 := by
  let δ : Q →* Subgroup.center Q :=
    { toFun := fun q => ⟨q⁻¹ * α q, h q⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hc := Subgroup.mem_center_iff.1 (h x) y⁻¹
        show (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
        calc (x * y)⁻¹ * α (x * y) = y⁻¹ * (x⁻¹ * α x) * α y := by simp [mul_assoc]
          _ = x⁻¹ * α x * y⁻¹ * α y := by rw [hc]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by simp [mul_assoc] }
  have hker : commutator Q ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [hQ.commutator_eq_top] at hker
  ext q
  have hq : δ q = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top q))
  have := congrArg Subtype.val hq
  simp only [OneMemClass.coe_one] at this
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 this).symm

end CFSG.RankThree.PartTwo.Sec17.Proof176Steps
