module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6Q
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCSchurL32

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem pCore_le_Q : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
    have h : T ≤ Subgroup.normalizer (L : Set G) := by
      rw [c.f.MN]
      exact c.f.T_le
    exact h.trans (normalizer_le_normalizer_pCoreOf 2 L)
  exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 L) hTN) (pCoreOf_isPGroup 2 L)

theorem V_le_pCore : V ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 c.V_le_L c.f.normalizes ?_
  exact IsPGroup.of_card (p := 2) (n := 4) (by rw [c.card16])

theorem isPerfect_L : Group.IsPerfect ↥L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := c.q3
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have hQ : Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hmap : (commutator ↥L).map π = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π
      (QuotientGroup.mk'_surjective _), ← commutator_def, Group.isPerfect_def.mp hQ]
  have hpow : ∀ x : ↥L, ∃ k : ℕ, x ^ 2 ^ k ∈ commutator ↥L := by
    intro x
    obtain ⟨n, hn, hnx⟩ : π x ∈ (commutator ↥L).map π := by
      rw [hmap]
      exact Subgroup.mem_top _
    have hp : n⁻¹ * x ∈ CFSG.pCore 2 ↥L := by
      have h1 : π (n⁻¹ * x) = 1 := by rw [map_mul, map_inv, hnx, inv_mul_cancel]
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, hp⟩
    have hk' : (n⁻¹ * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hxn : (QuotientGroup.mk x : ↥L ⧸ commutator ↥L) = QuotientGroup.mk (n⁻¹ * x) := by
      rw [QuotientGroup.eq]
      have : x⁻¹ * (n⁻¹ * x) = x⁻¹ * n⁻¹ * x⁻¹⁻¹ := by group
      rw [this]
      exact (inferInstance : (commutator ↥L).Normal).conj_mem _
        (Subgroup.inv_mem _ hn) x⁻¹
    have : (QuotientGroup.mk (x ^ 2 ^ k) : ↥L ⧸ commutator ↥L) = 1 := by
      rw [QuotientGroup.mk_pow, hxn, ← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one]
    exact QuotientGroup.eq_one_iff _ |>.1 this
  have hperf : commutator ↥L = ⊤ := by
    set N : Subgroup G := (commutator ↥L).map L.subtype with hN
    have hNL : N ≤ L := Subgroup.map_subtype_le _
    have hNn : (N.subgroupOf L).Normal := by
      have hsub : N.subgroupOf L = commutator ↥L := by
        ext x
        rw [Subgroup.mem_subgroupOf, hN, Subgroup.mem_map]
        constructor
        · rintro ⟨y, hy, hyx⟩
          have : y = x := Subtype.ext hyx
          rwa [this] at hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [hsub]
      exact inferInstance
    have hNp : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
      intro x hx
      obtain ⟨k, hk⟩ := hpow ⟨x, hx⟩
      exact ⟨k, Subgroup.mem_map.2 ⟨_, hk, rfl⟩⟩
    have hNL' := c.perf N hNL hNn hNp
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hxN : x ∈ N := hNL' ▸ hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxN
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  exact Group.isPerfect_def.mpr hperf

end Ctx

theorem three_le_card_of_distinct {α : Type*} [Finite α] {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : 3 ≤ Nat.card α := by
  let f : Fin 3 → α := ![x, y, z]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have h3 := Nat.card_le_card_of_injective f hf
  simpa using h3

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem inv_mul_comm_mem (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) {a b : G}
    (ha : a ∈ pCoreOf 2 L) (hb : b ∈ L) : a⁻¹ * b⁻¹ * a * b ∈ V := by
  have haL : a ∈ L := pCoreOf_le 2 L ha
  have h1 := comm_mem hcomm (c.pCore_le_Q ha) (L.inv_mem hb)
  have h2 := (Subgroup.mem_normalizer_iff.1 (c.f.normalizes (L.inv_mem haL))
    (b⁻¹ * a * (b⁻¹)⁻¹ * a⁻¹)).1 h1
  convert h2 using 1
  group

theorem pCore_comm (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) :
    ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := c.q3
  have hVL : (V.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.V_le_L).2 c.f.normalizes
  haveI := hVL
  haveI := c.isPerfect_L
  have hVP : V.subgroupOf L ≤ CFSG.pCore 2 ↥L := by
    rw [← CFSG.openPCoreOf_subgroupOf 2 L]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact c.V_le_pCore hx
  let q : (↥L ⧸ V.subgroupOf L) →* (↥L ⧸ CFSG.pCore 2 ↥L) :=
    QuotientGroup.map (V.subgroupOf L) (CFSG.pCore 2 ↥L) (MonoidHom.id ↥L) hVP
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk a, rfl⟩
  have hEperf : Group.IsPerfect (↥L ⧸ V.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (V.subgroupOf L))
      (QuotientGroup.mk'_surjective _)
  let eGL : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* GL (Fin 3) (ZMod 2) :=
    e.trans (MulEquiv.ofBijective _
      CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two)
  have hmkP : ∀ a (ha : a ∈ pCoreOf 2 L),
      (QuotientGroup.mk ⟨a, pCoreOf_le 2 L ha⟩ : ↥L ⧸ V.subgroupOf L) ∈ q.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk ⟨a, pCoreOf_le 2 L ha⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) = 1
    rw [QuotientGroup.eq_one_iff, ← CFSG.openPCoreOf_subgroupOf 2 L, Subgroup.mem_subgroupOf]
    exact ha
  have hker : q.ker ≤ Subgroup.center (↥L ⧸ V.subgroupOf L) := by
    intro x hx
    obtain ⟨⟨a, haL⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have ha : a ∈ pCoreOf 2 L := by
      have hx' : (QuotientGroup.mk ⟨a, haL⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := hx
      rw [QuotientGroup.eq_one_iff, ← CFSG.openPCoreOf_subgroupOf 2 L,
        Subgroup.mem_subgroupOf] at hx'
      exact hx'
    refine Subgroup.mem_center_iff.2 fun g => ?_
    obtain ⟨⟨b, hbL⟩, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    convert inv_mul_comm_mem c hcomm ha hbL using 1
    group
  haveI := hEperf
  have hcard : Nat.card q.ker ≤ 2 :=
    CFSG.Quasithin.Stellmacher.PU.L3YC.card_ker_le_two_of_perfect_central eGL q hq hker
  intro a ha b hb
  have haL : a ∈ L := pCoreOf_le 2 L ha
  have hbL : b ∈ L := pCoreOf_le 2 L hb
  by_cases hav : a ∈ V
  · exact Subgroup.mem_centralizer_iff.1 (c.f.pCore hb) a hav
  by_cases hbv : b ∈ V
  · exact (Subgroup.mem_centralizer_iff.1 (c.f.pCore ha) b hbv).symm
  have hmk : (QuotientGroup.mk ⟨a, haL⟩ : ↥L ⧸ V.subgroupOf L) = QuotientGroup.mk ⟨b, hbL⟩ := by
    by_contra hne
    have h1 : (1 : ↥L ⧸ V.subgroupOf L) ≠ QuotientGroup.mk ⟨a, haL⟩ := by
      intro h
      exact hav (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := V.subgroupOf L) _).1 h.symm))
    have h2 : (1 : ↥L ⧸ V.subgroupOf L) ≠ QuotientGroup.mk ⟨b, hbL⟩ := by
      intro h
      exact hbv (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := V.subgroupOf L) _).1 h.symm))
    have h3 := three_le_card_of_distinct
      (x := (⟨1, q.ker.one_mem⟩ : q.ker))
      (y := ⟨QuotientGroup.mk ⟨a, haL⟩, hmkP a ha⟩)
      (z := ⟨QuotientGroup.mk ⟨b, hbL⟩, hmkP b hb⟩)
      (fun h => h1 (congrArg Subtype.val h)) (fun h => h2 (congrArg Subtype.val h))
      (fun h => hne (congrArg Subtype.val h))
    omega
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hmk
  have hw : (a : G)⁻¹ * (b : G) ∈ V := by
    simpa using hmk
  have hwa : (a : G)⁻¹ * (b : G) * a = a * ((a : G)⁻¹ * (b : G)) :=
    Subgroup.mem_centralizer_iff.1 (c.f.pCore ha) _ hw
  have hb' : (b : G) = a * ((a : G)⁻¹ * (b : G)) := by group
  generalize (a : G)⁻¹ * (b : G) = w at hw hwa hb'
  rw [hb', mul_assoc, hwa]

end Ctx

end N1246

end CFSG.Quasithin.H13
