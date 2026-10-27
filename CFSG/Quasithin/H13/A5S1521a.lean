module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.Quasithin.H13.A5HBar

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open scoped commutatorElement

section Comp

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isComponent_of_isComponentOf_top {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    CFSG.IsComponent K :=
  ⟨A3.isQuasisimple_iff_open.mpr hK.2.2, (CFSG.Adapters.isSubnormal_top_iff K).mp hK.2.1⟩

theorem mem_cComp_of_isComponentOf_top {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    K ∈ cComp (⊤ : Subgroup X) :=
  mem_cComp_top_of_isComponent (isComponent_of_isComponentOf_top hK)

theorem not_central_of_isSylowTwoOf {K S : Subgroup X} (hK : IsComponentOf K ⊤)
    (hS : IsSylowTwoOf S K) : ¬ ∀ x ∈ S, ∀ k ∈ K, k * x = x * k := by
  intro hc
  obtain ⟨hcomm, hsimple⟩ := hK.2.2
  have hle : S.subgroupOf K ≤ Subgroup.center ↥K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hc _ hx _ k.2)
  have hodd : ¬ 2 ∣ (Subgroup.center ↥K).index := fun h =>
    hS.2.2 (h.trans (Subgroup.index_dvd_of_le hle))
  have hodd' : Odd (Nat.card (↥K ⧸ Subgroup.center ↥K)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
  have hperf : commutator (↥K ⧸ Subgroup.center ↥K) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    have hy : y ∈ commutator ↥K := by rw [hcomm]; exact Subgroup.mem_top y
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center ↥K)) hy
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      QuotientGroup.range_mk'] at this
    rw [commutator_def]
    exact this
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥K ⧸ Subgroup.center ↥K)
  rw [hperf] at this
  exact lt_irrefl _ this

theorem mem_normalizer_of_centralizes_sylow {K S : Subgroup X} (hK : IsComponentOf K ⊤)
    (hS : IsSylowTwoOf S K) {d : X} (hd : ∀ x ∈ S, x * d = d * x) :
    d ∈ Subgroup.normalizer (K : Set X) := by
  by_contra hdK
  have hK' := isComponent_of_isComponentOf_top hK
  have hKd := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj d) hK'
  have hne : K ≠ K.map (MulAut.conj d).toMonoidHom := by
    intro h
    apply hdK
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
    exact h.symm
  have hcomm := (CFSG.LocalCores.distinct_components_commute hK' hKd).resolve_left hne
  apply not_central_of_isSylowTwoOf hK hS
  intro x hx k hk
  have hxK : x ∈ K.map (MulAut.conj d).toMonoidHom := by
    refine ⟨x, hS.1 hx, ?_⟩
    change d * x * d⁻¹ = x
    rw [← hd x hx, mul_inv_cancel_right]
  have hKc : K.map (MulAut.conj d).toMonoidHom ≤ Subgroup.centralizer (K : Set X) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact Subgroup.mem_centralizer_iff.mp (hKc hxK) k hk

omit [Finite X] in
theorem centralizes_of_comm_central {K : Subgroup X} (hK : IsComponentOf K ⊤) {b : X}
    (hbK : b ∈ Subgroup.normalizer (K : Set X))
    (hc : ∀ k ∈ K, ∀ k' ∈ K, k' * (b * k * b⁻¹ * k⁻¹) = (b * k * b⁻¹ * k⁻¹) * k') :
    ∀ k ∈ K, k * b = b * k := by
  have hperf := hK.2.2.1
  have hz : ∀ a : ↥K, (⟨b * a * b⁻¹ * (a : X)⁻¹, K.mul_mem
      ((Subgroup.mem_normalizer_iff.mp hbK a).mp a.2) (K.inv_mem a.2)⟩ : ↥K) ∈
      Subgroup.center ↥K := by
    intro a
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc a a.2 g g.2)
  have hconj : ∀ a : ↥K, b * a * b⁻¹ ∈ K := fun a => (Subgroup.mem_normalizer_iff.mp hbK a).mp a.2
  set Cb : Subgroup ↥K := (Subgroup.centralizer {b}).subgroupOf K with hCb
  have hle : commutator ↥K ≤ Cb := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ c _
    rw [hCb, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have e1 : (⟨b * a * b⁻¹, hconj a⟩ : ↥K) =
        a * (⟨b * a * b⁻¹ * (a : X)⁻¹, K.mul_mem (hconj a) (K.inv_mem a.2)⟩ : ↥K) := by
      rw [(Subgroup.mem_center_iff.mp (hz a) a)]
      exact Subtype.ext (by simp)
    have e2 : (⟨b * c * b⁻¹, hconj c⟩ : ↥K) =
        c * (⟨b * c * b⁻¹ * (c : X)⁻¹, K.mul_mem (hconj c) (K.inv_mem c.2)⟩ : ↥K) := by
      rw [(Subgroup.mem_center_iff.mp (hz c) c)]
      exact Subtype.ext (by simp)
    have h1 : ⁅(⟨b * a * b⁻¹, hconj a⟩ : ↥K), ⟨b * c * b⁻¹, hconj c⟩⁆ = ⁅a, c⁆ := by
      rw [e1, e2, commutatorElement_mul_center_left _ (hz a),
        commutatorElement_mul_center_right _ (hz c)]
    have h2 := congrArg Subtype.val h1
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have h3 : b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹) * b⁻¹ =
        (a : X) * c * (a : X)⁻¹ * (c : X)⁻¹ := by
      calc b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹) * b⁻¹ =
          b * a * b⁻¹ * (b * c * b⁻¹) * (b * a * b⁻¹)⁻¹ * (b * c * b⁻¹)⁻¹ := by group
        _ = _ := h2
    show (a : X) * c * (a : X)⁻¹ * (c : X)⁻¹ * b = b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹)
    calc (a : X) * c * (a : X)⁻¹ * (c : X)⁻¹ * b =
        b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹) * b⁻¹ * b := by rw [h3]
      _ = b * ((a : X) * c * (a : X)⁻¹ * (c : X)⁻¹) := by group
  rw [hperf] at hle
  intro k hk
  have := hle (Subgroup.mem_top (⟨k, hk⟩ : ↥K))
  rw [hCb, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem central_of_normal_pGroup {K N : Subgroup X} (hK : IsComponentOf K ⊤) (hNK : N ≤ K)
    (hNn : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N) (hN : IsPGroup 2 N) :
    ∀ n ∈ N, ∀ k ∈ K, k * n = n * k := by
  have hqs : CFSG.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mpr hK.2.2
  have hnorm : (N.subgroupOf K).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn k k.2 n hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs hnorm with h | h
  ·
    exfalso
    have hKp : IsPGroup 2 ↥K := by
      intro k
      have hk : k ∈ N.subgroupOf K := h ▸ Subgroup.mem_top k
      rw [Subgroup.mem_subgroupOf] at hk
      obtain ⟨e, he⟩ := hN ⟨k, hk⟩
      exact ⟨e, Subtype.ext (by simpa using congrArg Subtype.val he)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := hKp.isNilpotent
    have hsolv : Group.IsSolvable ↥K := inferInstance
    have hnt : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hqs
    have := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K
    rw [hK.2.2.1] at this
    exact lt_irrefl _ this
  · intro n hn k hk
    have hc := Subgroup.mem_center_iff.mp (h (show (⟨n, hNK hn⟩ : ↥K) ∈ N.subgroupOf K from hn))
      ⟨k, hk⟩
    exact congrArg Subtype.val hc

end Comp

@[expose] noncomputable def Tstar {G : Type} [Group G] (T H : Subgroup G) : Subgroup (Hstar H) :=
  (T.subgroupOf H).map (piQ H)

end CFSG.Quasithin.H13.A5
