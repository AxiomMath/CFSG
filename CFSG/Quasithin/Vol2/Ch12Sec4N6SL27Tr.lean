module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27CL1
public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27Perf
public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27Transfer
public import CFSG.Quasithin.Vol2.Ch12Sec4N6SL27Hstr

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3 CFSG.LieType.BorelTits
open scoped IsMulCommutative Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sup {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ y : G, y ∈ Subgroup.normalizer (A : Set G) → y ∈ Subgroup.normalizer (B : Set G) →
      ∀ g ∈ A ⊔ B, y * g * y⁻¹ ∈ A ⊔ B := by
    intro y hyA hyB
    have hA' := Subgroup.mem_normalizer_iff.1 hyA
    have hB' := Subgroup.mem_normalizer_iff.1 hyB
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro a ha
        exact Subgroup.mem_sup_left ((hA' a).1 ha)
      · intro b hb
        exact Subgroup.mem_sup_right ((hB' b).1 hb)
    intro g hg
    exact hle hg
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key x hA hB g
  · intro hg
    have h1 := key x⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hg
    have e : x⁻¹ * (x * g * x⁻¹) * x⁻¹⁻¹ = g := by group
    rwa [e] at h1

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

theorem V_le_centralizer_E : V ≤ Subgroup.centralizer (E : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h : (⟨x, hx⟩ : ↥V) * ⟨e, c.EV he⟩ = ⟨e, c.EV he⟩ * ⟨x, hx⟩ := mul_comm _ _
  have h' : x * e = e * x := congrArg Subtype.val h
  exact h'.symm

theorem L1_sup_V_le_NE : c.L1 ⊔ V ≤ L ⊓ Subgroup.normalizer (E : Set G) :=
  sup_le (c.L1_le.trans (inf_le_inf_left L (Subgroup.centralizer_le_normalizer (E : Set G))))
    (le_inf c.V_le_L ((c.V_le_centralizer_E).trans (Subgroup.centralizer_le_normalizer _)))

theorem comm_mem_L1_sup_of_inf_centralizer (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) {x b : G}
    (hx : x ∈ L ⊓ Subgroup.centralizer (E : Set G)) (hb : b ∈ L ⊓ Subgroup.normalizer (E : Set G)) :
    x * b * x⁻¹ * b⁻¹ ∈ c.L1 ⊔ V := by
  obtain ⟨n, hn, p, hp, rfl⟩ := c.inf_centralizer_E_mem_L1_mul hx
  have hbL : b ∈ L := hb.1
  have hbE : b ∈ Subgroup.normalizer (E : Set G) := hb.2
  have hpb : p * b * p⁻¹ * b⁻¹ ∈ V := by
    have h1 := c.inv_mul_comm_mem hcomm (Subgroup.inv_mem _ hp) (L.inv_mem hbL)
    convert h1 using 1
    group
  have hbn : b * n⁻¹ * b⁻¹ ∈ c.L1 :=
    (Subgroup.mem_normalizer_iff.1 (c.mem_N_L1 (Subgroup.le_normalizer hbL) hbE) n⁻¹).1
      (c.L1.inv_mem hn)
  have e : n * p * b * (n * p)⁻¹ * b⁻¹ = n * (p * b * p⁻¹ * b⁻¹) * (b * n⁻¹ * b⁻¹) := by
    group
  rw [e]
  exact (c.L1 ⊔ V).mul_mem ((c.L1 ⊔ V).mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hpb))
    (Subgroup.mem_sup_left hbn)

theorem mem_L1_sup_of_central (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V) {d : G}
    (hdP : d ∈ pCoreOf 2 L) (hdC : d ∈ Subgroup.centralizer (L : Set G)) :
    d ∈ c.L1 ⊔ V := by
  classical
  haveI := c.isPerfect_L
  have hdL : d ∈ L := pCoreOf_le 2 L hdP
  have hdCE : d ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.centralizer_le c.EV (c.f.pCore hdP)
  have hdN : d ∈ Subgroup.normalizer (E : Set G) := Subgroup.centralizer_le_normalizer _ hdCE
  have hdH' : d ∈ L ⊓ Subgroup.normalizer (E : Set G) := ⟨hdL, hdN⟩
  have hnorm : ∀ g : G, g ∈ L ⊓ Subgroup.normalizer (E : Set G) →
      ∀ k ∈ c.L1 ⊔ V, g * k * g⁻¹ ∈ c.L1 ⊔ V := by
    intro g hg k hk
    have hgN : g ∈ Subgroup.normalizer ((c.L1 ⊔ V : Subgroup G) : Set G) :=
      mem_normalizer_sup (c.mem_N_L1 (Subgroup.le_normalizer hg.1) hg.2)
        (c.f.normalizes hg.1)
    exact (Subgroup.mem_normalizer_iff.1 hgN k).1 hk
  set H : Subgroup ↥L := (L ⊓ Subgroup.normalizer (E : Set G)).subgroupOf L with hH
  set K : Subgroup ↥L := (c.L1 ⊔ V).subgroupOf L with hK
  have hKH : K ≤ H := by
    intro x hx
    rw [hK, Subgroup.mem_subgroupOf] at hx
    rw [hH, Subgroup.mem_subgroupOf]
    exact c.L1_sup_V_le_NE hx
  have hH' : ∀ x : ↥L, x ∈ H ↔ (x : G) ∈ L ⊓ Subgroup.normalizer (E : Set G) := by
    intro x
    rw [hH, Subgroup.mem_subgroupOf]
  have hK' : ∀ x : ↥L, x ∈ K ↔ (x : G) ∈ c.L1 ⊔ V := by
    intro x
    rw [hK, Subgroup.mem_subgroupOf]
  have hNK : ∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk
    rw [hK', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hK'] at hk
    exact hnorm _ ((hH' x).1 hx) _ hk
  have hKn : (K.subgroupOf H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 fun x hx => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact hNK x hx k
    · intro hk
      have h1 := hNK x⁻¹ (H.inv_mem hx) _ hk
      have e : x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k := by group
      rwa [e] at h1
  have h2 : ∀ x ∈ H, ∃ j : ℕ, x ^ 2 ^ j ∈ K := by
    intro x hx
    have hx' := (hH' x).1 hx
    by_cases hxC : (x : G) ∈ L ⊓ Subgroup.centralizer (E : Set G)
    · obtain ⟨j, hj⟩ := exists_pow_mem_oTwoUpper (L ⊓ Subgroup.centralizer (E : Set G)) hxC
      refine ⟨j, (hK' _).2 ?_⟩
      rw [Subgroup.coe_pow]
      exact Subgroup.mem_sup_left hj
    · have hxx : (x : G) * (x : G) ∈ L ⊓ Subgroup.centralizer (E : Set G) :=
        c.NE_mul_mem_CE hx' hx' hxC hxC
      obtain ⟨j, hj⟩ := exists_pow_mem_oTwoUpper (L ⊓ Subgroup.centralizer (E : Set G)) hxx
      refine ⟨j + 1, (hK' _).2 ?_⟩
      have e : (x : G) ^ 2 ^ (j + 1) = ((x : G) * (x : G)) ^ 2 ^ j := by
        rw [pow_succ', pow_mul, sq]
      rw [Subgroup.coe_pow, e]
      exact Subgroup.mem_sup_left hj
  have hcomm' : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ K := by
    intro x hx y hy
    rw [hK']
    have hx' := (hH' x).1 hx
    have hy' := (hH' y).1 hy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    by_cases hxC : (x : G) ∈ L ⊓ Subgroup.centralizer (E : Set G) <;>
      by_cases hyC : (y : G) ∈ L ⊓ Subgroup.centralizer (E : Set G)
    · exact comm_mem_L1_sup_of_inf_centralizer c hcomm hxC hy'
    · exact comm_mem_L1_sup_of_inf_centralizer c hcomm hxC hy'
    · have h := comm_mem_L1_sup_of_inf_centralizer c hcomm hyC hx'
      have e : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ =
          ((y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹)⁻¹ := by group
      rw [e]
      exact (c.L1 ⊔ V).inv_mem h
    · have hxi : (x : G)⁻¹ ∈ L ⊓ Subgroup.normalizer (E : Set G) :=
        (L ⊓ Subgroup.normalizer (E : Set G)).inv_mem hx'
      have hxi' : (x : G)⁻¹ ∉ L ⊓ Subgroup.centralizer (E : Set G) := by
        intro h
        apply hxC
        have := (L ⊓ Subgroup.centralizer (E : Set G)).inv_mem h
        simpa using this
      have hc0 : (x : G)⁻¹ * (y : G) ∈ L ⊓ Subgroup.centralizer (E : Set G) :=
        c.NE_mul_mem_CE hxi hy' hxi' hyC
      have h := comm_mem_L1_sup_of_inf_centralizer c hcomm hc0 hx'
      have e : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ =
          (x : G) * (((x : G)⁻¹ * (y : G)) * (x : G) * ((x : G)⁻¹ * (y : G))⁻¹ * (x : G)⁻¹)⁻¹
            * (x : G)⁻¹ := by group
      rw [e]
      exact hnorm _ hx' _ ((c.L1 ⊔ V).inv_mem h)
  have hd' : ∀ g : ↥L, g * ⟨d, hdL⟩ = ⟨d, hdL⟩ * g := by
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.1 hdC g.1 g.2
  have hdH : (⟨d, hdL⟩ : ↥L) ∈ H := (hH' _).2 hdH'
  have hmem := SL27.mem_of_transfer hKH hKn c.NE_index_odd h2 hcomm' hd' hdH
  exact (hK' _).1 hmem

end Ctx

end N1246

end CFSG.Quasithin.H13
