module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9J
public import CFSG.LocalAnalysis.SteinbergBKSolvableQuaternionWitness

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup CFSG.LocalAnalysis.SteinbergBK
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

namespace Cfg

omit [Finite G] in
theorem A_le_closure_pair (h : Cfg A B) {x y : G} (hx : x ∈ A) (hy : y ∈ A)
    (hx2 : x ^ 2 = h.z) (hy2 : y ^ 2 = h.z) (hyx : y * x * y⁻¹ = x⁻¹) :
    A ≤ Subgroup.closure {x, y} := by
  obtain ⟨u, rfl⟩ := h.exists_phiA hx
  obtain ⟨v, rfl⟩ := h.exists_phiA hy
  have hu2 : u ^ 2 = a 2 := h.phiA_inj (by rw [map_pow, hx2]; rfl)
  have hv2 : v ^ 2 = a 2 := h.phiA_inj (by rw [map_pow, hy2]; rfl)
  have hvu : v * u * v⁻¹ = u⁻¹ :=
    h.phiA_inj (by rw [map_mul, map_mul, map_inv, map_inv]; exact hyx)
  have key : ∀ u v : Q8, u ^ 2 = a 2 → v ^ 2 = a 2 → v * u * v⁻¹ = u⁻¹ →
      ∀ q : Q8, ∃ ij : Fin 4 × Fin 2, q = u ^ (ij.1 : ℕ) * v ^ (ij.2 : ℕ) := by
    decide +kernel
  intro g hg
  obtain ⟨q, rfl⟩ := h.exists_phiA hg
  obtain ⟨ij, hij⟩ := key u v hu2 hv2 hvu q
  rw [hij, map_mul, map_pow, map_pow]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem J_sl (h : Cfg A B) {y : G} (hy3 : orderOf y = 3) (hy : y ∈ normalizer (A : Set G))
    (hyc : ∃ a ∈ A, y * a ≠ a * y) :
    Nonempty (↥(A ⊔ zpowers y) ≃* SL(2, ZMod 3)) ∧
      A ≤ Subgroup.closure {u : G | u ∈ A ⊔ zpowers y ∧ orderOf u = 3} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := A ⊔ zpowers y with hJ
  have hAJ : A ≤ J := le_sup_left
  have hJN : J ≤ normalizer (A : Set G) := sup_le Subgroup.le_normalizer (zpowers_le.mpr hy)
  have hJ24 : Nat.card J = 24 := h.card_J hy3 hy
  let P : Subgroup J := A.subgroupOf J
  have hPn : P.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAJ).mpr hJN
  let e : P ≃* Q8 := (Subgroup.subgroupOfEquivOfLe hAJ).trans h.eA.some
  have hP8 : Nat.card P = 8 := by rw [Nat.card_congr e.toEquiv, card_q8]
  let t : J := ⟨h.z, hAJ h.z_mem_A⟩
  have ht2 : t ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact h.z_mul_self)
  have ht1 : t ≠ 1 := fun ht => h.z_ne_one (congrArg Subtype.val ht)
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have huniq : ∀ u : J, orderOf u = 2 → u = t := by
    intro u hu
    have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hu
      omega
    apply Subtype.ext
    refine h.J_unique_involution hy3 hy u.2 ?_ (fun h1 => hu1 (Subtype.ext h1))
    have := congrArg Subtype.val hu2
    simpa [pow_two] using this
  have hC : centralizer (P : Set J) = zpowers t := by
    ext x
    constructor
    · intro hx
      have hxc : ∀ m ∈ A, (x : G) * m = m * (x : G) := by
        intro m hm
        have := Subgroup.mem_centralizer_iff.mp hx ⟨m, hAJ hm⟩
          (Subgroup.mem_subgroupOf.mpr hm)
        exact (congrArg Subtype.val this).symm
      rcases h.J_centralizer hy3 hy hyc x.2 hxc with h1 | h1
      · have hx1 : x = 1 := Subtype.ext h1
        rw [hx1]
        exact one_mem _
      · have hxt : x = t := Subtype.ext h1
        rw [hxt]
        exact mem_zpowers t
    · intro hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hpA : (p : G) ∈ A := Subgroup.mem_subgroupOf.mp hp
      have hcomm : p * t = t * p :=
        Subtype.ext (h.z_comm_sup (Subgroup.mem_sup_left hpA))
      exact (Commute.zpow_right hcomm k).eq
  have hJ3 : 3 ∣ Nat.card (⊤ : Subgroup J) := by
    rw [Subgroup.card_top, hJ24]
    norm_num
  obtain ⟨a, x, y', -, hxP, hyP, ha3, hx2, hy2, hyx, hax, hay⟩ :=
    exists_quaternion_triple (R := J) (P := P) (J := ⊤) e hto huniq hC hJ3
  refine ⟨?_, ?_⟩
  · obtain ⟨ψ, -, -, -⟩ := exists_mulEquiv_slTwoThree (R := J) (P := P) (J := ⊤) le_top hP8
      (by rw [Subgroup.card_top, hJ24]) (Subgroup.mem_top a) hxP hyP ha3 hx2 hy2 hyx hax hay
      ht1 ht2
    exact ⟨Subgroup.topEquiv.symm.trans ψ⟩
  · have hxA : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hxP
    have hyA : (y' : G) ∈ A := Subgroup.mem_subgroupOf.mp hyP
    have hx2' : (x : G) ^ 2 = h.z := by
      have := congrArg Subtype.val hx2
      simpa using this
    have hy2' : (y' : G) ^ 2 = h.z := by
      have := congrArg Subtype.val hy2
      simpa using this
    have hyx' : (y' : G) * x * (y' : G)⁻¹ = (x : G)⁻¹ := by
      have := congrArg Subtype.val hyx
      simpa using this
    have hax' : (a : G) * x * (a : G)⁻¹ = y' := by
      have := congrArg Subtype.val hax
      simpa using this
    have hay' : (a : G) * y' * (a : G)⁻¹ = x * y' := by
      have := congrArg Subtype.val hay
      simpa using this
    have haS : (a : G) ∈ {u : G | u ∈ J ∧ orderOf u = 3} :=
      ⟨a.2, by rw [Subgroup.orderOf_coe]; exact ha3⟩
    have hcS : (y' : G) * a * (y' : G)⁻¹ ∈ {u : G | u ∈ J ∧ orderOf u = 3} := by
      refine ⟨J.mul_mem (J.mul_mem y'.2 a.2) (J.inv_mem y'.2), ?_⟩
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
      exact ha3
    have hxe : (x : G) = (a : G) * ((y' : G) * a * (y' : G)⁻¹)⁻¹ := by
      have h1 : (x : G) = ((a : G) * y' * (a : G)⁻¹) * (y' : G)⁻¹ := by rw [hay']; group
      rw [h1]
      group
    have hxcl : (x : G) ∈ Subgroup.closure {u : G | u ∈ J ∧ orderOf u = 3} := by
      rw [hxe]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure haS)
        (Subgroup.inv_mem _ (Subgroup.subset_closure hcS))
    have hycl : (y' : G) ∈ Subgroup.closure {u : G | u ∈ J ∧ orderOf u = 3} := by
      rw [← hax']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure haS) hxcl)
        (Subgroup.inv_mem _ (Subgroup.subset_closure haS))
    refine (h.A_le_closure_pair hxA hyA hx2' hy2' hyx').trans ?_
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxcl
    · exact hycl

end Cfg

end CFSG.Quasithin.H13.Q8SqE9
