module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClDefs
import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainGroups

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.GGQ2Frame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private def ggQTwoClIota {Bs K : Subgroup G} : Bs.subgroupOf K →* ↥Bs where
  toFun x := ⟨((x : ↥K) : G), Subgroup.mem_subgroupOf.mp x.2⟩
  map_one' := by ext; rfl
  map_mul' := by intro x y; ext; rfl

private theorem ggQTwoClIota_injective {Bs K : Subgroup G} :
    Function.Injective (ggQTwoClIota (Bs := Bs) (K := K)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥Bs => (z : G)) h))

private theorem ggQTwoCl_exists_decomp {Bs K : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c) :
    ∀ b : ↥Bs, ∃ a : ↥(Bs.subgroupOf K), ∃ c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G)),
      (b : G) = (ggQTwoClIota a : G) * (c : G) := by
  intro b
  obtain ⟨a, ha, c, hc, hbc⟩ := hsplit b b.2
  exact ⟨⟨⟨a, ha.2⟩, ha.1⟩, ⟨c, hc⟩, hbc⟩

private theorem ggQTwoCl_unique_decomp {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    {a a' : ↥(Bs.subgroupOf K)} {c c' : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))}
    (h : (ggQTwoClIota a : G) * (c : G) = (ggQTwoClIota a' : G) * (c' : G)) :
    a = a' ∧ c = c' := by
  have hx_eq : ((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)) =
      ((c : G) * (c' : G)⁻¹) := by
    have h1 := congrArg (fun t : G => (ggQTwoClIota a : G)⁻¹ * t * (c' : G)⁻¹) h
    group at h1
    simpa only [zpow_neg_one] using h1.symm
  have hxBs : ((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)) ∈ Bs := by
    refine Bs.mul_mem ?_ ?_
    · exact Bs.inv_mem (Subgroup.mem_subgroupOf.mp a.2)
    · exact Subgroup.mem_subgroupOf.mp a'.2
  have hxK : ((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)) ∈ K := by
    refine K.mul_mem (K.inv_mem ?_) ?_
    · exact (a : ↥K).2
    · exact (a' : ↥K).2
  have hxC : ((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)) ∈
      Subgroup.centralizer (K : Set G) := by
    rw [hx_eq]
    exact (Subgroup.centralizer (K : Set G)).mul_mem c.2.2
      ((Subgroup.centralizer (K : Set G)).inv_mem c'.2.2)
  have hx_center : (⟨((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)), hxK⟩ : ↥K) ∈
      Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxC (y : G) y.2
  have hx_pow : ((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)) ^ 3 = 1 := hEab.2 _ hxBs
  have hx1 : ((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)) = 1 := by
    by_contra hxne
    have hord : orderOf ((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)) = 3 :=
      orderOf_eq_prime hx_pow hxne
    let y : ↥K := ⟨((ggQTwoClIota a : G)⁻¹ * (ggQTwoClIota a' : G)), hxK⟩
    have hy_center : y ∈ Subgroup.center ↥K := hx_center
    have hyord : orderOf y = 3 := by
      rw [Subgroup.orderOf_mk, hord]
    have hdvd : 3 ∣ Nat.card (Subgroup.center ↥K) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hy_center
      rwa [hyord] at h
    exact hZ3 hdvd
  have haa' : a = a' := by
    apply Subtype.ext
    apply Subtype.ext
    exact inv_mul_eq_one.mp hx1
  have hcc' : c = c' := by
    apply Subtype.ext
    rw [haa'] at h
    exact mul_left_cancel h
  exact ⟨haa', hcc'⟩

private noncomputable def ggQTwoClPr {Bs K : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (b : ↥Bs) : ↥(Bs.subgroupOf K) :=
  Classical.choose (ggQTwoCl_exists_decomp hsplit b)

private noncomputable def ggQTwoClC {Bs K : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (b : ↥Bs) : ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
  Classical.choose (Classical.choose_spec (ggQTwoCl_exists_decomp hsplit b))

private def ggQTwoClCtoBs {Bs K : Subgroup G}
    (c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) : ↥Bs :=
  ⟨(c : G), c.2.1⟩

@[simp] private theorem ggQTwoClCtoBs_coe {Bs K : Subgroup G}
    (c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) :
    ((ggQTwoClCtoBs c : ↥Bs) : G) = (c : G) := rfl

@[simp] private theorem ggQTwoClCtoBs_one {Bs K : Subgroup G} :
    ggQTwoClCtoBs (1 : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) = 1 := rfl

private theorem ggQTwoCl_decomp {Bs K : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (b : ↥Bs) :
    (b : G) = (ggQTwoClIota (ggQTwoClPr hsplit b) : G) * (ggQTwoClC hsplit b : G) :=
  Classical.choose_spec (Classical.choose_spec (ggQTwoCl_exists_decomp hsplit b))

private theorem ggQTwoCl_decomp_self {Bs K : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (b : ↥Bs) :
    b = ggQTwoClIota (ggQTwoClPr hsplit b) * ggQTwoClCtoBs (ggQTwoClC hsplit b) := by
  apply Subtype.ext
  simpa using ggQTwoCl_decomp hsplit b

private theorem ggQTwoCl_unique_alt {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    {b : ↥Bs} {a' : ↥(Bs.subgroupOf K)} {c' : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))}
    (hb : (b : G) = (ggQTwoClIota a' : G) * (c' : G)) :
    ggQTwoClPr hsplit b = a' ∧ ggQTwoClC hsplit b = c' := by
  have h1 : (b : G) = (ggQTwoClIota (ggQTwoClPr hsplit b) : G) *
      (ggQTwoClC hsplit b : G) := ggQTwoCl_decomp hsplit b
  exact ggQTwoCl_unique_decomp (a := ggQTwoClPr hsplit b) (a' := a')
    (c := ggQTwoClC hsplit b) (c' := c') hEab hZ3 (h1.symm.trans hb)

private theorem ggQTwoCl_mul_decomp {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (b1 b2 : ↥Bs) :
    (b1 * b2 : G) =
      (ggQTwoClIota (ggQTwoClPr hsplit b1 * ggQTwoClPr hsplit b2) : G) *
      ((ggQTwoClC hsplit b1 * ggQTwoClC hsplit b2 :
        ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) : G) := by
  have h1 := ggQTwoCl_decomp hsplit b1
  have h2 := ggQTwoCl_decomp hsplit b2
  have hcomm : ((ggQTwoClC hsplit b1 : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) : G) *
      (ggQTwoClIota (ggQTwoClPr hsplit b2) : G) =
      (ggQTwoClIota (ggQTwoClPr hsplit b2) : G) *
      ((ggQTwoClC hsplit b1 : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) : G) := by
    have hc1 : ((ggQTwoClC hsplit b1 : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) : G) ∈ Bs :=
      (ggQTwoClC hsplit b1).2.1
    have ha2 : (ggQTwoClIota (ggQTwoClPr hsplit b2) : G) ∈ Bs :=
      Subgroup.mem_subgroupOf.mp (ggQTwoClPr hsplit b2).2
    exact congrArg Subtype.val (isMulCommutative_iff.mp hEab.1
      ⟨(ggQTwoClC hsplit b1 : G), hc1⟩ ⟨(ggQTwoClIota (ggQTwoClPr hsplit b2) : G), ha2⟩)
  calc (b1 * b2 : G) = (b1 : G) * (b2 : G) := rfl
    _ = ((ggQTwoClIota (ggQTwoClPr hsplit b1) : G) * (ggQTwoClC hsplit b1 : G)) *
          ((ggQTwoClIota (ggQTwoClPr hsplit b2) : G) * (ggQTwoClC hsplit b2 : G)) := by
          rw [h1, h2]
    _ = ((ggQTwoClIota (ggQTwoClPr hsplit b1) : G) *
            (ggQTwoClIota (ggQTwoClPr hsplit b2) : G)) *
          ((ggQTwoClC hsplit b1 : G) * (ggQTwoClC hsplit b2 : G)) := by
          have hreassoc : ((ggQTwoClIota (ggQTwoClPr hsplit b1) : G) *
              (ggQTwoClC hsplit b1 : G)) *
              ((ggQTwoClIota (ggQTwoClPr hsplit b2) : G) * (ggQTwoClC hsplit b2 : G)) =
              (ggQTwoClIota (ggQTwoClPr hsplit b1) : G) *
                (((ggQTwoClC hsplit b1 : G) * (ggQTwoClIota (ggQTwoClPr hsplit b2) : G)) *
                  (ggQTwoClC hsplit b2 : G)) := by group
          rw [hreassoc, hcomm]
          group
    _ = (ggQTwoClIota (ggQTwoClPr hsplit b1 * ggQTwoClPr hsplit b2) : G) *
          ((ggQTwoClC hsplit b1 * ggQTwoClC hsplit b2 :
            ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) : G) := by
          rw [map_mul]; rfl

private theorem ggQTwoClPr_mul {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (b1 b2 : ↥Bs) :
    ggQTwoClPr hsplit (b1 * b2) = ggQTwoClPr hsplit b1 * ggQTwoClPr hsplit b2 :=
  (ggQTwoCl_unique_alt hEab hZ3 hsplit (b := b1 * b2)
    (a' := ggQTwoClPr hsplit b1 * ggQTwoClPr hsplit b2)
    (c' := ggQTwoClC hsplit b1 * ggQTwoClC hsplit b2)
    (ggQTwoCl_mul_decomp hEab hsplit b1 b2)).1

private theorem ggQTwoClC_mul {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (b1 b2 : ↥Bs) :
    ggQTwoClC hsplit (b1 * b2) = ggQTwoClC hsplit b1 * ggQTwoClC hsplit b2 :=
  (ggQTwoCl_unique_alt hEab hZ3 hsplit (b := b1 * b2)
    (a' := ggQTwoClPr hsplit b1 * ggQTwoClPr hsplit b2)
    (c' := ggQTwoClC hsplit b1 * ggQTwoClC hsplit b2)
    (ggQTwoCl_mul_decomp hEab hsplit b1 b2)).2

private theorem ggQTwoClPr_one {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c) :
    ggQTwoClPr hsplit 1 = 1 :=
  (ggQTwoCl_unique_alt hEab hZ3 hsplit (b := 1) (a' := 1) (c' := 1)
    (by simp)).1

private theorem ggQTwoClC_one {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c) :
    ggQTwoClC hsplit 1 = 1 :=
  (ggQTwoCl_unique_alt hEab hZ3 hsplit (b := 1) (a' := 1) (c' := 1)
    (by simp)).2

private theorem ggQTwoClPr_iota {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (x : ↥(Bs.subgroupOf K)) :
    ggQTwoClPr hsplit (ggQTwoClIota x) = x :=
  (ggQTwoCl_unique_alt hEab hZ3 hsplit (b := ggQTwoClIota x) (a' := x) (c' := 1)
    (by simp)).1

private theorem ggQTwoClC_iota {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (x : ↥(Bs.subgroupOf K)) :
    ggQTwoClC hsplit (ggQTwoClIota x) = 1 :=
  (ggQTwoCl_unique_alt hEab hZ3 hsplit (b := ggQTwoClIota x) (a' := x) (c' := 1)
    (by simp)).2

private theorem ggQTwoClPr_Psi {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (ψ : MulAut ↥(Bs.subgroupOf K)) (b : ↥Bs) :
    ggQTwoClPr hsplit (ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) *
      ggQTwoClCtoBs (ggQTwoClC hsplit b)) = ψ (ggQTwoClPr hsplit b) := by
  let x := ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) * ggQTwoClCtoBs (ggQTwoClC hsplit b)
  have hx : (x : G) = (ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) : G) *
      (ggQTwoClC hsplit b : G) := rfl
  exact (ggQTwoCl_unique_decomp (a := ψ (ggQTwoClPr hsplit b))
    (a' := ggQTwoClPr hsplit x) (c := ggQTwoClC hsplit b) (c' := ggQTwoClC hsplit x)
    hEab hZ3 (hx.symm.trans (ggQTwoCl_decomp hsplit x))).1.symm

private theorem ggQTwoClC_Psi {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (ψ : MulAut ↥(Bs.subgroupOf K)) (b : ↥Bs) :
    ggQTwoClC hsplit (ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) *
      ggQTwoClCtoBs (ggQTwoClC hsplit b)) = ggQTwoClC hsplit b := by
  let x := ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) * ggQTwoClCtoBs (ggQTwoClC hsplit b)
  have hx : (x : G) = (ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) : G) *
      (ggQTwoClC hsplit b : G) := rfl
  exact (ggQTwoCl_unique_decomp (a := ψ (ggQTwoClPr hsplit b))
    (a' := ggQTwoClPr hsplit x) (c := ggQTwoClC hsplit b) (c' := ggQTwoClC hsplit x)
    hEab hZ3 (hx.symm.trans (ggQTwoCl_decomp hsplit x))).2.symm

private noncomputable def ggQTwoClPsiFun {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (φ : MulAut ↥(Bs.subgroupOf K)) : ↥Bs →* ↥Bs where
  toFun b := ggQTwoClIota (φ (ggQTwoClPr hsplit b)) * ggQTwoClCtoBs (ggQTwoClC hsplit b)
  map_one' := by
    rw [ggQTwoClPr_one hEab hZ3 hsplit, ggQTwoClC_one hEab hZ3 hsplit, map_one, map_one,
      one_mul]
    exact Subtype.ext rfl
  map_mul' := fun b1 b2 => by
    rw [ggQTwoClPr_mul hEab hZ3 hsplit, ggQTwoClC_mul hEab hZ3 hsplit, map_mul, map_mul]
    have h2 : Commute (ggQTwoClCtoBs (ggQTwoClC hsplit b1))
        (ggQTwoClIota (φ (ggQTwoClPr hsplit b2))) :=
      isMulCommutative_iff.mp hEab.1 _ _
    calc (ggQTwoClIota (φ (ggQTwoClPr hsplit b1)) *
            ggQTwoClIota (φ (ggQTwoClPr hsplit b2))) *
          (ggQTwoClCtoBs (ggQTwoClC hsplit b1) * ggQTwoClCtoBs (ggQTwoClC hsplit b2))
        = ggQTwoClIota (φ (ggQTwoClPr hsplit b1)) *
            ((ggQTwoClIota (φ (ggQTwoClPr hsplit b2)) *
              ggQTwoClCtoBs (ggQTwoClC hsplit b1)) *
              ggQTwoClCtoBs (ggQTwoClC hsplit b2)) := by group
      _ = ggQTwoClIota (φ (ggQTwoClPr hsplit b1)) *
            ((ggQTwoClCtoBs (ggQTwoClC hsplit b1) *
              ggQTwoClIota (φ (ggQTwoClPr hsplit b2))) *
              ggQTwoClCtoBs (ggQTwoClC hsplit b2)) := by rw [← h2.eq]
      _ = (ggQTwoClIota (φ (ggQTwoClPr hsplit b1)) *
            ggQTwoClCtoBs (ggQTwoClC hsplit b1)) *
          (ggQTwoClIota (φ (ggQTwoClPr hsplit b2)) *
            ggQTwoClCtoBs (ggQTwoClC hsplit b2)) := by group

private theorem ggQTwoClPsiFun_injective {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (φ : MulAut ↥(Bs.subgroupOf K)) :
    Function.Injective (ggQTwoClPsiFun hEab hZ3 hsplit φ) := by
  intro b1 b2 h
  have hpr : ggQTwoClPr hsplit (ggQTwoClPsiFun hEab hZ3 hsplit φ b1) =
      ggQTwoClPr hsplit (ggQTwoClPsiFun hEab hZ3 hsplit φ b2) := by rw [h]
  have hc : ggQTwoClC hsplit (ggQTwoClPsiFun hEab hZ3 hsplit φ b1) =
      ggQTwoClC hsplit (ggQTwoClPsiFun hEab hZ3 hsplit φ b2) := by rw [h]
  change ggQTwoClPr hsplit (ggQTwoClIota (φ (ggQTwoClPr hsplit b1)) *
    ggQTwoClCtoBs (ggQTwoClC hsplit b1)) =
    ggQTwoClPr hsplit (ggQTwoClIota (φ (ggQTwoClPr hsplit b2)) *
    ggQTwoClCtoBs (ggQTwoClC hsplit b2)) at hpr
  change ggQTwoClC hsplit (ggQTwoClIota (φ (ggQTwoClPr hsplit b1)) *
    ggQTwoClCtoBs (ggQTwoClC hsplit b1)) =
    ggQTwoClC hsplit (ggQTwoClIota (φ (ggQTwoClPr hsplit b2)) *
    ggQTwoClCtoBs (ggQTwoClC hsplit b2)) at hc
  rw [ggQTwoClPr_Psi hEab hZ3 hsplit, ggQTwoClPr_Psi hEab hZ3 hsplit] at hpr
  rw [ggQTwoClC_Psi hEab hZ3 hsplit, ggQTwoClC_Psi hEab hZ3 hsplit] at hc
  have hp : ggQTwoClPr hsplit b1 = ggQTwoClPr hsplit b2 := φ.injective hpr
  rw [ggQTwoCl_decomp_self hsplit b1, ggQTwoCl_decomp_self hsplit b2, hp, hc]

private theorem ggQTwoClPsiFun_bijective [Finite G] {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (φ : MulAut ↥(Bs.subgroupOf K)) :
    Function.Bijective (ggQTwoClPsiFun hEab hZ3 hsplit φ) :=
  ⟨ggQTwoClPsiFun_injective hEab hZ3 hsplit φ,
    (Finite.injective_iff_surjective).mp (ggQTwoClPsiFun_injective hEab hZ3 hsplit φ)⟩

private noncomputable def ggQTwoClPsi [Finite G] {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c) :
    MulAut ↥(Bs.subgroupOf K) →* MulAut ↥Bs where
  toFun φ := MulEquiv.ofBijective (ggQTwoClPsiFun hEab hZ3 hsplit φ)
    (ggQTwoClPsiFun_bijective hEab hZ3 hsplit φ)
  map_one' := by
    apply MulEquiv.ext
    intro b
    change ggQTwoClIota ((1 : MulAut ↥(Bs.subgroupOf K)) (ggQTwoClPr hsplit b)) *
      ggQTwoClCtoBs (ggQTwoClC hsplit b) = b
    rw [show (1 : MulAut ↥(Bs.subgroupOf K)) (ggQTwoClPr hsplit b) =
      ggQTwoClPr hsplit b from rfl]
    exact (ggQTwoCl_decomp_self hsplit b).symm
  map_mul' φ ψ := by
    apply MulEquiv.ext
    intro b
    change ggQTwoClIota ((φ * ψ) (ggQTwoClPr hsplit b)) *
        ggQTwoClCtoBs (ggQTwoClC hsplit b) =
      ggQTwoClIota (φ (ggQTwoClPr hsplit (ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) *
        ggQTwoClCtoBs (ggQTwoClC hsplit b)))) *
      ggQTwoClCtoBs (ggQTwoClC hsplit (ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) *
        ggQTwoClCtoBs (ggQTwoClC hsplit b)))
    rw [ggQTwoClPr_Psi hEab hZ3 hsplit, ggQTwoClC_Psi hEab hZ3 hsplit]
    rfl

private theorem ggQTwoCl_conj_mem_of_mem {Bs K : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    {g : G} (hgK : g ∈ K)
    (hgE : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.normalizer (Bs.subgroupOf K))
    {b : G} (hb : b ∈ Bs) : g * b * g⁻¹ ∈ Bs := by
  obtain ⟨a, ha, c, hc, rfl⟩ := hsplit b hb
  have hc_comm : g * c * g⁻¹ = c := by
    have h := Subgroup.mem_centralizer_iff.mp hc.2 g hgK
    calc g * c * g⁻¹ = (g * c) * g⁻¹ := rfl
      _ = (c * g) * g⁻¹ := by rw [h]
      _ = c := by group
  have hconj : g * a * g⁻¹ ∈ Bs :=
    Subgroup.mem_subgroupOf.mp
      ((Subgroup.mem_normalizer_iff.mp hgE (⟨a, ha.2⟩ : ↥K)).mp
        (Subgroup.mem_subgroupOf.mpr ha.1))
  have hEq : g * (a * c) * g⁻¹ = (g * a * g⁻¹) * c := by
    calc g * (a * c) * g⁻¹ = (g * a * g⁻¹) * (g * c * g⁻¹) := by group
      _ = (g * a * g⁻¹) * c := by rw [hc_comm]
  rw [hEq]
  exact Bs.mul_mem hconj hc.1

private theorem ggQTwoCl_mem_normalizer_of_mem_normalizer_subgroupOf {Bs K : Subgroup G}
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    {g : G} (hgK : g ∈ K)
    (hgE : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.normalizer (Bs.subgroupOf K)) :
    g ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact ggQTwoCl_conj_mem_of_mem hsplit hgK hgE hb
  · intro hb
    have hgE_inv : (⟨g, hgK⟩ : ↥K)⁻¹ ∈ Subgroup.normalizer (Bs.subgroupOf K) :=
      (Subgroup.normalizer (Bs.subgroupOf K) : Subgroup ↥K).inv_mem hgE
    have h := ggQTwoCl_conj_mem_of_mem hsplit (K.inv_mem hgK) hgE_inv hb
    have hb_eq : g⁻¹ * (g * b * g⁻¹) * g = b := by group
    simpa only [inv_inv, hb_eq] using h

private theorem ggQTwoCl_mem_normalizer_subgroupOf_of_mem_normalizer {Bs K : Subgroup G}
    {g : G} (hgK : g ∈ K) (hgB : g ∈ Subgroup.normalizer (Bs : Set G)) :
    (⟨g, hgK⟩ : ↥K) ∈ Subgroup.normalizer (Bs.subgroupOf K) := by
  rw [Subgroup.mem_normalizer_iff] at hgB ⊢
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact hgB (x : G)

private theorem ggQTwoCl_Psi_apply_conj [Finite G] {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    {g : G} (hgK : g ∈ K)
    (hgE : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.normalizer (Bs.subgroupOf K)) (b : ↥Bs) :
    (ggQTwoClPsi hEab hZ3 hsplit
      ((Bs.subgroupOf K).normalizerMonoidHom ⟨⟨g, hgK⟩, hgE⟩) b : G) = g * (b : G) * g⁻¹ := by
  let ψ := (Bs.subgroupOf K).normalizerMonoidHom ⟨⟨g, hgK⟩, hgE⟩
  have hψ : ((ψ (ggQTwoClPr hsplit b) : ↥K) : G) =
      g * (ggQTwoClIota (ggQTwoClPr hsplit b) : G) * g⁻¹ := by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hc_comm : g * (ggQTwoClC hsplit b : G) * g⁻¹ = (ggQTwoClC hsplit b : G) := by
    have h := Subgroup.mem_centralizer_iff.mp (ggQTwoClC hsplit b).2.2 g hgK
    calc g * (ggQTwoClC hsplit b : G) * g⁻¹ = (g * (ggQTwoClC hsplit b : G)) * g⁻¹ := rfl
      _ = ((ggQTwoClC hsplit b : G) * g) * g⁻¹ := by rw [h]
      _ = (ggQTwoClC hsplit b : G) := by group
  change ((ψ (ggQTwoClPr hsplit b) : ↥K) : G) *
    (ggQTwoClC hsplit b : G) = g * (b : G) * g⁻¹
  rw [hψ]
  have hgc : g * (ggQTwoClC hsplit b : G) = (ggQTwoClC hsplit b : G) * g :=
    Subgroup.mem_centralizer_iff.mp (ggQTwoClC hsplit b).2.2 g hgK
  have hgc' : g⁻¹ * (ggQTwoClC hsplit b : G) = (ggQTwoClC hsplit b : G) * g⁻¹ := by
    have h := congrArg (fun t => g⁻¹ * t) hc_comm
    group at h
    simpa only [zpow_neg_one] using h.symm
  have h1 : (g * (ggQTwoClIota (ggQTwoClPr hsplit b) : G) * g⁻¹) *
      (ggQTwoClC hsplit b : G) =
      g * ((ggQTwoClIota (ggQTwoClPr hsplit b) : G) * (ggQTwoClC hsplit b : G)) * g⁻¹ := by
    calc (g * (ggQTwoClIota (ggQTwoClPr hsplit b) : G) * g⁻¹) *
          (ggQTwoClC hsplit b : G)
        = g * (ggQTwoClIota (ggQTwoClPr hsplit b) : G) *
            (g⁻¹ * (ggQTwoClC hsplit b : G)) := by group
      _ = g * (ggQTwoClIota (ggQTwoClPr hsplit b) : G) *
            ((ggQTwoClC hsplit b : G) * g⁻¹) := by rw [hgc']
      _ = g * ((ggQTwoClIota (ggQTwoClPr hsplit b) : G) * (ggQTwoClC hsplit b : G)) * g⁻¹ := by
            group
  rw [h1, ← ggQTwoCl_decomp hsplit b]

private theorem ggQTwoCl_automizer [Finite G] {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    {X : Subgroup G} (hXK : X ≤ K) :
    ggAutomizer X Bs = (ggAutomizer (X.subgroupOf K) (Bs.subgroupOf K)).map
      (ggQTwoClPsi hEab hZ3 hsplit) := by
  rw [ggAutomizer, ggAutomizer, MonoidHom.map_closure]
  congr 1
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, hgX, hgB, hφ⟩ := hφ
    have hgK : g ∈ K := hXK hgX
    have hgE : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.normalizer (Bs.subgroupOf K) :=
      ggQTwoCl_mem_normalizer_subgroupOf_of_mem_normalizer hgK hgB
    refine ⟨(Bs.subgroupOf K).normalizerMonoidHom ⟨⟨g, hgK⟩, hgE⟩, ?_, ?_⟩
    · refine ⟨⟨g, hgK⟩, Subgroup.mem_subgroupOf.mpr hgX, hgE, ?_⟩
      intro a
      rfl
    · ext b
      rw [hφ b]
      exact ggQTwoCl_Psi_apply_conj hEab hZ3 hsplit hgK hgE b
  · rintro ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hgX, hgE, hψ⟩ := hψ
    have hgK : ((g : ↥K) : G) ∈ K := g.2
    have hgB : ((g : ↥K) : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      ggQTwoCl_mem_normalizer_of_mem_normalizer_subgroupOf hsplit hgK hgE
    refine ⟨((g : ↥K) : G), Subgroup.mem_subgroupOf.mp hgX, hgB, ?_⟩
    have hψ_eq : ψ = (Bs.subgroupOf K).normalizerMonoidHom ⟨g, hgE⟩ := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simpa using congrArg Subtype.val (hψ a)
    rw [hψ_eq]
    exact ggQTwoCl_Psi_apply_conj hEab hZ3 hsplit hgK hgE

private theorem ggQTwoClPsi_injective [Finite G] {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c) :
    Function.Injective (ggQTwoClPsi hEab hZ3 hsplit) := by
  intro φ ψ h
  apply MulEquiv.ext
  intro x
  have hb := congrArg (fun θ : MulAut ↥Bs => θ (ggQTwoClIota x)) h
  change (ggQTwoClIota (φ (ggQTwoClPr hsplit (ggQTwoClIota x))) *
      ggQTwoClCtoBs (ggQTwoClC hsplit (ggQTwoClIota x))) =
    (ggQTwoClIota (ψ (ggQTwoClPr hsplit (ggQTwoClIota x))) *
      ggQTwoClCtoBs (ggQTwoClC hsplit (ggQTwoClIota x))) at hb
  rw [ggQTwoClPr_iota hEab hZ3 hsplit, ggQTwoClC_iota hEab hZ3 hsplit,
    ggQTwoClCtoBs_one] at hb
  simp only [mul_one] at hb
  exact ggQTwoClIota_injective hb


private theorem ggQTwoCl_swapEquiv_mul_self (t : ℕ) (i j : Fin t) :
    PlaneRaw.swapEquiv t i j * PlaneRaw.swapEquiv t i j = 1 := by
  ext u k
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq, PlaneRaw.swapEquiv_apply]
  have h : ∀ x : Fin t, Equiv.swap i j (Equiv.swap i j x) = x := fun x => by simp
  rw [h]

private theorem ggQTwoCl_card_ker {t : ℕ} (f : PlaneRaw.V t →ₗ[ZMod 3] ZMod 3)
    (hf : ∃ w : PlaneRaw.V t, f w = 1) :
    Nat.card {v : PlaneRaw.V t // f v = 0} * 3 = Nat.card (PlaneRaw.V t) := by
  obtain ⟨w, hw⟩ := hf
  have hcard : Nat.card ({v : PlaneRaw.V t // f v = 0} × ZMod 3) =
      Nat.card {v : PlaneRaw.V t // f v = 0} * 3 := by
    rw [Nat.card_prod, Nat.card_zmod]
  rw [← hcard]
  refine Nat.card_congr ?_
  refine
    { toFun := fun q => (q.1 : PlaneRaw.V t) + q.2 • w
      invFun := fun v => (⟨v - f v • w, ?_⟩, f v)
      left_inv := ?_
      right_inv := ?_ }
  · rw [map_sub, map_smul, hw, smul_eq_mul, mul_one, sub_self]
  · rintro ⟨⟨u, hu⟩, a⟩
    have h1 : u + a • w - f (u + a • w) • w = u := by
      rw [map_add, map_smul, hu, zero_add, hw, smul_eq_mul, mul_one]
      abel
    have h2 : f (u + a • w) = a := by
      rw [map_add, map_smul, hu, zero_add, hw, smul_eq_mul, mul_one]
    exact Prod.ext (Subtype.ext h1) h2
  · intro v
    change (v - f v • w) + f v • w = v
    abel

private theorem ggQTwoCl_card_fixed_neg (t : ℕ) (i : Fin t) :
    Nat.card {v : PlaneRaw.V t // PlaneRaw.negEquiv t i v = v} * 3 =
      Nat.card (PlaneRaw.V t) := by
  have hfix : Nat.card {v : PlaneRaw.V t // PlaneRaw.negEquiv t i v = v} =
      Nat.card {v : PlaneRaw.V t // v i = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun v => ?_))
    constructor
    · intro h
      have h1 := congrFun h i
      rw [PlaneRaw.negEquiv_apply, if_pos rfl] at h1
      exact (by decide : ∀ x : ZMod 3, -x = x → x = 0) _ h1
    · intro h
      funext k
      rw [PlaneRaw.negEquiv_apply]
      by_cases hk : k = i
      · rw [if_pos hk, hk, h, neg_zero]
      · rw [if_neg hk]
  rw [hfix]
  exact ggQTwoCl_card_ker
    { toFun := fun v : PlaneRaw.V t => v i
      map_add' := fun a b => rfl
      map_smul' := fun a b => rfl }
    ⟨fun k => if k = i then 1 else 0, by simp⟩

private theorem ggQTwoCl_card_fixed_swap {t : ℕ} {i j : Fin t} (hij : i ≠ j) :
    Nat.card {v : PlaneRaw.V t // PlaneRaw.swapEquiv t i j v = v} * 3 =
      Nat.card (PlaneRaw.V t) := by
  have hfix : Nat.card {v : PlaneRaw.V t // PlaneRaw.swapEquiv t i j v = v} =
      Nat.card {v : PlaneRaw.V t // v i - v j = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun v => ?_))
    constructor
    · intro h
      have h1 := congrFun h i
      rw [PlaneRaw.swapEquiv_apply, Equiv.swap_apply_left] at h1
      exact sub_eq_zero.mpr h1.symm
    · intro h
      have hvij : v i = v j := sub_eq_zero.mp h
      funext k
      rw [PlaneRaw.swapEquiv_apply]
      by_cases hki : k = i
      · rw [hki, Equiv.swap_apply_left, hvij]
      · by_cases hkj : k = j
        · rw [hkj, Equiv.swap_apply_right, hvij]
        · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hfix]
  exact ggQTwoCl_card_ker
    { toFun := fun v : PlaneRaw.V t => v i - v j
      map_add' := fun a b => by
        simp only [Pi.add_apply]
        abel
      map_smul' := fun a b => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_sub, RingHom.id_apply] }
    ⟨fun k => if k = i then 1 else 0, by simp [Ne.symm hij]⟩

private theorem ggQTwoClPr_iota_mul {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (a : ↥(Bs.subgroupOf K)) (c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) :
    ggQTwoClPr hsplit (ggQTwoClIota a * ggQTwoClCtoBs c) = a :=
  (ggQTwoCl_unique_alt hEab hZ3 hsplit
    (b := ggQTwoClIota a * ggQTwoClCtoBs c) (a' := a) (c' := c) rfl).1

private theorem ggQTwoClC_iota_mul {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (a : ↥(Bs.subgroupOf K)) (c : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) :
    ggQTwoClC hsplit (ggQTwoClIota a * ggQTwoClCtoBs c) = c :=
  (ggQTwoCl_unique_alt hEab hZ3 hsplit
    (b := ggQTwoClIota a * ggQTwoClCtoBs c) (a' := a) (c' := c) rfl).2

private noncomputable def ggQTwoClProdEquiv {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c) :
    ↥Bs ≃ ↥(Bs.subgroupOf K) × ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) where
  toFun b := (ggQTwoClPr hsplit b, ggQTwoClC hsplit b)
  invFun q := ggQTwoClIota q.1 * ggQTwoClCtoBs q.2
  left_inv b := (ggQTwoCl_decomp_self hsplit b).symm
  right_inv q := Prod.ext (ggQTwoClPr_iota_mul hEab hZ3 hsplit q.1 q.2)
    (ggQTwoClC_iota_mul hEab hZ3 hsplit q.1 q.2)

private theorem ggQTwoCl_card_bs {Bs K : Subgroup G} {t : ℕ}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (coord : Additive ↥(Bs.subgroupOf K) ≃+ PlaneRaw.V t) :
    Nat.card ↥Bs = Nat.card (PlaneRaw.V t) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
  refine (Nat.card_congr (ggQTwoClProdEquiv hEab hZ3 hsplit)).trans ?_
  rw [Nat.card_prod, card_eq_of_ggLin coord]

private theorem ggQTwoCl_psi_fixed_iff [Finite G] {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (ψ : MulAut ↥(Bs.subgroupOf K)) (b : ↥Bs) :
    ggQTwoClPsi hEab hZ3 hsplit ψ b = b ↔
      ψ (ggQTwoClPr hsplit b) = ggQTwoClPr hsplit b := by
  constructor
  · intro h
    have h1 : (ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) : G) * (ggQTwoClC hsplit b : G) =
        (ggQTwoClIota (ggQTwoClPr hsplit b) : G) * (ggQTwoClC hsplit b : G) := by
      have h2 : (ggQTwoClPsi hEab hZ3 hsplit ψ b : G) = (b : G) := congrArg Subtype.val h
      rw [ggQTwoCl_decomp hsplit b] at h2
      exact h2
    exact (ggQTwoCl_unique_decomp (a := ψ (ggQTwoClPr hsplit b))
      (a' := ggQTwoClPr hsplit b) (c := ggQTwoClC hsplit b) (c' := ggQTwoClC hsplit b)
      hEab hZ3 h1).1
  · intro h
    have h2 : ggQTwoClPsi hEab hZ3 hsplit ψ b =
        ggQTwoClIota (ggQTwoClPr hsplit b) * ggQTwoClCtoBs (ggQTwoClC hsplit b) := by
      change ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) * ggQTwoClCtoBs (ggQTwoClC hsplit b) = _
      rw [h]
    rw [h2]
    exact (ggQTwoCl_decomp_self hsplit b).symm

private theorem ggQTwoCl_card_fixed_psi [Finite G] {Bs K : Subgroup G} {t : ℕ}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (coord : Additive ↥(Bs.subgroupOf K) ≃+ PlaneRaw.V t)
    (ψ : MulAut ↥(Bs.subgroupOf K)) :
    Nat.card {b : ↥Bs // ggQTwoClPsi hEab hZ3 hsplit ψ b = b} =
      Nat.card {v : PlaneRaw.V t // ggLin (p := 3) coord ψ v = v} *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
  have h1 : Nat.card {b : ↥Bs // ggQTwoClPsi hEab hZ3 hsplit ψ b = b} =
      Nat.card {q : ↥(Bs.subgroupOf K) × ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) //
        ψ q.1 = q.1} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (ggQTwoClProdEquiv hEab hZ3 hsplit) (fun b => ?_))
    exact ggQTwoCl_psi_fixed_iff hEab hZ3 hsplit ψ b
  have h2 : Nat.card {q : ↥(Bs.subgroupOf K) × ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) //
      ψ q.1 = q.1} =
      Nat.card {a : ↥(Bs.subgroupOf K) // ψ a = a} *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun a => ψ a = a))
  have h3 : Nat.card {a : ↥(Bs.subgroupOf K) // ψ a = a} =
      Nat.card {v : PlaneRaw.V t // ggLin (p := 3) coord ψ v = v} :=
    card_fixed_ggLin (p := 3) coord ψ
  rw [h1, h2, h3]

private theorem ggQTwoCl_inv_decomp {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (b : ↥Bs) :
    ((b⁻¹ : ↥Bs) : G) = (ggQTwoClIota (ggQTwoClPr hsplit b)⁻¹ : G) *
      ((ggQTwoClC hsplit b)⁻¹ : G) := by
  have hcomm : ((ggQTwoClIota (ggQTwoClPr hsplit b) : G) * (ggQTwoClC hsplit b : G)) =
      ((ggQTwoClC hsplit b : G) * (ggQTwoClIota (ggQTwoClPr hsplit b) : G)) := by
    have hc : ((ggQTwoClC hsplit b : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) : G) ∈ Bs :=
      (ggQTwoClC hsplit b).2.1
    have ha : (ggQTwoClIota (ggQTwoClPr hsplit b) : G) ∈ Bs :=
      Subgroup.mem_subgroupOf.mp (ggQTwoClPr hsplit b).2
    exact (congrArg Subtype.val (isMulCommutative_iff.mp hEab.1
      ⟨_, hc⟩ ⟨_, ha⟩)).symm
  have hb : ((b⁻¹ : ↥Bs) : G) = ((b : ↥Bs) : G)⁻¹ := rfl
  rw [hb, ggQTwoCl_decomp hsplit b, hcomm, mul_inv_rev, map_inv]
  rfl

private theorem ggQTwoCl_psi_inv_data [Finite G] {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (ψ : MulAut ↥(Bs.subgroupOf K)) {b : ↥Bs}
    (h : ggQTwoClPsi hEab hZ3 hsplit ψ b = b⁻¹) :
    ψ (ggQTwoClPr hsplit b) = (ggQTwoClPr hsplit b)⁻¹ ∧
      ggQTwoClC hsplit b = (ggQTwoClC hsplit b)⁻¹ := by
  have h1 : (ggQTwoClIota (ψ (ggQTwoClPr hsplit b)) : G) * (ggQTwoClC hsplit b : G) =
      (ggQTwoClIota (ggQTwoClPr hsplit b)⁻¹ : G) * ((ggQTwoClC hsplit b)⁻¹ : G) := by
    have h2 : (ggQTwoClPsi hEab hZ3 hsplit ψ b : G) = ((b⁻¹ : ↥Bs) : G) :=
      congrArg Subtype.val h
    rw [ggQTwoCl_inv_decomp hEab hsplit b] at h2
    exact h2
  exact ggQTwoCl_unique_decomp (a := ψ (ggQTwoClPr hsplit b))
    (a' := (ggQTwoClPr hsplit b)⁻¹) (c := ggQTwoClC hsplit b)
    (c' := (ggQTwoClC hsplit b)⁻¹) hEab hZ3 h1

private theorem ggQTwoCl_isReflection_of [Finite G] {Bs K : Subgroup G} {t : ℕ}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (coord : Additive ↥(Bs.subgroupOf K) ≃+ PlaneRaw.V t)
    (ψ : MulAut ↥(Bs.subgroupOf K))
    (hT2 : ggLin (p := 3) coord ψ * ggLin (p := 3) coord ψ = 1)
    (hfix : Nat.card {v : PlaneRaw.V t // ggLin (p := 3) coord ψ v = v} * 3 =
      Nat.card (PlaneRaw.V t)) :
    GGIsReflection 3 (ggQTwoClPsi hEab hZ3 hsplit ψ) := by
  have hψ2 : ψ * ψ = 1 := by
    apply ggLin_injective (p := 3) coord
    rw [map_mul, hT2, map_one]
  refine ⟨?_, ?_⟩
  · rw [pow_two, ← map_mul, hψ2, map_one]
  · rw [ggQTwoCl_card_fixed_psi hEab hZ3 hsplit coord ψ,
      ggQTwoCl_card_bs hEab hZ3 hsplit coord]
    have harith : (Nat.card {v : PlaneRaw.V t // ggLin (p := 3) coord ψ v = v} *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) * 3 =
        (Nat.card {v : PlaneRaw.V t // ggLin (p := 3) coord ψ v = v} * 3) *
          Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by ring
    rw [harith, hfix]

private theorem ggQTwoCl_isComponentOf_subgroupOf {K X H : Subgroup G}
    (hX : IsComponentOf X K) (hKH : K ≤ H) :
    IsComponentOf (X.subgroupOf H) (K.subgroupOf H) := by
  have hXH : X ≤ H := hX.1.trans hKH
  have hle : X.subgroupOf H ≤ K.subgroupOf H := Subgroup.subgroupOf_mono H hX.1
  refine ⟨hle, ?_, ?_⟩
  · have hsub : (X.subgroupOf K).IsSubnormal := (IsSubnormal.iff_subgroupOf hX.1).mp hX.2.1
    let e : K ≃* K.subgroupOf H := (Subgroup.subgroupOfEquivOfLe hKH).symm
    have hmap : (X.subgroupOf K).map (e : K →* K.subgroupOf H) =
        (X.subgroupOf H).subgroupOf (K.subgroupOf H) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨(y : G), y.2⟩, hy, Subtype.ext (Subtype.ext rfl)⟩
    have hsn : ((X.subgroupOf H).subgroupOf (K.subgroupOf H)).IsSubnormal := by
      rw [← hmap]
      exact hsub.map (f := (e : K →* K.subgroupOf H)) e.surjective
    exact (IsSubnormal.iff_subgroupOf hle).mpr hsn
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXH) hX.2.2

private theorem ggQTwoCl_isReflection_neg [Finite G] {Bs K : Subgroup G} {t : ℕ}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (coord : Additive ↥(Bs.subgroupOf K) ≃+ PlaneRaw.V t)
    (e : MulAut ↥(Bs.subgroupOf K) ≃* (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t))
    (he : ∀ ψ : MulAut ↥(Bs.subgroupOf K), e ψ = ggLin (p := 3) coord ψ) (i : Fin t) :
    GGIsReflection 3 (ggQTwoClPsi hEab hZ3 hsplit (e.symm (PlaneRaw.negEquiv t i))) := by
  have hTe : ggLin (p := 3) coord (e.symm (PlaneRaw.negEquiv t i)) = PlaneRaw.negEquiv t i := by
    rw [← he]
    exact MulEquiv.apply_symm_apply e _
  refine ggQTwoCl_isReflection_of hEab hZ3 hsplit coord (e.symm (PlaneRaw.negEquiv t i))
    ?_ ?_
  · rw [hTe]
    exact PlaneRaw.negEquiv_mul_self t i
  · have hiff : Nat.card {v : PlaneRaw.V t //
        ggLin (p := 3) coord (e.symm (PlaneRaw.negEquiv t i)) v = v} =
        Nat.card {v : PlaneRaw.V t // PlaneRaw.negEquiv t i v = v} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun v => by rw [hTe]))
    rw [hiff]
    exact ggQTwoCl_card_fixed_neg t i

private theorem ggQTwoCl_isReflection_swap [Finite G] {Bs K : Subgroup G} {t : ℕ}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (coord : Additive ↥(Bs.subgroupOf K) ≃+ PlaneRaw.V t)
    (e : MulAut ↥(Bs.subgroupOf K) ≃* (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t))
    (he : ∀ ψ : MulAut ↥(Bs.subgroupOf K), e ψ = ggLin (p := 3) coord ψ)
    {i j : Fin t} (hij : i ≠ j) :
    GGIsReflection 3 (ggQTwoClPsi hEab hZ3 hsplit (e.symm (PlaneRaw.swapEquiv t i j))) := by
  have hTe : ggLin (p := 3) coord (e.symm (PlaneRaw.swapEquiv t i j)) =
      PlaneRaw.swapEquiv t i j := by
    rw [← he]
    exact MulEquiv.apply_symm_apply e _
  refine ggQTwoCl_isReflection_of hEab hZ3 hsplit coord (e.symm (PlaneRaw.swapEquiv t i j))
    ?_ ?_
  · rw [hTe]
    exact ggQTwoCl_swapEquiv_mul_self t i j
  · have hiff : Nat.card {v : PlaneRaw.V t //
        ggLin (p := 3) coord (e.symm (PlaneRaw.swapEquiv t i j)) v = v} =
        Nat.card {v : PlaneRaw.V t // PlaneRaw.swapEquiv t i j v = v} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun v => by rw [hTe]))
    rw [hiff]
    exact ggQTwoCl_card_fixed_swap hij

private theorem ggQTwoClC_eq_one_of_inv [Finite G] {Bs K : Subgroup G}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (ψ : MulAut ↥(Bs.subgroupOf K)) {v : ↥Bs}
    (h : ggQTwoClPsi hEab hZ3 hsplit ψ v = v⁻¹) :
    ggQTwoClC hsplit v = 1 := by
  have hCinv : ggQTwoClC hsplit v = (ggQTwoClC hsplit v)⁻¹ :=
    (ggQTwoCl_psi_inv_data hEab hZ3 hsplit ψ h).2
  have hC2 : ggQTwoClC hsplit v * ggQTwoClC hsplit v = 1 := by
    nth_rewrite 2 [hCinv]
    exact mul_inv_cancel (ggQTwoClC hsplit v)
  have hC3 : ggQTwoClC hsplit v ^ 3 = 1 := by
    apply Subtype.ext
    have hmem : ((ggQTwoClC hsplit v : ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) : G) ∈ Bs :=
      (ggQTwoClC hsplit v).2.1
    simpa using hEab.2 _ hmem
  have hsq : ggQTwoClC hsplit v = (ggQTwoClC hsplit v) ^ 3 * ((ggQTwoClC hsplit v) ^ 2)⁻¹ := by
    group
  rw [hsq, hC3, pow_two, hC2]
  simp

private theorem ggQTwoCl_fixed_clause {Bs K : Subgroup G} {t : ℕ}
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (coord : Additive ↥(Bs.subgroupOf K) ≃+ PlaneRaw.V t)
    (e : MulAut ↥(Bs.subgroupOf K) ≃* (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t))
    (he : ∀ ψ : MulAut ↥(Bs.subgroupOf K), e ψ = ggLin (p := 3) coord ψ)
    (v : ↥Bs)
    (hv : ∀ i : Fin t, e.symm (PlaneRaw.negEquiv t i) (ggQTwoClPr hsplit v) =
      ggQTwoClPr hsplit v) :
    (v : G) ∈ Subgroup.centralizer (K : Set G) := by
  have hzero : ∀ k : Fin t, coord (Additive.ofMul (ggQTwoClPr hsplit v)) k = 0 := by
    intro k
    have hTe : ggLin (p := 3) coord (e.symm (PlaneRaw.negEquiv t k)) = PlaneRaw.negEquiv t k := by
      rw [← he]
      exact MulEquiv.apply_symm_apply e _
    have hTw : PlaneRaw.negEquiv t k (coord (Additive.ofMul (ggQTwoClPr hsplit v))) =
        coord (Additive.ofMul (ggQTwoClPr hsplit v)) := by
      have h1 := ggLin_apply_ofMul (p := 3) coord (e.symm (PlaneRaw.negEquiv t k))
        (ggQTwoClPr hsplit v)
      rw [hv k] at h1
      rw [← hTe]
      exact h1
    have h2 := congrFun hTw k
    rw [PlaneRaw.negEquiv_apply, if_pos rfl] at h2
    exact (by decide : ∀ x : ZMod 3, -x = x → x = 0) _ h2
  have hcoord0 : coord (Additive.ofMul (ggQTwoClPr hsplit v)) = 0 := funext hzero
  have h0 : Additive.ofMul (ggQTwoClPr hsplit v) = 0 := by
    apply coord.injective
    rw [hcoord0, map_zero]
  have hpr : ggQTwoClPr hsplit v = 1 := by
    have h := Additive.ofMul.injective h0
    simpa using h
  have hv_eq : v = ggQTwoClCtoBs (ggQTwoClC hsplit v) :=
    (ggQTwoCl_decomp_self hsplit v).trans (by rw [hpr]; simp)
  rw [hv_eq]
  exact (ggQTwoClC hsplit v).2.2

private theorem ggQTwoCl_single_support [Finite G] {Bs K : Subgroup G} {t : ℕ}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (coord : Additive ↥(Bs.subgroupOf K) ≃+ PlaneRaw.V t)
    (e : MulAut ↥(Bs.subgroupOf K) ≃* (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t))
    (he : ∀ ψ : MulAut ↥(Bs.subgroupOf K), e ψ = ggLin (p := 3) coord ψ)
    (v : ↥Bs) (i₁ : Fin t)
    (hvinv : ggQTwoClPsi hEab hZ3 hsplit (e.symm (PlaneRaw.negEquiv t i₁)) v = v⁻¹) :
    ggQTwoClC hsplit v = 1 ∧
      (∀ i, i ≠ i₁ → coord (Additive.ofMul (ggQTwoClPr hsplit v)) i = 0) := by
  have hψpr : e.symm (PlaneRaw.negEquiv t i₁) (ggQTwoClPr hsplit v) =
      (ggQTwoClPr hsplit v)⁻¹ :=
    (ggQTwoCl_psi_inv_data hEab hZ3 hsplit _ hvinv).1
  refine ⟨ggQTwoClC_eq_one_of_inv hEab hZ3 hsplit _ hvinv, ?_⟩
  intro k hk
  have hneg : coord (Additive.ofMul ((ggQTwoClPr hsplit v)⁻¹)) =
      - coord (Additive.ofMul (ggQTwoClPr hsplit v)) := by
    rw [ofMul_inv, map_neg]
  have hTe : ggLin (p := 3) coord (e.symm (PlaneRaw.negEquiv t i₁)) =
      PlaneRaw.negEquiv t i₁ := by
    rw [← he]
    exact MulEquiv.apply_symm_apply e _
  have hTw : PlaneRaw.negEquiv t i₁ (coord (Additive.ofMul (ggQTwoClPr hsplit v))) =
      - coord (Additive.ofMul (ggQTwoClPr hsplit v)) := by
    have h1 := ggLin_apply_ofMul (p := 3) coord (e.symm (PlaneRaw.negEquiv t i₁))
      (ggQTwoClPr hsplit v)
    rw [hψpr, hneg] at h1
    rw [← hTe]
    exact h1
  have h2 := congrFun hTw k
  rw [PlaneRaw.negEquiv_apply, if_neg hk] at h2
  exact (by decide : ∀ x : ZMod 3, x = -x → x = 0) _ h2

private theorem ggQTwoCl_inf_centralizer_subgroupOf {K : Subgroup G} {v : G} (hvK : v ∈ K) :
    (K ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf K =
      Subgroup.centralizer ({⟨v, hvK⟩} : Set ↥K) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨x.2, congrArg Subtype.val h⟩

private theorem ggQTwoCl_component_clause [Finite G] {Bs K : Subgroup G} {t : ℕ}
    (hEab : IsElemAbelian 3 Bs)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K))
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (coord : Additive ↥(Bs.subgroupOf K) ≃+ PlaneRaw.V t)
    (e : MulAut ↥(Bs.subgroupOf K) ≃* (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t))
    (he : ∀ ψ : MulAut ↥(Bs.subgroupOf K), e ψ = ggLin (p := 3) coord ψ)
    (hframe : ∀ (u : ↥(Bs.subgroupOf K)) (i₁ : Fin t), u ≠ 1 →
      (∀ i, i ≠ i₁ → coord (Additive.ofMul u) i = 0) →
      ∀ X : Subgroup ↥K, IsComponentOf X (Subgroup.centralizer ({(u : ↥K)} : Set ↥K)) →
        (∃ i, PlaneRaw.negEquiv t i ∈
          (ggAutomizer X (Bs.subgroupOf K)).map (ggLin (p := 3) coord)) ∨
        ∃ i j, i ≠ j ∧ PlaneRaw.rotEquiv t i j ∈
          (ggAutomizer X (Bs.subgroupOf K)).map (ggLin (p := 3) coord))
    (v : ↥Bs) (i₁ : Fin t) (hv : v ≠ 1)
    (hvinv : ggQTwoClPsi hEab hZ3 hsplit (e.symm (PlaneRaw.negEquiv t i₁)) v = v⁻¹)
    (X : Subgroup G) (hX : IsComponentOf X (K ⊓ Subgroup.centralizer ({(v : G)} : Set G))) :
    (∃ i, ggQTwoClPsi hEab hZ3 hsplit (e.symm (PlaneRaw.negEquiv t i)) ∈ ggAutomizer X Bs) ∨
      ∃ i j, i ≠ j ∧
        ggQTwoClPsi hEab hZ3 hsplit (e.symm (PlaneRaw.rotEquiv t i j)) ∈ ggAutomizer X Bs := by
  obtain ⟨hC1, hcoord_zero⟩ :=
    ggQTwoCl_single_support hEab hZ3 hsplit coord e he v i₁ hvinv
  have hv_eq : v = ggQTwoClIota (ggQTwoClPr hsplit v) :=
    (ggQTwoCl_decomp_self hsplit v).trans (by rw [hC1]; simp)
  have hvK : (v : G) ∈ K := by
    rw [hv_eq]
    exact ((ggQTwoClPr hsplit v) : ↥K).2
  have hpr_ne : ggQTwoClPr hsplit v ≠ 1 := by
    intro h
    apply hv
    rw [hv_eq, h]
    rfl
  have hsub := ggQTwoCl_inf_centralizer_subgroupOf hvK
  have hvK_eq : (⟨v, hvK⟩ : ↥K) = ((ggQTwoClPr hsplit v) : ↥K) := by
    apply Subtype.ext
    exact congrArg (fun z : ↥Bs => (z : G)) hv_eq
  have hcompX : IsComponentOf (X.subgroupOf K)
      (Subgroup.centralizer ({⟨v, hvK⟩} : Set ↥K)) := by
    rw [← hsub]
    exact ggQTwoCl_isComponentOf_subgroupOf hX inf_le_left
  rw [hvK_eq] at hcompX
  have hAut := ggQTwoCl_automizer hEab hZ3 hsplit (hX.1.trans inf_le_left)
  have hkey : ∀ ψ : MulAut ↥(Bs.subgroupOf K),
      ggQTwoClPsi hEab hZ3 hsplit (e.symm (ggLin (p := 3) coord ψ)) =
        ggQTwoClPsi hEab hZ3 hsplit ψ := by
    intro ψ
    rw [← he, MulEquiv.symm_apply_apply]
  rcases hframe (ggQTwoClPr hsplit v) i₁ hpr_ne hcoord_zero (X.subgroupOf K) hcompX
    with ⟨i, hi⟩ | ⟨i, j, hij, hi⟩
  · left
    obtain ⟨ψ, hψmem, hψeq⟩ := Subgroup.mem_map.mp hi
    refine ⟨i, ?_⟩
    rw [hAut, ← hψeq, hkey ψ]
    exact Subgroup.mem_map.mpr ⟨ψ, hψmem, rfl⟩
  · right
    obtain ⟨ψ, hψmem, hψeq⟩ := Subgroup.mem_map.mp hi
    refine ⟨i, j, hij, ?_⟩
    rw [hAut, ← hψeq, hkey ψ]
    exact Subgroup.mem_map.mpr ⟨ψ, hψmem, rfl⟩

theorem ggQTwoClLocal_of_frameIn [Finite G] {Bs K : Subgroup G} (hEab : IsElemAbelian 3 Bs)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ K, ∃ c ∈ Bs ⊓ Subgroup.centralizer (K : Set G), b = a * c)
    (hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K)) {t : ℕ} (ht : 3 ≤ t)
    (hF : GGQTwoClFrameIn (Bs.subgroupOf K) t) : GGQTwoClLocal Bs K := by
  obtain ⟨coord, hcoord, hframeComp⟩ := hF
  let e : MulAut ↥(Bs.subgroupOf K) ≃* (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) :=
    MulEquiv.ofBijective (ggLin (p := 3) coord)
      ⟨ggLin_injective coord, ggLin_surjective coord⟩
  let Φ : (PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) →* MulAut ↥Bs :=
    (ggQTwoClPsi hEab hZ3 hsplit).comp e.symm.toMonoidHom
  have hPhi_apply : ∀ (T : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t) (b : ↥Bs),
      Φ T b = ggQTwoClIota (e.symm T (ggQTwoClPr hsplit b)) *
        ggQTwoClCtoBs (ggQTwoClC hsplit b) := fun T b => rfl
  refine ⟨t, Φ, ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x y h
    apply e.symm.injective
    exact ggQTwoClPsi_injective hEab hZ3 hsplit h
  ·
    have hAut := ggQTwoCl_automizer hEab hZ3 hsplit (le_refl K)
    rw [show K.subgroupOf K = ⊤ from Subgroup.subgroupOf_self K] at hAut
    rw [hAut, ← hcoord, Subgroup.map_map]
    have h1 : e.symm.toMonoidHom.comp (ggLin (p := 3) coord) = MonoidHom.id _ := by
      ext x a
      have h : (e.symm ((ggLin (p := 3) coord) x)) a = x a :=
        congrArg (fun z : MulAut ↥(Bs.subgroupOf K) => (z a : ↥(Bs.subgroupOf K)))
          (MulEquiv.symm_apply_apply e x)
      exact congrArg (fun z : ↥(Bs.subgroupOf K) => (z : G)) h
    have hcomp : Φ.comp (ggLin (p := 3) coord) = ggQTwoClPsi hEab hZ3 hsplit := by
      calc Φ.comp (ggLin (p := 3) coord)
          = (ggQTwoClPsi hEab hZ3 hsplit).comp
              (e.symm.toMonoidHom.comp (ggLin (p := 3) coord)) := rfl
        _ = (ggQTwoClPsi hEab hZ3 hsplit).comp (MonoidHom.id _) := by rw [h1]
        _ = ggQTwoClPsi hEab hZ3 hsplit := by rfl
    rw [hcomp]
  ·
    intro i
    exact ggQTwoCl_isReflection_neg hEab hZ3 hsplit coord e (fun _ => rfl) i
  ·
    intro i j hij
    exact ggQTwoCl_isReflection_swap hEab hZ3 hsplit coord e (fun _ => rfl) hij
  ·
    intro v hv
    exact ggQTwoCl_fixed_clause hsplit coord e (fun _ => rfl) v
      (fun i => (ggQTwoCl_psi_fixed_iff hEab hZ3 hsplit _ v).mp (hv i))
  ·
    intro v i₁ hv hvinv X hX
    exact ggQTwoCl_component_clause hEab hZ3 hsplit coord e (fun _ => rfl) hframeComp
      v i₁ hv hvinv X hX

end CFSG.StandardType

end
