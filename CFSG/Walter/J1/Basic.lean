module

public import CFSG.Walter.J1.Defs
public import CFSG.Walter.J1.A5Sub
public import CFSG.GroupTheory.CentralizerMap
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Walter.J1

namespace JankoHyp

variable {G : Type} [Group G] [Finite G] (h : JankoHyp G)

theorem t_mul_t : h.t * h.t = 1 := by
  rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]

theorem t_inv : h.t⁻¹ = h.t := inv_eq_of_mul_eq_one_right h.t_mul_t

theorem t_ne_one : h.t ≠ 1 := by
  intro h1
  have := h.orderOf_t
  rw [h1, orderOf_one] at this
  omega

theorem t_mem_centralizer : h.t ∈ Subgroup.centralizer ({h.t} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem commute_of_mem {x : G} (hx : x ∈ Subgroup.centralizer ({h.t} : Set G)) :
    x * h.t = h.t * x :=
  Subgroup.mem_centralizer_singleton_iff.mp hx

theorem commute_of_mem_F {x : G} (hx : x ∈ h.F) : x * h.t = h.t * x :=
  h.commute_of_mem (h.le_centralizer hx)

theorem mem_centralizer_t {x : G} :
    x ∈ Subgroup.centralizer ({h.t} : Set G) ↔ x ∈ h.F ∨ h.t * x ∈ h.F := by
  constructor
  · intro hx
    have hta : ∀ y ∈ h.F, h.t * y = y * h.t := fun y hy => (h.commute_of_mem_F hy).symm
    let H : Subgroup G :=
      { carrier := {y | y ∈ h.F ∨ h.t * y ∈ h.F}
        one_mem' := Or.inl h.F.one_mem
        mul_mem' := by
          intro a b ha hb
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (h.F.mul_mem ha hb)
          · right
            have : h.t * (a * b) = a * (h.t * b) := by
              rw [← mul_assoc, hta a ha, mul_assoc]
            rw [this]
            exact h.F.mul_mem ha hb
          · right
            rw [← mul_assoc]
            exact h.F.mul_mem ha hb
          · left
            have hta' : h.t * a = a * h.t := by
              have := hta _ ha
              calc h.t * a = h.t * (h.t * (h.t * a)) := by
                    rw [← mul_assoc, h.t_mul_t, one_mul]
                _ = h.t * ((h.t * a) * h.t) := by rw [this]
                _ = a * h.t := by rw [← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
            have : a * b = (h.t * a) * (h.t * b) := by
              rw [← mul_assoc, hta', mul_assoc a, h.t_mul_t, mul_one]
            rw [this]
            exact h.F.mul_mem ha hb
        inv_mem' := by
          intro a ha
          rcases ha with ha | ha
          · exact Or.inl (h.F.inv_mem ha)
          · right
            have hc : h.t * a = a * h.t := by
              have := (h.commute_of_mem_F ha)
              calc h.t * a = h.t * (h.t * (h.t * a)) := by
                    rw [← mul_assoc, h.t_mul_t, one_mul]
                _ = h.t * ((h.t * a) * h.t) := by rw [this]
                _ = a * h.t := by rw [← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
            have : h.t * a⁻¹ = (h.t * a)⁻¹ := by
              rw [mul_inv_rev, h.t_inv]
              calc h.t * a⁻¹ = a⁻¹ * (a * h.t) * a⁻¹ := by group
                _ = a⁻¹ * (h.t * a) * a⁻¹ := by rw [hc]
                _ = a⁻¹ * h.t := by group
            rw [this]
            exact h.F.inv_mem ha }
    have hle : Subgroup.zpowers h.t ⊔ h.F ≤ H := by
      refine sup_le ?_ (fun y hy => Or.inl hy)
      rw [Subgroup.zpowers_le]
      exact Or.inr (by rw [h.t_mul_t]; exact h.F.one_mem)
    rw [h.centralizer_eq] at hx
    exact hle hx
  · rintro (hx | hx)
    · exact h.le_centralizer hx
    · have : x = h.t * (h.t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ h.t_mem_centralizer (h.le_centralizer hx)

theorem mem_F_of_odd {x : G} (hx : x ∈ Subgroup.centralizer ({h.t} : Set G))
    (hodd : Odd (orderOf x)) : x ∈ h.F := by
  rcases h.mem_centralizer_t.mp hx with hx | hx
  · exact hx
  · exfalso
    set y := h.t * x
    have hxy : x = h.t * y := by rw [← mul_assoc, h.t_mul_t, one_mul]
    have hc : Commute h.t y := (h.commute_of_mem_F hx).symm
    obtain ⟨k, hk⟩ := hodd
    have h2 : h.t ^ 2 = 1 := by rw [← h.orderOf_t, pow_orderOf_eq_one]
    have h1 : (h.t * y) ^ (2 * k + 1) = 1 := by
      rw [← hk, ← hxy]
      exact pow_orderOf_eq_one x
    rw [hc.mul_pow, pow_succ h.t, pow_mul, h2, one_pow, one_mul] at h1
    apply h.t_not_mem
    have : h.t = (y ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact h.F.inv_mem (h.F.pow_mem hx _)

theorem le_F_of_odd {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({h.t} : Set G))
    (hodd : Odd (Nat.card K)) : K ≤ h.F := fun _ hx =>
  h.mem_F_of_odd (hK hx) (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard K hx))

theorem sylow_le_centralizer (S : Sylow 2 G) (htS : h.t ∈ S) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({h.t} : Set G) := by
  intro x hx
  have := h.abelian_sylow S
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨h.t, htS⟩))

theorem card_F : Nat.card h.F = 60 := A5Sub.card_eq h.iso

theorem disjoint_zpowers_F : Disjoint (Subgroup.zpowers h.t) h.F := by
  rw [Subgroup.disjoint_def]
  intro x hx hxF
  rcases (mem_zpowers_of_orderOf_eq_two h.orderOf_t).mp hx with rfl | rfl
  · rfl
  · exact absurd hxF h.t_not_mem

theorem card_centralizer : Nat.card (Subgroup.centralizer ({h.t} : Set G)) = 120 := by
  rw [h.centralizer_eq, sup_comm, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer,
    h.card_F, Nat.card_zpowers, h.orderOf_t]
  · rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rw [← h.commute_of_mem_F hx, mul_inv_cancel_right]
    exact hx
  · exact h.disjoint_zpowers_F.symm

include h in
theorem nonabelian : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ : ∃ x : h.F, orderOf x = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [h.card_F]; norm_num)
  have hx3 : (x : G) ^ 3 = 1 := by
    rw [← Subgroup.orderOf_coe] at hx
    rw [← hx, pow_orderOf_eq_one]
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hx
    omega
  obtain ⟨y, hyF, hy2, hy1, hyx⟩ := A5Sub.exists_inv h.iso x.2 hx1 (by
    rw [show (15 : ℕ) = 3 * 5 by norm_num, pow_mul, hx3, one_pow])
  rw [hcon y (x : G), mul_assoc, mul_inv_cancel, mul_one] at hyx
  have : (x : G) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hyx]
    exact mul_inv_cancel _
  have h1 : orderOf (x : G) ∣ 2 := orderOf_dvd_of_pow_eq_one this
  rw [Subgroup.orderOf_coe, hx] at h1
  omega

@[expose] noncomputable def conj (g : G) : JankoHyp G where
  isSimpleGroup := h.isSimpleGroup
  abelian_sylow := h.abelian_sylow
  t := g * h.t * g⁻¹
  orderOf_t := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_t]
  F := h.F.map (MulAut.conj g).toMonoidHom
  le_centralizer := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change g * x * g⁻¹ * (g * h.t * g⁻¹) = g * h.t * g⁻¹ * (g * x * g⁻¹)
    have := h.commute_of_mem_F hx
    calc g * x * g⁻¹ * (g * h.t * g⁻¹) = g * (x * h.t) * g⁻¹ := by group
      _ = g * (h.t * x) * g⁻¹ := by rw [this]
      _ = g * h.t * g⁻¹ * (g * x * g⁻¹) := by group
  t_not_mem := by
    rintro ⟨x, hx, hxt⟩
    apply h.t_not_mem
    have : x = h.t := by
      have := congrArg (fun y => g⁻¹ * y * g) hxt
      simpa [MulAut.conj_apply, mul_assoc] using this
    rwa [← this]
  centralizer_eq := by
    have := centralizer_singleton_map (MulAut.conj g) h.t
    rw [MulAut.conj_apply] at this
    rw [← this, h.centralizer_eq, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  iso := (Subgroup.equivMapOfInjective h.F (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans h.iso

@[simp] theorem conj_t (g : G) : (h.conj g).t = g * h.t * g⁻¹ := rfl

theorem conj_F (g : G) : (h.conj g).F = h.F.map (MulAut.conj g).toMonoidHom := rfl

theorem mem_conj_F {g x : G} : x ∈ (h.conj g).F ↔ g⁻¹ * x * g ∈ h.F := by
  rw [conj_F, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

end JankoHyp

end CFSG.Walter.J1
