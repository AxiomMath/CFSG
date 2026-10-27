module

public import CFSG.Quasithin.EmptyFaithful.E22QPlumb
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Dih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Two
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Cases

public section

namespace CFSG.Quasithin.Gap6R2.L3

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.E2.E22N
open scoped Pointwise

variable {G : Type} [Group G]

theorem oddComm_of_wr [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (h : Wr p T M J₁ J₂ z₁) :
    ∀ x ∈ M, Odd (orderOf x) → ∀ y ∈ M, Odd (orderOf y) → x * y = y * x := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hT2 : IsPGroup 2 T := h.sylow.2.1
  have hX := h.normal_X
  have hodd : Odd p := h.p_prime.odd_of_ne_two (by have := h.p_ge; omega)
  have h7 : 7 ≤ p ^ 1 := by simpa using h.p_ge
  obtain ⟨c₁, hc₁⟩ := exists_zpowers_of_odd_centralizer hodd (by norm_num) h7 h.psl₁
    (g := (⟨z₁, h.z₁_mem⟩ : ↥J₁)) (by rw [Subgroup.orderOf_mk]; exact h.z₁_ord)
  obtain ⟨t, htT, hJ₂⟩ := h.swap
  have htM : t ∈ M := h.T_le htT
  set c₂ : G := t * (c₁ : G) * t⁻¹ with hc₂
  have hc₁J : (c₁ : G) ∈ J₁ := c₁.2
  have h1 : ∀ u ∈ M ⊓ J₁, Odd (orderOf u) → ∃ k : ℤ, (c₁ : G) ^ k = u := by
    intro u hu hou
    have hmem : (⟨u, hu.2⟩ : ↥J₁) ∈ Subgroup.centralizer ({(⟨z₁, h.z₁_mem⟩ : ↥J₁)} :
        Set ↥J₁) := by
      have hu' : u ∈ Subgroup.centralizer ({z₁} : Set G) ⊓ J₁ := h.M_J₁ ▸ hu
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hu'.1)
    have hord : Odd (orderOf (⟨u, hu.2⟩ : ↥J₁)) := by rw [Subgroup.orderOf_mk]; exact hou
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc₁ _ hmem hord)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have h2 : ∀ u ∈ M ⊓ J₂, Odd (orderOf u) → ∃ k : ℤ, c₂ ^ k = u := by
    intro u hu hou
    have hu2 : u ∈ A1b.conjSub t J₁ := hJ₂ ▸ hu.2
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu2
    have hvu' : t * v * t⁻¹ = u := by simpa [MulAut.conj_apply] using hvu
    have hvM : v ∈ M := by
      have : v = t⁻¹ * u * t := by rw [← hvu']; group
      rw [this]
      exact M.mul_mem (M.mul_mem (M.inv_mem htM) hu.1) htM
    have hvodd : Odd (orderOf v) := by
      have := orderOf_conj_eq t v
      rw [hvu'] at this
      exact this ▸ hou
    obtain ⟨k, hk⟩ := h1 v ⟨hvM, hv⟩ hvodd
    refine ⟨k, ?_⟩
    rw [← hvu', ← hk]
    have := map_zpow (MulAut.conj t) (c₁ : G) k
    simp only [MulAut.conj_apply, hc₂] at this ⊢
    exact this.symm
  have hc₂J : c₂ ∈ J₂ := by
    rw [← hJ₂]
    exact Subgroup.mem_map.mpr ⟨(c₁ : G), hc₁J, by simp [MulAut.conj_apply, hc₂]⟩
  have hcomm : Commute (c₁ : G) c₂ := h.comm _ hc₁J _ hc₂J
  have hdec : ∀ x ∈ M, Odd (orderOf x) → ∃ i j : ℤ, x = (c₁ : G) ^ i * c₂ ^ j := by
    intro x hx hox
    have hXn : T ≤ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := fun s _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr hX]
      exact Subgroup.mem_top s
    have hxX : x ∈ J₁ ⊔ J₂ := by
      refine odd_mem_of_sup hT2 hXn ?_ hox
      rw [h.gen]
      exact Subgroup.mem_top x
    have hxM := h.M_X ⟨hx, hxX⟩
    have hnorm : M ⊓ J₁ ≤ Subgroup.normalizer ((M ⊓ J₂ : Subgroup G) : Set G) := by
      intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        have hc : u * w = w * u := h.comm u hu.2 w hw.2
        have : u * w * u⁻¹ = w := by rw [hc]; group
        rwa [this]
      · intro hw
        have hc : u⁻¹ * (u * w * u⁻¹) = (u * w * u⁻¹) * u⁻¹ := by
          have := h.comm u⁻¹ (J₁.inv_mem hu.2) _ hw.2
          exact this
        have : u * w * u⁻¹ = w := by
          have h3 : w = u⁻¹ * (u * w * u⁻¹) * u := by group
          rw [hc] at h3
          simpa using h3.symm
        rwa [this] at hw
    have hmul : ((M ⊓ J₁ ⊔ M ⊓ J₂ : Subgroup G) : Set G) =
        ((M ⊓ J₁ : Subgroup G) : Set G) * ((M ⊓ J₂ : Subgroup G) : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
    have hxmem : x ∈ ((M ⊓ J₁ ⊔ M ⊓ J₂ : Subgroup G) : Set G) := hxM
    rw [hmul] at hxmem
    obtain ⟨x₁, hx₁, x₂, hx₂, hxe⟩ := Set.mem_mul.mp hxmem
    have hc12 : x₁ * x₂ = x₂ * x₁ := h.comm x₁ hx₁.2 x₂ hx₂.2
    have hxo : ∀ m : ℕ, x ^ m = x₁ ^ m * x₂ ^ m := fun m => by
      rw [← hxe]
      exact (Commute.mul_pow hc12 m)
    have hodd' : Odd (orderOf x₁) ∧ Odd (orderOf x₂) := by
      have hm : x ^ orderOf x = 1 := pow_orderOf_eq_one x
      rw [hxo] at hm
      have hmem1 : x₁ ^ orderOf x ∈ J₁ ⊓ J₂ := by
        refine ⟨J₁.pow_mem hx₁.2 _, ?_⟩
        have : x₁ ^ orderOf x = (x₂ ^ orderOf x)⁻¹ := eq_inv_of_mul_eq_one_left hm
        rw [this]
        exact J₂.inv_mem (J₂.pow_mem hx₂.2 _)
      rw [h.disj, Subgroup.mem_bot] at hmem1
      have hmem2 : x₂ ^ orderOf x = 1 := by
        rw [hmem1, one_mul] at hm
        exact hm
      exact ⟨Odd.of_dvd_nat hox (orderOf_dvd_of_pow_eq_one hmem1),
        Odd.of_dvd_nat hox (orderOf_dvd_of_pow_eq_one hmem2)⟩
    obtain ⟨k₁, hk₁⟩ := h1 x₁ hx₁ hodd'.1
    obtain ⟨k₂, hk₂⟩ := h2 x₂ hx₂ hodd'.2
    exact ⟨k₁, k₂, by rw [hk₁, hk₂, hxe]⟩
  intro x hx hox y hy hoy
  obtain ⟨i, j, rfl⟩ := hdec x hx hox
  obtain ⟨i', j', rfl⟩ := hdec y hy hoy
  exact (Commute.mul_left (Commute.mul_right (Commute.zpow_zpow_self (c₁ : G) i i')
    (hcomm.zpow_zpow i j')) (Commute.mul_right (hcomm.symm.zpow_zpow j i')
    (Commute.zpow_zpow_self c₂ j j'))).eq


theorem oddComm_of_one_b [Finite G] (hOrb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    {K T N K0 : Subgroup G} (hmin : MinParabolic K T N) (hSQ : SQTKGroup ↥K)
    (hK0 : K0 ∈ cComp K) (hKK0 : K = K0 ⊔ T) (h : E22Case1b K T N K0) :
    ∀ a ∈ N, Odd (orderOf a) → ∀ b ∈ N, Odd (orderOf b) →
      a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold E22Case1b at h
  dsimp only at h
  obtain ⟨hJ, t, htT, hne, hMeq, p, hp, hp8, hpsl, hMK, -⟩ := h
  obtain ⟨J₂, z₁, hWr⟩ := plumb_exists_wr hOrb hmin hSQ hK0 hKK0 hJ ⟨t, htT, hne, hMeq⟩ hp hp8
    hpsl hMK
  have hsyl : IsSylowTwoOf T K := hmin.isSylow
  have hNK : N ≤ K := hmin.maximal.1.le
  have hTN : T ≤ N := hmin.le
  have hQT : pCoreOf 2 K ≤ T := CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hsyl
  have hQN : pCoreOf 2 K ≤ pCoreOf 2 N :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans hTN)
      (fun x hx => le_normalizer_pCoreOf 2 K (hNK hx)) (pCoreOf_isPGroup 2 K)
  intro a ha hoa b hb hob
  set π : ↥K →* E2.StarQuot N K := QuotientGroup.mk' ((kerIn N K).subgroupOf K) with hπ
  have haK : a ∈ K := hNK ha
  have hbK : b ∈ K := hNK hb
  have hma : π ⟨a, haK⟩ ∈ E2.star N K N :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ha)
  have hmb : π ⟨b, hbK⟩ ∈ E2.star N K N :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hb)
  have hoda : Odd (orderOf (π ⟨a, haK⟩)) := by
    refine Odd.of_dvd_nat (n := orderOf (⟨a, haK⟩ : ↥K)) ?_ (orderOf_map_dvd π _)
    rw [Subgroup.orderOf_mk]
    exact hoa
  have hodb : Odd (orderOf (π ⟨b, hbK⟩)) := by
    refine Odd.of_dvd_nat (n := orderOf (⟨b, hbK⟩ : ↥K)) ?_ (orderOf_map_dvd π _)
    rw [Subgroup.orderOf_mk]
    exact hob
  have hc := oddComm_of_wr hWr _ hma hoda _ hmb hodb
  have h1 : π (⟨a, haK⟩ * ⟨b, hbK⟩ * ⟨a, haK⟩⁻¹ * ⟨b, hbK⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ kerIn N K := by simpa using Subgroup.mem_subgroupOf.mp h2
  rw [hJ] at h3
  exact hQN h3

end CFSG.Quasithin.Gap6R2.L3
