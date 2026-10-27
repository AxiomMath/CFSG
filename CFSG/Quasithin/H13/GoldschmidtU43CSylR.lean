module

public import CFSG.Quasithin.H13.GoldschmidtU43CTheta
public import CFSG.Quasithin.H13.GoldschmidtU43CSyl

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

structure SylR {z : G} (h : Hyp z) (R : Subgroup ↥(Hz z)) : Prop where
  le_W : R ≤ h.Wsub
  card : Nat.card R = 9
  frattini : Subgroup.normalizer (R : Set ↥(Hz z)) ⊔ h.Wsub = ⊤

namespace Hyp

variable {z : G} (h : Hyp z)

theorem card_ker [Finite G] : Nat.card h.act.ker = 32 := by
  rw [h.ker_act, ← h.card_U]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Uz_le_Hz z)).toEquiv

theorem exists_SylR [Finite G] : ∃ R : Subgroup ↥(Hz z), SylR h R := by
  obtain ⟨R, h1, h2, h3⟩ := h.exists_sylowR
  exact ⟨R, ⟨h1, h2, h3⟩⟩

end Hyp

namespace SylR

variable {z : G} {h : Hyp z} {R : Subgroup ↥(Hz z)} (hR : SylR h R)
include hR

theorem inf_ker [Finite G] : R ⊓ h.act.ker = ⊥ := by
  have h1 : Nat.card ↥(R ⊓ h.act.ker) ∣ 9 := hR.card ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(R ⊓ h.act.ker) ∣ 32 :=
    h.card_ker ▸ Subgroup.card_dvd_of_le inf_le_right
  have h3 : Nat.card ↥(R ⊓ h.act.ker) ∣ Nat.gcd 9 32 := Nat.dvd_gcd h1 h2
  have h4 : Nat.card ↥(R ⊓ h.act.ker) = 1 := by
    have : Nat.gcd 9 32 = 1 := by norm_num
    rw [this] at h3
    exact Nat.dvd_one.mp h3
  exact Subgroup.card_eq_one.mp h4

theorem act_inj [Finite G] {r : ↥(Hz z)} (hr : r ∈ R) (h1 : h.act r = 1) : r = 1 := by
  have : r ∈ R ⊓ h.act.ker := ⟨hr, MonoidHom.mem_ker.mpr h1⟩
  rw [hR.inf_ker] at this
  exact (Subgroup.mem_bot.mp this)

theorem act_inj' [Finite G] {r r' : ↥(Hz z)} (hr : r ∈ R) (hr' : r' ∈ R)
    (e : h.act r = h.act r') : r = r' := by
  have := hR.act_inj (R.mul_mem (R.inv_mem hr) hr') (by rw [map_mul, map_inv, e]; simp)
  calc r = r * (r⁻¹ * r') := by rw [this]; simp
    _ = r' := by group

theorem pow_three [Finite G] {r : ↥(Hz z)} (hr : r ∈ R) : r ^ 3 = 1 := by
  have h1 : h.act r ∈ Rbar := h.mem_Wsub.1 (hR.le_W hr)
  exact hR.act_inj (pow_mem hr 3) (by rw [map_pow]; exact h1.2)

theorem act_onto [Finite G] {g : MulAut (Multiplicative V4)} (hg : g ∈ Rbar) :
    ∃ r ∈ R, h.act r = g := by
  have : Finite Rbar := Nat.finite_of_card_ne_zero (by rw [card_Rbar]; norm_num)
  let f : R → Rbar := fun r => ⟨h.act r, h.mem_Wsub.1 (hR.le_W r.2)⟩
  have hinj : Function.Injective f := by
    intro r r' e
    exact Subtype.ext (hR.act_inj' r.2 r'.2 (congrArg Subtype.val e))
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [card_Rbar, hR.card])
  obtain ⟨r, hr⟩ := hbij.2 ⟨g, hg⟩
  exact ⟨r, r.2, congrArg Subtype.val hr⟩

theorem comm [Finite G] {r r' : ↥(Hz z)} (hr : r ∈ R) (hr' : r' ∈ R) : r * r' = r' * r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥R)
    (by rw [hR.card]; norm_num)).is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩
  exact congrArg Subtype.val hc

theorem normalizer_inf_ker [Finite G] {n : ↥(Hz z)}
    (hn : n ∈ Subgroup.normalizer (R : Set ↥(Hz z))) (hk : n ∈ h.act.ker) :
    (n : G) = 1 ∨ (n : G) = z := by
  have hn1 : h.act n = 1 := MonoidHom.mem_ker.mp hk
  have hnU : (n : G) ∈ Uz z := h.mem_U_of_act_eq_one n hn1
  have hcomm : ∀ r ∈ R, n * r = r * n := by
    intro r hr
    have hr' : n * r * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn r).mp hr
    have e : n * r * n⁻¹ = r := by
      apply hR.act_inj' hr' hr
      rw [map_mul, map_mul, map_inv, hn1]
      simp
    calc n * r = (n * r * n⁻¹) * n := by group
      _ = r * n := by rw [e]
  by_contra hne
  push Not at hne
  have hξ : h.tv ⟨n, hnU⟩ ≠ 0 := fun e => by
    rcases (h.tv_eq_zero_iff _).1 e with e1 | e1
    exacts [hne.1 e1, hne.2 e1]
  obtain ⟨g, hg, hgξ⟩ := Rbar_fixed hξ
  obtain ⟨r, hr, rfl⟩ := hR.act_onto hg
  apply hgξ
  rw [← h.tv_conj r ⟨n, hnU⟩]
  congr 1
  apply Subtype.ext
  rw [coe_conjU]
  have hc : (n : G) * (r : G) = (r : G) * (n : G) := congrArg Subtype.val (hcomm r hr)
  show (r : G) * n * (r : G)⁻¹ = n
  calc (r : G) * n * (r : G)⁻¹ = ((n : G) * r) * (r : G)⁻¹ := by rw [hc]
    _ = n := by group

theorem frattini_elt [Finite G] (k : ↥(Hz z)) :
    ∃ x ∈ h.act.ker, ∃ n ∈ Subgroup.normalizer (R : Set ↥(Hz z)), k = x * n := by
  have := h.Wsub_normal
  have hk : k ∈ Subgroup.normalizer (R : Set ↥(Hz z)) ⊔ h.Wsub := by
    rw [hR.frattini]
    exact Subgroup.mem_top k
  obtain ⟨n₀, hn₀, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hk
  obtain ⟨r, hr, hrw⟩ := hR.act_onto (h.mem_Wsub.1 hw)
  have hx₀ : w * r⁻¹ ∈ h.act.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrw]
    simp
  refine ⟨n₀ * (w * r⁻¹) * n₀⁻¹, ?_, n₀ * r, ?_, by group⟩
  · have hker : h.act.ker.Normal := inferInstance
    exact hker.conj_mem _ hx₀ n₀
  · exact Subgroup.mul_mem _ hn₀ (Subgroup.le_normalizer hr)

end SylR

end CFSG.Quasithin.H13.U43
