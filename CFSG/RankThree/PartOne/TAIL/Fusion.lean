module

public import CFSG.RankThree.PartOne.TAIL.Power

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup

variable {G : Type} [Group G]

namespace SchemeHyp

variable [Finite G] {A B : Subgroup G} {c b d y₀ : G} {K M₀ : Subgroup G}
  (h : SchemeHyp G A B c b d y₀ K M₀)

include h in
theorem card_le_of_pgroup_centralizer {R : Subgroup G} (hR : R ≤ Subgroup.centralizer ({c} : Set G))
    (hp : IsPGroup 7 R) : Nat.card R ≤ 7 ^ 3 := by
  obtain ⟨hAc, _, hAidx⟩ := h.A_sylow_cent
  have h1 := Subgroup.relIndex_mul_card A (Subgroup.centralizer ({c} : Set G))
  rw [inf_eq_left.mpr hAc, h.A_card] at h1
  have h2 := Subgroup.relIndex_mul_card R (Subgroup.centralizer ({c} : Set G))
  rw [inf_eq_left.mpr hR] at h2
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at h2
  have e : 7 ^ k * R.relIndex (Subgroup.centralizer ({c} : Set G)) =
      7 ^ 3 * A.relIndex (Subgroup.centralizer ({c} : Set G)) := by
    rw [mul_comm, h2, ← h1]; ring
  have := pow_le_of_mul_eq hAidx e
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) this

variable {P : Subgroup G} (hP : PData A B y₀ P)

include h hP

theorem fusion
    (hadj : ∀ n ∈ Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G), ∃ l ∈ M₀, l * n ∈ Subgroup.normalizer (K : Set G))
    {g : G} (hg : g * c * g⁻¹ ∈ P) : ∃ q ∈ Qsub K P, g * c * g⁻¹ = c * q := by
  have hc'7 : (g * c * g⁻¹) ^ 7 = 1 := by rw [conj_pow, h.c_pow]; group
  have hc'Q : g * c * g⁻¹ ∉ Qsub K P := by
    intro hcQ
    have hle : conjSub g⁻¹ (Qsub K P) ≤ Subgroup.centralizer ({c} : Set G) := by
      intro x hx
      have hx' : g * x * g⁻¹ ∈ Qsub K P := by simpa [mem_conjSub] using hx
      have hcomm := h.Q_comm hP hx' hcQ
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : g * x * g⁻¹ * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := by group
      have e2 : g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
      rw [e1, e2] at hcomm
      exact mul_left_cancel (mul_right_cancel hcomm)
    have hcard : Nat.card (conjSub g⁻¹ (Qsub K P)) = 7 ^ 4 := by
      rw [conjSub_card, h.Q_card hP]
    have := h.card_le_of_pgroup_centralizer hle
      (conjSub_pgroup (hP.pgroup.to_le (Qsub_le K P)))
    rw [hcard] at this
    norm_num at this
  obtain ⟨j, q, hq, hcq⟩ := h.P_eq_zpowers_mul_Q hP hg
  have hc7 : c ^ (7 : ℤ) = 1 := by exact_mod_cast h.c_pow
  have hj7 : ¬ (7 : ℤ) ∣ j := by
    rintro ⟨k, hk⟩
    apply hc'Q
    have : c ^ j = 1 := by rw [hk, zpow_mul, hc7, one_zpow]
    rw [hcq, this, one_mul]
    exact hq
  have hq7 : q ^ 7 = 1 := by
    have := hc'7
    rw [hcq, h.pow7_eq hP hq] at this
    exact this
  have hqB : q ∈ B := h.Q_pow_eq_one hP hq hq7
  obtain ⟨t, w, htw⟩ := exists_inv_mod_seven hj7
  have hqt : q ^ t ∈ B := B.zpow_mem hqB t
  obtain ⟨u, hu⟩ := h.epsHom_surjective ⟨q ^ t, hqt⟩
  have hεu : eps c (u : G) = q ^ t := by
    have := congrArg Subtype.val hu
    rwa [SchemeHyp.epsHom_apply] at this
  have hu1 : (u : G) * c * (u : G)⁻¹ = q ^ t * c := by
    calc (u : G) * c * (u : G)⁻¹ = ((u : G) * c * (u : G)⁻¹ * c⁻¹) * c := by group
      _ = q ^ t * c := by rw [show (u : G) * c * (u : G)⁻¹ * c⁻¹ = eps c (u : G) from rfl, hεu]
  have hq7' : q ^ (7 : ℤ) = 1 := by exact_mod_cast hq7
  have hu2 : (u : G) * c ^ j * (u : G)⁻¹ = c ^ j * q := by
    have hcomm : Commute (q ^ t) c := Commute.zpow_left (h.c_comm_B hqB).symm t
    calc (u : G) * c ^ j * (u : G)⁻¹ = ((u : G) * c * (u : G)⁻¹) ^ j := (conj_zpow).symm
      _ = (q ^ t * c) ^ j := by rw [hu1]
      _ = (q ^ t) ^ j * c ^ j := hcomm.mul_zpow j
      _ = q * c ^ j := by
          rw [← zpow_mul, mul_comm t j, htw, zpow_add, zpow_one, zpow_mul, hq7', one_zpow, mul_one]
      _ = c ^ j * q := (Commute.zpow_left (show Commute c q from h.c_comm_B hqB) j).eq.symm
  have hg₁ : (u : G)⁻¹ * g * c * ((u : G)⁻¹ * g)⁻¹ = c ^ j := by
    calc (u : G)⁻¹ * g * c * ((u : G)⁻¹ * g)⁻¹ = (u : G)⁻¹ * (g * c * g⁻¹) * u := by group
      _ = (u : G)⁻¹ * (c ^ j * q) * u := by rw [hcq]
      _ = (u : G)⁻¹ * ((u : G) * c ^ j * (u : G)⁻¹) * u := by rw [hu2]
      _ = c ^ j := by group
  set g₁ : G := (u : G)⁻¹ * g with hg₁def
  have hA'le : conjSub g₁⁻¹ A ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    have hxa : g₁ * x * g₁⁻¹ ∈ A := by simpa [mem_conjSub] using hx
    have hcomm : g₁ * x * g₁⁻¹ * c ^ j = c ^ j * (g₁ * x * g₁⁻¹) :=
      h.A_comm hxa (A.zpow_mem h.c_mem j)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : g₁ * (x * c) * g₁⁻¹ = g₁ * (c * x) * g₁⁻¹ := by
      calc g₁ * (x * c) * g₁⁻¹ = (g₁ * x * g₁⁻¹) * (g₁ * c * g₁⁻¹) := by group
        _ = (g₁ * x * g₁⁻¹) * c ^ j := by rw [hg₁]
        _ = c ^ j * (g₁ * x * g₁⁻¹) := hcomm
        _ = (g₁ * c * g₁⁻¹) * (g₁ * x * g₁⁻¹) := by rw [hg₁]
        _ = g₁ * (c * x) * g₁⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)
  obtain ⟨x, hxC, hx⟩ := exists_conj_sylow (C := Subgroup.centralizer ({c} : Set G))
    (P₁ := conjSub g₁⁻¹ A) (P₂ := A) (conjSub_sylow h.A_sylow_cent hA'le) h.A_sylow_cent
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hnA : g₁ * x⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hx y, mem_conjSub]
    have e : (g₁⁻¹)⁻¹ * (x⁻¹ * y * x) * g₁⁻¹ = g₁ * x⁻¹ * y * (g₁ * x⁻¹)⁻¹ := by group
    rw [e]
  have hncn : (g₁ * x⁻¹) * c * (g₁ * x⁻¹)⁻¹ = c ^ j := by
    calc (g₁ * x⁻¹) * c * (g₁ * x⁻¹)⁻¹ = g₁ * (x⁻¹ * c * x) * g₁⁻¹ := by group
      _ = g₁ * c * g₁⁻¹ := by
          have : x⁻¹ * c * x = c := by
            calc x⁻¹ * c * x = x⁻¹ * (c * x) := by group
              _ = x⁻¹ * (x * c) := by rw [hxc]
              _ = c := by group
          rw [this]
      _ = c ^ j := hg₁
  have hnN : g₁ * x⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    refine mem_normalizer_of_conj_mem (Subgroup.zpowers c) fun y hy => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : (g₁ * x⁻¹) * c ^ i * (g₁ * x⁻¹)⁻¹ = (c ^ j) ^ i := by
      rw [← hncn, conj_zpow]
    rw [this, ← zpow_mul]
    exact Subgroup.mem_zpowers_iff.mpr ⟨j * i, rfl⟩
  obtain ⟨l, hlM, hln⟩ := hadj (g₁ * x⁻¹) ⟨hnA, hnN⟩
  have hlc : l * c * l⁻¹ = c := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (h.M₀_cent hlM)
    calc l * c * l⁻¹ = (c * l) * l⁻¹ := by rw [this]
      _ = c := by group
  have hlnc : (l * (g₁ * x⁻¹)) * c * (l * (g₁ * x⁻¹))⁻¹ = c ^ j := by
    calc (l * (g₁ * x⁻¹)) * c * (l * (g₁ * x⁻¹))⁻¹
        = l * ((g₁ * x⁻¹) * c * (g₁ * x⁻¹)⁻¹) * l⁻¹ := by group
      _ = l * c ^ j * l⁻¹ := by rw [hncn]
      _ = (l * c * l⁻¹) ^ j := (conj_zpow).symm
      _ = c ^ j := by rw [hlc]
  have hcj : c ^ j = c := by
    rw [← hlnc]
    exact h.K_data.out_central _ hln (by rw [hlnc]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) j)
  exact ⟨q, hq, by rw [hcq, hcj]⟩

end SchemeHyp

end CFSG.RankThree.PartOne.TAIL
