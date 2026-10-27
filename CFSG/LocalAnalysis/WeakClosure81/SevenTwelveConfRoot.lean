module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfMap

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private lemma sevenTwelveRoot_conj_commutator_mem {H : Subgroup G} {g a b : G}
    (hg : g ∈ H) (ha : a ∈ H) (hb : b ∈ H) :
    g * ⁅a, b⁆ * g⁻¹ ∈ ⁅H, H⁆ := by
  have hga : g * a * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg ha) (H.inv_mem hg)
  have hgb : g * b * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg hb) (H.inv_mem hg)
  have hmem := Subgroup.commutator_mem_commutator hga hgb
  have heq : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ :=
    conjugate_commutatorElement (g₁ := a) (g₂ := b) (g₃ := g)
  rw [heq]
  exact hmem

private lemma sevenTwelveRoot_commutator_normal (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  have key : ∀ l ∈ H, ∀ x ∈ ⁅H, H⁆, l * x * l⁻¹ ∈ ⁅H, H⁆ := by
    intro l hl x hx
    rw [Subgroup.commutator_def] at hx
    refine Subgroup.closure_induction (p := fun y _ => l * y * l⁻¹ ∈ ⁅H, H⁆) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨a, ha, b, hb, rfl⟩
      have hmem := Subgroup.commutator_mem_commutator (H₁ := H) (H₂ := H)
        (H.mul_mem (H.mul_mem hl ha) (H.inv_mem hl))
        (H.mul_mem (H.mul_mem hl hb) (H.inv_mem hl))
      have heq : l * ⁅a, b⁆ * l⁻¹ = ⁅l * a * l⁻¹, l * b * l⁻¹⁆ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rwa [heq]
    · simp
    · intro y z hy hz hypy hypz
      have heq : l * (y * z) * l⁻¹ = (l * y * l⁻¹) * (l * z * l⁻¹) := by group
      rw [heq]
      exact mul_mem hypy hypz
    · intro y hy hypy
      have heq : l * y⁻¹ * l⁻¹ = (l * y * l⁻¹)⁻¹ := by group
      rw [heq]
      exact inv_mem hypy
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key l hl x hx
  · intro hx
    have hmem : l⁻¹ * (l * x * l⁻¹) * (l⁻¹)⁻¹ ∈ ⁅H, H⁆ :=
      key l⁻¹ (H.inv_mem hl) (l * x * l⁻¹) hx
    convert hmem using 1
    group

private lemma sevenTwelveRoot_zpowers_eq_of_sq_eq_one {t x : G} (ht : t * t = 1)
    (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ht2 : t ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, ht]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, ht2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, ht2, one_zpow]
    simp

private lemma sevenTwelveRoot_mem_normalizer_zpowers_of_commute {q t : G} (h : Commute q t) :
    q ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hk : q * t ^ k * q⁻¹ = t ^ k := (h.zpow_right k).mul_inv_cancel
    rw [hk]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  · intro hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
    have hk' : q⁻¹ * t ^ k * q = t ^ k := (h.zpow_right k).inv_mul_cancel
    have hs_eq : s = t ^ k := by
      calc s = q⁻¹ * (q * s * q⁻¹) * q := by group
        _ = q⁻¹ * t ^ k * q := by rw [← hk]
        _ = t ^ k := hk'
    rw [hs_eq]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩

theorem sevenTwelveRoot_mem {t y n u : G} {m : ℕ} {L : Subgroup G}
    (hL : L = sevenTwelveGen (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹)
    (hy : y = n * t * u * t) (hx : u = n * (y * t * y⁻¹) * n⁻¹)
    (hn : n = (y ^ m * u) * t * (y ^ m * u)⁻¹) :
    t ∈ L ∧ y * t * y⁻¹ ∈ L ∧ n ∈ L ∧ u ∈ L ∧ y ∈ L := by
  have htL : t ∈ L := by
    rw [hL]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hytL : y * t * y⁻¹ ∈ L := by
    rw [hL]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (by
      rw [sevenTwelve_conjSubgroup_zpowers, inv_inv]
      exact Subgroup.mem_zpowers (y * t * y⁻¹)))
  have hnL : n ∈ L := by
    rw [hL]
    exact Subgroup.mem_sup_right (by
      rw [sevenTwelve_conjSubgroup_zpowers, inv_inv, ← hn]
      exact Subgroup.mem_zpowers n)
  have huL : u ∈ L := by
    rw [hx]
    exact mul_mem (mul_mem hnL hytL) (inv_mem hnL)
  have hyL : y ∈ L := by
    rw [hy]
    exact mul_mem (mul_mem (mul_mem hnL htL) huL) htL
  exact ⟨htL, hytL, hnL, huL, hyL⟩

theorem sevenTwelveRoot_perfect {t y n u : G} {m j : ℕ}
    (hy : y = n * t * u * t) (hx : u = n * (y * t * y⁻¹) * n⁻¹)
    (hn : n = (y ^ m * u) * t * (y ^ m * u)⁻¹)
    (hzech : y * t * y⁻¹ * t⁻¹ = y ^ j * t * (y ^ j)⁻¹) :
    ⁅sevenTwelveGen (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹,
        sevenTwelveGen (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹⁆ =
      sevenTwelveGen (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹ := by
  let L : Subgroup G := sevenTwelveGen (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹
  let C : Subgroup G := ⁅L, L⁆
  change C = L
  have hmem := sevenTwelveRoot_mem (L := L) rfl hy hx hn
  obtain ⟨htL, hytL, hnL, huL, hyL⟩ := hmem
  have hCnorm : L ≤ Subgroup.normalizer (C : Set G) :=
    sevenTwelveRoot_commutator_normal L
  have hxL : (y ^ j)⁻¹ ∈ L := L.inv_mem (L.pow_mem hyL j)
  have htC : t ∈ C := by
    have hmemC := sevenTwelveRoot_conj_commutator_mem (H := L) hxL hyL htL
    have heq : (y ^ j)⁻¹ * ⁅y, t⁆ * ((y ^ j)⁻¹)⁻¹ = t := by
      rw [commutatorElement_def, hzech]
      group
    rwa [← heq]
  have hytC : y * t * y⁻¹ ∈ C :=
    (Subgroup.mem_normalizer_iff.mp (hCnorm hyL) t).mp htC
  have hgL : y ^ m * u ∈ L := L.mul_mem (L.pow_mem hyL m) huL
  have hnC : n ∈ C := by
    have h := (Subgroup.mem_normalizer_iff.mp (hCnorm hgL) t).mp htC
    rw [← hn] at h
    exact h
  have hL_le_C : L ≤ C := by
    change Subgroup.zpowers t ⊔ conjSubgroup (Subgroup.zpowers t) y⁻¹ ⊔
      conjSubgroup (Subgroup.zpowers t) (y ^ m * u)⁻¹ ≤ C
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr htC
    · rw [sevenTwelve_conjSubgroup_zpowers, inv_inv]
      exact Subgroup.zpowers_le.mpr hytC
    · rw [sevenTwelve_conjSubgroup_zpowers, inv_inv, ← hn]
      exact Subgroup.zpowers_le.mpr hnC
  exact le_antisymm (Subgroup.commutator_le_self L) hL_le_C

theorem sevenTwelveRoot_ne {t y n u : G} {m : ℕ} (ht : t * t = 1)
    (hn : n = (y ^ m * u) * t * (y ^ m * u)⁻¹) (hyt : y * t * y⁻¹ ≠ t)
    (hc₁ : t * n ≠ n * t) (hc₂ : y * t * y⁻¹ * n ≠ n * (y * t * y⁻¹)) :
    conjSubgroup (Subgroup.zpowers t) y⁻¹ ≠ Subgroup.zpowers t ∧
      ⁅Subgroup.zpowers t, conjSubgroup (Subgroup.zpowers t) (y ^ m * u)⁻¹⁆ ≠ ⊥ ∧
      ⁅conjSubgroup (Subgroup.zpowers t) y⁻¹,
        conjSubgroup (Subgroup.zpowers t) (y ^ m * u)⁻¹⁆ ≠ ⊥ ∧
      y ∉ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  have hconj₂ : conjSubgroup (Subgroup.zpowers t) y⁻¹ =
      Subgroup.zpowers (y * t * y⁻¹) := by
    rw [sevenTwelve_conjSubgroup_zpowers, inv_inv]
  have hconj₃ : conjSubgroup (Subgroup.zpowers t) (y ^ m * u)⁻¹ =
      Subgroup.zpowers n := by
    rw [sevenTwelve_conjSubgroup_zpowers, inv_inv, ← hn]
  have hyt_eq_one : y * t * y⁻¹ = 1 → t = 1 := by
    intro h1
    calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    have hmem : y * t * y⁻¹ ∈ Subgroup.zpowers t := by
      rw [← heq, hconj₂]
      exact Subgroup.mem_zpowers (y * t * y⁻¹)
    rcases sevenTwelveRoot_zpowers_eq_of_sq_eq_one ht hmem with h1 | h1
    · exact hyt (by rw [h1, hyt_eq_one h1])
    · exact hyt h1
  · intro hbot
    have hmem : ⁅t, n⁆ ∈ ⁅Subgroup.zpowers t,
        conjSubgroup (Subgroup.zpowers t) (y ^ m * u)⁻¹⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t)
        (by rw [hconj₃]; exact Subgroup.mem_zpowers n)
    rw [hbot] at hmem
    exact hc₁ (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem))
  · intro hbot
    have hmem : ⁅y * t * y⁻¹, n⁆ ∈ ⁅conjSubgroup (Subgroup.zpowers t) y⁻¹,
        conjSubgroup (Subgroup.zpowers t) (y ^ m * u)⁻¹⁆ :=
      Subgroup.commutator_mem_commutator
        (by rw [hconj₂]; exact Subgroup.mem_zpowers (y * t * y⁻¹))
        (by rw [hconj₃]; exact Subgroup.mem_zpowers n)
    rw [hbot] at hmem
    exact hc₂ (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem))
  · intro hy
    have hmem : y * t * y⁻¹ ∈ Subgroup.zpowers t :=
      (Subgroup.mem_normalizer_iff.mp hy t).mp (Subgroup.mem_zpowers t)
    rcases sevenTwelveRoot_zpowers_eq_of_sq_eq_one ht hmem with h1 | h1
    · exact hyt (by rw [h1, hyt_eq_one h1])
    · exact hyt h1

theorem sevenTwelveConfig_of_root {t y n u : G} {m j : ℕ} {Q : Subgroup G} (ht : t * t = 1)
    (hy : y = n * t * u * t) (hx : u = n * (y * t * y⁻¹) * n⁻¹)
    (hn : n = (y ^ m * u) * t * (y ^ m * u)⁻¹)
    (hzech : y * t * y⁻¹ * t⁻¹ = y ^ j * t * (y ^ j)⁻¹) (hyt : y * t * y⁻¹ ≠ t)
    (hc₁ : t * n ≠ n * t) (hc₂ : y * t * y⁻¹ * n ≠ n * (y * t * y⁻¹))
    (hQ : IsPGroup 2 Q) (htQ : t ∈ Q) (hytQ : y * t * y⁻¹ ∈ Q) (hQt : ∀ q ∈ Q, q * t = t * q)
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G)) (hgenQ : ∀ H : Subgroup G, n ∈ H → Q ≤ H → H = ⊤) :
    SevenTwelveConfig (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹ y
      (sevenTwelveGen (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹ ⊓ Q) Q := by
  have hmem := sevenTwelveRoot_mem
    (L := sevenTwelveGen (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹) rfl hy hx hn
  obtain ⟨htL, hytL, hnL, huL, hyL⟩ := hmem
  obtain ⟨hne, hc₁₃, hc₂₃, hy_s⟩ := sevenTwelveRoot_ne ht hn hyt hc₁ hc₂
  have hperfect := sevenTwelveRoot_perfect hy hx hn hzech
  refine ⟨hne, hc₁₃, hc₂₃, hperfect, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsPGroup.to_inf_right hQ
  · exact Subgroup.zpowers_le.mpr ⟨htL, htQ⟩
  · rw [sevenTwelve_conjSubgroup_zpowers, inv_inv]
    exact Subgroup.zpowers_le.mpr ⟨hytL, hytQ⟩
  · exact inf_le_left
  · exact hQ
  · intro q hq
    exact sevenTwelveRoot_mem_normalizer_zpowers_of_commute (hQt q hq)
  · exact hgenQ (sevenTwelveGen (Subgroup.zpowers t) y⁻¹ (y ^ m * u)⁻¹ ⊔ Q)
      (Subgroup.mem_sup_left hnL) le_sup_right
  · exact hyL
  · exact hyQ
  · exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hyL, hyQ⟩
  · exact hy_s

end CFSG.LocalAnalysis.WeakClosure81

end
