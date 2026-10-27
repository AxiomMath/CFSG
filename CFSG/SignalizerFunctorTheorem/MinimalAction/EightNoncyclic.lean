module

public import CFSG.SignalizerFunctorTheorem.MinimalAction.EightSubgroup
public import CFSG.SignalizerFunctorTheorem.MinimalAction.Generation

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conj_centralizes {N : Subgroup G} (hN : N.Normal) {k : G}
    (hk : ∀ z ∈ N, z * k = k * z) (y : G) : ∀ z ∈ N, z * (y * k * y⁻¹) = y * k * y⁻¹ * z := by
  intro z hz
  have hz' : y⁻¹ * z * y ∈ N := by simpa using hN.conj_mem z hz y⁻¹
  calc z * (y * k * y⁻¹) = y * ((y⁻¹ * z * y) * k) * y⁻¹ := by group
    _ = y * (k * (y⁻¹ * z * y)) * y⁻¹ := by rw [hk _ hz']
    _ = y * k * y⁻¹ * z := by group

omit [Finite G] in
private theorem exists_zpow_mul_zpow_of_mem_sup {b d x : G} (hbd : Commute b d)
    (hx : x ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d) : ∃ i j : ℤ, x = b ^ i * d ^ j := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨i, 0, by rw [zpow_zero, mul_one]⟩
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨0, j, by rw [zpow_zero, one_mul]⟩
  | one => exact ⟨0, 0, by rw [zpow_zero, zpow_zero, mul_one]⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨i, j, rfl⟩ := ihx
    obtain ⟨k, l, rfl⟩ := ihy
    refine ⟨i + k, j + l, ?_⟩
    calc b ^ i * d ^ j * (b ^ k * d ^ l) = b ^ i * (d ^ j * b ^ k) * d ^ l := by
          simp only [mul_assoc]
      _ = b ^ i * (b ^ k * d ^ j) * d ^ l := by rw [(hbd.symm.zpow_zpow j k).eq]
      _ = b ^ (i + k) * d ^ (j + l) := by rw [zpow_add, zpow_add]; simp only [mul_assoc]
  | inv x _ ih =>
    obtain ⟨i, j, rfl⟩ := ih
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
    exact (hbd.symm.zpow_zpow (-j) (-i)).eq

private theorem card_le_three_mul_card_inf_centralizer {D W : Subgroup G} (hD : IsPGroup 3 D)
    (hW : Nat.card W = 4) (hDW : D ≤ Subgroup.normalizer (W : Set G)) :
    Nat.card D ≤ 3 * Nat.card ↥(D ⊓ Subgroup.centralizer (W : Set G)) := by
  let := conjugationAction D W hDW
  let φ : D →* Equiv.Perm W := MulAction.toPermHom D W
  have hker : φ.ker.map D.subtype = D ⊓ Subgroup.centralizer (W : Set G) := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have h1 := congrArg (fun p : Equiv.Perm W => (p ⟨z, hz⟩ : G)) (MonoidHom.mem_ker.mp hy)
      change (y : G) * z * (y : G)⁻¹ = z at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    · rintro ⟨hgD, hgC⟩
      refine ⟨⟨g, hgD⟩, MonoidHom.mem_ker.mpr (Equiv.ext fun z => Subtype.ext ?_), rfl⟩
      change g * (z : G) * g⁻¹ = z
      exact mul_inv_eq_iff_eq_mul.mpr (Subgroup.mem_centralizer_iff.mp hgC z z.2).symm
  have h2 : Nat.card ↥(D ⊓ Subgroup.centralizer (W : Set G)) = Nat.card φ.ker := by
    rw [← hker]
    exact Subgroup.card_map_of_injective D.subtype_injective
  have h3 : φ.ker.index ∣ 24 := by
    rw [Subgroup.index_ker]
    have h24 : Nat.card (Equiv.Perm W) = 24 := by simp [Nat.card_perm, hW, Nat.factorial]
    have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [h24] at this
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hD
  have h4 : φ.ker.index ∣ 3 ^ n := hn ▸ Subgroup.index_dvd_card φ.ker
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h4
  have hm1 : m ≤ 1 := by
    by_contra hm2
    have h9 : 3 ^ 2 ∣ 3 ^ m := pow_dvd_pow 3 (by omega)
    rw [← hm] at h9
    have := h9.trans h3
    norm_num at this
  have h5 : φ.ker.index ≤ 3 := by
    rw [hm]
    calc 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
      _ = 3 := by norm_num
  calc Nat.card D = Nat.card φ.ker * φ.ker.index := (Subgroup.card_mul_index _).symm
    _ ≤ Nat.card φ.ker * 3 := Nat.mul_le_mul_left _ h5
    _ = 3 * Nat.card ↥(D ⊓ Subgroup.centralizer (W : Set G)) := by rw [h2, mul_comm]

namespace EightSetting

variable {P : Subgroup G} {d : G} {W : Subgroup G}

omit [Finite G] in
private theorem exists_not_commute (h : EightSetting P d W) : ∃ z ∈ W, d * z ≠ z * d := by
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.ne_bot
  refine ⟨w, hw, fun hdw => hw1 (Subtype.ext (h.free w hw ?_))⟩
  rw [hdw, mul_inv_cancel_right]

private theorem pow_three_eq_one (h : EightSetting P d W) : d ^ 3 = 1 :=
  (h.star h.three h.exists_not_commute).2.2

private theorem eq_one_of_mem_zpowers_of_centralizes (h : EightSetting P d W) {y : G}
    (hy : y ∈ Subgroup.zpowers d) (hyc : ∀ z ∈ W, y * z = z * y) : y = 1 := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hd3 := h.pow_three_eq_one
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 h.ne_one
  have hmod : d ^ j = d ^ (j % 3) := by
    have := zpow_mod_orderOf d j
    rwa [hord, Nat.cast_ofNat, eq_comm] at this
  obtain ⟨z, hz, hdz⟩ := h.exists_not_commute
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2
  · rw [hmod, h0, zpow_zero]
  · rw [hmod, h1, zpow_one] at hyc
    exact absurd (hyc z hz) hdz
  · rw [hmod, h2, zpow_two] at hyc
    have hc : Commute (d * d) z := hyc z hz
    have h4 : d * d * (d * d) = d := by
      rw [← mul_assoc, ← pow_three', hd3, one_mul]
    have := (hc.mul_left hc).eq
    rw [h4] at this
    exact absurd this hdz

private theorem noncyclic_case_of_isPGroup (h : EightSetting P d W) {D : Subgroup G}
    (hD : IsPGroup 3 D) (hdD : d ∈ D) (hcyc : ¬ IsCyclic D) : False := by
  have hWn : W.Normal := h.normal_left
  have hd3 : d ^ 3 = 1 := h.pow_three_eq_one
  obtain ⟨z0, hz0, hdz0⟩ := h.exists_not_commute
  have hD9 : 9 ≤ Nat.card D := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hD
    rcases n with _ | _ | n
    · have h1 : Nat.card D = 1 := by simpa using hn
      have : Subsingleton D := (Nat.card_eq_one_iff_unique.mp h1).1
      exact (hcyc inferInstance).elim
    · have h3 : Nat.card D = 3 := by simpa using hn
      exact (hcyc (isCyclic_of_prime_card h3)).elim
    · rw [hn]
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup G, K = D ⊓ Subgroup.centralizer (W : Set G) := ⟨_, rfl⟩
  have hKmem : ∀ k, k ∈ K ↔ k ∈ D ∧ ∀ z ∈ W, z * k = k * z := by
    subst hKdef
    exact fun k =>
      Subgroup.mem_inf.trans (and_congr_right fun _ => Subgroup.mem_centralizer_iff)
  have hKD : K ≤ D := fun k hk => ((hKmem k).mp hk).1
  have hDW : D ≤ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer_of_normal
  have hcard := card_le_three_mul_card_inf_centralizer hD h.card_eq_four hDW
  rw [← hKdef] at hcard
  have hK3 : 3 ∣ Nat.card K := by
    rcases (hD.to_le hKD).card_eq_or_dvd with h1 | h3
    · omega
    · exact h3
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun y hy k hk => ?_
    obtain ⟨hkD, hkW⟩ := (hKmem k).mp hk
    exact (hKmem _).mpr ⟨D.mul_mem (D.mul_mem hy hkD) (D.inv_mem hy),
      conj_centralizes hWn hkW y⟩
  have hmod := centralizer_card_modEq 3 Nat.prime_three D K hD hDK
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(K ⊓ Subgroup.centralizer (D : Set G))) 3 ((hmod.dvd_iff dvd_rfl).mp hK3)
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp x.2
  obtain ⟨b, hbK, hbD', hb3⟩ : ∃ b : G, b ∈ K ∧ (∀ y ∈ D, y * b = b * y) ∧ orderOf b = 3 :=
    ⟨x, hxK, Subgroup.mem_centralizer_iff.mp hxC, by rw [Subgroup.orderOf_coe, hx]⟩
  have hbD : b ∈ D := hKD hbK
  have hbW : ∀ z ∈ W, z * b = b * z := ((hKmem b).mp hbK).2
  have hbd : Commute b d := (hbD' d hdD).symm
  have hb3' : b ^ 3 = 1 := by simpa [hb3] using pow_orderOf_eq_one b
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = Subgroup.zpowers b ⊔ Subgroup.zpowers d := ⟨_, rfl⟩
  have hbE : Subgroup.zpowers b ≤ E := by rw [hEdef]; exact le_sup_left
  have hdE : d ∈ E := by rw [hEdef]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hED : E ≤ D := by
    rw [hEdef]
    exact sup_le (Subgroup.zpowers_le.mpr hbD) (Subgroup.zpowers_le.mpr hdD)
  have hE : IsElemAbelian 3 E := by
    rw [hEdef]
    refine isElemAbelian_sup (isElemAbelian_zpowers hb3') (isElemAbelian_zpowers hd3) ?_
    intro a ha c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (hbd.zpow_zpow i j).eq
  have hS : Nat.card (Subgroup.zpowers b) = 3 := (Nat.card_zpowers b).trans hb3
  have hbC : b ∈ Subgroup.centralizer (W : Set G) := Subgroup.mem_centralizer_iff.mpr hbW
  have hdb : d ∉ Subgroup.zpowers b := fun hd =>
    hdz0 (Subgroup.mem_centralizer_iff.mp (Subgroup.zpowers_le.mpr hbC hd) z0 hz0).symm
  have hlt : Nat.card (Subgroup.zpowers b) < Nat.card E := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hbE) fun heq => hdb ?_
    rw [Subgroup.eq_of_le_of_card_ge hbE heq.ge]
    exact hdE
  have hE9 : 9 ≤ Nat.card E := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hD.to_le hED)
    rw [hS, hn] at hlt
    rw [hn]
    rcases n with _ | _ | n
    · norm_num at hlt
    · norm_num at hlt
    · calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcop : Nat.Coprime 3 (Nat.card P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.pgroup
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hEP : E ≤ Subgroup.normalizer (P : Set G) := by
    have := h.normal
    exact Subgroup.le_normalizer_of_normal
  have hfree : ∀ s ∈ E, s ∉ Subgroup.zpowers b → ∀ g ∈ P, s * g = g * s → g = 1 := by
    intro s hsE hsb g hgP hsg
    have hs3 : IsPGroup 3 (Subgroup.zpowers s) :=
      hD.to_le (Subgroup.zpowers_le.mpr (hED hsE))
    have hsW : ∃ z ∈ W, s * z ≠ z * s := by
      by_contra hne
      have hno : ∀ z ∈ W, s * z = z * s := fun z hz => by_contra fun hsz => hne ⟨z, hz, hsz⟩
      have hsE' : s ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers d := by rw [← hEdef]; exact hsE
      obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_sup hbd hsE'
      have hdj : d ^ j = 1 := by
        refine h.eq_one_of_mem_zpowers_of_centralizes (Subgroup.zpow_mem_zpowers d j)
          fun z hz => ?_
        have hzb : z * b ^ i = b ^ i * z :=
          (Commute.zpow_right (show Commute z b from hbW z hz) i).eq
        refine mul_left_cancel (a := b ^ i) ?_
        calc b ^ i * (d ^ j * z) = b ^ i * d ^ j * z := (mul_assoc _ _ _).symm
          _ = z * (b ^ i * d ^ j) := hno z hz
          _ = z * b ^ i * d ^ j := (mul_assoc _ _ _).symm
          _ = b ^ i * z * d ^ j := by rw [hzb]
          _ = b ^ i * (z * d ^ j) := mul_assoc _ _ _
      rw [hdj, mul_one] at hsb
      exact hsb (Subgroup.zpow_mem_zpowers b i)
    exact (h.star hs3 hsW).2.1 g hgP hsg
  have hPb := centralizes_of_elemAbelian_nine hE hE9 hcop hEP hbE hS hfree
  have hbP : b ∈ P := h.selfCentralizing b fun p hp =>
    (Subgroup.mem_centralizer_iff.mp (hPb hp) b (Subgroup.mem_zpowers b)).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h.pgroup ⟨b, hbP⟩
  rw [Subgroup.orderOf_mk, hb3] at hk
  rcases k with _ | k
  · norm_num at hk
  · rw [pow_succ] at hk
    omega

theorem noncyclic_case (h : EightSetting P d W) (D : Sylow 3 G)
    (hdD : d ∈ (D : Subgroup G)) (hcyc : ¬ IsCyclic (D : Subgroup G)) : False :=
  noncyclic_case_of_isPGroup h D.isPGroup' hdD hcyc

end EightSetting

end CFSG.SignalizerFunctorTheorem.MinimalAction
