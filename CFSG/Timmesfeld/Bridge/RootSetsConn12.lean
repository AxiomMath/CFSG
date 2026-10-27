module

public import CFSG.Timmesfeld.Bridge.RootSetsConn9

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem commute_self_mul_pow {y u : G} (hy2 : y * y = 1) (hu2 : u * u = 1) {n : ℕ}
    (hord : orderOf (y * u) = 2 * n) : Commute y ((y * u) ^ n) := by
  set r := y * u with hr
  have hyr : y * r * y⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, inv_eq_of_mul_eq_one_right hu2, inv_eq_of_mul_eq_one_right hy2,
      ← mul_assoc, hy2, one_mul]
  have hr2n : r ^ (2 * n) = 1 := by rw [← hord]; exact pow_orderOf_eq_one r
  have ht2 : r ^ n * r ^ n = 1 := by rw [← pow_add, ← two_mul, hr2n]
  have h1 : y * r ^ n * y⁻¹ = r ^ n := by
    rw [← conj_pow, hyr, inv_pow, inv_eq_of_mul_eq_one_right ht2]
  show y * r ^ n = r ^ n * y
  calc y * r ^ n = y * r ^ n * y⁻¹ * y := by group
    _ = r ^ n * y := by rw [h1]

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem mul_not_mem_qcore (hC : ConnCex D) (h : Step6 D a b c x z P) :
    a * b ∉ qcore D x P := by
  intro hab
  have hD := hC.setting.root
  have hz : z ∈ qcore D x P := ⟨_, h.z_mem_pCore hC, rfl⟩
  have hu2 := hC.mul_mul_self_of_commute h.ha h.hb h.hcab
  have hc : c = z * (a * b) := by
    rw [h.hz, mul_assoc, hu2, mul_one]
  exact h.not_mem_qcore hC h.hc (hc ▸ (qcore D x P).mul_mem hz hab)

theorem exists_not_class (hC : ConnCex D) (h : Step6 D a b c x z P) {e : G} (he : e ∈ D) :
    ∃ b' ∈ D, b' ∈ P ∧ b' * e ∉ qcore D x P := by
  by_contra hall
  push Not at hall
  apply h.mul_not_mem_qcore hC
  exact mul_mem_qcore_trans hC he (hall a h.ha h.haP)
    (mul_mem_qcore_comm hC h.hb he (hall b h.hb h.hbP))

theorem final_aux (hB : OddTranspBender) (h3 : Step6ThreeProductHyp) (hC : ConnCex D)
    (h : Step6 D a b c x z P) (hT : ThreeClasses D x P) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hPS : P ≤ S) {e : G} (he : e ∈ D) (heP : e ∈ P) {c₁ : G} (hc₁ : c₁ ∈ D) (hc₁S : c₁ ∈ S)
    (hc₁e : Commute c₁ e) (hc₁P : c₁ ∉ P) :
    (∀ ℓ ∈ D, ℓ ∈ P → ℓ * e ∉ qcore D x P → ¬ Commute c₁ ℓ) ∧
      c₁ ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ ℓ ∈ D, ℓ ∈ P → ℓ * e ∉ qcore D x P → c₁ * ℓ * c₁⁻¹ * e * ℓ ∈ qcore D x P := by
  have hD := hC.setting.root
  have hN := hC.setting.normal
  have hinv : c₁⁻¹ = c₁ := hD.inv_eq hc₁
  have hnc : ∀ ℓ ∈ D, ℓ ∈ P → ℓ * e ∉ qcore D x P → ¬ Commute c₁ ℓ := by
    intro ℓ hℓ hℓP hℓe hcomm
    exact hc₁P (h.mem_of_commute_of_threeClasses hB h3 hC hT hS2 hPS he hℓ heP hℓP
      (fun h' => hℓe (mul_mem_qcore_comm hC he hℓ h')) hc₁ hc₁S hc₁e hcomm)
  have hout : ∀ ℓ ∈ D, ℓ ∈ P → ℓ * e ∉ qcore D x P → c₁ * ℓ * c₁⁻¹ ∈ P := by
    intro ℓ hℓ hℓP hℓe
    have hle : Commute ℓ e := h.commute_of_mem hC hℓ he hℓP heP
    exact h.mem_of_commute_of_threeClasses hB h3 hC hT hS2 hPS he hℓ heP hℓP
      (fun h' => hℓe (mul_mem_qcore_comm hC he hℓ h')) (hN c₁ ℓ hℓ)
      (S.mul_mem (S.mul_mem hc₁S (hPS hℓP)) (S.inv_mem hc₁S))
      ((hc₁e.mul_left hle).mul_left hc₁e.inv_left)
      (commute_conj_of_isPGroup hC hS2 hc₁ hℓ hc₁S (hPS hℓP)).symm
  obtain ⟨b₀, hb₀, hb₀P, hb₀e⟩ := h.exists_not_class hC he
  have hcc : ∀ u : G, c₁ * (c₁ * u * c₁⁻¹) * c₁⁻¹ = u := fun u => by
    rw [hinv, ← mul_assoc, ← mul_assoc, hD.mul_self_eq_one hc₁, one_mul, mul_assoc,
      hD.mul_self_eq_one hc₁, mul_one]
  have hnorm : c₁ ∈ Subgroup.normalizer (P : Set G) := by
    refine h.mem_normalizer_of_conj_mem_L hC fun ℓ hℓ hℓP => ?_
    by_cases hℓe : ℓ * e ∈ qcore D x P
    · have hb₀c := hout b₀ hb₀ hb₀P hb₀e
      have hcomm : Commute (c₁ * ℓ * c₁⁻¹) b₀ := by
        have := (Commute.conj_iff c₁).2
          (h.commute_of_mem hC hℓ (hN c₁ b₀ hb₀) hℓP hb₀c)
        rwa [hcc] at this
      have hle : Commute ℓ e := h.commute_of_mem hC hℓ he hℓP heP
      exact h.mem_of_commute_of_threeClasses hB h3 hC hT hS2 hPS he hb₀ heP hb₀P
        (fun h' => hb₀e (mul_mem_qcore_comm hC he hb₀ h')) (hN c₁ ℓ hℓ)
        (S.mul_mem (S.mul_mem hc₁S (hPS hℓP)) (S.inv_mem hc₁S))
        ((hc₁e.mul_left hle).mul_left hc₁e.inv_left) hcomm
    · exact hout ℓ hℓ hℓP hℓe
  refine ⟨hnc, hnorm, fun ℓ hℓ hℓP hℓe => ?_⟩
  have hℓc := hout ℓ hℓ hℓP hℓe
  have hℓcD : c₁ * ℓ * c₁⁻¹ ∈ D := hN c₁ ℓ hℓ
  have heℓ : e * ℓ ∉ qcore D x P := fun h' => hℓe (mul_mem_qcore_comm hC he hℓ h')
  rcases hT e he heP ℓ hℓ hℓP heℓ _ hℓcD hℓc with hq | hq | hq
  · exfalso
    have h1 := h.conj_mul_mem_qcore hB h3 hC hnorm hℓcD he hℓc heP hq
    rw [hcc, hc₁e.eq, mul_inv_cancel_right] at h1
    exact hℓe h1
  · exfalso
    apply hnc ℓ hℓ hℓP hℓe
    exact h.commute_of_mul_conj_mem_qcore hC hc₁ hnorm hℓ hℓP
      (mul_mem_qcore_comm hC hℓcD hℓ hq)
  · exact hq

end Step6

end CFSG.Timmesfeld.Bridge
