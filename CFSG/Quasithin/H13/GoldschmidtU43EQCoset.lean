module

public import CFSG.Quasithin.H13.GoldschmidtU43EQRel
public import CFSG.Quasithin.H13.GoldschmidtU43EQGen
public import CFSG.Quasithin.H13.GoldschmidtU43ECent
public import CFSG.Quasithin.H13.GoldschmidtU43EQFix

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem exists_coset (n : ↥(Hz z)) :
    ∃ r ∈ S.R, ∃ w ∈ ({1, S.u, S.v, S.u * S.v} : Set ↥(Hz z)),
      S.hyp.act n = S.hyp.act w * S.hyp.act r := by
  classical
  have h := S.hyp
  set Φ := h.act.range with hΦ
  have hRΦ : Rbar ≤ Φ := fun g hg => by
    obtain ⟨r, -, hr⟩ := S.hR.act_onto hg
    exact ⟨r, hr⟩
  have hΦO : ∀ g ∈ Φ, g ∈ Oq := by
    rintro g ⟨x, rfl⟩
    exact h.act_mem_Oq x
  let Rb : Subgroup ↥Φ := Rbar.subgroupOf Φ
  have : Rb.Normal := ⟨fun r hr g => by
    have hr' : (r : MulAut (Multiplicative V4)) ∈ Rbar := hr
    exact conj_mem_Rbar (hΦO g g.2) hr'⟩
  have hcardRb : Nat.card Rb = 9 := by
    rw [← card_Rbar]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΦ).toEquiv
  have hcardQ : Nat.card (↥Φ ⧸ Rb) = 4 := by
    have h1 := Subgroup.card_mul_index Rb
    have h2 : Nat.card ↥Φ = 36 := h.card_range_act
    rw [hcardRb, h2] at h1
    rw [← Subgroup.index_eq_card]
    omega
  let au : ↥Φ := ⟨h.act S.u, ⟨S.u, rfl⟩⟩
  let av : ↥Φ := ⟨h.act S.v, ⟨S.v, rfl⟩⟩
  have hau2 : au * au = 1 := Subtype.ext (by
    show h.act S.u * h.act S.u = 1
    rw [← map_mul, S.uu, map_one])
  have hav2 : av * av = 1 := Subtype.ext (by
    show h.act S.v * h.act S.v = 1
    rw [← map_mul, S.vv, S.act_zK])
  have hau1 : (QuotientGroup.mk au : ↥Φ ⧸ Rb) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact not_mem_Rbar_of_sq (by simpa using congrArg Subtype.val hau2) S.act_u_ne_one
  have hav1 : (QuotientGroup.mk av : ↥Φ ⧸ Rb) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact not_mem_Rbar_of_sq (by simpa using congrArg Subtype.val hav2) S.act_v_ne_one
  have hauv : (QuotientGroup.mk au : ↥Φ ⧸ Rb) ≠ QuotientGroup.mk av := by
    rw [Ne, QuotientGroup.eq]
    have e : ((au⁻¹ * av : ↥Φ) : MulAut (Multiplicative V4)) = h.act (S.u * S.v) := by
      show (h.act S.u)⁻¹ * h.act S.v = h.act (S.u * S.v)
      rw [← map_inv, S.ui, map_mul]
    intro hmem
    have hmem' : ((au⁻¹ * av : ↥Φ) : MulAut (Multiplicative V4)) ∈ Rbar := hmem
    rw [e] at hmem'
    exact not_mem_Rbar_of_sq (by rw [← map_mul, S.uvuv, map_one]) S.act_uv_ne_one hmem'
  have hq := u43_eq_of_card_four hcardQ hau1 hav1 hauv
    (by rw [← QuotientGroup.mk_mul, hau2, QuotientGroup.mk_one])
    (QuotientGroup.mk (⟨h.act n, ⟨n, rfl⟩⟩ : ↥Φ))
  have key : ∀ a : ↥Φ,
      (QuotientGroup.mk (⟨h.act n, ⟨n, rfl⟩⟩ : ↥Φ) : ↥Φ ⧸ Rb) = QuotientGroup.mk a →
      ∃ ρ ∈ Rbar, h.act n = (a : MulAut (Multiplicative V4)) * ρ := by
    intro a hqa
    have hmem : (a⁻¹ * (⟨h.act n, ⟨n, rfl⟩⟩ : ↥Φ) : ↥Φ) ∈ Rb := QuotientGroup.eq.mp hqa.symm
    have hmem' : (a : MulAut (Multiplicative V4))⁻¹ * h.act n ∈ Rbar := hmem
    exact ⟨_, hmem', by group⟩
  have fin : ∀ w : ↥(Hz z), w ∈ ({1, S.u, S.v, S.u * S.v} : Set ↥(Hz z)) →
      (∃ ρ ∈ Rbar, h.act n = h.act w * ρ) →
      ∃ r ∈ S.R, ∃ w ∈ ({1, S.u, S.v, S.u * S.v} : Set ↥(Hz z)),
        S.hyp.act n = S.hyp.act w * S.hyp.act r := by
    rintro w hw ⟨ρ, hρ, hn⟩
    obtain ⟨r, hr, hrρ⟩ := S.hR.act_onto hρ
    exact ⟨r, hr, w, hw, by rw [hn, hrρ]⟩
  rcases hq with h1 | h1 | h1 | h1
  · obtain ⟨ρ, hρ, hn⟩ := key 1 (by rw [h1, QuotientGroup.mk_one])
    exact fin 1 (by simp) ⟨ρ, hρ, by rw [map_one, one_mul]; simpa using hn⟩
  · obtain ⟨ρ, hρ, hn⟩ := key au h1
    exact fin S.u (by simp) ⟨ρ, hρ, hn⟩
  · obtain ⟨ρ, hρ, hn⟩ := key av h1
    exact fin S.v (by simp) ⟨ρ, hρ, hn⟩
  · obtain ⟨ρ, hρ, hn⟩ := key (au * av) (by rw [h1, QuotientGroup.mk_mul])
    refine fin (S.u * S.v) (by simp) ⟨ρ, hρ, ?_⟩
    rw [map_mul]
    exact hn

omit [Finite G] in
theorem conj_σ₁_ne : ∀ w ∈ ({S.u, S.v, S.u * S.v} : Set ↥(Hz z)), w * S.σ₁ * w⁻¹ ≠ S.σ₁ := by
  have hs : S.σ₁ ≠ S.σ₁⁻¹ := by
    intro h
    apply S.σ₁_ne_one
    have h2 : S.σ₁ * S.σ₁ = 1 := by
      calc S.σ₁ * S.σ₁ = S.σ₁ * S.σ₁⁻¹ := by rw [← h]
        _ = 1 := by group
    calc S.σ₁ = S.σ₁ * S.σ₁ * S.σ₁ * (S.σ₁ * S.σ₁)⁻¹ := by group
      _ = 1 := by rw [S.σ₁_cube, h2]; group
  have hvσ : S.v * S.σ₁ * S.v⁻¹ = S.σ₁⁻¹ := by
    rw [← S.conj_v_inv, S.conj_v_σ₁]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · rw [S.conj_u_σ₁']
    exact S.σ₂_ne_σ₁
  · rw [hvσ]
    exact hs.symm
  · have e : S.u * S.v * S.σ₁ * (S.u * S.v)⁻¹ = (S.u * S.σ₁ * S.u⁻¹)⁻¹ := by
      calc S.u * S.v * S.σ₁ * (S.u * S.v)⁻¹ = S.u * (S.v * S.σ₁ * S.v⁻¹) * S.u⁻¹ := by group
        _ = S.u * S.σ₁⁻¹ * S.u⁻¹ := by rw [hvσ]
        _ = (S.u * S.σ₁ * S.u⁻¹)⁻¹ := by group
    rw [e, S.conj_u_σ₁']
    intro h
    apply S.σ₂_ne_σ₁_inv
    rw [← h]
    group

theorem exists_RY {n : ↥(Hz z)} (hn : (n : G) ∈ S.Cg1) :
    ∃ r ∈ S.R, ∃ k : ↥(Hz z), (k : G) ∈ S.Yg ∧ n = r * k := by
  have h := S.hyp
  obtain ⟨r, hr, w, hw, hact⟩ := S.exists_coset n
  have hnσ : n * S.σ₁ = S.σ₁ * n :=
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hn)
  have hrσ : r * S.σ₁ = S.σ₁ * r := S.hR.comm hr S.hσR
  have hw1 : w = 1 := by
    by_contra hw1
    have hw' : w ∈ ({S.u, S.v, S.u * S.v} : Set ↥(Hz z)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      tauto
    have hwN : w ∈ Subgroup.normalizer (S.R : Set ↥(Hz z)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
      rcases hw' with rfl | rfl | rfl
      · exact S.hu
      · exact S.hv
      · exact S.huv
    have hconj : w * S.σ₁ * w⁻¹ ∈ S.R :=
      (Subgroup.mem_normalizer_iff.mp hwN S.σ₁).mp S.hσR
    have hcomm : h.act w * h.act S.σ₁ = h.act S.σ₁ * h.act w := by
      have e1 : h.act n * h.act S.σ₁ = h.act S.σ₁ * h.act n := by
        rw [← map_mul, ← map_mul, hnσ]
      have e2 : h.act r * h.act S.σ₁ = h.act S.σ₁ * h.act r := by
        rw [← map_mul, ← map_mul, hrσ]
      rw [hact] at e1
      have e3 : h.act w * h.act S.σ₁ * h.act r = h.act S.σ₁ * h.act w * h.act r := by
        calc h.act w * h.act S.σ₁ * h.act r = h.act w * (h.act S.σ₁ * h.act r) := by group
          _ = h.act w * (h.act r * h.act S.σ₁) := by rw [e2]
          _ = h.act w * h.act r * h.act S.σ₁ := by group
          _ = h.act S.σ₁ * (h.act w * h.act r) := e1
          _ = h.act S.σ₁ * h.act w * h.act r := by group
      exact mul_right_cancel e3
    have heq : h.act (w * S.σ₁ * w⁻¹) = h.act S.σ₁ := by
      rw [map_mul, map_mul, map_inv, hcomm]
      group
    have := S.hR.act_inj' hconj S.hσR heq
    exact S.conj_σ₁_ne w hw' this
  subst hw1
  refine ⟨r, hr, r⁻¹ * n, ?_, by group⟩
  have hk1 : h.act (r⁻¹ * n) = 1 := by
    rw [map_mul, map_inv, hact, map_one, one_mul]
    group
  have hkU : ((r⁻¹ * n : ↥(Hz z)) : G) ∈ Uz z := by
    have : r⁻¹ * n ∈ h.act.ker := MonoidHom.mem_ker.mpr hk1
    rw [h.ker_act] at this
    exact this
  refine ⟨hkU, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have : (r⁻¹ * n) * S.σ₁ = S.σ₁ * (r⁻¹ * n) := by
    calc r⁻¹ * n * S.σ₁ = r⁻¹ * (n * S.σ₁) := by group
      _ = r⁻¹ * (S.σ₁ * n) := by rw [hnσ]
      _ = (r⁻¹ * S.σ₁) * n := by group
      _ = (S.σ₁ * r⁻¹) * n := by
          rw [show r⁻¹ * S.σ₁ = S.σ₁ * r⁻¹ by
            calc r⁻¹ * S.σ₁ = r⁻¹ * (S.σ₁ * r) * r⁻¹ := by group
              _ = r⁻¹ * (r * S.σ₁) * r⁻¹ := by rw [← hrσ]
              _ = S.σ₁ * r⁻¹ := by group]
      _ = S.σ₁ * (r⁻¹ * n) := by group
  exact congrArg Subtype.val this

theorem mem_Yg_of_pow {n : ↥(Hz z)} (hn : (n : G) ∈ S.Cg1) {m : ℕ} (hm : n ^ (2 ^ m) = 1) :
    (n : G) ∈ S.Yg := by
  have h := S.hyp
  obtain ⟨r, hr, k, hk, rfl⟩ := S.exists_RY hn
  have hkU : (k : G) ∈ Uz z := hk.1
  have hk1 : h.act k = 1 := by
    have : k ∈ h.act.ker := by
      rw [h.ker_act]
      exact hkU
    exact MonoidHom.mem_ker.mp this
  have hact : h.act (r * k) = h.act r := by rw [map_mul, hk1, mul_one]
  have h1 : (h.act r) ^ (2 ^ m) = 1 := by rw [← hact, ← map_pow, hm, map_one]
  have h3 : (h.act r) ^ 3 = 1 := by rw [← map_pow, S.hR.pow_three hr, map_one]
  have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
  have hord : orderOf (h.act r) = 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h3)
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  have hr1 : r = 1 := S.hR.act_inj hr (orderOf_eq_one_iff.mp hord)
  rw [hr1, one_mul]
  exact hk

theorem mem_Yg_of_pow_G {x : G} (hxH : x ∈ Hz z) (hxC : x ∈ S.Cg1) {m : ℕ}
    (hm : x ^ (2 ^ m) = 1) : x ∈ S.Yg :=
  S.mem_Yg_of_pow (n := ⟨x, hxH⟩) hxC (m := m) (Subtype.ext (by simpa using hm))

end JWSetup

end CFSG.Quasithin.H13.U43
