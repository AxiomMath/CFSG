module

public import CFSG.Quasithin.H13.GoldschmidtU43EAbel1

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem eq_closure_of_card_nine [Finite G] {B : Subgroup G} (hB : Nat.card B = 9) {σ ρ : G}
    (hσ : σ ∈ B) (hρ : ρ ∈ B) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hn : ρ ∉ Subgroup.zpowers σ) :
    B = Subgroup.closure {σ, ρ} := by
  have hle : Subgroup.closure ({σ, ρ} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [hσ, hρ]
  have hzσ : Subgroup.zpowers σ ≤ Subgroup.closure ({σ, ρ} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Or.inl rfl)
  have hcardσ : Nat.card (Subgroup.zpowers σ) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hσ3 hσ1
  have hd : Nat.card (Subgroup.closure ({σ, ρ} : Set G)) ∣ 9 := hB ▸ Subgroup.card_dvd_of_le hle
  have h3 : 3 ∣ Nat.card (Subgroup.closure ({σ, ρ} : Set G)) :=
    hcardσ ▸ Subgroup.card_dvd_of_le hzσ
  have hne3 : Nat.card (Subgroup.closure ({σ, ρ} : Set G)) ≠ 3 := by
    intro h
    have heq : Subgroup.zpowers σ = Subgroup.closure ({σ, ρ} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hzσ (by rw [h, hcardσ])
    apply hn
    rw [heq]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hdiv : Nat.card (Subgroup.closure ({σ, ρ} : Set G)) ∈ Nat.divisors 9 :=
    Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
  have : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [this] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have h9 : Nat.card (Subgroup.closure ({σ, ρ} : Set G)) = 9 := by
    rcases hdiv with h | h | h
    · rw [h] at h3
      omega
    · exact absurd h hne3
    · exact h
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hB, h9])).symm

theorem mem_zpowers_of_pow_three {K : Type} [Group K] {g : K} (h : g ^ 3 = 1) {x : K}
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g ∨ x = g⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : g ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact h
  have e : g ^ k = g ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul, h3, one_zpow, mul_one]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · left
    rw [e, h0]
    simp
  · right
    left
    rw [e, h1]
    simp
  · right
    right
    rw [e, h2]
    have : g ^ (2 : ℤ) * g = 1 := by rw [← zpow_add_one]; exact h3
    exact eq_inv_of_mul_eq_one_left this

namespace JWSetup

variable {z : G} (S : JWSetup z)
include S

noncomputable def sig : G := ((S.σ₁ * S.σ₂ : ↥(Hz z)) : G)

theorem sig_mem_Tg : S.sig ∈ S.Tg := S.coe_mem_Tg (mul_mem S.hσR S.σ₂_mem)

theorem sig_ne_one : S.sig ≠ 1 := fun h => S.σ₁σ₂_ne_one (Subtype.ext h)

theorem sig_comm_z : S.sig * z = z * S.sig := z_comm_H (S.σ₁ * S.σ₂)

theorem sig_comm_u : S.sig * (S.u : G) = (S.u : G) * S.sig :=
  congrArg Subtype.val S.u_comm_σ₁σ₂.symm

variable [Finite G]

theorem sig_pow_three : S.sig ^ 3 = 1 := S.pow_three_Tg S.sig_mem_Tg

theorem sig_mem_T1 : S.sig ∈ S.T1 := by
  have : S.sig ∈ S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G) :=
    ⟨S.Tg_le_Mg S.sig_mem_Tg, Subgroup.mem_centralizer_singleton_iff.mpr S.sig_comm_u⟩
  exact this

theorem sig_mem_T2 : S.sig ∈ S.T2 := by
  have hc : S.sig * (z * (S.u : G)) = (z * (S.u : G)) * S.sig := by
    calc S.sig * (z * (S.u : G)) = (S.sig * z) * (S.u : G) := by group
      _ = (z * S.sig) * (S.u : G) := by rw [S.sig_comm_z]
      _ = z * (S.sig * (S.u : G)) := by group
      _ = z * ((S.u : G) * S.sig) := by rw [S.sig_comm_u]
      _ = z * (S.u : G) * S.sig := by group
  have : S.sig ∈ S.Mg ⊓ Subgroup.centralizer ({z * (S.u : G)} : Set G) :=
    ⟨S.Tg_le_Mg S.sig_mem_Tg, Subgroup.mem_centralizer_singleton_iff.mpr hc⟩
  exact this

theorem comm_mem_Tg {x y : G} (hx : x ∈ S.Mg) (hy : y ∈ S.Mg) : x⁻¹ * y⁻¹ * x * y ∈ S.Tg := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup ↥S.Mg := S.Tg.subgroupOf S.Mg
  have hN : N.Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ S.Tg := hn
    have hc := (S.mem_Cg).1 (S.Mg_le_Cg g.2) _ hn'
    show (g : G) * n * (g : G)⁻¹ ∈ S.Tg
    have e : (g : G) * n * (g : G)⁻¹ = n := by
      rw [← hc]
      group
    rw [e]
    exact hn'⟩
  have hNcard : Nat.card N = 9 := by
    rw [← S.card_Tg]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.Tg_le_Mg).toEquiv
  have hQ : Nat.card (↥S.Mg ⧸ N) = 9 := by
    have h1 := Subgroup.card_mul_index N
    rw [hNcard, S.card_Mg_eq_81] at h1
    rw [← Subgroup.index_eq_card]
    omega
  have hcomm : IsMulCommutative (↥S.Mg ⧸ N) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hQ]; norm_num)
  have h := hcomm.is_comm.comm (QuotientGroup.mk (⟨y, hy⟩ : ↥S.Mg))
    (QuotientGroup.mk (⟨x, hx⟩ : ↥S.Mg))
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have h' : ((⟨y, hy⟩ * ⟨x, hx⟩ : ↥S.Mg)⁻¹ * (⟨x, hx⟩ * ⟨y, hy⟩ : ↥S.Mg) : ↥S.Mg) ∈ N := h
  have h'' : ((y * x)⁻¹ * (x * y) : G) ∈ S.Tg := h'
  have e : x⁻¹ * y⁻¹ * x * y = (y * x)⁻¹ * (x * y) := by group
  rw [e]
  exact h''

omit [Finite G] in
theorem σ₂_ne_one : S.σ₂ ≠ 1 := by
  intro h
  apply S.σ₁_ne_one
  have h' : S.u⁻¹ * S.σ₁ * S.u = 1 := h
  calc S.σ₁ = S.u * (S.u⁻¹ * S.σ₁ * S.u) * S.u⁻¹ := by group
    _ = 1 := by rw [h']; group

theorem R_eq_closure : S.R = Subgroup.closure {S.σ₁, S.σ₂} := by
  have h3 : S.σ₁ ^ 3 = 1 := S.jw.r1
  have hn : S.σ₂ ∉ Subgroup.zpowers S.σ₁ := by
    intro hmem
    rcases mem_zpowers_of_pow_three h3 hmem with h | h | h
    · exact S.σ₂_ne_one h
    · exact S.σ₂_ne_σ₁ h
    · exact S.σ₂_ne_σ₁_inv h
  exact eq_closure_of_card_nine S.hR.card S.hσR S.σ₂_mem h3 S.σ₁_ne_one hn

theorem v_inv_R {r : ↥(Hz z)} (hr : r ∈ S.R) : S.v⁻¹ * r * S.v = r⁻¹ := by
  have hcl : ∀ x, x ∈ Subgroup.closure ({S.σ₁, S.σ₂} : Set ↥(Hz z)) → x ∈ S.R := fun x hx => by
    rw [S.R_eq_closure]
    exact hx
  have key : ∀ r ∈ Subgroup.closure ({S.σ₁, S.σ₂} : Set ↥(Hz z)), S.v⁻¹ * r * S.v = r⁻¹ := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact S.conj_v_σ₁
      · exact S.conj_v_σ₂
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hc : x * y = y * x := S.hR.comm (hcl x hx) (hcl y hy)
      calc S.v⁻¹ * (x * y) * S.v = (S.v⁻¹ * x * S.v) * (S.v⁻¹ * y * S.v) := by group
        _ = x⁻¹ * y⁻¹ := by rw [ihx, ihy]
        _ = (y * x)⁻¹ := by group
        _ = (x * y)⁻¹ := by rw [hc]
    | inv x hx ih =>
      calc S.v⁻¹ * x⁻¹ * S.v = (S.v⁻¹ * x * S.v)⁻¹ := by group
        _ = (x⁻¹)⁻¹ := by rw [ih]
  rw [S.R_eq_closure] at hr
  exact key r hr

theorem v_inv_Tg {r : G} (hr : r ∈ S.Tg) : (S.v : G)⁻¹ * r * S.v = r⁻¹ := by
  obtain ⟨r', hr', rfl⟩ := (S.mem_Tg).1 hr
  exact congrArg Subtype.val (S.v_inv_R hr')

theorem z_normalizes_T1 (x : G) : x ∈ S.T1 ↔ z * x * z⁻¹ ∈ S.T1 :=
  normalizes_inf_centralizer S.z_normalizes_Mg S.u_comm_z.eq x

theorem exists_rho : ∃ ρ ∈ S.T1, ρ ≠ 1 ∧ z * ρ * z⁻¹ = ρ⁻¹ := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right S.z_sq
  have hzz : z⁻¹ * z⁻¹ = 1 := by rw [hz, S.z_sq]
  have hnot : ¬ S.T1 ≤ Subgroup.centralizer ({z} : Set G) := by
    intro hle
    have h1 : S.T1 ⊓ Subgroup.centralizer ({z} : Set G) = S.T1 := inf_eq_left.mpr hle
    have h2 : S.T1 ⊓ Subgroup.centralizer ({z} : Set G) =
        S.Tg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G) := by
      show S.Mg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G) ⊓
        Subgroup.centralizer ({z} : Set G) = _
      rw [inf_right_comm]
      exact congrArg (· ⊓ _) S.Mg_inf_cent_z
    have h3 := S.card_Tg_inf_u
    rw [← h2, h1, S.card_T1] at h3
    omega
  obtain ⟨x, hx, hxz⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  refine ⟨x⁻¹ * (z * x * z⁻¹), mul_mem (inv_mem hx) ((S.z_normalizes_T1 x).1 hx), ?_, ?_⟩
  · intro h
    apply hxz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : z * x * z⁻¹ = x := by
      have := congrArg (x * ·) h
      simpa using this
    calc x * z = (z * x * z⁻¹) * z := by rw [h']
      _ = z * x := by group
  · calc z * (x⁻¹ * (z * x * z⁻¹)) * z⁻¹ = z * x⁻¹ * z⁻¹ * (z * z * x * z⁻¹ * z⁻¹) := by group
      _ = z * x⁻¹ * z⁻¹ * x := by rw [S.z_sq, one_mul, mul_assoc x, hzz, mul_one]
      _ = (x⁻¹ * (z * x * z⁻¹))⁻¹ := by group

end JWSetup

end CFSG.Quasithin.H13.U43
