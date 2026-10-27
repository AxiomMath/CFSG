module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79CtlStmt
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79QuoK
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79SZ

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)

variable {H : Type} [Group H] [Finite H]

namespace Ctl34

structure Frame (b b₁ b₂ : H) (J : Subgroup H) (w τ c : H) (J' : Subgroup H) : Prop where
  w_mem : w ∈ Subgroup.closure ({b₁, b₂} : Set H)
  w_ne : w ≠ 1
  w3 : w ^ 3 = 1
  c_mem : c ∈ Subgroup.closure ({b₁, b₂} : Set H)
  c_ne : c ≠ 1
  c3 : c ^ 3 = 1
  B₁_le : Subgroup.closure ({b₁, b₂} : Set H) ≤ Subgroup.zpowers w ⊔ Subgroup.zpowers c
  τ_mem : τ ∈ J
  τ2 : τ * τ = 1
  τ_inv : τ * w * τ⁻¹ = w⁻¹
  J'_le : J' ≤ J
  J'_iso : Nonempty (↥J' ≃* Perm (Fin 3))
  c_mem_J' : c ∈ J'
  J'_comm_w : ∀ j ∈ J', j * w = w * j
  J'_comm_τ : ∀ j ∈ J', j * τ = τ * j
  decomp1 : ∀ j₀ ∈ J, j₀ * w * j₀⁻¹ = w → ∃ i : ℤ, ∃ s ∈ J', j₀ = w ^ i * s
  decomp2 : ∀ j₀ ∈ J, j₀ * w * j₀⁻¹ = w⁻¹ → ∃ i : ℤ, ∃ s ∈ J', j₀ = w ^ i * τ * s
  fusion_c : ∀ j₁ ∈ J, j₁ * c * j₁⁻¹ ∈ Subgroup.zpowers c →
    j₁ * w * j₁⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)
  ctl_c : CtlEq b c

section Aux

variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem K_comm_b (h : FS79Hyp b t b₁ b₂ J) {k : H}
    (hk : k ∈ Opp 3 (Nor (Subgroup.zpowers b))) : k * b = b * k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkN : k ∈ Nor (Subgroup.zpowers b) := L14.Opp_le 3 _ hk
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := by
    intro h1
    have := h.ord_b
    rw [h1, orderOf_one] at this
    omega
  have h1 : k * b * k⁻¹ = b := by
    refine conj_eq_of_coprime_normal (X := Nor (Subgroup.zpowers b))
      (Q := Opp 3 (Nor (Subgroup.zpowers b))) (fun g hg q hq => L14.Opp_conj_mem hg hq)
      (L14.Opp_coprime 3 _) (mem_Nor_self b) hb3 hb1 hk ?_
    exact (Subgroup.mem_normalizer_iff.mp hkN b).mp (Subgroup.mem_zpowers b)
  calc k * b = (k * b * k⁻¹) * k := by group
    _ = b * k := by rw [h1]

theorem comm_of_conj_eq' {g x : H} (h : g * x * g⁻¹ = x) : g * x = x * g := by
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [h]

theorem conj_commute_of_commute' {g j x : H} (hg : g * x = x * g) (hj : j * x = x * j) :
    (g * j * g⁻¹) * x = x * (g * j * g⁻¹) := by
  have h1 : g⁻¹ * x = x * g⁻¹ := by
    calc g⁻¹ * x = g⁻¹ * (x * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * x) * g⁻¹ := by rw [hg]
      _ = x * g⁻¹ := by group
  calc (g * j * g⁻¹) * x = g * j * (g⁻¹ * x) := by group
    _ = g * j * (x * g⁻¹) := by rw [h1]
    _ = g * (j * x) * g⁻¹ := by group
    _ = g * (x * j) * g⁻¹ := by rw [hj]
    _ = (g * x) * j * g⁻¹ := by group
    _ = (x * g) * j * g⁻¹ := by rw [hg]
    _ = x * (g * j * g⁻¹) := by group

theorem nor_normalizes_cen {β g x : H} (hg : g ∈ Nor (Subgroup.zpowers β)) (hx : x ∈ Cen β) :
    g * x * g⁻¹ ∈ Cen β := by
  have hβ' : g⁻¹ * β * g⁻¹⁻¹ ∈ Subgroup.zpowers β :=
    (Subgroup.mem_normalizer_iff.mp ((Nor _).inv_mem hg) _).mp (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hβ'
  have hcm : Commute x β := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hck : x * β ^ k = β ^ k * x := (Commute.zpow_right hcm k).eq
  rw [hk] at hck
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc (g * x * g⁻¹) * β = g * (x * (g⁻¹ * β * g⁻¹⁻¹)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * β * g⁻¹⁻¹) * x) * g⁻¹ := by rw [hck]
    _ = β * (g * x * g⁻¹) := by group

theorem conj_b_pos (h : FS79Hyp b t b₁ b₂ J) {κ j₀ : H}
    (hκ : κ ∈ Opp 3 (Nor (Subgroup.zpowers b))) (hj₀ : j₀ ∈ J) (i : ℤ) :
    (κ * b ^ i * j₀) * b * (κ * b ^ i * j₀)⁻¹ = b := by
  have h1 : Commute b κ := (K_comm_b h hκ).symm
  have h2 : Commute b (b ^ i) := (Commute.refl b).zpow_right i
  have h3 : Commute b j₀ := (Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj₀)).symm
  have := ((h1.mul_right h2).mul_right h3).eq
  calc (κ * b ^ i * j₀) * b * (κ * b ^ i * j₀)⁻¹
      = ((κ * b ^ i * j₀) * b) * (κ * b ^ i * j₀)⁻¹ := rfl
    _ = (b * (κ * b ^ i * j₀)) * (κ * b ^ i * j₀)⁻¹ := by rw [← this]
    _ = b := by group

theorem conj_b_neg (h : FS79Hyp b t b₁ b₂ J) {κ j₀ : H}
    (hκ : κ ∈ Opp 3 (Nor (Subgroup.zpowers b))) (hj₀ : j₀ ∈ J) (i : ℤ) :
    (κ * (b ^ i * t) * j₀) * b * (κ * (b ^ i * t) * j₀)⁻¹ = b⁻¹ := by
  have hj : j₀ * b * j₀⁻¹ = b := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b hj₀)]
    group
  have hk : κ * b⁻¹ * κ⁻¹ = b⁻¹ := by
    have h1 := K_comm_b h hκ
    calc κ * b⁻¹ * κ⁻¹ = (κ * b * κ⁻¹)⁻¹ := by group
      _ = b⁻¹ := by rw [show κ * b * κ⁻¹ = b by rw [h1]; group]
  calc (κ * (b ^ i * t) * j₀) * b * (κ * (b ^ i * t) * j₀)⁻¹
      = κ * (b ^ i * t * (j₀ * b * j₀⁻¹) * t⁻¹ * (b ^ i)⁻¹) * κ⁻¹ := by group
    _ = κ * (b ^ i * (t * b * t⁻¹) * (b ^ i)⁻¹) * κ⁻¹ := by rw [hj]; group
    _ = κ * (b ^ i * b⁻¹ * (b ^ i)⁻¹) * κ⁻¹ := by rw [h.inv_b]
    _ = κ * b⁻¹ * κ⁻¹ := by group
    _ = b⁻¹ := hk

end Aux

section Identities

variable {G : Type} [Group G]

theorem decomp_eq_pos (κ b w s : G) (i i' : ℤ) (hbw : Commute b w) (hsb : Commute s b)
    (hsw : Commute s w) :
    κ * b ^ i' * (w ^ i * s) = κ * b ^ (i' - i) * s * (b * w) ^ i := by
  have hsβ : s * (b * w) ^ i = (b * w) ^ i * s := (Commute.zpow_right (hsb.mul_right hsw) i).eq
  have e1 : (b * w) ^ i = b ^ i * w ^ i := hbw.mul_zpow i
  calc κ * b ^ i' * (w ^ i * s) = κ * b ^ (i' - i) * (b ^ i * w ^ i) * s := by group
    _ = κ * b ^ (i' - i) * (b * w) ^ i * s := by rw [e1]
    _ = κ * b ^ (i' - i) * ((b * w) ^ i * s) := by group
    _ = κ * b ^ (i' - i) * (s * (b * w) ^ i) := by rw [hsβ]
    _ = κ * b ^ (i' - i) * s * (b * w) ^ i := by group

theorem decomp_eq_neg (κ b w s t τ : G) (i i' : ℤ) (hbw : Commute b w) (hsb : Commute s b)
    (hsw : Commute s w) (htw : Commute t w)
    (hβ : (t * τ) * (b * w) * (t * τ)⁻¹ = (b * w)⁻¹) :
    κ * (b ^ i' * t) * (w ^ i * τ * s) =
      κ * (b ^ (i' - i) * (t * τ)) * s * (b * w) ^ (-i) := by
  have hsβ : s * (b * w) ^ (-i) = (b * w) ^ (-i) * s :=
    (Commute.zpow_right (hsb.mul_right hsw) (-i)).eq
  have e1 : (b * w) ^ i = b ^ i * w ^ i := hbw.mul_zpow i
  have htwi : t * w ^ i = w ^ i * t := (htw.zpow_right i).eq
  have hconj : (t * τ) * (b * w) ^ (-i) = (b * w) ^ i * (t * τ) := by
    have h1 : (t * τ) * (b * w) ^ (-i) * (t * τ)⁻¹ = (b * w) ^ i := by
      have := map_zpow (MulAut.conj (t * τ)) (b * w) (-i)
      simp only [MulAut.conj_apply] at this
      rw [this, hβ, inv_zpow', neg_neg]
    calc (t * τ) * (b * w) ^ (-i) = ((t * τ) * (b * w) ^ (-i) * (t * τ)⁻¹) * (t * τ) := by group
      _ = (b * w) ^ i * (t * τ) := by rw [h1]
  calc κ * (b ^ i' * t) * (w ^ i * τ * s)
      = κ * b ^ (i' - i) * (b ^ i * w ^ i * t) * τ * s := by
        calc κ * (b ^ i' * t) * (w ^ i * τ * s) = κ * b ^ i' * (t * w ^ i) * τ * s := by group
          _ = κ * b ^ i' * (w ^ i * t) * τ * s := by rw [htwi]
          _ = κ * b ^ (i' - i) * (b ^ i * w ^ i * t) * τ * s := by group
    _ = κ * b ^ (i' - i) * ((b * w) ^ i * (t * τ)) * s := by rw [e1]; group
    _ = κ * b ^ (i' - i) * ((t * τ) * (b * w) ^ (-i)) * s := by rw [hconj]
    _ = κ * (b ^ (i' - i) * (t * τ)) * ((b * w) ^ (-i) * s) := by group
    _ = κ * (b ^ (i' - i) * (t * τ)) * (s * (b * w) ^ (-i)) := by rw [hsβ]
    _ = κ * (b ^ (i' - i) * (t * τ)) * s * (b * w) ^ (-i) := by group

end Identities

namespace Frame

variable {b t b₁ b₂ : H} {J : Subgroup H} {w τ c : H} {J' : Subgroup H}
variable (F : Frame b b₁ b₂ J w τ c J') (h : FS79Hyp b t b₁ b₂ J)

include F h

theorem w_mem_J : w ∈ J := h.B₁_le_J F.w_mem

theorem c_mem_J : c ∈ J := h.B₁_le_J F.c_mem

theorem w_comm_b : w * b = b * w :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b (F.w_mem_J h))

theorem c_comm_b : c * b = b * c :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b (F.c_mem_J h))

theorem c_comm_w : c * w = w * c :=
  h.B_comm (FS79Hyp.B₁_le_B b b₁ b₂ F.c_mem) (FS79Hyp.B₁_le_B b b₁ b₂ F.w_mem)

theorem τ_comm_b : τ * b = b * τ :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b F.τ_mem)

theorem τ_comm_t : τ * t = t * τ :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t F.τ_mem)

theorem w_orderOf : orderOf w = 3 := orderOf_eq_prime F.w3 F.w_ne

theorem beta_pow_three : (b * w) ^ 3 = 1 := by
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hc : Commute b w := (F.w_comm_b h).symm
  rw [hc.mul_pow, hb3, F.w3, one_mul]

theorem zpowers_beta_inf_J : Subgroup.zpowers (b * w) ⊓ J = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxZ, hxJ⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxZ
  have hc : Commute b w := (F.w_comm_b h).symm
  rw [hc.mul_zpow] at hxJ ⊢
  have hbkJ : b ^ k ∈ J := by
    have := J.mul_mem hxJ (J.inv_mem (J.zpow_mem (F.w_mem_J h) k))
    simpa using this
  have hmem : b ^ k ∈ Subgroup.zpowers b ⊓ J :=
    ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k, hbkJ⟩
  rw [h.zpowers_inf_J, Subgroup.mem_bot] at hmem
  have h3 : (3 : ℤ) ∣ k := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := b) (i := k)).mpr hmem
    rwa [h.ord_b] at this
  have hwk : w ^ k = 1 :=
    (orderOf_dvd_iff_zpow_eq_one (x := w) (i := k)).mp (by rw [F.w_orderOf h]; exact h3)
  rw [hmem, hwk, mul_one]
  exact Subgroup.one_mem _

theorem beta_ne_one : b * w ≠ 1 := by
  intro h1
  have hb : b ∈ J := by
    have : b = w⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact J.inv_mem (F.w_mem_J h)
  exact h.b_not_mem_J hb

theorem beta_orderOf : orderOf (b * w) = 3 :=
  orderOf_eq_prime (F.beta_pow_three h) (F.beta_ne_one h)

theorem card_Z : Nat.card (Subgroup.zpowers (b * w)) = 3 := by
  rw [Nat.card_zpowers, F.beta_orderOf h]

theorem beta_comm_b : (b * w) * b = b * (b * w) := by
  rw [mul_assoc, F.w_comm_b h]

theorem w_comm_t : w * t = t * w :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t (F.w_mem_J h))

theorem isPGroup_E :
    IsPGroup 3 (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w) : Subgroup H) := by
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  refine IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_three hb3)
    (isPGroup_zpowers_of_pow_three (F.beta_pow_three h)) ?_
  rw [Subgroup.zpowers_le]
  exact mem_Nor_zpowers_of_comm (F.beta_comm_b h)

theorem Nor_E_le_Nor {g : H} (hg : g ∈ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w))) :
    g ∈ Nor (Subgroup.zpowers b) := by
  have hbE : b ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hgb := (Subgroup.mem_normalizer_iff.mp hg b).mp hbE
  exact mem_Nor_zpowers_of_conj (h.conj_mem_zpowers_of_pgroup (F.isPGroup_E h) hbE hgb)

theorem weak_E {h' : H}
    (hh : ∀ k : ℤ, h' * b ^ k * h'⁻¹ ∈ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w))) :
    h' * b * h'⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w) := by
  have h1 : h' * b * h'⁻¹ ∈ Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w)) := by
    simpa using hh 1
  have hle : Subgroup.zpowers (h' * b * h'⁻¹) ≤
      Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w)) := Subgroup.zpowers_le.mpr h1
  have hS : IsPGroup 3 (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w) ⊔
      Subgroup.zpowers (h' * b * h'⁻¹) : Subgroup H) := by
    have hb3' : (h' * b * h'⁻¹) ^ 3 = 1 := by
      have hb3 : b ^ 3 = 1 := by
        rw [← h.ord_b]
        exact pow_orderOf_eq_one b
      rw [conj_pow, hb3]
      group
    exact IsPGroup.to_sup_of_normal_left' (F.isPGroup_E h)
      (isPGroup_zpowers_of_pow_three hb3') hle
  have hbS : b ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w) ⊔
      Subgroup.zpowers (h' * b * h'⁻¹) :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  have hgS : h' * b * h'⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w) ⊔
      Subgroup.zpowers (h' * b * h'⁻¹) := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have := h.conj_mem_zpowers_of_pgroup hS hbS hgS
  exact Subgroup.mem_sup_left this

theorem hat_sq : (t * τ) * (t * τ) = 1 := by
  calc (t * τ) * (t * τ) = t * (τ * t) * τ := by group
    _ = t * (t * τ) * τ := by rw [F.τ_comm_t h]
    _ = (t * t) * (τ * τ) := by group
    _ = 1 := by rw [h.t_sq, F.τ2, one_mul]

theorem hat_inv_b : (t * τ) * b * (t * τ)⁻¹ = b⁻¹ := by
  have e : τ * b * τ⁻¹ = b := by
    rw [F.τ_comm_b h]
    group
  calc (t * τ) * b * (t * τ)⁻¹ = t * (τ * b * τ⁻¹) * t⁻¹ := by group
    _ = t * b * t⁻¹ := by rw [e]
    _ = b⁻¹ := h.inv_b

theorem hat_beta : (t * τ) * (b * w) * (t * τ)⁻¹ = (b * w)⁻¹ := by
  have e1 : τ * (b * w) * τ⁻¹ = b * w⁻¹ := by
    have e : τ * b * τ⁻¹ = b := by
      rw [F.τ_comm_b h]
      group
    calc τ * (b * w) * τ⁻¹ = (τ * b * τ⁻¹) * (τ * w * τ⁻¹) := by group
      _ = b * w⁻¹ := by rw [e, F.τ_inv]
  have htw : t * w⁻¹ * t⁻¹ = w⁻¹ := by
    have : t * w = w * t := (F.w_comm_t h).symm
    calc t * w⁻¹ * t⁻¹ = (t * w * t⁻¹)⁻¹ := by group
      _ = w⁻¹ := by rw [this]; group
  have hbw : Commute b w := (F.w_comm_b h).symm
  have hc : Commute b⁻¹ w⁻¹ := hbw.inv_inv
  calc (t * τ) * (b * w) * (t * τ)⁻¹ = t * (τ * (b * w) * τ⁻¹) * t⁻¹ := by group
    _ = t * (b * w⁻¹) * t⁻¹ := by rw [e1]
    _ = (t * b * t⁻¹) * (t * w⁻¹ * t⁻¹) := by group
    _ = b⁻¹ * w⁻¹ := by rw [h.inv_b, htw]
    _ = w⁻¹ * b⁻¹ := hc.eq
    _ = (b * w)⁻¹ := by group

theorem hat_mem_Nor : t * τ ∈ Nor (Subgroup.zpowers (b * w)) :=
  mem_Nor_zpowers_of_conj (by rw [F.hat_beta h]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))

theorem beta_pow_eq {e m : ℤ} {u : H} (hu : u ∈ J) (hm : (b * w) ^ m = b ^ e * u) :
    (3 : ℤ) ∣ m - e ∧ u = w ^ e := by
  have hc : Commute b w := (F.w_comm_b h).symm
  rw [hc.mul_zpow] at hm
  have e1 : b ^ (m - e) * w ^ m = u := by
    have : u = (b ^ e)⁻¹ * (b ^ m * w ^ m) := by rw [hm]; group
    rw [this]
    group
  have hbJ : b ^ (m - e) ∈ J := by
    have : b ^ (m - e) = u * (w ^ m)⁻¹ := by rw [← e1]; group
    rw [this]
    exact J.mul_mem hu (J.inv_mem (J.zpow_mem (F.w_mem_J h) m))
  have hmem : b ^ (m - e) ∈ Subgroup.zpowers b ⊓ J :=
    ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) _, hbJ⟩
  rw [h.zpowers_inf_J, Subgroup.mem_bot] at hmem
  have h3 : (3 : ℤ) ∣ m - e := by
    have := (orderOf_dvd_iff_zpow_eq_one (x := b) (i := m - e)).mpr hmem
    rwa [h.ord_b] at this
  refine ⟨h3, ?_⟩
  have hw : w ^ (m - e) = 1 :=
    (orderOf_dvd_iff_zpow_eq_one (x := w) (i := m - e)).mp (by rw [F.w_orderOf h]; exact h3)
  rw [hmem, one_mul] at e1
  rw [← e1]
  calc w ^ m = w ^ (m - e) * w ^ e := by group
    _ = w ^ e := by rw [hw, one_mul]

theorem decomp {g : H}
    (hg : g ∈ Nor (Subgroup.zpowers (b * w)) ⊓
      Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w))) :
    ∃ κ ∈ Opp 3 (Nor (Subgroup.zpowers b)), ∃ y ∈ Subgroup.closure ({b, t * τ} : Set H),
      ∃ s ∈ J', ∃ z ∈ Subgroup.zpowers (b * w), g = κ * y * s * z := by
  classical
  have hgb := F.Nor_E_le_Nor h hg.2
  obtain ⟨κ, hκ, y₀, hy₀, j₀, hj₀, rfl⟩ := h.nor_decomp hgb
  have hgβ : (κ * y₀ * j₀) * (b * w) * (κ * y₀ * j₀)⁻¹ ∈ Subgroup.zpowers (b * w) :=
    (Subgroup.mem_normalizer_iff.mp hg.1 _).mp (Subgroup.mem_zpowers _)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hgβ
  have hwJ := F.w_mem_J h
  have hconjw := h.conj_eq_of_decomp hκ hy₀ hj₀ hwJ
  have hu₀J : j₀ * w * j₀⁻¹ ∈ J := J.mul_mem (J.mul_mem hj₀ hwJ) (J.inv_mem hj₀)
  have hbw : Commute b w := (F.w_comm_b h).symm
  have htw : Commute t w := (F.w_comm_t h).symm
  have hsplit : ∀ x : H, x * (b * w) * x⁻¹ = (x * b * x⁻¹) * (x * w * x⁻¹) := fun x => by
    group
  have hsb : ∀ s ∈ J', Commute s b := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b (F.J'_le hs))
  obtain ⟨i', hy | hy⟩ := mem_closure_bt_iff h.inv_b h.t_sq hy₀
  ·
    have hgb' : (κ * y₀ * j₀) * b * (κ * y₀ * j₀)⁻¹ = b := by
      rw [hy]
      exact conj_b_pos h hκ hj₀ i'
    have hm' : (b * w) ^ m = b ^ (1 : ℤ) * (j₀ * w * j₀⁻¹) := by
      rw [hm, hsplit, hgb', hconjw, zpow_one]
    obtain ⟨-, hu⟩ := F.beta_pow_eq h hu₀J hm'
    rw [zpow_one] at hu
    obtain ⟨i, s, hs, rfl⟩ := F.decomp1 j₀ hj₀ hu
    refine ⟨κ, hκ, b ^ (i' - i), ?_, s, hs, (b * w) ^ i,
      Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) i, ?_⟩
    · exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _
    · rw [hy]
      exact decomp_eq_pos κ b w s i i' hbw (hsb s hs) (F.J'_comm_w s hs)
  ·
    have hgb' : (κ * y₀ * j₀) * b * (κ * y₀ * j₀)⁻¹ = b⁻¹ := by
      rw [hy]
      exact conj_b_neg h hκ hj₀ i'
    have hm' : (b * w) ^ m = b ^ (-1 : ℤ) * (j₀ * w * j₀⁻¹) := by
      rw [hm, hsplit, hgb', hconjw, zpow_neg_one]
    obtain ⟨-, hu⟩ := F.beta_pow_eq h hu₀J hm'
    rw [zpow_neg_one] at hu
    obtain ⟨i, s, hs, rfl⟩ := F.decomp2 j₀ hj₀ hu
    refine ⟨κ, hκ, b ^ (i' - i) * (t * τ), ?_, s, hs, (b * w) ^ (-i),
      Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.subset_closure (by simp))
    · rw [hy]
      exact decomp_eq_neg κ b w s t τ i i' hbw (hsb s hs) (F.J'_comm_w s hs) htw (F.hat_beta h)

theorem beta_comm_c : c * (b * w) = (b * w) * c := by
  rw [← mul_assoc, F.c_comm_b h, mul_assoc, F.c_comm_w h, ← mul_assoc]

theorem J'_comm_beta {j : H} (hj : j ∈ J') : j * (b * w) = (b * w) * j := by
  have hjb : j * b = b * j :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b (F.J'_le hj))
  rw [← mul_assoc, hjb, mul_assoc, F.J'_comm_w j hj, ← mul_assoc]

theorem closure_comm_J' {y j : H} (hy : y ∈ Subgroup.closure ({b, t * τ} : Set H))
    (hj : j ∈ J') : y * j = j * y := by
  have hle : Subgroup.closure ({b, t * τ} : Set H) ≤ Subgroup.centralizer ({j} : Set H) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b (F.J'_le hj))).symm
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have h1 : j * t = t * j :=
        Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_t (F.J'_le hj))
      have h2 := F.J'_comm_τ j hj
      calc t * τ * j = t * (τ * j) := by group
        _ = t * (j * τ) := by rw [h2]
        _ = (t * j) * τ := by group
        _ = (j * t) * τ := by rw [h1]
        _ = j * (t * τ) := by group
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))

theorem struct_b : ∃ W : Subgroup H,
    W ≤ Nor (Subgroup.zpowers (b * w)) ⊓
      Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w)) ∧
    Nat.Coprime 3 (Nat.card W) ∧
    (∀ g ∈ Nor (Subgroup.zpowers (b * w)) ⊓
        Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w)),
      ∀ x ∈ W, ∃ x' ∈ W, ∃ z ∈ Subgroup.zpowers (b * w), g * x * g⁻¹ = x' * z) ∧
    (∀ g ∈ Nor (Subgroup.zpowers (b * w)) ⊓
        Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w)),
      ∃ x ∈ W, ∃ y ∈ Subgroup.closure ({b, t * τ} : Set H), ∃ j ∈ J',
        ∃ z ∈ Subgroup.zpowers (b * w), g = x * y * j * z) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Opp 3 (Nor (Subgroup.zpowers b)), ?_, L14.Opp_coprime 3 _, ?_, ?_⟩
  · intro κ hκ
    have hκβ : κ * (b * w) = (b * w) * κ := by
      rw [← mul_assoc, K_comm_b h hκ, mul_assoc, h.K_comm_J hκ (F.w_mem_J h), ← mul_assoc]
    have hN : κ ∈ Nor (Subgroup.zpowers (b * w)) := mem_Nor_zpowers_of_comm hκβ
    exact ⟨hN, Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨L14.Opp_le 3 _ hκ, hN⟩⟩
  · intro g hg x hx
    exact ⟨g * x * g⁻¹, L14.Opp_conj_mem (F.Nor_E_le_Nor h hg.2) hx, 1, Subgroup.one_mem _,
      (mul_one _).symm⟩
  · intro g hg
    obtain ⟨κ, hκ, y, hy, s, hs, z, hz, rfl⟩ := F.decomp h hg
    exact ⟨κ, hκ, y, hy, s, hs, z, hz, rfl⟩

theorem N_J {g : H}
    (hg : g ∈ Nor (Subgroup.zpowers (b * w)) ⊓
      Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w))) {j : H} (hj : j ∈ J') :
    ∃ j' ∈ J', ∃ z ∈ Subgroup.zpowers (b * w), g * j * g⁻¹ = j' * z := by
  obtain ⟨κ, hκ, y, hy, s, hs, z, hz, rfl⟩ := F.decomp h hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hjJ : j ∈ J := F.J'_le hj
  have hzj : (b * w) ^ k * j = j * (b * w) ^ k :=
    ((Commute.zpow_left (F.J'_comm_beta h hj).symm k)).eq
  have hκj : κ * j = j * κ := h.K_comm_J hκ hjJ
  have hyj : y * j = j * y := F.closure_comm_J' h hy hj
  refine ⟨s * j * s⁻¹, J'.mul_mem (J'.mul_mem hs hj) (J'.inv_mem hs), 1, Subgroup.one_mem _, ?_⟩
  have e : (κ * y * s * (b * w) ^ k) * j * (κ * y * s * (b * w) ^ k)⁻¹ =
      κ * y * (s * ((b * w) ^ k * j * ((b * w) ^ k)⁻¹) * s⁻¹) * y⁻¹ * κ⁻¹ := by group
  have e2 : (b * w) ^ k * j * ((b * w) ^ k)⁻¹ = j := by
    rw [hzj]
    group
  rw [e, e2]
  have e3 : y * (s * j * s⁻¹) * y⁻¹ = s * j * s⁻¹ := by
    have hc : y * (s * j * s⁻¹) = (s * j * s⁻¹) * y :=
      F.closure_comm_J' h hy (J'.mul_mem (J'.mul_mem hs hj) (J'.inv_mem hs))
    rw [hc]
    group
  have e4 : κ * (s * j * s⁻¹) * κ⁻¹ = s * j * s⁻¹ := by
    have hc : κ * (s * j * s⁻¹) = (s * j * s⁻¹) * κ :=
      h.K_comm_J hκ (F.J'_le (J'.mul_mem (J'.mul_mem hs hj) (J'.inv_mem hs)))
    rw [hc]
    group
  calc κ * y * (s * j * s⁻¹) * y⁻¹ * κ⁻¹ = κ * (y * (s * j * s⁻¹) * y⁻¹) * κ⁻¹ := by group
    _ = κ * (s * j * s⁻¹) * κ⁻¹ := by rw [e3]
    _ = s * j * s⁻¹ := e4
    _ = (s * j * s⁻¹) * 1 := (mul_one _).symm

theorem E'_inf_J {x : H} (hx : x ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w))
    (hxJ : x ∈ J) : x ∈ Subgroup.zpowers c := by
  have hcomm : ∀ a ∈ Subgroup.zpowers c, ∀ z ∈ Subgroup.zpowers (b * w), a * z = z * a := by
    intro a ha z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow (F.beta_comm_c h) i k).eq
  obtain ⟨a, ha, z, hz, hxaz⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx
  have haJ : a ∈ J := (Subgroup.zpowers_le.mpr (F.c_mem_J h)) ha
  have hzJ : z ∈ J := by
    have : z = a⁻¹ * x := by rw [← hxaz]; group
    rw [this]
    exact J.mul_mem (J.inv_mem haJ) hxJ
  have hz1 : z = 1 := by
    have : z ∈ Subgroup.zpowers (b * w) ⊓ J := ⟨hz, hzJ⟩
    rw [F.zpowers_beta_inf_J h, Subgroup.mem_bot] at this
    exact this
  rw [← hxaz, hz1, mul_one]
  exact ha

theorem weak_c {g : H} (hg : g * c * g⁻¹ ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w)) :
    g * c * g⁻¹ ∈ Subgroup.zpowers c := by
  have hcB : c ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := FS79Hyp.B₁_le_B b b₁ b₂ F.c_mem
  have hβB : b * w ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    Subgroup.mul_mem _ (FS79Hyp.zpowers_le_B b b₁ b₂ (Subgroup.mem_zpowers b))
      (FS79Hyp.B₁_le_B b b₁ b₂ F.w_mem)
  have hxB : g * c * g⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := by
    have : Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w) ≤
        Subgroup.closure ({b, b₁, b₂} : Set H) :=
      sup_le (Subgroup.zpowers_le.mpr hcB) (Subgroup.zpowers_le.mpr hβB)
    exact this hg
  obtain ⟨n, hn, hnc⟩ := h.fusion_B (g := g) hcB hxB rfl
  obtain ⟨k, hk, y, hy, j, hj, hn_eq, hconj, hjB⟩ := h.nor_B_decomp hn
  have hxJ : g * c * g⁻¹ ∈ J := by
    rw [← hnc, hconj c F.c_mem]
    exact J.mul_mem (J.mul_mem hj (F.c_mem_J h)) (J.inv_mem hj)
  exact F.E'_inf_J h hg hxJ

theorem Nor_cE'_le_Nor_c {g : H}
    (hg : g ∈ Nor (Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w))) :
    g ∈ Nor (Subgroup.zpowers c) := by
  have hcE : c ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hgc := (Subgroup.mem_normalizer_iff.mp hg c).mp hcE
  exact mem_Nor_zpowers_of_conj (F.weak_c h hgc)

theorem Q_comm_of_B {Q : Subgroup H} (hQ : Ctl b c Q) {q u : H} (hq : q ∈ Q)
    (huB : u ∈ Subgroup.closure ({b, b₁, b₂} : Set H))
    (hquB : q * u * q⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) : q * u * q⁻¹ = u := by
  have hcB : c ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := FS79Hyp.B₁_le_B b b₁ b₂ F.c_mem
  have huN : u ∈ Nor (Subgroup.zpowers c) := mem_Nor_zpowers_of_comm (h.B_comm huB hcB)
  have h1 : q * u * q⁻¹ * u⁻¹ ∈ Q := by
    have := Q.mul_mem hq (hQ.norm u huN q⁻¹ (Q.inv_mem hq))
    have e : q * (u * q⁻¹ * u⁻¹) = q * u * q⁻¹ * u⁻¹ := by group
    rwa [e] at this
  have h2 : q * u * q⁻¹ * u⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    Subgroup.mul_mem _ hquB (Subgroup.inv_mem _ huB)
  have h3 : q * u * q⁻¹ * u⁻¹ = 1 :=
    eq_one_of_mem_coprime_of_pow_three hQ.cop h1 (h.B_pow_three h2)
  calc q * u * q⁻¹ = (q * u * q⁻¹ * u⁻¹) * u := by group
    _ = u := by rw [h3, one_mul]

theorem decomp_c {g : H}
    (hg : g ∈ Nor (Subgroup.zpowers (b * w)) ⊓
      Nor (Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w))) :
    ∃ q ∈ Opp 3 (Nor (Subgroup.zpowers c)), q ∈ Cen (b * w) ∧
      ∃ n₁ ∈ Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers c) ⊓
        Nor (Subgroup.zpowers (b * w)), g = q * n₁ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgc : g ∈ Nor (Subgroup.zpowers c) := F.Nor_cE'_le_Nor_c h hg.2
  have hQ : Ctl b c (Opp 3 (Nor (Subgroup.zpowers c))) := Ctl.of_N_bi F.ctl_c
  obtain ⟨q, hq, n₁, hn₁, hgqn⟩ := hQ.decomp g hgc
  obtain ⟨κ, hκ, y, hy, j₁, hj₁, hn₁eq⟩ := h.nor_decomp hn₁.1
  have hcJ := F.c_mem_J h
  have hwJ := F.w_mem_J h
  have hn₁c : n₁ * c * n₁⁻¹ = j₁ * c * j₁⁻¹ := by
    rw [hn₁eq]
    exact h.conj_eq_of_decomp hκ hy hj₁ hcJ
  have hn₁w : n₁ * w * n₁⁻¹ = j₁ * w * j₁⁻¹ := by
    rw [hn₁eq]
    exact h.conj_eq_of_decomp hκ hy hj₁ hwJ
  have hj₁c : j₁ * c * j₁⁻¹ ∈ Subgroup.zpowers c := by
    rw [← hn₁c]
    exact (Subgroup.mem_normalizer_iff.mp hn₁.2 c).mp (Subgroup.mem_zpowers c)
  have hj₁w : j₁ * w * j₁⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H) := F.fusion_c j₁ hj₁ hj₁c
  have hbB : b ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.zpowers_le_B b b₁ b₂ (Subgroup.mem_zpowers b)
  have hn₁b : n₁ * b * n₁⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    FS79Hyp.zpowers_le_B b b₁ b₂
      ((Subgroup.mem_normalizer_iff.mp hn₁.1 b).mp (Subgroup.mem_zpowers b))
  have hu : n₁ * (b * w) * n₁⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := by
    have e : n₁ * (b * w) * n₁⁻¹ = (n₁ * b * n₁⁻¹) * (j₁ * w * j₁⁻¹) := by
      rw [← hn₁w]
      group
    rw [e]
    exact Subgroup.mul_mem _ hn₁b (FS79Hyp.B₁_le_B b b₁ b₂ hj₁w)
  have hβB : b * w ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    Subgroup.mul_mem _ hbB (FS79Hyp.B₁_le_B b b₁ b₂ F.w_mem)
  have hgβ : g * (b * w) * g⁻¹ ∈ Subgroup.zpowers (b * w) :=
    (Subgroup.mem_normalizer_iff.mp hg.1 _).mp (Subgroup.mem_zpowers _)
  have hgu : g * (b * w) * g⁻¹ = q * (n₁ * (b * w) * n₁⁻¹) * q⁻¹ := by
    rw [hgqn]
    group
  have hqu : q * (n₁ * (b * w) * n₁⁻¹) * q⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := by
    rw [← hgu]
    exact (Subgroup.zpowers_le.mpr hβB) hgβ
  have hqu_eq : q * (n₁ * (b * w) * n₁⁻¹) * q⁻¹ = n₁ * (b * w) * n₁⁻¹ :=
    F.Q_comm_of_B h hQ hq hu hqu
  have hgβ' : g * (b * w) * g⁻¹ = n₁ * (b * w) * n₁⁻¹ := by rw [hgu, hqu_eq]
  have hu_mem : n₁ * (b * w) * n₁⁻¹ ∈ Subgroup.zpowers (b * w) := by
    rw [← hgβ']
    exact hgβ
  have hn₁N : n₁ ∈ Nor (Subgroup.zpowers (b * w)) := mem_Nor_zpowers_of_conj hu_mem
  have hu1 : n₁ * (b * w) * n₁⁻¹ ≠ 1 := by
    intro h1
    apply F.beta_ne_one h
    calc b * w = n₁⁻¹ * (n₁ * (b * w) * n₁⁻¹) * n₁ := by group
      _ = 1 := by rw [h1]; group
  have hqβ : q * (b * w) * q⁻¹ = b * w := by
    rcases eq_or_inv_of_mem_zpowers_of_pow_three (F.beta_pow_three h) (F.beta_ne_one h) hu_mem
      hu1 with h1 | h1
    · rw [h1] at hqu_eq
      exact hqu_eq
    · rw [h1] at hqu_eq
      calc q * (b * w) * q⁻¹ = (q * (b * w)⁻¹ * q⁻¹)⁻¹ := by group
        _ = ((b * w)⁻¹)⁻¹ := by rw [hqu_eq]
        _ = b * w := inv_inv _
  exact ⟨q, hq, Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq' hqβ), n₁,
    ⟨hn₁, hn₁N⟩, hgqn⟩

theorem struct_c : ∃ Wc : Subgroup H,
    Wc ≤ Nor (Subgroup.zpowers (b * w)) ⊓
      Nor (Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w)) ∧
    Nat.Coprime 3 (Nat.card Wc) ∧
    (∀ g ∈ Nor (Subgroup.zpowers (b * w)) ⊓
        Nor (Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w)),
      ∀ x ∈ Wc, ∃ x' ∈ Wc, ∃ z ∈ Subgroup.zpowers (b * w), g * x * g⁻¹ = x' * z) ∧
    (∀ g ∈ Nor (Subgroup.zpowers (b * w)) ⊓
        Nor (Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w)),
      ∃ x ∈ Wc, ∃ n ∈ Nor (Subgroup.zpowers (b * w)) ⊓
          Nor (Subgroup.zpowers c ⊔ Subgroup.zpowers (b * w)) ⊓
          Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w)),
        ∃ z ∈ Subgroup.zpowers (b * w), g = x * n * z) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ : Ctl b c (Opp 3 (Nor (Subgroup.zpowers c))) := Ctl.of_N_bi F.ctl_c
  refine ⟨Opp 3 (Nor (Subgroup.zpowers c)) ⊓ Cen (b * w), ?_, ?_, ?_, ?_⟩
  · rintro q ⟨hq, hqC⟩
    have hqN : q ∈ Nor (Subgroup.zpowers (b * w)) := fs79_cen_le_nor_zpowers _ hqC
    exact ⟨hqN, Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨L14.Opp_le 3 _ hq, hqN⟩⟩
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hQ.cop
  · intro g hg x hx
    have hgc : g ∈ Nor (Subgroup.zpowers c) := F.Nor_cE'_le_Nor_c h hg.2
    exact ⟨g * x * g⁻¹, ⟨hQ.norm g hgc x hx.1, nor_normalizes_cen hg.1 hx.2⟩, 1,
      Subgroup.one_mem _, (mul_one _).symm⟩
  · intro g hg
    obtain ⟨q, hq, hqC, n₁, hn₁, hgqn⟩ := F.decomp_c h hg
    refine ⟨q, ⟨hq, hqC⟩, n₁, ⟨⟨hn₁.2, Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hn₁.1.2, hn₁.2⟩⟩, Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hn₁.1.1, hn₁.2⟩⟩, 1,
      Subgroup.one_mem _, ?_⟩
    rw [hgqn, mul_one]

theorem no2 {R : Subgroup H} (hRΓ : R ≤ Nor (Subgroup.zpowers (b * w)))
    (hZR : Subgroup.zpowers (b * w) ≤ R)
    (hR2 : ∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ Subgroup.zpowers (b * w))
    (hb : b ∈ Nor R) (hc : c ∈ Nor R) : R ≤ Subgroup.zpowers (b * w) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hβ3 := F.beta_pow_three h
  have hβ1 := F.beta_ne_one h
  have hZ3 : Nat.card (Subgroup.zpowers (b * w)) = 3 := F.card_Z h
  have hb3 : b ^ 3 = 1 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  have hZ_cen : Subgroup.zpowers (b * w) ≤ Cen (b * w) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hZcen : ∀ z ∈ Subgroup.zpowers (b * w), ∀ r ∈ Cen (b * w), r * z = z * r := by
    intro z hz r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hr) k).eq
  have hbC : b ∈ Cen (b * w) := Subgroup.mem_centralizer_singleton_iff.mpr (F.beta_comm_b h).symm
  have hcC : c ∈ Cen (b * w) := Subgroup.mem_centralizer_singleton_iff.mpr (F.beta_comm_c h)
  have hZR₀ : Subgroup.zpowers (b * w) ≤ R ⊓ Cen (b * w) := fun z hz => ⟨hZR hz, hZ_cen hz⟩
  have hZc : ∀ r ∈ R ⊓ Cen (b * w), ∀ z ∈ Subgroup.zpowers (b * w), r * z = z * r :=
    fun r hr z hz => hZcen z hz r hr.2
  have hcop : ∀ r ∈ R ⊓ Cen (b * w), ∃ m : ℕ, Nat.Coprime 3 m ∧
      r ^ m ∈ Subgroup.zpowers (b * w) := by
    intro r hr
    obtain ⟨k, hk⟩ := hR2 r hr.1
    exact ⟨2 ^ k, Nat.Coprime.pow_right k (by norm_num), hk⟩
  obtain ⟨O, hOR, hZO, hOdec, hOc⟩ := exists_central_complement hZR₀ hZc hZ3 hcop
  have hO2 : IsPGroup 2 O := by
    intro x
    obtain ⟨k, hk⟩ := hR2 x.1 (hOR x.2).1
    refine ⟨k, Subtype.ext ?_⟩
    have hmem : (x : H) ^ (2 ^ k) ∈ Subgroup.zpowers (b * w) ⊓ O := ⟨hk, O.pow_mem x.2 _⟩
    rw [hZO, Subgroup.mem_bot] at hmem
    simpa using hmem
  have key : ∀ g ∈ Nor R ⊓ Cen (b * w), ∀ x ∈ O, g * x * g⁻¹ ∈ O := by
    intro g hg x hx
    have hxR₀ : x ∈ R ⊓ Cen (b * w) := hOR hx
    have hxR : g * x * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg.1 x).mp hxR₀.1
    have hxC : g * x * g⁻¹ ∈ Cen (b * w) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (conj_commute_of_commute'
        (Subgroup.mem_centralizer_singleton_iff.mp hg.2)
        (Subgroup.mem_centralizer_singleton_iff.mp hxR₀.2))
    exact conj_mem_complement hZc hZ3 hOR hOdec hOc hx ⟨hxR, hxC⟩
  have hNor : ∀ g ∈ Nor R ⊓ Cen (b * w), g ∈ Nor O := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
    have := key g⁻¹ ((Nor R ⊓ Cen (b * w)).inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hbO : b ∈ Nor O := hNor b ⟨hb, hbC⟩
  have hcO : c ∈ Nor O := hNor c ⟨hc, hcC⟩
  have hβO : b * w ∈ Nor O := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (hOR hx).2
  have hwO : w ∈ Nor O := by
    have e : w = b⁻¹ * (b * w) := by group
    rw [e]
    exact (Nor O).mul_mem ((Nor O).inv_mem hbO) hβO
  have hBO : Subgroup.closure ({b, b₁, b₂} : Set H) ≤ Nor O := by
    rw [closure_bb₁b₂_eq]
    refine sup_le (Subgroup.zpowers_le.mpr hbO) (F.B₁_le.trans (sup_le ?_ ?_))
    · exact Subgroup.zpowers_le.mpr hwO
    · exact Subgroup.zpowers_le.mpr hcO
  have hObot : O = ⊥ := h.no_two O hO2 hBO
  have hR₀Z : ∀ r ∈ R ⊓ Cen (b * w), r ∈ Subgroup.zpowers (b * w) := by
    intro r hr
    obtain ⟨z, hz, x, hx, rfl⟩ := hOdec r hr
    rw [hObot, Subgroup.mem_bot] at hx
    rw [hx, mul_one]
    exact hz
  by_contra hRZ
  obtain ⟨r, hrR, hrZ⟩ := SetLike.not_le_iff_exists.mp hRZ
  have hmin : ∀ k : ℕ, ∀ r ∈ R, r ∉ Subgroup.zpowers (b * w) →
      r ^ (2 ^ k) ∈ Subgroup.zpowers (b * w) →
      ∃ r' ∈ R, r' ∉ Subgroup.zpowers (b * w) ∧ r' * r' ∈ Subgroup.zpowers (b * w) := by
    intro k
    induction k with
    | zero =>
      intro r hr hrZ hk
      exact absurd (by simpa using hk) hrZ
    | succ k ih =>
      intro r hr hrZ hk
      by_cases hmid : r ^ (2 ^ k) ∈ Subgroup.zpowers (b * w)
      · exact ih r hr hrZ hmid
      · refine ⟨r ^ (2 ^ k), R.pow_mem hr _, hmid, ?_⟩
        have e : r ^ (2 ^ k) * r ^ (2 ^ k) = r ^ (2 ^ (k + 1)) := by
          rw [← pow_two, ← pow_mul, ← pow_succ]
        rw [e]
        exact hk
  obtain ⟨k, hk⟩ := hR2 r hrR
  obtain ⟨r', hr'R, hr'Z, hr'2⟩ := hmin k r hrR hrZ hk
  have hr'N : r' ∈ Nor (Subgroup.zpowers (b * w)) := hRΓ hr'R
  have hr'C : r' ∉ Cen (b * w) := fun hC => hr'Z (hR₀Z r' ⟨hr'R, hC⟩)
  have hr'β : r' * (b * w) * r'⁻¹ = (b * w)⁻¹ := by
    have hmem := (Subgroup.mem_normalizer_iff.mp hr'N (b * w)).mp (Subgroup.mem_zpowers _)
    have hne : r' * (b * w) * r'⁻¹ ≠ 1 := by
      intro h1
      apply hβ1
      calc b * w = r'⁻¹ * (r' * (b * w) * r'⁻¹) * r' := by group
        _ = 1 := by rw [h1]; group
    rcases eq_or_inv_of_mem_zpowers_of_pow_three hβ3 hβ1 hmem hne with h1 | h1
    · exact absurd (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq' h1)) hr'C
    · exact h1
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hr'2
  have hr'sq : r' * r' = 1 := by
    have h1 : r' * (r' * r') * r'⁻¹ = r' * r' := by group
    have h2 : r' * (r' * r') * r'⁻¹ = (r' * r')⁻¹ := by
      rw [← ha]
      have := map_zpow (MulAut.conj r') (b * w) a
      simp only [MulAut.conj_apply] at this
      rw [this, hr'β, inv_zpow]
    have h3 : (r' * r') * (r' * r') = 1 := by
      have : r' * r' = (r' * r')⁻¹ := h1.symm.trans h2
      calc (r' * r') * (r' * r') = (r' * r') * (r' * r')⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel _
    have hz3 : (r' * r') ^ 3 = 1 := by
      rw [← ha, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hβ3, one_zpow]
    calc r' * r' = (r' * r') * ((r' * r') * (r' * r')) := by rw [h3, mul_one]
      _ = (r' * r') ^ 3 := (pow_three (r' * r')).symm
      _ = 1 := hz3
  have hr'inv : r'⁻¹ = r' := inv_eq_of_mul_eq_one_right hr'sq
  have hbβ : b * (b * w) * b⁻¹ = b * w := by
    rw [← F.beta_comm_b h]
    group
  have hxR : b * r' * b⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hb r').mp hr'R
  have hxβ : (b * r' * b⁻¹) * (b * w) * (b * r' * b⁻¹)⁻¹ = (b * w)⁻¹ := by
    calc (b * r' * b⁻¹) * (b * w) * (b * r' * b⁻¹)⁻¹
        = b * (r' * (b⁻¹ * (b * w) * b) * r'⁻¹) * b⁻¹ := by group
      _ = b * (r' * (b * w) * r'⁻¹) * b⁻¹ := by
        rw [show b⁻¹ * (b * w) * b = b * w by
          have := hbβ
          calc b⁻¹ * (b * w) * b = b⁻¹ * (b * (b * w) * b⁻¹) * b := by rw [this]
            _ = b * w := by group]
      _ = b * (b * w)⁻¹ * b⁻¹ := by rw [hr'β]
      _ = (b * (b * w) * b⁻¹)⁻¹ := by group
      _ = (b * w)⁻¹ := by rw [hbβ]
  have hxr'C : (b * r' * b⁻¹) * r' ∈ Cen (b * w) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_conj_eq' ?_)
    calc (b * r' * b⁻¹ * r') * (b * w) * (b * r' * b⁻¹ * r')⁻¹
        = (b * r' * b⁻¹) * (r' * (b * w) * r'⁻¹) * (b * r' * b⁻¹)⁻¹ := by group
      _ = (b * r' * b⁻¹) * (b * w)⁻¹ * (b * r' * b⁻¹)⁻¹ := by rw [hr'β]
      _ = ((b * r' * b⁻¹) * (b * w) * (b * r' * b⁻¹)⁻¹)⁻¹ := by group
      _ = b * w := by rw [hxβ, inv_inv]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
    (hR₀Z _ ⟨R.mul_mem hxR hr'R, hxr'C⟩)
  have hxi : b * r' * b⁻¹ = (b * w) ^ i * r' := by
    have : b * r' * b⁻¹ = ((b * r' * b⁻¹) * r') * r'⁻¹ := by group
    rw [this, ← hi, hr'inv]
  have hconjb : r' * b * r'⁻¹ = (b * w) ^ (-i) * b := by
    have e1 : b * r' = (b * w) ^ i * r' * b := by
      calc b * r' = (b * r' * b⁻¹) * b := by group
        _ = (b * w) ^ i * r' * b := by rw [hxi]
    have e2 : r' * (b * w) ^ i * r'⁻¹ = (b * w) ^ (-i) := by
      have := map_zpow (MulAut.conj r') (b * w) i
      simp only [MulAut.conj_apply] at this
      rw [this, hr'β, inv_zpow']
    rw [hr'inv] at e2 ⊢
    calc r' * b * r' = r' * (b * r') := by group
      _ = r' * ((b * w) ^ i * r' * b) := by rw [e1]
      _ = (r' * (b * w) ^ i * r') * b := by group
      _ = (b * w) ^ (-i) * b := by rw [e2]
  have hbE : b ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hEmem : r' * b * r'⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b * w) := by
    rw [hconjb]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.zpow_mem _
      (Subgroup.mem_zpowers _) _)) hbE
  have hmemb : r' * b * r'⁻¹ ∈ Subgroup.zpowers b :=
    h.conj_mem_zpowers_of_pgroup (F.isPGroup_E h) hbE hEmem
  obtain ⟨k', hk'⟩ := Subgroup.mem_zpowers_iff.mp hmemb
  have hβi : (b * w) ^ i = 1 := by
    have e : (b * w) ^ (-i) = b ^ (k' - 1) * 1 := by
      rw [mul_one]
      calc (b * w) ^ (-i) = ((b * w) ^ (-i) * b) * b⁻¹ := by group
        _ = b ^ (k' - 1) := by rw [← hconjb, ← hk']; group
    obtain ⟨h3a, h3b⟩ := F.beta_pow_eq h J.one_mem e
    have h3c : (3 : ℤ) ∣ k' - 1 := by
      have := (orderOf_dvd_iff_zpow_eq_one (x := w) (i := k' - 1)).mpr h3b.symm
      rwa [F.w_orderOf h] at this
    have h3i : (3 : ℤ) ∣ i := by omega
    obtain ⟨q, hq⟩ := h3i
    have hβ3z : (b * w) ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact hβ3
    rw [hq, zpow_mul, hβ3z, one_zpow]
  have hr'b : r' * b * r'⁻¹ = b := by
    rw [hconjb, zpow_neg, hβi, inv_one, one_mul]
  have hr'w : r' * w * r'⁻¹ = b * w⁻¹ := by
    have hr'b' : r' * b⁻¹ * r'⁻¹ = b⁻¹ := by
      calc r' * b⁻¹ * r'⁻¹ = (r' * b * r'⁻¹)⁻¹ := by group
        _ = b⁻¹ := by rw [hr'b]
    have hbw : Commute b w := (F.w_comm_b h).symm
    calc r' * w * r'⁻¹ = (r' * b⁻¹ * r'⁻¹) * (r' * (b * w) * r'⁻¹) := by group
      _ = b⁻¹ * (b * w)⁻¹ := by rw [hr'b', hr'β]
      _ = b⁻¹ * (b⁻¹ * w⁻¹) := by rw [mul_inv_rev, hbw.inv_inv.eq]
      _ = (b⁻¹ * b⁻¹) * w⁻¹ := by group
      _ = b * w⁻¹ := by
        have : b⁻¹ * b⁻¹ = b := by
          calc b⁻¹ * b⁻¹ = b⁻¹ * b⁻¹ * b ^ 3 := by rw [hb3, mul_one]
            _ = b := by group
        rw [this]
  have hwB : w ∈ Subgroup.closure ({b, b₁, b₂} : Set H) := FS79Hyp.B₁_le_B b b₁ b₂ F.w_mem
  have hybB : b * w⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H) :=
    Subgroup.mul_mem _ (FS79Hyp.zpowers_le_B b b₁ b₂ (Subgroup.mem_zpowers b))
      (Subgroup.inv_mem _ hwB)
  obtain ⟨n, hn, hnw⟩ := h.fusion_B (g := r') hwB hybB hr'w
  obtain ⟨k₂, hk₂, y, hy, j, hj, hn_eq, hconj, hjB⟩ := h.nor_B_decomp hn
  have hbwJ : b * w⁻¹ ∈ J := by
    rw [← hnw, hconj w F.w_mem]
    exact J.mul_mem (J.mul_mem hj (F.w_mem_J h)) (J.inv_mem hj)
  apply h.b_not_mem_J
  have := J.mul_mem hbwJ (F.w_mem_J h)
  simpa using this

theorem beta_inv_ne : (b * w)⁻¹ ≠ b * w := by
  intro h1
  have hx2 : (b * w) * (b * w) = 1 := by
    calc (b * w) * (b * w) = (b * w) * (b * w)⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel _
  have hx3 : (b * w) * ((b * w) * (b * w)) = 1 := by
    rw [← pow_three]
    exact F.beta_pow_three h
  rw [hx2, mul_one] at hx3
  exact F.beta_ne_one h hx3

theorem qdata : QData (Nor (Subgroup.zpowers (b * w))) (Subgroup.zpowers (b * w)) b (t * τ) c J'
    where
  Z_le := Subgroup.le_normalizer
  Z_norm := fun g hg z hz => (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  b_mem := mem_Nor_zpowers_of_comm (F.beta_comm_b h).symm
  t_mem := F.hat_mem_Nor h
  c_mem := mem_Nor_zpowers_of_comm (F.beta_comm_c h)
  J'_le := fun x hx => mem_Nor_zpowers_of_comm (F.J'_comm_beta h hx)
  c_mem_J := F.c_mem_J'
  b3 := by
    rw [← h.ord_b]
    exact pow_orderOf_eq_one b
  b_nmem := fun hb => by
    have hw : w ∈ Subgroup.zpowers (b * w) := by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) (Subgroup.mem_zpowers (b * w))
      rwa [inv_mul_cancel_left] at this
    have hmem : w ∈ Subgroup.zpowers (b * w) ⊓ J := ⟨hw, F.w_mem_J h⟩
    rw [F.zpowers_beta_inf_J h, Subgroup.mem_bot] at hmem
    exact F.w_ne hmem
  t2 := F.hat_sq h
  t_nmem := fun ht => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hcomm : (t * τ) * (b * w) = (b * w) * (t * τ) := by
      rw [← hk]
      exact (Commute.zpow_left (Commute.refl (b * w)) k).eq
    have h1 : (t * τ) * (b * w) * (t * τ)⁻¹ = b * w := by
      rw [hcomm]
      group
    rw [F.hat_beta h] at h1
    exact F.beta_inv_ne h h1
  tb := F.hat_inv_b h
  c3 := F.c3
  c_nmem := fun hc => F.c_ne (by
    have hmem : c ∈ Subgroup.zpowers (b * w) ⊓ J := ⟨hc, F.c_mem_J h⟩
    rw [F.zpowers_beta_inf_J h, Subgroup.mem_bot] at hmem
    exact hmem)
  J'_iso := F.J'_iso
  J'_inf_Z := by
    rw [eq_bot_iff]
    rintro x ⟨hxJ', hxZ⟩
    have hmem : x ∈ Subgroup.zpowers (b * w) ⊓ J := ⟨hxZ, F.J'_le hxJ'⟩
    rw [F.zpowers_beta_inf_J h] at hmem
    exact hmem
  J'_comm_b := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.J_le_cen_b (F.J'_le hj))
  J'_comm_t := fun j hj =>
    (F.closure_comm_J' h (Subgroup.subset_closure (by simp)) hj).symm
  N_J := fun g hg j hj => F.N_J h hg hj
  struct_b := F.struct_b h
  struct_c := F.struct_c h
  no2 := fun R hRΓ hZR hR2 hb hc => F.no2 h hRΓ hZR hR2 hb hc
  weak := fun h' _ hh => F.weak_E h hh

theorem ctlEq (hR1K : KF_FS79Prop2OneK) (hK : KCore.KGroupNonab InCatalog H) :
    CtlEq b (b * w) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have D := F.qdata h
  haveI hN : ((Subgroup.zpowers (b * w)).subgroupOf (Nor (Subgroup.zpowers (b * w)))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using D.Z_norm (g : H) g.2 (n : H) hn⟩
  obtain ⟨Ot, hZO, hOΓ, hOn, hO6, hdec⟩ := D.conclusionP
    (fun G _ _ => KCore.KGroupNonab InCatalog G) (fun G _ _ hG => hR1K G hG)
    (kGroupNonab_quotient hK _ _)
  have hβ3 := F.beta_pow_three h
  have hβ1 := F.beta_ne_one h
  have hZ3 : Nat.card (Subgroup.zpowers (b * w)) = 3 := F.card_Z h
  have hOcen : ∀ o ∈ Ot, o * (b * w) = (b * w) * o := by
    intro o ho
    have hoN : o ∈ Nor (Subgroup.zpowers (b * w)) := hOΓ ho
    have hmem := (Subgroup.mem_normalizer_iff.mp hoN (b * w)).mp (Subgroup.mem_zpowers _)
    have hne : o * (b * w) * o⁻¹ ≠ 1 := by
      intro h1
      apply hβ1
      calc b * w = o⁻¹ * (o * (b * w) * o⁻¹) * o := by group
        _ = 1 := by rw [h1]; group
    rcases eq_or_inv_of_mem_zpowers_of_pow_three hβ3 hβ1 hmem hne with h1 | h1
    · exact comm_of_conj_eq' h1
    · exfalso
      obtain ⟨m, hm6, hm⟩ := hO6 o ho
      obtain ⟨q, hq⟩ : Odd m :=
        Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_left (by norm_num) hm6)
      have h1' : o * (b * w) = (b * w)⁻¹ * o := by
        calc o * (b * w) = (o * (b * w) * o⁻¹) * o := by group
          _ = (b * w)⁻¹ * o := by rw [h1]
      have h1'' : o * (b * w)⁻¹ = (b * w) * o := by
        calc o * (b * w)⁻¹ = (o * (b * w) * o⁻¹)⁻¹ * o := by group
          _ = (b * w) * o := by rw [h1, inv_inv]
      have hc2 : Commute (o ^ 2) (b * w) := by
        show o ^ 2 * (b * w) = (b * w) * o ^ 2
        calc o ^ 2 * (b * w) = o * (o * (b * w)) := by rw [pow_two, mul_assoc]
          _ = o * ((b * w)⁻¹ * o) := by rw [h1']
          _ = (o * (b * w)⁻¹) * o := by group
          _ = ((b * w) * o) * o := by rw [h1'']
          _ = (b * w) * o ^ 2 := by rw [pow_two, mul_assoc]
      have hcq' : ((o ^ 2) ^ q) * (b * w)⁻¹ = (b * w)⁻¹ * (o ^ 2) ^ q :=
        ((hc2.inv_right).pow_left q).eq
      have hom : o ^ m * (b * w) = (b * w)⁻¹ * o ^ m := by
        rw [hq, pow_succ, pow_mul]
        calc ((o ^ 2) ^ q * o) * (b * w) = (o ^ 2) ^ q * (o * (b * w)) := by group
          _ = (o ^ 2) ^ q * ((b * w)⁻¹ * o) := by rw [h1']
          _ = ((o ^ 2) ^ q * (b * w)⁻¹) * o := by group
          _ = ((b * w)⁻¹ * (o ^ 2) ^ q) * o := by rw [hcq']
          _ = (b * w)⁻¹ * ((o ^ 2) ^ q * o) := by group
      have hmcomm : o ^ m * (b * w) = (b * w) * o ^ m := by
        obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hm
        rw [← ha]
        exact (Commute.zpow_left (Commute.refl (b * w)) a).eq
      have : (b * w)⁻¹ * o ^ m = (b * w) * o ^ m := hom.symm.trans hmcomm
      exact F.beta_inv_ne h (mul_right_cancel this)
  have hZc : ∀ r ∈ Ot, ∀ z ∈ Subgroup.zpowers (b * w), r * z = z * r := by
    intro r hr z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (hOcen r hr) k).eq
  have hcop : ∀ r ∈ Ot, ∃ m : ℕ, Nat.Coprime 3 m ∧ r ^ m ∈ Subgroup.zpowers (b * w) := by
    intro r hr
    obtain ⟨m, hm6, hm⟩ := hO6 r hr
    exact ⟨m, Nat.Coprime.coprime_dvd_left (by norm_num : 3 ∣ 6) hm6, hm⟩
  obtain ⟨O, hOR, hZOb, hOdec, hOc⟩ := exists_central_complement hZO hZc hZ3 hcop
  have hOopp : O ≤ Opp 3 (Nor (Subgroup.zpowers (b * w))) :=
    L14.le_Opp_of_normalized (hOR.trans hOΓ)
      (fun g hg x hx => conj_mem_complement hZc hZ3 hOR hOdec hOc hx (hOn g hg x (hOR hx))) hOc
  have hZN : Subgroup.zpowers (b * w) ≤ Nor (Subgroup.zpowers b) :=
    Subgroup.zpowers_le.mpr (mem_Nor_zpowers_of_comm (F.beta_comm_b h))
  have hΓdec : ∀ γ ∈ Nor (Subgroup.zpowers (b * w)), ∃ x ∈ Opp 3 (Nor (Subgroup.zpowers (b * w))),
      ∃ m ∈ Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers (b * w)), γ = x * m := by
    intro γ hγ
    obtain ⟨o', ho', n, hn, hγ'⟩ := hdec γ hγ
    obtain ⟨z, hz, x, hx, rfl⟩ := hOdec o' ho'
    have hxz : x * z = z * x := hZc x (hOR hx) z hz
    refine ⟨x, hOopp hx, z * n, ⟨?_, ?_⟩, ?_⟩
    · exact (Nor _).mul_mem (hZN hz) (F.Nor_E_le_Nor h hn.2)
    · exact (Nor _).mul_mem (Subgroup.le_normalizer hz) hn.1
    · rw [hγ', ← mul_assoc, ← hxz, mul_assoc]
  show setMul (Opp 3 (Nor (Subgroup.zpowers (b * w))))
    (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers (b * w))) =
      Nor (Subgroup.zpowers (b * w))
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨o, ho, k, hk, rfl⟩
    exact (Nor _).mul_mem (L14.Opp_le 3 _ ho) hk.2
  · intro g hg
    obtain ⟨x, hx, m, hm, rfl⟩ := hΓdec g hg
    exact ⟨x, hx, m, hm, rfl⟩

end Frame

end Ctl34

end CFSG.RankThree.PartTwo.Sec21.FF81
