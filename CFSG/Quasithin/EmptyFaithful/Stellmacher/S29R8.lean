module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S29Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S27Tools

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S29

open CosetGeom

namespace S29Step5

section Pure

variable {G : Type} [Group G]

theorem mul_inv_mem_of_relIndex_two {A B : Subgroup G} (h : A.relIndex B = 2) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) (hxA : x ∉ A) (hyA : y ∉ A) : x * y⁻¹ ∈ A := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h
  have key : ∀ z : G, (hz : z ∈ B) → z ∉ A → z * (a : G) ∈ A := fun z hz hzA => by
    rcases ha ⟨z, hz⟩ with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 (by simpa [Subgroup.mem_subgroupOf] using hzA)
  have := A.mul_mem (key x hx hxA) (A.inv_mem (key y hy hyA))
  simpa [mul_assoc] using this

theorem comm_mul_right {n v q : G} (h2 : n * (q * v⁻¹ * q⁻¹) = (q * v⁻¹ * q⁻¹) * n) :
    v * (n * q) * v⁻¹ * (n * q)⁻¹ = v * q * v⁻¹ * q⁻¹ := by
  calc v * (n * q) * v⁻¹ * (n * q)⁻¹ = v * (n * (q * v⁻¹ * q⁻¹) * n⁻¹) := by group
    _ = v * q * v⁻¹ * q⁻¹ := by rw [h2]; group

theorem comm_conj_swap {v q : G} (h : q * (q * v * q⁻¹) * q⁻¹ = v) :
    v * q * v⁻¹ * q⁻¹ = ((q * v * q⁻¹) * q * (q * v * q⁻¹)⁻¹ * q⁻¹)⁻¹ := by
  have e1 : v * q * v⁻¹ * q⁻¹ = v * (q * v * q⁻¹)⁻¹ := by group
  generalize q * v * q⁻¹ = z at h e1 ⊢
  have e2 : (z * q * z⁻¹ * q⁻¹)⁻¹ = (q * z * q⁻¹) * z⁻¹ := by group
  rw [e1, e2, h]

end Pure

section Geo

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

theorem comm_Zv_Qv (hA : F53Amalgam H M S) (δ : Geo H M) {z x : G} (hz : z ∈ Zv δ)
    (hx : x ∈ Qv δ) : x * z = z * x :=
  Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA δ hz).2 x hx

theorem comm_Zv_of_le (hA : F53Amalgam H M S) {a b : Geo H M} (hle : Zv a ≤ Qv b) {x y : G}
    (hx : x ∈ Zv a) (hy : y ∈ Zv b) : x * y = y * x :=
  comm_Zv_Qv hA b hy (hle hx)

theorem comm_Zv (hA : F53Amalgam H M S) (δ : Geo H M) {x y : G} (hx : x ∈ Zv δ)
    (hy : y ∈ Zv δ) : x * y = y * x := by
  have := (isElemAbelian_Zv hA δ).1
  exact setLike_mul_comm hx hy

omit [Finite G] in
theorem Qv_le_stab_self (δ : Geo H M) : Qv δ ≤ stab δ := pCoreOf_le 2 _

omit [Finite G] in
theorem Qv_le_normalizer (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Qv δ : Set G) :=
  le_normalizer_pCoreOf 2 (stab δ)

theorem Z₂_le_Qβ (hs : Sit29 H M S α a₂ a₃ β) : Zv a₂ ≤ Qv β := hs.swap₁₂.Zv_le_Qv_right

theorem Z₃_le_Qβ (hs : Sit29 H M S α a₂ a₃ β) : Zv a₃ ≤ Qv β :=
  hs.swap₂₃.swap₁₂.Zv_le_Qv_right

theorem Qα_le_stab_β (hs : Sit29 H M S α a₂ a₃ β) : Qv α ≤ stab β :=
  Qv_le_stab_of_mem_nbrs hs.amalg (show β ∈ nbrs α from hs.adj)

theorem Qβ_le_stab_α (hs : Sit29 H M S α a₂ a₃ β) : Qv β ≤ stab α :=
  Qv_le_stab_of_mem_nbrs hs.amalg hs.n₁

theorem relIndex_N (hs : Sit29 H M S α a₂ a₃ β) : (Qv α ⊓ Qv β).relIndex (Qv α) = 2 := by
  have hn : Qv α ≤ Subgroup.normalizer (Qv β : Set G) :=
    (Qα_le_stab_β hs).trans (Qv_le_normalizer β)
  rw [relIndex_inf_eq_relIndex_sup hn, hs.sup_Qv]
  exact hs.relIndex_Qv_right

theorem relIndex_R (hs : Sit29 H M S α a₂ a₃ β) (h8 : Nat.card ↥(Zv α ⊓ Zv a₂) = 8) :
    (Zv α ⊓ Zv a₂).relIndex (Zv a₂) = 2 := by
  have h := Subgroup.relIndex_mul_card (H := Zv α ⊓ Zv a₂) (K := Zv a₂)
  have e : (Zv α ⊓ Zv a₂) ⊓ Zv a₂ = Zv α ⊓ Zv a₂ := inf_eq_left.mpr inf_le_right
  rw [e, h8, hs.swap₁₂.card_Zv] at h
  omega

theorem mem_Z₁_of_mem_Z₂_Z₃ (hs : Sit29 H M S α a₂ a₃ β) {y : G} (h2 : y ∈ Zv a₂)
    (h3 : y ∈ Zv a₃) : y ∈ Zv α := by
  have : y ∈ Zv a₂ ⊓ Zv a₃ := ⟨h2, h3⟩
  rw [← hs.R_eq₂] at this
  exact this.1

theorem cent_N₂ (hs : Sit29 H M S α a₂ a₃ β) (h8 : Nat.card ↥(Zv α ⊓ Zv a₂) = 8) {n v : G}
    (hn : n ∈ Qv α ⊓ Qv β) (hv : v ∈ Zv a₂) : n * v = v * n := by
  have hA := hs.amalg
  have hsβ : n ∈ stab a₂ ⊓ stab β :=
    ⟨Qv_le_stab_of_mem_nbrs hA hs.n₂ hn.2, Qv_le_stab_self β hn.2⟩
  have hQ : n ∈ Qv a₂ :=
    hs.mod₂.centralizer_order_eight (Zv α ⊓ Zv a₂) inf_le_right
      (fun g hg => hs.R_normal hg.2) h8 n hsβ (fun u hu => comm_Zv_Qv hA α hu.1 hn.1)
  exact comm_Zv_Qv hA a₂ hv hQ

theorem cent_N₃ (hs : Sit29 H M S α a₂ a₃ β) (h8 : Nat.card ↥(Zv α ⊓ Zv a₂) = 8) {n v : G}
    (hn : n ∈ Qv α ⊓ Qv β) (hv : v ∈ Zv a₃) : n * v = v * n :=
  cent_N₂ hs.swap₂₃ (by rw [← hs.R_eq₁]; exact h8) hn hv

theorem cent_N (hs : Sit29 H M S α a₂ a₃ β) (h8 : Nat.card ↥(Zv α ⊓ Zv a₂) = 8) {n v : G}
    (hn : n ∈ Qv α ⊓ Qv β) (hv : v ∈ Zv a₂ ∨ v ∈ Zv a₃) : n * v = v * n :=
  hv.elim (cent_N₂ hs h8 hn) (cent_N₃ hs h8 hn)

theorem conj_Z₂ (hs : Sit29 H M S α a₂ a₃ β) {q : G} (hq : q ∈ Qv α) (hqβ : q ∉ Qv β) {y : G}
    (hy : y ∈ Zv a₂) : q * y * q⁻¹ ∈ Zv a₃ := by
  have h := (hs.Zv_conj_swap (Qv_le_stab_self α hq) (Qα_le_stab_β hs hq) hqβ).1
  rw [← h]
  refine mem_conjSub.mpr ?_
  have e : q⁻¹ * (q * y * q⁻¹) * q = y := by group
  rw [e]
  exact hy

theorem conj_Z₃ (hs : Sit29 H M S α a₂ a₃ β) {q : G} (hq : q ∈ Qv α) (hqβ : q ∉ Qv β) {y : G}
    (hy : y ∈ Zv a₃) : q * y * q⁻¹ ∈ Zv a₂ := by
  have h := (hs.Zv_conj_swap (Qv_le_stab_self α hq) (Qα_le_stab_β hs hq) hqβ).2
  rw [← h]
  refine mem_conjSub.mpr ?_
  have e : q⁻¹ * (q * y * q⁻¹) * q = y := by group
  rw [e]
  exact hy

theorem conj_Z₂₃ (hs : Sit29 H M S α a₂ a₃ β) {s : G} (hsα : s ∈ stab α) (hsβ : s ∈ stab β)
    {y : G} (hy : y ∈ Zv a₂) : s * y * s⁻¹ ∈ Zv a₂ ∨ s * y * s⁻¹ ∈ Zv a₃ := by
  by_cases hQ : s ∈ Qv β
  · left
    have h := stab_le_normalizer_Zv hs.amalg a₂ (Qv_le_stab_of_mem_nbrs hs.amalg hs.n₂ hQ)
    exact (Subgroup.mem_normalizer_iff.mp h y).mp hy
  · right
    have h := (hs.Zv_conj_swap hsα hsβ hQ).1
    rw [← h]
    refine mem_conjSub.mpr ?_
    have e : s⁻¹ * (s * y * s⁻¹) * s = y := by group
    rw [e]
    exact hy

theorem sq_mem_N (hs : Sit29 H M S α a₂ a₃ β) {q : G} (hq : q ∈ Qv α) (hqβ : q ∉ Qv β) :
    q * q ∈ Qv α ⊓ Qv β := by
  have hn : q * q⁻¹⁻¹ ∈ Qv α ⊓ Qv β := by
    refine mul_inv_mem_of_relIndex_two (relIndex_N hs) hq (Subgroup.inv_mem _ hq) ?_ ?_
    · exact fun h => hqβ h.2
    · exact fun h => hqβ (by simpa using Subgroup.inv_mem _ h.2)
  simpa using hn

theorem comm_q₂ (hs : Sit29 H M S α a₂ a₃ β) (h8 : Nat.card ↥(Zv α ⊓ Zv a₂) = 8) {q : G}
    (hq : q ∈ Qv α) (hqβ : q ∉ Qv β) {y₀ t : G} (hy₂ : y₀ ∈ Zv a₂) (hy₁ : y₀ ∉ Zv α)
    (ht : t = y₀ * q * y₀⁻¹ * q⁻¹) {v : G} (hv : v ∈ Zv a₂) :
    v * q * v⁻¹ * q⁻¹ = 1 ∨ v * q * v⁻¹ * q⁻¹ = t := by
  have hA := hs.amalg
  by_cases hvZ : v ∈ Zv α
  · left
    have := comm_Zv_Qv hA α hvZ hq
    rw [← this]
    group
  · right
    have hvR : v ∉ Zv α ⊓ Zv a₂ := fun h => hvZ h.1
    have hyR : y₀ ∉ Zv α ⊓ Zv a₂ := fun h => hy₁ h.1
    have hr : v * y₀⁻¹ ∈ Zv α ⊓ Zv a₂ :=
      mul_inv_mem_of_relIndex_two (relIndex_R hs h8) hv hy₂ hvR hyR
    set r := v * y₀⁻¹ with hrdef
    have hvr : v = r * y₀ := by rw [hrdef]; group
    have hr3 : r ∈ Zv a₃ := by
      have : r ∈ Zv a₂ ⊓ Zv a₃ := by rw [← hs.R_eq₂]; exact hr
      exact this.2
    have hw : q * y₀ * q⁻¹ ∈ Zv a₃ := conj_Z₂ hs hq hqβ hy₂
    have hc1 : Commute r y₀ := comm_Zv hA a₂ hr.2 hy₂
    have hc2 : Commute r (q * y₀ * q⁻¹) := comm_Zv hA a₃ hr3 hw
    have hrt : r * t = t * r := by
      have e : t = y₀ * (q * y₀ * q⁻¹)⁻¹ := by rw [ht]; group
      rw [e]
      exact (hc1.mul_right hc2.inv_right).eq
    have hrq : q * r⁻¹ * q⁻¹ = r⁻¹ := by
      have := (Commute.inv_right (show Commute q r from comm_Zv_Qv hA α hr.1 hq)).eq
      rw [this]
      group
    calc v * q * v⁻¹ * q⁻¹ = r * (y₀ * q * y₀⁻¹ * q⁻¹) * (q * r⁻¹ * q⁻¹) := by rw [hvr]; group
      _ = r * t * r⁻¹ := by rw [hrq, ← ht]
      _ = t := by rw [hrt]; group

theorem sq_t (hs : Sit29 H M S α a₂ a₃ β) (hb : 2 < bMin H M) {q : G} (hq : q ∈ Qv α)
    (hqβ : q ∉ Qv β) {y₀ t : G} (hy₂ : y₀ ∈ Zv a₂) (ht : t = y₀ * q * y₀⁻¹ * q⁻¹) :
    t * t = 1 := by
  have hA := hs.amalg
  have hw : q * y₀ * q⁻¹ ∈ Zv a₃ := conj_Z₂ hs hq hqβ hy₂
  have hc : Commute y₀ (q * y₀ * q⁻¹) :=
    comm_Zv_of_le hA (hs.swap₁₂.swap₂₃.Zv_le_Qv_other hb) hy₂ hw
  have e : t = y₀ * (q * y₀ * q⁻¹)⁻¹ := by rw [ht]; group
  have h1 : y₀ ^ 2 = 1 := (isElemAbelian_Zv hA a₂).2 y₀ hy₂
  have h2 : (q * y₀ * q⁻¹) ^ 2 = 1 := (isElemAbelian_Zv hA a₃).2 _ hw
  rw [e, ← sq, hc.inv_right.mul_pow, h1, inv_pow, h2, inv_one, one_mul]

theorem comm_q (hs : Sit29 H M S α a₂ a₃ β) (hb : 2 < bMin H M)
    (h8 : Nat.card ↥(Zv α ⊓ Zv a₂) = 8) {q : G} (hq : q ∈ Qv α) (hqβ : q ∉ Qv β) {y₀ t : G}
    (hy₂ : y₀ ∈ Zv a₂) (hy₁ : y₀ ∉ Zv α) (ht : t = y₀ * q * y₀⁻¹ * q⁻¹) {v : G}
    (hv : v ∈ Zv a₂ ∨ v ∈ Zv a₃) : v * q * v⁻¹ * q⁻¹ = 1 ∨ v * q * v⁻¹ * q⁻¹ = t := by
  rcases hv with hv | hv
  · exact comm_q₂ hs h8 hq hqβ hy₂ hy₁ ht hv
  · have hqq := sq_mem_N hs hq hqβ
    have hcq : (q * q) * v = v * (q * q) := cent_N₃ hs h8 hqq hv
    have hv' : q * v * q⁻¹ ∈ Zv a₂ := conj_Z₃ hs hq hqβ hv
    have hback : q * (q * v * q⁻¹) * q⁻¹ = v := by
      calc q * (q * v * q⁻¹) * q⁻¹ = (q * q) * v * (q * q)⁻¹ := by group
        _ = v := by rw [hcq]; group
    rw [comm_conj_swap hback]
    have ht2 : t⁻¹ = t := by
      have := sq_t hs hb hq hqβ hy₂ ht
      exact (mul_eq_one_iff_eq_inv.mp this).symm
    rcases comm_q₂ hs h8 hq hqβ hy₂ hy₁ ht hv' with h | h
    · left; rw [h, inv_one]
    · right; rw [h, ht2]

theorem comm_x (hs : Sit29 H M S α a₂ a₃ β) (hb : 2 < bMin H M)
    (h8 : Nat.card ↥(Zv α ⊓ Zv a₂) = 8) {q : G} (hq : q ∈ Qv α) (hqβ : q ∉ Qv β) {y₀ t : G}
    (hy₂ : y₀ ∈ Zv a₂) (hy₁ : y₀ ∉ Zv α) (ht : t = y₀ * q * y₀⁻¹ * q⁻¹) {v x : G}
    (hv : v ∈ Zv a₂ ∨ v ∈ Zv a₃) (hx : x ∈ Qv α) :
    v * x * v⁻¹ * x⁻¹ = 1 ∨ v * x * v⁻¹ * x⁻¹ = t := by
  by_cases hxN : x ∈ Qv β
  · left
    have := cent_N hs h8 ⟨hx, hxN⟩ hv
    rw [← this]
    group
  · have hn : x * q⁻¹ ∈ Qv α ⊓ Qv β :=
      mul_inv_mem_of_relIndex_two (relIndex_N hs) hx hq (fun h => hxN h.2) (fun h => hqβ h.2)
    obtain ⟨n, hn', rfl⟩ : ∃ n ∈ Qv α ⊓ Qv β, x = n * q := ⟨x * q⁻¹, hn, by group⟩
    have hw : q * v⁻¹ * q⁻¹ ∈ Zv a₂ ∨ q * v⁻¹ * q⁻¹ ∈ Zv a₃ := by
      rcases hv with hv | hv
      · exact Or.inr (conj_Z₂ hs hq hqβ (Subgroup.inv_mem _ hv))
      · exact Or.inl (conj_Z₃ hs hq hqβ (Subgroup.inv_mem _ hv))
    rw [comm_mul_right (cent_N hs h8 hn' hw)]
    exact comm_q hs hb h8 hq hqβ hy₂ hy₁ ht hv

end Geo

end S29Step5

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α a₂ a₃ β : Geo H M}

open S29Step5 in
theorem step5 (hs : Sit29 H M S α a₂ a₃ β) (hb : 2 < bMin H M) :
    Nat.card ↥(Zv α ⊓ Zv a₂) ≠ 8 := by
  intro h8
  have hA := hs.amalg
  obtain ⟨q, hq, hqβ⟩ := hs.exists_q
  obtain ⟨y₀, hy₂, hy₁⟩ := IsConcreteLE.not_le_iff_exists.mp hs.swap₁₂.not_Zv_le
  obtain ⟨t, ht⟩ : ∃ t : G, t = y₀ * q * y₀⁻¹ * q⁻¹ := ⟨_, rfl⟩
  have hw : q * y₀ * q⁻¹ ∈ Zv a₃ := conj_Z₂ hs hq hqβ hy₂
  have het : t = y₀ * (q * y₀ * q⁻¹)⁻¹ := by rw [ht]; group
  have ht1 : t ≠ 1 := by
    intro h1
    have hy3 : y₀ ∈ Zv a₃ := by
      have : q * y₀ * q⁻¹ = y₀ := by
        have h2 : y₀ * (q * y₀ * q⁻¹)⁻¹ = 1 := by rw [← het]; exact h1
        have := mul_inv_eq_one.mp h2
        exact this.symm
      rw [← this]
      exact hw
    exact hy₁ (mem_Z₁_of_mem_Z₂_Z₃ hs hy₂ hy3)
  have ht2 : t * t = 1 := sq_t hs hb hq hqβ hy₂ ht
  have htQ : t ∈ Qv β := by
    rw [het]
    exact Subgroup.mul_mem _ (Z₂_le_Qβ hs hy₂)
      (Subgroup.inv_mem _ (Z₃_le_Qβ hs hw))
  have hcomm : ∀ s ∈ stab β ⊓ stab α, s * t = t * s := by
    intro s hs'
    have hsβ : s ∈ stab β := hs'.1
    have hsα : s ∈ stab α := hs'.2
    have hx : s * q * s⁻¹ ∈ Qv α :=
      (Subgroup.mem_normalizer_iff.mp (Qv_le_normalizer α hsα) q).mp hq
    have hv : s * y₀ * s⁻¹ ∈ Zv a₂ ∨ s * y₀ * s⁻¹ ∈ Zv a₃ := conj_Z₂₃ hs hsα hsβ hy₂
    have hconj : s * t * s⁻¹ =
        (s * y₀ * s⁻¹) * (s * q * s⁻¹) * (s * y₀ * s⁻¹)⁻¹ * (s * q * s⁻¹)⁻¹ := by
      rw [ht]; group
    have hcases := comm_x hs hb h8 hq hqβ hy₂ hy₁ ht hv hx
    have hst : s * t * s⁻¹ = t := by
      rcases hcases with h | h
      · exfalso
        rw [← hconj] at h
        exact ht1 (by simpa using h)
      · rw [← hconj] at h
        exact h
    exact (mul_inv_eq_iff_eq_mul.mp hst)
  have htT : t ∈ stab β ⊓ stab α :=
    ⟨Qv_le_stab_self β htQ, Qβ_le_stab_α hs htQ⟩
  have htZ : t ∈ Zv β := by
    rw [(Zv_eq_omegaOneCenter_inf hs.amalg hs.n₁ hs.hz).1]
    refine Subgroup.subset_closure ⟨⟨htT, Subgroup.mem_centralizer_iff.mpr fun s hs' => ?_⟩, ?_⟩
    · exact hcomm s hs'
    · simpa [sq] using ht2
  have htR : t ∈ Zv a₃ := by
    have h1 : t ∈ Zv α ⊓ Zv a₂ := hs.Zv_right_le_R htZ
    rw [hs.R_eq₂] at h1
    exact h1.2
  have hy3 : y₀ ∈ Zv a₃ := by
    have : y₀ = t * (q * y₀ * q⁻¹) := by rw [het]; group
    rw [this]
    exact Subgroup.mul_mem _ htR hw
  exact hy₁ (mem_Z₁_of_mem_Z₂_Z₃ hs hy₂ hy3)

end F53.Stellmacher.S29

end CFSG.Quasithin
