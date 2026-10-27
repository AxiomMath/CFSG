module

public import CFSG.Walter.ReeOrder.JT.Section7K

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

theorem card_mul_relIndex {H K : Subgroup X} (hHK : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have h1 := Subgroup.relIndex_mul_index hHK
  have h2 := H.card_mul_index
  have h3 := K.card_mul_index
  have hK0 : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have : Nat.card H * H.relIndex K * K.index = Nat.card K * K.index := by
    rw [mul_assoc, h1, h2, h3]
  exact Nat.eq_of_mul_eq_mul_right hK0 this

theorem relIndex_dvd_of_pow_mem {p : ℕ} (hp : p ≠ 0) {Y Z : Subgroup X} (hZ : IsCyclic Z)
    (hYZ : Y ≤ Z) (hpow : ∀ z ∈ Z, z ^ p ∈ Y) : Y.relIndex Z ∣ p := by
  obtain ⟨g₀, hg₀⟩ := hZ
  obtain ⟨g, hZg⟩ : ∃ g : X, Z = Subgroup.zpowers g := by
    refine ⟨g₀, le_antisymm ?_ ?_⟩
    · intro z hz
      obtain ⟨k, hk⟩ := hg₀ ⟨z, hz⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact g₀.2
  subst hZg
  have hle : Subgroup.zpowers (g ^ p) ≤ Y := by
    rw [Subgroup.zpowers_le]
    exact hpow _ (Subgroup.mem_zpowers g)
  have hle' : Subgroup.zpowers (g ^ p) ≤ Subgroup.zpowers g := hle.trans hYZ
  refine (Subgroup.relIndex_dvd_of_le_left _ hle).trans ?_
  have hc := card_mul_relIndex hle'
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow' _ hp] at hc
  have hpos : 0 < orderOf g := orderOf_pos _
  set n := orderOf g with hn
  set d := n.gcd p with hd
  obtain ⟨m, hm⟩ : d ∣ n := Nat.gcd_dvd_left _ _
  have hgpos : 0 < d := Nat.gcd_pos_of_pos_left _ hpos
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm; omega
    · exact h0
  have hdiv : n / d = m := by
    rw [hm]
    exact Nat.mul_div_cancel_left m hgpos
  rw [hdiv] at hc
  have : (Subgroup.zpowers (g ^ p)).relIndex (Subgroup.zpowers g) = d := by
    have h2 : m * (Subgroup.zpowers (g ^ p)).relIndex (Subgroup.zpowers g) = m * d := by
      rw [hc, hm, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hm0 h2
  rw [this]
  exact Nat.gcd_dvd_right _ _

theorem inf_ne_bot_of_isCyclic {p : ℕ} [Fact p.Prime] {P H K : Subgroup X} (hP : IsCyclic P)
    (hPp : IsPGroup p P) (hHP : H ≤ P) (hKP : K ≤ P) (hH : H ≠ ⊥) (hK : K ≠ ⊥) :
    H ⊓ K ≠ ⊥ := by
  obtain ⟨a, ha⟩ := (hPp.to_le hHP).exists_card_eq
  obtain ⟨b, hb⟩ := (hPp.to_le hKP).exists_card_eq
  have key : ∀ {A B : Subgroup X} {m n : ℕ}, A ≤ P → B ≤ P → Nat.card A = p ^ m →
      Nat.card B = p ^ n → m ≤ n → A ≤ B := by
    intro A B m n hA hB hAm hBn hmn
    have hBc : IsCyclic B := by
      have : IsCyclic (B.subgroupOf P) := Subgroup.isCyclic _
      exact isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe hB).toMonoidHom (MulEquiv.surjective _)
    obtain ⟨A', hA'⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) p
      (n := m) (by rw [hBn]; exact pow_dvd_pow p hmn)
    have hA'P : A'.map B.subtype ≤ P := (Subgroup.map_subtype_le _).trans hB
    have heq : A'.map B.subtype = A := eq_of_le_of_isCyclic hP hA'P hA (by
      rw [Subgroup.card_map_of_injective B.subtype_injective, hA', hAm])
    rw [← heq]
    exact Subgroup.map_subtype_le _
  have hle : H ≤ K ∨ K ≤ H := by
    rcases le_total a b with hab | hab
    · exact Or.inl (key hHP hKP ha hb hab)
    · exact Or.inr (key hKP hHP hb ha hab)
  rcases hle with hle | hle
  · rwa [inf_eq_left.mpr hle]
  · rwa [inf_eq_right.mpr hle]

end General

namespace TorusConf

variable {h : JTHyp G} (c : TorusConf h)

theorem orderOf_w : orderOf c.w = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact c.w_mul_w) c.w_ne_one

theorem tw_mul_tw : h.t * c.w * (h.t * c.w) = 1 := by
  rw [mul_assoc, ← mul_assoc c.w, ← c.commute_t_w.eq, mul_assoc, c.w_mul_w, mul_one,
    h.t_mul_t]

theorem tw_ne_one : h.t * c.w ≠ 1 := fun h0 => c.t_ne_w (by
  rw [← mul_one h.t, ← c.w_mul_w, ← mul_assoc, h0, one_mul])

theorem orderOf_tw : orderOf (h.t * c.w) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact c.tw_mul_tw) c.tw_ne_one

theorem tw_mem_T₀ : h.t * c.w ∈ c.T₀ := c.mem_T₀.mpr (Or.inl rfl)

theorem t_ne_tw : h.t ≠ h.t * c.w := fun h0 => c.w_ne_one (by
  have := congrArg (h.t⁻¹ * ·) h0
  simpa using this.symm)

theorem w_ne_tw : c.w ≠ h.t * c.w := fun h0 => h.t_ne_one (by
  have := congrArg (· * c.w⁻¹) h0
  simpa using this.symm)

theorem orderOf_of_mem {u : G} (hu : u ∈ c.T₀) (hu1 : u ≠ 1) : orderOf u = 2 := by
  rcases c.mem_T₀.mp hu with rfl | rfl | rfl | rfl
  · exact c.orderOf_tw
  · exact h.orderOf_t
  · exact c.orderOf_w
  · exact absurd rfl hu1

theorem comm_of_mem {u v : G} (hu : u ∈ c.T₀) (hv : v ∈ c.T₀) : u * v = v * u := by
  have := c.isKleinFour_T₀
  have hc : IsMulCommutative c.T₀ := IsKleinFour.isMulCommutative
  exact congrArg Subtype.val (hc.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

end TorusConf

namespace JTHyp

variable (h : JTHyp G) (hp3 : h.p = 3)
include hp3

theorem relIndex_eq_mul
    (c : TorusConf h) {p : ℕ} [Fact p.Prime] (hpq : p ∣ (h.q - 1) / 2)
    {K₁ K₂ : Subgroup G} (hK₁ : IsPGroup p K₁) (hK₂₁ : K₂ ≤ K₁)
    (hT₁ : c.T₀ ≤ Subgroup.normalizer (K₁ : Set G))
    (hT₂ : c.T₀ ≤ Subgroup.normalizer (K₂ : Set G)) :
    K₂.relIndex K₁ =
      (K₂ ⊓ Subgroup.centralizer ({h.t} : Set G)).relIndex
          (K₁ ⊓ Subgroup.centralizer ({h.t} : Set G)) *
        (K₂ ⊓ Subgroup.centralizer ({c.w} : Set G)).relIndex
          (K₁ ⊓ Subgroup.centralizer ({c.w} : Set G)) *
        (K₂ ⊓ Subgroup.centralizer ({h.t * c.w} : Set G)).relIndex
          (K₁ ⊓ Subgroup.centralizer ({h.t * c.w} : Set G)) := by
  have h₁ := h.card_eq_mul_of_le_normalizer hp3 c hpq hK₁ hT₁
  have h₂ := h.card_eq_mul_of_le_normalizer hp3 c hpq (hK₁.to_le hK₂₁) hT₂
  have e := card_mul_relIndex hK₂₁
  have ea := card_mul_relIndex (inf_le_inf_right (Subgroup.centralizer ({h.t} : Set G)) hK₂₁)
  have eb := card_mul_relIndex (inf_le_inf_right (Subgroup.centralizer ({c.w} : Set G)) hK₂₁)
  have ec := card_mul_relIndex
    (inf_le_inf_right (Subgroup.centralizer ({h.t * c.w} : Set G)) hK₂₁)
  rw [← e, h₂, ← ea, ← eb, ← ec] at h₁
  have hpos : 0 < Nat.card (K₂ ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) *
      Nat.card (K₂ ⊓ Subgroup.centralizer ({c.w} : Set G) : Subgroup G) *
      Nat.card (K₂ ⊓ Subgroup.centralizer ({h.t * c.w} : Set G) : Subgroup G) :=
    Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h₁]
  ring

theorem relIndex_dvd_pow_three
    (c : TorusConf h) {p : ℕ} [hp : Fact p.Prime]
    (hpq : p ∣ (h.q - 1) / 2) {K₁ K₂ : Subgroup G} (hK₁ : IsPGroup p K₁) (hK₂₁ : K₂ ≤ K₁)
    (hT₁ : c.T₀ ≤ Subgroup.normalizer (K₁ : Set G))
    (hT₂ : c.T₀ ≤ Subgroup.normalizer (K₂ : Set G)) (hpow : ∀ z ∈ K₁, z ^ p ∈ K₂) :
    K₂.relIndex K₁ ∣ p ^ 3 := by
  have key : ∀ u ∈ c.T₀, u ≠ 1 →
      (K₂ ⊓ Subgroup.centralizer ({u} : Set G)).relIndex
        (K₁ ⊓ Subgroup.centralizer ({u} : Set G)) ∣ p := by
    intro u hu hu1
    have hcyc := h.isCyclic_of_le_centralizer_pi hp3 hpq (hK₁.to_le inf_le_left)
      (c.orderOf_of_mem hu hu1) (inf_le_right :
        K₁ ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({u} : Set G))
    exact relIndex_dvd_of_pow_mem hp.out.ne_zero hcyc
      (inf_le_inf_right _ hK₂₁) fun z hz => ⟨hpow z hz.1, Subgroup.pow_mem _ hz.2 p⟩
  rw [h.relIndex_eq_mul hp3 c hpq hK₁ hK₂₁ hT₁ hT₂, show p ^ 3 = p * p * p by ring]
  exact Nat.mul_dvd_mul (Nat.mul_dvd_mul (key _ c.t_mem_T₀ h.t_ne_one)
    (key _ c.w_mem_T₀ c.w_ne_one)) (key _ c.tw_mem_T₀ c.tw_ne_one)

end JTHyp

end CFSG.Walter.JT
