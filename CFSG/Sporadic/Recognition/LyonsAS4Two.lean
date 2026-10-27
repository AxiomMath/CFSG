module

public import CFSG.Sporadic.Recognition.LyonsAS4Local
public import CFSG.Sporadic.Recognition.LyonsAS4Sylow
public import CFSG.Sporadic.Recognition.LyonsAS4E8
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}

namespace LyData

theorem not_isConj_x1p_y12p (D : LyData G t ρ) {x y : ↥(centralizer ({t} : Set G))}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hx : ρ x = x1p) (hy : ρ y = y12p) :
    ¬ IsConj (x : G) (y : G) := by
  intro hconj
  have hcov := D.cover
  have h128 : 128 ∣ Nat.card ↥(centralizer ({(x : G)} : Set G)) := by
    have h1 := D.card_centralizer_inf hx3
    rw [hx, card_CA_x1p] at h1
    have h2 : Nat.card ↥(centralizer ({(x : G)} : Set G) ⊓ centralizer ({t} : Set G)) ∣
        Nat.card ↥(centralizer ({(x : G)} : Set G)) := Subgroup.card_dvd_of_le inf_le_left
    rw [h1] at h2
    exact (by norm_num : 128 ∣ 2 * 60480).trans h2
  have hS0A : S0 ≤ alternatingGroup (Fin 11) := S0_le_CA.trans inf_le_right
  set S : Subgroup G := (S0.comap ρ).map (centralizer ({t} : Set G)).subtype with hS
  have hSle : S ≤ centralizer ({(y : G)} : Set G) ⊓ centralizer ({t} : Set G) := by
    rintro g ⟨s, hs, rfl⟩
    refine ⟨?_, s.2⟩
    have hsy : ρ s * ρ y = ρ y * ρ s := by
      rw [hy]
      exact mem_centralizer_singleton_iff.1 (S0_le_CA hs).1
    have := hcov.commute_of_rho_commute_pow_three hy3 hsy
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hSt : t ∈ S := ⟨⟨t, self_mem_centralizer_singleton t⟩, by
    show ρ _ ∈ S0
    rw [hcov.rho_z]; exact one_mem _, rfl⟩
  have hScard : Nat.card S = 16 := by
    rw [hS, Subgroup.card_map_of_injective (centralizer ({t} : Set G)).subtype_injective,
      hcov.card_comap hS0A, card_S0]
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 4) (by rw [hScard]; norm_num)
  have hTK : Nat.card S * 135 =
      Nat.card ↥(centralizer ({(y : G)} : Set G) ⊓ centralizer ({t} : Set G)) := by
    rw [hScard, D.card_centralizer_inf hy3, hy, card_CA_y12p]
  have hty : t * (y : G) = (y : G) * t := (mem_centralizer_singleton_iff.1 y.2).symm
  have hZ : ∀ c ∈ S, orderOf c = 2 → (∀ s ∈ S, s * c = c * s) → c = t := by
    rintro _ ⟨c, hc, rfl⟩ hc2 hcen
    have hcz : orderOf c = 2 := by
      rw [← hc2]
      exact (orderOf_injective (centralizer ({t} : Set G)).subtype
        (centralizer ({t} : Set G)).subtype_injective c).symm
    have hcc : c ^ 2 = 1 := by rw [← hcz]; exact pow_orderOf_eq_one c
    have hcc' : ρ c ∈ S0 := hc
    have hcen' : ∀ s ∈ S0, s * ρ c = ρ c * s := by
      intro s hs
      obtain ⟨s', hs'⟩ := hcov.exists_lift (mem_alternatingGroup.1 (hS0A hs))
      have := hcen (s' : G) ⟨s', by show ρ s' ∈ S0; rw [hs']; exact hs, rfl⟩
      have h2 : s' * c = c * s' := Subtype.ext this
      rw [← hs', ← map_mul, ← map_mul, h2]
    rcases S0_center hcc' hcen' with h1 | ⟨h1, h2⟩
    · rcases hcov.mem_ker_iff.1 h1 with h3 | h3
      · exfalso
        rw [h3, orderOf_one] at hcz
        exact absurd hcz (by norm_num)
      · rw [h3]; rfl
    · exfalso
      have := hcov.sq_eq_z_of_type22 (cycleType_type22_of_card_11 h1 h2)
      rw [hcc] at this
      exact hcov.ne_one this.symm
  obtain ⟨m, hm, hmeq⟩ := exists_odd_card_mul_of_centralizer_sylow D.order_t hty S hSle hSt hS2
    (by decide : Odd 135) hTK hZ
  have hcard := card_centralizer_eq_of_isConj hconj
  rw [hScard] at hmeq
  rw [← hmeq] at hcard
  rw [hcard] at h128
  obtain ⟨j, hj⟩ := hm
  omega

theorem not_isConj_x1p_u123p (D : LyData G t ρ) {x u : ↥(centralizer ({t} : Set G))}
    (hx3 : x ^ 3 = 1) (hu3 : u ^ 3 = 1) (hx : ρ x = x1p) (hu : ρ u = u123p) :
    ¬ IsConj (x : G) (u : G) := by
  have hcov := D.cover
  have hE8A : E8 ≤ alternatingGroup (Fin 11) := fun σ hσ => mem_alternatingGroup.2 (E8_even hσ)
  have h16 : Nat.card ↥(E8.comap ρ) = 16 := by
    rw [hcov.card_comap hE8A, card_E8]
  obtain ⟨K, hK8⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(E8.comap ρ)) 2 (n := 3)
    (by rw [h16]; norm_num)
  set F : Subgroup G := (K.map (E8.comap ρ).subtype).map (centralizer ({t} : Set G)).subtype with hF
  have hF8 : Nat.card F = 8 := by
    rw [hF, Subgroup.card_map_of_injective (centralizer ({t} : Set G)).subtype_injective,
      Subgroup.card_map_of_injective (E8.comap ρ).subtype_injective, hK8]
    norm_num
  have hFE : ∀ f ∈ F, ∃ s : ↥(centralizer ({t} : Set G)), ρ s ∈ E8 ∧ (s : G) = f := by
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨(k : ↥(centralizer ({t} : Set G))), k.2, rfl⟩
  have hF2 : ∀ f ∈ F, f ^ 2 = 1 := by
    intro f hf
    obtain ⟨s, hs, rfl⟩ := hFE f hf
    have hs2 : ρ s ^ 2 = 1 := E8_sq hs
    by_cases h1 : ρ s = 1
    · rcases hcov.mem_ker_iff.1 h1 with h3 | h3
      · rw [h3]; simp
      · rw [h3]
        have := hcov.sq_eq_one
        exact congrArg Subtype.val this
    · have ht := cycleType_type2222_of_card_11 hs2 (E8_support hs h1)
      have := hcov.sq_eq_one_of_type2222_lift ht
      exact congrArg Subtype.val this
  have hFx : F ≤ centralizer ({(x : G)} : Set G) := by
    intro f hf
    obtain ⟨s, hs, rfl⟩ := hFE f hf
    obtain ⟨h0, h1, h2⟩ := E8_fix hs
    have hcomm : ρ s * ρ x = ρ x * ρ s := by
      rw [hx]; exact commute_x1p_of_fix h0 h1 h2
    have := hcov.commute_of_rho_commute_pow_three hx3 hcomm
    exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have htu : t * (u : G) = (u : G) * t := (mem_centralizer_singleton_iff.1 u.2).symm
  have hK : ¬ 8 ∣ Nat.card ↥(centralizer ({(u : G)} : Set G) ⊓ centralizer ({t} : Set G)) := by
    rw [D.card_centralizer_inf hu3, hu, card_CA_u123p]
    norm_num
  exact not_isConj_of_elementaryAbelian_eight F hF8 hF2 hFx D.order_t htu hK

omit [Finite G] in
theorem exists_lift_x1p (D : LyData G t ρ) :
    ∃ x : ↥(centralizer ({t} : Set G)), x ^ 3 = 1 ∧ ρ x = x1p := by
  obtain ⟨c, hc, hc3⟩ := D.cover.exists_lift_cube_one (p := x1p)
    (by rw [sign_of_cycleType, cycleType_x1p]; decide) x1p_pow_three
  exact ⟨c, hc3, hc⟩

omit [Finite G] in
theorem exists_lift_y12p (D : LyData G t ρ) :
    ∃ x : ↥(centralizer ({t} : Set G)), x ^ 3 = 1 ∧ ρ x = y12p := by
  obtain ⟨c, hc, hc3⟩ := D.cover.exists_lift_cube_one (p := y12p)
    (by rw [sign_of_cycleType, cycleType_y12p]; decide) y12p_pow_three
  exact ⟨c, hc3, hc⟩

omit [Finite G] in
theorem exists_lift_u123p (D : LyData G t ρ) :
    ∃ x : ↥(centralizer ({t} : Set G)), x ^ 3 = 1 ∧ ρ x = u123p := by
  obtain ⟨c, hc, hc3⟩ := D.cover.exists_lift_cube_one (p := u123p)
    (by rw [sign_of_cycleType, cycleType_u123p]; decide) u123p_pow_three
  exact ⟨c, hc3, hc⟩

theorem isConj_of_isConj_x1 (D : LyData G t ρ) {x a : ↥(centralizer ({t} : Set G))}
    (hx3 : x ^ 3 = 1) (hx : ρ x = x1p) (ha3 : a ^ 3 = 1) (hconj : IsConj (a : G) (x : G)) :
    IsConj a x := by
  have hcov := D.cover
  have ha1 : ρ a ≠ 1 := by
    intro h1
    rcases hcov.mem_ker_iff.1 h1 with h3 | h3
    · have ha : (a : G) = 1 := by rw [h3]; rfl
      rw [ha] at hconj
      have hx1 : (x : G) = 1 := isConj_one_right.1 hconj
      have : x = 1 := Subtype.ext hx1
      rw [this, map_one] at hx
      exact (by decide : (1 : Perm (Fin 11)) ≠ x1p) hx
    · have : a ^ 3 = a := by
        rw [h3, pow_succ, hcov.sq_eq_one, one_mul]
      rw [this] at ha3
      exact hcov.ne_one (h3 ▸ ha3)
  have ha3' : ρ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  rcases cycleType_of_pow_three ha3' ha1 with h | h | h
  · exact hcov.isConj_of_cycleType_eq ha3 hx3 (by rw [h, hx, cycleType_x1p])
  · exfalso
    obtain ⟨y, hy3, hy⟩ := D.exists_lift_y12p
    have h1 : IsConj a y := hcov.isConj_of_cycleType_eq ha3 hy3 (by rw [h, hy, cycleType_y12p])
    have h2 : IsConj (a : G) (y : G) := (centralizer ({t} : Set G)).subtype.map_isConj h1
    exact D.not_isConj_x1p_y12p hx3 hy3 hx hy (hconj.symm.trans h2)
  · exfalso
    obtain ⟨u, hu3, hu⟩ := D.exists_lift_u123p
    have h1 : IsConj a u := hcov.isConj_of_cycleType_eq ha3 hu3 (by rw [h, hu, cycleType_u123p])
    have h2 : IsConj (a : G) (u : G) := (centralizer ({t} : Set G)).subtype.map_isConj h1
    exact D.not_isConj_x1p_u123p hx3 hu3 hx hu (hconj.symm.trans h2)

theorem lemma42 (D : LyData G t ρ) {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}
    (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1) (h₃ : x₃ ^ 3 = 1)
    (hρ₁ : ρ x₁ = x1p) (hρ₂ : ρ x₂ = x2p) (hρ₃ : ρ x₃ = x3p) :
    ¬ IsConj (x₁ : G) ((x₁ * x₂ : ↥(centralizer ({t} : Set G))) : G) ∧
      ¬ IsConj (x₁ : G) ((x₁ * x₂ * x₃ : ↥(centralizer ({t} : Set G))) : G) := by
  have hcov := D.cover
  have hc12 : x₂ * x₁ = x₁ * x₂ := hcov.commute_of_rho_commute_pow_three h₁
    (by rw [hρ₁, hρ₂]; exact disjoint_x1p_x2p.commute.symm)
  have hy3 : (x₁ * x₂) ^ 3 = 1 := by
    rw [Commute.mul_pow (show Commute x₁ x₂ from hc12.symm), h₁, h₂, one_mul]
  have hρy : ρ (x₁ * x₂) = y12p := by rw [map_mul, hρ₁, hρ₂]; rfl
  have hc3 : x₃ * (x₁ * x₂) = (x₁ * x₂) * x₃ := hcov.commute_of_rho_commute_pow_three hy3
    (by rw [hρy, hρ₃]; exact disjoint_y12p_x3p.commute.symm)
  have hu3 : (x₁ * x₂ * x₃) ^ 3 = 1 := by
    rw [Commute.mul_pow (show Commute (x₁ * x₂) x₃ from hc3.symm), hy3, h₃, one_mul]
  have hρu : ρ (x₁ * x₂ * x₃) = u123p := by rw [map_mul, hρy, hρ₃]; rfl
  exact ⟨D.not_isConj_x1p_y12p h₁ hy3 hρ₁ hρy, D.not_isConj_x1p_u123p h₁ hu3 hρ₁ hρu⟩

end LyData

end CFSG.Sporadic.Recognition.LyonsSims
