module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3M4
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A4

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup

section M3
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem M3_O3'_Y (h : FF84Sec3 b L B b₁ b₂) (hX : Opp 3 (Cen b) = ⊥) (hZ : Subgroup.center L = ⊥) :
    Opp 3 (Cen b ⊓ Cen (b₁ * b₂)) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e', he'⟩ := M0_quot h hZ
  have hL : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp h.hyp.quasi.1
  obtain ⟨θ, hθc, hθx, hθ1⟩ := M0_T0_conj hL e'
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  obtain ⟨y₁, hy₁⟩ : ∃ y : ↥L, (y : G) = b₁ := ⟨⟨b₁, hb₁L⟩, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y : ↥L, (y : G) = b₂ := ⟨⟨b₂, hb₂L⟩, rfl⟩
  obtain ⟨hm₁, hm₂⟩ := he' y₁ y₂ hy₁ hy₂
  obtain ⟨yc, hyc⟩ : ∃ y : ↥L, (y : G) = b₁ * b₂ := ⟨y₁ * y₂, by simp [hy₁, hy₂]⟩
  have hycy : yc = y₁ * y₂ := Subtype.ext (by simp [hy₁, hy₂, hyc])
  have hc : ((e' (QuotientGroup.mk yc) : alternatingGroup (Fin 8)) : P8) = m₁ * m₂ := by
    rw [hycy, QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul, hm₁, hm₂]
  have hEq : CenS L ⊓ Cen b = Subgroup.zpowers b := by
    obtain ⟨-, h2, -⟩ := P_C_structure h
    rw [hX, sup_bot_eq] at h2
    exact h2.symm
  have hb3 : b ^ 3 = 1 := by
    have := pow_orderOf_eq_one b
    rwa [h.hyp.ord] at this
  have hb3z : b ^ (3 : ℤ) = 1 := by exact_mod_cast hb3
  have hcomm_c : ∀ n : ↥(Nor L), (n : G) ∈ Cen (b₁ * b₂) →
      θ n * (m₁ * m₂) = (m₁ * m₂) * θ n := by
    intro n hn
    have hnc : (n : G) * (b₁ * b₂) = (b₁ * b₂) * (n : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 hn
    have h1 := hθc (n : G) n.2 yc yc (by rw [hyc, hnc]; group)
    rw [hc] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1.symm
  have hsurj : ∀ a : P8, a ∈ A8s → ∃ x : ↥L, θ ⟨(x : G), Subgroup.le_normalizer x.2⟩ = a := by
    intro a ha
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e'.symm ⟨a, ha⟩)
    refine ⟨x, ?_⟩
    rw [hθx x, hx, MulEquiv.apply_symm_apply]
  set H : Subgroup G := Cen b ⊓ Cen (b₁ * b₂) with hH
  have hHN : H ≤ Nor L := fun g hg => h.hyp.hLN (Subgroup.mem_inf.1 hg).1
  have hNH : Opp 3 H ≤ H := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hY₂ : (H.subgroupOf (Nor L)).map θ ≤ Subgroup.centralizer ({m₁ * m₂} : Set P8) := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_centralizer_singleton_iff.2
      (hcomm_c n (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hn)).2)
  have hY₁ : Subgroup.centralizer ({m₁ * m₂} : Set P8) ⊓ A8s ≤ (H.subgroupOf (Nor L)).map θ := by
    intro a ha
    obtain ⟨hacent, haA⟩ := Subgroup.mem_inf.1 ha
    obtain ⟨x, hx⟩ := hsurj a haA
    have hfix : θ ⟨(x : G), Subgroup.le_normalizer x.2⟩ *
        ((e' (QuotientGroup.mk yc) : alternatingGroup (Fin 8)) : P8) *
        (θ ⟨(x : G), Subgroup.le_normalizer x.2⟩)⁻¹ =
        ((e' (QuotientGroup.mk yc) : alternatingGroup (Fin 8)) : P8) := by
      rw [hx, hc]
      have hac := Subgroup.mem_centralizer_singleton_iff.1 hacent
      rw [hac]
      group
    have hxc : Commute (x : G) (yc : G) :=
      M4_commute_fix hZ e' θ hθc (x : G) (Subgroup.le_normalizer x.2) yc hfix
    rw [hyc] at hxc
    have hxH : (x : G) ∈ H :=
      Subgroup.mem_inf.2 ⟨h.hyp.hLC x.2, Subgroup.mem_centralizer_singleton_iff.2 hxc.eq⟩
    exact Subgroup.mem_map.2 ⟨⟨(x : G), Subgroup.le_normalizer x.2⟩,
      Subgroup.mem_subgroupOf.2 hxH, hx⟩
  have hN : ((Opp 3 H).subgroupOf (Nor L)).map θ ≤ (H.subgroupOf (Nor L)).map θ := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 (hNH (Subgroup.mem_subgroupOf.1 hn)))
  have hNnorm : ((((Opp 3 H).subgroupOf (Nor L)).map θ).subgroupOf
      ((H.subgroupOf (Nor L)).map θ)).Normal := by
    constructor
    intro z hz g
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.1 hz
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.1 g.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hkg, ← hmz, ← map_inv, ← map_mul,
      ← map_mul]
    apply Subgroup.mem_map_of_mem
    apply Subgroup.mem_subgroupOf.2
    have hconj := opp3_conj (Subgroup.mem_subgroupOf.1 hk) (Subgroup.mem_subgroupOf.1 hm)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj
  have h3 : ¬ 3 ∣ Nat.card (((Opp 3 H).subgroupOf (Nor L)).map θ) := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have hz3 : orderOf ((z : P8)) = 3 := by rw [Subgroup.orderOf_coe, hz]
    obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.1 z.2
    have hdiv : orderOf (θ m) ∣ orderOf m := orderOf_map_dvd θ m
    rw [hmz, hz3, ← Subgroup.orderOf_coe] at hdiv
    exact opp3_not_dvd (Subgroup.mem_subgroupOf.1 hm) hdiv
  have hN'bot := A6_O3'_centralizer_c _ _ hY₁ hY₂ hN hNnorm h3
  rw [eq_bot_iff_forall]
  intro x hx
  have hxH : x ∈ H := hNH hx
  have hθn : θ ⟨x, hHN hxH⟩ = 1 := by
    have hmem : θ ⟨x, hHN hxH⟩ ∈ ((Opp 3 H).subgroupOf (Nor L)).map θ :=
      Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 hx)
    rw [hN'bot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hxC : x ∈ CenS L := (hθ1 x (hHN hxH)).1 hθn
  have hxZ : x ∈ CenS L ⊓ Cen b := Subgroup.mem_inf.2 ⟨hxC, (Subgroup.mem_inf.1 hxH).1⟩
  rw [hEq] at hxZ
  have hdvd3 : orderOf x ∣ 3 := by
    have := orderOf_dvd_of_mem_zpowers hxZ
    rwa [h.hyp.ord] at this
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd3 with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · exact absurd (dvd_of_eq h1.symm) (opp3_not_dvd hx)

end M3

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
