module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TN1a
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNLie
public import CFSG.Quasithin.EmptyFaithful.SBc13JRaMain
public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.L828N

section N1aGlue

variable {G : Type} [Group G] [Finite G]

private theorem star_simple_five_N1aGlue {X : Type} [Group X] {n : ℕ} (hsz : IsSz n X) :
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ 5 ∣ Nat.card X := by
  obtain ⟨hn3, hodd⟩ : 3 ≤ n ∧ Odd n := by
    obtain ⟨-, a, ha1, K, -, -, hf, -, -⟩ := hsz
    exact ⟨by omega, ⟨a, hf⟩⟩
  obtain ⟨hs, hna⟩ := e22Simple_simple (show E22Simple X from Or.inl ⟨n, by omega, Or.inr hsz⟩)
  refine ⟨hs, hna, ?_⟩
  have hsq : (2 ^ n) ^ 2 % 5 = 4 := (CFSG.Quasithin.H13.sq_cube_mod_five
    (CFSG.Quasithin.H13.two_pow_odd_mod_five hodd)).1
  have h5 : 5 ∣ (2 ^ n) ^ 2 + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    generalize (2 ^ n) ^ 2 = s at hsq ⊢
    omega
  rw [CFSG.Quasithin.card_of_isSz hsz]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h5 _) _

private theorem orderOf_conj_N1aGlue {B : Type} [Group B] (g x : B) :
    orderOf (g * x * g⁻¹) = orderOf x :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulEquiv.injective (MulAut.conj g)) x

private noncomputable def starToRad_N1aGlue {M H Y : Subgroup G}
    (hJ : (kerIn M H).subgroupOf H ≤ CFSG.solvableRadical ↥H) :
    ↥(E2.star M H Y) →* (↥H ⧸ CFSG.solvableRadical ↥H) :=
  (QuotientGroup.map ((kerIn M H).subgroupOf H) (CFSG.solvableRadical ↥H) (MonoidHom.id ↥H) hJ).comp
    (E2.star M H Y).subtype

private theorem starToRad_apply_N1aGlue {M H Y : Subgroup G}
    (hJ : (kerIn M H).subgroupOf H ≤ CFSG.solvableRadical ↥H) (x : ↥(E2.star M H Y)) (a : ↥H)
    (h : QuotientGroup.mk' ((kerIn M H).subgroupOf H) a = (x : E2.StarQuot M H)) :
    starToRad_N1aGlue hJ x = QuotientGroup.mk' (CFSG.solvableRadical ↥H) a := by
  obtain ⟨x, hx⟩ := x
  dsimp only at h
  subst h
  rfl

theorem s828N_case1a_false {H Y M : Subgroup G} {t : G} {n : ℕ}
    (htH : t ∈ H) (hYc : Y ∈ cComp H) (hne : cjSub t Y ≠ Y)
    (hJ : (kerIn M H).subgroupOf H ≤ CFSG.solvableRadical ↥H)
    (hsz : IsSz n ↥(E2.star M H Y)) (h5 : CFSG.Open.pRank 5 H ≤ 1) : False := by
  obtain ⟨hs, hna, h5dvd⟩ := star_simple_five_N1aGlue hsz
  haveI : IsSimpleGroup ↥(E2.star M H Y) := hs
  have hψinj : Function.Injective (starToRad_N1aGlue (M := M) (Y := Y) hJ) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases Subgroup.Normal.eq_bot_or_eq_top (starToRad_N1aGlue (M := M) (Y := Y) hJ).ker with hk | hk
    · exact hk
    · exfalso
      have hYN : Y.subgroupOf H ≤ CFSG.solvableRadical ↥H := by
        intro a ha
        have hmem : QuotientGroup.mk' ((kerIn M H).subgroupOf H) a ∈ E2.star M H Y :=
          Subgroup.mem_map_of_mem (QuotientGroup.mk' ((kerIn M H).subgroupOf H)) ha
        have h1 : starToRad_N1aGlue hJ ⟨QuotientGroup.mk' ((kerIn M H).subgroupOf H) a, hmem⟩ = 1 :=
          MonoidHom.mem_ker.mp (by rw [hk]; exact Subgroup.mem_top _)
        have h2 : ((a : ↥H) : ↥H ⧸ CFSG.solvableRadical ↥H) = 1 := h1
        exact (QuotientGroup.eq_one_iff a).mp h2
      have hYH : Y ≤ H := CFSG.Quasithin.le_of_mem_cComp hYc
      have hYsolv : Y ≤ CFSG.Quasithin.solvRad H := by
        rw [CFSG.Quasithin.solvRad_eq_map_solvableRadical]
        intro l hl
        exact ⟨⟨l, hYH hl⟩, hYN hl, rfl⟩
      haveI := CFSG.Quasithin.solvRad_isSolvable H
      have hsolv : Group.IsSolvable ↥Y :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYsolv)
          (Subgroup.inclusion_injective hYsolv)
      exact CFSG.Quasithin.not_isSolvable_of_mem_cComp hYc hsolv
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 5 h5dvd
  have hcent : ∃ g : ↥(E2.star M H Y), c * g ≠ g * c := by
    by_contra hcon
    push_neg at hcon
    have hcz : c ∈ Subgroup.center ↥(E2.star M H Y) :=
      Subgroup.mem_center_iff.mpr (fun g => (hcon g).symm)
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center ↥(E2.star M H Y)) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hcz
      rw [hcz, orderOf_one] at hc
      norm_num at hc
    · obtain ⟨x, y, hxy⟩ := hna
      have hx : x ∈ Subgroup.center ↥(E2.star M H Y) := by
        rw [ht]
        exact Subgroup.mem_top x
      exact hxy (Subgroup.mem_center_iff.mp hx y).symm
  obtain ⟨g, hg⟩ := hcent
  have hcS : (c : E2.StarQuot M H) ∈
      (Y.subgroupOf H).map (QuotientGroup.mk' ((kerIn M H).subgroupOf H)) := c.2
  obtain ⟨a, ha, hac⟩ := Subgroup.mem_map.mp hcS
  have hgS : (g : E2.StarQuot M H) ∈
      (Y.subgroupOf H).map (QuotientGroup.mk' ((kerIn M H).subgroupOf H)) := g.2
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hgS
  have hψc := starToRad_apply_N1aGlue hJ c a hac
  have hψg := starToRad_apply_N1aGlue hJ g y hyg
  have hord : orderOf (QuotientGroup.mk' (CFSG.solvableRadical ↥H) a) = 5 := by
    rw [← hψc, orderOf_injective _ hψinj c, hc]
  have hnc : QuotientGroup.mk' (CFSG.solvableRadical ↥H) a *
      QuotientGroup.mk' (CFSG.solvableRadical ↥H) y ≠
      QuotientGroup.mk' (CFSG.solvableRadical ↥H) y *
      QuotientGroup.mk' (CFSG.solvableRadical ↥H) a := by
    intro heq
    apply hg
    apply hψinj
    rw [map_mul, map_mul, hψc, hψg]
    exact heq
  obtain ⟨τ, hτ⟩ : ∃ τ : ↥H, (τ : G) = t := ⟨⟨t, htH⟩, rfl⟩
  have hbmem : τ * a * τ⁻¹ ∈ (cjSub t Y).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.mem_cjSub]
    have ha' : (a : G) ∈ Y := Subgroup.mem_subgroupOf.mp ha
    have heq : t⁻¹ * ((τ * a * τ⁻¹ : ↥H) : G) * t = (a : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hτ]
      group
    rw [heq]
    exact ha'
  have hbord : orderOf (QuotientGroup.mk' (CFSG.solvableRadical ↥H) (τ * a * τ⁻¹)) = 5 := by
    rw [map_mul, map_mul, map_inv, orderOf_conj_N1aGlue, hord]
  have hY'c : cjSub t Y ∈ cComp H := CFSG.Quasithin.SBc13.mem_cComp_conjSub_of_mem hYc htH
  have h2 := s828N_two_le_pRank_five hYc hY'c hne.symm
    ⟨a, ha, hord, y, hy, hnc⟩ ⟨τ * a * τ⁻¹, hbmem, hbord⟩
  omega

end N1aGlue

end CFSG.Quasithin.H13
