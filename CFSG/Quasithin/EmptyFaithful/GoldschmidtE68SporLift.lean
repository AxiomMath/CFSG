module

public import CFSG.Quasithin.Background.GoldschmidtTDE68CovBase

public section

namespace CFSG.Quasithin.E6.Spor

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6 CFSG.Quasithin.E6.Bar
  CFSG.Quasithin.E6.Inn

theorem mem_of_involution_centralizes_sylow {X : Type*} [Group X] [Finite X] {D : Subgroup X}
    (hD : IsSylowTwoOf D ⊤) {t : X} (ht : orderOf t = 2) (hc : ∀ d ∈ D, d * t = t * d) :
    t ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hp, hi⟩ := hD
  have hi' : ¬ 2 ∣ D.index := by
    rwa [show (D.subgroupOf ⊤).index = D.index from Subgroup.relIndex_top_right D] at hi
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hc)
  have hQ : IsPGroup 2 (Subgroup.zpowers t ⊔ D : Subgroup X) :=
    hzp.to_sup_of_normal_right' hp hnorm
  have hmax := (hp.toSylow hi').is_maximal' hQ (le_sup_right : D ≤ Subgroup.zpowers t ⊔ D)
  have : t ∈ (Subgroup.zpowers t ⊔ D : Subgroup X) := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  rw [hmax] at this
  exact this

variable {Y : Type} [Group Y] [Finite Y] {L R : Subgroup Y} {u : Y}

@[expose] def imgD (L R : Subgroup Y) : Subgroup (Qbar L) :=
  ((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (center ↥L))

theorem exists_inner_lift_central (h : E68CentHyp L R u) (hfix : InvolFixInner (Qbar L)) :
    ∃ y : ↥L, orderOf (QuotientGroup.mk y : Qbar L) = 2 ∧
      (∀ x : ↥L, u * (x : Y) * u⁻¹ = (y : Y) * x * (y : Y)⁻¹) ∧
      (QuotientGroup.mk y : Qbar L) ∈ imgD L R ∧
      ∀ q ∈ imgD L R, q * (QuotientGroup.mk y : Qbar L) = (QuotientGroup.mk y : Qbar L) * q := by
  obtain ⟨y, hy2, hact⟩ := exists_inner_lift h hfix
  have hcomm : ∀ q ∈ imgD L R,
      q * (QuotientGroup.mk y : Qbar L) = (QuotientGroup.mk y : Qbar L) * q := by
    rintro _ ⟨p, hp, rfl⟩
    have hpR : (p : Y) ∈ R := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hp)).1
    have h1 : u * (p : Y) * u⁻¹ = p := by
      rw [h.central (p : Y) hpR]
      group
    have h2 : (y : Y) * (p : Y) * (y : Y)⁻¹ = p := (hact p).symm.trans h1
    have h3 : (y : Y) * (p : Y) = (p : Y) * y := by
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2
    have h4 : y * p = p * y := Subtype.ext h3
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h4]
  have hmem : (QuotientGroup.mk y : Qbar L) ∈ imgD L R :=
    mem_of_involution_centralizes_sylow (isSylowTwoOf_map_mk h) hy2 hcomm
  exact ⟨y, hy2, hact, hmem, hcomm⟩

end CFSG.Quasithin.E6.Spor
