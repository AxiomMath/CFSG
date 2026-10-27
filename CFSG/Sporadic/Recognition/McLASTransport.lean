module

public import CFSG.Monster.B.Short.Extraspecial

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup

variable {G M : Type*} [Group G] [Group M]

theorem map_centralizer_eq_inf_of_injective {ι : G →* M} (hι : Function.Injective ι) (S : Set G) :
    (centralizer S).map ι = ι.range ⊓ centralizer (ι '' S) := by
  ext y
  simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_centralizer_iff, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hx s hs]
  · rintro ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, fun s hs => hι ?_, rfl⟩
    rw [map_mul, map_mul]
    exact hy _ ⟨s, hs, rfl⟩

theorem map_normalizer_eq_inf_of_injective {ι : G →* M} (hι : Function.Injective ι)
    (K : Subgroup G) :
    (normalizer (K : Set G)).map ι = ι.range ⊓ normalizer ((K.map ι : Subgroup M) : Set M) := by
  ext y
  simp only [mem_map, mem_inf, MonoidHom.mem_range, mem_normalizer_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, fun m => ?_⟩
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨g * k * g⁻¹, (hg k).1 hk, by simp⟩
    · rintro ⟨k, hk, hkm⟩
      refine ⟨g⁻¹ * k * g, ?_, ?_⟩
      · have := (hg (g⁻¹ * k * g)).2
        rw [show g * (g⁻¹ * k * g) * g⁻¹ = k by group] at this
        exact this hk
      · apply_fun fun z => (ι g)⁻¹ * z * ι g at hkm
        simp only [map_mul, map_inv] at hkm ⊢
        rw [hkm]
        group
  · rintro ⟨⟨g, rfl⟩, hn⟩
    refine ⟨g, fun k => ?_, rfl⟩
    have h1 := hn (ι k)
    rw [show ι g * ι k * (ι g)⁻¹ = ι (g * k * g⁻¹) by simp] at h1
    constructor
    · intro hk
      obtain ⟨k', hk', hkk⟩ := h1.1 ⟨k, hk, rfl⟩
      rwa [← hι hkk]
    · intro hk
      obtain ⟨k', hk', hkk⟩ := h1.2 ⟨_, hk, rfl⟩
      rwa [← hι hkk]

theorem map_inSubgroup_pCore {ι : G →* M} (hι : Function.Injective ι) (p : ℕ) (N : Subgroup G) :
    (CFSG.inSubgroup (CFSG.pCore p) N).map ι = CFSG.inSubgroup (CFSG.pCore p) (N.map ι) := by
  have h := CFSG.pCore_map_iso p (N.equivMapOfInjective ι hι)
  unfold CFSG.inSubgroup
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isExtraspecialPGroup_of_invariants [Finite M] {p : ℕ} [Fact p.Prime] {R : Subgroup M}
    {x : M} (hexp : ∀ r ∈ R, r ^ p = 1) (hZ : R ⊓ centralizer (R : Set M) = zpowers x)
    (hC : ⁅R, R⁆ = zpowers x) (hx : orderOf x = p) (hR : p < Nat.card R) :
    CFSG.IsExtraspecialPGroup p ↥R := by
  rw [CFSG.isExtraspecialPGroup_iff_isExtraspecial]
  have hcen : (center ↥R).map R.subtype = R ⊓ centralizer (R : Set M) := by
    ext y
    simp only [mem_map, mem_center_iff, coe_subtype, mem_inf, mem_centralizer_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨r.2, fun h hh => ?_⟩
      exact congrArg Subtype.val (hr ⟨h, hh⟩)
    · rintro ⟨hyR, hy⟩
      exact ⟨⟨y, hyR⟩, fun g => Subtype.ext (hy g g.2), rfl⟩
  have hZcard : Nat.card (center ↥R) = p := by
    rw [← Subgroup.card_map_of_injective (f := R.subtype) R.subtype_injective, hcen, hZ,
      Nat.card_zpowers, hx]
  have hcomm : commutator ↥R ≤ center ↥R := by
    have h1 : (commutator ↥R).map R.subtype = ⁅R, R⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [← map_le_map_iff_of_injective R.subtype_injective, h1, hcen, hC, hZ]
  have hcomm' : IsMulCommutative (↥R ⧸ center ↥R) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := center ↥R)).2 hcomm
  have hEA : CFSG.IsElementaryAbelian p (↥R ⧸ center ↥R) :=
    { toIsMulCommutative := hcomm'
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun q => by
        induction q using QuotientGroup.induction_on with
        | H r =>
          rw [← QuotientGroup.mk_pow]
          have : r ^ p = 1 := Subtype.ext (hexp r.1 r.2)
          rw [this]
          rfl }
  have hnt : Nontrivial (↥R ⧸ center ↥R) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥R)
    rw [hZcard] at h
    by_contra hle
    have : Nat.card (↥R ⧸ center ↥R) ≤ 1 := not_lt.1 hle
    have h2 : Nat.card ↥R ≤ p := by
      calc Nat.card ↥R = Nat.card (↥R ⧸ center ↥R) * p := h
        _ ≤ 1 * p := Nat.mul_le_mul_right p this
        _ = p := one_mul p
    omega
  exact ⟨hZcard, hEA, hnt⟩

end CFSG.Sporadic.Recognition.McLAS
