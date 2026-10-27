module

public import CFSG.Quasithin.EmptyFaithful.R3c5Star

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {H : Type} [Group H] [Finite H]

section SignSylow

omit [Finite H] in
theorem exists_sylow_of_isSylowTwoOf {Q A : Subgroup H} (h : IsSylowTwoOf Q A) :
    ∃ P₀ : Sylow 2 ↥A, (P₀ : Subgroup ↥A) = Q.subgroupOf A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Q.subgroupOf A) := h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm
  exact ⟨hp.toSylow h.2.2, rfl⟩

theorem isSylowTwoOf_of_sylow {A : Subgroup H} (P : Sylow 2 ↥A) :
    IsSylowTwoOf ((P : Subgroup ↥A).map A.subtype) A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map A.subtype, ?_⟩
  have h : ((P : Subgroup ↥A).map A.subtype).subgroupOf A = P :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective _
  rw [h]
  exact Sylow.not_dvd_index P

theorem isSylowTwoOf_map {A B : Type} [Group A] [Finite A] [Group B] [Finite B] (φ : A →* B)
    {Q₀ A₀ : Subgroup A} (h : IsSylowTwoOf Q₀ A₀) :
    IsSylowTwoOf (Q₀.map φ) (A₀.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_of_isSylowTwoOf h
  set π : ↥A₀ →* ↥(A₀.map φ) := φ.subgroupMap A₀ with hπ
  have hπs : Function.Surjective π := φ.subgroupMap_surjective A₀
  have h1 := isSylowTwoOf_of_sylow (P₀.mapSurjective hπs)
  have h2 : ((P₀.mapSurjective hπs : Subgroup ↥(A₀.map φ))).map (A₀.map φ).subtype = Q₀.map φ := by
    rw [Sylow.coe_mapSurjective, hP₀, Subgroup.map_map]
    have : (A₀.map φ).subtype.comp π = φ.comp A₀.subtype := by
      ext x
      rfl
    rw [this, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le h.1]
  rwa [h2] at h1

omit [Finite H] in
theorem isSylowTwoOf_of_odd_index {Q X P : Subgroup H} (hQ : IsSylowTwoOf Q X) (hXP : X ≤ P)
    (hodd : ¬ 2 ∣ (X.subgroupOf P).index) : IsSylowTwoOf Q P := by
  refine ⟨hQ.1.trans hXP, hQ.2.1, ?_⟩
  have h := Subgroup.relIndex_mul_relIndex Q X P hQ.1 hXP
  have h1 : (Q.subgroupOf P).index = Q.relIndex P := rfl
  have h2 : (Q.subgroupOf X).index = Q.relIndex X := rfl
  have h3 : (X.subgroupOf P).index = X.relIndex P := rfl
  rw [h1, ← h, ← h2, ← h3]
  intro hd
  rcases Nat.Prime.dvd_mul Nat.prime_two |>.mp hd with hd | hd
  · exact hQ.2.2 hd
  · exact hodd hd

end SignSylow

section SignHyps

theorem OTwoQuot_map_pow_three {A B : Type} [Group A] [Finite A] [Group B] [Finite B] (f : A →* B)
    {Y : Subgroup A} (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) :
    ∀ z : OTwoQuot (Y.map f), z ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥Y →* ↥(Y.map f) := f.subgroupMap Y with hπ
  have hπs : Function.Surjective π := f.subgroupMap_surjective Y
  have hle : (CFSG.Open.pCore 2 ↥Y) ≤ (CFSG.Open.pCore 2 ↥(Y.map f)).comap π := by
    rw [← Subgroup.map_le_iff_le_comap]
    exact CFSG.LieType.BorelTits.map_pCore_le 2 π hπs
  let ρ : OTwoQuot Y →* OTwoQuot (Y.map f) :=
    QuotientGroup.map (CFSG.Open.pCore 2 ↥Y) (CFSG.Open.pCore 2 ↥(Y.map f)) π hle
  intro z
  obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
  obtain ⟨y, rfl⟩ := hπs z'
  have h1 : (QuotientGroup.mk (π y) : OTwoQuot (Y.map f)) = ρ (QuotientGroup.mk y) := rfl
  rw [h1, ← map_pow, hYe, map_one]

theorem map_le_oPrimeResidualOf {Y : Subgroup H} (hYo : oTwoUpper Y = Y)
    (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) :
    Y.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) ≤
      oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) := by
  rintro _ ⟨y, hy, rfl⟩
  exact mk_mem_oPrimeResidualOf_of_mem hYo hYe hy

theorem sign_hyps {L Y S : Subgroup H} [L.Normal] (hYo : oTwoUpper Y = Y)
    (hYe : ∀ z : OTwoQuot Y, z ^ 3 = 1) (hrY : 2 ≤ CFSG.Open.pRank 3 Y)
    (hSY : S ≤ Subgroup.normalizer (Y : Set H)) (hS : IsSylowTwoOf (S ⊓ L) L)
    (hXP : starImage 3 L ≤ oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)))
    (hcard : Nat.card ↥(oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H))) =
      3 * Nat.card ↥(starImage 3 L)) :
    IsSylowTwoOf ((S ⊓ L).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)))
        (oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H))) ∧
      (S ⊓ L).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) ≤
        Subgroup.normalizer ((Y.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) : Subgroup (PStar 3 H)) :
          Set (PStar 3 H)) ∧
      Y.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)) ≤
        oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) ∧
      IsPGroup 3 (OTwoQuot (Y.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H)))) ∧
      2 ≤ CFSG.Open.pRank 3 (Y.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 H))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ := QuotientGroup.mk' (CFSG.pPrimeCore 3 H) with hφ
  set P := oPrimeResidualOf 3 (⊤ : Subgroup (PStar 3 H)) with hP
  set X := starImage 3 L with hX
  refine ⟨?_, ?_, map_le_oPrimeResidualOf hYo hYe, ?_, ?_⟩
  ·
    have h1 : IsSylowTwoOf ((S ⊓ L).map φ) X := isSylowTwoOf_map φ hS
    have hcardX' : Nat.card ↥(X.subgroupOf P) = Nat.card ↥X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXP).toEquiv
    have hXpos : 0 < Nat.card ↥X := Nat.card_pos
    have hidx : (X.subgroupOf P).index = 3 := by
      have h := Subgroup.index_mul_card (X.subgroupOf P)
      rw [hcardX', hcard] at h
      exact Nat.eq_of_mul_eq_mul_right hXpos (by rw [h])
    refine isSylowTwoOf_of_odd_index h1 hXP ?_
    rw [hidx]
    omega
  ·
    rintro _ ⟨s, hs, rfl⟩
    have hsS : s ∈ S := hs.1
    have hsN := hSY hsS
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨s * y * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsN y).mp hy, by simp⟩
    · rintro ⟨y', hy', hy'h⟩
      have h1 : s⁻¹ * y' * (s⁻¹)⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsN) y').mp hy'
      refine ⟨s⁻¹ * y' * s, by simpa using h1, ?_⟩
      have : φ s * h * (φ s)⁻¹ = φ y' := hy'h.symm
      calc φ (s⁻¹ * y' * s) = (φ s)⁻¹ * (φ y') * φ s := by simp
        _ = (φ s)⁻¹ * (φ s * h * (φ s)⁻¹) * φ s := by rw [this]
        _ = h := by group
  · exact fun z => ⟨1, by simpa using OTwoQuot_map_pow_three φ hYe z⟩
  · exact (A318.pRank_le_pRank_map_of_coprime φ (by
      rw [QuotientGroup.ker_mk']
      exact CFSG.pPrimeCore_coprime_card) Y).trans' hrY

end SignHyps

end CFSG.Quasithin.R3c5
