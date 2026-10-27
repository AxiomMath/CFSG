module

public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLACarrier

public section

namespace CFSG.Quasithin.GoldMLA

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over
open CFSG.QuasithinUnique.Unc25G2.BenderBorel CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem mem_normalizer_sup {g : G} {P₁ P₂ : Subgroup G} (h1 : g ∈ Subgroup.normalizer (P₁ : Set G))
    (h2 : g ∈ Subgroup.normalizer (P₂ : Set G)) :
    g ∈ Subgroup.normalizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (P₁ : Set G) → h ∈ Subgroup.normalizer (P₂ : Set G) →
      (P₁ ⊔ P₂).map (MulAut.conj h).toMonoidHom ≤ P₁ ⊔ P₂ := by
    intro h hh1 hh2
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      simpa using (Subgroup.mem_normalizer_iff.mp hh1 x).mp hx
    · rintro _ ⟨x, hx, rfl⟩
      simpa using (Subgroup.mem_normalizer_iff.mp hh2 x).mp hx
  exact mem_normalizer_of_map_le (key g h1 h2)
    (key g⁻¹ ((Subgroup.normalizer (P₁ : Set G)).inv_mem h1)
      ((Subgroup.normalizer (P₂ : Set G)).inv_mem h2))

theorem le_normalizer_of_conj_mem {X B : Subgroup G} (h : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ B) :
    X ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => h x hx b hb, fun hb => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hb
  simpa [mul_assoc] using this

theorem conj_mem_of_comm {L' L B P Y : Subgroup G} (hL'N : L' ≤ Subgroup.normalizer (L : Set G))
    (hBL : B ≤ L) (hPB : P ≤ B) (hcomm : ∀ x ∈ L', ∀ b ∈ L, x * b * x⁻¹ * b⁻¹ ∈ Y)
    (hYL : Y ⊓ L ≤ P) : ∀ x ∈ L', ∀ b ∈ B, x * b * x⁻¹ ∈ B := by
  intro x hx b hb
  have h1 : x * b * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hL'N hx) b).mp (hBL hb)
  have h2 : x * b * x⁻¹ * b⁻¹ ∈ Y ⊓ L :=
    ⟨hcomm x hx b (hBL hb), L.mul_mem h1 (L.inv_mem (hBL hb))⟩
  have h3 := B.mul_mem (hPB (hYL h2)) hb
  simpa [mul_assoc] using h3

theorem mem_of_centralizes_mod [Finite G] {L P : Subgroup G} (hP : IsSylowTwoOf P L)
    (hB : fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {x : G} (hxL : x ∈ L)
    (hxC : ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ pCoreOf 2 L) : x ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  let π : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ y : ↥L, π y = 1 → y ∈ P.subgroupOf L := fun y hy =>
    pCore_le_subgroupOf hP y ((QuotientGroup.eq_one_iff y).mp hy)
  let Q : Sylow 2 (↥L ⧸ CFSG.pCore 2 ↥L) := (CFSG.Quasithin.A4.toSylow hP).mapSurjective hπ
  have hQ : (Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) = (P.subgroupOf L).map π := rfl
  obtain ⟨q, k, hq4, hBor⟩ := exists_borel_of_bender hB
  obtain ⟨hSE, ⟨D, hDcyc, -, -, hsup⟩, -, -, -⟩ := hBor Q
  have hsolvN := isSolvable_normalizer_of_sup_cyclic Q.isPGroup' hDcyc hsup
  have hxC' : ∀ q' ∈ (Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)),
      π ⟨x, hxL⟩ * q' = q' * π ⟨x, hxL⟩ := by
    intro q' hq'
    rw [hQ] at hq'
    obtain ⟨p, hp, rfl⟩ := hq'
    have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
    have hc : x * p * x⁻¹ * (p : G)⁻¹ ∈ pCoreOf 2 L := hxC p hpP
    have hc' : (⟨x, hxL⟩ * p * ⟨x, hxL⟩⁻¹ * p⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      obtain ⟨z, hz, hzv⟩ := hc
      have hz' : z = ⟨x * p * x⁻¹ * (p : G)⁻¹, by
          have hxm : x * p * x⁻¹ * (p : G)⁻¹ ∈ L :=
            L.mul_mem (L.mul_mem (L.mul_mem hxL p.2) (L.inv_mem hxL)) (L.inv_mem p.2)
          exact hxm⟩ := Subtype.ext hzv
      convert hz using 1
      rw [hz']
      rfl
    have e : π (⟨x, hxL⟩ * p * ⟨x, hxL⟩⁻¹ * p⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hc'
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at e
    calc π ⟨x, hxL⟩ * π p
        = (π ⟨x, hxL⟩ * π p * (π ⟨x, hxL⟩)⁻¹ * (π p)⁻¹) * (π p * π ⟨x, hxL⟩) := by group
      _ = π p * π ⟨x, hxL⟩ := by rw [e, one_mul]
  have hxN' : π ⟨x, hxL⟩ ∈ Subgroup.normalizer
      ((Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Set (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    mem_normalizer_of_commute hxC'
  have hmem := centralizer_le_of_borel (isSimpleBenderGroup_of_fusion hB) Q hsolvN hSE.1 hxN' hxC'
  rw [hQ] at hmem
  exact Subgroup.mem_subgroupOf.mp ((mem_image_iff π hker _).mp hmem)


section Sylow

variable [Finite G]

theorem IsCarrier.isSylow {B P : Subgroup G} (h : IsCarrier B P) : IsSylowTwoOf P B := by
  refine CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mpr ⟨h.le, h.pGroup, fun R hRB hR hPR => ?_⟩
  intro r hr
  obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
  exact h.hall r (hRB hr) k (by simpa using congrArg Subtype.val hk)

omit [Finite G] in
theorem card_eq_mul_index {B P : Subgroup G} (h : P ≤ B) :
    Nat.card B = Nat.card P * (P.subgroupOf B).index := by
  rw [← Subgroup.card_mul_index (P.subgroupOf B),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]

theorem mem_of_isSylow_of_normal {K Q : Subgroup G} (hs : IsSylowTwoOf Q K)
    (hn : K ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hx : x ∈ K) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x ∈ Q := by
  have hp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hz : Subgroup.zpowers x ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le).mpr (hn hx)
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers x ⊔ Q) := hp.to_sup_of_normal_right' hs.2.1 hz
  have hle : Subgroup.zpowers x ⊔ Q ≤ K := sup_le ((Subgroup.zpowers_le).mpr hx) hs.1
  have := (CFSG.Quasithin.A4.isSylowTwoOf_iff_maximal.mp hs).2.2 _ hle hsup le_sup_right
  exact this (le_sup_left (a := Subgroup.zpowers x) (b := Q) (Subgroup.mem_zpowers x))

theorem isSylow_sup_of_inf_eq {B B' P P' : Subgroup G} (hB : IsSylowTwoOf P B)
    (hB' : IsSylowTwoOf P' B') (hB'B : B' ≤ Subgroup.normalizer (B : Set G))
    (hP'P : P' ≤ Subgroup.normalizer (P : Set G)) (hinf : B ⊓ B' = P ⊓ P') :
    IsSylowTwoOf (P ⊔ P') (B ⊔ B') := by
  have c1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hB'B
  have c2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hP'P
  rw [hinf] at c1
  have hpos : 0 < Nat.card ↥(P ⊓ P') := Nat.card_pos
  have hKQ : P ⊔ P' ≤ B ⊔ B' := sup_le_sup hB.1 hB'.1
  have hQp : IsPGroup 2 ↥(P ⊔ P') := by
    rw [sup_comm]
    exact hB'.2.1.to_sup_of_normal_right' hB.2.1 hP'P
  have e1 := card_eq_mul_index hB.1
  have e2 := card_eq_mul_index hB'.1
  have e3 := card_eq_mul_index hKQ
  have hK : Nat.card ↥(B ⊔ B') = Nat.card ↥(P ⊔ P') *
      ((P.subgroupOf B).index * (P'.subgroupOf B').index) := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc Nat.card ↥(B ⊔ B') * Nat.card ↥(P ⊓ P') = Nat.card B * Nat.card B' := c1
      _ = (Nat.card P * (P.subgroupOf B).index) * (Nat.card P' * (P'.subgroupOf B').index) := by
        rw [← e1, ← e2]
      _ = (Nat.card ↥(P ⊔ P') * Nat.card ↥(P ⊓ P')) *
          ((P.subgroupOf B).index * (P'.subgroupOf B').index) := by rw [c2]; ring
      _ = _ := by ring
  have hQpos : 0 < Nat.card ↥(P ⊔ P') := Nat.card_pos
  have hj : ((P ⊔ P').subgroupOf (B ⊔ B')).index =
      (P.subgroupOf B).index * (P'.subgroupOf B').index := by
    refine Nat.eq_of_mul_eq_mul_left hQpos ?_
    rw [← e3, hK]
  refine ⟨hKQ, hQp, ?_⟩
  rw [hj]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hB.2.2 h
  · exact hB'.2.2 h

end Sylow

end CFSG.Quasithin.GoldMLA
