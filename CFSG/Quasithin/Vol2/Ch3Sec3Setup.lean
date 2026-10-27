module

public import CFSG.Quasithin.Vol2.Ch3Sec3Cor332
public import CFSG.Quasithin.Background.B1MoreChief

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

structure Setup331 (G : Type) [Group G] [Finite G] (T M L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maxM : quasithinIsMaxTwoLocal M
  TM : T ≤ M
  Lmax : quasithinIsMaximalLocal T L
  LM : L ≤ M
  Lq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)

structure Hyp331 (G : Type) [Group G] [Finite G] (T M L D : Subgroup G) : Prop
    extends Setup331 G T M L where
  DN : D ≤ Subgroup.normalizer (T : Set G)
  Dodd : Odd (Nat.card D)
  ND : Subgroup.normalizer (T : Set G) = T ⊔ D
  counter : ¬ Subgroup.normalizer (T : Set G) ≤ M

variable {G : Type} [Group G]

abbrev mPlus (L T : Subgroup G) : Subgroup G := conjClosure L T

abbrev vPlus (L T : Subgroup G) : Subgroup G :=
  conjClosure (quasithinOmegaOneCenter T) (conjClosure L T)

abbrev qL (L T : Subgroup G) : Subgroup G := pCoreOf 2 (L ⊔ T)

abbrev tC (L T : Subgroup G) : Subgroup G := T ⊓ Subgroup.centralizer (L : Set G)

@[expose] def HasNoncentralTwoChief (X : Subgroup G) (k : ℕ) : Prop :=
  ∃ A B : Fin k → Subgroup G, (∀ i, IsTwoChiefFactor X (A i) (B i) ∧ ¬ ⁅A i, X⁆ ≤ B i) ∧
    ∀ i j, i < j → A i ≤ B j

@[expose] def InducesInnerOn (T Y : Subgroup G) : Prop :=
  ∀ t ∈ T, ∃ y ∈ Y, ∀ x ∈ Y, (t * x * t⁻¹) * (y * x * y⁻¹)⁻¹ ∈ pCoreOf 2 Y

@[expose] def wreathS3Z2 : Subgroup (Equiv.Perm (Fin 6)) :=
  Subgroup.closure {Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5}

@[expose] def IsDoubleCoverS5NotGL25 (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 2 ∧ Nonempty (X ⧸ Subgroup.center X ≃* Equiv.Perm (Fin 5)) ∧
    ¬ ∃ f : X →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5), Function.Injective f

@[expose] noncomputable def preCenterAut (T V : Subgroup G) : Subgroup G :=
  T ⊓ (((Subgroup.center ↥(autOn T V)).map (autOn T V).subtype).comap
    (conjAct V)).map (Subgroup.normalizer (V : Set G)).subtype

variable [Finite G]

theorem exists_hall_normalizer {T : Subgroup G} (hT : quasithinIsSylowTwo T) :
    ∃ D : Subgroup G, D ≤ Subgroup.normalizer (T : Set G) ∧ Odd (Nat.card D) ∧
      Subgroup.normalizer (T : Set G) = T ⊔ D := by
  set N := Subgroup.normalizer (T : Set G) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have : (T.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hcard : Nat.card ↥(T.subgroupOf N) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
  have h2 : ¬ 2 ∣ (T.subgroupOf N).index := by
    intro h
    apply hT.2
    have h1 : (T.subgroupOf N).index ∣ T.index := by
      rw [← Subgroup.relIndex]
      exact Subgroup.relIndex_dvd_index_of_le hTN
    exact h.trans h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hT.1
  have hcop : Nat.Coprime (Nat.card ↥(T.subgroupOf N)) (T.subgroupOf N).index := by
    rw [hcard, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨H.map N.subtype, Subgroup.map_subtype_le H, ?_, ?_⟩
  · have hH' : Nat.card H = (T.subgroupOf N).index := hH.symm.index_eq_card.symm
    rw [Subgroup.card_map_of_injective N.subtype_injective, hH']
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)
  · apply le_antisymm
    · intro x hx
      obtain ⟨t, h, ht, hh, hth⟩ : ∃ t h : ↥N, t ∈ T.subgroupOf N ∧ h ∈ H ∧ t * h = ⟨x, hx⟩ := by
        obtain ⟨⟨t, h⟩, hth⟩ := hH.surjective ⟨x, hx⟩
        exact ⟨t, h, t.2, h.2, hth⟩
      have hx' : x = (t : G) * (h : G) := by
        rw [← Subgroup.coe_mul, hth]
      rw [hx']
      exact Subgroup.mul_mem_sup ht ⟨h, hh, rfl⟩
    · exact sup_le hTN (Subgroup.map_subtype_le H)

theorem exists_hyp331 {T M L : Subgroup G} (h : Setup331 G T M L)
    (hc : ¬ Subgroup.normalizer (T : Set G) ≤ M) : ∃ D : Subgroup G, Hyp331 G T M L D := by
  obtain ⟨D, hDN, hDo, hND⟩ := exists_hall_normalizer h.sylow
  exact ⟨D, { h with DN := hDN, Dodd := hDo, ND := hND, counter := hc }⟩

theorem stmt3_3_1A_of_false
    (h : ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D → False) :
    Stmt3_3_1A := by
  intro G _ _ T hs hnab hK hT M L hM hTM hL hLM hq
  by_contra hc
  obtain ⟨D, hD⟩ := exists_hyp331 ⟨hs, hnab, hK, hT, hM, hTM, hL, hLM, hq⟩ hc
  exact h G T M L D hD

end CFSG.Quasithin.H13
