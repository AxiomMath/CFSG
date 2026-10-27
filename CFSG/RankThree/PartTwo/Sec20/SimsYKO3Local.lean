module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKO3

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsYKO3

open CFSG

@[expose] noncomputable def oTwoPCore {G : Type} [Group G] (p : ℕ) (O : Subgroup G) :
    Subgroup G :=
  ((CFSG.pCore p (O ⧸ CFSG.pCore 2 O)).comap (QuotientGroup.mk' (CFSG.pCore 2 O))).map O.subtype

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oTwoPCore_le (p : ℕ) (O : Subgroup G) : oTwoPCore p O ≤ O :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem le_normalizer_oTwoPCore (p : ℕ) {O H : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (O : Set G)) :
    H ≤ Subgroup.normalizer (oTwoPCore p O : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  rintro h hh _ ⟨x, hx, rfl⟩
  have hx' : QuotientGroup.mk' (CFSG.pCore 2 O) x ∈ CFSG.pCore p (O ⧸ CFSG.pCore 2 O) := hx
  have hy : Res11.quotAction hH ⟨h, hh⟩ (QuotientGroup.mk' (CFSG.pCore 2 O) x) ∈
      CFSG.pCore p (O ⧸ CFSG.pCore 2 O) :=
    Subgroup.characteristic_iff_le_comap.mp
      (inferInstance : (CFSG.pCore p (O ⧸ CFSG.pCore 2 O)).Characteristic)
      (Res11.quotAction hH ⟨h, hh⟩) hx'
  rw [Res11.quotAction_mk] at hy
  exact ⟨_, hy, rfl⟩

omit [Finite G] in
private theorem pCore_two_le_comap (p : ℕ) (O : Subgroup G) :
    CFSG.pCore 2 O ≤
      (CFSG.pCore p (O ⧸ CFSG.pCore 2 O)).comap (QuotientGroup.mk' (CFSG.pCore 2 O)) := by
  intro x hx
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 O) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  show QuotientGroup.mk' (CFSG.pCore 2 O) x ∈ CFSG.pCore p (O ⧸ CFSG.pCore 2 O)
  rw [h1]
  exact Subgroup.one_mem _

omit [Finite G] in
private theorem pCoreOf_two_le_oTwoPCore (p : ℕ) (O : Subgroup G) :
    CFSG.Open.pCoreOf 2 O ≤ oTwoPCore p O :=
  Subgroup.map_mono (pCore_two_le_comap p O)

omit [Finite G] in
private theorem relIndex_pCoreOf_oTwoPCore (p : ℕ) (O : Subgroup G) :
    (CFSG.Open.pCoreOf 2 O).relIndex (oTwoPCore p O) =
      Nat.card (CFSG.pCore p (O ⧸ CFSG.pCore 2 O)) := by
  have h := Subgroup.relIndex_comap (⊥ : Subgroup (O ⧸ CFSG.pCore 2 O))
    (QuotientGroup.mk' (CFSG.pCore 2 O))
    ((CFSG.pCore p (O ⧸ CFSG.pCore 2 O)).comap (QuotientGroup.mk' (CFSG.pCore 2 O)))
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    Subgroup.relIndex_bot_left, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h
  unfold CFSG.Open.pCoreOf oTwoPCore
  rw [Subgroup.relIndex_map_map_of_injective _ _ O.subtype_injective]
  exact h

private theorem exists_relIndex_oTwoPCore {p : ℕ} (hp : p.Prime) (O : Subgroup G) :
    ∃ a : ℕ, (CFSG.Open.pCoreOf 2 O).relIndex (oTwoPCore p O) = p ^ a := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [relIndex_pCoreOf_oTwoPCore]
  exact IsPGroup.iff_card.mp CFSG.pCore_isPGroup

private theorem isSolvable_oTwoPCore {p : ℕ} (hp : p.Prime) (O : Subgroup G) :
    Group.IsSolvable ↥(oTwoPCore p O) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsSolvable ↥(CFSG.pCore 2 O) := by
    haveI := (CFSG.pCore_isPGroup (p := 2) (G := O)).isNilpotent
    infer_instance
  haveI : Group.IsSolvable ↥(CFSG.pCore p (O ⧸ CFSG.pCore 2 O)) := by
    haveI := (CFSG.pCore_isPGroup (p := p) (G := O ⧸ CFSG.pCore 2 O)).isNilpotent
    infer_instance
  let W₀ : Subgroup O :=
    (CFSG.pCore p (O ⧸ CFSG.pCore 2 O)).comap (QuotientGroup.mk' (CFSG.pCore 2 O))
  haveI : Group.IsSolvable ↥W₀ :=
    Group.isSolvable_of_ker_le_range (Subgroup.inclusion (pCore_two_le_comap p O))
      ((QuotientGroup.mk' (CFSG.pCore 2 O)).subgroupComap
        (CFSG.pCore p (O ⧸ CFSG.pCore 2 O))) (by
      intro x hx
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 O) (x : O) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩)
  exact Group.isSolvable_of_surjective (O.subtype.subgroupMap_surjective W₀)

omit [Finite G] in
private theorem relIndex_sup_eq_of_le_normalizer {W R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (W : Set G)) : W.relIndex (W ⊔ R) = W.relIndex R := by
  have hW : W ≤ Subgroup.normalizer (W : Set G) := Subgroup.le_normalizer
  have h := Subgroup.relIndex_sup_left (R.subgroupOf (Subgroup.normalizer (W : Set G)))
    (W.subgroupOf (Subgroup.normalizer (W : Set G)))
  rwa [← Subgroup.subgroupOf_sup hW hR, Subgroup.relIndex_subgroupOf (sup_le hW hR),
    Subgroup.relIndex_subgroupOf hR] at h

private theorem relIndex_sup_right_eq {W R : Subgroup G}
    (hR : R ≤ Subgroup.normalizer (W : Set G)) :
    R.relIndex (W ⊔ R) = (W ⊓ R).relIndex W := by
  have hI1 := relIndex_sup_eq_of_le_normalizer hR
  have h1 := Subgroup.relIndex_mul_relIndex (W ⊓ R) R (W ⊔ R) inf_le_right le_sup_right
  have h2 := Subgroup.relIndex_mul_relIndex (W ⊓ R) W (W ⊔ R) inf_le_left le_sup_left
  have h3 : (W ⊓ R).relIndex R = W.relIndex R := Subgroup.inf_relIndex_right W R
  have hpos : 0 < (W ⊓ R).relIndex R :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card _ _) Nat.card_pos
  rw [hI1, ← h3] at h2
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [h1, ← h2, mul_comm]

omit [Finite G] in
private theorem card_sup_eq {W R : Subgroup G} :
    Nat.card ↥(W ⊔ R) = R.relIndex (W ⊔ R) * Nat.card R := by
  have h := Subgroup.relIndex_mul_card R (W ⊔ R)
  rw [inf_of_le_left le_sup_right] at h
  exact h.symm

omit [Finite G] in
private theorem eq_one_of_mem_of_isPGroup {Z N : Subgroup G} (hZ : IsPGroup 2 Z)
    (hN : ¬ 2 ∣ Nat.card N) {g : G} (hgN : g ∈ N) (hgZ : g ∈ Z) : g = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZ ⟨g, hgZ⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | k
  · exact orderOf_eq_one_iff.mp (by simpa using hk)
  · exact absurd ((dvd_pow_self 2 k.succ_ne_zero).trans (hk ▸ Subgroup.orderOf_dvd_natCard N hgN))
      hN

omit [Finite G] in
private theorem pCoreOf_conj_mem {X : Subgroup G} {x z : G} (hx : x ∈ X)
    (hz : z ∈ CFSG.Open.pCoreOf 2 X) : x * z * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X := by
  obtain ⟨z', hz', rfl⟩ := hz
  exact ⟨⟨x, hx⟩ * z' * ⟨x, hx⟩⁻¹,
    (inferInstance : (CFSG.pCore 2 X).Normal).conj_mem z' hz' ⟨x, hx⟩, rfl⟩

theorem oTwoPCore_sup_package {X O R : Subgroup G} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hOX : O ≤ X) (hXO : X ≤ Subgroup.normalizer (O : Set G)) (h3 : Nat.Coprime 3 (Nat.card O))
    (hR2 : IsPGroup 2 R) (hRX : R ≤ X) (hQR : CFSG.Open.pCoreOf 2 O ≤ R)
    (hX2R : CFSG.Open.pCoreOf 2 X ≤ R) (hchar : CFSG.QuasithinUnique.CharTwo X) :
    Group.IsSolvable ↥(oTwoPCore p O ⊔ R) ∧ ¬ 3 ∣ Nat.card ↥(oTwoPCore p O ⊔ R) ∧
      (p ≠ 5 → ¬ 5 ∣ Nat.card ↥(oTwoPCore p O ⊔ R)) ∧
      (∀ N : Subgroup G, N ≤ oTwoPCore p O ⊔ R →
        oTwoPCore p O ⊔ R ≤ Subgroup.normalizer (N : Set G) → ¬ 2 ∣ Nat.card N → N = ⊥) ∧
      ¬ 2 ∣ R.relIndex (oTwoPCore p O ⊔ R) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hWO : oTwoPCore p O ≤ O := oTwoPCore_le p O
  have hQW : CFSG.Open.pCoreOf 2 O ≤ oTwoPCore p O := pCoreOf_two_le_oTwoPCore p O
  have hRN : R ≤ Subgroup.normalizer (oTwoPCore p O : Set G) :=
    le_normalizer_oTwoPCore p (hRX.trans hXO)
  have hRH : R ≤ oTwoPCore p O ⊔ R := le_sup_right
  have hWH : oTwoPCore p O ≤ oTwoPCore p O ⊔ R := le_sup_left
  have hHX : oTwoPCore p O ⊔ R ≤ X := sup_le (hWO.trans hOX) hRX
  have hHN : oTwoPCore p O ⊔ R ≤ Subgroup.normalizer (oTwoPCore p O : Set G) :=
    sup_le Subgroup.le_normalizer hRN
  obtain ⟨a, ha⟩ := exists_relIndex_oTwoPCore hp O
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hrel : R.relIndex (oTwoPCore p O ⊔ R) = (oTwoPCore p O ⊓ R).relIndex (oTwoPCore p O) :=
    relIndex_sup_right_eq hRN
  have hdvdP : (oTwoPCore p O ⊓ R).relIndex (oTwoPCore p O) ∣ p ^ a := by
    rw [← ha]
    exact Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex (CFSG.Open.pCoreOf 2 O)
      (oTwoPCore p O ⊓ R) (oTwoPCore p O) (le_inf hQW hQR) inf_le_left)
  have hdvdO : (oTwoPCore p O ⊓ R).relIndex (oTwoPCore p O) ∣ Nat.card O :=
    (Subgroup.relIndex_dvd_card _ _).trans (Subgroup.card_dvd_of_le hWO)
  have hcard : Nat.card ↥(oTwoPCore p O ⊔ R) =
      (oTwoPCore p O ⊓ R).relIndex (oTwoPCore p O) * 2 ^ k := by
    rw [card_sup_eq, hk, hrel]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    haveI : Group.IsSolvable ↥(oTwoPCore p O) := isSolvable_oTwoPCore hp O
    haveI : ((oTwoPCore p O).subgroupOf (oTwoPCore p O ⊔ R)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hWH).mpr hHN
    have hq : IsPGroup 2
        (↥(oTwoPCore p O ⊔ R) ⧸ (oTwoPCore p O).subgroupOf (oTwoPCore p O ⊔ R)) := by
      refine IsPGroup.of_card_dvd_pow (n := k) ?_
      have h : (oTwoPCore p O).relIndex (oTwoPCore p O ⊔ R) ∣ 2 ^ k := by
        rw [relIndex_sup_eq_of_le_normalizer hRN, ← hk]
        exact Subgroup.relIndex_dvd_card _ _
      exact h
    haveI : Group.IsSolvable
        (↥(oTwoPCore p O ⊔ R) ⧸ (oTwoPCore p O).subgroupOf (oTwoPCore p O ⊔ R)) := by
      haveI := hq.isNilpotent
      infer_instance
    exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion hWH)
      (QuotientGroup.mk' ((oTwoPCore p O).subgroupOf (oTwoPCore p O ⊔ R)))
      (by rw [QuotientGroup.ker_mk', Subgroup.inclusion_range])
  ·
    intro h
    rw [hcard] at h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · have := Nat.Coprime.eq_one_of_dvd h3 (h.trans hdvdO)
      omega
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
  ·
    intro hp5' h
    rw [hcard] at h
    have h5 : Nat.Prime 5 := by norm_num
    rcases (Nat.Prime.dvd_mul h5).mp h with h | h
    · have h5p : 5 ∣ p := Nat.Prime.dvd_of_dvd_pow h5 (h.trans hdvdP)
      exact hp5' ((Nat.prime_dvd_prime_iff_eq h5 hp).mp h5p).symm
    · have := Nat.Prime.dvd_of_dvd_pow h5 h
      omega
  ·
    intro N hNH hHN' hN2
    have hZ2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 X) :=
      (CFSG.pCore_isPGroup (p := 2) (G := X)).map X.subtype
    have hNX : N ≤ X := hNH.trans hHX
    have hZH : CFSG.Open.pCoreOf 2 X ≤ oTwoPCore p O ⊔ R := hX2R.trans hRH
    have hNZ : ∀ g ∈ N, g ∈ CFSG.Open.pCoreOf 2 X → g = 1 := fun g hgN hgZ =>
      eq_one_of_mem_of_isPGroup hZ2 hN2 hgN hgZ
    have hcomm : ∀ n ∈ N, ∀ z ∈ CFSG.Open.pCoreOf 2 X, z * n = n * z := by
      intro n hn z hz
      have h1 : n * z * n⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
        Subgroup.mul_mem _ (pCoreOf_conj_mem (hNX hn) hz) (Subgroup.inv_mem _ hz)
      have h2 : n * z * n⁻¹ * z⁻¹ ∈ N := by
        have := Subgroup.mul_mem N hn
          (Subgroup.le_normalizer_iff.mp hHN' z (hZH hz) n⁻¹ (Subgroup.inv_mem _ hn))
        rwa [show n * (z * n⁻¹ * z⁻¹) = n * z * n⁻¹ * z⁻¹ by group] at this
      have h4 : n * z * n⁻¹ * z⁻¹ = 1 := hNZ _ h2 h1
      calc z * n = (n * z * n⁻¹ * z⁻¹)⁻¹ * (n * z) := by group
        _ = n * z := by rw [h4]; simp
    have hNc : N ≤ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) := fun n hn =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => hcomm n hn z hz
    have hchar' : X ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 X : Set G) ≤
        CFSG.Open.pCoreOf 2 X := hchar
    exact (Subgroup.eq_bot_iff_forall N).mpr fun n hn =>
      hNZ n hn (hchar' ⟨hNX hn, hNc hn⟩)
  ·
    intro h
    rw [hrel] at h
    have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h.trans hdvdP)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2p
    omega

end CFSG.RankThree.PartTwo.Sec20.SimsYKO3
