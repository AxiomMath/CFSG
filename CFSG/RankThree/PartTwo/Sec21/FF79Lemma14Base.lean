module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab


public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.L14

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_card {H P : Subgroup G} (h : IsSylowOf 3 P H) :
    Nat.card P = 3 ^ (Nat.card H).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hp, hcop⟩ := h
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, ha] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hf : (P.relIndex H).factorization 3 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hcop)
  rw [← h1, Nat.factorization_mul hne (by positivity), Finsupp.add_apply, hf,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same, zero_add, ha]

theorem isSylowOf_of_card {H P : Subgroup G} (hle : P ≤ H)
    (hc : Nat.card P = 3 ^ (Nat.card H).factorization 3) : IsSylowOf 3 P H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hle, IsPGroup.of_card hc, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, hc] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro hdvd
  have hpos : 0 < (P.relIndex H).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hne hdvd
  have h2 : (P.relIndex H * 3 ^ (Nat.card H).factorization 3).factorization 3 =
      (Nat.card H).factorization 3 := by rw [h1]
  rw [Nat.factorization_mul hne (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at h2
  omega

theorem exists_sylowOf (H : Subgroup G) : ∃ P : Subgroup G, IsSylowOf 3 P H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  refine ⟨(P : Subgroup H).map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact P.isPGroup'.map H.subtype
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (P.not_dvd_index)

theorem exists_conj_le_sylowOf {H P Q : Subgroup G} (hP : IsSylowOf 3 P H) (hQH : Q ≤ H)
    (hQ : IsPGroup 3 Q) : ∃ k ∈ H, ∀ x ∈ Q, k * x * k⁻¹ ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hPH, hPp, hPi⟩ := hP
  let A : Subgroup ↥H := P.subgroupOf H
  let Q' : Subgroup ↥H := Q.subgroupOf H
  have hAp : IsPGroup 3 A := hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hQ'p : IsPGroup 3 Q' := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hAi : ¬ 3 ∣ A.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hPi
  obtain ⟨S, hS⟩ := hQ'p.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq ↥H (hAp.toSylow hAi) S
  refine ⟨((k : ↥H) : G)⁻¹, H.inv_mem k.2, fun x hx => ?_⟩
  have hxS : (⟨x, hQH hx⟩ : ↥H) ∈ ((k • hAp.toSylow hAi : Sylow 3 ↥H) : Subgroup ↥H) := by
    rw [hk]
    exact hS (show (⟨x, hQH hx⟩ : ↥H) ∈ Q' from hx)
  rw [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
    Subgroup.mem_smul_pointwise_iff_exists] at hxS
  obtain ⟨s, hs, hseq⟩ := hxS
  have h1 := congrArg Subtype.val hseq
  have hsP : (s : G) ∈ P := hs
  have h2 : ((k : ↥H) : G) * (s : G) * ((k : ↥H) : G)⁻¹ = x := by
    simpa [MulAut.smul_def, MulAut.conj_apply] using h1
  have h3 : ((k : ↥H) : G)⁻¹ * x * ((k : ↥H) : G) = s := by
    rw [← h2]; group
  have : ((k : ↥H) : G)⁻¹ * x * ((k : ↥H) : G)⁻¹⁻¹ = s := by rw [inv_inv]; exact h3
  rw [this]
  exact hsP

theorem isSylowOf_inf_normal {H B N : Subgroup G} (hB : IsSylowOf 3 B H) (hNH : N ≤ H)
    (hnorm : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) : IsSylowOf 3 (B ⊓ N) N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := exists_sylowOf (G := G) N
  obtain ⟨k, hkH, hk⟩ := exists_conj_le_sylowOf hB (hQ.1.trans hNH) hQ.2.1
  let Q' : Subgroup G := Q.map (MulAut.conj k).toMonoidHom
  have hQ'le : Q' ≤ B ⊓ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hk x hx, hnorm k hkH x (hQ.1 hx)⟩
  have hQ'card : Nat.card Q' = 3 ^ (Nat.card N).factorization 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact isSylowOf_card hQ
  have hQ'syl : IsSylowOf 3 Q' N := isSylowOf_of_card (hQ'le.trans inf_le_right) hQ'card
  refine ⟨inf_le_right, hB.2.1.to_le inf_le_left, ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex Q' (B ⊓ N) N hQ'le inf_le_right
  have h2 : Nat.Coprime 3 (Q'.relIndex N) := hQ'syl.2.2
  rw [← h1] at h2
  exact Nat.Coprime.coprime_dvd_right (Dvd.intro_left _ rfl) h2

theorem Opp_le (p : ℕ) (H : Subgroup G) : Opp p H ≤ H := Subgroup.map_subtype_le _

theorem Opp_conj_mem {p : ℕ} {H : Subgroup G} {g z : G} (hg : g ∈ H) (hz : z ∈ Opp p H) :
    g * z * g⁻¹ ∈ Opp p H := by
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * z' * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  exact (CFSG.pPrimeCore_normal (p := p) (G := H)).conj_mem z' hz' ⟨g, hg⟩

theorem Opp_coprime (p : ℕ) [Fact p.Prime] (H : Subgroup G) :
    Nat.Coprime p (Nat.card (Opp p H)) := by
  have h : Opp p H = (pPrimeCore p H).map H.subtype := rfl
  rw [h, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card (p := p) (G := H)

theorem le_Opp_of_normalized {p : ℕ} {N H : Subgroup G} (hNH : N ≤ H)
    (hn : ∀ h ∈ H, ∀ x ∈ N, h * x * h⁻¹ ∈ N) (hc : Nat.Coprime p (Nat.card N)) :
    N ≤ Opp p H := by
  have hN : (N.subgroupOf H).Normal := ⟨fun x hx h => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hn h h.2 x hx⟩
  have hcop : Nat.Coprime p (Nat.card (N.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hc
  have hle : N.subgroupOf H ≤ pPrimeCore p H := le_sSup ⟨hN, hcop⟩
  intro x hx
  exact ⟨⟨x, hNH hx⟩, hle hx, rfl⟩

theorem Opp_le_Opp_of_normalized {p : ℕ} [Fact p.Prime] {C H : Subgroup G} (hCH : C ≤ H)
    (hCn : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C) : Opp p C ≤ Opp p H := by
  have hmem : ∀ g ∈ H, ∀ z ∈ Opp p C, g * z * g⁻¹ ∈ Opp p C := by
    intro g hg z hz
    set N : Subgroup G := (Opp p C).map (MulAut.conj g).toMonoidHom with hN
    have hNC : N ≤ C := by
      rintro _ ⟨x, hx, rfl⟩
      exact hCn g hg x (Opp_le p C hx)
    have hNn : ∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N := by
      rintro c hc _ ⟨x, hx, rfl⟩
      have hc' : g⁻¹ * c * g ∈ C := by
        simpa using hCn g⁻¹ (H.inv_mem hg) c hc
      refine ⟨(g⁻¹ * c * g) * x * (g⁻¹ * c * g)⁻¹, Opp_conj_mem hc' hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hNc : Nat.Coprime p (Nat.card N) := by
      rw [hN, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact Opp_coprime p C
    have hle := le_Opp_of_normalized hNC hNn hNc
    exact hle ⟨z, hz, rfl⟩
  exact le_Opp_of_normalized ((Opp_le p C).trans hCH) (fun g hg z hz => hmem g hg z hz)
    (Opp_coprime p C)

theorem conjBy_Opp_le {p : ℕ} [Fact p.Prime] (g : G) (H : Subgroup G) :
    conjBy g (Opp p H) ≤ Opp p (conjBy g H) := by
  refine le_Opp_of_normalized (Subgroup.map_mono (Opp_le p H)) ?_ ?_
  · rintro _ ⟨h, hh, rfl⟩ _ ⟨x, hx, rfl⟩
    refine ⟨h * x * h⁻¹, Opp_conj_mem hh hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact Opp_coprime p H

theorem conjBy_conjBy_inv (g : G) (H : Subgroup G) : conjBy g⁻¹ (conjBy g H) = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    simpa [mul_assoc] using hh
  · intro hx
    exact ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, by group⟩

theorem conjBy_Opp {p : ℕ} [Fact p.Prime] (g : G) (H : Subgroup G) :
    conjBy g (Opp p H) = Opp p (conjBy g H) := by
  refine le_antisymm (conjBy_Opp_le g H) ?_
  have h := conjBy_Opp_le (p := p) g⁻¹ (conjBy g H)
  rw [conjBy_conjBy_inv] at h
  intro x hx
  have h2 : conjBy g (conjBy g⁻¹ (Opp p (conjBy g H))) = Opp p (conjBy g H) := by
    have := conjBy_conjBy_inv g⁻¹ (Opp p (conjBy g H))
    simpa using this
  have h3 : conjBy g (conjBy g⁻¹ (Opp p (conjBy g H))) ≤ conjBy g (Opp p H) :=
    Subgroup.map_mono h
  rw [h2] at h3
  exact h3 hx

theorem le_of_coprime_relIndex {X D Y : Subgroup G} (hXD : X ≤ D)
    (hXn : ∀ d ∈ D, ∀ x ∈ X, d * x * d⁻¹ ∈ X) (hYD : Y ≤ D)
    (hcop : Nat.Coprime (Nat.card Y) (X.relIndex D)) : Y ≤ X := by
  have hN : (X.subgroupOf D).Normal := ⟨fun x hx h => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hXn h h.2 x hx⟩
  let f := QuotientGroup.mk' (X.subgroupOf D)
  let A := (Y.subgroupOf D).map f
  have h1 : Nat.card A ∣ Nat.card Y := by
    have := (Y.subgroupOf D).card_map_dvd f
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYD).toEquiv] at this
  have h2 : Nat.card A ∣ X.relIndex D := Subgroup.card_subgroup_dvd_card A
  have h3 : Nat.card A = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hA : A = ⊥ := (Subgroup.eq_bot_iff_card A).mpr h3
  intro y hy
  have hyD : y ∈ D := hYD hy
  have hmem : f ⟨y, hyD⟩ ∈ A :=
    Subgroup.mem_map_of_mem f (show (⟨y, hyD⟩ : ↥D) ∈ Y.subgroupOf D from hy)
  rw [hA, Subgroup.mem_bot] at hmem
  haveI := hN
  exact (QuotientGroup.eq_one_iff (N := X.subgroupOf D) (⟨y, hyD⟩ : ↥D)).mp hmem

end CFSG.RankThree.PartTwo.Sec21.FF79.L14
