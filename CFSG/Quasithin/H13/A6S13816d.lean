module

public import CFSG.Quasithin.H13.A6S13816b
public import CFSG.Quasithin.H13.A6S13816c
public import CFSG.Quasithin.EmptyFaithful.SBc11List

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7

namespace L32Case

variable {G : Type} [Group G]

theorem nonempty_sl3 {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
  exact ⟨e.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 F
    (by rw [hcard]; norm_num))⟩

theorem conjClosure_eq_of_normal {H K T : Subgroup G} (hKH : K ≤ H) (hTH : T ≤ H)
    (hn : (K.subgroupOf H).Normal) : conjClosure K T = K := by
  refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (le_conjClosure K T)
  have h1 := hn.conj_mem ⟨k, hKH hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨t, hTH ht⟩
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem map_le_normalizer_map {H A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G))
    {Q : Type*} [Group Q] (f : ↥H →* Q) :
    (B.subgroupOf H).map f ≤
      Subgroup.normalizer (((A.subgroupOf H).map f : Subgroup Q) : Set Q) := by
  rintro _ ⟨b, hb, rfl⟩
  apply Subgroup.le_normalizer_map f
  refine ⟨b, Subgroup.mem_normalizer_iff.mpr fun y => ?_, rfl⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hB (Subgroup.mem_subgroupOf.mp hb)) y

theorem card_eq_eight_of_sylow [Finite G] {Y S : Subgroup G} (hS : IsSylowTwoOf S Y)
    (hY : Nat.card Y = 168) : Nat.card S = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS.2.1
  have h1 := (S.subgroupOf Y).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv, hn, hY] at h1
  have h2 := hS.2.2
  have hn4 : n < 4 := by
    by_contra h
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 (not_lt.mp h)).trans ⟨_, h1.symm⟩
    norm_num at this
  rw [hn]
  rcases n with _ | _ | _ | _ | n
  · norm_num at h1
    omega
  · norm_num at h1
    omega
  · norm_num at h1
    omega
  · norm_num
  · omega

end L32Case

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_ell :
    ∃ ℓ : Subgroup G, ∃ c : G, ℓ ≤ S.L1 ∧ T ≤ Subgroup.normalizer (ℓ : Set G) ∧ c ∈ ℓ ∧
      c ^ 3 = 1 ∧ c ∉ pCoreOf 2 ℓ ∧
      ∀ x ∈ ℓ, x ∈ pCoreOf 2 ℓ ∨ c * c * x ∈ pCoreOf 2 ℓ ∨ c * x ∈ pCoreOf 2 ℓ := by
  by_cases hhat : IsHatA6 L
  · obtain ⟨c, hc, hc3, hcO, hdec⟩ := l0_decomp hhat
    exact ⟨l0 L, c, S.l0_le_L1, A5.le_normalizer_oTwoRes_of_le_normalizer
      (S.T_le_NL.trans normalizer_L_le_o2Z), hc, hc3, hcO, hdec⟩
  · exact ⟨S.L1, S.cL1 hhat, le_rfl, S.T_le_normalizer_L1, S.cL1_mem hhat, S.cL1_cube hhat,
      S.cL1_not_mem hhat, fun x hx => S.L1_decomp hhat hx⟩

theorem L1_le_closure_three {H : Subgroup G} (hH : H ∈ S.Hz) :
    S.L1 ≤ Subgroup.closure {x : G | x ∈ H ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcube : ∀ x ∈ S.L1, x ^ 3 ∈ pCoreOf 2 S.L1 := fun x hx => by
    by_cases hhat : IsHatA6 L
    · exact S.cube_mem_pCoreOf_L1_hat hhat hx
    · exact S.cube_mem_pCoreOf_L1 hhat hx
  show oTwoRes (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) ≤ _
  rw [oTwoRes, Subgroup.closure_le]
  rintro x ⟨hx, m, hm, hxm⟩
  have hxL1 : x ∈ S.L1 := mem_oTwoRes_of_odd hx hm hxm
  refine Subgroup.subset_closure ⟨(le_sup_left.trans hH.1.1) hxL1, ?_⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨_, hcube x hxL1⟩
  have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (x ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hxm, one_pow]
  have h2 : x ^ 3 = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h1)
    rw [(Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at h
    exact h
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

theorem L1_le_conjClosure (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K) (hpsl : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    S.L1 ≤ conjClosure K T := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hcard2 : Set.ncard (conjSubgroupsBy H K) = 2 := by
    rcases CFSG.Quasithin.lemma_1_2_1_three S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
      hH.1.2 hK with hn | ⟨h2, -⟩
    · exact absurd (L32Case.conjClosure_eq_of_normal hKH hTH hn) hne
    · exact h2
  have h3 : 3 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [SBc11.card_of_isPSL_three_two hpsl]
    norm_num
  have hcl := h122 G S.h13.simple S.h13.qtke S.h13.nonabelian H K hH.1.2 hK 3 Nat.prime_three
    (by norm_num) hcard2 h3
  have hN : H ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
      hH.1.2 hTsyl hK
  refine (S.L1_le_closure_three hH).trans (hcl.le.trans (conjClosure_le fun h hh k hk => ?_))
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) k).mp (le_conjClosure K T hk)

theorem false_of_L32 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hne : conjClosure K T ≠ K) (hpsl : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  obtain ⟨ℓ, c, hℓ, hTℓ, hc, hc3, hcO, hdec⟩ := S.exists_ell
  have hℓK : ℓ ≤ conjClosure K T := hℓ.trans (S.L1_le_conjClosure h37 h38 h122 hH hK hne hpsl)
  have hℓH : ℓ ≤ H := hℓ.trans (le_sup_left.trans hH.1.1)
  have hN₀ : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Kb := (K.subgroupOf H).map π with hKb
  set Tb := (T.subgroupOf H).map π with hTb
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) := modO2Image_mem_cComp hK
  have hTbs : IsSylowTwoOf Tb ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTsyl) π hπs
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH.1.2
  obtain ⟨-, hL2⟩ := h38 _ hQ Kb hKbc
  rcases hL2 Tb hTbs with ⟨hnorm, -, -⟩ | ⟨t, htT, -, hconj, -, hcomm, hinf, -, -⟩
  · exact hne (L32Case.conjClosure_eq_of_normal hKH hTH (normal_of_normal_map_of_mem_cComp
      (CFSG.pCore 2 ↥H) (isSolvable_pCore_two_group ↥H) (subgroupOf_mem_cComp hK) hnorm))
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  obtain ⟨e₂⟩ := L32Case.nonempty_sl3 hpsl
  have hKcard : Nat.card Kb = 168 := by
    have h1 := Nat.card_congr e₁.toEquiv
    rw [SBc11.card_of_isPSL_three_two hpsl] at h1
    exact h1.symm
  set X := (ℓ.subgroupOf H).map π with hX
  have hXle : X ≤ Kb ⊔ Kb.map (MulAut.conj t).toMonoidHom := by
    have hcc : (conjClosure (K.subgroupOf H) (T.subgroupOf H)).map H.subtype =
        conjClosure K T := by
      rw [A3.map_conjClosure, Subgroup.map_subgroupOf_eq_of_le hKH,
        Subgroup.map_subgroupOf_eq_of_le hTH]
    have hcl : conjClosure (K.subgroupOf H) (T.subgroupOf H) ≤
        (Kb ⊔ Kb.map (MulAut.conj t).toMonoidHom).comap π := by
      refine conjClosure_le fun s hs k hk => ?_
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      have hs' : π s ∈ Tb := Subgroup.mem_map_of_mem π hs
      have hk' : π k ∈ Kb := Subgroup.mem_map_of_mem π hk
      have hmem : Kb.map (MulAut.conj (π s)).toMonoidHom ∈ conjSubgroupsBy Tb Kb :=
        ⟨π s, hs', rfl⟩
      rw [hconj] at hmem
      have hsk : π s * π k * (π s)⁻¹ ∈ Kb.map (MulAut.conj (π s)).toMonoidHom :=
        ⟨π k, hk', by simp [MulAut.conj_apply]⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · rw [h] at hsk
        exact Subgroup.mem_sup_left hsk
      · rw [h] at hsk
        exact Subgroup.mem_sup_right hsk
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ conjClosure K T := hℓK (Subgroup.mem_subgroupOf.mp hy)
    rw [← hcc] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hcl hz
  have hTX : Tb ≤ Subgroup.normalizer (X : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    L32Case.map_le_normalizer_map hTℓ π
  have hPsyl : IsSylowTwoOf (Tb ⊓ Kb) Kb :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hKbc) hTbs
  have hP8 : Nat.card ↥(Tb ⊓ Kb) = 8 := L32Case.card_eq_eight_of_sylow hPsyl hKcard
  have hNp : IsPGroup 2 (((pCoreOf 2 ℓ).subgroupOf H).map π) := by
    have h1 : IsPGroup 2 ((pCoreOf 2 ℓ).subgroupOf H) :=
      (pCoreOf_isPGroup 2 ℓ).of_equiv
        (Subgroup.subgroupOfEquivOfLe ((pCoreOf_le 2 ℓ).trans hℓH)).symm
    exact h1.map π
  set cb := π ⟨c, hℓH hc⟩ with hcb
  have hcbX : cb ∈ X := ⟨⟨c, hℓH hc⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
  have hcH3 : (⟨c, hℓH hc⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simp [hc3])
  have hcb3 : cb ^ 3 = 1 := by rw [hcb, ← map_pow, hcH3, map_one]
  have hcb1 : cb ≠ 1 := by
    intro h
    have h' : ((⟨c, hℓH hc⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 := h
    have hmem := (QuotientGroup.eq_one_iff _).mp h'
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hmem⟩
    have hk' : c ^ 2 ^ k = 1 := by
      have := congrArg (fun w : ↥(CFSG.pCore 2 ↥H) => ((w : ↥H) : G)) hk
      simpa using this
    exact hcO (by rw [L32Comm.eq_one_of_pow_of_cube hk' hc3]; exact Subgroup.one_mem _)
  have hdecb : ∀ x ∈ X, x ∈ ((pCoreOf 2 ℓ).subgroupOf H).map π ∨
      cb * cb * x ∈ ((pCoreOf 2 ℓ).subgroupOf H).map π ∨
      cb * x ∈ ((pCoreOf 2 ℓ).subgroupOf H).map π := by
    rintro _ ⟨y, hy, rfl⟩
    rcases hdec y (Subgroup.mem_subgroupOf.mp hy) with h | h | h
    · exact Or.inl ⟨y, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    · refine Or.inr (Or.inl ⟨⟨c, hℓH hc⟩ * ⟨c, hℓH hc⟩ * y, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩)
      · simpa using h
      · rw [hcb, map_mul, map_mul]
    · refine Or.inr (Or.inr ⟨⟨c, hℓH hc⟩ * y, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩)
      · simpa using h
      · rw [hcb, map_mul]
  exact L32Comm.false_of_pair (K₁ := Kb) (X := X) (N := ((pCoreOf 2 ℓ).subgroupOf H).map π)
    (P := Tb ⊓ Kb) (t := t) (c := cb) hcomm hinf hXle (hTX htT) (inf_le_left.trans hTX)
    inf_le_right hP8 hKcard (e₁.symm.trans e₂)
    (L32Case.map_le_normalizer_map (le_normalizer_pCoreOf 2 ℓ) π) hNp hcbX hcb3 hcb1 hdecb

end Setting4

theorem case13816L32_of (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h122 : CFSG.Quasithin.Lemma122A) : Case13816L32 := by
  intro G _ _ T L V S _ H hH K hK hne _ hpsl
  exact S.false_of_L32 h37 h38 h122 hH hK hne hpsl

end CFSG.Quasithin.H13.A6

