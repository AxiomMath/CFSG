module

public import CFSG.Quasithin.H13.L32A707b
public import CFSG.Quasithin.H13.L32ASk7
public import CFSG.Quasithin.EmptyFaithful.S146zMComp
public import CFSG.Quasithin.H13.L32A708a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem eq_bot_of_isPGroup_three_of_coprime {Q : Type*} [Group Q] {P : Subgroup Q} [Finite P]
    (hP : IsPGroup 3 P) (hc : Nat.Coprime (Nat.card P) 3) : P = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq P hk
  · have h3 : 3 ∣ Nat.card P := by
      rw [hk]
      exact dvd_pow_self 3 (Nat.succ_ne_zero k)
    exact absurd h3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc.symm)

theorem fitting_eq_bot_of_coprime_three {Q : Type} [Group Q] [Finite Q]
    (h3 : IsPGroup 3 ↥(CFSG.fittingSubgroup Q)) {S : Subgroup Q} (hS : IsSubnormal S ⊤)
    (hS3 : Nat.Coprime (Nat.card S) 3) : CFSG.fittingSubgroup ↥S = ⊥ := by
  rw [CFSG.fitting_eq_sup_pCore]
  refine iSup_eq_bot.mpr fun p => ?_
  have hpf : Fact (Nat.Prime p.1.1) := ⟨Nat.prime_of_mem_primeFactors p.1.2⟩
  set P := CFSG.pCore p.1.1 ↥S with hP
  have h1 : P.map S.subtype ≤ pCoreOf p.1.1 S := by
    rw [hP, pCoreOf]
  have h2 : pCoreOf p.1.1 S ≤ pCoreOf p.1.1 (⊤ : Subgroup Q) := A4.pCoreOf_le_of_subnormal p.1.1 hS
  have h3' : pCoreOf p.1.1 (⊤ : Subgroup Q) ≤ CFSG.pCore p.1.1 Q := by
    have hn : (pCoreOf p.1.1 (⊤ : Subgroup Q)).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_pCoreOf p.1.1 ⊤))
    exact le_sSup ⟨hn, pCoreOf_isPGroup p.1.1 ⊤⟩
  have himg : P.map S.subtype ≤ CFSG.fittingSubgroup Q :=
    ((h1.trans h2).trans h3').trans (CFSG.pCore_le_fitting Q p.1.1)
  have hcard : Nat.card ↥(P.map S.subtype) = Nat.card P :=
    Subgroup.card_map_of_injective S.subtype_injective
  have hc : Nat.Coprime (Nat.card ↥(P.map S.subtype)) 3 := by
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card P) hS3
  have hbot := eq_bot_of_isPGroup_three_of_coprime (h3.to_le himg) hc
  exact (Subgroup.map_eq_bot_iff_of_injective P S.subtype_injective).mp hbot

variable {G : Type} [Group G] [Finite G]

namespace Setting147

variable {T L V H : Subgroup G}

theorem exists_sz_comp (h76 : Lemma14_7_6) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G))
    (hX : CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) ≠ ⊥) :
    ∃ K ∈ cComp H, ∃ n : ℕ, IsSz n (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      ∀ c ∈ l1 T L V, ∀ k ∈ conjClosure K T, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNn : (CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pPrimeCore_normal
  have hN3 : Nat.Coprime (Nat.card ↥(CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) 3 :=
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H ⧸ CFSG.pCore 2 ↥H)).symm
  have hF3 := h76 G T L V H S
  have hNsolv : ¬ Group.IsSolvable ↥(CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro hs
    have hsub : IsSubnormal (CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) ⊤ :=
      IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
    have hF := fitting_eq_bot_of_coprime_three hF3 hsub hN3
    exact hX (Subgroup.eq_bot_of_card_eq _
      ((CFSG.fitting_eq_bot_iff_card_eq_one_of_solvable _).mp hF))
  obtain ⟨J, hJ, hJN⟩ := exists_cComp_le_of_not_solvable le_top inferInstance hNsolv
  obtain ⟨K, hK, hKJ⟩ := exists_cComp_modO2Image_eq hJ
  have hK3 : Nat.Coprime (Nat.card ↥(modO2Image H K)) 3 := by
    rw [hKJ]
    exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hJN) hN3
  have hK3' : ¬ 3 ∣ Nat.card ↥(modO2Image H K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hK3.symm
  have hA := CFSG.Quasithin.lemma_1_2_1_four_strong S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian h36 S.hz.1.2 hK
  obtain ⟨e⟩ := modO2_mulEquiv hK
  have hKsub : IsSubnormal (modO2Image H K) ⊤ := subnormal_of_mem_cComp (modO2Image_mem_cComp hK)
  refine ⟨K, hK, ?_⟩
  have hsz : ∃ n : ℕ, IsSz n (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rcases hA.1 with ⟨-, -, hlistK⟩ | ⟨-, hZ3, -⟩ | h3 | h4
    · obtain ⟨f, -, -, hf⟩ := hlist _ hlistK hK3'
      exact ⟨f, isSz_congr e.symm hf⟩
    · exfalso
      apply hK3'
      rw [← hZ3]
      exact Subgroup.card_subgroup_dvd_card _
    · exact absurd (fitting_eq_bot_of_coprime_three hF3 hKsub hK3)
        (C.fitting_ne_bot_coprime_six (Or.inl h3)).1
    · exact absurd (fitting_eq_bot_of_coprime_three hF3 hKsub hK3)
        (C.fitting_ne_bot_coprime_six (Or.inr h4)).1
  obtain ⟨n, hn⟩ := hsz
  refine ⟨n, hn, fun c hc k hk => ?_⟩
  have hcH : c ∈ H := Setting147.l1H' S hc
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := Setting147.TH' S
  have hK₀N : conjClosure K T ≤ ((CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype := by
    refine conjClosure_le fun t ht y hy => ?_
    have hyH : y ∈ H := hKH hy
    have hy' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ ∈
        CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) :=
      hJN (hKJ ▸ mem_modO2Image'.mpr ⟨⟨y, hyH⟩, hy, rfl⟩)
    refine ⟨⟨t, hTH ht⟩ * ⟨y, hyH⟩ * ⟨t, hTH ht⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hNn.conj_mem _ hy' _
  obtain ⟨k', hk', rfl⟩ := hK₀N hk
  have hLn : ∀ x ∈ modO2Image H (l1 T L V), ∀ g : ↥H ⧸ CFSG.pCore 2 ↥H,
      g * x * g⁻¹ ∈ modO2Image H (l1 T L V) := by
    intro x hx g
    obtain ⟨l, hl, rfl⟩ := mem_modO2Image'.mp hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥H) g
    rw [← map_inv, ← map_mul, ← map_mul]
    refine mem_modO2Image'.mpr ⟨h * l * h⁻¹, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHL h.2) l).mp hl
  have hcl : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨c, hcH⟩ ∈ modO2Image H (l1 T L V) :=
    mem_modO2Image'.mpr ⟨⟨c, hcH⟩, hc, rfl⟩
  have hk'' : QuotientGroup.mk' (CFSG.pCore 2 ↥H) k' ∈
      CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) := hk'
  obtain ⟨cb, hcb⟩ : ∃ x, QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨c, hcH⟩ = x := ⟨_, rfl⟩
  obtain ⟨kb, hkb⟩ : ∃ x, QuotientGroup.mk' (CFSG.pCore 2 ↥H) k' = x := ⟨_, rfl⟩
  rw [hcb] at hcl
  rw [hkb] at hk''
  have hwL : cb * kb * cb⁻¹ * kb⁻¹ ∈ modO2Image H (l1 T L V) := by
    rw [show cb * kb * cb⁻¹ * kb⁻¹ = cb * (kb * cb⁻¹ * kb⁻¹) by group]
    exact mul_mem hcl (hLn _ (inv_mem hcl) kb)
  have hwN : cb * kb * cb⁻¹ * kb⁻¹ ∈ CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) :=
    mul_mem (hNn.conj_mem _ hk'' cb) (inv_mem hk'')
  have hcard := Setting147.card_l1_star S h1222 h1332 h1334 hHL
  have hw1 : cb * kb * cb⁻¹ * kb⁻¹ = 1 := by
    have h1 : orderOf (cb * kb * cb⁻¹ * kb⁻¹) ∣ 3 := by
      rw [← hcard, ← Subgroup.orderOf_mk _ hwL]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (cb * kb * cb⁻¹ * kb⁻¹) ∣
        Nat.card ↥(CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← Subgroup.orderOf_mk _ hwN]
      exact orderOf_dvd_natCard _
    exact orderOf_eq_one_iff.mp
      ((Nat.Coprime.coprime_dvd_left h1 hN3.symm).eq_one_of_dvd h2)
  have hab : QuotientGroup.mk' (CFSG.pCore 2 ↥H) k' *
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨c, hcH⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨c, hcH⟩ * QuotientGroup.mk' (CFSG.pCore 2 ↥H) k' := by
    rw [hcb, hkb]
    calc kb * cb = (cb * kb * cb⁻¹ * kb⁻¹)⁻¹ * (cb * kb) := by group
      _ = cb * kb := by rw [hw1, inv_one, one_mul]
  exact mem_O2H_of_commute ⟨c, hcH⟩ k' hab

end Setting147

theorem lemma14_7_7_of
    (h76 : Lemma14_7_6) (h519 : Lemma14_5_19) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hlist : SQTKList3Dvd) (h310 : D310) (h391 : D391) (hI4 : Insp4)
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hSzE : A6.SzEnd) :
    Lemma14_7_7 := by
  intro G _ _ T L V H S hN
  by_contra hX
  have hHL := Setting147.H_le_N_l1 S h1332 hN
  obtain ⟨K, hK, n, hn, hcomm⟩ :=
    Setting147.exists_sz_comp h76 h36 hlist h1222 h1332 h1334 S hHL hX
  exact Setting147.false_of_sz_comp h519 h1222 h1332 h1334 h37 h38 h39 h310 h391 hI4 hD36 hD37
    hD321 hI5 hSzE S hHL hK hn hcomm

end CFSG.Quasithin.H13.L32A
