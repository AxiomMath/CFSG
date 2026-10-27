module

public import CFSG.Quasithin.H13.L32A768h
public import CFSG.Quasithin.Background.C2Six
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.Quasithin.H13.L32A768a
public import CFSG.Quasithin.H13.L32A768b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Lemma14_7_68_case34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    ∀ u ∈ L32A.u0 T V, u ≠ 1 → (∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) →
      QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.centralizer ({u} : Set G))
        (Subgroup.centralizer ({u} : Set G)) →
      ∀ I ∈ cComp (Subgroup.centralizer ({u} : Set G)),
        (I.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal → L32A.kz T V ≤ I →
          I ≠ L32A.kz T V →
          (Quasithin.A36Case3 ↥(modO2Image (Subgroup.centralizer ({u} : Set G)) I) ∨
            Quasithin.A36Case4 ↥(modO2Image (Subgroup.centralizer ({u} : Set G)) I)) →
          ¬ pCoreOf 2 (L32A.kz T V) ≤ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) → False

namespace L32A

variable {G : Type} [Group G] [Finite G]

theorem alt5_two_involutions : ∃ a b : alternatingGroup (Fin 5), a ^ 2 = 1 ∧ b ^ 2 = 1 ∧
    a ≠ 1 ∧ b ≠ 1 ∧ (a * b⁻¹) ^ 2 = 1 ∧ a * b⁻¹ ≠ 1 :=
  ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, by decide⟩

theorem inf_pCoreOf_le_of_le {X B : Subgroup G} (hXB : X ≤ B) :
    X ⊓ pCoreOf 2 B ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B).to_le inf_le_right)
  intro x hx
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B (hXB hx)⟩

theorem not_pCoreOf_le_of_sl2 {G₀ I K : Subgroup G} (hKI : K ≤ I) (hIG : I ≤ G₀)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) {p : ℕ} [Fact p.Prime]
    (hp2 : (2 : ZMod p) ≠ 0)
    (ψ : ↥(modO2Image G₀ I) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hψ : ∀ x, ψ x = 1 → Odd (orderOf x)) : ¬ pCoreOf 2 K ≤ pCoreOf 2 G₀ := by
  intro hle
  have hKG : K ≤ G₀ := hKI.trans hIG
  let κ₀ : ↥K →* ↥G₀ ⧸ CFSG.pCore 2 ↥G₀ :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥G₀)).comp (Subgroup.inclusion hKG)
  have hκ₀ : ∀ k, κ₀ k ∈ modO2Image G₀ I := fun k =>
    ⟨Subgroup.inclusion hKG k, Subgroup.mem_subgroupOf.mpr (hKI k.2), rfl⟩
  let κ : ↥K →* ↥(modO2Image G₀ I) := κ₀.codRestrict _ hκ₀
  have hκ1 : ∀ k : ↥K, κ k = 1 ↔ (k : G) ∈ pCoreOf 2 G₀ := by
    intro k
    have h1 : κ k = 1 ↔ κ₀ k = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1]
    exact (QuotientGroup.eq_one_iff _).trans C2Six.mem_pCore_two_iff
  let π : ↥K →* alternatingGroup (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ1 : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
    intro k
    show e (QuotientGroup.mk k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact (QuotientGroup.eq_one_iff _).trans C2Six.mem_pCore_two_iff
  have hinv : ∀ k : ↥K, π k ^ 2 = 1 → π k ≠ 1 → (ψ (κ k)) ^ 2 = 1 ∧ ψ (κ k) ≠ 1 := by
    intro k h2 h1
    have hk2 : κ (k ^ 2) = 1 := by
      rw [hκ1]
      exact hle ((hπ1 _).mp (by rw [map_pow, h2]))
    have hκne : κ k ≠ 1 := by
      intro h
      have hk : (k : G) ∈ pCoreOf 2 K :=
        inf_pCoreOf_le_of_le hKG ⟨k.2, (hκ1 k).mp h⟩
      exact h1 ((hπ1 k).mpr hk)
    refine ⟨by rw [← map_pow, ← map_pow, hk2, map_one], fun hψ1 => ?_⟩
    have hodd := hψ _ hψ1
    have hord : orderOf (κ k) = 2 :=
      orderOf_eq_prime (by rw [← map_pow, hk2]) hκne
    rw [hord] at hodd
    exact absurd hodd (by decide)
  obtain ⟨a, b, ha2, hb2, ha1, hb1, hab2, hab1⟩ := alt5_two_involutions
  obtain ⟨k₁, rfl⟩ := hπs a
  obtain ⟨k₂, rfl⟩ := hπs b
  obtain ⟨h₁, n₁⟩ := hinv k₁ ha2 ha1
  obtain ⟨h₂, n₂⟩ := hinv k₂ hb2 hb1
  obtain ⟨-, n₁₂⟩ := hinv (k₁ * k₂⁻¹) (by rwa [map_mul, map_inv]) (by rwa [map_mul, map_inv])
  have e₁ := LinearGroups.SL2_coe_eq_neg_one_of_sq hp2 _ h₁ n₁
  have e₂ := LinearGroups.SL2_coe_eq_neg_one_of_sq hp2 _ h₂ n₂
  apply n₁₂
  rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one]
  exact Subtype.ext (e₁.trans e₂.symm)

variable {T L V : Subgroup G}

theorem nonempty_quot_kz_alt5 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    Nonempty (↥(kz T V) ⧸ CFSG.pCore 2 ↥(kz T V) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨-, π, -, hπs, hπk, -⟩ := isL24Section_u0 h hMod h63
  have := isSimpleGroup_sl24
  obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty card_sl24
  have hk : π.ker = CFSG.pCore 2 ↥(kz T V) := by
    rw [hπk, pCoreOf_subgroupOf_self]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective π hπs).trans e)⟩

theorem two_ne_zero_zmod {p : ℕ} (hp2 : 2 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem lemma14_7_68_quasi_of (hMod : StmtL32NModule) (h63 : Thm14_7_63) (h36 : A36ForSQTK)
    (h34 : Lemma14_7_68_case34) : Lemma14_7_68_quasi := by
  intro G _ _ T L V h u hu hu1 hTu hS I hI hIn hKI hne
  set Gu := Subgroup.centralizer ({u} : Set G) with hGu
  have hUe := isElemAbelian_fsuU_of h hMod
  have hu2 : u * u = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one hUe (centralizerMod_le_left _ _ _ hu)
  have hH : pCoreOf 2 Gu ≠ ⊥ := pCoreOf_centralizer_ne_bot hu1 hu2
  have hA := CFSG.Quasithin.lemma_1_2_1_four_strong h.fsu.qtke h.fsu.simple h.fsu.nonabelian h36
    hH hI
  have hIG : I ≤ Gu := le_of_mem_cComp hI
  obtain ⟨eK⟩ := nonempty_quot_kz_alt5 h hMod h63
  rcases hA.1 with ⟨hc, -, -⟩ | ⟨hc, -, -⟩ | h3 | h4
  · obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hI
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hc.1
  · obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hI
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hc.1
  · refine (h34 G T L V h u hu hu1 hTu hS I hI hIn hKI hne (Or.inl h3) ?_).elim
    obtain ⟨p, hp, hp3, -, ⟨eF⟩, ⟨-, ψ, -, hψk, -⟩⟩ := h3
    have : Fact p.Prime := ⟨hp⟩
    refine not_pCoreOf_le_of_sl2 hKI hIG eK (two_ne_zero_zmod (by omega)) ψ fun x hx => ?_
    have hxF : x ∈ CFSG.fittingSubgroup ↥(modO2Image Gu I) := by
      rw [← hψk]
      exact hx
    have hcard : Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image Gu I)) = p ^ 2 := by
      rw [Nat.card_congr (eF.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have hdvd : orderOf x ∣ p ^ 2 := by
      have := orderOf_dvd_natCard (⟨x, hxF⟩ : ↥(CFSG.fittingSubgroup ↥(modO2Image Gu I)))
      rwa [Subgroup.orderOf_mk, hcard] at this
    exact (hp.odd_of_ne_two (by omega)).pow.of_dvd_nat hdvd
  · refine (h34 G T L V h u hu hu1 hTu hS I hI hIn hKI hne (Or.inr h4) ?_).elim
    obtain ⟨-, -, ⟨eS⟩, hprimes⟩ := h4
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let ψ : ↥(modO2Image Gu I) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
      eS.toMonoidHom.comp (QuotientGroup.mk' _)
    refine not_pCoreOf_le_of_sl2 hKI hIG eK (two_ne_zero_zmod (by norm_num)) ψ
      fun x hx => ?_
    have hxF : x ∈ CFSG.fittingSubgroup ↥(modO2Image Gu I) := by
      have h1 : QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image Gu I)) x = 1 := by
        apply eS.injective
        rw [map_one]
        exact hx
      exact (QuotientGroup.eq_one_iff x).mp h1
    have h2 : ¬ 2 ∣ Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image Gu I)) := by
      intro h2
      rcases (hprimes 2 Nat.prime_two h2).1 with h | h | h <;> norm_num at h
    have hdvd := orderOf_dvd_natCard (⟨x, hxF⟩ : ↥(CFSG.fittingSubgroup ↥(modO2Image Gu I)))
    rw [Subgroup.orderOf_mk] at hdvd
    have h3 : ¬ 2 ∣ orderOf x := fun h => h2 (h.trans hdvd)
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)

end L32A

end CFSG.Quasithin.H13
