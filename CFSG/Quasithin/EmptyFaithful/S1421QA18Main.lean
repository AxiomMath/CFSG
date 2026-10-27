module

public import CFSG.Quasithin.EmptyFaithful.S1421QA18G
public import CFSG.Quasithin.EmptyFaithful.S1421QA18Rig
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Lemma14218NormalLegacyBare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
    (oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) →
    ¬ mcOf T ≤ K1 → mcOf T ≤ Subgroup.normalizer (K1 : Set G)

@[expose] def Lemma14218KcEqLegacyBare : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) →
    (oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1) →
    ∀ L ∈ cComp (mcOf T), K1 ≤ L → L ≤ K1

namespace S1421QA18

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

omit [Finite G] in
theorem le_normalizer_of_normal_subgroupOf {K M : Subgroup G} (hKM : K ≤ M)
    (h : (K.subgroupOf M).Normal) : M ≤ Subgroup.normalizer (K : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have h1 := h.conj_mem ⟨k, hKM hk⟩ hk ⟨m, hm⟩
    exact h1
  · intro hk
    have hkM' : m * k * m⁻¹ ∈ M := hKM hk
    have h1 := h.conj_mem ⟨m * k * m⁻¹, hkM'⟩ hk ⟨m⁻¹, M.inv_mem hm⟩
    have e : m⁻¹ * (m * k * m⁻¹) * (m⁻¹)⁻¹ = k := by group
    exact e ▸ h1

theorem lemma14218Normal_of_kcEq_legacyBare (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hKc : Lemma14218KcEqLegacyBare) : Lemma14218NormalLegacyBare := by
  intro G _ _ T M H K1 st h13 hsurv htail hnot
  have hyp := st.hyp
  have hK1Mc : K1 ≤ mcOf T := S1421.K1_le_mcOf st
  obtain ⟨z, -, hz1, -, hzZ, -, -, -, -⟩ := exists_z hyp
  have hne : pCoreOf 2 (mcOf T) ≠ ⊥ := fun hb =>
    hz1 (by simpa using (hb ▸ omegaOneCenter_le_pCoreOf_mcOf hyp hzZ : z ∈ (⊥ : Subgroup G)))
  have hS : IsSylowTwoOf (S1421.sOf T K1) (mcOf T) := by
    rw [← htail.2.1]
    exact isSylowTwoOf_of_isSylowTwo hyp.sylow hyp.toQTFE14.t_le_mc
  obtain ⟨L, hL, hKL, hLn⟩ := S1421.exists_cComp_normal_of_syl h37 h38 h39 st hne hS hK1Mc
  have hLK : L = K1 := le_antisymm (hKc G T M H K1 st h13 hsurv htail L hL hKL) hKL
  rw [hLK] at hLn
  exact le_normalizer_of_normal_subgroupOf hK1Mc hLn

theorem le_K1_of_order (st : Setting1427 T M H K1) (hS : S1421.sOf T K1 = T)
    (hsurv : Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) (hO : D4Order) :
    T ≤ K1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨D, _, hD, TD, P₁, P₂, yam, ⟨φ⟩⟩, hq1, hsp, -, -⟩ := hsurv
  have hDc := hO D hD
  have hfinD : Finite D := Nat.finite_of_card_ne_zero (by rw [hDc]; norm_num)
  have hTA : T ≤ K1 ⊔ bigB K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) :=
    calc T = S1421.sOf T K1 := hS.symm
      _ ≤ bigB K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1) := le_sup_right
      _ ≤ _ := le_sup_right
  have hinj : Function.Injective
      (P₁.subtype.comp ((iso1 φ).toMonoidHom.comp (Subgroup.inclusion hTA))) :=
    Subtype.val_injective.comp ((iso1 φ).injective.comp (Subgroup.inclusion_injective hTA))
  have hdvd : Nat.card ↥T ∣ Nat.card D := Subgroup.card_dvd_of_injective _ hinj
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp st.hyp.sylow.1
  have hn12 : n ≤ 12 := by
    rw [hn, hDc, show (211341312 : ℕ) = 2 ^ 12 * 51597 by norm_num] at hdvd
    have h1 : 2 ^ n ∣ 2 ^ 12 :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left n (by norm_num)) hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have hK1card : Nat.card ↥K1 = 258048 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥K1)
    have h2 : Nat.card (OTwoQuot K1) = 2 ^ 3 * (4 ^ 3 - 1) :=
      IsL2Quot.card (by norm_num) hq1
    have h3 : Nat.card ↥(pCoreOf 2 K1) = Nat.card ↥(CFSG.Open.pCore 2 ↥K1) :=
      Subgroup.card_map_of_injective K1.subtype_injective
    have h4 : Nat.card ↥(pCoreOf 2 K1) = 2 ^ (1 + 2 * 4) := hsp.2.1
    rw [h1, ← h3, h4]
    exact (congrArg (· * 2 ^ (1 + 2 * 4)) h2).trans (by norm_num)
  have hsyl : Nat.card ↥(T ⊓ K1) = 2 ^ 12 := by
    have h1 := IsSylowTwoOf.card_eq st.notation_.sylow
    rw [h1, twoPart, hK1card, Nat.factorization_def _ Nat.prime_two,
      show (258048 : ℕ) = 2 ^ 12 * 63 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have heq : T ⊓ K1 = T := Subgroup.eq_of_le_of_card_ge inf_le_left (by
    rw [hn, hsyl]; exact Nat.pow_le_pow_right (by norm_num) hn12)
  exact inf_eq_left.mp heq

theorem lemma14218_of_le (h311 : Theorem311) (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1)
    (hsurv : Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1))
    (htail : oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1)
    (hMc : mcOf T ≤ K1) :
    ∃ (M₁ M₂ : Subgroup G) (z : G),
      (∃ (D : Type) (_ : Group D), IsLieOverTwo .trialityD4 0 1 D ∧
        IsExtensionOfLieAmalgam D M₁ M₂) ∧
      z ^ 2 = 1 ∧ z ≠ 1 ∧ z ∈ twoPrimeResidual M₁ ∧
      z ∈ Subgroup.centralizer (twoPrimeResidual M₁ : Set G) ∧
      Subgroup.centralizer ({z} : Set G) ≤ M₁ := by
  have hyp := st.hyp
  obtain ⟨hK, hST, hQ⟩ := htail
  have hS : S1421.sOf T K1 = T := hST.symm
  have hTK : T ≤ K1 := hyp.toQTFE14.t_le_mc.trans hMc
  have hK1Mc : K1 ≤ mcOf T := S1421.K1_le_mcOf st
  obtain ⟨z, hz2, hz1, -, -, hzr, hzc, hzC, -⟩ := exists_z hyp
  have hA₁ := sup_bigB_eq h311 st h13 hS hTK
  obtain ⟨⟨D, _, hD, TD, P₁, P₂, yam, ⟨φ⟩⟩, -, hsp, -, -⟩ := hsurv
  refine ⟨mcOf T, S1421.l2Of T H (yOfL22 T M) ⊔
    bigB K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1), z, ⟨D, inferInstance, hD, ?_⟩,
    hz2, hz1, hzr, hzc, hzC.le⟩
  have hext := isExtension_of_iso φ yam (fun b hb₁ hb₂ hc => by
    obtain ⟨hck, hcl⟩ := centralizes_of_conj_eq_one φ hb₁ hb₂ hc
    have hbK : b ∈ K1 := hA₁ ▸ hb₁
    exact eq_one_of_centralizes st hQ hsp (hK1Mc hbK) (fun k hk => hck k (Subgroup.mem_sup_left hk))
      (fun l hl => hcl l (Subgroup.mem_sup_left hl)))
  rwa [hA₁.trans (le_antisymm hMc hK1Mc).symm] at hext

theorem lemma14218_of_normal (h311 : Theorem311) (hR : D4AmalgamRigid) (hO : D4Order)
    (st : Setting1427 T M H K1)
    (h13 : pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1)
    (hsurv : Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1))
    (htail : oTwoUpper H = K1 ∧ T = S1421.sOf T K1 ∧ pCoreOf 2 (mcOf T) = pCoreOf 2 K1)
    (hnorm : mcOf T ≤ Subgroup.normalizer (K1 : Set G)) :
    ∃ (M₁ M₂ : Subgroup G) (z : G),
      (∃ (D : Type) (_ : Group D), IsLieOverTwo .trialityD4 0 1 D ∧
        IsExtensionOfLieAmalgam D M₁ M₂) ∧
      z ^ 2 = 1 ∧ z ≠ 1 ∧ z ∈ twoPrimeResidual M₁ ∧
      z ∈ Subgroup.centralizer (twoPrimeResidual M₁ : Set G) ∧
      Subgroup.centralizer ({z} : Set G) ≤ M₁ := by
  have hyp := st.hyp
  obtain ⟨hK, hST, hQ⟩ := htail
  have hS : S1421.sOf T K1 = T := hST.symm
  have hTK : T ≤ K1 := le_K1_of_order st hS hsurv hO
  have hK1Mc : K1 ≤ mcOf T := S1421.K1_le_mcOf st
  obtain ⟨z, hz2, hz1, -, -, hzr, hzc, hzC, -⟩ := exists_z hyp
  have hA₁ := sup_bigB_eq h311 st h13 hS hTK
  have hbig := bigB_eq h311 st h13 hS hTK
  obtain ⟨⟨D, _, hD, TD, P₁, P₂, yam, ⟨φ⟩⟩, -, hsp, -, -⟩ := hsurv
  have hrig := hR D hD TD P₁ P₂ yam
  have hNTM : Subgroup.normalizer (T : Set G) ≤ M ⊓ mcOf T := hyp.normalizer_le
  have hBM : K1 ⊓ Subgroup.normalizer (T : Set G) ≤ M := by
    have hb := st.notation_.borel_le
    rw [inf_eq_left.mpr hTK] at hb
    exact hb
  have hFr : mcOf T ≤ K1 ⊔ (mcOf T ⊓ Subgroup.normalizer (T : Set G)) := by
    intro m hm
    obtain ⟨g, hg, hgn⟩ :=
      exists_mem_normalizer_of_normalizes hTK hyp.sylow.1 hyp.sylow.2 (hnorm hm)
    have hgm : g⁻¹ * m ∈ mcOf T ⊓ Subgroup.normalizer (T : Set G) :=
      ⟨(mcOf T).mul_mem ((mcOf T).inv_mem (hK1Mc hg)) hm, hgn⟩
    have hmm : m = g * (g⁻¹ * m) := by group
    rw [hmm]
    exact (K1 ⊔ _).mul_mem (Subgroup.mem_sup_left hg) (Subgroup.mem_sup_right hgm)
  have key : ∀ A₁ A₂ : Subgroup G, K1 = A₁ →
      S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G) = A₂ →
      (RankTwoAmalgam.ofSubgroups A₁ A₂).Iso (RankTwoAmalgam.ofSubgroups P₁ P₂) →
      IsExtensionOfLieAmalgam D (mcOf T)
        ((S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G)) ⊔
          (mcOf T ⊓ Subgroup.normalizer (T : Set G))) := by
    intro A₁ A₂ h₁ h₂ φ
    subst h₁ h₂
    have hN'M : mcOf T ⊓ Subgroup.normalizer (T : Set G) ≤ M :=
      inf_le_right.trans (hNTM.trans inf_le_left)
    have hN'norm : mcOf T ⊓ Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer
        ((S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :
          Set G) :=
      le_normalizer_l2_sup hK hN'M inf_le_right (inf_le_left.trans hnorm)
    have hM₂norm : (S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G)) ⊔
        (mcOf T ⊓ Subgroup.normalizer (T : Set G)) ≤ Subgroup.normalizer
        ((S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :
          Set G) := sup_le Subgroup.le_normalizer hN'norm
    have hM₂M : (S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G)) ⊔
        (mcOf T ⊓ Subgroup.normalizer (T : Set G)) ≤ M :=
      sup_le (sup_le (l2_le_M hyp) hBM) hN'M
    refine isExtension_of_rigid φ yam hrig hK1Mc le_sup_left
      (fun m hm a ha => (Subgroup.mem_normalizer_iff.mp (hnorm hm) a).mp ha)
      (fun m hm a ha => (Subgroup.mem_normalizer_iff.mp (hM₂norm hm) a).mp ha)
      (hFr.trans (sup_le_sup_left (le_inf inf_le_left le_sup_right) K1))
      (sup_le le_sup_left ((le_inf inf_le_left le_sup_right).trans le_sup_right))
      (fun g hg => ?_) (l2_sup_inf_mcOf_le st hK hTK)
      (fun x hx h₁ h₂ => eq_one_of_centralizes st hQ hsp hx.1 h₁
        (fun l hl => h₂ l (Subgroup.mem_sup_left hl)))
    have hgM : g ∈ M := hM₂M hg.2
    have hbi := st.notation_.borel_inf
    rw [hK, inf_eq_left.mpr hTK] at hbi
    exact Subgroup.mem_sup_right ⟨hg.1, hbi ⟨hgM, hg.1⟩⟩
  refine ⟨mcOf T, (S1421.l2Of T H (yOfL22 T M) ⊔ K1 ⊓ Subgroup.normalizer (T : Set G)) ⊔
    (mcOf T ⊓ Subgroup.normalizer (T : Set G)), z, ⟨D, inferInstance, hD,
    key _ _ hA₁.symm (by rw [hbig]) φ⟩, hz2, hz1, hzr, hzc, hzC.le⟩

theorem lemma14218D4_of_inputs_legacyBare (h311 : Theorem311) (hN : Lemma14218NormalLegacyBare)
    (hR : D4AmalgamRigid) (hO : D4Order) : Lemma14218D4LegacyBare := by
  intro G _ _ T M H K1 st h13 hsurv htail
  by_cases hMc : mcOf T ≤ K1
  · exact lemma14218_of_le h311 st h13 hsurv htail hMc
  · exact lemma14218_of_normal h311 hR hO st h13 hsurv htail
      (hN G T M H K1 st h13 hsurv htail hMc)

end S1421QA18

end CFSG.Quasithin
