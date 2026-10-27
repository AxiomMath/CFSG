module

public import CFSG.Quasithin.H13.A5S1327f

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

@[expose] noncomputable def G1bar (S : Setting G T L V) (H : Subgroup G) :
    Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H)) :=
  ((S.L1 ⊔ T).subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))

@[expose] noncomputable def G2bar (S : Setting G T L V) (H : Subgroup G) :
    Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H)) :=
  (H.subgroupOf (S.H0 H)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))

end Setting

@[expose] def FactF618Big : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtAmalgam G₁ G₂ →
    (F6.IsF618CaseFour G₁ G₂ ∨ F6.IsF618CaseFive G₁ G₂ ∨ F6.IsF618CaseSix G₁ G₂ ∨
      F6.IsF618CaseSeven G₁ G₂ ∨ F6.IsF618CaseEightCat G₁ G₂ ∨ F6.IsF618CaseNineCat G₁ G₂ ∨
      F6.IsF618CaseTen G₁ G₂ ∨ F6.IsF618CaseEleven G₁ G₂ ∨ F6.IsF618CaseTwelve G₁ G₂ ∨
      F6.IsF618CaseThirteen G₁ G₂) →
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b

@[expose] def Final1327CaseThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V) (H : Subgroup G),
    IsHStar T (Subgroup.normalizer (L : Set G)) H →
    ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) → Group.IsSolvable ↥H →
    Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)) → pCoreOf 2 (S.H0 H) ≠ ⊥ →
    ¬ ThreeTop (S.H0 H) → F6.IsF618CaseThree (S.G1bar H) (S.G2bar H) → False

theorem isPGroup_oTwoUpper_of_caseTwo {D : Type} [Group D] [Finite D] (h : F6.IsF618CaseTwo D) :
    IsPGroup 3 ↥(oTwoUpper (⊤ : Subgroup D)) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨φ, hφ, hker⟩
  ·
    have hA : oTwoUpper (⊤ : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ≤
        (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      have hodd : Odd (orderOf x) := hx.2
      have h1 : Odd (orderOf x.1) := hodd.of_dvd_nat (orderOf_fst_dvd_orderOf (x := x))
      have h2 : Odd (orderOf x.2) := hodd.of_dvd_nat (orderOf_snd_dvd_orderOf (x := x))
      have hc : ∀ σ : Equiv.Perm (Fin 3), Odd (orderOf σ) → σ ∈ alternatingGroup (Fin 3) := by
        intro σ hσ
        refine Equiv.Perm.mem_alternatingGroup.mpr ?_
        have hσ3 : σ ^ 3 = 1 := by
          refine eq_one_of_pow_coprime (m := 2) (n := orderOf σ) (perm3_cube_sq σ) ?_
            (Nat.coprime_two_left.mpr hσ)
          rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
        have h3 : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 → Equiv.Perm.sign τ = 1 := by decide
        exact h3 σ hσ3
      exact ⟨hc _ h1, hc _ h2⟩
    have h3 : ∀ τ : Equiv.Perm (Fin 3), Equiv.Perm.sign τ = 1 → τ ^ 3 = 1 := by decide
    intro q
    refine ⟨1, ?_⟩
    have hq : e q ∈ oTwoUpper (⊤ : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
      rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, oTwoUpper_map]
      exact ⟨q, q.2, rfl⟩
    obtain ⟨ha, hb⟩ := hA hq
    have h1 : e ((q : D) ^ 3) = 1 := by
      rw [map_pow]
      exact Prod.ext (by simpa using h3 _ (Equiv.Perm.mem_alternatingGroup.mp ha))
        (by simpa using h3 _ (Equiv.Perm.mem_alternatingGroup.mp hb))
    apply Subtype.ext
    simpa using (map_eq_one_iff e e.injective).mp h1
  ·
    have hE : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y ^ 2 ^ 1 = 1 := by
      decide
    have hle : oTwoUpper (⊤ : Subgroup D) ≤ φ.ker := by
      refine oTwoUpper_le_of_pow_mem fun x _ => ⟨1, ?_⟩
      rw [MonoidHom.mem_ker, map_pow]
      exact hE _
    intro q
    refine ⟨1, Subtype.ext ?_⟩
    have := hker.2.2 ⟨q, hle q.2⟩
    simpa using congrArg Subtype.val this

theorem card_map_of_A5 {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) (L' : Subgroup X) (φ : ↥L' →* alternatingGroup (Fin 5))
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.Open.pCore 2 ↥L') :
    ∃ b : ℕ, Nat.card ↥(L'.map (QuotientGroup.mk' N)) = 60 * 2 ^ b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : ↥L' →* X ⧸ N := (QuotientGroup.mk' N).comp L'.subtype with hf
  have hrange : f.range = L'.map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  set K := f.ker with hK
  have hKn : K.Normal := MonoidHom.normal_ker f
  have hK3 : Nat.Coprime 3 (Nat.card K) := by
    have hKN : K.map L'.subtype ≤ N := by
      rintro _ ⟨k, hk, rfl⟩
      have : (QuotientGroup.mk' N) (k : X) = 1 := hk
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have h1 : Nat.card ↥(K.map L'.subtype) = Nat.card K :=
      Subgroup.card_map_of_injective L'.subtype_injective
    rw [← h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKN) hN
  have hKO : K ≤ CFSG.Open.pCore 2 ↥L' := by
    rw [← hker]
    have hn : (K.map φ).Normal := hKn.map φ hφ
    rcases hn.eq_bot_or_eq_top with h | h
    · intro k hk
      have : φ k ∈ K.map φ := Subgroup.mem_map_of_mem φ hk
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        decide
      have h1 : Nat.card ↥(K.map φ) ∣ Nat.card K := K.card_map_dvd φ
      rw [h, Subgroup.card_top, h60] at h1
      have := Nat.Coprime.coprime_dvd_right h1 hK3
      norm_num at this
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L') 2).exists_card_eq
  have hL' : Nat.card ↥L' = 60 * 2 ^ a := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hker, ha] at h1
    rw [h1, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin,
      show Nat.factorial 5 / 2 = 60 by decide]
  obtain ⟨c, hc⟩ := ((CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L') 2).to_le hKO).exists_card_eq
  have hca : c ≤ a := by
    have h1 := Subgroup.card_dvd_of_le hKO
    rw [hc, ha] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hL', hc] at h2
  refine ⟨a - c, ?_⟩
  have h3 : (2 : ℕ) ^ a = 2 ^ (a - c) * 2 ^ c := by rw [← pow_add, Nat.sub_add_cancel hca]
  rw [h3, ← mul_assoc] at h2
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos two_pos c) h2).symm

@[expose] def dih12Cube : Subgroup (DihedralGroup 12) where
  carrier := {g | g ^ 3 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have h : ∀ a b : DihedralGroup 12, a ^ 3 = 1 → b ^ 3 = 1 → (a * b) ^ 3 = 1 := by decide
    exact h a b ha hb
  inv_mem' := by
    intro a ha
    show a⁻¹ ^ 3 = 1
    rw [inv_pow]
    have : a ^ 3 = 1 := ha
    rw [this, inv_one]

theorem oTwoUpper_dih12 : ∀ g ∈ oTwoUpper (⊤ : Subgroup (DihedralGroup 12)), g ^ 3 = 1 := by
  have hle : oTwoUpper (⊤ : Subgroup (DihedralGroup 12)) ≤ dih12Cube := by
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    show g ^ 3 = 1
    have h12 : ∀ g : DihedralGroup 12, g ^ 12 = 1 := by decide
    refine eq_one_of_pow_coprime (m := 4) (n := orderOf g) ?_ ?_ ?_
    · rw [← pow_mul]
      exact h12 g
    · rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    · exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hg.2)
  intro g hg
  exact hle hg

theorem mem_of_pow_three_of_mem_map {I : Type} [Group I] [Finite I]
    (hN3s : Group.IsSolvable ↥(CFSG.pPrimeCore 3 I)) {L' : Subgroup I}
    (hL' : L' ∈ cComp (⊤ : Subgroup I)) {k : I} {a : ℕ} (hka : k ^ 3 ^ a = 1)
    (hk : QuotientGroup.mk' (CFSG.pPrimeCore 3 I) k ∈
      L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 I))) : k ∈ L' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N3 := CFSG.pPrimeCore 3 I with hN3
  have hN3n : N3.Normal := inferInstance
  have hnorm : N3 ≤ Subgroup.normalizer (L' : Set I) := by
    have hLN3 : L' ≤ Subgroup.normalizer (N3 : Set I) :=
      le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hN3n).ge
    have h1 := (cComp_commutator_perfectCore hL' le_top hN3s hLN3).1
    intro n hn
    refine A4.mem_normalizer_of_conj_mem fun l hl => ?_
    have hc : ⁅n, l⁆ ∈ L' := by
      rw [← Subgroup.commutator_comm] at h1
      exact h1 (Subgroup.commutator_mem_commutator hn hl)
    have e : n * l * n⁻¹ = ⁅n, l⁆ * l := by rw [commutatorElement_def]; group
    rw [e]
    exact L'.mul_mem hc hl
  obtain ⟨l, hl, hlk⟩ := hk
  have hn : l⁻¹ * k ∈ N3 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hlk
    exact hlk
  set n := l⁻¹ * k with hndef
  have hkln : k = l * n := by rw [hndef]; group
  obtain ⟨l'', hl'', he⟩ := pow_mem_mul_of_normalizes hl (hnorm hn) (3 ^ a)
  rw [← hkln, hka] at he
  have hna : n ^ 3 ^ a ∈ L' := by
    have : n ^ 3 ^ a = l''⁻¹ := by
      have := congrArg (fun x => l''⁻¹ * x) he
      simpa using this.symm
    rw [this]
    exact L'.inv_mem hl''
  have hnL : n ∈ L' := by
    have hco : Nat.Coprime (3 ^ a) (orderOf n) := by
      have h1 : orderOf (⟨n, hn⟩ : ↥N3) ∣ Nat.card ↥N3 := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Nat.Coprime.pow_left a (Nat.Coprime.coprime_dvd_right h1 CFSG.pPrimeCore_coprime_card)
    exact (Subgroup.zpowers_le.mpr hna) (A4.mem_zpowers_pow_of_coprime hco)
  rw [hkln]
  exact L'.mul_mem hl hnL

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem L1T_le_normalizer_R1 : S.L1 ⊔ T ≤ Subgroup.normalizer (S.R1 : Set G) := by
  intro g hg
  refine A4.mem_normalizer_of_conj_mem fun r hr => ?_
  have hrT := S.R1_le_T hr
  have hgN := S.L1T_le_NV hg
  have hrN := S.frame.T_le hrT
  have hgrN : g * r * g⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hrN) (Subgroup.inv_mem _ hgN)
  have hgLT : g ∈ L ⊔ T := sup_le (S.L1_le_L.trans le_sup_left) le_sup_right hg
  have hgrLT : g * r * g⁻¹ ∈ L ⊔ T :=
    (L ⊔ T).mul_mem ((L ⊔ T).mul_mem hgLT (Subgroup.mem_sup_right hrT)) ((L ⊔ T).inv_mem hgLT)
  have hρ : InK4 (S.frame.ρ ⟨g * r * g⁻¹, hgrN⟩) := by
    have e : (⟨g * r * g⁻¹, hgrN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨g, hgN⟩ * ⟨r, hrN⟩ * (⟨g, hgN⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact InK4_conj_of_fix4 _ _ (S.rho_four_of_mem_L1T hg) ((S.mem_R1 hrT).1 hr)
  have hT := S.mem_T_of_InK4 ⟨_, hgrN⟩ hgrLT hρ
  exact (S.mem_R1 hT).2 hρ

theorem pCoreOf_H0_le_R1 {H : Subgroup G} (hTH : T ≤ H) {t : G} (ht : t ∈ T)
    (htN : t ∈ Subgroup.normalizer (V : Set G)) (hts : S.frame.ρ ⟨t, htN⟩ = Equiv.swap 0 1) :
    pCoreOf 2 (S.H0 H) ≤ S.R1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  have hO2T : pCoreOf 2 (S.H0 H) ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTI)
  have hO2G1 : pCoreOf 2 (S.H0 H) ≤ S.L1 ⊔ T := hO2T.trans le_sup_right
  have hG1I : S.L1 ⊔ T ≤ S.H0 H := sup_le (S.L1_le_borel_L.trans le_sup_left) hTI
  set P0 := (pCoreOf 2 (S.H0 H)).subgroupOf (S.L1 ⊔ T) with hP0
  have hP0n : P0.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hO2G1).mpr
    (hG1I.trans (le_normalizer_pCoreOf 2 _))
  have hs := S.phiL1T_surjective ht htN hts
  have hn : (P0.map S.phiL1T).Normal := hP0n.map _ hs
  have hp : IsPGroup 2 ↥(P0.map S.phiL1T) :=
    (A4.isPGroup_subgroupOf_of_le hO2G1 (pCoreOf_isPGroup 2 _)).map _
  have hbot := eq_bot_of_normal_isPGroup_perm3 hn hp
  intro x hx
  have hxT := hO2T hx
  have hxG1 : x ∈ S.L1 ⊔ T := hO2G1 hx
  have h1 : S.phiL1T ⟨x, hxG1⟩ = 1 := by
    have : S.phiL1T ⟨x, hxG1⟩ ∈ P0.map S.phiL1T :=
      Subgroup.mem_map_of_mem _ (show (⟨x, hxG1⟩ : ↥(S.L1 ⊔ T)) ∈ P0 from hx)
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  rw [phiL1T_apply, kappa_eq_one_iff _ (S.rho_four_of_mem_L1T hxG1)] at h1
  exact (S.mem_R1 hxT).2 h1

theorem mem_pCoreOf_H0_of_mem_pPrimeCore {H : Subgroup G} (hTH : T ≤ H)
    (htriple : F6.IsGoldschmidtTripleIn (S.H0 H) (S.L1 ⊔ T) H) {t : G} (ht : t ∈ T)
    (htI : t ∈ S.H0 H) (htN : (⟨t, htI⟩ : ↥(S.H0 H)) ∈ CFSG.pPrimeCore 3 ↥(S.H0 H)) :
    t ∈ pCoreOf 2 (S.H0 H) := by
  have hTI : T ≤ S.H0 H := hTH.trans le_sup_right
  have hsylO := htriple.isSylowTwoOf_pCore_pPrimeCore
  have hO2T : CFSG.Open.pCore 2 ↥(S.H0 H) ≤ T.subgroupOf (S.H0 H) := fun x hx =>
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTI) ⟨x, hx, rfl⟩
  have hmax := (A4.isSylowTwoOf_iff_maximal.mp hsylO).2.2
    ((T.subgroupOf (S.H0 H)) ⊓ CFSG.pPrimeCore 3 ↥(S.H0 H)) inf_le_right
    ((A4.isPGroup_subgroupOf_of_le hTI S.isPGroup_T).to_le inf_le_left) (le_inf hO2T hsylO.1)
  exact ⟨⟨t, htI⟩, hmax ⟨ht, htN⟩, rfl⟩

theorem false_of_caseOne (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) (hQ1 : pCoreOf 2 (S.G1bar H) = ⊥) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have htriple := S.triple_of h331 h1222 h5172 hH hHZ hsolv hS3 h3
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer h5172 hH hHZ)
  have hjT : j ∈ T := thompsonJ_le_self T hjJ
  set I := S.H0 H with hI
  set N3 := CFSG.pPrimeCore 3 ↥I with hN3
  set π := QuotientGroup.mk' N3 with hπ
  have hTI : T ≤ I := hTH.trans le_sup_right
  have hR1G1 : S.R1 ≤ S.L1 ⊔ T := S.R1_le_T.trans le_sup_right
  set R1b := (S.R1.subgroupOf I).map π with hR1b
  have hR1b_le : R1b ≤ S.G1bar H := Subgroup.map_mono (Subgroup.comap_mono hR1G1)
  have hG1R1b : S.G1bar H ≤ Subgroup.normalizer (R1b : Set (↥I ⧸ N3)) := by
    rintro _ ⟨g, hg, rfl⟩
    refine A4.mem_normalizer_of_conj_mem ?_
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨g * r * g⁻¹, ?_, by simp only [map_mul, map_inv]; rfl⟩
    show ((g * r * g⁻¹ : ↥I) : G) ∈ S.R1
    have := (Subgroup.mem_normalizer_iff.mp (S.L1T_le_normalizer_R1 hg) r).mp hr
    simpa using this
  have hR1b2 : IsPGroup 2 ↥R1b :=
    (A4.isPGroup_subgroupOf_of_le (S.R1_le_T.trans hTI) (S.isPGroup_T.to_le S.R1_le_T)).map _
  have hR1b_bot : R1b = ⊥ := by
    have := le_pCoreOf_of_le_normalizer hR1b_le hG1R1b hR1b2
    rw [hQ1] at this
    exact le_bot_iff.mp this
  have hR1O2 : S.R1 ≤ pCoreOf 2 I := by
    intro r hr
    have hrI : r ∈ I := hTI (S.R1_le_T hr)
    have hrN3 : (⟨r, hrI⟩ : ↥I) ∈ N3 := by
      have : π ⟨r, hrI⟩ ∈ R1b := ⟨⟨r, hrI⟩, hr, rfl⟩
      rw [hR1b_bot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    exact S.mem_pCoreOf_H0_of_mem_pPrimeCore hTH htriple (S.R1_le_T hr) hrI hrN3
  have heq : S.R1 = pCoreOf 2 I := le_antisymm hR1O2 (S.pCoreOf_H0_le_R1 hTH hjT hjN hj)
  obtain ⟨-, hJR1, -⟩ := S.lemma_13_2_4_one
  have hHN : H ≤ Subgroup.normalizer (S.R1 : Set G) := by
    rw [heq]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 I)
  have hNJ : Subgroup.normalizer (thompsonJ S.R1 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [hJR1]
    exact S.normalizer_thompsonJ_Q_le
  exact hH.2.1 ((hHN.trans (GammaExtra.normalizer_le_normalizer_thompsonJ _)).trans hNJ)

theorem P_le_R1_of_dihedral (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) (e : ↥(S.G2bar H) ≃* DihedralGroup 12) :
    pCoreOf 2 H ⊓ oTwoUpper H ≤ S.R1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have htriple := S.triple_of h331 h1222 h5172 hH hHZ hsolv hS3 h3
  obtain ⟨⟨j, hjJ, hjN, hj⟩, -⟩ :=
    S.lemma_13_2_4_two_b (S.thompsonJ_not_le_centralizer h5172 hH hHZ)
  have hjT : j ∈ T := thompsonJ_le_self T hjJ
  set I := S.H0 H with hI
  set N3 := CFSG.pPrimeCore 3 ↥I with hN3
  set π := QuotientGroup.mk' N3 with hπ
  have hHI : H ≤ I := le_sup_right
  set ψ : ↥H →* ↥(S.G2bar H) :=
    (π.comp (Subgroup.inclusion hHI)).codRestrict (S.G2bar H)
      (fun h => ⟨Subgroup.inclusion hHI h, h.2, rfl⟩) with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, ⟨g, hg, rfl⟩⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  intro x hx
  have hxT : x ∈ T := pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTH) hx.1
  have hxH : x ∈ H := hTH hxT
  have hxO : (⟨x, hxH⟩ : ↥H) ∈ oTwoUpper (⊤ : Subgroup ↥H) := by
    have h1 : x ∈ (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype := by
      rw [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hx.2
    obtain ⟨y, hy, hyx⟩ := h1
    have : y = ⟨x, hxH⟩ := Subtype.ext hyx
    rwa [this] at hy
  have hψO : ψ ⟨x, hxH⟩ ∈ oTwoUpper (⊤ : Subgroup ↥(S.G2bar H)) := by
    rw [← Subgroup.map_top_of_surjective ψ hψs, oTwoUpper_map]
    exact ⟨_, hxO, rfl⟩
  have heO : e (ψ ⟨x, hxH⟩) ∈ oTwoUpper (⊤ : Subgroup (DihedralGroup 12)) := by
    rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, oTwoUpper_map]
    exact ⟨_, hψO, rfl⟩
  have h3' : ψ ⟨x, hxH⟩ ^ 3 = 1 := by
    have h1 : e (ψ ⟨x, hxH⟩ ^ 3) = 1 := by rw [map_pow]; exact oTwoUpper_dih12 _ heO
    exact (map_eq_one_iff e e.injective).mp h1
  obtain ⟨b, hb⟩ := S.isPGroup_T ⟨x, hxT⟩
  have hb' : (⟨x, hxH⟩ : ↥H) ^ 2 ^ b = 1 := Subtype.ext (by simpa using congrArg Subtype.val hb)
  have h2' : ψ ⟨x, hxH⟩ ^ 2 ^ b = 1 := by rw [← map_pow, hb', map_one]
  have h1 : ψ ⟨x, hxH⟩ = 1 :=
    eq_one_of_pow_coprime h2' h3' (Nat.Coprime.pow_left b (by norm_num))
  have hxN3 : (⟨x, hHI hxH⟩ : ↥I) ∈ N3 := by
    have h2 : π ⟨x, hHI hxH⟩ = 1 := congrArg Subtype.val h1
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact S.pCoreOf_H0_le_R1 hTH hjT hjN hj
    (S.mem_pCoreOf_H0_of_mem_pPrimeCore hTH htriple hxT (hHI hxH) hxN3)

theorem false_of_caseThree_two (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) (h311 : Theorem311Stmt) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) (hcase : F6.IsF618CaseThree (S.G2bar H) (S.G1bar H)) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨e⟩, -, -⟩ := hcase
  exact S.false_of_P_le_R1 h331 h311 hH hHZ hsolv hS3
    (S.P_le_R1_of_dihedral h331 h1222 h5172 hH hHZ hsolv hS3 h3 e)

theorem card_image_of_comm_ne {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥)
    {L' : Subgroup ↥(S.H0 H)} (hL' : L' ∈ cComp (⊤ : Subgroup ↥(S.H0 H)))
    (hZL : ⁅quasithinOmegaOneCenter T, L'.map (S.H0 H).subtype⁆ ≠ ⊥) :
    ∃ b : ℕ, Nat.card ↥(L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) = 60 * 2 ^ b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTI : T ≤ S.H0 H := hH.1.1.trans le_sup_right
  have hsylI : IsSylowTwoOf T (S.H0 H) := isSylowTwoOf_of_le S.h13.sylow hTI
  have hL₀c : L'.map (S.H0 H).subtype ∈ cComp (S.H0 H) := map_subtype_mem_cComp hL'
  have hloc : quasithinIsLocal T (L'.map (S.H0 H).subtype) :=
    isLocal_of_mem_cComp_of_sylow hsylI hO2 hL₀c
  have hf := Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hloc hZL
  obtain ⟨φ, hφ, hker⟩ := S.h13.a5 S.a5 _ hf
  set e : ↥L' ≃* ↥(L'.map (S.H0 H).subtype) :=
    L'.equivMapOfInjective (S.H0 H).subtype (S.H0 H).subtype_injective with he
  have hker' : (φ.comp e.toMonoidHom).ker = CFSG.Open.pCore 2 ↥L' := by
    rw [← MonoidHom.comap_ker, hker, Subgroup.comap_equiv_eq_map_symm']
    exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e.symm
  exact card_map_of_A5 _ CFSG.pPrimeCore_coprime_card L' (φ.comp e.toMonoidHom)
    (hφ.comp e.surjective) hker'

theorem oTwoUpper_le_of_le_image (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h5172 : Stmt5_1_7_two) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (h3 : ¬ ThreeTop (S.H0 H)) {L' : Subgroup ↥(S.H0 H)}
    (hL' : L' ∈ cComp (⊤ : Subgroup ↥(S.H0 H)))
    (himg : oTwoUpper (⊤ : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H))) ≤
      L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)))) :
    oTwoUpper H ≤ L'.map (S.H0 H).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htriple := S.triple_of h331 h1222 h5172 hH hHZ hsolv hS3 h3
  have hpow3 := S.pow_three_pow_mem h331 hH hHZ hsolv hS3
  refine (Subgroup.closure_le _).mpr ?_
  rintro k ⟨hkH, hko⟩
  have hkI : k ∈ S.H0 H := Subgroup.mem_sup_right hkH
  obtain ⟨a, ha⟩ := hpow3 k (mem_oTwoUpper_of_odd hkH hko)
  have hka : k ^ 3 ^ a = 1 := by
    obtain ⟨c, hc⟩ := pCoreOf_isPGroup 2 H ⟨_, ha⟩
    have hc' : (k ^ 3 ^ a) ^ 2 ^ c = 1 := by simpa using congrArg Subtype.val hc
    have hco : (k ^ 3 ^ a) ^ orderOf k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    exact eq_one_of_pow_coprime hc' hco (Nat.Coprime.pow_left c (Nat.coprime_two_left.mpr hko))
  have hk'a : (⟨k, hkI⟩ : ↥(S.H0 H)) ^ 3 ^ a = 1 := Subtype.ext (by simpa using hka)
  have hπk : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H)) ⟨k, hkI⟩ ∈
      L'.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))) := by
    refine himg (mem_oTwoUpper_of_odd (Subgroup.mem_top _) ?_)
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(S.H0 H))) ⟨k, hkI⟩
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hko h1
  exact ⟨⟨k, hkI⟩, mem_of_pow_three_of_mem_map htriple.isSolvable_pPrimeCore hL' hk'a hπk, rfl⟩

theorem false_of_caseBig (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) ≠ ⊥) (h3 : ¬ ThreeTop (S.H0 H))
    (hq : CFSG.IsQuasisimple ↥(oTwoUpper
      (⊤ : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H)))))
    (hcard : ∀ b : ℕ, Nat.card ↥(oTwoUpper
      (⊤ : Subgroup (↥(S.H0 H) ⧸ CFSG.pPrimeCore 3 ↥(S.H0 H)))) ≠ 60 * 2 ^ b) : False := by
  have htriple := S.triple_of h331 h1222 h5172 hH hHZ hsolv hS3 h3
  set I := S.H0 H with hI
  set N3 := CFSG.pPrimeCore 3 ↥I with hN3
  set π := QuotientGroup.mk' N3 with hπ
  set Kb := oTwoUpper (⊤ : Subgroup (↥I ⧸ N3)) with hKb
  have hKbn : Kb.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_oTwoUpper ⊤))
  have hKbc : Kb ∈ cComp (⊤ : Subgroup (↥I ⧸ N3)) :=
    mem_cComp_top_of_isComponent ⟨hq, hKbn.isSubnormal⟩
  obtain ⟨L', hL', hL'K⟩ := (cComp_quotient_bijOn N3 htriple.isSolvable_pPrimeCore).2.2 hKbc
  have hZL : ⁅quasithinOmegaOneCenter T, L'.map I.subtype⁆ = ⊥ := by
    by_contra hne
    obtain ⟨b, hb⟩ := S.card_image_of_comm_ne hH hO2 hL' hne
    rw [hL'K] at hb
    exact hcard b hb
  have hLH := S.oTwoUpper_le_of_le_image h331 h1222 h5172 hH hHZ hsolv hS3 h3 hL' hL'K.ge
  apply hHZ
  rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_le S.h13.sylow hH.1.1)]
  refine sup_le ?_ (T_le_centralizer_omegaOneCenter T)
  refine hLH.trans ?_
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZL)

end Setting

theorem final1327_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h5172 : Stmt5_1_7_two) (h311 : Theorem311Stmt) (hF618 : F6.TheoremF618Cat)
    (hBig : FactF618Big) (hThree : Final1327CaseThree) : Final1327 := by
  intro G _ _ T L V S H hH hHZ hsolv hS3 hO2 h3
  obtain ⟨hAm, hconc⟩ := S.f618_of h331 h1222 h5172 hF618 hH hHZ hsolv hS3 hO2 h3
  have hAm' : IsGoldschmidtAmalgam (S.G2bar H) (S.G1bar H) :=
    { toIsGoldschmidtTriple := hAm.toIsGoldschmidtTriple.symm
      pCore_eq_bot := hAm.pCore_eq_bot }
  rcases hconc with h | h
  · rcases h with h1 | h2 | h3' | hrest
    · exact S.false_of_caseOne h331 h1222 h5172 hH hHZ hsolv hS3 h3 h1.2.1
    · exact h3 (isPGroup_oTwoUpper_of_caseTwo h2)
    · exact hThree G T L V S H hH hHZ hsolv hS3 hO2 h3 h3'
    · obtain ⟨hq, hc⟩ := hBig _ _ _ hAm hrest
      exact S.false_of_caseBig h331 h1222 h5172 hH hHZ hsolv hS3 hO2 h3 hq hc
  · rcases h with h1 | h2 | h3' | hrest
    · exact S.false_of_caseOne h331 h1222 h5172 hH hHZ hsolv hS3 h3 h1.2.2.1
    · exact h3 (isPGroup_oTwoUpper_of_caseTwo h2)
    · exact S.false_of_caseThree_two h331 h1222 h5172 h311 hH hHZ hsolv hS3 h3 h3'
    · obtain ⟨hq, hc⟩ := hBig _ _ _ hAm' hrest
      exact S.false_of_caseBig h331 h1222 h5172 hH hHZ hsolv hS3 hO2 h3 hq hc

end CFSG.Quasithin.H13.A5
