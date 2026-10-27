module

public import CFSG.Quasithin.Vol2.Ch11SecDO22
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.A4Local
public import CFSG.Quasithin.Vol2.Ch11SecB23Two
public import CFSG.Quasithin.Vol2.Ch11SecDSetup
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem mem_of_pow_mem_of_coprime {H : Subgroup G} {y : G} {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : y ^ a ∈ H) (hb : y ^ b ∈ H) : y ∈ H := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hy : y = (y ^ a) ^ (Nat.gcdA a b) * (y ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast y a, ← zpow_natCast y b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h,
      zpow_one]
  rw [hy]
  exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)

theorem mem_of_odd_two {H : Subgroup G} {y : G} (hy : orderOf y ≠ 0)
    (hodd : ∀ m : ℕ, Odd (orderOf (y ^ m)) → y ^ m ∈ H)
    (htwo : ∀ m k : ℕ, (y ^ m) ^ 2 ^ k = 1 → y ^ m ∈ H) : y ∈ H := by
  obtain ⟨e, o, ho, hord⟩ := Nat.exists_eq_two_pow_mul_odd hy
  have h1 : y ^ 2 ^ e ∈ H := by
    apply hodd
    have hd : orderOf (y ^ 2 ^ e) ∣ o :=
      orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, ← hord, pow_orderOf_eq_one])
    exact ho.of_dvd_nat hd
  have h2 : y ^ o ∈ H := htwo o e (by rw [← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one])
  exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr ho)) h1 h2

variable [Finite G]

theorem noncentral_oTwoUpper_oTwoTwoPrime (K : Subgroup G) :
    NoncentralTwoChiefFactorsInO2 (oTwoUpper (oTwoTwoPrime K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := oTwoUpper (oTwoTwoPrime K) with hX
  intro A B hAB
  exfalso
  obtain ⟨hOB, hBA, hAX, -, -, -, h2⟩ := hAB
  have hXK : X ≤ K := (oTwoUpper_le _).trans (SecD.oTwoTwoPrime_le K)
  have hPX : pCoreOf 2 K ⊓ X ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun x hx => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
    exact SecD.mem_normalizer_inf
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (hXK hx)) (Subgroup.le_normalizer hx)
  have htwoB : ∀ x ∈ X, ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ B := fun x hx k hk =>
    hOB (hPX ⟨SecD.mem_pCoreOf_of_mem_oTwoTwoPrime (oTwoUpper_le _ hx) hk, hx⟩)
  apply (lt_iff_le_not_ge.mp hBA).2
  intro a ha
  have haX := hAX ha
  obtain ⟨k, hk⟩ := h2 a ha
  apply mem_of_odd_two (orderOf_pos a).ne'
  · intro m hm
    have hmem : (a ^ m) ^ 2 ^ k ∈ B := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact B.pow_mem hk m
    have hcop : Nat.Coprime (2 ^ k) (orderOf (a ^ m)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
    exact (Subgroup.zpowers_le.mpr hmem) (A4.mem_zpowers_pow_of_coprime hcop)
  · intro m j hj
    exact htwoB _ (X.pow_mem haX m) j hj

variable {T L I : Subgroup G} {n : ℕ}

theorem pCoreOf_le_rOf (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K) :
    pCoreOf 2 (K ⊔ T) ≤ ROf T L V₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (le_sup_right : T ≤ K ⊔ T)
  exact CFSG.Quasithin.pCoreOf_le_pCoreOf_of_sylow (sup_le_sup_right hLK T) hsyl.2.1
    le_sup_right hsyl.2.2

theorem le_omegaOneCenterOf (hP : SecB.PointFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {V₁ K : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hLK : LOf L V₁ ≤ K)
    (hO : pCoreOf 2 (K ⊔ T) ≠ ⊥) :
    V₁ ≤ omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hchar : QuasithinUnique.CharTwo (K ⊔ T) :=
    charTwo_of_inH h.fsu.qtke.2.1 S ⟨hS ▸ le_sup_right, hO⟩
  have hOC : pCoreOf 2 (K ⊔ T) ≤ Subgroup.centralizer (V₁ : Set G) :=
    (pCoreOf_le_rOf h hLK).trans (SecB.rOf_le_centralizer hP h1102 h hV₁)
  intro v hv
  have hvV := SecA.IsVi.le_fsuV hV₁ hv
  have hvC : v ∈ Subgroup.centralizer (pCoreOf 2 (K ⊔ T) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun o ho =>
      ((Subgroup.mem_centralizer_iff.mp (hOC ho)) v hv).symm
  have hvO : v ∈ pCoreOf 2 (K ⊔ T) :=
    hchar ⟨Subgroup.mem_sup_right (SecA.fsuV_le_T h hvV), hvC⟩
  exact Subgroup.subset_closure ⟨⟨hvO, hvC⟩, (SecA.isElemAbelian_fsuV h).2 v hvV⟩

theorem oTwoTwoPrime_le_centralizer (h3214 : TmpL6_3_2_14) (hP : SecB.PointFacts)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hloc : quasithinIsLocal T K) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K) (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    oTwoTwoPrime K ≤ Subgroup.centralizer (V₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := oTwoTwoPrime K with hY
  set X := oTwoUpper Y with hX
  have hO : pCoreOf 2 (K ⊔ T) ≠ ⊥ := hloc.2.2.2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hchar : QuasithinUnique.CharTwo (K ⊔ T) :=
    charTwo_of_inH h.fsu.qtke.2.1 S ⟨hS ▸ le_sup_right, hO⟩
  have hR := h3214 G T K h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow hloc hnq
  have hYK : Y ≤ K := SecD.oTwoTwoPrime_le K
  have hKY : K ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.le_normalizer.trans (SecD.normalizer_le_normalizer_oTwoTwoPrime K)
  have hYs : Y ≤ solvRad K := le_solvRad hYK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hKY) (SecD.isSolvable_oTwoTwoPrime K)
  have hXY : X ≤ Y := oTwoUpper_le Y
  have hKM : K ≤ K ⊔ T := le_sup_left
  have hMK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hXsub : IsSubnormal X (K ⊔ T) :=
    IsSubnormal.step hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr
      (le_normalizer_oTwoUpper Y)) (IsSubnormal.step hYK
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hKY)
        (A3.subnormal_of_normal hKM
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMK)))
  have hXR : ⁅twoReducedJoin (K ⊔ T), X⁆ = ⊥ := by
    rw [← primeReducedAggregate_map_subtype_eq_twoReducedJoin,
      Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
    exact (hXY.trans hYs).trans hR
  have htfae := a4_11 hchar (A4.oTwoUpper_oTwoUpper Y).symm hXsub
    (noncentral_oTwoUpper_oTwoTwoPrime K)
  have h13 : IsXf X ↔ ⁅twoReducedJoin (K ⊔ T), X⁆ ≠ ⊥ := htfae.out 1 3
  have hnXf : ¬ IsXf X := fun hXf => h13.mp hXf hXR
  have hXC : X ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ T)) : Set G) := by
    by_cases hX1 : X = ⊥
    · rw [hX1]
      exact bot_le
    have hXc : IsXClass X :=
      ⟨hX1, (A4.oTwoUpper_oTwoUpper Y).symm, A4.charTwo_of_subnormal hXsub hchar⟩
    have hVY : VY X = ⊥ := by
      by_contra hne
      exact hnXf ⟨hXc, hne⟩
    have hb : ¬ ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ T)), X⁆ ≠ ⊥ := fun hne =>
      ((a4_9 hXc hXsub).mp hne) hVY
    rw [not_not, Subgroup.commutator_eq_bot_iff_le_centralizer] at hb
    exact Subgroup.le_centralizer_iff.mp hb
  have hV := le_omegaOneCenterOf hP h1102 h hV₁ hLK hO
  have hOKM : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM)
      (hMK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  intro y hy
  apply mem_of_odd_two (orderOf_pos y).ne'
  · intro m hm
    exact Subgroup.centralizer_le hV (hXC (mem_oTwoUpper_of_odd (Y.pow_mem hy m) hm))
  · intro m k hk
    exact ((pCoreOf_le_rOf h hLK).trans (SecB.rOf_le_centralizer hP h1102 h hV₁))
      (hOKM (SecD.mem_pCoreOf_of_mem_oTwoTwoPrime (Y.pow_mem hy m) hk))

end CFSG.Quasithin.Vol2.Ch11.SecE
