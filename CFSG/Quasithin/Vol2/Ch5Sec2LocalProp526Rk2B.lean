module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2A
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526SndA
public import CFSG.Quasithin.H13.NQCatL2LieParabolic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

namespace Sec526

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normalizes {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have : (B.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  have : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e : B.relIndex (A ⊔ B) = B.relIndex A :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B h).toEquiv.symm
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_eq_left.mpr (le_sup_right : B ≤ A ⊔ B), e] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_eq_of_isSylowTwoOf {S H : Subgroup G} (h : IsSylowTwoOf S H) :
    Nat.card S = 2 ^ (Nat.card H).factorization 2 := by
  have h1 := card_eq_two_pow_of_odd_index (T := S.subgroupOf H)
    (h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm) h.2.2
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv] at h1

theorem factorization_two_card_eq {X : Type*} [Group X] [Finite X] (N : Subgroup X) :
    (Nat.card X).factorization 2 = (Nat.card N).factorization 2 +
      (Nat.card (X ⧸ N)).factorization 2 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, add_comm]

theorem card_eq_two_pow_factorization {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X) :
    Nat.card X = 2 ^ (Nat.card X).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  rw [hk, Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem factorization_two_card_SL3 {F : Type} [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k)
    (hF : Nat.card F = 2 ^ k) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 3) F)).factorization 2 = 3 * k := by
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 2 ^ k := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field, hq, Fin.prod_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  set q := 2 ^ k with hqdef
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ q := Nat.pow_le_pow_right (by norm_num) hk
  have h1 : 1 ≤ q := by omega
  have hq3 : q ≤ q ^ 3 := Nat.le_self_pow (by norm_num) q
  have hq23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hqq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hprod : (q ^ 3 - 1) * (q ^ 3 - q) * (q ^ 3 - q ^ 2) =
      (q - 1) * (q ^ 3 * ((q ^ 3 - 1) * (q ^ 2 - 1))) := by
    zify [hq3, hq23, hqq2, hqq3, h1]
    ring
  rw [hprod, Nat.mul_div_cancel_left _ (by omega)]
  have hodd : ¬ 2 ∣ (q ^ 3 - 1) * (q ^ 2 - 1) := by
    have h2 : 2 ∣ q := dvd_pow_self 2 (by omega)
    rw [Nat.Prime.dvd_mul Nat.prime_two]
    rintro (h | h)
    · have : 2 ∣ q ^ 3 := h2.trans (dvd_pow_self q (by norm_num))
      omega
    · have : 2 ∣ q ^ 2 := h2.trans (dvd_pow_self q (by norm_num))
      omega
  have hne : (q ^ 3 - 1) * (q ^ 2 - 1) ≠ 0 := by
    intro h
    apply hodd
    rw [h]
    exact dvd_zero 2
  rw [Nat.factorization_mul (pow_ne_zero _ (by omega)) hne,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, hqdef, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [mul_comm]

theorem factorization_two_of_rank2
    {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k) :
    (IsSL3Ch5 k X → (Nat.card X).factorization 2 = 3 * k) ∧
      (LieModel X .PSp 2 2 k → (Nat.card X).factorization 2 = 4 * k) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | ⟨F, _, _, hF, ⟨e⟩⟩
    · have hadm := adm_psl3 (f := k) (by omega)
      rw [(factorization_of_lieModel hadm h).2]
      simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
    · rw [Nat.card_congr e.toEquiv]
      exact factorization_two_card_SL3 (by omega) hF
  · have hadm := adm_psp2 (f := k) hk
    rw [(factorization_of_lieModel hadm h).2]
    simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]

theorem rank2_facts
    (h510 : Stmt5_1_10) {T M L V H B D L₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hK : quasithinIsCComponent (oTwoUpper H) H)
    (hnb : ¬ IsBenderAny (O2Q (oTwoUpper H))) {P : Subgroup G}
    (hP : IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P)
    (hL₂ : quasithinIsCComponent L₂ P) :
    ∃ k : ℕ, 2 ≤ k ∧
      (IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
      IsPSL 2 2 k (ModO2 L₂) ∧ IsL2Quot k (oTwoQuot ↥L₂) ∧ ⁅L₂, L₂⁆ = L₂ ∧
      L₂ ≤ Subgroup.normalizer ((pCoreOf 2 (oTwoUpper H) ⊓ L₂ : Subgroup G) : Set G) ∧
      pCoreOf 2 (oTwoUpper H) ⊓ L₂ ≤ pCoreOf 2 L₂ ∧
      ⁅pCoreOf 2 (oTwoUpper H) ⊓ L₂, L₂⁆ ≠ ⊥ ∧
      Nat.card ↥(pCoreOf 2 (oTwoUpper H) ⊓ L₂) *
          2 ^ (Nat.card (O2Q (oTwoUpper H))).factorization 2 =
        Nat.card ↥(pCoreOf 2 L₂) * 2 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  set K := oTwoUpper H with hKdef
  set R := pCoreOf 2 K with hRdef
  obtain ⟨k, hk, htype, -, hMK⟩ := nonBender_type h510 hyp.toHyp5_1_8 hN hK hnb rfl
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
  have hF := NQCat.factL2LieParabolic_holds
  obtain ⟨hL₂eq, hpsl, -, -⟩ := l2Lie_nonBender hF hk htype hTK hMK hP hL₂
  obtain ⟨Pj, hPj, hj, -⟩ := exists_parabolics hF hk htype hTK
  have hOS : R ≤ T ⊓ K := F7.isSylowTwoOf_pCoreOf_le hTK
  obtain ⟨j, hPeq⟩ := hPj P hP
  have hPK : P ≤ K := hP.1
  have hcore : modO2Image K (perfectCore P) = perfectCore (Pj j) := by
    rw [modO2Image_perfectCore hPK, hPeq]
  obtain ⟨-, -, hTKL⟩ := eq_perfectCore_of_isPSL hTK hP hL₂
    (by rw [hcore]; exact (hj j).2.1) (by rw [hcore]; exact (hj j).2.2)
  have hL₂K : L₂ ≤ K := hL₂eq ▸ (perfectCore_le P).trans hPK
  have hRN : R ≤ Subgroup.normalizer (L₂ : Set G) := by
    rw [hL₂eq]
    exact (hP.pCoreOf_le hTK.1 hOS).trans
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P))
  have hTKeq : T ⊓ K = R ⊔ (T ⊓ L₂) := by
    have h1 := A3.eq_sup_inf_of_le_sup hRN hOS (by rw [sup_comm]; exact hTKL)
    rw [inf_assoc, inf_eq_right.mpr hL₂K] at h1
    exact h1
  have hperf : ⁅L₂, L₂⁆ = L₂ := hL₂.2.1
  have hL₂q : IsL2Quot k (oTwoQuot ↥L₂) :=
    isL2Quot_oTwoQuot_of_lieModel (by omega) (Or.inl ⟨by decide, hpsl⟩)
  have hL₂NR : L₂ ≤ Subgroup.normalizer (R : Set G) :=
    hL₂K.trans (le_normalizer_pCoreOf 2 K)
  have hL₂NR₀ : L₂ ≤ Subgroup.normalizer ((R ⊓ L₂ : Subgroup G) : Set G) :=
    le_inf hL₂NR Subgroup.le_normalizer |>.trans (Subgroup.inf_normalizer_le_normalizer_inf)
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 K
  have hR₀Q : R ⊓ L₂ ≤ pCoreOf 2 L₂ :=
    le_pCoreOf 2 inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hL₂NR₀)
      (hR2.to_le inf_le_left)
  have hcharK : CharTwo K :=
    CharTwo.of_normal (charTwo_of_inH' h.qtke h.sylow hyp.hStar.1) (oTwoUpper_le H)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr
        (le_normalizer_oTwoUpper H))
  have hRL : ⁅R, L₂⁆ ≠ ⊥ := by
    intro h0
    have hLC : L₂ ≤ Subgroup.centralizer (R : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact h0
    have hLR : L₂ ≤ R := (le_inf hL₂K hLC).trans hcharK
    have : Group.IsNilpotent ↥L₂ := (hR2.to_le hLR).isNilpotent
    exact not_isSolvable_of_perfect hperf hL₂.1 inferInstance
  have hRLle : ⁅R, L₂⁆ ≤ R ⊓ L₂ := by
    refine le_inf (F112W.commutator_le_self_of_le_normalizer hL₂NR) ?_
    rw [Subgroup.commutator_comm]
    exact F112W.commutator_le_self_of_le_normalizer hRN
  have hR₀L : ⁅R ⊓ L₂, L₂⁆ ≠ ⊥ := by
    intro h0
    apply hRL
    refine commutator_eq_bot_of_perfect hperf (eq_bot_iff.mpr ?_)
    rw [← h0]
    exact Subgroup.commutator_mono hRLle le_rfl
  have hPN : P ≤ Subgroup.normalizer (L₂ : Set G) := by
    rw [hL₂eq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P)
  have hTKP' : T ⊓ K ≤ P := (le_inf hTK.1 Subgroup.le_normalizer).trans hP.2.1
  have hTKP : IsSylowTwoOf (T ⊓ K) P := by
    refine ⟨hTKP', hTK.2.1, fun h2 => hTK.2.2 (h2.trans ?_)⟩
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex (T ⊓ K) P K hTKP' hPK)
  have hTL : IsSylowTwoOf (T ⊓ L₂) L₂ := by
    have h1 := A4.isSylowTwoOf_inf_normal hTKP (hL₂eq ▸ perfectCore_le P) hPN
    rwa [inf_assoc, inf_eq_right.mpr hL₂K] at h1
  have hcL : Nat.card ↥(T ⊓ L₂) = Nat.card ↥(pCoreOf 2 L₂) * 2 ^ k := by
    rw [card_eq_of_isSylowTwoOf hTL, factorization_two_card_eq (Open.pCore 2 ↥L₂),
      hL₂q.card (by omega), pow_add]
    have hQ : Nat.card ↥(Open.pCore 2 ↥L₂) = Nat.card ↥(pCoreOf 2 L₂) :=
      Nat.card_congr ((Open.pCore 2 ↥L₂).equivMapOfInjective L₂.subtype
        L₂.subtype_injective).toEquiv
    rw [← hQ, ← card_eq_two_pow_factorization
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L₂) 2)]
    congr 1
    have hodd : ¬ 2 ∣ 4 ^ k - 1 := by
      have : 2 ∣ 4 ^ k := dvd_pow (by norm_num : 2 ∣ 4) (by omega)
      have h1 : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
      omega
    have hne : 4 ^ k - 1 ≠ 0 := by
      intro h0
      apply hodd
      rw [h0]
      exact dvd_zero 2
    rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hne,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hcK : Nat.card ↥(T ⊓ K) =
      Nat.card ↥R * 2 ^ (Nat.card (O2Q K)).factorization 2 := by
    rw [card_eq_of_isSylowTwoOf hTK, factorization_two_card_eq (CFSG.pCore 2 ↥K), pow_add]
    have hQ : Nat.card ↥(CFSG.pCore 2 ↥K) = Nat.card ↥R := by
      exact Nat.card_congr ((Open.pCore 2 ↥K).equivMapOfInjective K.subtype
        K.subtype_injective).toEquiv
    have hp : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := by
      exact CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) 2
    rw [← hQ, ← card_eq_two_pow_factorization hp]
  have hprod := card_sup_mul_card_inf_of_normalizes (A := T ⊓ L₂) (B := R)
    ((inf_le_right.trans hL₂K).trans (le_normalizer_pCoreOf 2 K))
  have hinf : T ⊓ L₂ ⊓ R = R ⊓ L₂ := by
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr (hOS.trans inf_le_left)]
  rw [sup_comm, ← hTKeq, hinf, hcK, hcL] at hprod
  refine ⟨k, hk, htype, hpsl, hL₂q, hperf, hL₂NR₀, hR₀Q, hR₀L, ?_⟩
  have hRpos : 0 < Nat.card ↥R := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hRpos
  calc Nat.card ↥R * (Nat.card ↥(R ⊓ L₂) * 2 ^ (Nat.card (O2Q K)).factorization 2)
      = Nat.card ↥R * 2 ^ (Nat.card (O2Q K)).factorization 2 * Nat.card ↥(R ⊓ L₂) := by ring
    _ = Nat.card ↥(pCoreOf 2 L₂) * 2 ^ k * Nat.card ↥R := hprod
    _ = Nat.card ↥R * (Nat.card ↥(pCoreOf 2 L₂) * 2 ^ k) := by ring

end Sec526

end CFSG.Quasithin.H13
