module

public import CFSG.Quasithin.Recognition.Stroth.BenderH7
public import CFSG.Quasithin.Recognition.Stroth.BenderSylow
public import CFSG.Quasithin.Recognition.St84.Gen.S3Slice

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem eq_or_eq_sup_of_normal_of_isL2Quot {L1 L2 S K : Subgroup G} (hF : F112HypW L1 L2 S)
    {n : ℕ} (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hK : K ≤ L2 ⊔ Q2 L1 L2 S)
    (hKn : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (K : Set G))
    (hQK : Q2 L1 L2 S ≤ K) :
    K = Q2 L1 L2 S ∨ K = L2 ⊔ Q2 L1 L2 S := by
  classical
  set H : Subgroup G := L2 ⊔ Q2 L1 L2 S with hH
  set Q : Subgroup G := Q2 L1 L2 S with hQ
  have hQH : Q ≤ H := by
    rw [hH]
    exact le_sup_right
  have hHleP2 : H ≤ P2 L1 L2 S := by
    rw [hH, hQ]
    exact sup_le le_sup_left (pCoreOf_le 2 (P2 L1 L2 S))
  have hQN : H ≤ Subgroup.normalizer (Q : Set G) :=
    hHleP2.trans (by
      rw [hQ]
      exact le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hQNsub : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hQN
  have hpQ : pCoreOf 2 H = Q := by
    rw [hH, hQ]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hcore : pCore 2 ↥H = Q.subgroupOf H := by
    ext x
    rw [F1.mem_pCore_iff_coe, hpQ]
    rfl
  let π : ↥H →* ↥H ⧸ Q.subgroupOf H := QuotientGroup.mk' (Q.subgroupOf H)
  let eH : oTwoQuot ↥H ≃* oTwoQuot ↥L2 := by
    have h := oTwoQuotSupEquiv (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    have hH' : H = L2 ⊔ Q1 L2 L1 S := by
      simp [H, Q1, Q2, P1, P2, bigB_comm]
    rw [hH']
    exact h
  obtain ⟨eL⟩ := hL2
  have hcard : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard
  haveI : IsSimpleGroup (oTwoQuot ↥L2) := eL.isSimpleGroup
  have eQ : (↥H ⧸ Q.subgroupOf H) ≃* oTwoQuot ↥H :=
    QuotientGroup.quotientMulEquivOfEq hcore.symm
  haveI : IsSimpleGroup (↥H ⧸ Q.subgroupOf H) := (eQ.trans eH).isSimpleGroup
  have hKnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK).mpr hKn
  have hmapN : ((K.subgroupOf H).map π).Normal :=
    hKnorm.map π (QuotientGroup.mk'_surjective (Q.subgroupOf H))
  rcases (haveI := hmapN;
    IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K.subgroupOf H).map π)) with hbot | htop
  · left
    refine le_antisymm ?_ hQK
    intro k hk
    have hkH : k ∈ H := hK hk
    have hmem : π ⟨k, hkH⟩ ∈ (K.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk)
    rw [hbot, Subgroup.mem_bot] at hmem
    have : (⟨k, hkH⟩ : ↥H) ∈ Q.subgroupOf H :=
      (QuotientGroup.eq_one_iff _).mp hmem
    exact Subgroup.mem_subgroupOf.mp this
  · right
    refine le_antisymm hK ?_
    intro h hh
    have hmem : π ⟨h, hh⟩ ∈ (K.subgroupOf H).map π := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hmem
    have hkK' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hkK
    have hdiff : (k : G)⁻¹ * h ∈ Q := by
      have hq : π (k⁻¹ * (⟨h, hh⟩ : ↥H)) = 1 := by
        rw [map_mul, map_inv, hkx, inv_mul_cancel]
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hq)
    have heq : h = (k : G) * ((k : G)⁻¹ * h) := by group
    rw [heq]
    exact K.mul_mem hkK' (hQK hdiff)

theorem inf_centralizer_le_omegaOneCenterOf_of_eq {L1 L2 S : Subgroup G}
    (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S) :
    Z2 L1 L2 S ⊓
      Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) ≤
        omegaOneCenterOf S := by
  intro y hy
  have hyZ2 : y ∈ Z2 L1 L2 S := (Subgroup.mem_inf.mp hy).1
  have hyCent : y ∈ Subgroup.centralizer
      ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := (Subgroup.mem_inf.mp hy).2
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hS2le : S ≤ L2 ⊔ Q2 L1 L2 S := by
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
      _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hyS : y ∈ S := hQ2S ((omegaOneCenterOf_le (Q2 L1 L2 S)) hyZ2)
  have hyCentS : y ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hyCent ⊢
    intro s hs
    exact hyCent s (hS2le hs)
  have hy2 : y ^ 2 = 1 :=
    (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 y hyZ2
  exact Subgroup.subset_closure ⟨Subgroup.mem_inf.mpr ⟨hyS, hyCentS⟩, hy2⟩

theorem z2_inf_centralizer_eq_bot_of_caseI
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S)
    (hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S)
    (hZ1 : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z2 L1 L2 S ⊓
      Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) = ⊥ := by
  set Y : Subgroup G :=
    Z2 L1 L2 S ⊓
      Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) with hY
  have hSle1 : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hS1
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hZ1eq : Z1 L1 L2 S = omegaOneCenterOf S :=
    omegaOneCenterOf_pCoreOf_eq hF.1 hSle1 hZ1
  have hYleZ : Y ≤ omegaOneCenterOf S := by
    rw [hY]
    exact inf_centralizer_le_omegaOneCenterOf_of_eq hS2
  have hYleS : Y ≤ S := hYleZ.trans (omegaOneCenterOf_le S)
  have hY2 : IsPGroup 2 Y := hF.1.h1.pgroup.to_le hYleS
  have hYZ1 : Y ≤ Z1 L1 L2 S := by
    rw [hZ1eq]
    exact hYleZ
  have hCY : Subgroup.centralizer (Z1 L1 L2 S : Set G) ≤
      Subgroup.normalizer (Y : Set G) :=
    (Subgroup.centralizer_le hYZ1).trans (Subgroup.centralizer_le_normalizer (Y : Set G))
  have hL1NY : L1 ≤ Subgroup.normalizer (Y : Set G) :=
    ((le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S).trans hZ1).trans hCY
  have hSNY : S ≤ Subgroup.normalizer (Y : Set G) :=
    (hSle1.trans hZ1).trans hCY
  have hBL2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    have := bigB_le_normalizer_of_hyp111 hF.1.symm
    rwa [bigB_comm] at this
  have hP2L2 : P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer hBL2
  have hP2Q2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hP2L2Q2 : P2 L1 L2 S ≤
      Subgroup.normalizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hP2L2 hP2Q2
  have hP2Z2 : P2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (le_normalizer_pCoreOf 2 (P2 L1 L2 S)).trans
      (normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S))
  have hP2NY : P2 L1 L2 S ≤ Subgroup.normalizer (Y : Set G) := by
    intro p hp
    exact CFSG.Quasithin.A4.mem_normalizer_inf (hP2Z2 hp)
      ((hP2L2Q2.trans
        (CFSG.Quasithin.F7.normalizer_le_normalizer_centralizer
          (L2 ⊔ Q2 L1 L2 S))) hp)
  have hB1NY : borelOf L1 S ≤ Subgroup.normalizer (Y : Set G) :=
    (F1.borelOf_le L1 S).trans hL1NY
  have hB2NY : borelOf L2 S ≤ Subgroup.normalizer (Y : Set G) :=
    (((le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans
      (le_sup_left : borelOf L1 S ⊔ borelOf L2 S ≤ bigB L1 L2 S)).trans
        (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S)).trans hP2NY
  have hBNY : bigB L1 L2 S ≤ Subgroup.normalizer (Y : Set G) := by
    change borelOf L1 S ⊔ borelOf L2 S ⊔ S ≤ Subgroup.normalizer (Y : Set G)
    exact sup_le (sup_le hB1NY hB2NY) hSNY
  have hP1NY : P1 L1 L2 S ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le hL1NY hBNY
  have hG0NY : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (Y : Set G) := by
    rw [← F1.parabolic_sup_parabolic L1 L2 S]
    exact sup_le hP1NY hP2NY
  have hYleG0 : Y ≤ L1 ⊔ L2 ⊔ S := hYleS.trans le_sup_right
  have hYleO : Y ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 hYleG0 hG0NY hY2
  rw [hF.1.o2] at hYleO
  exact le_bot_iff.mp hYleO

theorem str86_caseI_basics {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (h1 : VU3Big L1) (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Z1 L1 L2 S = omegaOneCenterOf S ∧ Z1 L1 L2 S ≤ Z2 L1 L2 S ∧
      Z2 L1 L2 S ⊓
        Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) = ⊥ ∧
      S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S ∧
      Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S := by
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n :=
    CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hSB (Or.inr (Or.inl h1))
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨n, hn, hL2⟩))
  have hSle1 : S ≤ L1 ⊔ Q1 L1 L2 S := by
    calc S = (S ⊓ L1) ⊔ Q1 L1 L2 S := hS1
      _ ≤ L1 ⊔ Q1 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hSle2 : S ≤ L2 ⊔ Q2 L1 L2 S := by
    calc S = (S ⊓ L2) ⊔ Q2 L1 L2 S := hS2
      _ ≤ L2 ⊔ Q2 L1 L2 S := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hZ1eq : Z1 L1 L2 S = omegaOneCenterOf S :=
    omegaOneCenterOf_pCoreOf_eq hF.1 hSle1 hZI
  have hZ1ne : Z1 L1 L2 S ≠ ⊥ := by
    rw [hZ1eq]
    exact omegaOneCenterOf_ne_bot_of_hyp111 hF.1
  have hZ1Z2 : Z1 L1 L2 S ≤ Z2 L1 L2 S := by
    rw [hZ1eq]
    have h := omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf
      (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Z1, Z2, Q1, Q2, P1, P2, bigB_comm] using h
  have hZ2bot : Z2 L1 L2 S ⊓
      Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) = ⊥ :=
    z2_inf_centralizer_eq_bot_of_caseI hF.toW hS1 hS2 hZI
  have hHNZ2 : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    (sup_le le_sup_left (pCoreOf_le 2 (P2 L1 L2 S))).trans
      (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S))
  have hQ2C : Q2 L1 L2 S ≤
      Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
    SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  have hCeq : (L2 ⊔ Q2 L1 L2 S) ⊓
      Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S := by
    have hK0 : (L2 ⊔ Q2 L1 L2 S) ⊓
        Subgroup.centralizer (Z2 L1 L2 S : Set G) ≤ L2 ⊔ Q2 L1 L2 S := inf_le_left
    have hQK0 : Q2 L1 L2 S ≤ (L2 ⊔ Q2 L1 L2 S) ⊓
        Subgroup.centralizer (Z2 L1 L2 S : Set G) := le_inf le_sup_right hQ2C
    have hKn0 : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer
        (((L2 ⊔ Q2 L1 L2 S) ⊓
          Subgroup.centralizer (Z2 L1 L2 S : Set G) : Subgroup G) : Set G) := by
      have hHnC : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.normalizer
          (Subgroup.centralizer (Z2 L1 L2 S : Set G) : Set G) :=
        hHNZ2.trans (F7.normalizer_le_normalizer_centralizer (Z2 L1 L2 S))
      intro x hx
      exact CFSG.Quasithin.A4.mem_normalizer_inf (Subgroup.le_normalizer hx) (hHnC hx)
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hF.toW hn hL2 hK0 hKn0 hQK0 with hQ | hH
    · exact hQ
    · exfalso
      have hHC : L2 ⊔ Q2 L1 L2 S ≤
          Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
        rw [← hH]
        exact inf_le_right
      have hZ2leC : Z2 L1 L2 S ≤
          Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp (hHC hx) z hz).symm
      have hZ2le : Z2 L1 L2 S ≤ Z2 L1 L2 S ⊓
          Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
        le_inf le_rfl hZ2leC
      have hZ2eq : Z2 L1 L2 S = ⊥ :=
        le_bot_iff.mp (hZ2le.trans (le_of_eq hZ2bot))
      exact hZ1ne (le_bot_iff.mp (hZ1Z2.trans (le_of_eq hZ2eq)))
  have hSQ2C : S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G) = Q2 L1 L2 S := by
    calc S ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)
        = (S ⊓ (L2 ⊔ Q2 L1 L2 S)) ⊓
            Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
          rw [inf_eq_left.mpr hSle2]
      _ = S ⊓ ((L2 ⊔ Q2 L1 L2 S) ⊓
            Subgroup.centralizer (Z2 L1 L2 S : Set G)) := by rw [inf_assoc]
      _ = S ⊓ Q2 L1 L2 S := by rw [hCeq]
      _ = Q2 L1 L2 S := inf_eq_right.mpr hQ2S
  refine ⟨hZ1eq, hZ1Z2, hZ2bot, hSQ2C, ?_⟩
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxZ2 : x ∈ Z2 L1 L2 S := (Subgroup.mem_inf.mp hx).1
    have hxCS : x ∈ Subgroup.centralizer (S : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxQ2 : x ∈ Q2 L1 L2 S := (omegaOneCenterOf_le (Q2 L1 L2 S)) hxZ2
    have hxS : x ∈ S := hQ2S hxQ2
    have hx2 : x ^ 2 = 1 :=
      (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 x hxZ2
    rw [hZ1eq]
    exact Subgroup.subset_closure
      ⟨Subgroup.mem_inf.mpr ⟨hxS, hxCS⟩, hx2⟩
  · intro x hx
    have hxZ2 : x ∈ Z2 L1 L2 S := hZ1Z2 hx
    have hxCS : x ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (Subgroup.mem_centralizer_iff.mp (hZI (hSle1 hs)) x hx).symm
    exact Subgroup.mem_inf.mpr ⟨hxZ2, hxCS⟩

end CFSG.Quasithin.Stroth
