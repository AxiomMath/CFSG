module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem smul_centralizer (a : MulAut G) (s : Set G) :
    a • Subgroup.centralizer s = Subgroup.centralizer (a • s) := by
  apply le_antisymm
  · have himg : (fun x => (MulDistribMulAction.toMonoidHom G a) x) '' s = a • s := by
      rw [show (fun x => (MulDistribMulAction.toMonoidHom G a) x) = (fun x => a • x) from rfl]
      exact Set.image_smul
    have h := Subgroup.map_centralizer_le_centralizer_image s
      (MulDistribMulAction.toMonoidHom G a)
    rw [CFSG.Quasithin.Stroth.map_mulDistrib_eq_smul, himg] at h
    exact h
  · have himg : (fun x => (MulDistribMulAction.toMonoidHom G a⁻¹) x) '' (a • s) = s := by
      rw [show (fun x => (MulDistribMulAction.toMonoidHom G a⁻¹) x) = (fun x => a⁻¹ • x)
        from rfl]
      rw [Set.image_smul, smul_smul]
      simp
    have h := Subgroup.map_centralizer_le_centralizer_image (a • s)
      (MulDistribMulAction.toMonoidHom G a⁻¹)
    rw [CFSG.Quasithin.Stroth.map_mulDistrib_eq_smul, himg] at h
    have h'' := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a)).mpr h
    simpa [smul_smul] using h''

theorem inf_centralizer_eq_bot_of_sup_eq {V E E' Q S M L : Subgroup G}
    (hQV : Q ≤ Subgroup.centralizer (V : Set G))
    (hES : E ⊔ Q = S) (hE'S : E' ⊔ Q = M)
    (hL : L ≤ S ⊔ M ⊔ Q)
    (hVL : V ⊓ Subgroup.centralizer ((L ⊔ Q : Subgroup G) : Set G) = ⊥) :
    (V ⊓ Subgroup.centralizer (E : Set G)) ⊓
      (V ⊓ Subgroup.centralizer (E' : Set G)) = ⊥ := by
  classical
  let C1 : Subgroup G := V ⊓ Subgroup.centralizer (E : Set G)
  let C2 : Subgroup G := V ⊓ Subgroup.centralizer (E' : Set G)
  have hC1E : C1 ≤ Subgroup.centralizer (E : Set G) := inf_le_right
  have hC2E : C2 ≤ Subgroup.centralizer (E' : Set G) := inf_le_right
  have hC1V : C1 ≤ V := inf_le_left
  have hC2V : C2 ≤ V := inf_le_left
  have hC12V : C1 ⊓ C2 ≤ V := inf_le_left.trans hC1V
  have hEC1 : E ≤ Subgroup.centralizer (C1 : Set G) :=
    (Subgroup.le_centralizer_iff).mpr hC1E
  have hE'C2 : E' ≤ Subgroup.centralizer (C2 : Set G) :=
    (Subgroup.le_centralizer_iff).mpr hC2E
  have hcentC1 : Subgroup.centralizer (C1 : Set G) ≤
      Subgroup.centralizer ((C1 ⊓ C2 : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)
  have hcentC2 : Subgroup.centralizer (C2 : Set G) ≤
      Subgroup.centralizer ((C1 ⊓ C2 : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right)
  have hQcent : Q ≤ Subgroup.centralizer ((C1 ⊓ C2 : Subgroup G) : Set G) :=
    hQV.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hC12V))
  have hScent : S ≤ Subgroup.centralizer ((C1 ⊓ C2 : Subgroup G) : Set G) := by
    rw [← hES]
    exact sup_le (hEC1.trans hcentC1) hQcent
  have hMcent : M ≤ Subgroup.centralizer ((C1 ⊓ C2 : Subgroup G) : Set G) := by
    rw [← hE'S]
    exact sup_le (hE'C2.trans hcentC2) hQcent
  have hSMQcent : S ⊔ M ⊔ Q ≤ Subgroup.centralizer ((C1 ⊓ C2 : Subgroup G) : Set G) :=
    sup_le (sup_le hScent hMcent) hQcent
  have hLcent : L ⊔ Q ≤ Subgroup.centralizer ((C1 ⊓ C2 : Subgroup G) : Set G) :=
    sup_le (hL.trans hSMQcent) hQcent
  have hC12cent : C1 ⊓ C2 ≤ Subgroup.centralizer ((L ⊔ Q : Subgroup G) : Set G) :=
    (Subgroup.le_centralizer_iff).mp hLcent
  have hC12VL : C1 ⊓ C2 ≤ V ⊓ Subgroup.centralizer ((L ⊔ Q : Subgroup G) : Set G) :=
    le_inf hC12V hC12cent
  rwa [hVL, le_bot_iff] at hC12VL

theorem str86_rankOne_sup_conj_S {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    {h : G} (hhL2 : h ∈ L2) (hhN : h ∉ Subgroup.normalizer (S : Set G)) :
    L2 ≤ S ⊔ MulAut.conj h • S ⊔ Q2 L1 L2 S := by
  classical
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  let T : Subgroup G := S ⊓ L2
  let B : Subgroup G := borelOf L2 S
  let M : Subgroup G := S ⊔ MulAut.conj h • S ⊔ Q2 L1 L2 S
  have hTsylL2 : IsSylowTwoOf T L2 := hF.1.h2.sylow
  have hTsylB : IsSylowTwoOf T B := F112W.isSylowTwoOf_borelOf_right hR
  have hTnormB : (T.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTsylB.1).mpr
      (show B ≤ Subgroup.normalizer (T : Set G) from inf_le_right)
  have hTL2 : T ≤ L2 := inf_le_right
  have hTS : T ≤ S := inf_le_left
  have hT_le_M : T ≤ M := hTS.trans (le_sup_left.trans le_sup_left)
  have hhL2S : MulAut.conj h • L2 = L2 := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hhL2)
  have hhT_L2 : MulAut.conj h • T ≤ L2 := by
    calc MulAut.conj h • T ≤ MulAut.conj h • L2 :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hTL2
      _ = L2 := hhL2S
  have hhT_S : MulAut.conj h • T ≤ MulAut.conj h • S :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hTS
  have hhT_le_M : MulAut.conj h • T ≤ M :=
    hhT_S.trans (le_sup_right.trans le_sup_left)
  have hM0eq : M ⊓ L2 = L2 := by
    by_contra hne
    have hTle : T ≤ M ⊓ L2 := le_inf hT_le_M hTL2
    have hMleN : M ⊓ L2 ≤ Subgroup.normalizer (T : Set G) :=
      hR.r2.unique_max (M ⊓ L2) hTle inf_le_right hne
    have hhT_le_M0 : MulAut.conj h • T ≤ M ⊓ L2 := le_inf hhT_le_M hhT_L2
    have hhT_N : MulAut.conj h • T ≤ Subgroup.normalizer (T : Set G) :=
      hhT_le_M0.trans hMleN
    have hhT_B : MulAut.conj h • T ≤ B := le_inf hhT_L2 hhT_N
    have hhT2 : IsPGroup 2 ↥(MulAut.conj h • T) := by
      let f : G →* G := MulDistribMulAction.toMonoidHom G (MulAut.conj h)
      have hmap : Subgroup.map f T = MulAut.conj h • T := by
        simpa [f] using CFSG.Quasithin.Stroth.map_mulDistrib_eq_smul (MulAut.conj h) T
      exact hmap ▸ hTsylL2.2.1.map f
    have hhT_le_T : MulAut.conj h • T ≤ T :=
      le_of_isSylowTwoOf_normal hTsylB hTnormB hhT_B hhT2
    have hcard : Nat.card ↥(MulAut.conj h • T) = Nat.card ↥T := by
      have h := Subgroup.card_map_of_injective
        (f := MulDistribMulAction.toMonoidHom G (MulAut.conj h))
        (MulEquiv.injective (MulAut.conj h)) (K := T)
      simpa [CFSG.Quasithin.Stroth.map_mulDistrib_eq_smul] using h
    have hhT_eq_T : MulAut.conj h • T = T :=
      Subgroup.eq_of_le_of_card_ge hhT_le_T (le_of_eq hcard.symm)
    have hmapT : Subgroup.map (MulDistribMulAction.toMonoidHom G (MulAut.conj h)) T = T := by
      simpa [CFSG.Quasithin.Stroth.map_mulDistrib_eq_smul] using hhT_eq_T
    have hhN_T : h ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hmapT
    have hBbig : B ≤ bigB L1 L2 S :=
      (le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans le_sup_left
    have hmemB : h ∈ B := by
      have hmem : h ∈ L2 ⊓ Subgroup.normalizer (T : Set G) := Subgroup.mem_inf.mpr ⟨hhL2, hhN_T⟩
      rwa [show L2 ⊓ Subgroup.normalizer (T : Set G) = B from rfl] at hmem
    exact hhN (hSB (hBbig hmemB))
  have hL2le : L2 ≤ M := (le_of_eq hM0eq.symm).trans inf_le_left
  exact hL2le

theorem str86_card_z2_le_sq
    {L1 L2 S : Subgroup G}
    {k n : ℕ} {F : Type} [Field F] [Finite F] (hF : F112Hyp L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (hk : 2 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (hB2 : VBig L2) (hZI : L1 ⊔ Q1 L1 L2 S ≤
      Subgroup.centralizer (Z1 L1 L2 S : Set G)) :
    Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2 := by
  classical
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  have hVL2 : VL2 L2 := ⟨n, hL2⟩
  have hcase := str86_caseI_basics hF hSB h1 hB2 hVL2 hZI
  have hZ2bot : Z2 L1 L2 S ⊓ Subgroup.centralizer
      ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) = ⊥ := hcase.2.2.1
  obtain ⟨g, hgL1, hgborel⟩ := SetLike.exists_of_lt (F1.lt_borelOf hR)
  have hgB : g ∉ bigB L1 L2 S := by
    intro h
    apply hgborel
    have hmem : g ∈ L1 ⊓ bigB L1 L2 S := Subgroup.mem_inf.mpr ⟨hgL1, h⟩
    rwa [F1.inf_bigB_eq_borelOf hR] at hmem
  have hg : g ∈ L1 ⊔ S := (le_sup_left : L1 ≤ L1 ⊔ S) hgL1
  have hL2borel : L2 ⊓ Subgroup.normalizer (S : Set G) = borelOf L2 S := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxL2, hxN⟩ := Subgroup.mem_inf.mp hx
      have hxNL2 : x ∈ Subgroup.normalizer (L2 : Set G) := Subgroup.le_normalizer hxL2
      exact Subgroup.mem_inf.mpr ⟨hxL2, CFSG.Quasithin.A4.mem_normalizer_inf hxN hxNL2⟩
    · intro x hx
      have hBbig : borelOf L2 S ≤ bigB L1 L2 S :=
        (le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans le_sup_left
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hSB (hBbig hx)⟩
  obtain ⟨h, hhL2, hhborel⟩ := SetLike.exists_of_lt (F1.lt_borelOf hR.symm)
  have hhN : h ∉ Subgroup.normalizer (S : Set G) := by
    intro hN
    apply hhborel
    have hmem : h ∈ L2 ⊓ Subgroup.normalizer (S : Set G) := Subgroup.mem_inf.mpr ⟨hhL2, hN⟩
    rwa [hL2borel] at hmem
  have hEsup : MulAut.conj g • u3Y L1 L2 S ⊔ Q2 L1 L2 S = S :=
    str86_u3Y_conj_sup_q2 hF hSB hk hFc hU3 hn hL2 hZQ hg hgB
  have hhP2 : h ∈ P2 L1 L2 S := (le_sup_left : L2 ≤ P2 L1 L2 S) hhL2
  have hhNZ2 : h ∈ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S)
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S) hhP2)
  have hhZ2 : MulAut.conj h • Z2 L1 L2 S = Z2 L1 L2 S := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self hhNZ2
  have hQ2fix : MulAut.conj h • Q2 L1 L2 S = Q2 L1 L2 S := by
    rw [mulAut_conj_smul_eq_conjAct]
    exact Subgroup.conjAct_pointwise_smul_eq_self
      ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)) hhP2)
  have hE'sup : MulAut.conj h • (MulAut.conj g • u3Y L1 L2 S) ⊔ Q2 L1 L2 S =
      MulAut.conj h • S := by
    rw [← hQ2fix, ← Subgroup.smul_sup, hEsup]
  have hL2le : L2 ≤ S ⊔ (MulAut.conj h • S) ⊔ Q2 L1 L2 S :=
    str86_rankOne_sup_conj_S hF hSB hhL2 hhN
  let E : Subgroup G := MulAut.conj g • u3Y L1 L2 S
  let C1 : Subgroup G := Z2 L1 L2 S ⊓ Subgroup.centralizer (E : Set G)
  let C2 : Subgroup G := Z2 L1 L2 S ⊓
    Subgroup.centralizer ((MulAut.conj h • E : Subgroup G) : Set G)
  have hC12bot : C1 ⊓ C2 = ⊥ :=
    inf_centralizer_eq_bot_of_sup_eq (V := Z2 L1 L2 S) (E := E) (E' := MulAut.conj h • E)
      (Q := Q2 L1 L2 S) (S := S) (M := MulAut.conj h • S) (L := L2)
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S))
      hEsup hE'sup hL2le hZ2bot
  have hcardV : Nat.card (Z2 L1 L2 S) ≤
      C1.relIndex (Z2 L1 L2 S) * C2.relIndex (Z2 L1 L2 S) := by
    have h := Subgroup.relIndex_inf_le (H := C1) (K := C2) (L := Z2 L1 L2 S)
    rwa [hC12bot, Subgroup.relIndex_bot_left] at h
  have hbound1 : C1.relIndex (Z2 L1 L2 S) ≤ 2 ^ k * 2 ^ n := by
    simpa [C1, E] using str86_u3Y_conj_centralizer_bound hF hSB hk hFc hU3 hn hL2 hZQ hg
  have hC1eq : MulAut.conj h • C1 = C2 := by
    show MulAut.conj h • (Z2 L1 L2 S ⊓ Subgroup.centralizer (E : Set G)) =
      Z2 L1 L2 S ⊓ Subgroup.centralizer ((MulAut.conj h • E : Subgroup G) : Set G)
    rw [Subgroup.smul_inf, hhZ2, smul_centralizer]
    rfl
  have hrel : C2.relIndex (Z2 L1 L2 S) = C1.relIndex (Z2 L1 L2 S) := by
    calc C2.relIndex (Z2 L1 L2 S)
        = (MulAut.conj h • C1).relIndex (MulAut.conj h • Z2 L1 L2 S) := by rw [hC1eq, hhZ2]
      _ = C1.relIndex (Z2 L1 L2 S) :=
          Subgroup.relIndex_pointwise_smul (MulAut.conj h) C1 (Z2 L1 L2 S)
  have hbound2 : C2.relIndex (Z2 L1 L2 S) ≤ 2 ^ k * 2 ^ n := by
    rw [hrel]
    exact hbound1
  calc Nat.card (Z2 L1 L2 S)
      ≤ C1.relIndex (Z2 L1 L2 S) * C2.relIndex (Z2 L1 L2 S) := hcardV
    _ ≤ (2 ^ k * 2 ^ n) * (2 ^ k * 2 ^ n) := Nat.mul_le_mul hbound1 hbound2
    _ = (2 ^ k * 2 ^ n) ^ 2 := (pow_two _).symm
