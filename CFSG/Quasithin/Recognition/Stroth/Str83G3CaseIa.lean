module

public import CFSG.Quasithin.Recognition.Stroth.Str83G3St8
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str83_natural_bottom_of_not_le_q1
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hJ1 : ¬ thompsonJ S ≤ Q1 L1 L2 S)
    {Y : Subgroup G} (hYZ : Y ≤ Z2 L1 L2 S) (hYH : Y ≤ L2 ⊔ S) (hV : IsElemAbelian 2 Y)
    (hstep : IsChiefStep (L2 ⊔ S) Y ⊥ Y) :
    let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
    letI _cg : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
    letI _mod : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ Y)) := l2ChiefSectionModule hE
    ∃ (e : oTwoQuot ↥(L2 ⊔ S) ≃* SL(2, GaloisField 2 (2 * a + 1)))
      (ρ : Representation (ZMod 2) SL(2, GaloisField 2 (2 * a + 1))
        (Additive (Ch3z.chiefMod ⊥ Y)))
      (φ : Additive (Ch3z.chiefMod ⊥ Y) ≃+ (Fin 2 → GaloisField 2 (2 * a + 1))),
      (∀ (h : ↥(L2 ⊔ S)) (w : Ch3z.chiefMod ⊥ Y),
        ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
          Additive.ofMul (l2ChiefSectionAction hstep hE h w)) ∧
      (∀ g w, φ (ρ g w) =
        (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 (2 * a + 1))).mulVec (φ w)) := by
  classical
  let H : Subgroup G := L2 ⊔ S
  let F := GaloisField 2 (2 * a + 1)
  let q : ℕ := 2 ^ (2 * a + 1)
  let W := Additive (Ch3z.chiefMod ⊥ Y)
  haveI : Fintype F := Fintype.ofFinite _
  have hm2 : 2 ≤ 2 * a + 1 := by omega
  have hn1 : 1 ≤ 2 * a + 1 := by omega
  have hFcardFin : Fintype.card F = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (2 * a + 1) (by omega)
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) :=
      congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hL2sup : IsL2Quot (2 * a + 1) (oTwoQuot ↥(L2 ⊔ S)) := by
    have hsupQ : L2 ⊔ S = L2 ⊔ Q1 L2 L1 S := by
      rw [hsup2]
      simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hsupQ]
    obtain ⟨eL⟩ := hL2
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL⟩
  have hZ2e : IsElemAbelian 2 (Z2 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf _
  have hZ2S : Z2 L1 L2 S ≤ S := (A4.omegaOneCenterOf_le (Q2 L1 L2 S)).trans hQ2S
  have hZ2H : Z2 L1 L2 S ≤ H := hZ2S.trans le_sup_right
  have hstepZ : IsChiefStep (L2 ⊔ S) (Z2 L1 L2 S) ⊥ Y :=
    ⟨⟨hYZ, hstep.1.2⟩, ⟨bot_le, hstep.2.1.2⟩, hstep.2.2.1,
      fun K hK _ hKY => hstep.2.2.2 K ⟨hKY, hK.2⟩ bot_le hKY⟩
  have hnc : ¬ IsCentralStep (L2 ⊔ S) ⊥ Y :=
    not_isCentralStep_bot_of_caseI hF hB ha hSz hL2 hZI hstepZ
  let hE := CFSG.Quasithin.isElemAbelian_chiefMod hstep hYH hV.isPGroup
  letI _cg : CommGroup ↥(Ch3z.chiefMod ⊥ Y) := l2ChiefSectionCommGroup hE
  letI _mod : Module (ZMod 2) W := l2ChiefSectionModule hE
  let e₀ := hL2sup.some
  let e : oTwoQuot ↥(L2 ⊔ S) ≃* SL(2, F) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := F))
  let ρ := l2ChiefSectionRep hstep hYH hE e
  have hρirr : Fact ρ.IsIrreducible := ⟨l2ChiefSectionRep_irreducible hstep hYH hE e⟩
  haveI : Fact ρ.IsIrreducible := hρirr
  have hρnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstep hYH hE e hnc
  have hρcompat : ∀ (h : ↥(L2 ⊔ S)) (w : Ch3z.chiefMod ⊥ Y),
      ρ (e (QuotientGroup.mk h)) (Additive.ofMul w) =
        Additive.ofMul (l2ChiefSectionAction hstep hE h w) :=
    fun h w => l2ChiefSectionRep_apply_mk hstep hYH hE e h w
  have hq : IsSzU3Quot (oTwoQuot ↥L1) q := by
    obtain ⟨eSz⟩ := hSz
    exact Or.inl ⟨a, ha, rfl, ⟨eSz⟩⟩
  have hnotJ : ¬ jAtLeast (2 ^ CFSG.Open.pRank 2 S) q S ≤ Q2 L1 L2 S :=
    not_jAtLeast_le_of_not_le_q1 hF.1 hB hS1 hS2 hq hJ1
  obtain ⟨E, hES, hEe, hmE, hEQ2⟩ := exists_not_le_of_not_jAtLeast_le hnotJ
  have hZp : IsPGroup 2 (Z2 L1 L2 S) := hF.1.h2.pgroup.to_le hZ2S
  have hR := relIndex_centralizer_le_mul (S := S) (V := Z2 L1 L2 S) (F := E) (k := q)
    hZ2e hZ2S hEe hES hmE
  have hErel : (E ⊓ Q2 L1 L2 S).relIndex E ≤ q := by
    rw [Subgroup.inf_relIndex_left]
    calc (Q2 L1 L2 S).relIndex E ≤ (Q2 L1 L2 S).relIndex S :=
          Subgroup.relIndex_le_of_le_right hES (D15Proof.relIndex_ne_zero _ _)
      _ = q := by
          have h := str86_relIndex_q2_s (n := 2 * a + 1) hF hB (by omega) hL2
          simpa [q] using h
  have hCV' : (E ⊓ Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E ≤
      (E ⊓ Q2 L1 L2 S).relIndex E := by
    refine Subgroup.relIndex_le_of_le_left ?_ (D15Proof.relIndex_ne_zero _ _)
    refine le_inf inf_le_left ?_
    intro x hx
    exact SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hx.2
  have hCV : (Subgroup.centralizer (Z2 L1 L2 S : Set G)).relIndex E ≤
      (E ⊓ Q2 L1 L2 S).relIndex E := by
    rwa [Subgroup.inf_relIndex_left] at hCV'
  have hdispZ : (Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S) ≤
      q * (E ⊓ Q2 L1 L2 S).relIndex E :=
    hR.trans (Nat.mul_le_mul_left q hCV)
  have hdispY : (Subgroup.centralizer (E : Set G)).relIndex Y ≤
      q * (E ⊓ Q2 L1 L2 S).relIndex E :=
    (Subgroup.relIndex_le_of_le_right hYZ (D15Proof.relIndex_ne_zero _ _)).trans hdispZ
  let P : Subgroup ↥H := E.subgroupOf H
  let Ē : Subgroup (SL(2, F)) :=
    (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom
  have hEH : E ≤ H := hES.trans le_sup_right
  have hsub : (pCoreOf 2 H).subgroupOf H = pCore 2 ↥H := by
    unfold pCoreOf Subgroup.subgroupOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hrelQ : (pCore 2 ↥H).relIndex (E.subgroupOf H) =
      (E ⊓ Q2 L1 L2 S).relIndex E := by
    rw [← hsub, Subgroup.relIndex_subgroupOf hEH,
      ← Subgroup.inf_relIndex_right (pCoreOf 2 H) E, inf_comm, hpCore2]
  have hcard_mk : Nat.card (P.map (QuotientGroup.mk' (pCore 2 ↥H))) =
      (pCore 2 ↥H).relIndex (E.subgroupOf H) := by
    have h := CFSG.Quasithin.Ch3E215M.card_map_eq_relIndex_ker
      (QuotientGroup.mk' (pCore 2 ↥H)) (E.subgroupOf H)
    rw [QuotientGroup.ker_mk'] at h
    exact h.symm
  have hcardE : Nat.card Ē = (E ⊓ Q2 L1 L2 S).relIndex E := by
    rw [show Ē = (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom from rfl,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hcard_mk, hrelQ]
  have hĒea : IsElemAbelian 2 Ē :=
    CFSG.Quasithin.Ch3E215M.isElemAbelian_map e.toMonoidHom
      (CFSG.Quasithin.Ch3E215M.isElemAbelian_map
        (QuotientGroup.mk' (pCore 2 ↥H))
        (CFSG.Open.IsElemAbelian.subgroupOf hEe H))
  have hĒ2 : ∀ x ∈ Ē, x * x = 1 := fun x hx => by
    simpa [pow_two] using hĒea.2 x hx
  have hĒle : Nat.card Ē ≤ q := hcardE.trans_le hErel
  have hĒne : Ē ≠ ⊥ := by
    intro hbot
    apply hEQ2
    have h1 : (E ⊓ Q2 L1 L2 S).relIndex E = 1 := by
      rw [← hcardE, hbot, Subgroup.card_bot]
    have hle : E ≤ E ⊓ Q2 L1 L2 S := (Subgroup.relIndex_eq_one).mp h1
    intro x hx
    exact (Subgroup.mem_inf.mp (hle hx)).2
  obtain ⟨t, htE, htQ2⟩ : ∃ t, t ∈ E ∧ t ∉ Q2 L1 L2 S := by
    by_contra hcon
    push Not at hcon
    exact hEQ2 (fun x hx => hcon x hx)
  have htS : t ∈ S := hES htE
  have htH : t ∈ H := Subgroup.mem_sup_right htS
  have ht2 : t * t ∈ pCoreOf 2 H := by
    rw [show t * t = 1 from by rw [← pow_two]; exact hEe.2 t htE]
    exact (pCoreOf 2 H).one_mem
  have htO : t ∉ pCoreOf 2 H := by
    rwa [hpCore2]
  let ā : SL(2, F) := e (QuotientGroup.mk (⟨t, htH⟩ : ↥H))
  have hsq : Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers ā)) ^ 2 =
      Nat.card W :=
    l2ChiefSectionRep_sq_card_fixSub (m := 2 * a + 1) hm2 hstep hYH hE e hnc htH ht2 htO
  have hāĒ : ā ∈ Ē := by
    have hx : (⟨t, htH⟩ : ↥H) ∈ P := Subgroup.mem_subgroupOf.mpr htE
    refine Subgroup.mem_map.mpr
      ⟨(QuotientGroup.mk' (pCore 2 ↥H)) (⟨t, htH⟩ : ↥H),
        Subgroup.mem_map_of_mem _ hx, ?_⟩
    rw [QuotientGroup.mk'_apply]
    rfl
  have hmono : CFSG.RankThree.FFModules.fixSub ρ Ē ≤
      CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers ā) := by
    intro w hw a ha
    exact hw a (Subgroup.zpowers_le.mpr hāĒ ha)
  have hCle : Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) ≤
      Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers ā)) := by
    refine Nat.card_le_card_of_injective (fun w => ⟨w.1, hmono w.2⟩) ?_
    intro x y h
    have h' : (x : W) = (y : W) :=
      congrArg (fun z : ↥(CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers ā)) =>
        (z : W)) h
    exact Subtype.ext h'
  have hCeq : Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) =
      Nat.card ↥(Y ⊓ Subgroup.centralizer (E : Set G)) := by
    have h := fixSub_chiefMod_bot_card (H := L2 ⊔ S) (U := Y) (W := Y)
      (m := 2 * a + 1) hstep hYH hE e (E.subgroupOf H)
    rw [Subgroup.map_subgroupOf_eq_of_le hEH] at h
    exact h
  have hYcard : Nat.card Y = (Subgroup.centralizer (E : Set G)).relIndex Y *
      Nat.card ↥(Y ⊓ Subgroup.centralizer (E : Set G)) := by
    have h := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) Y
    rw [inf_comm] at h
    exact h.symm
  have hWY : Nat.card W = Nat.card Y := by
    calc Nat.card W
        = Nat.card (Ch3z.chiefMod ⊥ Y) := Nat.card_congr Additive.ofMul
      _ = Nat.card ↥Y := (Nat.card_congr (chiefModBotMulEquiv Y).toEquiv).symm
  have hdispY' : (Subgroup.centralizer (E : Set G)).relIndex Y ≤ q * Nat.card Ē := by
    rw [hcardE]
    exact hdispY
  have hbound : Nat.card W ≤
      q * Nat.card Ē * Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := by
    rw [hWY, hYcard, ← hCeq]
    exact Nat.mul_le_mul_right _ hdispY'
  have hq2 : 2 ≤ q := by
    have h : 2 ^ 1 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [q] using h
  let s : ℕ := Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers ā))
  have hsq' : s ^ 2 = Nat.card W := hsq
  have hWs : Nat.card W ≤ q ^ 2 * s := by
    calc Nat.card W
        ≤ q * Nat.card Ē * Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := hbound
      _ ≤ q * q * s := Nat.mul_le_mul (Nat.mul_le_mul_left q hĒle) hCle
      _ = q ^ 2 * s := by ring
  have hspos : 0 < s := by
    dsimp only [s]
    exact Nat.card_pos
  have hsle : s ≤ q ^ 2 := by
    have h1 : s * s ≤ q ^ 2 * s := by
      calc s * s = s ^ 2 := (pow_two s).symm
        _ = Nat.card W := hsq'
        _ ≤ q ^ 2 * s := hWs
    exact Nat.le_of_mul_le_mul_right h1 hspos
  have hle4 : Nat.card W ≤ q ^ 4 := by
    rw [← hsq']
    calc s ^ 2 = s * s := pow_two s
      _ ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul hsle hsle
      _ = q ^ 4 := by ring
  have hne : Nat.card W ≠ q ^ 4 := by
    intro hWeq
    have hs : s = q ^ 2 := by
      apply Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)
      change s ^ 2 = (q ^ 2) ^ 2
      rw [hsq', hWeq]
      ring
    have hCge : q ^ 2 ≤ Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := by
      have h1 : q ^ 4 ≤ q ^ 2 * Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := by
        calc q ^ 4 = Nat.card W := hWeq.symm
          _ ≤ q * Nat.card Ē *
              Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := hbound
          _ ≤ q * q * Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) :=
              Nat.mul_le_mul (Nat.mul_le_mul_left q hĒle) le_rfl
          _ = q ^ 2 * Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := by ring
      have h2 : q ^ 2 * q ^ 2 ≤
          q ^ 2 * Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := by
        calc q ^ 2 * q ^ 2 = q ^ 4 := by ring
          _ ≤ _ := h1
      exact Nat.le_of_mul_le_mul_left h2 (by positivity)
    have hCeq2 : Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) = q ^ 2 :=
      le_antisymm (hCle.trans (le_of_eq hs)) hCge
    have hĒge : q ≤ Nat.card Ē := by
      have h1 : q ^ 4 ≤ q * Nat.card Ē * q ^ 2 := by
        calc q ^ 4 = Nat.card W := hWeq.symm
          _ ≤ q * Nat.card Ē *
              Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := hbound
          _ = q * Nat.card Ē * q ^ 2 := by rw [hCeq2]
      have h3 : q ^ 3 * q ≤ q ^ 3 * Nat.card Ē := by
        calc q ^ 3 * q = q ^ 4 := by ring
          _ ≤ q * Nat.card Ē * q ^ 2 := h1
          _ = q ^ 3 * Nat.card Ē := by ring
      exact Nat.le_of_mul_le_mul_left h3 (by positivity)
    have hĒeq : Nat.card Ē = q := le_antisymm hĒle hĒge
    have hoff : Nat.card W ≤ Nat.card Ē ^ 2 *
        Nat.card {w : W // ∀ x ∈ Ē, ρ x w = w} := by
      have hfix' : Nat.card {w : W //
          ∀ x ∈ Ē, ρ x w = w} =
          Nat.card (CFSG.RankThree.FFModules.fixSub ρ Ē) := rfl
      rw [hĒeq, hfix', hCeq2, hWeq]
      have hpow : q ^ 2 * q ^ 2 = q ^ 4 := by ring
      rw [hpow]
    obtain ⟨hD, hdim⟩ | ⟨s₂, hn2, -, -⟩ :=
      CFSG.Quasithin.B45L2.inner_class (n := 2 * a + 1) hn1 hFcardFin ρ hρnt Ē hĒne hĒ2 hoff
    · have hWcard : Nat.card W = q ^ 2 := by
        rw [CFSG.QuasithinUnique.Setup.SL2Modules.natCard_eq_pow_finrank (ρ := ρ), hD, hdim,
          show q = 2 ^ (2 * a + 1) from rfl]
      have hq4eq : q ^ 4 = q ^ 2 := hWeq.symm.trans hWcard
      have hq1 : 1 < q ^ 2 := by
        rw [pow_two]
        nlinarith [hq2]
      have hbad : q ^ 2 = 1 := by
        apply Nat.eq_of_mul_eq_mul_left (by positivity : 0 < q ^ 2)
        calc q ^ 2 * q ^ 2 = q ^ 4 := by ring
          _ = q ^ 2 := hq4eq
          _ = q ^ 2 * 1 := by ring
      omega
    · omega
  have hpow4 : 2 ^ (4 * (2 * a + 1)) = q ^ 4 := by
    rw [show q = 2 ^ (2 * a + 1) from rfl, ← pow_mul]
    congr 1
    ring
  have hlt : Nat.card W < q ^ 4 :=
    lt_of_le_of_ne hle4 hne
  have hlt' : Nat.card W < 2 ^ (4 * (2 * a + 1)) := by
    rw [hpow4]
    exact hlt
  let T : Sylow 2 (oTwoQuot ↥(L2 ⊔ S)) := Sylow.nonempty.some
  have hT := l2Sylow_sq_mem (m := 2 * a + 1) hm2 hL2sup T
  let A : Subgroup (SL(2, F)) := (T : Subgroup (oTwoQuot ↥(L2 ⊔ S))).map e.toMonoidHom
  have hA2 : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul, hT.1 y hy, map_one]
  have hAcard : Nat.card A = 2 ^ (2 * a + 1) := by
    rw [show A = (T : Subgroup (oTwoQuot ↥(L2 ⊔ S))).map e.toMonoidHom from rfl,
      Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hT.2]
  have h26 := CFSG.RankThree.GF2n.Tim81.Sec2.isNaturalModule_or_isOrthModule_or_of_card_lt
    (n := 2 * a + 1) (F := F) (W := W)
    hn1 hFcardFin ρ hρnt A hA2 hAcard hlt'
  clear hS1 hS2 hQ2S hsup2 hpCore2 hZ2e hZ2S hZ2H hstepZ hnc hq hnotJ hES hEe
    hmE hEQ2 hZp hR hErel hCV' hCV hdispZ hdispY hEH hsub hrelQ hcard_mk hcardE
    hĒea hĒle hCeq hYcard hWY hdispY' hq2 hne hlt ha
  clear hsq hsq' hWs hspos hsle hle4 hāĒ hmono hCle
  clear s
  clear ā
  clear t htE htQ2 htS htH ht2 htO
  rcases h26 with hnat | ⟨l, -, hn2, -⟩ | ⟨l, hn3, hW8l, -⟩
  · obtain ⟨φ, hφ⟩ := hnat
    exact ⟨e, ρ, φ, hρcompat, hφ⟩
  · exfalso
    omega
  · exfalso
    have h8 := eightL_module_bound (n := 2 * a + 1) (l := l) hn3 hFcardFin
      ρ hρnt hW8l Ē hĒne hĒ2 (by
        have hoff8 : Nat.card W ≤
            2 ^ (2 * a + 1) * Nat.card Ē *
              Nat.card {w : W //
                ∀ x ∈ Ē, ρ x w = w} := hbound
        exact hoff8)
    obtain ⟨hl1, -⟩ := h8
    have hW8 : Nat.card W = 2 ^ 8 :=
      hW8l.trans (by rw [hl1])
    clear hbound hĒne hĒ2 hA2 hAcard hρnt hρcompat
    have ha1 : a = 1 := by rw [hl1] at hn3; omega
    apply str83_bottom_st8_false (a := a) hF hB ha1 hSz hL2 hZI hJ1 hYZ hYH hV hstep
    change Nat.card W = 2 ^ 8
    exact hW8

end CFSG.Quasithin.Stroth

end
