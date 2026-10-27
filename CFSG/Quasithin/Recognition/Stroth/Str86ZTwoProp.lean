module
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoComm
public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefModBot
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Quot
public import CFSG.RankThree.GF2n.Tim81.Sec2.NaturalFixedPointwise
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelTransport

public section
namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_z2_commutator_eq_chief
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (h376 : Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hncW : ¬ IsCentralStep (u3H L1 L2 S) ⊥ W) (hWZ2 : W ≤ Z2 L1 L2 S) :
    ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W := by
  classical
  let H := u3H L1 L2 S
  let C : Subgroup G := ⁅Z2 L1 L2 S, H⁆
  have hC_le : C ≤ W := by
    exact str86_commutator_z2_u3H_le hF hSB hk hFc hU3 hn hL2 hZQ h376 hstepW hncW hWZ2
  have hCnorm : H ≤ Subgroup.normalizer (C : Set G) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := Z2 L1 L2 S) (H₂ := H)
  have hCnormal : IsNormalIn H (Q2 L1 L2 S) C :=
    ⟨hC_le.trans hstepW.1.1, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hCnorm hg) x).mp hx⟩
  have hCne : C ≠ ⊥ := by
    intro hbot
    apply hncW
    intro g hg w hw
    have hwZ : w ∈ Z2 L1 L2 S := hWZ2 hw
    have hcent : Z2 L1 L2 S ≤ Subgroup.centralizer ((H : Subgroup G) : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
    have hcomm : g * w = w * g := (Subgroup.mem_centralizer_iff.mp (hcent hwZ) g hg)
    rw [Subgroup.mem_bot, show g * w * g⁻¹ * w⁻¹ = 1 from by
      calc g * w * g⁻¹ * w⁻¹ = (g * w * g⁻¹) * w⁻¹ := rfl
        _ = (w * g * g⁻¹) * w⁻¹ := by rw [hcomm]
        _ = 1 := by group]
  have hCW : C = W := by
    rcases hstepW.2.2.2 C hCnormal bot_le hC_le with h | h
    · exact absurd h hCne
    · exact h
  exact hCW

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type} [Group G] [Finite G]

theorem str86_commutator_mem_w {L1 L2 S : Subgroup G} {W : Subgroup G}
    (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W) {h x : G}
    (hh : h ∈ u3H L1 L2 S) (hx : x ∈ Z2 L1 L2 S) :
    h * x * h⁻¹ * x⁻¹ ∈ W := by
  have hmem : ⁅h, x⁆ ∈ ⁅u3H L1 L2 S, Z2 L1 L2 S⁆ :=
    Subgroup.commutator_mem_commutator hh hx
  rw [Subgroup.commutator_comm] at hmem
  rw [hcomm] at hmem
  simpa [commutatorElement_def] using hmem

theorem str86_commutator_fixed_of_sq
    {L1 L2 S : Subgroup G} {n : ℕ}
    (hF : F112HypW L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2)) {s x : G}
    (hs : s ∈ S) (hx : x ∈ Z2 L1 L2 S) :
    s * (s * x * s⁻¹ * x⁻¹) * s⁻¹ = s * x * s⁻¹ * x⁻¹ := by
  classical
  have hZ2ea : IsElemAbelian 2 (Z2 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)
  have hcomm : ∀ a ∈ Z2 L1 L2 S, ∀ b ∈ Z2 L1 L2 S, a * b = b * a := by
    intro a ha b hb
    have h := (isMulCommutative_iff.mp hZ2ea.1) ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val h
  have hs2 : s * s ∈ Q2 L1 L2 S := str86_sq_mem_q2 hF hSB hn hL2 hs
  have hsx : s * x * s⁻¹ ∈ Z2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S) hs) x).mp hx
  have hcent : ∀ q ∈ Q2 L1 L2 S, ∀ y ∈ Z2 L1 L2 S, q * y = y * q := by
    intro q hq y hy
    exact (Subgroup.mem_centralizer_iff.mp
      (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq) y hy).symm
  have hs2x : s * (s * x * s⁻¹) * s⁻¹ = x := by
    calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s * s)⁻¹ := by group
      _ = x := by
          rw [hcent (s * s) hs2 x hx]
          group
  have hsxinv : (s * x * s⁻¹)⁻¹ = s * x⁻¹ * s⁻¹ := by group
  have hx2 : x * x = 1 := by
    simpa [pow_two] using hZ2ea.2 x hx
  have hsx2 : (s * x * s⁻¹) * (s * x * s⁻¹) = 1 := by
    simpa [pow_two] using hZ2ea.2 (s * x * s⁻¹) hsx
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hsxinv2 : (s * x * s⁻¹)⁻¹ = s * x * s⁻¹ :=
    inv_eq_of_mul_eq_one_right hsx2
  calc s * (s * x * s⁻¹ * x⁻¹) * s⁻¹
      = (s * (s * x * s⁻¹) * s⁻¹) * (s * x⁻¹ * s⁻¹) := by group
    _ = x * (s * x * s⁻¹)⁻¹ := by rw [hs2x, hsxinv]
    _ = x * (s * x * s⁻¹) := by rw [hsxinv2]
    _ = (s * x * s⁻¹) * x := hcomm x hx (s * x * s⁻¹) hsx
    _ = (s * x * s⁻¹) * x⁻¹ := by rw [hxinv]
    _ = s * x * s⁻¹ * x⁻¹ := rfl

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type} [Group G] [Finite G]

theorem str86_natural_case_false
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hB2 : VBig L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (h376 : Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hncW : ¬ IsCentralStep (u3H L1 L2 S) ⊥ W) (hWZ2 : W ≤ Z2 L1 L2 S)
    (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 n))
    (T : Sylow 2 (oTwoQuot ↥(u3H L1 L2 S)))
    (hTcoe : (T : Subgroup (oTwoQuot ↥(u3H L1 L2 S))) =
      CFSG.Quasithin.imageOTwoQuot (u3H L1 L2 S) S)
    (hnat : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsNaturalModule (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) : False := by
  classical
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have hnat' : IsNaturalModule ρ := hnat
  let A : Subgroup (SL(2, GaloisField 2 n)) := (T : Subgroup _).map e.toMonoidHom
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul]
    have ht2 := (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).1 t ht
    rw [ht2, map_one]
  have hAeqF : Nat.card A = Nat.card (GaloisField 2 n) := by
    have hTcard : Nat.card ↥(CFSG.Quasithin.imageOTwoQuot H S) = 2 ^ n := by
      rw [← hTcoe]
      exact (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).2
    calc Nat.card A = Nat.card ↥(T : Subgroup (oTwoQuot ↥H)) :=
          Subgroup.card_map_of_injective e.injective
      _ = Nat.card ↥(CFSG.Quasithin.imageOTwoQuot H S) := by rw [hTcoe]
      _ = 2 ^ n := hTcard
      _ = Nat.card (GaloisField 2 n) := by
          exact (GaloisField.card 2 n (by omega)).symm
  have hfixcard : Nat.card (fixedSub ρ A) = Nat.card (GaloisField 2 n) :=
    IsNaturalModule.natCard_fixedSub hnat' hA2 hAeqF
  have hfixeq : ∀ {a : SL(2, GaloisField 2 n)} (ha : a ∈ A) (ha1 : a ≠ 1),
      fixedSub ρ (Subgroup.zpowers a) = fixedSub ρ A :=
    fun ha ha1 => IsNaturalModule.fixedSub_zpowers_eq hnat' hA2 hAeqF ha ha1
  have hSleH : S ≤ H := str86_s_le_u3H hF.toW hSB hn hL2
  have hcase := str86_caseI_basics hF hSB ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
    hB2 ⟨n, hL2⟩ hZI
  have hZ1eq : Z1 L1 L2 S = Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) :=
    hcase.2.2.2.2.symm
  have hZ2ea : IsElemAbelian 2 (Z2 L1 L2 S) :=
    SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)
  have hmain : ∀ s ∈ S, s ∉ Q2 L1 L2 S → ∀ x ∈ Z2 L1 L2 S,
      x * s * x⁻¹ * s⁻¹ ∈ Z1 L1 L2 S := by
    intro s hsS hsQ x hxZ
    have hsH : s ∈ H := hSleH hsS
    let a : SL(2, GaloisField 2 n) := e (QuotientGroup.mk ⟨s, hsH⟩)
    have haA : a ∈ A := by
      have hmkT : (QuotientGroup.mk ⟨s, hsH⟩ : oTwoQuot ↥H) ∈ (T : Subgroup _) := by
        rw [hTcoe]
        exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (pCore 2 ↥H))
          (Subgroup.mem_subgroupOf.mpr hsS)
      exact Subgroup.mem_map_of_mem e.toMonoidHom hmkT
    have ha1 : a ≠ 1 := by
      intro h
      apply hsQ
      have hmk1 : (QuotientGroup.mk ⟨s, hsH⟩ : oTwoQuot ↥H) = 1 := by
        apply e.injective
        rw [map_one]
        exact h
      have hmem : (⟨s, hsH⟩ : ↥H) ∈ pCore 2 ↥H :=
        (QuotientGroup.eq_one_iff _).mp hmk1
      have := (F1.mem_pCore_iff_coe (⟨s, hsH⟩ : ↥H)).mp hmem
      rwa [str86_pCoreOf_u3H hF.toW] at this
    let y : G := s * x * s⁻¹ * x⁻¹
    have hyZ : y ∈ Z2 L1 L2 S := by
      have h1 : s * x * s⁻¹ ∈ Z2 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_z2_of_sylow (L1 := L1) (L2 := L2) (S := S) hsS) x).mp hxZ
      exact (Z2 L1 L2 S).mul_mem h1 ((Z2 L1 L2 S).inv_mem hxZ)
    have hyW : y ∈ W := str86_commutator_mem_w hcomm hsH hxZ
    have hyfix : s * y * s⁻¹ = y :=
      str86_commutator_fixed_of_sq hF.toW hSB hn hL2 hsS hxZ
    let P : Subgroup ↥H := Subgroup.zpowers ⟨s, hsH⟩
    have hPsub : (P.map H.subtype : Subgroup G) = Subgroup.zpowers s := by
      rw [show P = Subgroup.zpowers ⟨s, hsH⟩ from rfl, MonoidHom.map_zpowers]
      rfl
    have hPy : y ∈ Subgroup.centralizer ((P.map H.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [hPsub] at hh
      have hcomm_s : Commute s y := by
        rw [Commute]
        calc s * y = (s * y * s⁻¹) * s := by group
          _ = y * s := by rw [hyfix]
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (hcomm_s.zpow_left j).eq
    have hPimg : (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom =
        Subgroup.zpowers a := by
      rw [show P = Subgroup.zpowers ⟨s, hsH⟩ from rfl, MonoidHom.map_zpowers,
        MonoidHom.map_zpowers]
      rfl
    have hfixmem0 : Additive.ofMul (chiefModBotMulEquiv W ⟨y, hyW⟩) ∈
        CFSG.RankThree.FFModules.fixSub (l2ChiefSectionRep hstepW hUH hE e)
          ((P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom) :=
      (mem_fixSub_chiefMod_bot_iff hstepW hUH hE e P ⟨y, hyW⟩).mpr (by
        change (⟨y, hyW⟩ : ↥W).1 ∈ Subgroup.centralizer
          ((P.map H.subtype : Subgroup G) : Set G)
        simpa [hPsub] using hPy)
    rw [hPimg] at hfixmem0
    have hfixmem : Additive.ofMul (chiefModBotMulEquiv W ⟨y, hyW⟩) ∈
        fixedSub ρ (Subgroup.zpowers a) := hfixmem0
    rw [hfixeq haA ha1] at hfixmem
    let P2 : Subgroup ↥H := S.subgroupOf H
    have hP2img : (P2.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom = A := by
      rw [show P2 = S.subgroupOf H from rfl]
      rw [show A = (T : Subgroup (oTwoQuot ↥H)).map e.toMonoidHom from rfl, hTcoe]
      rfl
    have hP2sub : (P2.map H.subtype : Subgroup G) = S := by
      rw [show P2 = S.subgroupOf H from rfl, Subgroup.map_subgroupOf_eq_of_le hSleH]
    have hmem2 : Additive.ofMul (chiefModBotMulEquiv W ⟨y, hyW⟩) ∈
        CFSG.RankThree.FFModules.fixSub (l2ChiefSectionRep hstepW hUH hE e)
          ((P2.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom) := by
      rw [hP2img]
      exact hfixmem
    have hycent : y ∈ Subgroup.centralizer ((P2.map H.subtype : Subgroup G) : Set G) := by
      have h := (mem_fixSub_chiefMod_bot_iff hstepW hUH hE e P2 ⟨y, hyW⟩).mp hmem2
      rw [hP2sub] at h ⊢
      exact h
    rw [hP2sub, Subgroup.mem_centralizer_iff] at hycent
    have hyZ1 : y ∈ Z1 L1 L2 S := by
      rw [hZ1eq, Subgroup.mem_inf]
      refine ⟨hyZ, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hycent u hu
    have hinv : x * s * x⁻¹ * s⁻¹ = y⁻¹ := by
      show x * s * x⁻¹ * s⁻¹ = (s * x * s⁻¹ * x⁻¹)⁻¹
      group
    rw [hinv]
    exact (Z1 L1 L2 S).inv_mem hyZ1
  have hcomm_le : ⁅Z2 L1 L2 S, S⁆ ≤ Z1 L1 L2 S := by
    rw [Subgroup.commutator_le]
    intro x hx s hs
    by_cases hsQ : s ∈ Q2 L1 L2 S
    · have hcs : s ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) :=
        SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hsQ
      have h1 : x * s = s * x := (Subgroup.mem_centralizer_iff.mp hcs) x hx
      have hx1 : ⁅x, s⁆ = 1 := by
        rw [commutatorElement_def]
        calc x * s * x⁻¹ * s⁻¹ = (s * x) * x⁻¹ * s⁻¹ := by rw [h1]
          _ = 1 := by group
      rw [hx1]
      exact (Z1 L1 L2 S).one_mem
    · simpa [commutatorElement_def] using hmain s hs hsQ x hx
  have hcomm_le' : ⁅u3X1 L1 L2 S, Z2 L1 L2 S⁆ ≤ Z1 L1 L2 S := by
    calc ⁅u3X1 L1 L2 S, Z2 L1 L2 S⁆ ≤ ⁅S, Z2 L1 L2 S⁆ :=
          Subgroup.commutator_mono (u3X1_le_q1.trans
            (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW))) le_rfl
      _ = ⁅Z2 L1 L2 S, S⁆ := Subgroup.commutator_comm _ _
      _ ≤ Z1 L1 L2 S := hcomm_le
  exact (str86_commutator_u3X1_z2_not_le_z1 hF hSB hk hFc hU3 hB2 ⟨n, hL2⟩ hZI hZQ) hcomm_le'

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type} [Group G] [Finite G]

theorem str86_orth_case_cards
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hB2 : VBig L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (h376 : Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2)
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hncW : ¬ IsCentralStep (u3H L1 L2 S) ⊥ W) (hWZ2 : W ≤ Z2 L1 L2 S)
    (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 n))
    (T : Sylow 2 (oTwoQuot ↥(u3H L1 L2 S)))
    (hTcoe : (T : Subgroup (oTwoQuot ↥(u3H L1 L2 S))) =
      CFSG.Quasithin.imageOTwoQuot (u3H L1 L2 S) S)
    [Fintype (GaloisField 2 n)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 n) = 2 ^ (2 * l))
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    n = 2 * k ∧ Nat.card W = (2 ^ k) ^ 4 := by
  classical
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have horth' : IsOrthModule hl ρ := horth
  let A : Subgroup (SL(2, GaloisField 2 n)) := (T : Subgroup _).map e.toMonoidHom
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul]
    have ht2 := (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).1 t ht
    rw [ht2, map_one]
  have hTcard : Nat.card ↥(CFSG.Quasithin.imageOTwoQuot H S) = 2 ^ n := by
    rw [← hTcoe]
    exact (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).2
  have hcardGF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by omega)
  have hAcard : Nat.card A = 2 ^ (2 * l) := by
    calc Nat.card A = Nat.card ↥(T : Subgroup (oTwoQuot ↥H)) :=
          Subgroup.card_map_of_injective e.injective
      _ = Nat.card ↥(CFSG.Quasithin.imageOTwoQuot H S) := by rw [hTcoe]
      _ = 2 ^ n := hTcard
      _ = 2 ^ (2 * l) := by
          rw [← hcardGF]
          exact hl
  have hn2l : n = 2 * l := by
    apply Nat.pow_right_injective (by norm_num : 1 < 2)
    calc 2 ^ n = Fintype.card (GaloisField 2 n) := hcardGF.symm
      _ = 2 ^ (2 * l) := hl
  have hl1 : 1 ≤ l := by omega
  have hWcard : Nat.card W = 2 ^ (4 * l) := by
    obtain ⟨j, β, -⟩ := horth'
    have h1 : Nat.card W = Nat.card ↥(hermA l (GaloisField 2 n)) := by
      calc Nat.card W = Nat.card (Ch3z.chiefMod ⊥ W) :=
            Nat.card_congr (chiefModBotMulEquiv W).toEquiv
        _ = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
            (Nat.card_congr (Additive.ofMul : Ch3z.chiefMod ⊥ W ≃ Additive _)).symm
        _ = Nat.card ↥(hermA l (GaloisField 2 n)) := Nat.card_congr β.toEquiv
    rw [h1]
    exact card_hermA hl1 hl
  have hfixcard : Nat.card (fixedSub ρ A) = 2 ^ l := by
    exact IsOrthModule.card_fixedSub (hF := hl) horth' A hA2 hAcard
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨g, hgL1, hgborel⟩ := SetLike.exists_of_lt (F1.lt_borelOf hR)
  have hgB : g ∉ bigB L1 L2 S := by
    intro h
    apply hgborel
    have hmem : g ∈ L1 ⊓ bigB L1 L2 S := Subgroup.mem_inf.mpr ⟨hgL1, h⟩
    rwa [F1.inf_bigB_eq_borelOf hR] at hmem
  have hg : g ∈ L1 ⊔ S := (le_sup_left : L1 ≤ L1 ⊔ S) hgL1
  let E : Subgroup G := MulAut.conj g • u3Y L1 L2 S
  have hEsup : E ⊔ Q2 L1 L2 S = S := str86_u3Y_conj_sup_q2 hF hSB hk hFc hU3 hn hL2 hZQ hg hgB
  have hSleH : S ≤ H := str86_s_le_u3H hF.toW hSB hn hL2
  have hEH : E ≤ H := by
    have hEQ1 : E ≤ Q1 L1 L2 S := str86_u3Y_conj_le_q1 hg
    exact hEQ1.trans ((CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
      (f112_isSylowTwoOf_P1 hF.toW)).trans hSleH)
  have hEimg : CFSG.Quasithin.imageOTwoQuot H E = CFSG.Quasithin.imageOTwoQuot H S := by
    have h := CFSG.Quasithin.QA12.imageOTwoQuot_sup_pCoreOf (K := H) (X := E) hEH
    rw [str86_pCoreOf_u3H hF.toW, hEsup] at h
    exact h.symm
  let P : Subgroup ↥H := E.subgroupOf H
  have hPimg : (P.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom = A := by
    rw [show P = E.subgroupOf H from rfl]
    rw [show A = (T : Subgroup (oTwoQuot ↥H)).map e.toMonoidHom from rfl, hTcoe]
    rw [← hEimg]
    rfl
  have hPsub : (P.map H.subtype : Subgroup G) = E := by
    rw [show P = E.subgroupOf H from rfl, Subgroup.map_subgroupOf_eq_of_le hEH]
  have hfixcardE : Nat.card ↥(W ⊓ Subgroup.centralizer (E : Set G)) = 2 ^ l := by
    rw [← hPsub, ← fixSub_chiefMod_bot_card hstepW hUH hE e P, hPimg]
    change Nat.card ↥(fixedSub ρ A) = 2 ^ l
    exact hfixcard
  have hbound : (Z2 L1 L2 S ⊓ Subgroup.centralizer (E : Set G)).relIndex
      (Z2 L1 L2 S) ≤ 2 ^ k * 2 ^ n :=
    str86_u3Y_conj_centralizer_bound hF hSB hk hFc hU3 hn hL2 hZQ hg
  have hidx : (W ⊓ Subgroup.centralizer (E : Set G)).relIndex W ≤
      (Z2 L1 L2 S ⊓ Subgroup.centralizer (E : Set G)).relIndex (Z2 L1 L2 S) := by
    have h1 : (W ⊓ Subgroup.centralizer (E : Set G)) =
        (Z2 L1 L2 S ⊓ Subgroup.centralizer (E : Set G)) ⊓ W := by
      rw [inf_comm (W : Subgroup G), inf_assoc, inf_eq_right.mpr
        (show Subgroup.centralizer (E : Set G) ⊓ W ≤ Z2 L1 L2 S from
          inf_le_right.trans hWZ2)]
    rw [h1, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_right hWZ2 (D15Proof.relIndex_ne_zero _ _)
  have hrelcard : (W ⊓ Subgroup.centralizer (E : Set G)).relIndex W = 2 ^ (3 * l) := by
    have h := Subgroup.relIndex_mul_card (H := W ⊓ Subgroup.centralizer (E : Set G)) (K := W)
    rw [inf_eq_left.mpr inf_le_left, hfixcardE] at h
    rw [hWcard] at h
    have hpow : 2 ^ (4 * l) = 2 ^ (3 * l) * 2 ^ l := by
      rw [← pow_add]; ring_nf
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) l) h
  have hstep1 : 2 ^ (3 * l) ≤ 2 ^ k * 2 ^ n := hrelcard ▸ (hidx.trans hbound)
  have hlk_le : l ≤ k := by
    have h1 : 2 ^ (3 * l) ≤ 2 ^ (k + 2 * l) := by
      calc 2 ^ (3 * l) ≤ 2 ^ k * 2 ^ n := hstep1
        _ = 2 ^ (k + 2 * l) := by rw [hn2l, ← pow_add]
    have h2 : 3 * l ≤ k + 2 * l := Nat.pow_le_pow_iff_right (by norm_num) |>.mp h1
    have h3 : 3 * l = 2 * l + l := by ring
    omega
  have hqr : (2 ^ k) ^ 2 ≤ 2 ^ n := str86_q_sq_le_r hF hSB hk hFc hU3 hn hL2 hZQ
  have hk_le_l : k ≤ l := by
    have h1 : (2 ^ k) ^ 2 ≤ 2 ^ (2 * l) := by rwa [hn2l] at hqr
    have h2 : 2 ^ (2 * k) ≤ 2 ^ (2 * l) := by
      rwa [show (2 ^ k) ^ 2 = 2 ^ (2 * k) from by rw [← pow_mul]; ring] at h1
    have h3 : 2 * k ≤ 2 * l := Nat.pow_le_pow_iff_right (by norm_num) |>.mp h2
    omega
  have hlk : l = k := le_antisymm hlk_le hk_le_l
  refine ⟨by omega, ?_⟩
  rw [hWcard, hlk, ← pow_mul]
  ring_nf

end CFSG.Quasithin.Stroth
end
