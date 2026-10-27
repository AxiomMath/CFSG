module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoProp
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthH1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

private theorem p10s_cocycle_mem_w {L1 L2 S W : Subgroup G}
    (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W) :
    letI : CommGroup ↥(Z2 L1 L2 S) :=
      commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
    letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
      ⟨str86_z2_normal_u3H L1 L2 S⟩
    letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
        (str86_z2_normal_u3H L1 L2 S)
    ∀ (h : ↥(u3H L1 L2 S)) (v : ↥(Z2 L1 L2 S)),
      (((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ W := by
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
    ⟨str86_z2_normal_u3H L1 L2 S⟩
  letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
      (str86_z2_normal_u3H L1 L2 S)
  intro h v
  have hcoe : (((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) =
      (h : G) * (v : G) * (h : G)⁻¹ * (v : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  rw [hcoe]
  exact str86_commutator_mem_w hcomm h.2 v.2

private theorem p10s_smul_cocycle {L1 L2 S : Subgroup G}
    (a b : ↥(u3H L1 L2 S)) (v : ↥(Z2 L1 L2 S)) :
    letI : CommGroup ↥(Z2 L1 L2 S) :=
      commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
    letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
      ⟨str86_z2_normal_u3H L1 L2 S⟩
    letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
        (str86_z2_normal_u3H L1 L2 S)
    (a * b) • v * v⁻¹ = (a • v * v⁻¹) * (a • (b • v * v⁻¹)) := by
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
    ⟨str86_z2_normal_u3H L1 L2 S⟩
  letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
      (str86_z2_normal_u3H L1 L2 S)
  rw [mul_smul, MulDistribMulAction.smul_mul, smul_inv']
  have h : a • v * v⁻¹ * (a • b • v * (a • v)⁻¹) = a • b • v * v⁻¹ := by
    calc a • v * v⁻¹ * (a • b • v * (a • v)⁻¹)
        = (a • v * (a • v)⁻¹) * (v⁻¹ * (a • b • v)) := by ac_rfl
      _ = 1 * (v⁻¹ * (a • b • v)) := by rw [mul_inv_cancel]
      _ = a • b • v * v⁻¹ := by rw [one_mul, mul_comm]
  rw [h]

private theorem p10s_cocycle {L1 L2 S W : Subgroup G} {m : ℕ}
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    letI : CommGroup ↥(Z2 L1 L2 S) :=
      commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
    letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
      ⟨str86_z2_normal_u3H L1 L2 S⟩
    letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
        (str86_z2_normal_u3H L1 L2 S)
    ∀ (hmem : ∀ (h : ↥(u3H L1 L2 S)) (v : ↥(Z2 L1 L2 S)),
      (((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ W),
    let c : ↥(Z2 L1 L2 S) → ↥(u3H L1 L2 S) → Additive (Ch3z.chiefMod ⊥ W) := fun v h =>
      Additive.ofMul (chiefModBotMulEquiv W
        ⟨(((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h v⟩)
    ∀ (v : ↥(Z2 L1 L2 S)) (a b : ↥(u3H L1 L2 S)),
      c v (a * b) = c v a +
        l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e
          (e (QuotientGroup.mk a)) (c v b) := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
    ⟨str86_z2_normal_u3H L1 L2 S⟩
  letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
      (str86_z2_normal_u3H L1 L2 S)
  let θ := chiefModBotMulEquiv W
  have hWN : u3H L1 L2 S ≤ Subgroup.normalizer (W : Set G) :=
    D14.le_normalizer_of_isNormalIn hstepW.1
  intro hmem c v a b
  dsimp only [c]
  rw [l2ChiefSectionRep_apply_mk]
  have hZeq := p10s_smul_cocycle a b v
  apply Additive.ofMul.injective
  let wab : ↥W := ⟨((((a * b) • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem (a * b) v⟩
  let wa : ↥W := ⟨(((a • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem a v⟩
  let wb : ↥W := ⟨(((b • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem b v⟩
  let wconj : ↥W := ⟨(a : G) * (wb : G) * (a : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hWN a.2) (wb : G)).mp wb.2⟩
  have hbase : l2ChiefSectionAction hstepW hE a (θ wb) = θ wconj :=
    chiefModBotMulEquiv_conj hstepW (q2_le_u3H L1 L2 S) hE a wb
  change θ wab = θ wa * l2ChiefSectionAction hstepW hE a (θ wb)
  rw [hbase]
  have hmul : θ wa * θ wconj = θ (wa * wconj) := (map_mul θ wa wconj).symm
  rw [hmul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  change ((((a * b) • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) =
    (((a • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) * ((a : G) * (wb : G) * (a : G)⁻¹)
  rw [show (a : G) * (wb : G) * (a : G)⁻¹ =
    (((a • ((b • v) * v⁻¹) : ↥(Z2 L1 L2 S))) : G) from
    (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
      (A := u3H L1 L2 S) (K := Z2 L1 L2 S) a ((b • v) * v⁻¹)).symm]
  simpa [wa] using congrArg Subtype.val hZeq

private theorem p10s_kernel {L1 L2 S W : Subgroup G} {m : ℕ}
    (hF : F112Hyp L1 L2 S)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    letI : CommGroup ↥(Z2 L1 L2 S) :=
      commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
    letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
      ⟨str86_z2_normal_u3H L1 L2 S⟩
    letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
        (str86_z2_normal_u3H L1 L2 S)
    ∀ (hmem : ∀ (h : ↥(u3H L1 L2 S)) (v : ↥(Z2 L1 L2 S)),
      (((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ W),
    let c : ↥(Z2 L1 L2 S) → ↥(u3H L1 L2 S) → Additive (Ch3z.chiefMod ⊥ W) := fun v h =>
      Additive.ofMul (chiefModBotMulEquiv W
        ⟨(((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h v⟩)
    ∀ (v : ↥(Z2 L1 L2 S)) (a : ↥(u3H L1 L2 S)),
      e (QuotientGroup.mk a) = 1 → c v a = 0 := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
    ⟨str86_z2_normal_u3H L1 L2 S⟩
  letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
      (str86_z2_normal_u3H L1 L2 S)
  let θ := chiefModBotMulEquiv W
  intro hmem c v a ha
  have hmk : (QuotientGroup.mk a : oTwoQuot ↥(u3H L1 L2 S)) = 1 :=
    e.injective (by simpa using ha)
  have hmemQ : a ∈ pCore 2 ↥(u3H L1 L2 S) := (QuotientGroup.eq_one_iff a).mp hmk
  have haQ : (a : G) ∈ Q2 L1 L2 S := by
    have := (F1.mem_pCore_iff_coe a).mp hmemQ
    rwa [str86_pCoreOf_u3H hF.toW] at this
  have hact0 : a • v = v := by
    apply Subtype.ext
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hc : (a : G) * (v : G) = (v : G) * (a : G) :=
      (Subgroup.mem_centralizer_iff.mp
        (SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) haQ) v v.2).symm
    calc (a : G) * (v : G) * (a : G)⁻¹ = ((v : G) * (a : G)) * (a : G)⁻¹ := by rw [hc]
      _ = (v : G) := by group
  change Additive.ofMul (θ ⟨(((a • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem a v⟩) = 0
  have hv1 : ((a • v) * v⁻¹ : ↥(Z2 L1 L2 S)) = 1 := by
    rw [hact0, mul_inv_cancel]
  have hone : (⟨(((a • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem a v⟩ : ↥W) = 1 := by
    apply Subtype.ext
    simpa using congrArg (fun x : ↥(Z2 L1 L2 S) => (x : G)) hv1
  have h1 : θ ⟨(((a • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem a v⟩ = 1 := by
    rw [hone, map_one]
  exact congrArg Additive.ofMul h1

private theorem p10s_exists_w {L1 L2 S W : Subgroup G} {m l : ℕ}
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    [Fintype (GaloisField 2 m)]
    (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hlpos : 0 < l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    letI : CommGroup ↥(Z2 L1 L2 S) :=
      commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
    letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
      ⟨str86_z2_normal_u3H L1 L2 S⟩
    letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
        (str86_z2_normal_u3H L1 L2 S)
    ∀ (c : ↥(Z2 L1 L2 S) → ↥(u3H L1 L2 S) → Additive (Ch3z.chiefMod ⊥ W)),
      (∀ (v : ↥(Z2 L1 L2 S)) (a b : ↥(u3H L1 L2 S)), c v (a * b) = c v a +
        l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e
          (e (QuotientGroup.mk a)) (c v b)) →
      (∀ (v : ↥(Z2 L1 L2 S)) (a : ↥(u3H L1 L2 S)),
        e (QuotientGroup.mk a) = 1 → c v a = 0) →
      ∀ v : ↥(Z2 L1 L2 S), ∃ w : Additive (Ch3z.chiefMod ⊥ W),
        ∀ a : ↥(u3H L1 L2 S), c v a =
          l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e
            (e (QuotientGroup.mk a)) w - w := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
    ⟨str86_z2_normal_u3H L1 L2 S⟩
  letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
      (str86_z2_normal_u3H L1 L2 S)
  intro c hc hker v
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥(u3H L1 L2 S)))
  have hsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨w, hw⟩ := IsOrthModule.exists_eq_sub_of_cocycle_comp hl hlpos horth π hsurj
    (hc v) (hker v)
  refine ⟨w, fun a => ?_⟩
  have hwa := hw a
  rw [show π a = e (QuotientGroup.mk a) from rfl] at hwa
  exact hwa

private theorem p10s_eq_of_coboundary {L1 L2 S W : Subgroup G} {m : ℕ}
    (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m))
    (hWZ2 : W ≤ Z2 L1 L2 S) :
    letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
    letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
    letI : CommGroup ↥(Z2 L1 L2 S) :=
      commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
    letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
      ⟨str86_z2_normal_u3H L1 L2 S⟩
    letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
        (str86_z2_normal_u3H L1 L2 S)
    ∀ (hmem : ∀ (h : ↥(u3H L1 L2 S)) (v : ↥(Z2 L1 L2 S)),
        (((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ W)
      (c : ↥(Z2 L1 L2 S) → ↥(u3H L1 L2 S) → Additive (Ch3z.chiefMod ⊥ W))
      (v : ↥(Z2 L1 L2 S)) (w0 : ↥W),
      (∀ h : ↥(u3H L1 L2 S), c v h =
        Additive.ofMul (chiefModBotMulEquiv W
          ⟨(((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h v⟩)) →
      (∀ h : ↥(u3H L1 L2 S), c v h =
        l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e (e (QuotientGroup.mk h))
          (Additive.ofMul (chiefModBotMulEquiv W w0)) -
        Additive.ofMul (chiefModBotMulEquiv W w0)) →
      let wZ : ↥(Z2 L1 L2 S) := ⟨w0, hWZ2 w0.2⟩
      ∀ h : ↥(u3H L1 L2 S), (h • v) * v⁻¹ = (h • wZ) * wZ⁻¹ := by
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
    ⟨str86_z2_normal_u3H L1 L2 S⟩
  letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
      (str86_z2_normal_u3H L1 L2 S)
  let θ := chiefModBotMulEquiv W
  have hWN : u3H L1 L2 S ≤ Subgroup.normalizer (W : Set G) :=
    D14.le_normalizer_of_isNormalIn hstepW.1
  intro hmem c v w0 hcdef hw wZ h
  have hh := hw h
  let wconj : ↥W := ⟨(h : G) * (w0 : G) * (h : G)⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hWN h.2) (w0 : G)).mp w0.2⟩
  have h1 : l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e
      (e (QuotientGroup.mk h)) (Additive.ofMul (θ w0)) = Additive.ofMul (θ wconj) := by
    rw [l2ChiefSectionRep_apply_mk (hstep := hstepW) (hUH := q2_le_u3H L1 L2 S)
      (hE := hE) (e := e)]
    rw [chiefModBotMulEquiv_conj (hUH := q2_le_u3H L1 L2 S)]
  rw [h1] at hh
  have h2 : Additive.ofMul (θ wconj) - Additive.ofMul (θ w0) =
      Additive.ofMul (θ ⟨(((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h wZ⟩) := by
    rw [show Additive.ofMul (θ w0) = Additive.ofMul (θ ⟨(w0 : G), w0.2⟩) from rfl]
    rw [sub_eq_add_neg]
    rw [show -Additive.ofMul (θ ⟨(w0 : G), w0.2⟩) =
      Additive.ofMul ((θ ⟨(w0 : G), w0.2⟩)⁻¹) from rfl]
    have hmul : θ wconj * (θ ⟨(w0 : G), w0.2⟩)⁻¹ =
        θ (wconj * ⟨(w0 : G), w0.2⟩⁻¹) := by
      rw [← map_inv, ← map_mul]
    change Additive.ofMul (θ wconj * (θ ⟨(w0 : G), w0.2⟩)⁻¹) =
      Additive.ofMul (θ ⟨(((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h wZ⟩)
    rw [hmul]
    congr 1
  rw [h2] at hh
  have hh' : θ ⟨(((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h v⟩ =
      θ ⟨(((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h wZ⟩ := by
    apply Additive.ofMul.injective
    rw [← hcdef h]
    exact hh
  have hab : (⟨(((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h v⟩ : ↥W) =
      ⟨(((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h wZ⟩ := θ.injective hh'
  have hval : (((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) =
      (((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) :=
    congrArg (fun x : ↥W => (x : G)) hab
  exact Subtype.ext hval

private theorem p10s_fixed_of_eq {L1 L2 S : Subgroup G}
    (v wZ : ↥(Z2 L1 L2 S)) :
    letI : CommGroup ↥(Z2 L1 L2 S) :=
      commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
    letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
      ⟨str86_z2_normal_u3H L1 L2 S⟩
    letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
        (str86_z2_normal_u3H L1 L2 S)
    (∀ h : ↥(u3H L1 L2 S), (h • v) * v⁻¹ = (h • wZ) * wZ⁻¹) →
    ∀ h : ↥(u3H L1 L2 S), h • (v * wZ⁻¹) = v * wZ⁻¹ := by
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
    ⟨str86_z2_normal_u3H L1 L2 S⟩
  letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
      (str86_z2_normal_u3H L1 L2 S)
  intro hmain h
  have hh := hmain h
  have hsm : h • (v * wZ⁻¹) = (h • v) * (h • wZ)⁻¹ := by
    rw [MulDistribMulAction.smul_mul, smul_inv']
  rw [hsm]
  calc (h • v) * (h • wZ)⁻¹
      = ((h • v) * v⁻¹) * (v * (h • wZ)⁻¹) := by group
    _ = ((h • wZ) * wZ⁻¹) * (v * (h • wZ)⁻¹) := by rw [hh]
    _ = v * wZ⁻¹ := by
        calc ((h • wZ) * wZ⁻¹) * (v * (h • wZ)⁻¹)
            = ((h • wZ) * (h • wZ)⁻¹) * (v * wZ⁻¹) := by ac_rfl
          _ = v * wZ⁻¹ := by rw [mul_inv_cancel, one_mul]

private theorem p10s_mem_of_fixed
    {L1 L2 S W : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (v wZ : ↥(Z2 L1 L2 S)) :
    letI : CommGroup ↥(Z2 L1 L2 S) :=
      commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
    letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
      ⟨str86_z2_normal_u3H L1 L2 S⟩
    letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
        (str86_z2_normal_u3H L1 L2 S)
    (wZ : G) ∈ W →
    (∀ h : ↥(u3H L1 L2 S), h • (v * wZ⁻¹) = v * wZ⁻¹) →
    (v : G) ∈ W := by
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : (u3H L1 L2 S).Normalizes (Z2 L1 L2 S) :=
    ⟨str86_z2_normal_u3H L1 L2 S⟩
  letI : MulDistribMulAction ↥(u3H L1 L2 S) ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (u3H L1 L2 S) (Z2 L1 L2 S)
      (str86_z2_normal_u3H L1 L2 S)
  intro hwZ hfixall
  have hcent : ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈
      Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hhH
    have hfix := hfixall ⟨h, hhH⟩
    have hcoe' : (((⟨h, hhH⟩ : ↥(u3H L1 L2 S)) • (v * wZ⁻¹) : ↥(Z2 L1 L2 S)) : G) =
        h * ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) * h⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
        (A := u3H L1 L2 S) (K := Z2 L1 L2 S) ⟨h, hhH⟩ (v * wZ⁻¹)
    have hx : h * ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) * h⁻¹ =
        ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) := by
      rw [← hcoe', hfix]
    calc h * ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G)
        = (h * ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) * h⁻¹) * h := by group
      _ = ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) * h := by rw [hx]
  have hZ2C : Z2 L1 L2 S ⊓
      Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) = ⊥ :=
    (str86_caseI_basics hF hSB ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
      hB2 ⟨m, hL2⟩ hZI).2.2.1
  have hmem_bot : (((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ (⊥ : Subgroup G)) := by
    have hmemZ : ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ Z2 L1 L2 S := (v * wZ⁻¹).2
    have hmemInf : ((v * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈
        Z2 L1 L2 S ⊓ Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hmemZ, hcent⟩
    rwa [hZ2C, Subgroup.mem_bot] at hmemInf
  have h1 : v * wZ⁻¹ = 1 := by
    apply Subtype.ext
    simpa using hmem_bot
  have h2 : v = wZ := by
    calc v = (v * wZ⁻¹) * wZ := by group
      _ = 1 * wZ := by rw [h1]
      _ = wZ := one_mul wZ
  rw [h2]
  exact hwZ

theorem str86_orth_z2_eq_commutator
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : 2 ≤ m) (hL2 : IsL2Quot m (oTwoQuot ↥L2))
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    {W : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hWZ2 : W ≤ Z2 L1 L2 S) (hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W)
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 m)) [Fintype (GaloisField 2 m)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 m) = 2 ^ (2 * l)) (hml : m = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    Z2 L1 L2 S = W := by
  classical
  let H := u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let θ := chiefModBotMulEquiv W
  have hHnormZ : H ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : H.Normalizes (Z2 L1 L2 S) := ⟨hHnormZ⟩
  letI : MulDistribMulAction ↥H ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer H (Z2 L1 L2 S) hHnormZ
  have hmem := p10s_cocycle_mem_w hcomm
  let c : ↥(Z2 L1 L2 S) → ↥H → Additive (Ch3z.chiefMod ⊥ W) := fun v h =>
    Additive.ofMul (θ ⟨(((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h v⟩)
  have hc := p10s_cocycle hstepW hE e hmem
  have hker := p10s_kernel hF hE e hmem
  have hlpos : 0 < l := by omega
  have hsub : Z2 L1 L2 S ≤ W := by
    intro v hv
    let vv : ↥(Z2 L1 L2 S) := ⟨v, hv⟩
    obtain ⟨w, hw⟩ := p10s_exists_w hstepW hE e hl hlpos horth c hc hker vv
    let w0 : ↥W := θ.symm w.toMul
    have hw0 : Additive.ofMul (θ w0) = w := by
      rw [show θ w0 = w.toMul from θ.apply_symm_apply w.toMul]
      rfl
    have hw' : ∀ h : ↥(u3H L1 L2 S), c vv h =
        l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e (e (QuotientGroup.mk h))
          (Additive.ofMul (θ w0)) - Additive.ofMul (θ w0) := by
      intro h
      rw [hw h, ← hw0]
    let wZ : ↥(Z2 L1 L2 S) := ⟨w0, hWZ2 w0.2⟩
    have hmain : ∀ h : ↥H, (h • vv) * vv⁻¹ = (h • wZ) * wZ⁻¹ :=
      p10s_eq_of_coboundary hstepW hE e hWZ2 hmem c vv w0 (fun _ => rfl) hw'
    have hfix := p10s_fixed_of_eq vv wZ hmain
    exact p10s_mem_of_fixed hF hSB hk hFc hU3 hB2 hL2 hZI vv wZ
      (by simpa [wZ] using w0.2) hfix
  exact le_antisymm hsub hWZ2

end CFSG.Quasithin.Stroth

end
