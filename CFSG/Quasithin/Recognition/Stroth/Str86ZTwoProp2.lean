module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoProp
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoTrans2
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthH1

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type} [Group G] [Finite G]
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type} [Group G] [Finite G]

theorem str86_orth_case_z2_eq
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
    [Fintype (GaloisField 2 n)]
    {l : ℕ} (hl : Fintype.card (GaloisField 2 n) = 2 ^ (2 * l))
    (hn2l : n = 2 * l)
    (horth : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      IsOrthModule hl (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e)) :
    Z2 L1 L2 S = W := by
  classical
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have horth' : IsOrthModule hl ρ := horth
  let θ := chiefModBotMulEquiv W
  have hHnormZ : H ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  letI : CommGroup ↥(Z2 L1 L2 S) :=
    commGroupOfElemAbelian (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S))
  letI : H.Normalizes (Z2 L1 L2 S) := ⟨hHnormZ⟩
  letI : MulDistribMulAction ↥H ↥(Z2 L1 L2 S) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer H (Z2 L1 L2 S) hHnormZ
  have hWN : H ≤ Subgroup.normalizer (W : Set G) :=
    D14.le_normalizer_of_isNormalIn hstepW.1
  let v0 : ↥(Z2 L1 L2 S) := ⟨1, (Z2 L1 L2 S).one_mem⟩
  have hcoe (h : ↥H) (v : ↥(Z2 L1 L2 S)) :
      (((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) =
        (h : G) * (v : G) * (h : G)⁻¹ * (v : G)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  have hmem (h : ↥H) (v : ↥(Z2 L1 L2 S)) :
      (((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ W := by
    have hc := str86_commutator_mem_w hcomm h.2 v.2
    rwa [hcoe h v]
  let c : ↥(Z2 L1 L2 S) → ↥H → Additive (Ch3z.chiefMod ⊥ W) := fun v h =>
    Additive.ofMul (θ ⟨(((h • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h v⟩)
  have hc : ∀ (v : ↥(Z2 L1 L2 S)) (a b : ↥H),
      c v (a * b) = c v a + ρ (e (QuotientGroup.mk a)) (c v b) := by
    intro v a b
    dsimp only [c, ρ]
    rw [l2ChiefSectionRep_apply_mk]
    have hZeq : (a * b) • v * v⁻¹ =
        (a • v * v⁻¹) * (a • (b • v * v⁻¹)) := by
      rw [mul_smul, MulDistribMulAction.smul_mul, smul_inv']
      have h : a • v * v⁻¹ * (a • b • v * (a • v)⁻¹) = a • b • v * v⁻¹ := by
        calc a • v * v⁻¹ * (a • b • v * (a • v)⁻¹)
            = (a • v * (a • v)⁻¹) * (v⁻¹ * (a • b • v)) := by ac_rfl
          _ = 1 * (v⁻¹ * (a • b • v)) := by rw [mul_inv_cancel]
          _ = a • b • v * v⁻¹ := by rw [one_mul, mul_comm]
      rw [h]
    apply Additive.ofMul.injective
    change θ ⟨((((a * b) • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem (a*b) v⟩ =
      θ ⟨(((a • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem a v⟩ *
        l2ChiefSectionAction hstepW hE a
          (θ ⟨(((b • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem b v⟩)
    let wab : ↥W := ⟨((((a * b) • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem (a*b) v⟩
    let wa : ↥W := ⟨(((a • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem a v⟩
    let wb : ↥W := ⟨(((b • v) * v⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem b v⟩
    let wconj : ↥W := ⟨(a : G) * (wb : G) * (a : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hWN a.2) (wb : G)).mp wb.2⟩
    have hbase : l2ChiefSectionAction hstepW hE a (θ wb) = θ wconj :=
      chiefModBotMulEquiv_conj hstepW hUH hE a wb
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
        (A := H) (K := Z2 L1 L2 S) a ((b • v) * v⁻¹)).symm]
    simpa [wa] using congrArg Subtype.val hZeq
  have hker : ∀ (v : ↥(Z2 L1 L2 S)) (a : ↥H), e (QuotientGroup.mk a) = 1 → c v a = 0 := by
    intro v a ha
    have hmk : (QuotientGroup.mk a : oTwoQuot ↥H) = 1 := e.injective (by simpa using ha)
    have hmemQ : a ∈ pCore 2 ↥H := (QuotientGroup.eq_one_iff a).mp hmk
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
  have hlpos : 0 < l := by omega
  have hsurj : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥H))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hsub : Z2 L1 L2 S ≤ W := by
    intro v hv
    let vv : ↥(Z2 L1 L2 S) := ⟨v, hv⟩
    obtain ⟨w, hw⟩ := IsOrthModule.exists_eq_sub_of_cocycle_comp hl hlpos horth'
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥H))) hsurj (hc vv) (hker vv)
    let w0 : ↥W := θ.symm w.toMul
    have hw0 : Additive.ofMul (θ w0) = w := by
      rw [show θ w0 = w.toMul from θ.apply_symm_apply w.toMul]
      rfl
    let wZ : ↥(Z2 L1 L2 S) := ⟨w0, hWZ2 w0.2⟩
    have hmain : ∀ h : ↥H, (h • vv) * vv⁻¹ = (h • wZ) * wZ⁻¹ := by
      intro h
      have hh := hw h
      dsimp only [c] at hh
      rw [show (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥H))) h =
        e (QuotientGroup.mk h) from rfl] at hh
      let wconj : ↥W := ⟨(h : G) * (w0 : G) * (h : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hWN h.2) (w0 : G)).mp w0.2⟩
      have h1 : ρ (e (QuotientGroup.mk h)) w = Additive.ofMul (θ wconj) := by
        rw [← hw0]
        rw [l2ChiefSectionRep_apply_mk (hstep := hstepW) (hUH := q2_le_u3H L1 L2 S)
          (hE := hE) (e := e)]
        rw [chiefModBotMulEquiv_conj (hUH := q2_le_u3H L1 L2 S)]
      rw [h1] at hh
      have h2 : Additive.ofMul (θ wconj) - Additive.ofMul (θ w0) =
          Additive.ofMul (θ ⟨(((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h wZ⟩) := by
        rw [show Additive.ofMul (θ w0) =
          Additive.ofMul (θ ⟨(w0 : G), w0.2⟩) from rfl]
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
      rw [← hw0] at hh
      rw [h2] at hh
      have hh' : θ ⟨(((h • vv) * vv⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h vv⟩ =
          θ ⟨(((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h wZ⟩ :=
        Additive.ofMul.injective hh
      have hab : (⟨(((h • vv) * vv⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h vv⟩ : ↥W) =
          ⟨(((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G), hmem h wZ⟩ := θ.injective hh'
      have hval : (((h • vv) * vv⁻¹ : ↥(Z2 L1 L2 S)) : G) =
          (((h • wZ) * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) :=
        congrArg (fun x : ↥W => (x : G)) hab
      exact Subtype.ext hval
    have hfixall : ∀ h : ↥H, h • (vv * wZ⁻¹) = vv * wZ⁻¹ := by
      intro h
      have hh := hmain h
      have hsm : h • (vv * wZ⁻¹) = (h • vv) * (h • wZ)⁻¹ := by
        rw [MulDistribMulAction.smul_mul, smul_inv']
      rw [hsm]
      calc (h • vv) * (h • wZ)⁻¹
          = ((h • vv) * vv⁻¹) * (vv * (h • wZ)⁻¹) := by group
        _ = ((h • wZ) * wZ⁻¹) * (vv * (h • wZ)⁻¹) := by rw [hh]
        _ = vv * wZ⁻¹ := by
            calc ((h • wZ) * wZ⁻¹) * (vv * (h • wZ)⁻¹)
                = ((h • wZ) * (h • wZ)⁻¹) * (vv * wZ⁻¹) := by ac_rfl
              _ = vv * wZ⁻¹ := by rw [mul_inv_cancel, one_mul]
    have hcent : ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈
        Subgroup.centralizer ((H : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hhH
      have hfix := hfixall ⟨h, hhH⟩
      have hcoe' : (((⟨h, hhH⟩ : ↥H) • (vv * wZ⁻¹) : ↥(Z2 L1 L2 S)) : G) =
          h * ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) * h⁻¹ :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
          (A := H) (K := Z2 L1 L2 S) ⟨h, hhH⟩ (vv * wZ⁻¹)
      have hx : h * ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) * h⁻¹ =
          ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) := by
        rw [← hcoe', hfix]
      calc h * ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G)
          = (h * ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) * h⁻¹) * h := by group
        _ = ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) * h := by rw [hx]
    have hZ2C : Z2 L1 L2 S ⊓ Subgroup.centralizer ((H : Subgroup G) : Set G) = ⊥ := by
      rw [show H = u3H L1 L2 S from rfl]
      exact (str86_caseI_basics hF hSB ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
        hB2 ⟨n, hL2⟩ hZI).2.2.1
    have hmem_bot : (((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ (⊥ : Subgroup G)) := by
      have hmemZ : ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈ Z2 L1 L2 S := (vv * wZ⁻¹).2
      have hmemInf : ((vv * wZ⁻¹ : ↥(Z2 L1 L2 S)) : G) ∈
          Z2 L1 L2 S ⊓ Subgroup.centralizer ((H : Subgroup G) : Set G) :=
        Subgroup.mem_inf.mpr ⟨hmemZ, hcent⟩
      rwa [hZ2C, Subgroup.mem_bot] at hmemInf
    have h1 : vv * wZ⁻¹ = 1 := by
      apply Subtype.ext
      simpa using hmem_bot
    have h2 : vv = wZ := by
      calc vv = (vv * wZ⁻¹) * wZ := by group
        _ = 1 * wZ := by rw [h1]
        _ = wZ := one_mul wZ
    have hvW : (vv : G) ∈ W := by
      rw [h2]
      exact w0.2
    exact hvW
  exact le_antisymm hsub hWZ2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type} [Group G] [Finite G]

theorem str86_third_case_false
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
    (hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W))
    (e : oTwoQuot ↥(u3H L1 L2 S) ≃* SL(2, GaloisField 2 n))
    (T : Sylow 2 (oTwoQuot ↥(u3H L1 L2 S)))
    (hTcoe : (T : Subgroup (oTwoQuot ↥(u3H L1 L2 S))) =
      CFSG.Quasithin.imageOTwoQuot (u3H L1 L2 S) S)
    [Fintype (GaloisField 2 n)]
    {l : ℕ} (hn3l : n = 3 * l)
    (hWcard : Nat.card W = 2 ^ (8 * l))
    (hfixcard : letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
      Nat.card (CFSG.RankThree.FFModules.fixSub
        (l2ChiefSectionRep hstepW (q2_le_u3H L1 L2 S) hE e) (T.map e.toMonoidHom)) = 2 ^ l) :
    False := by
  classical
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  let A : Subgroup (SL(2, GaloisField 2 n)) := (T : Subgroup _).map e.toMonoidHom
  have hfixcard' : Nat.card (fixedSub ρ A) = 2 ^ l := hfixcard
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
    exact hfixcard'
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
  have hrelcard : (W ⊓ Subgroup.centralizer (E : Set G)).relIndex W = 2 ^ (7 * l) := by
    have h := Subgroup.relIndex_mul_card (H := W ⊓ Subgroup.centralizer (E : Set G)) (K := W)
    rw [inf_eq_left.mpr inf_le_left, hfixcardE] at h
    rw [hWcard] at h
    have hpow : 2 ^ (8 * l) = 2 ^ (7 * l) * 2 ^ l := by
      rw [← pow_add]; ring_nf
    rw [hpow] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) l) h
  have hstep1 : 2 ^ (7 * l) ≤ 2 ^ k * 2 ^ n := hrelcard ▸ (hidx.trans hbound)
  have h1 : 2 ^ (4 * l) ≤ 2 ^ k := by
    have h2 : 2 ^ (7 * l) ≤ 2 ^ (k + 3 * l) := by
      calc 2 ^ (7 * l) ≤ 2 ^ k * 2 ^ n := hstep1
        _ = 2 ^ (k + 3 * l) := by rw [hn3l, ← pow_add]
    have h3 : 7 * l ≤ k + 3 * l := Nat.pow_le_pow_iff_right (by norm_num) |>.mp h2
    have h4 : 7 * l = 4 * l + 3 * l := by ring
    have h5 : 4 * l ≤ k := by omega
    exact Nat.pow_le_pow_right (by norm_num) h5
  have hqr : (2 ^ k) ^ 2 ≤ 2 ^ n := str86_q_sq_le_r hF hSB hk hFc hU3 hn hL2 hZQ
  have h2 : 2 ^ (8 * l) ≤ 2 ^ (3 * l) := by
    calc 2 ^ (8 * l) = (2 ^ (4 * l)) ^ 2 := by rw [← pow_mul]; ring_nf
      _ ≤ (2 ^ k) ^ 2 := by exact Nat.pow_le_pow_left h1 2
      _ ≤ 2 ^ n := hqr
      _ = 2 ^ (3 * l) := by rw [hn3l]
  have h3 : 8 * l ≤ 3 * l := Nat.pow_le_pow_iff_right (by norm_num) |>.mp h2
  have hl1 : 1 ≤ l := by
    by_contra h
    have hl0 : l = 0 := by omega
    omega
  omega

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B45L2
open scoped Pointwise commutatorElement MatrixGroups
variable {G : Type} [Group G] [Finite G]

theorem str86_prop377
    {L1 L2 S : Subgroup G} {k : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (h2 : VL2 L2)
    (hZI : L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    IsL2Quot (2 * k) (oTwoQuot ↥L2) ∧
      Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4 ∧
      Nat.card (Z1 L1 L2 S) = 2 ^ k ∧
      Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3 := by
  classical
  obtain ⟨n, hL2⟩ := h2
  have hn : 2 ≤ n := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have h376 : Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2 :=
    str86_card_z2_le_sq hF hSB hk hFc hU3 hn hL2 hZQ hB2 hZI
  have h1 : VU3Big L1 := ⟨k, hk, F, inferInstance, inferInstance, hFc, hU3⟩
  obtain ⟨W, hWZ2, hstepW, hncW⟩ :=
    str86_exists_chiefStep_u3H hF hSB hk hFc hU3 hB2 ⟨n, hL2⟩ hZI
  have hcomm : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ = W :=
    str86_z2_commutator_eq_chief hF hSB hk hFc hU3 hn hL2 hZQ h376 hstepW hncW hWZ2
  let H := u3H L1 L2 S
  let hUH : Q2 L1 L2 S ≤ H := q2_le_u3H L1 L2 S
  have hE : IsElemAbelian 2 (Ch3z.chiefMod ⊥ W) :=
    isElemAbelian_chiefMod hstepW hUH (pCoreOf_isPGroup 2 (P2 L1 L2 S))
  letI : CommGroup (Ch3z.chiefMod ⊥ W) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod ⊥ W)) := l2ChiefSectionModule hE
  obtain ⟨e₀⟩ := str86_isL2Quot_u3H hF.toW hL2
  let e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 n) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 n))
  let ρ := l2ChiefSectionRep hstepW hUH hE e
  have hSleH : S ≤ H := str86_s_le_u3H hF.toW hSB hn hL2
  have hHP2 : H ≤ P2 L1 L2 S := u3H_le_p2 L1 L2 S
  have hSylH : IsSylowTwoOf S H :=
    CFSG.Quasithin.F7.isSylowTwoOf_mono_right (f112_isSylowTwoOf_P2 hF.toW) hSleH hHP2
  let Tsub : Subgroup (oTwoQuot ↥H) := CFSG.Quasithin.imageOTwoQuot H S
  have hT2 : IsPGroup 2 Tsub :=
    CFSG.Quasithin.Stroth.isPGroup_imageOTwoQuot_of_isSylow hSylH
  have hTidx : ¬ 2 ∣ Tsub.index :=
    CFSG.Quasithin.Stroth.not_two_dvd_index_imageOTwoQuot hSylH
  let T : Sylow 2 (oTwoQuot ↥H) := hT2.toSylow hTidx
  have hTcoe : (T : Subgroup (oTwoQuot ↥H)) = Tsub := IsPGroup.toSylow_coe hT2 hTidx
  let A : Subgroup (SL(2, GaloisField 2 n)) := (T : Subgroup _).map e.toMonoidHom
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← map_mul]
    have ht2 := (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).1 t ht
    rw [ht2, map_one]
  have hTcard : Nat.card ↥Tsub = 2 ^ n := by
    rw [← hTcoe]
    exact (l2Sylow_sq_mem hn (str86_isL2Quot_u3H hF.toW hL2) T).2
  have hAcard : Nat.card A = 2 ^ n := by
    calc Nat.card A = Nat.card ↥(T : Subgroup (oTwoQuot ↥H)) :=
          Subgroup.card_map_of_injective e.injective
      _ = Nat.card ↥Tsub := by rw [hTcoe]
      _ = 2 ^ n := hTcard
  have hnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstepW hUH hE e hncW
  have hirr : ρ.IsIrreducible := l2ChiefSectionRep_irreducible hstepW hUH hE e
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hWcardEq : Nat.card W = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) := by
    calc Nat.card W = Nat.card (Ch3z.chiefMod ⊥ W) :=
          Nat.card_congr (chiefModBotMulEquiv W).toEquiv
      _ = Nat.card (Additive (Ch3z.chiefMod ⊥ W)) :=
          Nat.card_congr (Additive.ofMul : Ch3z.chiefMod ⊥ W ≃ Additive _)
  have hWlt : Nat.card (Additive (Ch3z.chiefMod ⊥ W)) < 2 ^ (4 * n) := by
    rw [← hWcardEq]
    have hZle : Nat.card W ≤ Nat.card (Z2 L1 L2 S) := Subgroup.card_le_of_le hWZ2
    have hZ3 : Nat.card (Z2 L1 L2 S) ≤ 2 ^ (3 * n) := by
      have := str86_card_z2_le hF hSB hk hFc hU3 hn hL2 hZQ h376
      simpa [pow_mul, mul_comm] using this
    have hlt : 3 * n < 4 * n := by omega
    exact lt_of_le_of_lt (hZle.trans hZ3) (Nat.pow_lt_pow_right (by norm_num) hlt)
  have hcardGF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 n (by omega)
  have htri := isNaturalModule_or_isOrthModule_or_of_card_lt (by omega) hcardGF
    ρ hnt A hA2 hAcard hWlt
  rcases htri with hnat | ⟨l, hl, hn2l, horth⟩ | ⟨l, hn3l, hWcard3, hfix3⟩
  · exact (str86_natural_case_false hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376
      hstepW hncW hWZ2 hcomm hE e T hTcoe hnat).elim
  · have hcards := str86_orth_case_cards hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376
      hstepW hncW hWZ2 hcomm hE e T hTcoe hl horth
    have hn2k : n = 2 * k := hcards.1
    have hWcard : Nat.card W = (2 ^ k) ^ 4 := hcards.2
    have hZ2W : Z2 L1 L2 S = W :=
      str86_orth_case_z2_eq hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376 hstepW hncW
        hWZ2 hcomm hE e hl hn2l horth
    have hcardZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4 := by rw [hZ2W, hWcard]
    have hlk : l = k := by omega
    have hfixS : Nat.card (fixedSub ρ A) = 2 ^ l :=
      IsOrthModule.card_fixedSub (hF := hl) horth A hA2 (by rw [hAcard, hn2l])
    have hZ1eq : Z1 L1 L2 S = Z2 L1 L2 S ⊓ Subgroup.centralizer (S : Set G) :=
      (str86_caseI_basics hF hSB h1 hB2 ⟨n, hL2⟩ hZI).2.2.2.2.symm
    have hfixScard : Nat.card ↥(W ⊓ Subgroup.centralizer (S : Set G)) = 2 ^ l := by
      let P2 : Subgroup ↥H := S.subgroupOf H
      have hP2img : (P2.map (QuotientGroup.mk' (pCore 2 ↥H))).map e.toMonoidHom = A := by
        rw [show P2 = S.subgroupOf H from rfl]
        rw [show A = (T : Subgroup (oTwoQuot ↥H)).map e.toMonoidHom from rfl, hTcoe]
        rfl
      have hP2sub : (P2.map H.subtype : Subgroup G) = S := by
        rw [show P2 = S.subgroupOf H from rfl, Subgroup.map_subgroupOf_eq_of_le hSleH]
      rw [← hP2sub, ← fixSub_chiefMod_bot_card hstepW hUH hE e P2, hP2img]
      change Nat.card ↥(fixedSub ρ A) = 2 ^ l
      exact hfixS
    have hcardZ1 : Nat.card (Z1 L1 L2 S) = 2 ^ k := by
      rw [hZ1eq, hZ2W, hfixScard, hlk]
    obtain ⟨X0, -, -, -, -, hYrel⟩ := str86_z2_sup_q1_eq_X0 hF hSB hk hFc hU3 hZQ
    have hYcard : Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S) = (2 ^ k) ^ 3 := by
      have hmul := Subgroup.relIndex_mul_card
        (H := Z2 L1 L2 S ⊓ Q1 L1 L2 S) (K := Z2 L1 L2 S)
      rw [inf_eq_left.mpr inf_le_left] at hmul
      have hrel : (Z2 L1 L2 S ⊓ Q1 L1 L2 S).relIndex (Z2 L1 L2 S) = 2 ^ k := hYrel
      rw [hrel, hcardZ2] at hmul
      have hpow : (2 ^ k) ^ 4 = (2 ^ k) ^ 3 * 2 ^ k := by ring
      rw [hpow] at hmul
      rw [mul_comm (2 ^ k) (Nat.card ↥(Z2 L1 L2 S ⊓ Q1 L1 L2 S))] at hmul
      exact Nat.eq_of_mul_eq_mul_right (m := 2 ^ k) (pow_pos (by norm_num) k) hmul
    exact ⟨by rwa [hn2k] at hL2, hcardZ2, hcardZ1, hYcard⟩
  · have hWcard3' : Nat.card W = 2 ^ (8 * l) := by
      rw [hWcardEq]
      exact hWcard3
    exact (str86_third_case_false hF hSB hk hFc hU3 hn hL2 hB2 hZI hZQ h376
      hstepW hncW hWZ2 hE e T hTcoe hn3l hWcard3' hfix3).elim
end CFSG.Quasithin.Stroth
end
