module

public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth2
public import CFSG.GroupTheory.GroupAction.CoprimeSeriesTrivial

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin

variable {G : Type*} [Group G] [Finite G]

theorem commutator_mem_of_odd_of_central_chief {H Q Z W : Subgroup G}
    (hQH : Q ≤ H) (hZQ : Z ≤ Q) (hWZ : W ≤ Z) (hZ2 : IsPGroup 2 Z)
    (hZN : H ≤ Subgroup.normalizer (Z : Set G))
    (hWNorm : H ≤ Subgroup.normalizer (W : Set G))
    (hWn : IsNormalIn H Q W)
    (hcen : ∀ L N : Subgroup G, IsChiefStep H Q L N → W ≤ L → N ≤ Z →
      IsCentralStep H L N)
    {a : G} (haH : a ∈ H) (haodd : Odd (orderOf a)) :
    ∀ x ∈ Z, a * x * a⁻¹ * x⁻¹ ∈ W := by
  classical
  have hZnorm : IsNormalIn H Q Z :=
    ⟨hZQ, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hZN hg) x).mp hx⟩
  have hmain : ∀ n : ℕ, ∀ L : Subgroup G, Nat.card L = n → IsNormalIn H Q L →
      W ≤ L → L ≤ Z → ∀ x ∈ L, a * x * a⁻¹ * x⁻¹ ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro L hcard hLN hWL hLZ x hx
      by_cases hLW : L = W
      · rw [hLW] at hx
        have hax : a * x * a⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hWNorm haH) x).mp hx
        exact W.mul_mem hax (W.inv_mem hx)
      · have hWLlt : W < L := lt_of_le_of_ne hWL (fun hW => hLW hW.symm)
        let s : Set (Subgroup G) := {M | IsNormalIn H Q M ∧ W ≤ M ∧ M < L}
        have hsne : s.Nonempty := ⟨W, hWn, le_rfl, hWLlt⟩
        obtain ⟨M, hM⟩ := (Set.toFinite s).exists_maximalFor
          (fun M : Subgroup G => Nat.card M) s hsne
        have hMN : IsNormalIn H Q M := hM.1.1
        have hWM : W ≤ M := hM.1.2.1
        have hMLt : M < L := hM.1.2.2
        have hML : M ≤ L := hMLt.le
        have hMZ : M ≤ Z := hML.trans hLZ
        have hstep : IsChiefStep H Q M L := by
          refine ⟨hLN, hMN, hMLt, ?_⟩
          intro K hK hMK hKL
          by_cases hKL' : K = L
          · exact Or.inr hKL'
          · left
            have hKlt : K < L := lt_of_le_of_ne hKL hKL'
            have hKs : K ∈ s := ⟨hK, hWM.trans hMK, hKlt⟩
            have hcardK : Nat.card K ≤ Nat.card M := hM.le hKs
            exact (Subgroup.eq_of_le_of_card_ge hMK hcardK).symm
        have hcenML : IsCentralStep H M L := hcen M L hstep hWM hLZ
        have hMlt : Nat.card M < n := by
          rw [← hcard]
          exact Subgroup.card_lt_of_lt hMLt
        have hIHM : ∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ W := fun m hm =>
          ih (Nat.card M) hMlt M rfl hMN hWM hMZ m hm
        let A := Subgroup.zpowers a
        have hAH : A ≤ H := Subgroup.zpowers_le.mpr haH
        have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
          hAH.trans (D14.le_normalizer_of_isNormalIn hLN)
        haveI : Subgroup.Normalizes A L := ⟨hAL⟩
        have hoddA : Odd (Nat.card ↥A) := by
          rw [Nat.card_zpowers]
          exact haodd
        have hL2 : IsPGroup 2 ↥L := hZ2.to_le hLZ
        have hsm : ∀ (z : ↥A) (y : ↥L), ((z • y : ↥L) : G) = (z : G) * (y : G) * (z : G)⁻¹ :=
          fun z y =>
            (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe A L z y).symm
        have hWLnorm : (W.subgroupOf L).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mpr
            (((hLZ.trans hZQ).trans hQH).trans hWNorm)
        have hMLnorm : (M.subgroupOf L).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hML).mpr
            (((hLZ.trans hZQ).trans hQH).trans
              (D14.le_normalizer_of_isNormalIn hMN))
        haveI : (W.subgroupOf L).Normal := hWLnorm
        haveI : (M.subgroupOf L).Normal := hMLnorm
        have hWM' : W.subgroupOf L ≤ M.subgroupOf L := by
          intro y hy
          rw [Subgroup.mem_subgroupOf] at hy ⊢
          exact hWM hy
        have hW'inv : CFSG.IsInvariant ↥A ↥L (W.subgroupOf L) := by
          refine ⟨fun z y => ?_⟩
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          change (y : G) ∈ W ↔ ((z • y : ↥L) : G) ∈ W
          rw [hsm]
          exact Subgroup.mem_normalizer_iff.mp (hWNorm (hAH z.2)) (y : G)
        have hM'inv : CFSG.IsInvariant ↥A ↥L (M.subgroupOf L) := by
          refine ⟨fun z y => ?_⟩
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          change (y : G) ∈ M ↔ ((z • y : ↥L) : G) ∈ M
          rw [hsm]
          exact Subgroup.mem_normalizer_iff.mp
            ((D14.le_normalizer_of_isNormalIn hMN) (hAH z.2)) (y : G)
        have hMA : ∀ z ∈ A, ∀ m ∈ M, z * m * z⁻¹ * m⁻¹ ∈ W :=
          commutator_zpowers_le_of_mem_commutator (hWNorm haH) hIHM
        have hWN_triv : ∀ z : ↥A, ∀ m : ↥L, m ∈ M.subgroupOf L →
            (z • m) * m⁻¹ ∈ W.subgroupOf L := by
          intro z m hm
          rw [Subgroup.mem_subgroupOf] at hm ⊢
          have hcoe : (((z • m) * m⁻¹ : ↥L) : G) =
              ((z : G) * (m : G) * (z : G)⁻¹) * (m : G)⁻¹ := by
            rw [Subgroup.coe_mul, Subgroup.coe_inv, hsm]
          rw [hcoe]
          exact hMA (z : G) z.2 (m : G) hm
        have hNQ_triv : ∀ z : ↥A, ∀ y : ↥L,
            (z • y) * y⁻¹ ∈ M.subgroupOf L := by
          intro z y
          rw [Subgroup.mem_subgroupOf]
          have hcoe : (((z • y) * y⁻¹ : ↥L) : G) =
              ((z : G) * (y : G) * (z : G)⁻¹) * (y : G)⁻¹ := by
            rw [Subgroup.coe_mul, Subgroup.coe_inv, hsm]
          rw [hcoe]
          exact hcenML (z : G) (hAH z.2) (y : G) y.2
        have htriv := coprime_action_trivial_mod_of_fixed_normal_and_quotient
          (A := ↥A) (G := ↥L) hoddA hL2 (W.subgroupOf L) (M.subgroupOf L)
          hWM' hW'inv hM'inv hWN_triv hNQ_triv
        have hxL : x ∈ L := hx
        have hres := htriv ⟨a, Subgroup.mem_zpowers a⟩ ⟨x, hxL⟩
        rw [Subgroup.mem_subgroupOf] at hres
        have hcoe : ((((⟨a, Subgroup.mem_zpowers a⟩ : ↥A) • (⟨x, hxL⟩ : ↥L)) *
            (⟨x, hxL⟩ : ↥L)⁻¹ : ↥L) : G) = a * x * a⁻¹ * x⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, hsm]
        rwa [hcoe] at hres
  exact hmain (Nat.card Z) Z rfl hZnorm hWZ le_rfl

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_chiefStep_central
    {L1 L2 S : Subgroup G} {k n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hn : 2 ≤ n) (hL2 : IsL2Quot n (oTwoQuot ↥L2))
    (hZQ : ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S)
    (h376 : Nat.card (Z2 L1 L2 S) ≤ (2 ^ k * 2 ^ n) ^ 2)
    {W M L : Subgroup G} (hstepW : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) ⊥ W)
    (hncW : ¬ IsCentralStep (u3H L1 L2 S) ⊥ W)
    (hstep : IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) M L) (hWM : W ≤ M)
    (hLZ : L ≤ Z2 L1 L2 S) : IsCentralStep (u3H L1 L2 S) M L := by
  classical
  by_contra hnc
  have hMrel : (2 ^ n) ^ 2 ≤ M.relIndex L :=
    str86_card_chiefStep_ge hF.toW hn hL2 hstep hnc
  have hWcard : (2 ^ n) ^ 2 ≤ Nat.card W := by
    have h := str86_card_chiefStep_ge hF.toW hn hL2 hstepW hncW
    rwa [Subgroup.relIndex_bot_left] at h
  have hML : M ≤ L := hstep.2.2.1.le
  have hWleL : W ≤ L := hWM.trans hML
  have hcardL : Nat.card L = Nat.card W * W.relIndex L := by
    have h := Subgroup.relIndex_mul_card W L
    rw [inf_eq_left.mpr hWleL] at h
    rw [← h]
    ring
  have hrel : W.relIndex L = W.relIndex M * M.relIndex L :=
    (Subgroup.relIndex_mul_relIndex (H := W) (K := M) (L := L) hWM hML).symm
  have h1 : M.relIndex L ≤ W.relIndex L := by
    rw [hrel]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero W M))
  have hge : (2 ^ n) ^ 4 ≤ Nat.card L := by
    calc (2 ^ n) ^ 4 = (2 ^ n) ^ 2 * (2 ^ n) ^ 2 := by ring
      _ ≤ Nat.card W * M.relIndex L := Nat.mul_le_mul hWcard hMrel
      _ ≤ Nat.card W * W.relIndex L := Nat.mul_le_mul_left _ h1
      _ = Nat.card L := hcardL.symm
  have hLle : Nat.card L ≤ Nat.card (Z2 L1 L2 S) := Subgroup.card_le_of_le hLZ
  have hZle : Nat.card (Z2 L1 L2 S) ≤ (2 ^ n) ^ 3 :=
    str86_card_z2_le hF hSB hk hFc hU3 hn hL2 hZQ h376
  have hlt : (2 ^ n) ^ 3 < (2 ^ n) ^ 4 := by
    have hgt : 1 < 2 ^ n := by
      calc 1 < 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    calc (2 ^ n) ^ 3 = (2 ^ n) ^ 3 * 1 := by ring
      _ < (2 ^ n) ^ 3 * (2 ^ n) := Nat.mul_lt_mul_of_pos_left hgt (pow_pos (by norm_num) 3)
      _ = (2 ^ n) ^ 4 := by ring
  exact (not_le_of_gt hlt) (hge.trans (hLle.trans hZle))

end CFSG.Quasithin.Stroth

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_commutator_z2_u3H_le
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
    ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ≤ W := by
  classical
  have hZ2 : IsPGroup 2 (Z2 L1 L2 S) := by
    intro y
    exact ⟨1, Subtype.ext (by
      simpa using (SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)).2 y y.2)⟩
  have hWN : (u3H L1 L2 S) ≤ Subgroup.normalizer (W : Set G) :=
    D14.le_normalizer_of_isNormalIn hstepW.1
  have hcen : ∀ M L : Subgroup G, IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) M L →
      W ≤ M → L ≤ Z2 L1 L2 S → IsCentralStep (u3H L1 L2 S) M L :=
    fun M L hstep hWM hLZ =>
      str86_chiefStep_central hF hSB hk hFc hU3 hn hL2 hZQ h376 hstepW hncW hstep hWM hLZ
  have hcomm_odd : ∀ a ∈ u3H L1 L2 S, Odd (orderOf a) →
      ∀ x ∈ Z2 L1 L2 S, a * x * a⁻¹ * x⁻¹ ∈ W :=
    fun a ha haodd =>
      commutator_mem_of_odd_of_central_chief (q2_le_u3H L1 L2 S)
        (omegaOneCenterOf_le (Q2 L1 L2 S)) hWZ2 hZ2 (str86_z2_normal_u3H L1 L2 S) hWN
        hstepW.1 hcen ha haodd
  let K : Subgroup G :=
    { carrier := {h | h ∈ u3H L1 L2 S ∧ ∀ x ∈ Z2 L1 L2 S, h * x * h⁻¹ * x⁻¹ ∈ W}
      one_mem' := ⟨(u3H L1 L2 S).one_mem, by intro x hx; simp⟩
      mul_mem' := by
        rintro h1 h2 ⟨h1H, h1P⟩ ⟨h2H, h2P⟩
        refine ⟨(u3H L1 L2 S).mul_mem h1H h2H, fun x hx => ?_⟩
        have h2x : h2 * x * h2⁻¹ * x⁻¹ ∈ W := h2P x hx
        have hconj : h1 * (h2 * x * h2⁻¹ * x⁻¹) * h1⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hWN h1H) _).mp h2x
        have h1x : h1 * x * h1⁻¹ * x⁻¹ ∈ W := h1P x hx
        have hcalc : (h1 * h2) * x * (h1 * h2)⁻¹ * x⁻¹ =
            (h1 * (h2 * x * h2⁻¹ * x⁻¹) * h1⁻¹) * (h1 * x * h1⁻¹ * x⁻¹) := by
          group
        rw [hcalc]
        exact W.mul_mem hconj h1x
      inv_mem' := by
        rintro h ⟨hH, hP⟩
        refine ⟨(u3H L1 L2 S).inv_mem hH, fun x hx => ?_⟩
        have hxW : h * x * h⁻¹ * x⁻¹ ∈ W := hP x hx
        have hconj : h⁻¹ * (h * x * h⁻¹ * x⁻¹) * (h⁻¹)⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hWN ((u3H L1 L2 S).inv_mem hH)) _).mp hxW
        have hcalc : h⁻¹ * x * (h⁻¹)⁻¹ * x⁻¹ =
            (h⁻¹ * (h * x * h⁻¹ * x⁻¹) * (h⁻¹)⁻¹)⁻¹ := by
          group
        rw [hcalc]
        exact W.inv_mem hconj }
  have hoddK : ∀ y ∈ u3H L1 L2 S, Odd (orderOf y) → y ∈ K :=
    fun y hy hyodd => ⟨hy, fun x hx => hcomm_odd y hy hyodd x hx⟩
  have hOK : oTwoUpper (u3H L1 L2 S) ≤ K := by
    rw [oTwoUpper]
    exact (Subgroup.closure_le K).mpr (fun y hy => hoddK y hy.1 hy.2)
  have hQK : Q2 L1 L2 S ≤ K := by
    intro q hq
    refine ⟨q2_le_u3H L1 L2 S hq, fun x hx => ?_⟩
    have hcent := SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S) hq
    have hqx : x * q = q * x := Subgroup.mem_centralizer_iff.mp hcent x hx
    have hqconj : q * x * q⁻¹ = x := by
      calc q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [hqx]
        _ = x := by group
    simpa [hqconj] using W.one_mem
  have hHK : u3H L1 L2 S ≤ K := by
    rw [str86_u3H_eq_oTwoUpper_sup_q2 hF.toW hn hL2]
    exact sup_le hOK hQK
  rw [Subgroup.commutator_le]
  intro x hx h hh
  have hK := hHK hh
  have hxW : h * x * h⁻¹ * x⁻¹ ∈ W := hK.2 x hx
  simpa [commutatorElement_def, mul_assoc] using W.inv_mem hxW

end CFSG.Quasithin.Stroth

end
