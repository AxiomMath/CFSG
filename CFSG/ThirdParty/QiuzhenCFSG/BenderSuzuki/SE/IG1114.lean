module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

namespace CFSG
end CFSG
open CFSG

/-!
# The cross-characteristic core of `[IG; 11.14(i)]`

This file proves the exact part of `[IG; 11.14(i)]` used in Sections 9 and 10
of the Bender--Suzuki argument.  It follows the source proof: pass to the
Frattini quotient of the target `p`-group, use coprime fixed-point lifting,
apply the Hall--Higman representation theorem, and lift triviality through the
Frattini subgroup.
-/

noncomputable section

open scoped Pointwise IsMulCommutative

namespace CFSG.BenderSuzuki

set_option maxHeartbeats 1000000

/-- Cross-characteristic contrapositive of `[IG; 11.14(i)]`.

The actor is `S = A B`, with `A` normal, `B` of prime order, and
`A = [B,A]`.  If `B` has no nonidentity fixed point on the target `p`-group
and the actor and target have coprime orders, then `A` acts trivially on the
target. -/
public theorem ig1114_i_actsTrivially_of_fixedPointSubgroup_eq_bot
    {S T : Type*} [Group S] [Finite S] [Group T] [Finite T]
    [MulDistribMulAction S T]
    {p : ℕ} [Fact p.Prime]
    (A B : Subgroup S)
    (hT : IsPGroup p T)
    (hoddS : Odd (Nat.card S))
    (hA_normal : A.Normal)
    (hAB : A.IsComplement' B)
    (hcopAB : Nat.Coprime (Nat.card A) (Nat.card B))
    (hB_prime : Nat.Prime (Nat.card B))
    (hcopST : Nat.Coprime (Nat.card S) (Nat.card T))
    (hcomm : ⁅B, A⁆ = A)
    (hfixB : fixedPointSubgroup (↥B) T = ⊥) :
    ActsTrivially (A := ↥A) (G := T) := by
  classical
  letI : Fact (IsPGroup p T) := ⟨hT⟩
  by_cases hTnon : Nontrivial T
  · letI : Nontrivial T := hTnon
    let Phi : Subgroup T := frattini T
    letI : Phi.Characteristic := frattini_characteristic
    letI : Phi.Normal := inferInstance
    let hPhiInvS : IsInvariant S T Phi :=
      isInvariant_of_characteristic (A := S) (G := T) Phi
    letI : MulDistribMulAction S (T ⧸ Phi) :=
      quotientMulDistribMulAction (A := S) (G := T) Phi hPhiInvS
    letI : IsElementaryAbelian p (T ⧸ Phi) :=
      isElementaryAbelian_quotient_frattini (R := T) (p := p)
    let rho : Representation (ZMod p) S (Additive (T ⧸ Phi)) :=
      Theory.Representation.ofElementaryAbelianAction
        (A := S) (G := T ⧸ Phi) (p := p)
    have hAcopT : Nat.Coprime (Nat.card A) (Nat.card T) :=
      Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card A) hcopST
    have hBcopT : Nat.Coprime (Nat.card B) (Nat.card T) :=
      Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card B) hcopST
    letI : Group.IsNilpotent T := hT.isNilpotent
    have hsolvT : Group.IsSolvable T := by infer_instance
    let hPhiInvB : IsInvariant (↥B) T Phi :=
      isInvariant_of_characteristic (A := ↥B) (G := T) Phi
    have hfixBq : fixedPointSubgroup (↥B) (T ⧸ Phi) = ⊥ := by
      have heq :=
        fixedPointSubgroup_quotient_eq_map_of_solvable_coprime
          (G := T) (A := ↥B) hsolvT hBcopT Phi hPhiInvB
      rw [heq, hfixB]
      simp
    obtain ⟨n, hTcard⟩ := hT.exists_card_eq
    have hn : n ≠ 0 := by
      intro hn
      have hcardOne : Nat.card T = 1 := by simpa [hn] using hTcard
      exact (Finite.one_lt_card_iff_nontrivial.mpr hTnon).ne hcardOne.symm
    have hpDvdT : p ∣ Nat.card T := by
      rw [hTcard]
      exact dvd_pow_self p hn
    have hpCopS : Nat.Coprime p (Nat.card S) :=
      Nat.Coprime.of_dvd_left hpDvdT hcopST.symm
    have hchar :
        ringChar (ZMod p) = 0 ∨
          Nat.Prime (ringChar (ZMod p)) ∧
            Nat.Coprime (ringChar (ZMod p)) (Nat.card S) := by
      right
      rw [ZMod.ringChar_zmod_n]
      exact ⟨Fact.out, hpCopS⟩
    have hsolvS : Group.IsSolvable S := odd_order_theorem S hoddS
    have hfixRho : rho.fixedSubspace B = ⊥ := by
      exact
        theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot B hfixBq
    have hcommCent : ⁅B, A⁆ ≤ rho.centralizerIn A :=
      theorem_3_4 A B rho hsolvS hoddS hA_normal hAB hcopAB hB_prime
        hchar hfixRho
    have hACent : A ≤ rho.centralizerIn A := by
      intro x hx
      apply hcommCent
      simpa [hcomm] using hx
    have hfixAq : fixedPointSubgroup (↥A) (T ⧸ Phi) = ⊤ :=
      theorem_3_7_fixedPointSubgroup_eq_top_of_le_centralizerIn A hACent
    have htrivq : ActsTrivially (A := ↥A) (G := T ⧸ Phi) := by
      intro a x
      have hx : x ∈ fixedPointSubgroup (↥A) (T ⧸ Phi) := by
        simp [hfixAq]
      rw [FixedPoints.mem_subgroup] at hx
      exact hx a
    have hsupA :
        fixedPointSubgroup (↥A) T ⊔
            commutatorAction (A := ↥A) (G := T) = ⊤ :=
      fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
        hsolvT hAcopT
    exact
      actsTrivially_of_trivial_quotient_frattini_of_sup_eq_top
        (R := T) (A := ↥A) (p := p) hsupA
        (by simpa [Phi] using htrivq)
  · letI : Subsingleton T := not_nontrivial_iff_subsingleton.mp hTnon
    intro a x
    exact Subsingleton.elim (a • x) x

/-- The nilpotent-target form of `[IG; 11.14(i)]`.

Each Sylow subgroup of a finite nilpotent target is characteristic.  The
prime-target theorem therefore applies to each Sylow subgroup, and the Sylow
subgroups generate the target. -/
public theorem ig1114_i_actsTrivially_of_nilpotent_fixedPointSubgroup_eq_bot
    {S T : Type*} [Group S] [Finite S] [Group T] [Finite T]
    [MulDistribMulAction S T]
    (A B : Subgroup S)
    (hTnil : Group.IsNilpotent T)
    (hoddS : Odd (Nat.card S))
    (hA_normal : A.Normal)
    (hAB : A.IsComplement' B)
    (hcopAB : Nat.Coprime (Nat.card A) (Nat.card B))
    (hB_prime : Nat.Prime (Nat.card B))
    (hcopST : Nat.Coprime (Nat.card S) (Nat.card T))
    (hcomm : ⁅B, A⁆ = A)
    (hfixB : fixedPointSubgroup (↥B) T = ⊥) :
    ActsTrivially (A := ↥A) (G := T) := by
  classical
  have htop_le : (⊤ : Subgroup T) ≤ fixedPointSubgroup (↥A) T := by
    rw [← Sylow.iSup_sylow_eq_top (G := T)]
    refine iSup_le fun q ↦ iSup_le fun hq ↦ ?_
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    letI : Fact q.Prime := ⟨hqprime⟩
    let Q : Sylow q T := default
    have hQnormal : (Q : Subgroup T).Normal :=
      Group.IsNilpotent.sylow_normal hTnil q Q
    letI : (Q : Subgroup T).Characteristic :=
      Sylow.characteristic_of_normal Q hQnormal
    letI : IsInvariant S T (Q : Subgroup T) :=
      isInvariant_of_characteristic (A := S) (G := T) (Q : Subgroup T)
    have hfixBQ : fixedPointSubgroup (↥B) (Q : Subgroup T) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxT : (x : T) ∈ fixedPointSubgroup (↥B) T := by
        rw [FixedPoints.mem_subgroup]
        intro b
        have hx' := hx
        rw [FixedPoints.mem_subgroup] at hx'
        exact congrArg Subtype.val (hx' b)
      rw [hfixB] at hxT
      exact Subtype.ext (by simpa using hxT)
    have hcopSQ : Nat.Coprime (Nat.card S) (Nat.card (Q : Subgroup T)) :=
      Nat.Coprime.of_dvd_right
        (Subgroup.card_subgroup_dvd_card (Q : Subgroup T)) hcopST
    have htrivQ : ActsTrivially (A := ↥A) (G := (Q : Subgroup T)) :=
      ig1114_i_actsTrivially_of_fixedPointSubgroup_eq_bot
        A B Q.isPGroup' hoddS hA_normal hAB hcopAB hB_prime hcopSQ
          hcomm hfixBQ
    intro x hx
    rw [FixedPoints.mem_subgroup]
    intro a
    let xQ : (Q : Subgroup T) := ⟨x, hx⟩
    exact congrArg Subtype.val (htrivQ a xQ)
  intro a x
  have hx : x ∈ fixedPointSubgroup (↥A) T := htop_le (by simp)
  rw [FixedPoints.mem_subgroup] at hx
  exact hx a

/-- Coprime action gives the standard identity
`[[R,P],P] = [R,P]` whenever `P` normalizes `R`. -/
public theorem ig1114_commutator_idempotent_of_coprime
    {X : Type*} [Group X] [Finite X]
    (R P : Subgroup X)
    (hcopPR : Nat.Coprime (Nat.card P) (Nat.card R))
    (hPnormR : P ≤ Subgroup.normalizer (R : Set X)) :
    ⁅⁅R, P⁆, P⁆ = ⁅R, P⁆ := by
  let A0 : Subgroup X := ⁅R, P⁆
  letI : Subgroup.Normalizes P R := ⟨hPnormR⟩
  have hA0leR : A0 ≤ R := by
    rw [Subgroup.commutator_le]
    intro r hr p hp
    have hpnorm : p ∈ Subgroup.normalizer (R : Set X) := hPnormR hp
    have hconj : p * r⁻¹ * p⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hpnorm r⁻¹).1 (R.inv_mem hr)
    simpa [A0, commutatorElement_def, mul_assoc] using R.mul_mem hr hconj
  have hA0normRP : (A0.subgroupOf (R ⊔ P)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show A0 ≤ R ⊔ P from hA0leR.trans le_sup_left)).2
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (commutator_le_sup R P)).1 (commutator_normal_in_sup R P) |>.trans le_rfl
  have hPnormA0 : P ≤ Subgroup.normalizer (A0 : Set X) := by
    have hRPnormA0 : R ⊔ P ≤ Subgroup.normalizer (A0 : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (show A0 ≤ R ⊔ P from hA0leR.trans le_sup_left)).mp hA0normRP
    exact le_sup_right.trans hRPnormA0
  let C : Subgroup R := commutatorAction (A := ↥P) (G := ↥R)
  letI : IsInvariant (↥P) (↥R) C := by
    simpa [C] using commutatorAction_isInvariant (G := ↥R) (A := ↥P)
  have hCmap : C.map R.subtype = A0 := by
    simpa [C, A0] using
      commutatorAction_subgroup_conj_map_eq_commutator R P hPnormR
  have hC2 : commutatorAction₂ (A := ↥P) (G := ↥R) = C := by
    simpa [C] using commutatorAction₂_eq_commutatorAction_of_coprime
      (G := ↥R) (A := ↥P) hcopPR
  have hDmap :
      (commutatorAction (A := ↥P) (G := ↥C)).map C.subtype = C := by
    calc
      (commutatorAction (A := ↥P) (G := ↥C)).map C.subtype =
          commutatorAction₂ (A := ↥P) (G := ↥R) := by
            simpa [C] using commutatorAction_map_subtype_eq_commutatorAction₂
              (G := ↥R) (A := ↥P)
      _ = C := hC2
  have hDtop : commutatorAction (A := ↥P) (G := ↥C) = ⊤ := by
    apply eq_top_iff.2
    intro x _hx
    have hxmap : (x : R) ∈
        (commutatorAction (A := ↥P) (G := ↥C)).map C.subtype := by
      rw [hDmap]
      exact x.property
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
    have hy_eq_x : y = x := C.subtype_injective hyx
    simpa [hy_eq_x] using hy
  letI : Subgroup.Normalizes P A0 := ⟨hPnormA0⟩
  let e : C ≃* A0 :=
    (Subgroup.equivMapOfInjective C R.subtype R.subtype_injective).trans
      (MulEquiv.subgroupCongr hCmap)
  have he_coe (c : C) : ((e c : A0) : X) = ((c : R) : X) := by
    simp [e, Subgroup.coe_equivMapOfInjective_apply]
  have he_smul (a : P) (c : C) : e (a • c) = a • e c := by
    apply Subtype.ext
    change ((e (a • c) : A0) : X) = ((a • e c : A0) : X)
    rw [he_coe]
    change ((a • (c : R) : R) : X) = ((a • e c : A0) : X)
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, he_coe]
  have hmapD :
      (commutatorAction (A := ↥P) (G := ↥C)).map e.toMonoidHom =
        commutatorAction (A := ↥P) (G := ↥A0) := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    rw [MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨a, c, rfl⟩, rfl⟩
      refine ⟨a, e c, ?_⟩
      simp [he_smul]
    · rintro ⟨a, x, rfl⟩
      let c : C := e.symm x
      refine ⟨c⁻¹ * (a • c), ⟨a, c, rfl⟩, ?_⟩
      simp [he_smul, c]
  have hAtop : commutatorAction (A := ↥P) (G := ↥A0) = ⊤ := by
    rw [← hmapD, hDtop]
    exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
  have hAmap :
      (commutatorAction (A := ↥P) (G := ↥A0)).map A0.subtype =
        ⁅A0, P⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator A0 P hPnormA0
  have hAeq : ⁅A0, P⁆ = A0 := by
    symm
    calc
      A0 = (⊤ : Subgroup A0).map A0.subtype := by
        ext x
        simp
      _ = (commutatorAction (A := ↥P) (G := ↥A0)).map A0.subtype := by
        rw [hAtop]
      _ = ⁅A0, P⁆ := hAmap
  simpa [A0] using hAeq

/-- A prime-order subgroup acting fixed-point-freely by conjugation makes the
target subgroup nilpotent. -/
public theorem ig1114_nilpotent_of_prime_fixedPointFree
    {X : Type*} [Group X] [Finite X]
    (K P : Subgroup X)
    (hPnormK : P ≤ Subgroup.normalizer (K : Set X))
    (hPprime : Nat.Prime (Nat.card P))
    (hfix : subgroupCentralizerIn K P = ⊥) :
    Group.IsNilpotent K := by
  have hPne : P ≠ ⊥ := by
    intro hPbot
    exact hPprime.ne_one (by simp [hPbot])
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hxneX : (x : X) ≠ 1 := by
    intro hx
    apply hxne
    exact Subtype.ext hx
  have hfixed : ∀ y : X, y ∈ P → y ≠ 1 →
      Subgroup.centralizer ({y} : Set X) ⊓ K = ⊥ := by
    intro y hyP hyne
    have hyneP : (⟨y, hyP⟩ : P) ≠ 1 := by
      intro h
      exact hyne (congrArg Subtype.val h)
    have hcent := theorem_3_7_elementCentralizer_eq_bot
      K P hPprime hfix ⟨y, hyP⟩ hyneP
    simpa [elementCentralizerIn, inf_comm] using hcent
  exact
    External.huppert_V_8_14_thompson_fixedPointFree_conjugation_nilpotent_subgroup
      K P hPnormK ⟨x, x.property, hxneX⟩ hfixed

/-- The subgroup-conjugation adapter for `[IG; 11.14(i)]`.

For `A₀ = [R,P]` the coprime-action identity gives `[A₀,P] = A₀`.
If `P` acts fixed-point-freely on `K`, Thompson's theorem makes `K`
nilpotent.  Applying the nilpotent-target form prime by prime then shows that
`A₀` centralizes `K`. -/
public theorem ig1114_i_commutator_le_centralizer_of_fixedPointFree
    {X : Type*} [Group X] [Finite X]
    (K R P : Subgroup X)
    (hPnormR : P ≤ Subgroup.normalizer (R : Set X))
    (hRPnormK : R ⊔ P ≤ Subgroup.normalizer (K : Set X))
    (hoddRP : Odd (Nat.card (R ⊔ P : Subgroup X)))
    (hcopPR : Nat.Coprime (Nat.card P) (Nat.card R))
    (hcopRK : Nat.Coprime (Nat.card R) (Nat.card K))
    (hcopPK : Nat.Coprime (Nat.card P) (Nat.card K))
    (hPprime : Nat.Prime (Nat.card P))
    (hfix : subgroupCentralizerIn K P = ⊥) :
    ⁅R, P⁆ ≤ Subgroup.centralizer (K : Set X) := by
  classical
  let A0 : Subgroup X := ⁅R, P⁆
  let S : Subgroup X := A0 ⊔ P
  have hA0leR : A0 ≤ R := by
    rw [Subgroup.commutator_le]
    intro r hr p hp
    have hpnorm : p ∈ Subgroup.normalizer (R : Set X) := hPnormR hp
    have hconj : p * r⁻¹ * p⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hpnorm r⁻¹).1 (R.inv_mem hr)
    simpa [A0, commutatorElement_def, mul_assoc] using R.mul_mem hr hconj
  have hA0normRP : (A0.subgroupOf (R ⊔ P)).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show A0 ≤ R ⊔ P from hA0leR.trans le_sup_left)).2
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (commutator_le_sup R P)).1 (commutator_normal_in_sup R P) |>.trans le_rfl
  have hPnormA0 : P ≤ Subgroup.normalizer (A0 : Set X) := by
    have hRPnormA0 : R ⊔ P ≤ Subgroup.normalizer (A0 : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (show A0 ≤ R ⊔ P from hA0leR.trans le_sup_left)).mp hA0normRP
    exact le_sup_right.trans hRPnormA0
  have hAeq : ⁅A0, P⁆ = A0 := by
    simpa [A0] using
      ig1114_commutator_idempotent_of_coprime R P hcopPR hPnormR
  have hPnormK : P ≤ Subgroup.normalizer (K : Set X) :=
    le_sup_right.trans hRPnormK
  have hKnil : Group.IsNilpotent K :=
    ig1114_nilpotent_of_prime_fixedPointFree K P hPnormK hPprime hfix
  have hSleRP : S ≤ R ⊔ P :=
    sup_le (hA0leR.trans le_sup_left) le_sup_right
  have hoddS : Odd (Nat.card S) :=
    hoddRP.of_dvd_nat (Subgroup.card_dvd_of_le hSleRP)
  letI : Subgroup.Normalizes S K := ⟨hSleRP.trans hRPnormK⟩
  let AS : Subgroup S := A0.subgroupOf S
  let BS : Subgroup S := P.subgroupOf S
  have hASnormal : AS.Normal := by
    have hRPnormA0 : R ⊔ P ≤ Subgroup.normalizer (A0 : Set X) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (show A0 ≤ R ⊔ P from hA0leR.trans le_sup_left)).mp hA0normRP
    have hSnormA0 : S ≤ Subgroup.normalizer (A0 : Set X) :=
      hSleRP.trans hRPnormA0
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show A0 ≤ S from le_sup_left)).2
    exact hSnormA0
  letI : AS.Normal := hASnormal
  have hcopAB : Nat.Coprime (Nat.card AS) (Nat.card BS) := by
    simpa [AS, BS] using
      coprime_card_subgroupOf_sup_of_le A0 R P hA0leR hcopPR.symm
  have hAB : AS.IsComplement' BS := by
    have hdisj : Disjoint AS BS := by
      rw [disjoint_iff]
      exact Subgroup.inf_eq_bot_of_coprime hcopAB
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
    have hsup : AS ⊔ BS = ⊤ := by
      rw [← Subgroup.subgroupOf_sup
        (A := A0) (A' := P) (B := S) le_sup_left le_sup_right]
      simp [S]
    calc
      (AS : Set S) * (BS : Set S) = ((AS ⊔ BS : Subgroup S) : Set S) :=
        (Subgroup.coe_mul_of_right_le_normalizer_left AS BS (by
          rw [Subgroup.normalizer_eq_top (H := AS)]
          exact le_top)).symm
      _ = ((⊤ : Subgroup S) : Set S) := by rw [hsup]
      _ = Set.univ := by simp
  have hBcard : Nat.card BS = Nat.card P := by
    simpa [BS] using natCard_subgroupOf_eq P S le_sup_right
  have hBprime : Nat.Prime (Nat.card BS) := by simpa [hBcard] using hPprime
  have hcopASK : Nat.Coprime (Nat.card AS) (Nat.card K) := by
    rw [show Nat.card AS = Nat.card A0 by
      simpa [AS] using natCard_subgroupOf_eq A0 S le_sup_left]
    exact Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hA0leR) hcopRK
  have hcopBSK : Nat.Coprime (Nat.card BS) (Nat.card K) := by
    rw [hBcard]
    exact hcopPK
  have hcopSK : Nat.Coprime (Nat.card S) (Nat.card K) := by
    rw [← hAB.card_mul]
    exact hcopASK.mul_left hcopBSK
  have hcomm : ⁅BS, AS⁆ = AS := by
    have hA0S : A0 ≤ S := by
      dsimp [S]
      exact le_sup_left
    have hPS : P ≤ S := by
      dsimp [S]
      exact le_sup_right
    apply Subgroup.map_injective S.subtype_injective
    rw [commutator_subgroupOf_map_eq S A0 P hA0S hPS]
    rw [Subgroup.commutator_comm, hAeq]
    change A0 = (A0.subgroupOf S).map S.subtype
    exact (Subgroup.map_subgroupOf_eq_of_le hA0S).symm
  have hfixBS : fixedPointSubgroup (↥BS) K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxCent : (x : X) ∈ subgroupCentralizerIn K P := by
      refine ⟨x.property, ?_⟩
      change (x : X) ∈ Subgroup.centralizer (P : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      have hyS : y ∈ S := by
        dsimp [S]
        exact Subgroup.mem_sup_right hyP
      let yS : S := ⟨y, hyS⟩
      let b : BS := ⟨yS, hyP⟩
      have hx' := hx
      rw [FixedPoints.mem_subgroup] at hx'
      have hfixedx := hx' b
      change (b : S) • x = x at hfixedx
      have hval : y * (x : X) * y⁻¹ = (x : X) := by
        simpa [yS, b,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val hfixedx
      have hmul := congrArg (fun z : X ↦ z * y) hval
      simpa [mul_assoc] using hmul
    rw [hfix] at hxCent
    have hxoneX : (x : X) = 1 := by simpa using hxCent
    have hxone : x = 1 := Subtype.ext hxoneX
    simp [hxone]
  have htriv : ActsTrivially (A := ↥AS) (G := K) :=
    ig1114_i_actsTrivially_of_nilpotent_fixedPointSubgroup_eq_bot
      AS BS hKnil hoddS hASnormal hAB hcopAB hBprime hcopSK hcomm hfixBS
  intro a haA0
  rw [Subgroup.mem_centralizer_iff]
  intro k hkK
  have haS : a ∈ S := by
    dsimp [S]
    exact Subgroup.mem_sup_left haA0
  let aS : S := ⟨a, haS⟩
  let aAS : AS := ⟨aS, haA0⟩
  let kK : K := ⟨k, hkK⟩
  have hfixed := htriv aAS kK
  change (aAS : S) • kK = kK at hfixed
  have hval : a * k * a⁻¹ = k := by
    simpa [aS, aAS, kK,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val hfixed
  have hmul := congrArg (fun z : X ↦ z * a) hval
  have hak : a * k = k * a := by simpa [mul_assoc] using hmul
  exact hak.symm

end CFSG.BenderSuzuki
