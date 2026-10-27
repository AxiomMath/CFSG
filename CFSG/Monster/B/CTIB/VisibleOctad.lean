module

public import CFSG.Monster.B.TwoA.Census.CosetEnum
public import CFSG.Monster.Existence.TwoB
public import CFSG.Monster.Existence.Census.TrialityWitnesses
public import Certificates.Certificate3176

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.TwoA.Census
  CFSG.Monster.B.Rep4371 CFSG.Monster.B.Short
open scoped IsMulCommutative

theorem octFix_count : octFixCount (tT 1) (tD 1) = 2 ^ 24 :=
  Certificates.certificate3176.1

theorem octFixTest_true {n : ℕ} (hn : n < 2 ^ 24) :
    octFixTest (tT 1) (tD 1) n = true := by
  have h : ((Finset.range (2 ^ 24)).filter fun n => octFixTest (tT 1) (tD 1) n = true).card =
      2 ^ 24 :=
    (zero_add _).symm.trans ((countBelow_eq _ _ _).symm.trans octFix_count)
  exact Finset.card_filter_eq_iff.1 (h.trans (Finset.card_range _).symm) n (Finset.mem_range.2 hn)

theorem pauliQ_false_split (A D : ℕ) :
    pauliQ (false, A, D) = pauliQ (false, A, 0) * pauliQ (false, 0, D) :=
  (pauliQ_split false A D).trans (congrArg (· * pauliQ (false, 0, D))
    ((congrArg (· * pauliQ (false, A, 0)) pauliQ_false_zero).trans (one_mul _)))

theorem conjQ_one_pauliQ
    {A D : ℕ} (hA : A < 2 ^ 12)
    (hD : D < 2 ^ 12) :
    conjQ (cosetPair 1) (pauliQ (false, A, D)) =
      pauliQ (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!) := by
  have e := pauliQ_false_split A D
  calc conjQ (cosetPair 1) (pauliQ (false, A, D))
      = conjQ (cosetPair 1) (pauliQ (false, A, 0)) * conjQ (cosetPair 1) (pauliQ (false, 0, D)) :=
        (congrArg (conjQ (cosetPair 1)) e).trans (map_mul _ _ _)
    _ = pauliQ (Model.Pauli.mul (alphaN 1 (false, A, 0)) (alphaN 1 (false, 0, D))) :=
        (congrArg₂ (· * ·) (conjQ_cosetPair 1 _) (conjQ_cosetPair 1 _)).trans (pauliQ_mul _ _).symm
    _ = pauliQ (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!) :=
        congrArg pauliQ (congrArg₂ Model.Pauli.mul (tT_get 1 hA).symm (tD_get 1 hD).symm)

theorem pauliQ_false_mod {a d A D : ℕ} (ha : a % 2 ^ 12 = A) (hd : d % 2 ^ 12 = D) :
    pauliQ (false, a, d) = pauliQ (false, A, D) :=
  (pauliQ_mod_a false a d).symm.trans ((pauliQ_mod_d false _ d).symm.trans
    (congrArg pauliQ (Prod.ext rfl (Prod.ext ha hd))))

theorem conjQ_one_eq_of_coordOf
    {r : Q}
    (h : coordOf (conjQ (cosetPair 1) r) = coordOf r) :
    conjQ (cosetPair 1) r = r := by
  have hex := exists_qP r
  obtain ⟨s, -, A, hA, D, hD, hr⟩ := hex
  have e : r = pauliQ (s % 2 == 1, 0, 0) * pauliQ (false, A, D) :=
    hr.symm.trans ((pauliQ_split _ A D).trans ((mul_assoc _ _ _).trans
      (congrArg (pauliQ (s % 2 == 1, 0, 0) * ·) (pauliQ_false_split A D).symm)))
  have eα : conjQ (cosetPair 1) r = pauliQ (s % 2 == 1, 0, 0) *
      pauliQ (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!) :=
    (congrArg (conjQ (cosetPair 1)) e).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (conjQ_pauliQ_s _ _) (conjQ_one_pauliQ hA hD)))
  have h2 : coordOf (pauliQ (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!)) =
      coordOf (pauliQ (false, A, D)) :=
    add_left_cancel ((coordOf_mul _ _).symm.trans ((congrArg coordOf eα).symm.trans
      (h.trans ((congrArg coordOf e).trans (coordOf_mul _ _)))))
  have h3 := (AxisCount.coordOf_pauliQ _).symm.trans (h2.trans (AxisCount.coordOf_pauliQ _))
  have ha : (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!).2.1 % 2 ^ 12 = A :=
    toC_injective (Nat.mod_lt _ (by norm_num)) hA
      ((AxisCount.toC_mod_4096 _).trans (congrArg Prod.fst h3))
  have hd : (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!).2.2 % 2 ^ 12 = D :=
    toD_injective (Nat.mod_lt _ (by norm_num)) hD
      ((AxisCount.toD_mod_4096 _).trans (congrArg Prod.snd h3))
  have hn1 : (A + 2 ^ 12 * D) % 2 ^ 12 = A := by omega
  have hn2 : (A + 2 ^ 12 * D) / 2 ^ 12 % 2 ^ 12 = D := by omega
  have ht := octFixTest_true (n := A + 2 ^ 12 * D) (by omega)
  simp only [octFixTest, hn1, hn2, native_Pauli_mul, ha, hd, beq_self_eq_true, Bool.and_self,
    Bool.not_true, Bool.false_or, Bool.not_eq_true'] at ht
  have hpe : pauliQ (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!) = pauliQ (false, A, D) :=
    (congrArg pauliQ (Prod.ext ht rfl : Model.Pauli.mul (tT 1)[A]! (tD 1)[D]! =
      (false, (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!).2.1,
        (Model.Pauli.mul (tT 1)[A]! (tD 1)[D]!).2.2))).trans (pauliQ_false_mod ha hd)
  exact eα.trans ((congrArg (pauliQ (s % 2 == 1, 0, 0) * ·) hpe).trans e.symm)

theorem conjNormal_cosetRep_one
    (t : Q) :
    MulAut.conjNormal (cosetRep 1) (rhoN t) = rhoN (conjQ (cosetPair 1) t) :=
  conjNormal_thetaEquiv_rhoN (cosetPair 1) t

theorem mem_ker_sub_one_iff {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M) (v : M) : v ∈ LinearMap.ker (f - 1) ↔ f v = v := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem finrank_range_sub_one_eq {K M : Type*} [Field K] [Finite K] [AddCommGroup M]
    [Module K M] [Finite M] (f : M →ₗ[K] M) {n k : ℕ} (hM : Module.finrank K M = n)
    (hk : Nat.card (LinearMap.ker (f - 1)) = Nat.card K ^ k) :
    Module.finrank K (LinearMap.range (f - 1)) = n - k := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f - 1)
  have h := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker (f - 1))
  rw [hk] at h
  have h2 := Nat.pow_right_injective (Finite.one_lt_card (α := K)) h
  omega

theorem octA_apply (t : Q) :
    (repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod)
        (Additive.ofMul (QuotientGroup.mk (rhoN t))) =
      Additive.ofMul (QuotientGroup.mk (rhoN (conjQ (cosetPair 1) t))) :=
  (repVis_apply _ _).trans
    (congrArg (fun y : rhoQvis => Additive.ofMul (QuotientGroup.mk y : VisMod))
      (conjNormal_cosetRep_one t))

theorem commute_of_octA_fix
    (t : Q)
    (h : (repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod)
      (Additive.ofMul (QuotientGroup.mk (rhoN t))) = Additive.ofMul (QuotientGroup.mk (rhoN t))) :
    (rhoN t : Gvis) * cosetRep 1 = cosetRep 1 * rhoN t := by
  have hv' := (octA_apply t).symm.trans h
  have hfix := conjQ_one_eq_of_coordOf ((mk_rhoN_eq_iff _ _).1 (Additive.ofMul.injective hv'))
  have h1 : cosetRep 1 * (rhoN t : Gvis) * (cosetRep 1)⁻¹ = rhoN t :=
    (MulAut.conjNormal_apply _ _).symm.trans (congrArg Subtype.val
      ((conjNormal_cosetRep_one t).trans (congrArg rhoN hfix)))
  exact (mul_inv_eq_iff_eq_mul.1 h1).symm

theorem mem_ker_octA_iff
    (v : Additive VisMod) :
    v ∈ LinearMap.ker
        ((repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod) - 1) ↔
      ∃ u : rhoQvis, (u : Gvis) * cosetRep 1 = cosetRep 1 * u ∧
        v = Additive.ofMul (QuotientGroup.mk u) := by
  refine (mem_ker_sub_one_iff _ v).trans (Iff.intro (fun hv => ?_) (fun hu => ?_))
  · have hx := QuotientGroup.mk_surjective (Additive.toMul v)
    obtain ⟨u, hu⟩ := hx
    have ht := rhoN_surjective u
    obtain ⟨t, ht⟩ := ht
    have hv' : Additive.ofMul (QuotientGroup.mk (rhoN t) : VisMod) = v :=
      (congrArg (fun y : rhoQvis => Additive.ofMul (QuotientGroup.mk y : VisMod)) ht).trans
        (congrArg Additive.ofMul hu)
    have hfix := commute_of_octA_fix t
      ((congrArg (repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod) hv').trans
        (hv.trans hv'.symm))
    exact ⟨rhoN t, hfix, hv'.symm⟩
  · obtain ⟨u, hu, hv⟩ := hu
    have h1 : MulAut.conjNormal (cosetRep 1) u = u := Subtype.ext
      ((MulAut.conjNormal_apply _ _).trans (mul_inv_eq_iff_eq_mul.2 hu.symm))
    exact (congrArg (repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod) hv).trans
      ((repVis_apply _ _).trans ((congrArg (fun y : rhoQvis =>
        Additive.ofMul (QuotientGroup.mk y : VisMod)) h1).trans hv.symm))

theorem classRep_zero_eq_cosetRep_one
    : classRep 0 = cosetRep 1 := by
  have hq : qOfEnc 0 = 1 := pauliQ_false_zero
  rw [classRep, classEnc_zero, cosetElt, hq, rhoGvis_one, mul_one]

theorem ncard_qmatClass_cosetRep_one :
    (qmatClass (cosetRep 1)).ncard = 256 := by
  have h := ncard_qmatClass_classRep (k := 0) (by norm_num)
  rw [classRep_zero_eq_cosetRep_one, classSize_eq 0 (by norm_num)] at h
  exact h

theorem natCard_octU :
    Nat.card (rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) = 2 ^ 17 := by
  let _ : MulAction rhoQvis Gvis := MulAction.compHom Gvis (MulAut.conj.comp rhoQvis.subtype)
  have hsmul : ∀ (u : rhoQvis) (f : Gvis), u • f = (u : Gvis) * f * (u : Gvis)⁻¹ :=
    fun _ _ => rfl
  have horb : MulAction.orbit rhoQvis (cosetRep 1) = qmatClass (cosetRep 1) := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(u : Gvis)⁻¹, rhoQvis.inv_mem u.2, (hsmul u _).trans (by rw [inv_inv])⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩⁻¹, (hsmul _ _).trans (by rw [Subgroup.coe_inv, inv_inv])⟩
  have hst : MulAction.stabilizer rhoQvis (cosetRep 1) =
      (Subgroup.centralizer {cosetRep 1}).subgroupOf rhoQvis := by
    ext u
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (u : Gvis) * cosetRep 1 = (u : Gvis) * cosetRep 1 * (u : Gvis)⁻¹ * u := by group
        _ = cosetRep 1 * u := by rw [h]
    · intro h
      rw [h, mul_inv_cancel_right]
  have hidx := MulAction.index_stabilizer rhoQvis (cosetRep 1)
  rw [horb, ncard_qmatClass_cosetRep_one] at hidx
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer rhoQvis (cosetRep 1))
  rw [hidx, CFSG.Monster.Existence.natCard_rhoQvis, hst] at hmul
  have hc : Nat.card ((Subgroup.centralizer {cosetRep 1}).subgroupOf rhoQvis) = 2 ^ 17 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 256) (hmul.trans (by norm_num))
  rw [← hc, inf_comm, ← Subgroup.inf_subgroupOf_right]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm

theorem natCard_zRho : Nat.card zRho = 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup zRho
  rw [CFSG.Monster.Existence.natCard_rhoQvis, show Nat.card (rhoQvis ⧸ zRho) = 2 ^ 24 from
    natCard_visMod] at h
  omega

@[expose] noncomputable def octUMap :
    (Subgroup.centralizer {cosetRep 1}).subgroupOf rhoQvis →* VisMod :=
  (QuotientGroup.mk' zRho).comp ((Subgroup.centralizer {cosetRep 1}).subgroupOf rhoQvis).subtype

theorem zRho_le_octU :
    zRho ≤ (Subgroup.centralizer {cosetRep 1}).subgroupOf rhoQvis :=
  Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2
    (mul_inv_eq_iff_eq_mul.1 ((MulAut.conjNormal_apply _ _).symm.trans
      (congrArg Subtype.val (conjNormal_rhoN_zQ (cosetRep 1))))).symm))

theorem octUMap_apply
    (u : (Subgroup.centralizer {cosetRep 1}).subgroupOf rhoQvis) :
    octUMap u = QuotientGroup.mk (u : rhoQvis) := rfl

theorem ker_octUMap :
    octUMap.ker = zRho.subgroupOf
    ((Subgroup.centralizer {cosetRep 1}).subgroupOf rhoQvis) := by
  ext u
  exact (MonoidHom.mem_ker.trans ((congrArg (· = 1) (octUMap_apply u)).to_iff.trans
    (QuotientGroup.eq_one_iff _))).trans Subgroup.mem_subgroupOf.symm

theorem natCard_range_octUMap :
    Nat.card octUMap.range = 2 ^ 16 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup octUMap.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange octUMap).toEquiv, ker_octUMap,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe zRho_le_octU).toEquiv, natCard_zRho] at h
  have hU : Nat.card ((Subgroup.centralizer {cosetRep 1}).subgroupOf rhoQvis) = 2 ^ 17 := by
    rw [← natCard_octU, inf_comm, ← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  omega

theorem mem_range_octUMap_iff
    (x : VisMod) :
    x ∈ octUMap.range ↔ ∃ u : rhoQvis, (u : Gvis) * cosetRep 1 = cosetRep 1 * u ∧
      x = QuotientGroup.mk u := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 u.2), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2 hu)⟩, rfl⟩

instance finite_visMod : Finite VisMod :=
  Nat.finite_of_card_ne_zero (by rw [natCard_visMod]; norm_num)


theorem natCard_ker_octA :
    Nat.card (LinearMap.ker
    ((repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod) - 1)) = 2 ^ 16 :=
  (Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun v =>
    (mem_ker_octA_iff v).trans ((exists_congr fun u => and_congr_right fun _ =>
      (⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩ :
        v = Additive.ofMul (QuotientGroup.mk u) ↔ Additive.toMul v = QuotientGroup.mk u)).trans
        (mem_range_octUMap_iff _).symm))).trans natCard_range_octUMap

theorem finrank_range_octA :
    Module.finrank (ZMod 2) (LinearMap.range
      ((repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod) - 1)) = 8 :=
  (finrank_range_sub_one_eq _ finrank_visMod (natCard_ker_octA.trans (by rw [Nat.card_zmod]))).trans
    (by norm_num)

theorem isShortCoord_qP_three_sixty :
    IsShortCoord (coordOf (qP 0 3 60)) := by
  have h := AxisCount.short_octG 2 0 (by norm_num) (by norm_num)
  rw [← AxisCount.pauliQ_octG] at h
  have e : (⟨false, AxisCount.Native.octCodeG AxisCount.Native.octTab[2]!
      AxisCount.Native.evenTab[0]!, Model.thetaN (AxisCount.Native.octCodeG
        AxisCount.Native.octTab[2]! AxisCount.Native.evenTab[0]!) ^^^
          Model.dualN (AxisCount.Native.spreadG (Model.wordN AxisCount.Native.octTab[2]!)
            AxisCount.Native.evenTab[0]!)⟩ : Model.Pauli) = (false, 3, 60) :=
    Certificates.certificate3176.2
  rw [e] at h
  exact h

theorem tStar_mem_shortInv' : tStar ∈ shortInv := ⟨rStar, isShortCoord_rStar, rfl⟩

theorem exists_conj_cosetRep_one_tStar :
    ∃ g ∈ Gmat, g * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * g⁻¹ = tStar := by
  have hτ := CFSG.Monster.Existence.Census.trialityWitness_one
  obtain ⟨d, hd, hdt⟩ := shortInv_transitive ⟨qP 0 3 60, isShortCoord_qP_three_sixty, rfl⟩
    tStar_mem_shortInv'
  refine ⟨d * tauB ^ 2, mul_mem (Hmat_le_Gmat hd) (pow_mem tauB_mem_Gmat 2), ?_⟩
  rw [← hdt, ← hτ]
  group

theorem cosetRep_one_sq :
    (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * cosetRep 1 = 1 :=
  cosetRep_sq.1

theorem cosetRep_one_not_mem_Qmat :
    (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) ∉ Qmat :=
  cosetRep_not_mem (by norm_num) (by norm_num)

theorem orderOf_cosetRep_one :
    orderOf (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = 2 :=
  orderOf_eq_prime ((sq _).trans cosetRep_one_sq) fun h =>
    cosetRep_one_not_mem_Qmat (h ▸ Qmat.one_mem)

theorem visible_octad_involution_full_fixed_space :
    orderOf (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) = 2 ∧
    (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) ∉ Qmat ∧
    Module.finrank (ZMod 2) (LinearMap.range
      ((repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod) - 1)) = 8 ∧
    Nat.card (rhoQvis ⊓ Subgroup.centralizer {cosetRep 1} : Subgroup Gvis) = 2 ^ 17 ∧
    (∀ v : Additive VisMod, v ∈ LinearMap.ker
        ((repVis (cosetRep 1) : Additive VisMod →ₗ[ZMod 2] Additive VisMod) - 1) ↔
      ∃ u : rhoQvis, (u : Gvis) * cosetRep 1 = cosetRep 1 * u ∧
        v = Additive.ofMul (QuotientGroup.mk u)) ∧
    ∃ g ∈ Gmat, g * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * g⁻¹ = tStar :=
  ⟨orderOf_cosetRep_one, cosetRep_one_not_mem_Qmat, finrank_range_octA, natCard_octU,
    mem_ker_octA_iff, exists_conj_cosetRep_one_tStar⟩

end CFSG.Monster.B.CTIB
