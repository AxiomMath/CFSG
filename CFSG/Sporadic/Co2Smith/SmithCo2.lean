module

public import CFSG.Sporadic.Co2Smith.Structure
public import CFSG.Sporadic.Co2Smith.Frame
public import CFSG.ClassicalGroups.Symplectic.Simple

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Assembly.LowTwoRank CFSG.Certificates.ExtraspecialNF

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem isSimpleGroup_sp62 : IsSimpleGroup Sp62 := by
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have hscal : (StatedScalars (Fin 3 ⊕ Fin 3) (ZMod 2)).subgroupOf (StatedSp 3 (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, Subsingleton.elim c 1, map_one]
    rfl
  have : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, by norm_num⟩))
  exact ((QuotientGroup.quotientMulEquivOfEq hscal).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem isPGroup_Q :
    IsPGroup 2 (Qsub.subgroupOf Cz) :=
  IsPGroup.of_card natCard_Q_subgroupOf

theorem pCore_Cz :
    CFSG.pCore 2 Cz = Qsub.subgroupOf Cz := by
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, isPGroup_Q⟩)
  have := isSimpleGroup_sp62
  have hN : ((CFSG.pCore 2 Cz).map resSp).Normal :=
    Subgroup.Normal.map CFSG.pCore_normal resSp resSp_surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 Cz).map resSp) with h | h
  · rw [← ker_resSp]
    exact (Subgroup.map_eq_bot_iff _).mp h
  · exfalso
    have hp : IsPGroup 2 ((CFSG.pCore 2 Cz).map resSp) := CFSG.pCore_isPGroup.map resSp
    rw [h] at hp
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
    rw [Subgroup.card_top, natCard_sp62] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 1451520)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem natCard_pCore_Cz :
    Nat.card (CFSG.pCore 2 Cz) = 2 ^ 9 := by
  rw [pCore_Cz]
  exact natCard_Q_subgroupOf

theorem hE_mem_Qsub (i : Fin 8) : hE i ∈ Qsub :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨i, rfl⟩)

theorem mem_pCore_Cz
    {g : Cz} (h : (g : K) ∈ Qsub) : g ∈ CFSG.pCore 2 Cz := by
  rw [pCore_Cz]
  exact h

theorem hE_noncomm :
    hE 0 * hE 4 ≠ hE 4 * hE 0 := by
  intro h
  have h2 := hE_rel.comm 0 4
  rw [h, show hypMat 0 4 = 1 by decide, ZMod.val_one, pow_one] at h2
  exact z0_ne_one (mul_left_cancel (h2.symm.trans (mul_one _).symm))

@[expose] noncomputable def xE : K := frE 8

theorem xE_val :
    xE.val.val = rowsMatrix 22 (Native.fRows seedRowsArr)[8]! := frE_val (by norm_num)

theorem xE_mem_Cz :
    xE ∈ Cz := S0_le_Cz (frE_mem_S0 (by norm_num))

theorem xFpf_spec :
    ∀ s < 2, ∀ v < 255, Native.commRows (Native.fRows seedRowsArr)[8]!
    (Native.nfRows seedRowsArr hR s (v + 1)) = false := by
  have h := xFpf_check
  simp only [Native.xFpfOK, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  exact h

theorem xE_not_comm
    (σ : ZMod 2) {u : Fin 8 → ZMod 2} (hu : u ≠ 0) :
    xE * nf z0 hE σ u ≠ nf z0 hE σ u * xE := by
  obtain ⟨v, hv, rfl⟩ := exists_bitVec u
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hu (funext fun i => by simp [bitVec])
  obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hv0
  rw [Ne, commute_iff_commRows xE_val (nf_val σ (w + 1)) (validM_fRows (by norm_num))
    (validM_nfRows _ _), xFpf_spec σ.val (ZMod.val_lt σ) w (by omega)]
  exact Bool.false_ne_true

theorem xE_ne_one :
    xE ≠ 1 := by
  intro h
  have hu : (Pi.single 0 1 : Fin 8 → ZMod 2) ≠ 0 := by
    intro h'
    have := congrFun h' 0
    simp at this
  exact xE_not_comm 0 hu (by rw [h, one_mul, mul_one])

@[expose] noncomputable def xC :
    Cz := ⟨xE, xE_mem_Cz⟩

theorem orderOf_xC :
    orderOf xC = 5 :=
  orderOf_eq_prime (Subtype.ext frE_x_pow) fun h => xE_ne_one (congrArg Subtype.val h)

theorem exists_conj_xC_mem
    (P : Sylow 5 Cz) : ∃ g : Cz, g * xC * g⁻¹ ∈ P := by
  have hp : IsPGroup 5 (Subgroup.zpowers xC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_xC, pow_one])
  obtain ⟨P', hP'⟩ := hp.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Cz P' P
  refine ⟨g, ?_⟩
  have h := Subgroup.smul_mem_pointwise_smul xC (MulAut.conj g) (P' : Subgroup Cz)
    (hP' (Subgroup.mem_zpowers xC))
  rw [MulAut.smul_def, MulAut.conj_apply] at h
  exact h

theorem z0_pow_comm
    (h : Cz) (n : ℕ) : (h : K) * z0 ^ n = z0 ^ n * h :=
  (Commute.pow_right (comm_of_mem_Cz h.2) n).eq

theorem sylow_five_Cz :
    ∀ P : Sylow 5 Cz, ∀ y ∈ CFSG.pCore 2 Cz, (∀ p ∈ P, p * y = y * p) →
    ∀ w ∈ CFSG.pCore 2 Cz, y * w = w * y := by
  intro P y hy hP w _
  obtain ⟨g, hg⟩ := exists_conj_xC_mem P
  have hc := hP _ hg
  have hy' : g⁻¹ * y * g ∈ CFSG.pCore 2 Cz := by
    have := (CFSG.pCore_normal (p := 2) (G := Cz)).conj_mem y hy g⁻¹
    rwa [inv_inv] at this
  rw [pCore_Cz, Subgroup.mem_subgroupOf] at hy'
  obtain ⟨σ, u, hσu⟩ := (mem_closure_iff hE_rel).mp hy'
  have hcomm : xC * (g⁻¹ * y * g) = (g⁻¹ * y * g) * xC :=
    calc xC * (g⁻¹ * y * g) = g⁻¹ * ((g * xC * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * xC * g⁻¹)) * g := by rw [hc]
      _ = (g⁻¹ * y * g) * xC := by group
  by_cases hu : u = 0
  · subst hu
    rw [nf_zero_vec] at hσu
    have hcen : ∀ h : Cz, (g⁻¹ * y * g) * h = h * (g⁻¹ * y * g) := fun h => by
      apply Subtype.ext
      show ((g⁻¹ * y * g : Cz) : K) * h = h * ((g⁻¹ * y * g : Cz) : K)
      rw [← hσu]
      exact (z0_pow_comm h σ.val).symm
    have hyc : y = g⁻¹ * y * g := by
      calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = (g⁻¹ * y * g) * g * g⁻¹ := by rw [← hcen g]
        _ = g⁻¹ * y * g := by group
    rw [hyc]
    exact hcen w
  · exact absurd (by rw [hσu]; exact congrArg Subtype.val hcomm) (xE_not_comm σ hu)

theorem smithLocal_Cz :
    SmithLocal Cz where
  card_pCore := natCard_pCore_Cz
  pCore_noncomm := ⟨⟨hE 0, hE_mem_Cz 0⟩, mem_pCore_Cz (hE_mem_Qsub 0), ⟨hE 4, hE_mem_Cz 4⟩,
    mem_pCore_Cz (hE_mem_Qsub 4), fun h => hE_noncomm (congrArg Subtype.val h)⟩
  quotient_equiv := ⟨(QuotientGroup.quotientMulEquivOfEq pCore_Cz).trans quotientEquiv⟩
  sylow_five := sylow_five_Cz

theorem orderOf_z0 :
    orderOf z0 = 2 :=
  orderOf_eq_prime (by rw [sq]; exact seedA_mul_self) z0_ne_one

theorem index_Cz :
    Cz.index = 56925 := by
  have h := Subgroup.card_mul_index Cz
  rw [natCard_centralizer_z0, CFSG.Sporadic.Co2.card_Co2] at h
  omega

@[expose] noncomputable def z0C : Cz := ⟨z0, z0_mem_Cz⟩

theorem zpowers_z0C_normal : (Subgroup.zpowers z0C).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : g * z0C = z0C * g := Subtype.ext (comm_of_mem_Cz g.2)
  rw [((Commute.zpow_right hc k)).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers z0C k

theorem orderOf_z0C :
    orderOf z0C = 2 :=
  orderOf_eq_prime (Subtype.ext (by rw [Subgroup.coe_pow, sq]; exact seedA_mul_self))
    fun h => z0_ne_one (congrArg Subtype.val h)

theorem exists_sylow_two_z0 :
    ∃ S : Sylow 2 K, z0 ∈ S ∧ ∀ g ∈ S, g * z0 = z0 * g := by
  obtain ⟨T⟩ : Nonempty (Sylow 2 Cz) := inferInstance
  have hT' : IsPGroup 2 ((T : Subgroup Cz).map Cz.subtype) := T.isPGroup'.map Cz.subtype
  have hidx : ¬ 2 ∣ ((T : Subgroup Cz).map Cz.subtype).index := by
    rw [Subgroup.index_map_subtype, index_Cz]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    · exact T.not_dvd_index h
    · norm_num at h
  have hz : IsPGroup 2 (Subgroup.zpowers z0C) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_z0C, pow_one])
  have hzT : Subgroup.zpowers z0C ≤ T := by
    have := zpowers_z0C_normal
    exact hz.le_sylow_of_normal T
  refine ⟨hT'.toSylow hidx, ⟨z0C, hzT (Subgroup.mem_zpowers z0C), rfl⟩, ?_⟩
  rintro g ⟨h, -, rfl⟩
  exact comm_of_mem_Cz h.2

end CFSG.Sporadic.Co2Smith
