module

public import CFSG.Quasithin.Vol2.Ch10SecC8V1
public import CFSG.Quasithin.Vol2.Ch10SecABasicCent

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem Q_le_T1 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    (h1011 : Stmt10_1_1) : T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ T1 T L := by
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, hV1, hV2, hcap⟩ := hdec t ht htn
  rintro q ⟨hqT, hqV⟩
  refine ⟨hqT, ?_⟩
  rcases SecA.conjugate_eq_or h37 h38 hyp ht htn (SecA.le_fsuM T L hqT) with h | h
  · exact SecA.conjugate_eq_self_iff.mp h
  · exfalso
    have hV1V : fsuUL T L I ≤ fsuVM T L I :=
      commutator_le_left_of_le_normalizer
        ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
    have hq1 : CFSG.conjugate (fsuUL T L I) q = fsuUL T L I := by
      apply le_antisymm
      · rintro _ ⟨v, hv, rfl⟩
        have hc := Subgroup.mem_centralizer_iff.mp hqV v (hV1V hv)
        have : (MulAut.conj q⁻¹).toMonoidHom v = v := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          rw [mul_assoc, hc]
          group
        rw [this]
        exact hv
      · intro v hv
        rw [SecA.mem_conjugate_iff]
        have hc := Subgroup.mem_centralizer_iff.mp hqV v (hV1V hv)
        rw [← hc]
        simpa using hv
    have hq2 : CFSG.conjugate (fsuUL T L I) q = ⁅fsuVM T L I, CFSG.conjugate L t⁆ := by
      rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L hqT), h]
    rw [hq1] at hq2
    have hV1C : fsuUL T L I ≤ fsuCVM T L I := by
      intro v hv
      rw [← hcap]
      exact ⟨Subgroup.mem_sup_left hv, Subgroup.mem_sup_left (hq2 ▸ hv)⟩
    apply SecA.commutator_fsuVM_ne_bot hyp.fsu
    have hcomm : ⁅⁅fsuVM T L I, L⁆, L⁆ = ⁅fsuVM T L I, L⁆ := commutator_fsuUL_eq hyp
    rw [← hcomm, eq_bot_iff, Subgroup.commutator_le]
    intro v hv l hl
    have hc := Subgroup.mem_centralizer_iff.mp (hV1C hv).2 l (SecA.le_fsuL0 T L hl)
    rw [commutatorElement_def, Subgroup.mem_bot, ← hc]
    group

theorem fsuVM_ne_bot (hyp : Hyp10 G T L I) : fsuVM T L I ≠ ⊥ := by
  intro h
  apply SecA.commutator_fsuVM_ne_bot hyp.fsu
  rw [h, Subgroup.commutator_bot_left]

theorem fsuVM_le_Q (hyp : Hyp10 G T L I) :
    fsuVM T L I ≤ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
  refine le_inf (SecA.fsuVM_le_T hyp) fun v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val ((SecA.isElemAbelian_fsuVM hyp).1.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

theorem inf_centralizer_Q_le (hyp : Hyp10 G T L I) (h1027 : Stmt10_2_7) :
    (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer
        ((T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) ≤
      T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have hQ := (h1027 G T L I hyp).2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hH : InH (S : Subgroup G) (fsuL0 T L ⊔ T) := by
    refine ⟨hS ▸ le_sup_right, ?_⟩
    rw [← hQ]
    exact fun h => fsuVM_ne_bot hyp (le_bot_iff.mp (h ▸ fsuVM_le_Q hyp))
  have hc := charTwo_of_inH hyp.fsu.qtke.2.1 S hH
  rw [hQ]
  exact hc

theorem omegaOne_le_Q (hyp : Hyp10 G T L I) (h1027 : Stmt10_2_7)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (h1011 : Stmt10_1_1) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ∧
      omegaOneCenterOf (T1 T L) ≤ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have hle := inf_centralizer_Q_le hyp h1027
  have hQT1 := Q_le_T1 h37 h38 hyp h1011
  refine ⟨(Subgroup.closure_le _).mpr ?_, (Subgroup.closure_le _).mpr ?_⟩
  · rintro z ⟨⟨hzT, hzc⟩, -⟩
    exact hle ⟨Subgroup.mem_sup_right hzT, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_iff.mp hzc q hq.1⟩
  · rintro z ⟨⟨hzT, hzc⟩, -⟩
    exact hle ⟨Subgroup.mem_sup_right hzT.1, Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_iff.mp hzc q (hQT1 hq)⟩

theorem isUniqueM_L0T (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6) :
    IsUniqueM (fsuL0 T L ⊔ T) (fsuM T L) := by
  obtain ⟨⟨hM, -⟩, huniq⟩ := (h1026 G T L I hyp).1
  refine ⟨⟨hM, sup_le (SecA.fsuL0_le_fsuM T L) (SecA.le_fsuM T L)⟩, fun M' hM' => huniq M' ?_⟩
  exact ⟨hM'.1, (sup_le_sup_left inf_le_left _).trans hM'.2⟩

theorem exists_mem_center_fsuCVM (hyp : Hyp10 G T L I) (hcv : fsuCVM T L I ≠ ⊥) :
    ∃ z ∈ fsuCVM T L I, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) ∧ z ^ 2 = 1 ∧
      z ∈ quasithinOmegaOneCenter T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCT : fsuCVM T L I ≤ T := inf_le_left.trans (SecA.fsuVM_le_T hyp)
  have hTn : T ≤ Subgroup.normalizer (fsuCVM T L I : Set G) :=
    le_normalizer_inf' (SecA.le_normalizer_fsuVM T L I)
      (SecA.le_normalizer_centralizer (SecA.le_fsuM T L))
  have hN : ((fsuCVM T L I).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).mpr hTn
  have hnil : Group.IsNilpotent ↥T := hyp.fsu.sylow.1.isNilpotent
  have hne : (fsuCVM T L I).subgroupOf T ≠ ⊥ := by
    intro h
    apply hcv
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hCT hx⟩ : ↥T) ∈ (fsuCVM T L I).subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨a, ha1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one).mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hzC : ((a : ↥T) : G) ∈ fsuCVM T L I := a.2.1
  have hzZ : (a : ↥T) ∈ Subgroup.center ↥T := a.2.2
  have hcT : ((a : ↥T) : G) ∈ Subgroup.centralizer (T : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨y, hy⟩)
  have hsq : ((a : ↥T) : G) ^ 2 = 1 := (SecA.isElemAbelian_fsuVM hyp).2 _ hzC.1
  exact ⟨((a : ↥T) : G), hzC, fun h => ha1 (Subtype.ext (Subtype.ext h)), hcT, hsq,
    Subgroup.subset_closure ⟨⟨(a : ↥T).2, hcT⟩, hsq⟩⟩

theorem centralizer_le_fsuM (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6) {z : G}
    (hzC : z ∈ fsuCVM T L I) (hz1 : z ≠ 1) (hzZ : z ∈ Subgroup.centralizer (T : Set G))
    (hz2 : z ^ 2 = 1) : Subgroup.centralizer ({z} : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)) := by
    refine ⟨Subgroup.zpowers z, ?_, ?_, rfl⟩
    · rw [Ne, Subgroup.zpowers_eq_bot]
      exact hz1
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1, pow_one])
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hcz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    intro y hy
    have hc : y * z * y⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hy z rfl]
      group
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp only [← conj_zpow, hc]⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hk' : z ^ k = y * w * y⁻¹ := hk
      have : y * (z ^ k) * y⁻¹ = z ^ k := by rw [← conj_zpow, hc]
      rw [← this] at hk'
      have := congrArg (fun u => y⁻¹ * u * y) hk'
      simp only [mul_assoc, inv_mul_cancel_left] at this
      simpa [mul_assoc] using this
  have hL0T : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine (sup_le ?_ ?_).trans hcz
    · intro l hl
      exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (Subgroup.mem_centralizer_iff.mp hzC.2 l hl).symm
    · intro s hs
      exact Subgroup.mem_centralizer_iff.mpr fun w hw => by
        rw [Set.mem_singleton_iff] at hw
        rw [hw]
        exact (Subgroup.mem_centralizer_iff.mp hzZ s hs).symm
  have hM'eq := (isUniqueM_L0T hyp h1026).2 M' ⟨hM', hL0T.trans hle⟩
  rw [← hM'eq]
  exact hcz.trans hle

theorem commutator_Z_ne_bot (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6)
    (hcv : fsuCVM T L I ≠ ⊥) :
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
  obtain ⟨z, hzC, hz1, hzT, hz2, hzZ⟩ := exists_mem_center_fsuCVM hyp hcv
  intro H hH hbot
  apply hH.2.1
  refine le_trans ?_ (centralizer_le_fsuM hyp h1026 hzC hz1 hzT hz2)
  intro h hh
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  have hc : ⁅z, h⁆ ∈ ⁅quasithinOmegaOneCenter T, H⁆ := Subgroup.commutator_mem_commutator hzZ hh
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

end CFSG.Quasithin.Vol2.Ch10.SecC
