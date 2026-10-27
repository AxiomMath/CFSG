module

public import CFSG.Quasithin.Vol2.Ch11SecS12E
public import CFSG.Quasithin.Background.G2SL3Setting
public import CFSG.Quasithin.Vol2.Ch11SecA11SL2
public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.SL3Model CFSG.Quasithin.SL2Model
open CFSG.Quasithin.Vol2.Ch11
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] {n : ℕ} {L K V V₁ : Subgroup G}

section Pt

variable {F : Type} [Field F]

theorem exists_smul_e0 {A : SL(3, F)} (hA : A ∈ Pt (vE F 0)) :
    ∃ a : F, a ≠ 0 ∧ A • vE F 0 = a • vE F 0 ∧ A⁻¹ • vE F 0 = a⁻¹ • vE F 0 := by
  obtain ⟨a, ha⟩ := hA
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    have h1 := congrArg (fun w => A⁻¹ • w) ha
    simp only [inv_smul_smul, smul_zero] at h1
    have := congrFun h1 0
    simp [vE] at this
  refine ⟨a, ha0, ha, ?_⟩
  rw [inv_smul_eq_iff, smul_comm, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem commutator_Pt_le_stab0 : ⁅Pt (vE F 0), Pt (vE F 0)⁆ ≤ stab0 F := by
  rw [Subgroup.commutator_le]
  intro A hA B hB
  obtain ⟨a, ha0, ha, ha'⟩ := exists_smul_e0 hA
  obtain ⟨b, hb0, hb, hb'⟩ := exists_smul_e0 hB
  show ⁅A, B⁆ • vE F 0 = vE F 0
  have h2 : A⁻¹ • (b⁻¹ • vE F 0) = b⁻¹ • (a⁻¹ • vE F 0) := by rw [smul_comm A⁻¹ b⁻¹, ha']
  have h3 : B • (b⁻¹ • (a⁻¹ • vE F 0)) = b⁻¹ • (a⁻¹ • (b • vE F 0)) := by
    rw [smul_comm B b⁻¹, smul_comm B a⁻¹, hb]
  have h4 : A • (b⁻¹ • (a⁻¹ • (b • vE F 0))) = b⁻¹ • (a⁻¹ • (b • (a • vE F 0))) := by
    rw [smul_comm A b⁻¹, smul_comm A a⁻¹, smul_comm A b, ha]
  rw [commutatorElement_def, mul_smul, mul_smul, mul_smul, hb', h2, h3, h4, smul_smul,
    smul_smul, smul_smul]
  rw [show b⁻¹ * a⁻¹ * b * a = 1 by field_simp, one_smul]

end Pt

namespace NatData3'

variable (D : NatData3 n L K V V₁)

theorem theta_mem_Pt (hV₁V : V₁ ≤ V) (a : L) (ha : (a : G) ∈ Subgroup.normalizer (V₁ : Set G)) :
    D.θ a ∈ Pt (vE (GaloisField 2 n) 0) := by
  set v₀ : V := D.ψ.symm (Multiplicative.ofAdd (vE (GaloisField 2 n) 0)) with hv₀
  have hψ : D.ψ v₀ = Multiplicative.ofAdd (vE (GaloisField 2 n) 0) :=
    MulEquiv.apply_symm_apply _ _
  have hv₀1 : (v₀ : G) ∈ V₁ := (D.line v₀).2 ⟨1, by rw [hψ, toAdd_ofAdd, one_smul]⟩
  have h1 : (a : G) * v₀ * (a : G)⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.1 ha _).1 hv₀1
  have hV : (a : G) * v₀ * (a : G)⁻¹ ∈ V := hV₁V h1
  have h2 : conjAct V ⟨a, D.hnorm a.2⟩ v₀ = ⟨(a : G) * v₀ * (a : G)⁻¹, hV⟩ :=
    Subtype.ext (by rw [conjAct_coe_apply])
  obtain ⟨c, hc⟩ := (D.line ⟨(a : G) * v₀ * (a : G)⁻¹, hV⟩).1 h1
  have h3 := D.equiv a v₀
  rw [h2, hψ, natAct3_apply, toAdd_ofAdd] at h3
  have h4 := congrArg Multiplicative.toAdd h3
  rw [toAdd_ofAdd, hc] at h4
  exact ⟨c, h4.symm⟩

theorem conj_mem_V₁ (a : L) (ha : D.θ a ∈ Pt (vE (GaloisField 2 n) 0)) (v : V)
    (hv : (v : G) ∈ V₁) : (a : G) * v * (a : G)⁻¹ ∈ V₁ := by
  obtain ⟨c, hc⟩ := (D.line v).1 hv
  obtain ⟨r, hr⟩ := ha
  have h1 := (D.line (conjAct V ⟨a, D.hnorm a.2⟩ v)).2 ⟨c * r, ?_⟩
  · simpa [conjAct_coe_apply] using h1
  · rw [D.equiv, natAct3_apply, toAdd_ofAdd, hc, smul_comm, hr, smul_smul]

theorem mem_normalizer_of_mem_Pt (hV₁V : V₁ ≤ V) (a : L)
    (ha : D.θ a ∈ Pt (vE (GaloisField 2 n) 0)) :
    (a : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_V₁ D a ha ⟨h, hV₁V hh⟩ hh
  · intro hh
    have hV : (a : G) * h * (a : G)⁻¹ ∈ V := hV₁V hh
    have hhV : h ∈ V := (Subgroup.mem_normalizer_iff.1 (D.hnorm a.2) h).2 hV
    have ha' : D.θ a⁻¹ ∈ Pt (vE (GaloisField 2 n) 0) := by
      rw [map_inv]
      exact inv_mem ha
    have := conj_mem_V₁ D a⁻¹ ha' ⟨(a : G) * h * (a : G)⁻¹, hV⟩ hh
    simpa [mul_assoc] using this

theorem map_theta_N (hV₁V : V₁ ≤ V) :
    ((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L).map D.θ =
      Pt (vE (GaloisField 2 n) 0) := by
  ext A
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact theta_mem_Pt D hV₁V a (Subgroup.mem_subgroupOf.1 ha).2
  · intro hA
    obtain ⟨a, rfl⟩ := D.surj A
    exact ⟨a, Subgroup.mem_subgroupOf.2 ⟨a.2, mem_normalizer_of_mem_Pt D hV₁V a hA⟩, rfl⟩

theorem lOf_le : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left

variable [Finite G]

theorem lOf_eq_map :
    LOf L V₁ = (perfectCore ((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L)).map
      L.subtype :=
  by rw [map_perfectCore L.subtype _, Subgroup.map_subgroupOf_eq_of_le inf_le_left]

theorem map_theta_perfectCore (hV₁V : V₁ ≤ V) :
    (perfectCore ((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L)).map D.θ =
      perfectCore (Pt (vE (GaloisField 2 n) 0)) := by
  rw [map_perfectCore, map_theta_N D hV₁V]

theorem theta_mem_stab0 (hV₁V : V₁ ≤ V) (l : ↥(LOf L V₁)) :
    D.θ (Subgroup.inclusion lOf_le l) ∈ stab0 (GaloisField 2 n) := by
  have hl : (l : G) ∈ (perfectCore ((L ⊓ Subgroup.normalizer (V₁ : Set G)).subgroupOf L)).map
      L.subtype := (lOf_eq_map (L := L) (V₁ := V₁)) ▸ l.2
  obtain ⟨a, ha, hal⟩ := hl
  have hae : a = Subgroup.inclusion lOf_le l := Subtype.ext hal
  have h1 : D.θ a ∈ perfectCore (Pt (vE (GaloisField 2 n) 0)) :=
    map_theta_perfectCore D hV₁V ▸ ⟨a, ha, rfl⟩
  rw [← hae]
  exact commutator_Pt_le_stab0 ((iInf_le (derivedSeriesOf _) 1 :
    perfectCore (Pt (vE (GaloisField 2 n) 0)) ≤ derivedSeriesOf _ 1) h1)

@[expose] noncomputable def theta1 (hV₁V : V₁ ≤ V) : ↥(LOf L V₁) →* ↥(stab0 (GaloisField 2 n)) :=
  (D.θ.comp (Subgroup.inclusion lOf_le)).codRestrict (stab0 _) (theta_mem_stab0 D hV₁V)

theorem theta1_coe (hV₁V : V₁ ≤ V) (l : ↥(LOf L V₁)) :
    (theta1 D hV₁V l : SL(3, GaloisField 2 n)) = D.θ (Subgroup.inclusion lOf_le l) := rfl

@[expose] noncomputable def alpha0SL (hV₁V : V₁ ≤ V) : ↥(LOf L V₁) →* SL(2, GaloisField 2 n) :=
  (levi _).comp (theta1 D hV₁V)

theorem alpha0SL_apply (hV₁V : V₁ ≤ V) (l : ↥(LOf L V₁)) :
    alpha0SL D hV₁V l = levi _ (theta1 D hV₁V l) := rfl

theorem alpha0SL_surjective (hn : 2 ≤ n) (hV₁V : V₁ ≤ V) :
    Function.Surjective (alpha0SL D hV₁V) := by
  intro M
  have hn0 : n ≠ 0 := by omega
  have hperf : Group.IsPerfect (SL(2, GaloisField 2 n)) := by
    have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset (GaloisField 2 n)).card by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 n hn0]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
    exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
  have hrange : ⁅(blk : SL(2, GaloisField 2 n) →* SL(3, GaloisField 2 n)).range,
      (blk : SL(2, GaloisField 2 n) →* SL(3, GaloisField 2 n)).range⁆ =
        (blk : SL(2, GaloisField 2 n) →* SL(3, GaloisField 2 n)).range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      hperf.commutator_eq_top]
  have hle : (blk : SL(2, GaloisField 2 n) →* SL(3, GaloisField 2 n)).range ≤
      perfectCore (Pt (vE (GaloisField 2 n) 0)) := by
    refine le_perfectCore_of_perfect ?_ hrange
    rintro _ ⟨M', rfl⟩
    exact blk_mem_Pt M'
  have hM : blk M ∈ perfectCore (Pt (vE (GaloisField 2 n) 0)) := hle ⟨M, rfl⟩
  rw [← map_theta_perfectCore D hV₁V] at hM
  obtain ⟨a, ha, hθa⟩ := hM
  have haL : (a : G) ∈ LOf L V₁ := (lOf_eq_map (L := L) (V₁ := V₁)) ▸ ⟨a, ha, rfl⟩
  refine ⟨⟨a, haL⟩, ?_⟩
  rw [alpha0SL_apply]
  have h1 : theta1 D hV₁V ⟨a, haL⟩ = ⟨blk M, blk_mem_stab0 M⟩ := by
    apply Subtype.ext
    rw [theta1_coe]
    exact hθa
  rw [h1, levi_blk]

theorem alpha0SL_ker (hn : 2 ≤ n) (hV₁V : V₁ ≤ V) (hK : IsPGroup 2 ↥K) :
    (alpha0SL D hV₁V).ker = (pCoreOf 2 (LOf L V₁)).subgroupOf (LOf L V₁) := by
  have hn0 : n ≠ 0 := by omega
  have : CharP (GaloisField 2 n) 2 := inferInstance
  have hsurj := alpha0SL_surjective D hn hV₁V
  apply le_antisymm
  ·
    intro l hl
    have hl2 : ∀ y ∈ (alpha0SL D hV₁V).ker, ∃ k : ℕ, ((y : ↥(LOf L V₁)) : G) ^ 2 ^ k = 1 := by
      intro y hy
      have hQ := mem_Qv_of_levi_eq_one hy
      have hsq := Qv_sq _ hQ
      rw [← Subgroup.coe_mul, ← map_mul] at hsq
      have hθ : D.θ (Subgroup.inclusion lOf_le (y * y)) = 1 := by
        rw [← theta1_coe]
        exact hsq
      have hmem : Subgroup.inclusion lOf_le (y * y) ∈ D.θ.ker := hθ
      rw [D.ker_eq, Subgroup.mem_subgroupOf] at hmem
      obtain ⟨k, hk⟩ := hK ⟨_, hmem⟩
      refine ⟨k + 1, ?_⟩
      have hk' : (((y * y : ↥(LOf L V₁)) : G)) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      rw [Subgroup.coe_mul, ← sq, ← pow_mul, ← pow_succ'] at hk'
      exact hk'
    have hP : IsPGroup 2 ↥((alpha0SL D hV₁V).ker.map (LOf L V₁).subtype) := by
      intro z
      obtain ⟨y, hy, hyz⟩ := z.2
      obtain ⟨k, hk⟩ := hl2 y hy
      refine ⟨k, Subtype.ext ?_⟩
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hyz]
      simpa using hk
    have hN : (((alpha0SL D hV₁V).ker.map (LOf L V₁).subtype).subgroupOf (LOf L V₁)).Normal := by
      have e : ((alpha0SL D hV₁V).ker.map (LOf L V₁).subtype).subgroupOf (LOf L V₁) =
          (alpha0SL D hV₁V).ker :=
        Subgroup.comap_map_eq_self_of_injective (LOf L V₁).subtype_injective _
      rw [e]
      exact MonoidHom.normal_ker _
    have := CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le _) hN hP ⟨l, hl, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr this
  ·
    have hsimple := SecA.isSimpleGroup_SL2 (K := GaloisField 2 n) hn (GaloisField.card 2 n hn0)
    set P := ((pCoreOf 2 (LOf L V₁)).subgroupOf (LOf L V₁)).map (alpha0SL D hV₁V) with hPdef
    have hPn : P.Normal := by
      refine Subgroup.Normal.map ?_ _ hsurj
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    have hP2 : IsPGroup 2 ↥P := by
      refine IsPGroup.map ?_ _
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).of_equiv
        (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).symm
    rcases hsimple.eq_bot_or_eq_top_of_normal P with hb | ht
    · intro l hl
      have : alpha0SL D hV₁V l ∈ P := ⟨l, hl, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have hpg : IsPGroup 2 (SL(2, GaloisField 2 n)) :=
        hP2.of_equiv ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnt : Nontrivial (SL(2, GaloisField 2 n)) := hsimple.toNontrivial
      have hZ := hpg.center_nontrivial
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (SL(2, GaloisField 2 n)))
        with hZb | hZt
      · rw [hZb] at hZ
        exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hZ
      · obtain ⟨a, b, hab⟩ := exists_ne (1 : SL(2, GaloisField 2 n)) |> fun _ =>
          (show ∃ a b : SL(2, GaloisField 2 n), a * b ≠ b * a by
            by_contra hc
            push Not at hc
            have hcomm : commutator (SL(2, GaloisField 2 n)) = ⊥ := by
              rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
              intro x _
              rw [Subgroup.mem_centralizer_iff]
              intro y _
              exact hc y x
            have hperf : Group.IsPerfect (SL(2, GaloisField 2 n)) := by
              have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
              obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
                (show 4 ≤ (Finset.univ : Finset (GaloisField 2 n)).card by
                  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 n hn0]
                  calc 4 = 2 ^ 2 := by norm_num
                    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
              exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨t, ht⟩
            rw [hperf.commutator_eq_top] at hcomm
            exact (top_ne_bot hcomm))
        have ha : a ∈ Subgroup.center (SL(2, GaloisField 2 n)) := hZt ▸ Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.mp ha b).symm

@[expose] noncomputable def alpha0 (hV₁V : V₁ ≤ V) :
    ↥(LOf L V₁) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 n)) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 n)).toMonoidHom.comp
    (alpha0SL D hV₁V)

theorem alpha0_coe (hV₁V : V₁ ≤ V) (l : ↥(LOf L V₁)) :
    (((alpha0 D hV₁V l : ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 (GaloisField 2 n))) :
      GL (Fin 2) (GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) =
      ((levi _ (theta1 D hV₁V l) : SL(2, GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) _) := rfl

theorem alpha0_surjective (hn : 2 ≤ n) (hV₁V : V₁ ≤ V) : Function.Surjective (alpha0 D hV₁V) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 _).surjective.comp
    (alpha0SL_surjective D hn hV₁V)

theorem alpha0_ker (hn : 2 ≤ n) (hV₁V : V₁ ≤ V) (hK : IsPGroup 2 ↥K) :
    (alpha0 D hV₁V).ker = (pCoreOf 2 (LOf L V₁)).subgroupOf (LOf L V₁) := by
  rw [← alpha0SL_ker D hn hV₁V hK]
  ext l
  simp [alpha0, MonoidHom.mem_ker]

end NatData3'

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
