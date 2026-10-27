module

public import CFSG.Quasithin.H13.NQCatT513U35Y
public import CFSG.Quasithin.H13.NQCatT513U35Core
public import CFSG.Quasithin.H13.NQCatT513PSL2
public import Certificates.Certificate7159
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSylowNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.C1PackS15212C
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S152Y15
public import CFSG.Quasithin.EmptyFaithful.S152Y19
public import CFSG.Quasithin.Vol2.Ch10SecB4
public import CFSG.Quasithin.Vol2.KGFactAutSylowSmall
public import CFSG.Quasithin.Vol2.KGFactU35Star
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.Quasithin.H13.NQCat.T513

open CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise

local notation "L24" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)

namespace U35

open U35Perm HNUnitaryBridge CFSG.RankThree.PartOne.HNB Matrix
open CFSG.Quasithin.H13.KGU35 (f25Data suMat suMat_apply suMat_injective mem_SU)
open CFSG.Quasithin.H13.KGAutSyl.U35Syl (Rm RR SS coe_RR RR_pow)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem mem_range_psuConj_of_odd {α : MulAut PU} (hα : Odd (orderOf α)) :
    α ∈ (psuConj f25Data).range := by
  obtain ⟨k, hk⟩ := hα
  set γ := α ^ (k + 1) with hγdef
  have hγ : γ * γ = α := by
    rw [hγdef, ← pow_add, show k + 1 + (k + 1) = orderOf α + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField (h := f25Data) (by norm_num) γ
  have hσ : σ * σ = 1 :=
    ringAut_mul_self Nat.prime_five (by norm_num) le_rfl (by rw [F25.card]; norm_num) σ
  refine ⟨A * ⟨_, CFSG.RankThree.PartTwo.KFacts.glAut_mem_unitaryIsom3 σ A.2⟩, ?_⟩
  rw [← hγ, hAσ, map_mul, ← psuField_mul_psuConj_mul_inv]
  calc psuConj f25Data A * (psuField f25Data σ * psuConj f25Data A * (psuField f25Data σ)⁻¹)
      = psuConj f25Data A * (psuField f25Data σ * psuConj f25Data A * (psuField f25Data σ)⁻¹) *
          psuField f25Data (σ * σ) := by rw [hσ, map_one, mul_one]
    _ = _ := by rw [map_mul]; group

theorem psuConj_pow_three (A : unitaryIsom3 f25Data) :
    ∃ y : PU, psuConj f25Data A ^ 3 = MulAut.conj y := by
  set d : F25ˣ := Matrix.GeneralLinearGroup.det (A : GL (Fin 3) F25) with hd
  have hdn : (d : F25) ^ 6 = 1 := by
    have h1 := det_norm (unitary_mat A)
    rw [hd, Matrix.GeneralLinearGroup.val_det_apply, ← pow_succ] at *
    exact h1
  have hd0 : (d : F25) ≠ 0 := d.ne_zero
  have hdm := scalar_mem_isom hdn hd0
  set Z : unitaryIsom3 f25Data := ⟨_, hdm⟩ with hZ
  have hB : ((A ^ 3 * Z⁻¹ : unitaryIsom3 f25Data) : GL (Fin 3) F25) ∈ SU := by
    refine mem_SU.mpr ⟨?_, ?_⟩
    · rw [← Matrix.GeneralLinearGroup.val_det_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, map_mul, map_pow, map_inv,
        hZ, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
      rw [← hd, Units.mk0_val, mul_inv_cancel, Units.val_one]
    · have := unitary_mat (A ^ 3 * Z⁻¹)
      exact this
  refine ⟨proj ⟨_, hB⟩, ?_⟩
  rw [conj_proj]
  have hW : (⟨((⟨_, hB⟩ : ↥SU) : GL (Fin 3) F25),
      unitarySU_le_unitaryIsom3 (⟨_, hB⟩ : ↥SU).2⟩ : unitaryIsom3 f25Data) = A ^ 3 * Z⁻¹ := rfl
  rw [hW, map_mul, map_inv, map_pow, show psuConj f25Data Z = 1 from psuConj_scalar hdm, inv_one,
    mul_one]

theorem inner_of_two {α : MulAut PU} (hα : α ∈ (psuConj f25Data).range)
    (h2 : ∃ n : ℕ, α ^ (2 ^ n) = 1) : ∃ y : PU, α = MulAut.conj y := by
  obtain ⟨A, rfl⟩ := hα
  obtain ⟨n, hn⟩ := h2
  obtain ⟨y, hy⟩ := psuConj_pow_three A
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop (by positivity)
  refine ⟨y ^ u, ?_⟩
  have h1 : psuConj f25Data A = psuConj f25Data A ^ (3 * u) := by
    rw [pow_eq_pow_mod (3 * u) hn, hu, ← pow_eq_pow_mod 1 hn, pow_one]
  rw [h1, pow_mul, hy, map_pow]

theorem conj_mem_range (y : PU) : MulAut.conj y ∈ (psuConj f25Data).range := by
  obtain ⟨g, rfl⟩ := unitaryProj_surjective f25Data 3 y
  exact ⟨_, (conj_proj g).symm⟩


theorem center_PU : Subgroup.center PU = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hs0 := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F25 5 1
    (by rw [F25.card]; norm_num) 3 le_rfl (by decide)
  have hs : IsSimpleGroup PU := (unitaryPSUEquiv f25Data (n := 3) (by norm_num)).isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center PU) with h | h
  · exact h
  · exfalso
    have hcard := card_PU
    have hab : ∀ a b : PU, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have hs2 : ∀ H : Subgroup PU, H = ⊥ ∨ H = ⊤ := fun H => by
      have : H.Normal := ⟨fun n hn g => by rw [hab g n, mul_inv_cancel_right]; exact hn⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := PU) 2 (by rw [hcard]; norm_num)
    rcases hs2 (Subgroup.zpowers y) with h1 | h1
    · rw [Subgroup.zpowers_eq_bot] at h1
      rw [h1, orderOf_one] at hy
      norm_num at hy
    · have h2 := congrArg (fun H : Subgroup PU => Nat.card H) h1
      simp only [Nat.card_zpowers, hy, Subgroup.card_top, hcard] at h2
      norm_num at h2

theorem conj_injective_PU : Function.Injective (MulAut.conj : PU →* MulAut PU) :=
  conj_injective_of_center center_PU

theorem z0_mem_T0 : z0 ∈ T0 := ⟨RR ^ 4, pow_mem (Subgroup.subset_closure (by simp)) 4, rfl⟩

theorem z0_ne_one : z0 ≠ 1 := by
  intro h
  rw [z0, ← map_one proj, proj_eq_iff] at h
  obtain ⟨c, -, hc⟩ := h
  rw [suMat_RR4, map_one] at hc
  have h1 := congrFun (congrFun hc 0) 0
  have h2 := congrFun (congrFun hc 2) 2
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] at h1 h2
  norm_num at h1 h2
  rw [← h2] at h1
  exact absurd h1 (by decide)

theorem z0_sq : z0 ^ 2 = 1 := by
  rw [z0, ← map_pow, ← pow_mul, show 4 * 2 = 8 by norm_num, RR_pow, map_one]

theorem z0_comm_T0 {t : PU} (ht : t ∈ T0) : t * z0 = z0 * t := by
  obtain ⟨g, hg, rfl⟩ := ht
  obtain ⟨i, -, e, -, rfl⟩ := mem_tT0 hg
  rw [z0, ← map_mul, ← map_mul]
  have hS : SS * RR ^ 4 = RR ^ 4 * SS := by
    rw [SS_mul_RR_pow, RR_pow_mod (3 * 4)]
  have hSe : SS ^ e * RR ^ 4 = RR ^ 4 * SS ^ e := ((Commute.pow_left hS e)).eq
  have hcomm : RR ^ i * SS ^ e * RR ^ 4 = RR ^ 4 * (RR ^ i * SS ^ e) := by
    calc RR ^ i * SS ^ e * RR ^ 4 = RR ^ i * (SS ^ e * RR ^ 4) := by group
      _ = RR ^ i * (RR ^ 4 * SS ^ e) := by rw [hSe]
      _ = RR ^ 4 * (RR ^ i * SS ^ e) := by
        rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, add_comm]
  rw [hcomm]

theorem isPGroup_T0' (h : Nat.card T0 = 16) : IsPGroup 2 T0 :=
  IsPGroup.of_card (n := 4) (by rw [h]; norm_num)

theorem not_two_dvd_index_T0' (h : Nat.card T0 = 16) : ¬ 2 ∣ T0.index := by
  have h1 := Subgroup.card_mul_index T0
  rw [h, card_PU] at h1
  have : T0.index = 7875 := by omega
  rw [this]
  decide

theorem z0_mem_of_normal
    {N : Subgroup PU} (hNT : N ≤ T0) (hTN : T0 ≤ Subgroup.normalizer (N : Set PU))
    (hN : N ≠ ⊥) : z0 ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥T0 :=
    (isPGroup_T0' Certificates.certificate7159.1).isNilpotent
  set N' := N.subgroupOf T0 with hN'
  have : N'.Normal := ⟨fun n hn g => by
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hTN g.2) n).mp hn⟩
  have hN'1 : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro n hn
    have : (⟨n, hNT hn⟩ : ↥T0) ∈ N' := Subgroup.mem_subgroupOf.mpr hn
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN'1)
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨hwN, hwc⟩ := Subgroup.mem_inf.mp hw
  have hcx : ∀ y ∈ T0, (w : PU) * y = y * w := fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨y, hy⟩)).symm
  rcases Certificates.certificate7159.2.1 _ w.2 hcx with h | h
  · exact absurd (Subtype.ext h) hw1'
  · rw [← h]
    exact Subgroup.mem_subgroupOf.mp hwN


theorem map_centralizer_singleton {G : Type*} [Group G] (ψ : MulAut G) (z : G) :
    (Subgroup.centralizer {z}).map ψ.toMonoidHom = Subgroup.centralizer {ψ z} := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hc']
  · intro c hc
    have hc' : c * ψ z = ψ z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    refine ⟨ψ.symm c, Subgroup.mem_centralizer_singleton_iff.mpr ?_,
      by simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]⟩
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hc']

theorem conj_map {G : Type*} [Group G] (ψ : MulAut G) (y : G) :
    MulAut.conj (ψ y) = ψ * MulAut.conj y * ψ⁻¹ := by
  ext w
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mc_sylow {T : Subgroup PU} (hT2 : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) :
    ∃ z : PU, z ≠ 1 ∧ z ^ 2 = 1 ∧ (∀ t ∈ T, t * z = z * t) ∧
      (∀ N : Subgroup PU, N ≤ T → T ≤ Subgroup.normalizer (N : Set PU) → N ≠ ⊥ → z ∈ N) ∧
      Nat.card ↥⁅Subgroup.centralizer {z}, Subgroup.centralizer {z}⁆ ≤ 120 ∧
      ∀ x ∈ (psuConj f25Data).range, Odd (orderOf x) →
        (∀ t ∈ T, ∃ a : ℤ, ∃ t' ∈ T, MulAut.conj t * x = x ^ a * MulAut.conj t') → x z = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := Certificates.certificate7159.1
  obtain ⟨c, hcT⟩ := MulAction.exists_smul_eq PU ((isPGroup_T0' hcard).toSylow
    (not_two_dvd_index_T0' hcard)) (hT2.toSylow hTi)
  set ψ : MulAut PU := MulAut.conj c with hψ
  have hT : T = T0.map ψ.toMonoidHom := by
    have h1 := congrArg (fun P : Sylow 2 PU => (P : Subgroup PU)) hcT
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h1
    rw [← h1, Subgroup.pointwise_smul_def]
    rfl
  have hmemT : ∀ t, t ∈ T ↔ ψ.symm t ∈ T0 := by
    intro t
    rw [hT]
    constructor
    · rintro ⟨t₀, ht₀, rfl⟩
      simpa using ht₀
    · intro h
      exact ⟨_, h, by simp⟩
  refine ⟨ψ z0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Ne, map_eq_one_iff _ ψ.injective]
    exact z0_ne_one
  · rw [← map_pow, z0_sq, map_one]
  · intro t ht
    have h1 := z0_comm_T0 ((hmemT t).mp ht)
    have h2 := congrArg ψ h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  · intro N hNT hTN hN
    have hmem : ∀ y, y ∈ N.comap ψ.toMonoidHom ↔ ψ y ∈ N := fun y => Iff.rfl
    have h1 : N.comap ψ.toMonoidHom ≤ T0 := by
      intro y hy
      have := (hmemT _).mp (hNT ((hmem y).mp hy))
      simpa using this
    have h2 : T0 ≤ Subgroup.normalizer ((N.comap ψ.toMonoidHom : Subgroup PU) : Set PU) := by
      intro t₀ ht₀
      have hψt : ψ t₀ ∈ T := (hmemT _).mpr (by simpa using ht₀)
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hmem, hmem, map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.mp (hTN hψt) (ψ y)
    have h3 : N.comap ψ.toMonoidHom ≠ ⊥ := by
      intro h
      apply hN
      rw [eq_bot_iff]
      intro n hn
      have : ψ.symm n ∈ N.comap ψ.toMonoidHom := by
        rw [hmem, MulEquiv.apply_symm_apply]
        exact hn
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot, ← ψ.apply_symm_apply n, this, map_one]
    exact (hmem z0).mp (z0_mem_of_normal h1 h2 h3)
  · have h1 : ⁅Subgroup.centralizer {ψ z0}, Subgroup.centralizer {ψ z0}⁆ =
        (⁅Subgroup.centralizer {z0}, Subgroup.centralizer {z0}⁆).map ψ.toMonoidHom := by
      rw [Subgroup.map_commutator, map_centralizer_singleton]
    rw [h1, Subgroup.card_map_of_injective ψ.injective]
    exact card_commutator_centralizer_z0
  · intro x hx hodd hperm
    set x₀ := ψ⁻¹ * x * ψ with hx₀
    have hx₀J : x₀ ∈ (psuConj f25Data).range :=
      mul_mem (mul_mem (inv_mem (conj_mem_range c)) hx) (conj_mem_range c)
    have hx₀o : orderOf x₀ = orderOf x := by
      have : x₀ = MulAut.conj ψ⁻¹ x := by
        rw [hx₀, MulAut.conj_apply, inv_inv]
      rw [this, MulEquiv.orderOf_eq]
    have hx₀p : ∀ t ∈ T0, ∃ a : ℤ, ∃ t' ∈ T0, MulAut.conj t * x₀ = x₀ ^ a * MulAut.conj t' := by
      intro t₀ ht₀
      have hψt : ψ t₀ ∈ T := (hmemT _).mpr (by simpa using ht₀)
      obtain ⟨a, t', ht', hta⟩ := hperm _ hψt
      refine ⟨a, ψ.symm t', (hmemT t').mp ht', ?_⟩
      have e1 : MulAut.conj t₀ = ψ⁻¹ * MulAut.conj (ψ t₀) * ψ := by
        rw [conj_map]
        group
      have e2 : MulAut.conj (ψ.symm t') = ψ⁻¹ * MulAut.conj t' * ψ := by
        have := conj_map ψ (ψ.symm t')
        rw [MulEquiv.apply_symm_apply] at this
        rw [this]
        group
      have e3 : x₀ ^ a = ψ⁻¹ * x ^ a * ψ := by
        rw [hx₀]
        have := conj_zpow (a := ψ⁻¹) (b := x) (i := a)
        rwa [inv_inv] at this
      rw [e1, e2, e3, hx₀]
      calc ψ⁻¹ * MulAut.conj (ψ t₀) * ψ * (ψ⁻¹ * x * ψ)
          = ψ⁻¹ * (MulAut.conj (ψ t₀) * x) * ψ := by group
        _ = ψ⁻¹ * (x ^ a * MulAut.conj t') * ψ := by rw [hta]
        _ = ψ⁻¹ * x ^ a * ψ * (ψ⁻¹ * MulAut.conj t' * ψ) := by group
    have h1 := Certificates.certificate7159.2.2 _ hx₀J (hx₀o ▸ hodd) hx₀p
    rw [hx₀, MulAut.mul_apply, MulAut.mul_apply] at h1
    have h2 := congrArg ψ h1
    rwa [MulAut.apply_inv_self] at h2

end U35

section Case

variable {A : Type} [Group A] {Q R S B D : Subgroup A}

theorem card_le_sixteen (X : Subgroup U35.PU) (hX : IsPGroup 2 X) : Nat.card X ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  have h1 : 2 ^ k ∣ 16 * 7875 := by
    rw [← hk, show 16 * 7875 = 126000 by norm_num, ← U35.card_PU]
    exact Subgroup.card_subgroup_dvd_card X
  have h2 : 2 ^ k ∣ 16 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 7875)).dvd_of_dvd_mul_right h1
  rw [hk]
  exact Nat.le_of_dvd (by norm_num) h2

theorem center_l24 : Subgroup.center L24 = ⊥ := by
  have : IsSimpleGroup L24 := CFSG.Walter.JT.isSimpleGroup_of_psl24 (MulEquiv.refl L24)
  have hcard : Nat.card L24 = 60 := CFSG.Walter.JT.card_of_psl24 (MulEquiv.refl L24)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L24) with h | h
  · exact h
  · exfalso
    have hab : ∀ a b : L24, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := L24) 2 (by rw [hcard]; norm_num)
    have : (Subgroup.zpowers y).Normal :=
      ⟨fun n hn g => by rw [hab g n, mul_inv_cancel_right]; exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers y) with h1 | h1
    · rw [Subgroup.zpowers_eq_bot] at h1
      rw [h1, orderOf_one] at hy
      norm_num at hy
    · have h2 := congrArg (fun H : Subgroup L24 => Nat.card H) h1
      simp only [Nat.card_zpowers, hy, Subgroup.card_top, hcard] at h2
      norm_num at h2

variable {P : Type*} [Group P] (e : ↥Q ⧸ Subgroup.center ↥Q ≃* P)

theorem pImg_R_data (h : Star513 Q R S B D) :
    ⁅pImg Q e R, pImg Q e R⁆ = pImg Q e R ∧
      (∃ φ : ↥(pImg Q e R) →* L24, Function.Surjective φ ∧ IsPGroup 2 φ.ker) ∧
      ∀ (r : A) (hr : r ∈ R), toP Q e ⟨r, h.R_le hr⟩ = 1 → ∃ n : ℕ, r ^ (2 ^ n) = 1 := by
  obtain ⟨eX⟩ := exists_l24_of_lieModel h.R_type
  set fR : ↥R →* P := (toP Q e).comp (Subgroup.inclusion h.R_le) with hfR
  have hrange : fR.range = pImg Q e R := by
    ext y
    rw [MonoidHom.mem_range, mem_pImg]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, h.R_le r.2, r.2, rfl⟩
    · rintro ⟨r, hrQ, hrR, rfl⟩
      exact ⟨⟨r, hrR⟩, rfl⟩
  set φR : ↥R →* L24 := eX.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥R)) with hφR
  have hφRs : Function.Surjective φR :=
    eX.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφRk : ∀ r : ↥R, φR r = 1 → ∃ n : ℕ, r ^ (2 ^ n) = 1 := by
    intro r hr
    have h1 : r ∈ CFSG.pCore 2 ↥R := by
      rw [← QuotientGroup.eq_one_iff]
      exact eX.injective (by rw [map_one]; exact hr)
    exact CFSG.pCore_isPGroup ⟨r, h1⟩ |>.imp fun n hn => congrArg Subtype.val hn
  have hker : ∀ r : ↥R, fR r = 1 → φR r = 1 := by
    intro r hr
    have hz : (Subgroup.inclusion h.R_le r) ∈ Subgroup.center ↥Q := by
      rw [← ker_toP Q e, MonoidHom.mem_ker]
      exact hr
    have hc : ∀ s : ↥R, r * s = s * r := fun s => by
      have := Subgroup.mem_center_iff.mp hz (Subgroup.inclusion h.R_le s)
      have h2 : ((Subgroup.inclusion h.R_le r : ↥Q) : A) * (Subgroup.inclusion h.R_le s : ↥Q) =
          (Subgroup.inclusion h.R_le s : ↥Q) * (Subgroup.inclusion h.R_le r : ↥Q) :=
        congrArg Subtype.val this.symm
      exact Subtype.ext h2
    have hcen : φR r ∈ Subgroup.center L24 := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨s, rfl⟩ := hφRs w
      rw [← map_mul, ← map_mul, hc s]
    rw [center_l24, Subgroup.mem_bot] at hcen
    exact hcen
  refine ⟨?_, ?_, ?_⟩
  ·
    have htop : ⁅(⊤ : Subgroup ↥R), (⊤ : Subgroup ↥R)⁆ = (⊤ : Subgroup ↥R) := by
      apply Subgroup.map_injective R.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        h.R_perfect]
    rw [← hrange, MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]
  ·
    set f₁ : ↥R →* ↥fR.range := fR.rangeRestrict with hf₁def
    have hf₁s : Function.Surjective f₁ := fR.rangeRestrict_surjective
    have hle : f₁.ker ≤ φR.ker := by
      intro r hr
      apply hker
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hr)
      exact this
    set eQ := QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁s with heQ
    set φ₁ : ↥fR.range →* L24 := (QuotientGroup.lift f₁.ker φR hle).comp eQ.symm.toMonoidHom
    have hφ₁ : ∀ r : ↥R, φ₁ (f₁ r) = φR r := by
      intro r
      have e1 : eQ.symm (f₁ r) = (QuotientGroup.mk r : ↥R ⧸ f₁.ker) := eQ.symm_apply_eq.mpr rfl
      simp only [φ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e1, QuotientGroup.lift_mk]
    let eR : ↥(pImg Q e R) ≃* ↥fR.range := MulEquiv.subgroupCongr hrange.symm
    refine ⟨φ₁.comp eR.toMonoidHom, ?_, ?_⟩
    · intro w
      obtain ⟨r, rfl⟩ := hφRs w
      refine ⟨eR.symm (f₁ r), ?_⟩
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hφ₁]
    · intro y
      obtain ⟨r, hr⟩ := hf₁s (eR y)
      have hy : φR r = 1 := by
        rw [← hφ₁, hr]
        exact MonoidHom.mem_ker.mp y.2
      obtain ⟨n, hn⟩ := hφRk r hy
      have h1 : eR (y : ↥(pImg Q e R)) ^ (2 ^ n) = 1 := by rw [← hr, ← map_pow, hn, map_one]
      have h2 := congrArg eR.symm h1
      rw [map_pow, MulEquiv.symm_apply_apply, map_one] at h2
      refine ⟨n, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h2
  · intro r hr h1
    obtain ⟨n, hn⟩ := hφRk ⟨r, hr⟩ (hker ⟨r, hr⟩ h1)
    exact ⟨n, congrArg Subtype.val hn⟩

theorem pImg_SR_data [Finite P] (h : Star513 Q R S B D) :
    pImg Q e (S ⊓ R) ≤ pImg Q e R ∧ pImg Q e (S ⊓ R) ≤ pImg Q e (S ⊓ Q) ∧
      pImg Q e (S ⊓ Q) ≤ Subgroup.normalizer (pImg Q e (S ⊓ R) : Set P) ∧
      IsPGroup 2 (pImg Q e (S ⊓ R)) ∧
      ¬ 2 ∣ ((pImg Q e (S ⊓ R)).subgroupOf (pImg Q e R)).index := by
  obtain ⟨-, hSR2, hSRi⟩ := h.sylow_R
  refine ⟨pImg_mono Q e inf_le_right, pImg_mono Q e (inf_le_inf_left _ h.R_le), ?_,
    isPGroup_pImg Q e (inf_le_right.trans h.R_le) hSR2, ?_⟩
  · intro t ht
    obtain ⟨s, hsQ, hs, rfl⟩ := (mem_pImg Q e).1 ht
    apply mem_normalizer_of_conj_mem
    intro y hy
    obtain ⟨r, hrQ, hr, rfl⟩ := (mem_pImg Q e).1 hy
    obtain ⟨hs1, -⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨hr1, hr2⟩ := Subgroup.mem_inf.mp hr
    have hsr : s * r * s⁻¹ ∈ S ⊓ R :=
      Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hs1 hr1) (inv_mem hs1),
        (Subgroup.mem_normalizer_iff.mp (h.S_le_R hs1) r).mp hr2⟩
    have : toP Q e ⟨s, hsQ⟩ * toP Q e ⟨r, hrQ⟩ * (toP Q e ⟨s, hsQ⟩)⁻¹ =
        toP Q e ⟨s * r * s⁻¹, h.R_le (Subgroup.mem_inf.mp hsr).2⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact toP_mem_pImg Q e _ hsr
  · set Y := (pImg Q e (S ⊓ R)).subgroupOf (pImg Q e R)
    let f : ↥R →* ↥(pImg Q e R) :=
      ((toP Q e).comp (Subgroup.inclusion h.R_le)).codRestrict (pImg Q e R)
        fun r => toP_mem_pImg Q e (h.R_le r.2) r.2
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨r, hrQ, hrR, rfl⟩ := (mem_pImg Q e).1 hy
      exact ⟨⟨r, hrR⟩, rfl⟩
    have hXY : ((S ⊓ R).subgroupOf R).map f ≤ Y := by
      rintro _ ⟨s, hs, rfl⟩
      exact toP_mem_pImg Q e _ hs
    exact fun h2 =>
      hSRi ((h2.trans (Subgroup.index_dvd_of_le hXY)).trans (Subgroup.index_map_dvd _ hf))


theorem exists_b_u35 [Finite A] (h : Star513 Q R S B D)
    (hR2 : ∀ (r : A) (hr : r ∈ R), toP Q e ⟨r, h.R_le hr⟩ = 1 → ∃ n : ℕ, r ^ (2 ^ n) = 1) :
    ∃ (b : A) (hb : b ∈ B), orderOf (toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩) = 3 ∧
      ∀ t ∈ pImg Q e (S ⊓ Q), ∃ a : ℤ, ∃ t' ∈ pImg Q e (S ⊓ Q),
        t * toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩ =
          toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩ ^ a * t' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 := card_B h
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 (by rw [hB3])
  have hbB := b.2
  have hbR := (h.hall_B.1 hbB).1
  have hbQ := h.R_le hbR
  have hbo : orderOf (b : A) = 3 := by rw [Subgroup.orderOf_coe, hb]
  refine ⟨b, hbB, ?_, ?_⟩
  · have h1 : orderOf (toP Q e ⟨b, hbQ⟩) ∣ 3 := by
      rw [← hbo, ← Subgroup.orderOf_mk (b : A) hbQ]
      exact orderOf_map_dvd _ _
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
    · exfalso
      obtain ⟨n, hn⟩ := hR2 b hbR (orderOf_eq_one_iff.mp h1)
      have h2 : orderOf (b : A) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
      rw [hbo] at h2
      have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2)
      omega
    · exact h1
  ·
    have hBz : B = Subgroup.zpowers (b : A) := by
      symm
      apply Subgroup.eq_of_le_of_card_ge
      · rw [Subgroup.zpowers_le]
        exact hbB
      · rw [hB3, Nat.card_zpowers, hbo]
    intro t ht
    obtain ⟨s, hsQ, hs, rfl⟩ := (mem_pImg Q e).1 ht
    obtain ⟨hsS, -⟩ := Subgroup.mem_inf.mp hs
    have hsb : s * b ∈ (S : Set A) * (B : Set A) := Set.mul_mem_mul hsS hbB
    rw [← h.perm_B] at hsb
    obtain ⟨b', hb'B, s', hs'S, hsb'⟩ := hsb
    have hb'Q : b' ∈ Q := h.R_le (h.hall_B.1 hb'B).1
    have hs'Q : s' ∈ Q := by
      have : s' = b'⁻¹ * (s * b) := by rw [← hsb']; group
      rw [this]
      exact mul_mem (inv_mem hb'Q) (mul_mem hsQ hbQ)
    rw [hBz] at hb'B
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'B
    refine ⟨a, toP Q e ⟨s', hs'Q⟩, toP_mem_pImg Q e hs'Q (Subgroup.mem_inf.mpr ⟨hs'S, hs'Q⟩), ?_⟩
    have e1 : (⟨s, hsQ⟩ : ↥Q) * ⟨b, hbQ⟩ = ⟨(b : A), hbQ⟩ ^ a * ⟨s', hs'Q⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
      exact hsb'.symm
    rw [← map_mul, e1, map_mul, map_zpow]

theorem normalizer_of_u35_of_check [Finite A]
    (h : Star513 Q R S B D) (e : ↥Q ⧸ Subgroup.center ↥Q ≃* U35.PU) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut U35.PU) :=
    Finite.of_injective (fun f : MulAut U35.PU => (f : U35.PU → U35.PU))
      fun _ _ h => MulEquiv.ext (congrFun h)
  have hcj := U35.conj_injective_PU
  have hodd : ∀ α ∈ aImg Q e D, Odd (orderOf α) := fun α hα =>
    Odd.of_dvd_nat h.D_odd
      ((Subgroup.orderOf_dvd_natCard _ hα).trans (card_aImg_dvd Q e h.D_le_Q))
  have hDJ : aImg Q e D ≤ (CFSG.RankThree.PartTwo.KFacts.psuConj
      CFSG.Quasithin.H13.KGU35.f25Data).range :=
    fun α hα => U35.mem_range_psuConj_of_odd (hodd α hα)
  obtain ⟨hT2, hTi⟩ := pImg_SQ e h
  obtain ⟨z, hz1, hz2, hzc, hzN, hY, hMC⟩ := U35.mc_sylow hT2 hTi
  have hperm := aImg_perm Q e h.S_le_Q h.D_le_Q h.perm_D h.S_two hDJ U35.conj_mem_range
    (fun α hα h2 => U35.inner_of_two hα h2) hcj
    (fun X hX hle => (hT2.toSylow hTi).is_maximal' hX hle)
  have hcyc := isCyclic_aImg Q e h.D_le_Q h.D_cyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(aImg Q e D))
  have hgperm : ∀ t ∈ pImg Q e (S ⊓ Q), ∃ a : ℤ, ∃ t' ∈ pImg Q e (S ⊓ Q),
      MulAut.conj t * (g : MulAut U35.PU) = (g : MulAut U35.PU) ^ a * MulAut.conj t' := by
    intro t ht
    obtain ⟨x', hx', t', ht', he⟩ := hperm t ht _ g.2
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x', hx'⟩)
    refine ⟨a, t', ht', ?_⟩
    rw [he]
    have := congrArg Subtype.val ha
    rw [Subgroup.coe_zpow] at this
    rw [this]
  have hgz : (g : MulAut U35.PU) z = z := hMC _ (hDJ g.2) (hodd _ g.2) hgperm
  obtain ⟨hRp, ⟨φ, hφ, hker⟩, hR2⟩ := pImg_R_data e h
  obtain ⟨hER, hET, hEn, hE2, hEi⟩ := pImg_SR_data e h
  obtain ⟨b, hb, hb3, hbperm⟩ := exists_b_u35 e h hR2
  set bb := toP Q e ⟨b, h.R_le (h.hall_B.1 hb).1⟩ with hbb
  have hbz : bb * z = z * bb := by
    have h1 := hMC (MulAut.conj bb) (U35.conj_mem_range bb)
      (by rw [orderOf_injective _ hcj, hb3]; decide) (by
        intro t ht
        obtain ⟨a, t', ht', he⟩ := hbperm t ht
        exact ⟨a, t', ht', by rw [← map_mul, he, map_mul, map_zpow]⟩)
    rw [MulAut.conj_apply] at h1
    calc bb * z = bb * z * bb⁻¹ * bb := by group
      _ = z * bb := by rw [h1]
  have hbR : bb ∈ pImg Q e R := toP_mem_pImg Q e _ (h.hall_B.1 hb).1
  have hcore := core_u35 hz1 hz2 hzc hzN card_le_sixteen hY hRp φ hφ hker hER hET hEn hE2 hEi
    hbR hb3 hbz hgz
  have hpow : ∀ n : ℕ, ∀ y ∈ pImg Q e R, ((g : MulAut U35.PU) ^ n) y ∈ pImg Q e R := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', MulAut.mul_apply]
      exact hcore _ (ih y hy)
  have hall : ∀ x ∈ aImg Q e D, ∀ y ∈ pImg Q e R, x y ∈ pImg Q e R := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥(aImg Q e D)) ∈ Submonoid.powers g :=
      mem_powers_iff_mem_zpowers.mpr (hg _)
    obtain ⟨n, hn⟩ := hx'
    have hxn : x = (g : MulAut U35.PU) ^ n := by
      have := congrArg Subtype.val hn
      rw [Subgroup.coe_pow] at this
      exact this.symm
    rw [hxn]
    exact hpow n
  exact le_normalizer_of_pImg Q e h.R_le h.R_perfect h.D_le_Q fun d hd y hy =>
    hall _ (autOf_mem_aImg Q e _ hd) y hy


theorem nonempty_ringEquiv_f25 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 25) :
    Nonempty (K ≃+* CFSG.RankThree.PartOne.HNB.F25) := by
  have : Fintype K := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.RankThree.PartOne.HNB.F25.card, hK])⟩

theorem normalizer_of_psu35 [Finite A] (h : Star513 Q R S B D)
    (hQ : IsPSLEps3 false 5 1 ↥Q ∨ IsSLEps3 false 5 ↥Q) :
    D ≤ Subgroup.normalizer (R : Set A) := by
  rcases hQ with hQ | hQ
  ·
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨φ⟩ := nonempty_ringEquiv_f25 K (by rw [hK]; norm_num)
    let E : ↥Q ≃* U35.PU := e₀.trans
      ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
        (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ)
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 (5 ^ 1))
        (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans
        (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv CFSG.Quasithin.H13.KGU35.f25Data
          (n := 3) (by norm_num)).symm)
    have hZ : Subgroup.center ↥Q = ⊥ := by
      have h1 := Subgroup.map_center_eq E
      rw [U35.center_PU] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ E.injective).mp h1
    exact normalizer_of_u35_of_check h
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans E))
  ·
    obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ := hQ
    obtain ⟨φ⟩ := nonempty_ringEquiv_f25 K (by rw [hK]; norm_num)
    let E : ↥Q ≃* ↥U35.SU := e₀.trans
      (((CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin 3) φ).subgroupMap
        (CFSG.Assembly.LowTwoRank.StatedSU 3 5 K)).trans
        (MulEquiv.subgroupCongr (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU φ 3 5)))
    exact normalizer_of_u35_of_check h
      ((QuotientGroup.congr _ _ E (Subgroup.map_center_eq E)).trans
        (CFSG.RankThree.PartTwo.KFacts.suCenterEquiv CFSG.Quasithin.H13.KGU35.f25Data
          (by norm_num)))

end Case

end CFSG.Quasithin.H13.NQCat.T513
