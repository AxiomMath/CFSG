module

public import CFSG.OddTranspositions.FourEightBase
public import CFSG.OddTranspositions.WidthSylowSetup

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.OddTranspositions.QZ
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

theorem sylow_inter_D_of_config_ncard_le_three (hQ : Config D u w v z a K₁ S') :
    ((S' : Set G) ∩ D).ncard ≤ 3 := by
  classical
  obtain ⟨hz2, -, -, -, -, hzD⟩ := hQ.z_facts
  let A : Set K₁ := {x | ∃ d ∈ (S' : Set G) ∩ D, (x : G) = z * d}
  have hzd_mem : ∀ d ∈ (S' : Set G) ∩ D, z * d ∈ K₁ := by
    intro d hd
    exact hQ.delta_sub d (mem_Delta_iff.mpr
      ⟨hd.2, Subgroup.mem_centralizer_singleton_iff.mp (hQ.z_central.2 hd.1)⟩)
  have hzd2 : ∀ d ∈ (S' : Set G) ∩ D, (z * d) * (z * d) = 1 := by
    intro d hd
    have hdz : Commute d z :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQ.z_central.2 hd.1)
    calc (z * d) * (z * d) = z * (d * z) * d := by group
      _ = z * (z * d) * d := by rw [hdz.eq]
      _ = (z * z) * (d * d) := by group
      _ = 1 := by rw [hz2, hQ.setup.oddT.mul_self_eq_one hd.2, mul_one]
  have hzd_ne : ∀ d ∈ (S' : Set G) ∩ D, z * d ≠ 1 := by
    intro d hd h
    have hz_eq : z = d := by
      have h1 : z = d⁻¹ := eq_inv_of_mul_eq_one_left h
      rwa [hQ.setup.oddT.inv_eq hd.2] at h1
    exact hzD (hz_eq ▸ hd.2)
  have hA2 : ∀ x ∈ A, x * x = 1 := by
    rintro x ⟨d, hd, hxd⟩
    have hx : x = (⟨z * d, hzd_mem d hd⟩ : K₁) := Subtype.ext hxd
    rw [hx]
    exact Subtype.ext (by simpa using hzd2 d hd)
  have hAcomm : A.Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨d1, hd1, hxd1⟩ := hx
    obtain ⟨d2, hd2, hxd2⟩ := hy
    have hz1 : Commute z d1 :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hQ.z_central.2 hd1.1)).symm
    have hz2' : Commute z d2 :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hQ.z_central.2 hd2.1)).symm
    have hd12 : Commute d1 d2 :=
      hQ.setup.oddT.commute_of_isPGroup hQ.sylow.1 hd1.2 hd2.2 hd1.1 hd2.1
    have hcomm : Commute (z * d1) (z * d2) :=
      ((Commute.refl z).mul_right hz2').mul_left ((hz1.symm).mul_right hd12)
    have hx' : x = (⟨z * d1, hzd_mem d1 hd1⟩ : K₁) := Subtype.ext hxd1
    have hy' : y = (⟨z * d2, hzd_mem d2 hd2⟩ : K₁) := Subtype.ext hxd2
    rw [hx', hy']
    exact Subtype.ext (by simpa using hcomm.eq)
  let H : Subgroup K₁ := Subgroup.closure A
  haveI : IsMulCommutative H := Subgroup.isMulCommutative_closure hAcomm
  have hHsq : ∀ x : H, x ^ 2 = 1 := by
    have hsq_mem : ∀ g (hg : g ∈ H), (⟨g, hg⟩ : H) ^ 2 = 1 := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem y hy =>
        apply Subtype.ext
        simpa [pow_two] using hA2 y hy
      | one => simp
      | mul y y' hy hy' ihy ihy' =>
        change ((⟨y, hy⟩ : H) * ⟨y', hy'⟩) ^ 2 = 1
        have hc : Commute (⟨y, hy⟩ : H) ⟨y', hy'⟩ :=
          (IsMulCommutative.is_comm (M := H)).comm _ _
        rw [hc.mul_pow, ihy, ihy', mul_one]
      | inv y hy ihy =>
        change (⟨y, hy⟩ : H)⁻¹ ^ 2 = 1
        rw [inv_pow, ihy, inv_one]
    intro x
    exact hsq_mem (x : K₁) x.2
  have hexp : Monoid.exponent H ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hHsq
  have hHp2 : IsPGroup 2 H := IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa using hexp)
  have hKcard : Nat.card K₁ = 60 := by
    obtain ⟨e⟩ := hQ.K₁_A5
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hdvd : Nat.card H ∣ 60 := by
    simpa [hKcard] using Subgroup.card_subgroup_dvd_card H
  obtain ⟨k, hk⟩ := hHp2.exists_card_eq
  have hdvd' : 2 ^ k ∣ 60 := by rwa [hk] at hdvd
  have hk5 : k ≤ 5 := by
    by_contra h
    have h6 : 6 ≤ k := by omega
    have hdvd6 : 2 ^ 6 ∣ 2 ^ k := pow_dvd_pow 2 h6
    have : (64 : ℕ) ∣ 60 := by simpa using hdvd6.trans hdvd'
    norm_num at this
  have hk2 : k ≤ 2 := by
    interval_cases k
    · norm_num
    · norm_num
    · norm_num
    · exfalso; norm_num at hdvd'
    · exfalso; norm_num at hdvd'
    · exfalso; norm_num at hdvd'
  have hHcard4 : Nat.card H ≤ 4 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hAsub : A ⊆ (H : Set K₁) \ {1} := by
    rintro x hx
    refine ⟨Subgroup.subset_closure hx, ?_⟩
    rintro rfl
    obtain ⟨d, hd, hxd⟩ := hx
    exact hzd_ne d hd (by simpa using hxd.symm)
  have hAncard : A.ncard ≤ 3 := by
    have h1 : A.ncard ≤ ((H : Set K₁) \ {1}).ncard :=
      Set.ncard_le_ncard hAsub (Set.toFinite _)
    rw [Set.ncard_sdiff_singleton_of_mem (s := (H : Set K₁)) (Subgroup.one_mem H)] at h1
    have h2 : (H : Set K₁).ncard = Nat.card H := by
      simpa using (Nat.card_coe_set_eq (H : Set K₁)).symm
    rw [h2] at h1
    omega
  have hEq : ((S' : Set G) ∩ D).ncard = A.ncard := by
    refine Set.ncard_congr (fun d hd => (⟨z * d, hzd_mem d hd⟩ : K₁)) ?_ ?_ ?_
    · intro d hd
      exact ⟨d, hd, rfl⟩
    · intro d1 d2 hd1 hd2 heq
      exact mul_left_cancel (congrArg Subtype.val heq)
    · rintro x ⟨d, hd, hxd⟩
      exact ⟨d, hd, Subtype.ext hxd.symm⟩
  omega

theorem widthLe_three_of_config (hQ : Config D u w v z a K₁ S') : WidthLe D 3 := by
  classical
  refine (widthLe_iff_sylow_of_setup hQ.setup 3).mpr ?_
  intro T
  haveI : Finite (Sylow 2 G) := (default : Sylow 2 G).finite_of_finiteIndex
  let Syl : Sylow 2 G :=
    ⟨S', hQ.sylow.1, fun {P : Subgroup G} hP hle => hQ.sylow.2 P hP hle⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Syl T
  have hTset : (T : Set G) = MulAut.conj g '' (S' : Set G) := by
    rw [← hg, Sylow.coe_smul]
    change MulAut.conj g • (S' : Set G) = (MulAut.conj g : G → G) '' (S' : Set G)
    rw [← Set.image_smul]
    rfl
  have hDconj : MulAut.conj g '' D = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hQ.setup.normal g y hy
    · intro hx
      refine ⟨MulAut.conj g⁻¹ x, ?_, ?_⟩
      · simpa [MulAut.conj_apply] using hQ.setup.normal g⁻¹ x hx
      · simp [MulAut.conj_apply]
        group
  have hTinter : (T : Set G) ∩ D = MulAut.conj g '' ((S' : Set G) ∩ D) := by
    rw [hTset]
    conv_lhs => rw [← hDconj]
    rw [← Set.image_inter (MulAut.conj g).injective]
  rw [hTinter, Set.ncard_image_of_injective _ (MulAut.conj g).injective]
  exact sylow_inter_D_of_config_ncard_le_three hQ

end CFSG.OddTranspositions
