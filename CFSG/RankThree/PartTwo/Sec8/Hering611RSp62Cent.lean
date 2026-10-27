module

public import CFSG.RankThree.PartTwo.Sec8.Hering611RSp62Emb
public import CFSG.RankThree.PartTwo.Sec8.Hering611KFInvolFinal
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LieModelOrders
import TauCeti.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611R

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem exists_conj_mem_zpowers_x0 {x : H6} (hx : orderOf x = 5) :
    ∃ g : H6, g * x * g⁻¹ ∈ Subgroup.zpowers x0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h25 : ¬ 5 ^ 2 ∣ Nat.card H6 := by
    rw [card_H6]
    norm_num
  exact TauCeti.exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd h25 orderOf_x0 hx

theorem embHom_mem_centralizer_of_mem_range {y : H6} (hy : y ∈ embHom.range) :
    y ∈ Subgroup.centralizer ({s0} : Set H6) := by
  obtain ⟨h, rfl⟩ := hy
  exact embHom_mem_centralizer h

theorem cent_model {γ : H6} (hγ3 : γ ^ 3 = 1) (hγ1 : γ ≠ 1) {P : Subgroup H6}
    (hPC : P ≤ Subgroup.centralizer ({γ} : Set H6)) (hPperf : Group.IsPerfect P)
    (h5 : 5 ∣ Nat.card P) :
    ∃ Cg : Subgroup H6, Cg ≤ Subgroup.centralizer ({γ} : Set H6) ∧ P ≤ Cg ∧
      Nonempty (Cg ≃* Equiv.Perm (Fin 6)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 h5
  have hx5 : orderOf (x : H6) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers_x0 hx5
  set c : H6 ≃* H6 := MulAut.conj g with hc
  set γ' : H6 := g * γ * g⁻¹ with hγ'
  have hcomm : γ' * x0 = x0 * γ' := by
    have h1 : γ * (x : H6) = (x : H6) * γ :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hPC x.2)).symm
    have h2 : γ' * (g * x * g⁻¹) = (g * x * g⁻¹) * γ' := by
      rw [hγ']
      calc g * γ * g⁻¹ * (g * x * g⁻¹) = g * (γ * x) * g⁻¹ := by group
        _ = g * (x * γ) * g⁻¹ := by rw [h1]
        _ = (g * x * g⁻¹) * (g * γ * g⁻¹) := by group
    have h3 : x0 ∈ Subgroup.zpowers (g * x * g⁻¹) := by
      have hord : orderOf (g * x * g⁻¹) = 5 := by
        have : g * (x : H6) * g⁻¹ = MulAut.conj g (x : H6) := by simp [MulAut.conj_apply]
        rw [this, MulEquiv.orderOf_eq]
        exact hx5
      have hle : Subgroup.zpowers (g * x * g⁻¹) ≤ Subgroup.zpowers x0 :=
        (Subgroup.zpowers_le).2 hg
      have hcard : Nat.card (Subgroup.zpowers x0) ≤ Nat.card (Subgroup.zpowers (g * x * g⁻¹)) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord, orderOf_x0]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard) ▸ Subgroup.mem_zpowers x0
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h3
    rw [← hk]
    exact (Commute.zpow_right (show Commute γ' (g * x * g⁻¹) from h2) k).eq
  have hγ'3 : γ' ^ 3 = 1 := by
    have : γ' = c γ := by simp [hγ', hc, MulAut.conj_apply]
    rw [this, ← map_pow, hγ3, map_one]
  have hγ'1 : γ' ≠ 1 := by
    intro h
    apply hγ1
    have : c γ = 1 := by simpa [hγ', hc, MulAut.conj_apply] using h
    exact (map_eq_one_iff c c.injective).1 this
  have hs3 : s0 = s0 * s0 * (s0 * s0) := by
    calc s0 = s0 ^ 3 * s0 := by rw [s0_pow_three, one_mul]
      _ = s0 * s0 * (s0 * s0) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hcent : ∀ y : H6, y * γ' = γ' * y → y * s0 = s0 * y := by
    intro y hy
    rcases eq_one_or_s0_of_comm hcomm hγ'3 with h | h | h
    · exact absurd h hγ'1
    · rw [← h]; exact hy
    · have hyc : Commute y γ' := hy
      rw [h] at hyc
      rw [hs3]
      exact (hyc.mul_right hyc).eq
  have hcent' : ∀ y : H6, y * s0 = s0 * y → y * γ' = γ' * y := by
    intro y hy
    rcases eq_one_or_s0_of_comm hcomm hγ'3 with h | h | h
    · exact absurd h hγ'1
    · rw [h]; exact hy
    · have hyc : Commute y s0 := hy
      rw [h]
      exact (hyc.mul_right hyc).eq
  have hP' : Group.IsPerfect (P.map c.toMonoidHom) := by
    have := hPperf
    exact Group.IsPerfect.ofSurjective
      (f := (P.equivMapOfInjective c.toMonoidHom c.injective).toMonoidHom) (MulEquiv.surjective _)
  have hP'C : P.map c.toMonoidHom ≤ Subgroup.centralizer ({s0} : Set H6) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hcent
    have h1 : p * γ = γ * p := Subgroup.mem_centralizer_singleton_iff.mp (hPC hp)
    simp only [MulEquiv.coe_toMonoidHom, hc, MulAut.conj_apply, hγ']
    calc g * p * g⁻¹ * (g * γ * g⁻¹) = g * (p * γ) * g⁻¹ := by group
      _ = g * (γ * p) * g⁻¹ := by rw [h1]
      _ = g * γ * g⁻¹ * (g * p * g⁻¹) := by group
  have hfix := fixes_D_of_perfect hP' hP'C
  have hrange : P.map c.toMonoidHom ≤ embHom.range := fun y hy =>
    mem_range_embHom (hfix y hy).1 (hfix y hy).2
  refine ⟨embHom.range.map c.symm.toMonoidHom, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_map_equiv] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp
      (embHom_mem_centralizer_of_mem_range hy)
    have h2 := hcent' _ h1
    simp only [hc, MulEquiv.symm_symm, MulAut.conj_apply, hγ'] at h2
    calc y * γ = g⁻¹ * (g * y * g⁻¹ * (g * γ * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * γ * g⁻¹ * (g * y * g⁻¹)) * g := by rw [h2]
      _ = γ * y := by group
  · intro p hp
    rw [Subgroup.mem_map_equiv]
    exact hrange ⟨p, hp, rfl⟩
  · exact ⟨(Subgroup.equivMapOfInjective _ c.symm.toMonoidHom c.symm.injective).symm.trans
      embHomRangeEquiv⟩

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.RankThree.PartTwo.Sec8.Hering611 (KF611Sp62Cent)

theorem kF611Sp62Cent_holds : KF611Sp62Cent := by
  intro Kb _ _ hK γ hγ3 P hP hPq
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.nonempty_mulEquiv_statedSp_of_lieModel
      (Or.inl ⟨by decide, hK⟩ : CFSG.Blueprint.LieModel Kb .PSp 3 2 1)
  have hPperf : Group.IsPerfect P := isPerfect_of_mem_thetaComponentsIn hP
  have hPC : P ≤ Subgroup.centralizer ({γ} : Set Kb) := le_of_mem_thetaComponentsIn hP
  obtain ⟨ePA⟩ := hPq
  have hq : Nat.card (P ⧸ aschbacherSolvableCore 3 P) = 360 := by
    rw [Nat.card_congr ePA.toEquiv, nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h360 : 360 ∣ Nat.card P := hq ▸ Subgroup.card_quotient_dvd_card _
  have h5 : 5 ∣ Nat.card P := (by norm_num : 5 ∣ 360).trans h360
  have hKcard : Nat.card Kb = 1451520 :=
    Blueprint.LieModel.card_psp_three_two (Or.inl ⟨by decide, hK⟩)
  by_cases hγ1 : γ = 1
  · exfalso
    subst hγ1
    have hsimple : IsSimpleGroup Kb := Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hK
    have hCtop : Subgroup.centralizer ({1} : Set Kb) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_center_iff.mpr (fun g => by simp)
    rw [hCtop] at hP
    haveI : IsSimpleGroup (⊤ : Subgroup Kb) := Subgroup.topEquiv.isSimpleGroup
    have hsn : (P.subgroupOf ⊤).IsSubnormal := (mem_thetaComponentsIn_iff.mp hP).2.2.1
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup inferInstance hsn with hb | ht
    · have hPbot : P = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, Subgroup.mem_top x⟩ : (⊤ : Subgroup Kb)) ∈ P.subgroupOf ⊤ := hx
        rw [hb, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      rw [hPbot, Subgroup.card_bot] at h5
      omega
    · have hPtop : P = ⊤ := by
        rw [Subgroup.subgroupOf_eq_top] at ht
        exact eq_top_iff.mpr ht
      subst hPtop
      have hPcard : Nat.card (⊤ : Subgroup Kb) = 1451520 := by
        rw [Subgroup.card_top, hKcard]
      have hidx : (aschbacherSolvableCore 3 (⊤ : Subgroup Kb)).index = 360 := hq
      rcases (inferInstance : (aschbacherSolvableCore 3 (⊤ : Subgroup Kb)).Normal).eq_bot_or_eq_top
        with h | h
      · rw [h, Subgroup.index_bot, hPcard] at hidx
        omega
      · rw [h, Subgroup.index_top] at hidx
        omega
  ·
    have hγ3' : (e γ) ^ 3 = 1 := by rw [← map_pow, hγ3, map_one]
    have hγ1' : e γ ≠ 1 := fun h => hγ1 ((map_eq_one_iff e e.injective).1 h)
    have hPC' : P.map e.toMonoidHom ≤ Subgroup.centralizer ({e γ} : Set H6) := by
      rintro _ ⟨p, hp, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hPC hp)
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, this]
    have hPperf' : Group.IsPerfect (P.map e.toMonoidHom) := by
      have := hPperf
      exact Group.IsPerfect.ofSurjective
        (f := (P.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (MulEquiv.surjective _)
    have h5' : 5 ∣ Nat.card (P.map e.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective e.injective]
    obtain ⟨Cg', hCg'C, hPCg', ⟨ι⟩⟩ := cent_model hγ3' hγ1' hPC' hPperf' h5'
    refine ⟨Cg'.map e.symm.toMonoidHom, ?_, ?_,
      ⟨(Subgroup.equivMapOfInjective Cg' e.symm.toMonoidHom e.symm.injective).symm.trans ι⟩⟩
    · intro y hy
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm] at hy
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hCg'C hy)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul]
      exact h1
    · intro p hp
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
      exact hPCg' ⟨p, hp, rfl⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611R
