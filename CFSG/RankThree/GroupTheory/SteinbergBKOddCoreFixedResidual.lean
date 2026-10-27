module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.GroupTheory.SteinbergBMScalarActionQuasisimpleQuotient
import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBK

open Subgroup CFSG
open scoped commutatorElement

theorem odd_core_fixed_residual_retains_two_subgroups_and_scalar_center {p : ℕ} (hp : p.Prime)
    {L U : Type*} [Group L] [Finite L] [Group U] [Finite U] [MulDistribMulAction U L]
    (hLperf : Group.IsPerfect L) (O : Subgroup L) [O.Normal] (hOsolv : Group.IsSolvable O)
    (hOodd : Odd (Nat.card O)) (hOp : ¬ p ∣ Nat.card O) (hLO : IsQuasisimple (L ⧸ O))
    (hU : IsPGroup p U) (hUO : ∀ u : U, ∀ x ∈ O, u • x ∈ O)
    (hUtriv : ∀ u : U, ∀ x : L, x⁻¹ * (u • x) ∈ O) :
    O ⊔ inSubgroup perfectResidual (fixedPointSubgroup U L) = ⊤ ∧
      fixedPointSubgroup U L = (fixedPointSubgroup U L ⊓ O) ⊔
        inSubgroup perfectResidual (fixedPointSubgroup U L) ∧
      (∀ R : Subgroup L, R ≤ fixedPointSubgroup U L → IsPGroup 2 R →
        R ≤ inSubgroup perfectResidual (fixedPointSubgroup U L)) ∧
      (IsQuasisimple (inSubgroup perfectResidual (fixedPointSubgroup U L)) → ∀ {q : ℕ},
        q.Prime → ∀ D : Subgroup L, D.Normal → IsPGroup q D → ⁅(⊤ : Subgroup L), D⁆ ≠ ⊥ →
        ∀ z (hz : z ∈ inSubgroup perfectResidual (fixedPointSubgroup U L)),
          (∃ k : ℕ, ∀ d ∈ D, (z * d * z⁻¹)⁻¹ * d ^ k ∈ inSubgroup frattini D) →
          (⟨z, hz⟩ : inSubgroup perfectResidual (fixedPointSubgroup U L)) ∈
            center (inSubgroup perfectResidual (fixedPointSubgroup U L))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set C := fixedPointSubgroup U L with hC
  set P := inSubgroup perfectResidual C with hP
  have hPC : P ≤ C := map_subtype_le _
  have hOinv : IsInvariant U L O :=
    ⟨fun u x => ⟨hUO u x, fun h => by simpa using hUO u⁻¹ _ h⟩⟩
  have hcop : Nat.Coprime (Nat.card U) (Nat.card O) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hOp)
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting O hOinv hOsolv hcop
  have hCO : C.map (QuotientGroup.mk' O) = ⊤ := by
    let : MulDistribMulAction U (L ⧸ O) :=
      CFSG.quotientMulDistribMulAction (A := U) (G := L) O hOinv
    let : MulAction.QuotientAction U O := CFSG.quotientAction_of_isInvariant (A := U) O hOinv
    have htop : fixedPointSubgroup U (L ⧸ O) = ⊤ := by
      rw [eq_top_iff]
      intro q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      intro u
      change u • ((x : L) : L ⧸ O) = (x : L ⧸ O)
      rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
      have h := inv_mem (hUtriv u x)
      rwa [mul_inv_rev, inv_inv] at h
    rw [← htop]
    exact hlift.symm
  let f : C →* L ⧸ O := (QuotientGroup.mk' O).comp C.subtype
  have hf : Function.Surjective f := by
    intro q
    have hq : q ∈ C.map (QuotientGroup.mk' O) := hCO ▸ mem_top q
    obtain ⟨c, hc, rfl⟩ := hq
    exact ⟨⟨c, hc⟩, rfl⟩
  have hLOperf : Group.IsPerfect (L ⧸ O) := hLO.1
  have hDL : perfectResidual (L ⧸ O) = ⊤ :=
    eq_top_iff.mpr (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual ⊤
      (Group.IsPerfect.top_iff.mpr hLOperf))
  have hPO : P.map (QuotientGroup.mk' O) = ⊤ := by
    rw [hP, inSubgroup, map_map]
    exact (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq f hf).trans hDL
  have hOP : O ⊔ P = ⊤ := by
    have h := comap_map_eq (QuotientGroup.mk' O) P
    rw [hPO, comap_top, QuotientGroup.ker_mk'] at h
    rw [sup_comm]
    exact h.symm
  have hCdec : ∀ c ∈ C, ∃ o ∈ C ⊓ O, ∃ x ∈ P, c = o * x := by
    intro c hc
    have hc' : c ∈ ((O ⊔ P : Subgroup L) : Set L) := by rw [hOP]; exact mem_top c
    rw [normal_mul] at hc'
    obtain ⟨o, ho, x, hx, rfl⟩ := hc'
    refine ⟨o, Subgroup.mem_inf.mpr ⟨?_, ho⟩, x, hx, rfl⟩
    have : o = (o * x) * x⁻¹ := by group
    rw [this]
    exact mul_mem hc (inv_mem (hPC hx))
  have hCeq : C = (C ⊓ O) ⊔ P := by
    refine le_antisymm (fun c hc => ?_) (sup_le inf_le_left hPC)
    obtain ⟨o, ho, x, hx, rfl⟩ := hCdec c hc
    exact mul_mem (mem_sup_left ho) (mem_sup_right hx)
  refine ⟨hOP, hCeq, fun R hRC hR2 => ?_, ?_⟩
  swap
  · intro hPq q hq D hDn hDq hLD z hz hk
    obtain ⟨k, hk⟩ := hk
    have hconjD : ∀ g d : L, d ∈ D → g * d * g⁻¹ ∈ D := fun g d hd => hDn.conj_mem d hd g
    have hmemΦ : ∀ (x y : L) (hx : x ∈ D) (hy : y ∈ D), x⁻¹ * y ∈ inSubgroup frattini D ↔
        (QuotientGroup.mk (⟨x, hx⟩ : D) : D ⧸ frattini D) = QuotientGroup.mk ⟨y, hy⟩ := by
      intro x y hx hy
      rw [QuotientGroup.eq]
      constructor
      · rintro ⟨w, hw, hwe⟩
        have hw' : (⟨x, hx⟩ : D)⁻¹ * ⟨y, hy⟩ = w := Subtype.ext (by simp [← hwe])
        rw [hw']
        exact hw
      · intro h
        exact ⟨_, h, rfl⟩
    have hk' : ∀ (d : L) (hd : d ∈ D),
        (QuotientGroup.mk (⟨z * d * z⁻¹, hconjD z d hd⟩ : D) : D ⧸ frattini D) =
          (QuotientGroup.mk (⟨d, hd⟩ : D) : D ⧸ frattini D) ^ k := by
      intro d hd
      rw [← QuotientGroup.mk_pow]
      exact (hmemΦ _ _ _ (pow_mem hd k)).mp (hk d hd)
    have hpowmk : ∀ (n : ℕ) (d : L) (hd : d ∈ D),
        (QuotientGroup.mk (⟨z ^ n * d * (z ^ n)⁻¹, hconjD _ d hd⟩ : D) : D ⧸ frattini D) =
          (QuotientGroup.mk (⟨d, hd⟩ : D) : D ⧸ frattini D) ^ (k ^ n) := by
      intro n
      induction n with
      | zero =>
        intro d hd
        simp only [pow_zero, one_mul, inv_one, mul_one, pow_one]
      | succ n ih =>
        intro d hd
        have he : (⟨z ^ (n + 1) * d * (z ^ (n + 1))⁻¹, hconjD _ d hd⟩ : D) =
            ⟨z * (z ^ n * d * (z ^ n)⁻¹) * z⁻¹, hconjD z _ (hconjD _ d hd)⟩ :=
          Subtype.ext (by simp only [pow_succ']; group)
        rw [he, hk' _ (hconjD _ d hd), ih d hd, ← pow_mul, pow_succ]
    have hscalar : ∀ b ∈ zpowers z, ∃ k' : ℕ, ∀ d ∈ D,
        (b * d * b⁻¹)⁻¹ * d ^ k' ∈ inSubgroup frattini D := by
      intro b hb
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, z ^ n = b :=
        Submonoid.mem_powers_iff _ _ |>.mp
          ((isOfFinOrder_of_finite z).mem_powers_iff_mem_zpowers.mpr hb)
      refine ⟨k ^ n, fun d hd => ?_⟩
      refine (hmemΦ _ _ (hconjD _ d hd) (pow_mem hd _)).mpr ?_
      rw [hpowmk n d hd, ← QuotientGroup.mk_pow]
      rfl
    have hLtop : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := hLperf.commutator_eq_top
    have : (O.subgroupOf (⊤ : Subgroup L)).Normal := (inferInstance : O.Normal).subgroupOf ⊤
    have hQtop : IsQuasisimple ((⊤ : Subgroup L) ⧸ O.subgroupOf ⊤) := by
      have hmap : (O.subgroupOf (⊤ : Subgroup L)).map
          (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).toMonoidHom = O := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, mem_top x⟩, hx, rfl⟩
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (QuotientGroup.congr _ _ Subgroup.topEquiv hmap).symm hLO
    have hDtop : (⊤ : Subgroup L) ≤ normalizer (D : Set L) :=
      (normalizer_eq_top_iff.mpr hDn).ge
    have hBL : zpowers z ≤ normalizer ((⊤ : Subgroup L) : Set L) :=
      le_top.trans (normalizer_eq_top_iff.mpr inferInstance).ge
    have hBD : zpowers z ≤ normalizer (D : Set L) := le_top.trans hDtop
    have hcomm := SteinbergBM.scalar_critical_action_centralizes_quasisimple_solvable_quotient hq
      hLtop hOsolv hQtop hDtop hDq hLD hBL hBD hscalar
    have hPperf : Group.IsPerfect P := hPq.1
    have hON : (O.subgroupOf P).Normal := (inferInstance : O.Normal).subgroupOf P
    have hOZ : O.subgroupOf P ≤ center P := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hPq hON with h | h
      · exfalso
        have hPO : P ≤ O := by
          intro y hy
          have : (⟨y, hy⟩ : P) ∈ O.subgroupOf P := h ▸ mem_top _
          exact this
        have : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hPO) (Subgroup.inclusion_injective hPO)
        have : Nontrivial P := CFSG.LocalCores.isQuasisimple_nontrivial hPq
        exact Group.IsPerfect.not_isSolvable P inferInstance
      · exact h
    have hα := CFSG.ComponentClassification.CentralCover.eq_one_of_forall_inv_mul_mem_center
      (MulAut.conj (⟨z, hz⟩ : P)) fun g => by
        apply hOZ
        rw [mem_subgroupOf]
        have hg := commutator_mem_commutator (mem_top ((g : L)⁻¹)) (mem_zpowers z)
        have := hcomm hg
        simpa [commutatorElement_def, mul_assoc] using this
    rw [mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut P => φ g) hα
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * ⟨z, hz⟩ = (⟨z, hz⟩ * g * (⟨z, hz⟩ : P)⁻¹) * ⟨z, hz⟩ := by rw [h1]
      _ = ⟨z, hz⟩ * g := by group
  intro r hr
  have hrC : r ∈ C := hRC hr
  set P' := perfectResidual C with hP'
  obtain ⟨o, ho, x, hx, hrox⟩ := hCdec r hrC
  have hoC : o ∈ C := (mem_inf.mp ho).1
  have hxC : x ∈ C := hPC hx
  have hmk : (QuotientGroup.mk (⟨r, hrC⟩ : C) : C ⧸ P') = QuotientGroup.mk (⟨o, hoC⟩ : C) := by
    refine (QuotientGroup.eq.mpr ?_).symm
    have he : (⟨o, hoC⟩ : C)⁻¹ * ⟨r, hrC⟩ = ⟨x, hxC⟩ := Subtype.ext (by simp [hrox])
    rw [he]
    obtain ⟨y, hy, hyx⟩ := hx
    have hxy : (⟨x, hxC⟩ : C) = y := Subtype.ext hyx.symm
    rw [hxy]
    exact hy
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hrk : r ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf (QuotientGroup.mk (⟨r, hrC⟩ : C) : C ⧸ P') ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, show (⟨r, hrC⟩ : C) ^ 2 ^ k = 1 from Subtype.ext hrk,
      QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk (⟨r, hrC⟩ : C) : C ⧸ P') ∣ Nat.card O := by
    rw [hmk]
    refine (orderOf_map_dvd (QuotientGroup.mk' P') _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard O (mem_inf.mp ho).2
  have hcop2 : Nat.Coprime (2 ^ k) (Nat.card O) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hOodd)
  have h3 : orderOf (QuotientGroup.mk (⟨r, hrC⟩ : C) : C ⧸ P') = 1 :=
    Nat.dvd_one.mp (by rw [← hcop2.gcd_eq_one]; exact Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact ⟨⟨r, hrC⟩, h3, rfl⟩

end CFSG.RankThree.GroupTheory.SteinbergBK
