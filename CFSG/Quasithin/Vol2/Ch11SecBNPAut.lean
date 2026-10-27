module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A1bBasic
import CFSG.GroupTheory.Fitting.SelfCentralizingComponent

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

variable {X : Type} [Group X]

theorem center_eq_bot_of_nonabelian' [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) :
    Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hX
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

theorem mul_conj_mul_inv (φ : MulAut X) (g : X) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem normal_range_conj (X : Type) [Group X] : (MulAut.conj : X →* MulAut X).range.Normal :=
  ⟨by
    rintro _ ⟨g, rfl⟩ φ
    exact ⟨φ g, (mul_conj_mul_inv φ g).symm⟩⟩

theorem conj_injective (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : x * y * x⁻¹ = y := by
    have := congrArg (fun φ : MulAut X => φ y) hx
    simpa [MulAut.conj_apply] using this
  calc y * x = x * y * x⁻¹ * x := by rw [h1]
    _ = x * y := by group

theorem centralizer_range_conj_eq_bot (hZ : Subgroup.center X = ⊥) :
    Subgroup.centralizer ((MulAut.conj : X →* MulAut X).range : Set (MulAut X)) = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  ext g
  have h1 := Subgroup.mem_centralizer_iff.mp hφ (MulAut.conj g) ⟨g, rfl⟩
  have h2 : MulAut.conj (φ g) = MulAut.conj g := by
    rw [← mul_conj_mul_inv, ← h1, mul_inv_cancel_right]
  exact congrArg (fun y => y) (conj_injective hZ h2)

theorem generalizedFitting_eq_of_component {G : Type} [Group G] [Finite G] (Q : Subgroup G)
    (hQ : CFSG.IsComponent Q) (hC : Subgroup.centralizer (Q : Set G) = ⊥) :
    CFSG.generalizedFitting G = Q :=
  CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot Q hQ hC

noncomputable def rangeConjEquiv (hZ : Subgroup.center X = ⊥) :
    X ≃* ↥(MulAut.conj : X →* MulAut X).range :=
  MonoidHom.ofInjective (conj_injective hZ)

theorem pow_mem_of_mem_sup {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B) :
    ∀ y ∈ (MulAut.conj : X →* MulAut X).range ⊔ B, ∃ e : ℕ,
      y ^ 2 ^ e ∈ (MulAut.conj : X →* MulAut X).range := by
  have := normal_range_conj X
  intro y hy
  obtain ⟨i, hi, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  obtain ⟨e, he⟩ := hB ⟨b, hb⟩
  have hbe : b ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  refine ⟨e, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff i).mpr hi, one_mul, ← QuotientGroup.mk_pow, hbe,
    QuotientGroup.mk_one]

variable [Finite X] [IsSimpleGroup X]

theorem generalizedFitting_sup (hnab : ∃ a b : X, a * b ≠ b * a) (B : Subgroup (MulAut X)) :
    CFSG.generalizedFitting ↥((MulAut.conj : X →* MulAut X).range ⊔ B) =
      (MulAut.conj : X →* MulAut X).range.subgroupOf ((MulAut.conj : X →* MulAut X).range ⊔ B) := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  set Z := I ⊔ B with hZdef
  have hZ := center_eq_bot_of_nonabelian' hnab
  have hIn : I.Normal := normal_range_conj X
  set Q : Subgroup ↥Z := I.subgroupOf Z with hQ
  have hQn : Q.Normal := by rw [hQ]; infer_instance
  let e : X ≃* ↥Q := (rangeConjEquiv hZ).trans (Subgroup.subgroupOfEquivOfLe le_sup_left).symm
  have hQs : IsSimpleGroup ↥Q := e.symm.isSimpleGroup
  have hQab : ∃ a b : ↥Q, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul, h]
  refine generalizedFitting_eq_of_component Q
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hQab).1, hQn.isSubnormal⟩ ?_
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h1 : (z : MulAut X) ∈ Subgroup.centralizer (I : Set (MulAut X)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    have := Subgroup.mem_centralizer_iff.mp hz ⟨i, Subgroup.mem_sup_left hi⟩
      (by rw [hQ, SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hi)
    exact congrArg Subtype.val this
  rw [centralizer_range_conj_eq_bot hZ, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

omit [Finite X] [IsSimpleGroup X] in
theorem isSylowTwo_sup [Finite X] {B : Subgroup (MulAut X)} (hB : IsPGroup 2 B)
    (hBI : IsSylowIn 2 (B ⊓ (MulAut.conj : X →* MulAut X).range)
      (MulAut.conj : X →* MulAut X).range) :
    quasithinIsSylowTwo (B.subgroupOf ((MulAut.conj : X →* MulAut X).range ⊔ B)) := by
  set I := (MulAut.conj : X →* MulAut X).range with hI
  have hIn : I.Normal := normal_range_conj X
  refine ⟨hB.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm, ?_⟩
  have h1 : (B ⊓ I).relIndex I = B.relIndex (B ⊔ I) :=
    B6.relIndex_inf_eq_relIndex_sup (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have h2 : (B.subgroupOf (I ⊔ B)).index = B.relIndex (B ⊔ I) := by
    rw [sup_comm]
    rfl
  rw [h2, ← h1]
  exact hBI.not_dvd_relIndex

theorem generalizedFitting_sup_sup (hnab : ∃ a b : X, a * b ≠ b * a) (B : Subgroup (MulAut X)) :
    CFSG.generalizedFitting ↥((MulAut.conj : X →* MulAut X).range ⊔ B) ⊔
      B.subgroupOf ((MulAut.conj : X →* MulAut X).range ⊔ B) = ⊤ := by
  rw [generalizedFitting_sup hnab B, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
    Subgroup.subgroupOf_self]

noncomputable def generalizedFittingEquiv (hnab : ∃ a b : X, a * b ≠ b * a)
    (B : Subgroup (MulAut X)) :
    ↥(CFSG.generalizedFitting ↥((MulAut.conj : X →* MulAut X).range ⊔ B)) ≃* X :=
  (MulEquiv.subgroupCongr (generalizedFitting_sup hnab B)).trans
    ((Subgroup.subgroupOfEquivOfLe le_sup_left).trans
      (rangeConjEquiv (center_eq_bot_of_nonabelian' hnab)).symm)

end CFSG.Quasithin.Vol2.Ch11.SecB
