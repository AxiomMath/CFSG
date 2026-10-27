module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofExc
public import CFSG.RankThree.PartTwo.Sec11.FieldCentRigid82

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def NoOuterType424For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (α : MulAut Z) (J : Subgroup Z), α ^ 3 = 1 →
      α ∉ (MulAut.conj : Z →* MulAut Z).range →
      J ∈ thetaComponentsIn (Item426.fixSub α) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) → False

@[expose] def ThetaCentral119For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (z : Z) (J : Subgroup Z), MulAut.conj z ^ 3 = 1 →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      ∀ t ∈ inSubgroup (aschbacherSolvableCore 3) J, ∀ k ∈ J, t * k = k * t

@[expose] def CentJ119For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (z : Z) (β : MulAut Z) (J : Subgroup Z), MulAut.conj z ^ 3 = 1 →
      (∃ k : ℕ, β ^ 3 ^ k = 1) → MulAut.conj z * β = β * MulAut.conj z →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      (∀ j ∈ J, β j = j) →
        β ^ (3 ^ (Nat.card J).factorization 3) = 1

@[expose] def NormCentJ1117For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (z : Z) (J : Subgroup Z) (y g : Z), MulAut.conj z ^ 3 = 1 →
      J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      y ∈ J → (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 ≠ 1 →
      (∃ k : ℕ, g ^ 3 ^ k = 1) → g * y * g⁻¹ ∈ Subgroup.zpowers y →
        g ∈ Subgroup.normalizer ((Subgroup.centralizer (J : Set Z) : Subgroup Z) : Set Z)

namespace KS11Lie2Proof

section Generic

variable {Z : Type} [Group Z]

theorem eq_of_mul_inv_mem_central {β : MulAut Z} {J : Subgroup Z} (hJp : Group.IsPerfect J)
    (h : ∀ j ∈ J, β j * j⁻¹ ∈ J ∧ ∀ k ∈ J, β j * j⁻¹ * k = k * (β j * j⁻¹)) :
    ∀ j ∈ J, β j = j := by
  let ψ : J →* Subgroup.center J :=
    { toFun := fun j => ⟨⟨β j * (j : Z)⁻¹, (h j j.2).1⟩, by
        rw [Subgroup.mem_center_iff]
        intro k
        exact Subtype.ext ((h j j.2).2 k k.2).symm⟩
      map_one' := by
        ext
        simp
      map_mul' := fun j k => by
        ext
        have hc := (h k k.2).2 (j : Z)⁻¹ (J.inv_mem j.2)
        change β ((j : Z) * k) * ((j : Z) * k)⁻¹ = β j * (j : Z)⁻¹ * (β k * (k : Z)⁻¹)
        calc β ((j : Z) * k) * ((j : Z) * k)⁻¹
            = β j * (β k * (k : Z)⁻¹ * (j : Z)⁻¹) := by rw [map_mul]; group
          _ = β j * ((j : Z)⁻¹ * (β k * (k : Z)⁻¹)) := by rw [hc]
          _ = β j * (j : Z)⁻¹ * (β k * (k : Z)⁻¹) := by group }
  have hker : _root_.commutator J ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  rw [hJp.commutator_eq_top] at hker
  intro j hj
  have h1 : ψ ⟨j, hj⟩ = 1 := hker (Subgroup.mem_top _)
  have h2 : β j * j⁻¹ = 1 := congrArg (fun w : Subgroup.center J => ((w : J) : Z)) h1
  exact mul_inv_eq_one.mp h2

theorem mem_of_mem_theta {J : Subgroup Z} {t : Z}
    (ht : t ∈ inSubgroup (aschbacherSolvableCore 3) J) : t ∈ J :=
  Subgroup.map_subtype_le _ ht

theorem mem_theta_of_central {J : Subgroup Z} (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J))
    {t : Z} (htJ : t ∈ J) (htc : ∀ k ∈ J, t * k = k * t) :
    t ∈ inSubgroup (aschbacherSolvableCore 3) J := by
  have hZ := FieldCentRigid82.center_eq_bot_of_isType424 hJT
  have hmem : QuotientGroup.mk' (aschbacherSolvableCore 3 J) ⟨t, htJ⟩ ∈
      Subgroup.center (J ⧸ aschbacherSolvableCore 3 J) := by
    rw [Subgroup.mem_center_iff]
    intro u
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 J) u
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (htc k k.2).symm
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨⟨t, htJ⟩, hmem, rfl⟩

theorem mul_comm_of_mem_fixSub {z t : Z} (ht : t ∈ Item426.fixSub (MulAut.conj z)) :
    t * z = z * t := by
  have h1 : z * t * z⁻¹ = t := ht
  calc t * z = z * t * z⁻¹ * z := by rw [h1]
    _ = z * t := by group

end Generic

variable {F : ∀ (X : Type) [Group X], Prop}

theorem centAut119For_of_parts (hO : NoOuterType424For F) (hT : ThetaCentral119For F)
    (hC : CentJ119For F) : CentAut119For F := by
  intro Z _ _ hZ α β J hα3 hβ hαβ hJ hJT hβJ
  by_cases hin : α ∈ (MulAut.conj : Z →* MulAut Z).range
  · obtain ⟨z, rfl⟩ := hin
    have hJp : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
    refine hC Z hZ z β J hα3 hβ hαβ hJ hJT
      (eq_of_mul_inv_mem_central hJp fun j hj => ⟨mem_of_mem_theta (hβJ j hj), ?_⟩)
    exact hT Z hZ z J hα3 hJ hJT _ (hβJ j hj)
  · exact (hO Z hZ α J hα3 hin hJ hJT).elim

theorem noOuterType424For_or {F₁ F₂ : ∀ (X : Type) [Group X], Prop}
    (h₁ : NoOuterType424For F₁) (h₂ : NoOuterType424For F₂) :
    NoOuterType424For fun X _ => F₁ X ∨ F₂ X := by
  intro Z _ _ hZ α J hα3 hin hJ hJT
  obtain ⟨X, _, hX | hX, he⟩ := hZ
  · exact h₁ Z ⟨X, inferInstance, hX, he⟩ α J hα3 hin hJ hJT
  · exact h₂ Z ⟨X, inferInstance, hX, he⟩ α J hα3 hin hJ hJT

theorem normCentJ1117For_or {F₁ F₂ : ∀ (X : Type) [Group X], Prop}
    (h₁ : NormCentJ1117For F₁) (h₂ : NormCentJ1117For F₂) :
    NormCentJ1117For fun X _ => F₁ X ∨ F₂ X := by
  intro Z _ _ hZ z J y g hz3 hJ hJT hyJ hyk hy3 hgk hgy
  obtain ⟨X, _, hX | hX, he⟩ := hZ
  · exact h₁ Z ⟨X, inferInstance, hX, he⟩ z J y g hz3 hJ hJT hyJ hyk hy3 hgk hgy
  · exact h₂ Z ⟨X, inferInstance, hX, he⟩ z J y g hz3 hJ hJT hyJ hyk hy3 hgk hgy

end KS11Lie2Proof

@[expose] def NoOuterType424G2 : Prop :=
  NoOuterType424For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def ThetaCentral119G2 : Prop :=
  ThetaCentral119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def CentJ119G2 : Prop :=
  CentJ119For fun X _ => ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def NormCentJ1117G2 : Prop :=
  NormCentJ1117For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def NoOuterType424D4 : Prop :=
  NoOuterType424For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def ThetaCentral119D4 : Prop :=
  ThetaCentral119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def CentJ119D4 : Prop :=
  CentJ119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def NormCentJ1117D4 : Prop :=
  NormCentJ1117For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

theorem centAut119G2_of_parts (hO : NoOuterType424G2) (hT : ThetaCentral119G2)
    (hC : CentJ119G2) : CentAut119G2 :=
  KS11Lie2Proof.centAut119For_of_parts hO hT hC

theorem centAut119D4_of_parts (hO : NoOuterType424D4) (hT : ThetaCentral119D4)
    (hC : CentJ119D4) : CentAut119D4 :=
  KS11Lie2Proof.centAut119For_of_parts hO hT hC

theorem centBound119G2_of_parts (hO : NoOuterType424G2) (hT : ThetaCentral119G2)
    (hC : CentJ119G2) : CentBound119G2 :=
  centBound119G2_of (centAut119G2_of_parts hO hT hC)

theorem centBound119D4_of_parts (hO : NoOuterType424D4) (hT : ThetaCentral119D4)
    (hC : CentJ119D4) : CentBound119D4 :=
  centBound119D4_of (centAut119D4_of_parts hO hT hC)

end CFSG.RankThree.PartTwo.Sec11
