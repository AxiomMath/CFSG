module

public import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofCent
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Setup

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

@[expose] def CentAut119For (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X)) →
    ∀ (α β : MulAut Z) (J : Subgroup Z), α ^ 3 = 1 → (∃ k : ℕ, β ^ 3 ^ k = 1) →
      α * β = β * α → J ∈ thetaComponentsIn (Item426.fixSub α) →
      IsType424 (J ⧸ aschbacherSolvableCore 3 J) →
      (∀ j ∈ J, β j * j⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) J) →
        β ^ (3 ^ (Nat.card J).factorization 3) = 1

namespace KS11LieProof

variable {G : Type} [Group G] [Finite G]

theorem map_theta_le {Y K : Subgroup G} (hKY : K ≤ Y) {k : G}
    (hk : k ∈ inSubgroup (aschbacherSolvableCore 3) K) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨k, hKY (by
      obtain ⟨m, -, rfl⟩ := hk
      exact m.2)⟩ ∈ inSubgroup (aschbacherSolvableCore 3)
        ((K.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) := by
  set J := (K.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) with hJ
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  let ι : K →* Y := Subgroup.inclusion hKY
  have hιJ : ∀ x : K, π (ι x) ∈ J := fun x =>
    Subgroup.mem_map_of_mem π (by rw [Subgroup.mem_subgroupOf]; exact x.2)
  let ρ : K →* J := (π.comp ι).codRestrict J hιJ
  have hρ : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    obtain ⟨l, hl, rfl⟩ := hq
    exact ⟨⟨l, Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
  obtain ⟨hθs, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  obtain ⟨-, -, -, hmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := J) Nat.prime_three
  set M := (aschbacherSolvableCore 3 K).map ρ with hM
  have hMn : M.Normal :=
    Subgroup.Normal.map (inferInstance : (aschbacherSolvableCore 3 K).Normal) ρ hρ
  have hMs : Group.IsSolvable M := Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
  have hM3 : ¬ 3 ∣ Nat.card M := fun h =>
    hθ3 (h.trans (Subgroup.card_map_dvd (aschbacherSolvableCore 3 K) ρ))
  have hle := hmax M hMn hMs hM3
  obtain ⟨m, hm, rfl⟩ := hk
  refine ⟨ρ m, hle ⟨m, hm, rfl⟩, rfl⟩

theorem centBound119For_of_centAut {F : ∀ (X : Type) [Group X], Prop} (h : CentAut119For F) :
    CentBound119For F := by
  intro G _ _ Y K c t hY hcN hc3 hK hT htN ht3 htc htK
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  set J := (K.subgroupOf Y).map π with hJdef
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hJ := Item426.map_mem_thetaComponentsIn_fixSub Y hcN hc3 hK
  obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv Y hKY
  have hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J) := isType424_of_mulEquiv eK.symm hT
  obtain ⟨k, hk⟩ := ht3
  have hαβ : Item426.thetaAut Y hcN * Item426.thetaAut Y htN =
      Item426.thetaAut Y htN * Item426.thetaAut Y hcN := by
    have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (Y : Set G)) * ⟨t, htN⟩ = ⟨t, htN⟩ * ⟨c, hcN⟩ :=
      Subtype.ext htc.symm
    simp only [Item426.thetaAut]
    rw [← map_mul, ← map_mul, h1, map_mul, map_mul]
  have hβJ : ∀ j ∈ J, Item426.thetaAut Y htN j * j⁻¹ ∈
      inSubgroup (aschbacherSolvableCore 3) J := by
    rintro _ ⟨y, hy, rfl⟩
    have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
    have h1 := map_theta_le hKY (htK _ hyK)
    convert h1 using 1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, Item426.thetaAut_mk,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  have hconc := h (Y ⧸ aschbacherSolvableCore 3 Y) hY (Item426.thetaAut Y hcN)
    (Item426.thetaAut Y htN) J (Item426.thetaAut_pow_eq_one Y hcN hc3)
    ⟨k, Item426.thetaAut_pow_eq_one Y htN hk⟩ hαβ hJ hJT hβJ
  have hJK : Nat.card J ∣ Nat.card K := by
    have h1 := Subgroup.card_map_dvd (K.subgroupOf Y) π
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv] at h1
  have hle : (Nat.card J).factorization 3 ≤ (Nat.card K).factorization 3 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hJK 3
  have hτ : Item426.thetaAut Y htN ^ (3 ^ (Nat.card K).factorization 3) = 1 := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
    rw [hr, pow_add, pow_mul, hconc, one_pow]
  refine ⟨⟨t, htN⟩ ^ (3 ^ (Nat.card K).factorization 3), MonoidHom.mem_ker.mpr ?_, by simp⟩
  rw [map_pow]
  exact hτ

end KS11LieProof

@[expose] def CentAut119G2 : Prop :=
  CentAut119For fun X _ => ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)

@[expose] def CentAut119D4 : Prop :=
  CentAut119For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)

@[expose] def CentAut119Spor : Prop :=
  CentAut119For fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.He)

theorem centBound119G2_of (h : CentAut119G2) : CentBound119G2 :=
  KS11LieProof.centBound119For_of_centAut h

theorem centBound119D4_of (h : CentAut119D4) : CentBound119D4 :=
  KS11LieProof.centBound119For_of_centAut h

theorem centBound119Spor_of (h : CentAut119Spor) : CentBound119Spor :=
  KS11LieProof.centBound119For_of_centAut h

end CFSG.RankThree.PartTwo.Sec11
