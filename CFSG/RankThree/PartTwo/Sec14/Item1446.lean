module

public import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.Theta.SignalizerCompleteness
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
  CFSG.RankThree.PartTwo.Sec13 CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

@[expose] def Concl142 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ c : G, Subgroup.zpowers c ∈ omegaA A →
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3), Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {c})

@[expose] def Concl143 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
    ∀ Q ∈ maxInvariantPiSubgroups (delta A LB (Subgroup.centralizer {a})) A (piCompl 3),
      Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a})

@[expose] def Item1443 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ∀ S : Set (Subgroup G),
    S ⊆ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) →
    sSup S ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
    sSup S ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a})

@[expose] def Item1444 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ a ∈ A, a ≠ 1 → ∀ Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {a}),
    ∀ S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3),
      ⁅Q, S⁆ ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a})

@[expose] def Item146 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ Y ∈ invariantPiSubgroups ⊤ A (piCompl 3), Y = delta A LB Y → ∀ a ∈ A, a ≠ 1 →
    Y ⊓ Subgroup.centralizer {a} = delta A LB (Y ⊓ Subgroup.centralizer {a}) ∧
      delta A LB (Y ⊓ Subgroup.centralizer {a}) ∈
        collectionIn (scriptQ A LB) (Subgroup.centralizer {a})

omit [Finite G] in
theorem centralizer_singleton_le_normalizer_zpowers (a : G) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {w : G}
    (h : H.map (MulAut.conj w).toMonoidHom = H) : w ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have h1 : w * y * w⁻¹ = w * x * w⁻¹ := hyx
    rwa [← mul_left_cancel (mul_right_cancel h1)]

omit [Finite G] in
theorem le_normalizer_sSup {S : Set (Subgroup G)}
    (h : ∀ Q ∈ S, A ≤ Subgroup.normalizer (Q : Set G)) :
    A ≤ Subgroup.normalizer ((sSup S : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_of_map_conj_eq ?_
  rw [sSup_eq_iSup', Subgroup.map_iSup]
  exact iSup_congr fun Q => map_conj_eq_of_mem_normalizer (h Q.1 Q.2 hx)

omit [Finite G] in
theorem le_normalizer_commutator {Q S : Subgroup G} (hQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hS : A ≤ Subgroup.normalizer (S : Set G)) :
    A ≤ Subgroup.normalizer ((⁅Q, S⁆ : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_of_map_conj_eq ?_
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hQ hx),
    map_conj_eq_of_mem_normalizer (hS hx)]

omit [Finite G] in
theorem isPiSubgroup_piCompl_of_le {X Y : Subgroup G} (hY : IsPiSubgroup (piCompl 3) Y)
    (hXY : X ≤ Y) : IsPiSubgroup (piCompl 3) X :=
  fun q hq => hY q (hq.trans (Subgroup.card_dvd_of_le hXY))

theorem rank3II_14_4_3_reduction (h142 : Concl142 A LB) (h143 : Concl143 A LB) :
    Item1443 A LB := by
  intro a ha ha1 S hS hY
  have hYC : sSup S ≤ Subgroup.centralizer {a} := sSup_le fun Q hQ => (hS hQ).2
  have hAY : A ≤ Subgroup.normalizer ((sSup S : Subgroup G) : Set G) := hY.2.2
  by_cases hΩ : Subgroup.zpowers a ∈ omegaA A
  · have hYN : sSup S ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers a : Set G))
        A (piCompl 3) := ⟨hYC.trans (centralizer_singleton_le_normalizer_zpowers a), hY.2.1, hAY⟩
    obtain ⟨Q, hQ, hYQ⟩ := exists_le_mem_maxInvariantPiSubgroups hYN
    exact ⟨mem_scriptQ_of_le (h142 a hΩ Q hQ).1 hYQ hAY, hYC⟩
  · have hYΔ : sSup S ≤ delta A LB (Subgroup.centralizer {a}) :=
      sSup_le fun Q hQ => le_delta (hS hQ).1 (hS hQ).2
    obtain ⟨Q, hQ, hYQ⟩ := exists_le_mem_maxInvariantPiSubgroups
      (⟨hYΔ, hY.2.1, hAY⟩ : sSup S ∈ invariantPiSubgroups (delta A LB (Subgroup.centralizer {a}))
        A (piCompl 3))
    exact ⟨mem_scriptQ_of_le (h143 a ha ha1 hΩ Q hQ).1 hYQ hAY, hYC⟩

omit [Finite G] in
theorem commutator_mem_invariantPiSubgroups {a : G} {Q S : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3)) :
    ⁅Q, S⁆ ≤ S ∧ ⁅Q, S⁆ ∈ invariantPiSubgroups (Subgroup.centralizer {a}) A (piCompl 3) := by
  have hQS : Q ≤ Subgroup.normalizer (S : Set G) := le_sup_right.trans hS.2.2
  have hle : ⁅Q, S⁆ ≤ S := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hQS
  exact ⟨hle, hle.trans hS.1, isPiSubgroup_piCompl_of_le hS.2.1 hle,
    le_normalizer_commutator hQ.1.1.2.2 (le_sup_left.trans hS.2.2)⟩

theorem rank3II_14_4_4_of_mem_omegaA (h142 : Concl142 A LB) {a : G}
    (hΩ : Subgroup.zpowers a ∈ omegaA A) {Q S : Subgroup G}
    (hQ : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {a}))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3)) :
    ⁅Q, S⁆ ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) := by
  obtain ⟨-, hQS⟩ := commutator_mem_invariantPiSubgroups ⟨hQ.1.1, hQ.2⟩ hS
  obtain ⟨Q', hQ', hle⟩ := exists_le_mem_maxInvariantPiSubgroups
    (⟨hQS.1.trans (centralizer_singleton_le_normalizer_zpowers a), hQS.2.1, hQS.2.2⟩ :
      ⁅Q, S⁆ ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers a : Set G)) A
        (piCompl 3))
  exact ⟨mem_scriptQ_of_le (h142 a hΩ Q' hQ').1 hle hQS.2.2, hQS.1⟩

theorem rank3II_14_4_4_of_eq (h143 : Concl143 A LB) (hAab : IsMulCommutative A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (hK : delta A LB (Subgroup.centralizer {a}) =
      pPrimeCoreOf 3 (Subgroup.centralizer {a}) ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    {Q S : Subgroup G} (hQ : Q ∈ collectionIn (scriptQZero A LB) (Subgroup.centralizer {a}))
    (hS : S ∈ invariantPiSubgroups (Subgroup.centralizer {a}) (A ⊔ Q) (piCompl 3)) :
    ⁅Q, S⁆ ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) := by
  obtain ⟨hQSle, hQS⟩ := commutator_mem_invariantPiSubgroups ⟨hQ.1.1, hQ.2⟩ hS
  set O := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hO
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩))
  have hCAa : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha)
  have hON : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hO'N : O' ≤ Subgroup.normalizer (O : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans hCAa).trans hON
  have hQO : Q ≤ O := by
    have hQK : Q ≤ O ⊔ O' := hK ▸ le_delta hQ.1.1 hQ.2
    rw [hQ.1.2]
    refine (Subgroup.commutator_mono hQK le_rfl).trans ?_
    rw [Subgroup.commutator_le]
    intro x hx α hα
    have hx' : x ∈ ((O : Set G) * (O' : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left O O' hO'N]
      exact hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx'
    have hzα : z * α = α * z :=
      (Subgroup.mem_centralizer_iff.mp (pPrimeCoreOf_le 3 _ hz) α hα).symm
    have hkey : ⁅y * z, α⁆ = y * (α * y⁻¹ * α⁻¹) := by
      rw [commutatorElement_def]
      calc y * z * α * (y * z)⁻¹ * α⁻¹ = y * (z * α) * z⁻¹ * y⁻¹ * α⁻¹ := by group
        _ = y * (α * z) * z⁻¹ * y⁻¹ * α⁻¹ := by rw [hzα]
        _ = y * (α * y⁻¹ * α⁻¹) := by group
    rw [hkey]
    exact mul_mem hy ((Subgroup.mem_normalizer_iff.mp (hON (hAC hα)) y⁻¹).mp (inv_mem hy))
  have hQSO : ⁅Q, S⁆ ≤ O := by
    refine (Subgroup.commutator_mono hQO hS.1).trans ?_
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hON
  have hQSK : ⁅Q, S⁆ ≤ delta A LB (Subgroup.centralizer {a}) := hK ▸ hQSO.trans le_sup_left
  obtain ⟨Q', hQ', hle⟩ := exists_le_mem_maxInvariantPiSubgroups
    (⟨hQSK, hQS.2.1, hQS.2.2⟩ : ⁅Q, S⁆ ∈ invariantPiSubgroups
      (delta A LB (Subgroup.centralizer {a})) A (piCompl 3))
  exact ⟨mem_scriptQ_of_le (h143 a ha ha1 hΩ Q' hQ').1 hle hQS.2.2, hQS.1⟩

theorem rank3II_14_4_4_reduction (h142 : Concl142 A LB) (h143 : Concl143 A LB)
    (hAab : IsMulCommutative A)
    (h1431 : ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      delta A LB (Subgroup.centralizer {a}) = pPrimeCoreOf 3 (Subgroup.centralizer {a}) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    Item1444 A LB := by
  intro a ha ha1 Q hQ S hS
  by_cases hΩ : Subgroup.zpowers a ∈ omegaA A
  · exact rank3II_14_4_4_of_mem_omegaA h142 hΩ hQ hS
  · exact rank3II_14_4_4_of_eq h143 hAab ha ha1 hΩ (h1431 a ha ha1 hΩ) hQ hS

theorem rank3II_14_6_of_solvable (hA : IsE27 A) (h443 : Item1443 A LB) {Y : Subgroup G}
    (hYΔ : Y = delta A LB Y) (hY : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3))
    (hYsol : Group.IsSolvable Y) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Y ⊓ Subgroup.centralizer {a} = delta A LB (Y ⊓ Subgroup.centralizer {a}) ∧
      delta A LB (Y ⊓ Subgroup.centralizer {a}) ∈
        collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAab : IsMulCommutative A := hA.1.1
  have hY3 : ¬ 3 ∣ Nat.card Y := (isPiSubgroup_piCompl_iff Nat.prime_three Y).mp hY.2.1
  have hAC : ∀ b ∈ A, A ≤ Subgroup.normalizer ((Subgroup.centralizer {b} : Subgroup G) : Set G) :=
    fun b hb => le_trans (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨b, hb⟩))) Subgroup.le_normalizer
  let θ : G → Subgroup G := fun b => delta A LB (Y ⊓ Subgroup.centralizer {b})
  have hθY : ∀ b, θ b ≤ Y := fun b => (delta_le _).trans inf_le_left
  have hθQ : ∀ b ∈ A, b ≠ 1 → θ b ∈ collectionIn (scriptQ A LB) (Subgroup.centralizer {b}) := by
    intro b hb hb1
    refine h443 b hb hb1 _ (fun Q hQ => ⟨hQ.1, hQ.2.trans inf_le_right⟩) ⟨le_top, ?_, ?_⟩
    · exact isPiSubgroup_piCompl_of_le hY.2.1 (hθY b)
    · exact le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hθ : CFSG.Open.IsSolvableSignalizerFunctor 3 A θ := by
    refine ⟨fun b _ _ => (delta_le _).trans inf_le_right, fun b _ _ => ?_,
      fun b hb hb1 x hx => map_conj_eq_of_mem_normalizer ((hθQ b hb hb1).1.1.2.2 hx),
      fun b hb hb1 b' hb' _ => ?_, fun b _ _ => ?_⟩
    · refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hY3 ?_
      exact h3.trans (Subgroup.card_dvd_of_le (hθY b))
    · refine le_delta (mem_scriptQ_of_le (hθQ b hb hb1).1 inf_le_left
        (le_normalizer_inf (hθQ b hb hb1).1.1.2.2 (hAC b' hb'))) (le_inf ?_ inf_le_right)
      exact inf_le_left.trans (hθY b)
    · exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (hθY b))
  have hrank : 3 ^ 3 ∣ Nat.card A := by rw [hA.2]; norm_num
  obtain ⟨-, -, hW⟩ := CFSG.RankThree.Theta.glauberman_solvable_signalizer_functor_univ
    Nat.prime_three A hAab hA.1.2 hrank θ hθ
  have hYW : Y = ⨆ (b : G) (_ : b ∈ A) (_ : b ≠ 1), θ b := by
    refine le_antisymm ?_ (iSup_le fun b => iSup_le fun _ => iSup_le fun _ => hθY b)
    conv_lhs => rw [hYΔ]
    refine sSup_le fun Q hQ => ?_
    have hQ3 : Nat.Coprime 3 (Nat.card Q) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      fun h3 => hY3 (h3.trans (Subgroup.card_dvd_of_le hQ.2))
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hA.1 (by rw [hA.2]; norm_num)
      hQ.1.1.2.2 hQ3 fun h hhA hh1 => ?_
    refine le_trans ?_ (le_iSup_of_le h (le_iSup_of_le hhA (le_iSup_of_le hh1 le_rfl)))
    exact le_delta (mem_scriptQ_of_le hQ.1 inf_le_left (le_normalizer_inf hQ.1.1.2.2 (hAC h hhA)))
      (inf_le_inf_right _ hQ.2)
  refine ⟨?_, hθQ a ha ha1⟩
  conv_lhs => rw [hYW]
  exact (hW a ha ha1).symm

theorem item146_of_solvable (hA : IsE27 A) (h443 : Item1443 A LB)
    (hsol : ∀ Y ∈ invariantPiSubgroups ⊤ A (piCompl 3), Group.IsSolvable Y) : Item146 A LB :=
  fun Y hY hYΔ _ ha ha1 => rank3II_14_6_of_solvable hA h443 hYΔ hY (hsol Y hY) ha ha1

end CFSG.RankThree.PartTwo.Sec14
