module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1ShapeAux1
import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridge
import CFSG.SignalizerFunctorTheorem.ElementaryAbelian
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.WeakClosure81.Thirteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 CoverOf)
open CFSG.Blueprint (LieModel)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem w183odd_quasisimple_of_simple {X : Type} [Group X]
    (hs : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) :
    CFSG.Open.IsQuasisimple X := by
  have hcenter : Subgroup.center X = ⊥ := w183_center_eq_bot_of_simple hs hnab
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      haveI := (commutator_eq_bot_iff X).mp h
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (mul_comm a b)
    · exact h
  · have e : X ⧸ Subgroup.center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

theorem w183odd_component_cover_of_simple {W : Type} [Group W] {Y L : Subgroup W}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hsimple : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a) :
    CFSG.Open.IsComponentOf (L.subgroupOf Y) ⊤ ∧ CoverOf ↥(L.subgroupOf Y) ↥L := by
  haveI := hsimple
  have hqL : CFSG.Open.IsQuasisimple ↥L := w183odd_quasisimple_of_simple hsimple hnab
  have hqL' : CFSG.Open.IsQuasisimple ↥(L.subgroupOf Y) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY) hqL
  have hsimpleL' : IsSimpleGroup ↥(L.subgroupOf Y) :=
    (Subgroup.subgroupOfEquivOfLe hLY).isSimpleGroup
  have hnabL' : ∃ a b : ↥(L.subgroupOf Y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨(Subgroup.subgroupOfEquivOfLe hLY).symm a,
      (Subgroup.subgroupOfEquivOfLe hLY).symm b, ?_⟩
    intro h
    exact hab (by simpa using congrArg (Subgroup.subgroupOfEquivOfLe hLY) h)
  have hcenterL' : Subgroup.center ↥(L.subgroupOf Y) = ⊥ :=
    w183_center_eq_bot_of_simple hsimpleL' hnabL'
  refine ⟨⟨le_top, ?_, hqL'⟩, hqL', ⟨?_⟩⟩
  · exact CFSG.Open.IsSubnormal.step le_top (hLn.subgroupOf ⊤)
      (CFSG.Open.IsSubnormal.refl ⊤)
  · exact ((QuotientGroup.quotientMulEquivOfEq hcenterL').trans
      QuotientGroup.quotientBot).trans (Subgroup.subgroupOfEquivOfLe hLY)

theorem w183odd_index_eq_pow_mOf {A D : Subgroup (LGL 2 V)} (hel : IsElemAbelian 2 A)
    (hDA : D ≤ A) : (D.subgroupOf A).index = 2 ^ mOf A D := by
  obtain ⟨n, hn⟩ := IsPGroup.index hel.isPGroup (D.subgroupOf A)
  have hmOf : mOf A D = n := by
    unfold mOf
    rw [hn, Nat.log_pow (by norm_num : 1 < 2)]
  rw [hmOf, hn]

theorem w183odd_exists_card_four_inf_eq_bot {A D : Subgroup (LGL 2 V)}
    (hel : IsElemAbelian 2 A) (hDA : D ≤ A) (h2 : 2 ≤ mOf A D) :
    ∃ B : Subgroup (LGL 2 V), B ≤ A ∧ Nat.card ↥B = 4 ∧ B ⊓ D = ⊥ := by
  obtain ⟨F, hFA, -, hDF, hsup⟩ :=
    CFSG.SignalizerFunctorTheorem.exists_complement_containing Nat.prime_two hel hDA bot_le
      (inf_bot_eq D)
  have hcard := CFSG.SignalizerFunctorTheorem.card_mul_card_complement hel hDA hFA hDF hsup
  have hDsub : Nat.card ↥(D.subgroupOf A) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv
  have hmul1 : (D.subgroupOf A).index * Nat.card ↥D = Nat.card ↥A := by
    rw [← hDsub, Subgroup.index_mul_card]
  have hmul2 : Nat.card ↥D * Nat.card ↥F = Nat.card ↥A := hcard
  have hDpos : 0 < Nat.card ↥D :=
    Finite.card_pos_iff.2 ⟨⟨1, D.one_mem⟩⟩
  have hFcard : Nat.card ↥F = (D.subgroupOf A).index := by
    refine Nat.mul_right_cancel hDpos ?_
    calc Nat.card ↥F * Nat.card ↥D = Nat.card ↥D * Nat.card ↥F := Nat.mul_comm _ _
      _ = Nat.card ↥A := hmul2
      _ = (D.subgroupOf A).index * Nat.card ↥D := hmul1.symm
  have hF4 : 4 ≤ Nat.card ↥F := by
    rw [hFcard, w183odd_index_eq_pow_mOf hel hDA]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mOf A D := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨B, hBF, hBcard⟩ :=
    exists_subgroup_card_four (A := F) ((hel.mono hFA).isPGroup) hF4
  have hFD : F ⊓ D = ⊥ := by rw [inf_comm]; exact hDF
  exact ⟨B, hBF.trans hFA, hBcard,
    le_bot_iff.mp ((inf_le_inf_right D hBF).trans (le_of_eq hFD))⟩

theorem w183odd_card_le_two_of_mOf_le_one {A D F : Subgroup (LGL 2 V)}
    (hel : IsElemAbelian 2 A) (hDA : D ≤ A) (hFA : F ≤ A) (hDF : D ⊓ F = ⊥)
    (hF1 : mOf A F ≤ 1) : Nat.card ↥D ≤ 2 := by
  have hDFA : Nat.card ↥(D ⊔ F) = Nat.card ↥D * Nat.card ↥F :=
    CFSG.SignalizerFunctorTheorem.card_sup_of_le_elemAbelian hel hDA hFA hDF
  have hle : Nat.card ↥D * Nat.card ↥F ≤ Nat.card ↥A := by
    rw [← hDFA]
    exact Subgroup.card_le_of_le (sup_le hDA hFA)
  have hAeq : Nat.card ↥A = 2 ^ mOf A F * Nat.card ↥F := by
    rw [← Subgroup.index_mul_card (F.subgroupOf A),
      w183odd_index_eq_pow_mOf hel hFA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv]
  have hpow : 2 ^ mOf A F ≤ 2 := by
    calc 2 ^ mOf A F ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hF1
      _ = 2 := by norm_num
  have hFpos : 0 < Nat.card ↥F := Finite.card_pos_iff.2 ⟨⟨1, F.one_mem⟩⟩
  have hDle : Nat.card ↥D * Nat.card ↥F ≤ 2 * Nat.card ↥F := by
    calc Nat.card ↥D * Nat.card ↥F ≤ Nat.card ↥A := hle
      _ = 2 ^ mOf A F * Nat.card ↥F := hAeq
      _ ≤ 2 * Nat.card ↥F := Nat.mul_le_mul_right _ hpow
  exact Nat.le_of_mul_le_mul_right hDle hFpos

end CFSG.LocalAnalysis.WeakClosure81

end
