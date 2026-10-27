module

public import CFSG.RankThree.PartOne.S9.QD32.Rigidity
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction

public section

namespace CFSG.RankThree.PartOne

open CFSG.SectionRank.Ccomm CFSG.RankThree.PartOne.QD32Facts Subgroup
open scoped commutatorElement

namespace QD32Facts

variable {G : Type*} [Group G]

theorem crit_comm {P T : Subgroup G} (hTP : T ≤ P) (hcrit : ThompsonCritical (T.subgroupOf P)) :
    ∀ x ∈ P, ∀ t ∈ T, ⁅x, t⁆ ∈ T ∧ ∀ u ∈ T, u * ⁅x, t⁆ = ⁅x, t⁆ * u := by
  intro x hx t ht
  have h3 := hcrit.2.2.1
  have hmem : (⁅(⟨x, hx⟩ : P), (⟨t, hTP ht⟩ : P)⁆ : P) ∈
      ⁅(⊤ : Subgroup P), T.subgroupOf P⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) ht
  obtain ⟨hT1, hT2⟩ := h3 hmem
  refine ⟨hT1, fun u hu => ?_⟩
  have := Subgroup.mem_centralizer_iff.mp hT2 ⟨u, hTP hu⟩ hu
  exact congrArg Subtype.val this

theorem commutatorElement_mul_right' (x a b : G) : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

end QD32Facts

theorem criticalQuaternionDihedralOvergroupRigidity :
    CriticalQuaternionDihedralOvergroupRigidity := by
  intro G _ _ P A T S hP2 hAodd hAP hPA hTP hcrit hST hAS ⟨φ⟩ hcyc
  obtain ⟨z, hz2, hzc, ⟨i, j, hij⟩, hgen, hinn⟩ := QD32Facts.exists_data_of_equiv_QD32 φ
  have hSP : S ≤ P := hST.trans hTP
  set z' : G := (z : G) with hz'
  have hzS : z' ∈ S := z.2
  have hzcent : ∀ s ∈ S, s * z' = z' * s := by
    intro s hs
    have hzmem : z ∈ center S := by rw [hzc]; exact Subgroup.mem_zpowers z
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzmem) ⟨s, hs⟩)
  have hz'1 : z' ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz2
    omega
  have hz'sq : z' ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    exact congrArg Subtype.val h
  have hcomm := QD32Facts.crit_comm hTP hcrit
  have hz'T : z' ∈ T ∧ ∀ u ∈ T, u * z' = z' * u := by
    have hij' : z' = ⁅(i : G), (j : G)⁆ := by
      rw [hz', ← hij]
      rfl
    rw [hij']
    exact hcomm (i : G) (hSP i.2) (j : G) (hST j.2)
  set C : Subgroup G := P ⊓ Subgroup.centralizer (S : Set G) with hC
  have hCP : C ≤ P := inf_le_left
  have hZC : ∀ w ∈ T, (∀ u ∈ T, u * w = w * u) → w ∈ C := by
    intro w hw hwc
    refine ⟨hTP hw, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    exact hwc s (hST hs)
  have hz'C : z' ∈ C := hZC z' hz'T.1 hz'T.2
  have : IsCyclic C := hcyc
  have key : ∀ x ∈ P, ∀ s ∈ S, s ^ 2 = 1 → ⁅x, s⁆ = 1 ∨ ⁅x, s⁆ = z' := by
    intro x hx s hs hs2
    obtain ⟨hwT, hwc⟩ := hcomm x hx s (hST hs)
    have hwC : ⁅x, s⁆ ∈ C := hZC _ hwT hwc
    have hws : s * ⁅x, s⁆ = ⁅x, s⁆ * s := hwc s (hST hs)
    have hsq : ⁅x, s⁆ ^ 2 = 1 := by
      have h1 : (⁅x, s⁆ * s) ^ 2 = 1 := by
        have : ⁅x, s⁆ * s = x * s * x⁻¹ := by simp [commutatorElement_def]
        have hconj : (x * s * x⁻¹) ^ 2 = x * s ^ 2 * x⁻¹ := by
          simp only [pow_two]; group
        rw [this, hconj, hs2]
        group
      have h2 : (⁅x, s⁆ * s) ^ 2 = ⁅x, s⁆ ^ 2 * s ^ 2 :=
        (Commute.mul_pow (show Commute ⁅x, s⁆ s from hws.symm) 2)
      rw [h2, hs2, mul_one] at h1
      exact h1
    have hcase := QD32Facts.eq_one_or_eq_of_sq_eq_one_of_isCyclic
      (u := (⟨⁅x, s⁆, hwC⟩ : C)) (z := (⟨z', hz'C⟩ : C))
      (Subtype.ext (by simpa using hsq)) (Subtype.ext (by simpa using hz'sq))
      (fun h => hz'1 (by simpa using congrArg Subtype.val h))
    rcases hcase with h | h
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  have hzp : ∀ w ∈ Subgroup.zpowers z', ∀ s ∈ S, s * w = w * s := by
    intro w hw s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_right (show Commute s z' from hzcent s hs) k)).eq
  have hcommS : ∀ x ∈ P, ∀ t : S, ⁅x, (t : G)⁆ ∈ Subgroup.zpowers z' := by
    intro x hx t
    have ht : t ∈ Subgroup.closure {s : S | s ^ 2 = 1} := by
      rw [hgen]; exact Subgroup.mem_top _
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      have hsq : (t : G) ^ 2 = 1 := by
        have : t ^ 2 = 1 := ht
        exact congrArg Subtype.val this
      rcases key x hx t t.2 hsq with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers z'
    | one => simp
    | mul a b _ _ iha ihb =>
      have hcb : (a : G) * ⁅x, (b : G)⁆ * (a : G)⁻¹ = ⁅x, (b : G)⁆ := by
        have := hzp _ ihb (a : G) a.2
        rw [this]; group
      rw [Subgroup.coe_mul, QD32Facts.commutatorElement_mul_right', hcb]
      exact Subgroup.mul_mem _ iha ihb
    | inv a _ iha =>
      have h1 : ⁅x, ((a⁻¹ : S) : G)⁆ = (a : G)⁻¹ * ⁅x, (a : G)⁆⁻¹ * (a : G) := by
        simp only [Subgroup.coe_inv, commutatorElement_def]
        group
      have hcb : (a : G)⁻¹ * ⁅x, (a : G)⁆⁻¹ * (a : G) = ⁅x, (a : G)⁆⁻¹ := by
        have := hzp _ (Subgroup.inv_mem _ iha) (a⁻¹ : S) (a⁻¹).2
        simp only [Subgroup.coe_inv] at this
        rw [this]; group
      rw [h1, hcb]
      exact Subgroup.inv_mem _ iha
  have hnorm : ∀ x ∈ P, ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro x hx s hs
    have h1 : x * s * x⁻¹ = ⁅x, s⁆ * s := by simp [commutatorElement_def]
    rw [h1]
    exact S.mul_mem (Subgroup.zpowers_le.mpr hzS (hcommS x hx ⟨s, hs⟩)) hs
  have hfact : ∀ x ∈ P, ∃ s ∈ S, ∃ c ∈ C, x = s * c := by
    intro x hx
    let α : MulAut S :=
      { toFun := fun s => ⟨x * s * x⁻¹, hnorm x hx s s.2⟩
        invFun := fun s => ⟨x⁻¹ * s * x, by simpa using hnorm x⁻¹ (inv_mem hx) s s.2⟩
        left_inv := fun s => Subtype.ext (by simp [mul_assoc])
        right_inv := fun s => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
    have hα : ∀ s : S, s⁻¹ * α s ∈ center S := by
      intro s
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcommS x hx s)
      have hcen : s⁻¹ * α s = z ^ k := by
        apply Subtype.ext
        have h1 : ((s⁻¹ * α s : S) : G) = (s : G)⁻¹ * (x * s * x⁻¹) := rfl
        have h2 : (s : G)⁻¹ * (x * s * x⁻¹) = (s : G)⁻¹ * (⁅x, (s : G)⁆ * s) := by
          simp [commutatorElement_def]
        have h3 : (s : G)⁻¹ * (⁅x, (s : G)⁆ * s) = ⁅x, (s : G)⁆ := by
          have := hzp _ (hk ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers z') k) (s : G) s.2
          rw [← hk] at this ⊢
          rw [← this]
          group
        rw [h1, h2, h3, ← hk]
        simp [hz']
      rw [hzc, hcen]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k
    obtain ⟨s₀, hs₀⟩ := hinn α hα
    refine ⟨(s₀ : G), s₀.2, (s₀ : G)⁻¹ * x, ⟨?_, ?_⟩, by group⟩
    · exact P.mul_mem (P.inv_mem (hSP s₀.2)) hx
    · refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
      have h := congrArg (fun f : MulAut S => ((f ⟨s, hs⟩ : S) : G)) hs₀
      simp only [MulAut.conj_apply] at h
      have h2 : x * s * x⁻¹ = (s₀ : G) * s * (s₀ : G)⁻¹ := h
      calc s * ((s₀ : G)⁻¹ * x) = (s₀ : G)⁻¹ * ((s₀ : G) * s * (s₀ : G)⁻¹) * x := by group
        _ = (s₀ : G)⁻¹ * (x * s * x⁻¹) * x := by rw [h2]
        _ = (s₀ : G)⁻¹ * x * s := by group
  have hCcent : ∀ c ∈ C, ∀ x ∈ P, c * x = x * c := by
    intro c hc x hx
    obtain ⟨s, hs, c', hc', rfl⟩ := hfact x hx
    have h1 : s * c = c * s := Subgroup.mem_centralizer_iff.mp hc.2 s hs
    have h2 : c' * c = c * c' := by
      have := (IsCyclic.isMulCommutative (α := C)).is_comm.comm ⟨c, hc⟩ ⟨c', hc'⟩
      exact (congrArg Subtype.val this).symm
    calc c * (s * c') = (c * s) * c' := by group
      _ = (s * c) * c' := by rw [h1]
      _ = s * (c * c') := by group
      _ = s * (c' * c) := by rw [h2]
      _ = s * c' * c := by group
  have hconj : ∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ ∈ C := by
    intro a ha c hc
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hAP ha) c).mp (hCP hc),
      Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hs' : a⁻¹ * s * a ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (hAS (inv_mem ha)) s).mp hs
      simpa using this
    have hcc : (a⁻¹ * s * a) * c = c * (a⁻¹ * s * a) :=
      Subgroup.mem_centralizer_iff.mp hc.2 _ hs'
    calc s * (a * c * a⁻¹) = a * ((a⁻¹ * s * a) * c) * a⁻¹ := by group
      _ = a * (c * (a⁻¹ * s * a)) * a⁻¹ := by rw [hcc]
      _ = (a * c * a⁻¹) * s := by group
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨fun hc => hconj a ha c hc, fun hc => ?_⟩
    have := hconj a⁻¹ (inv_mem ha) _ hc
    simpa [mul_assoc] using this
  have hAcent : ∀ a ∈ A, ∀ c ∈ C, a * c * a⁻¹ = c := by
    let _ := Subgroup.conjMulDistribMulActionOfLeNormalizer A C hAC
    have hCp : IsPGroup 2 C := hP2.to_le hCP
    have h1 := QD32Facts.hom_eq_one_of_isCyclic_isPGroup_two hCp hAodd
      (MulDistribMulAction.toMulAut ↥A ↥C)
    intro a ha c hc
    have h2 : (MulDistribMulAction.toMulAut ↥A ↥C ⟨a, ha⟩) ⟨c, hc⟩ = ⟨c, hc⟩ := by
      rw [DFunLike.congr_fun h1 ⟨a, ha⟩]
      rfl
    exact congrArg Subtype.val h2
  have hPAS : ⁅P, A⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    obtain ⟨s, hs, c, hc, rfl⟩ := hfact x hx
    have hca : c * a = a * c := by
      have := hAcent a ha c hc
      calc c * a = (a * c * a⁻¹) * a := by rw [this]
        _ = a * c := by group
    have h1 : ⁅s * c, a⁆ = s * (a * s⁻¹ * a⁻¹) := by
      calc ⁅s * c, a⁆ = s * (c * a) * c⁻¹ * s⁻¹ * a⁻¹ := by simp only [commutatorElement_def]; group
        _ = s * (a * c) * c⁻¹ * s⁻¹ * a⁻¹ := by rw [hca]
        _ = s * (a * s⁻¹ * a⁻¹) := by group
    rw [h1]
    exact S.mul_mem hs ((Subgroup.mem_normalizer_iff.mp (hAS ha) s⁻¹).mp (S.inv_mem hs))
  exact le_antisymm (hPA.symm.le.trans hPAS) hSP

end CFSG.RankThree.PartOne
