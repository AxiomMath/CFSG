module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndX
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndXExt
import CFSG.LocalAnalysis.UniquenessCase.UC6K318Step

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K318

open Subgroup CFSG.RankThree.PartTwo.Sec4.Census CFSG.ComponentClassification.PresentationLocal
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (eq_of_simple_quotients)
open scoped commutatorElement

variable {X : Type} [Group X]

theorem exists_commData [Finite X] {T : Subgroup X} [T.Normal] (hT2 : IsPGroup 2 T)
    (hTZ : ¬ T ≤ center X)
    (H1 : ∀ A : Subgroup X, A.Normal → IsPGroup 2 A → IsMulCommutative A → A ≤ center X)
    (H2 : ∀ s ∈ center X, ∀ t ∈ center X, s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s = t) :
    ∃ z : T, CommData T z ∧ (∀ c ∈ center T, (c : X) ∈ center X) ∧
      ∃ w : ℕ, 1 ≤ w ∧ Nat.card (T ⧸ center T) = 2 ^ (2 * w) := by
  have hcenX : ∀ A : Subgroup T, A.Characteristic → IsMulCommutative A → ∀ a ∈ A,
      (a : X) ∈ center X := by
    intro A hA hAc a ha
    have hn : (A.map T.subtype).Normal := inferInstance
    exact H1 _ hn ((hT2.to_subgroup A).map _) inferInstance ⟨a, ha, rfl⟩
  have hZX : ∀ c ∈ center T, (c : X) ∈ center X := hcenX _ inferInstance inferInstance
  have hcenT : ∀ A : Subgroup T, A.Characteristic → IsMulCommutative A → A ≤ center T := by
    intro A hA hAc a ha
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp (hcenX A hA hAc a ha) g)
  have hsymp : ∀ A : Subgroup T, A.Characteristic → IsMulCommutative A → IsCyclic A := by
    intro A hA hAc
    refine isCyclic_of_unique_involution (hT2.to_subgroup A) fun s t hs ht hs1 ht1 => ?_
    have hs' : ((s : T) : X) * (s : T) = 1 := by
      have := congrArg (fun v : A => ((v : T) : X)) hs
      simpa using this
    have ht' : ((t : T) : X) * (t : T) = 1 := by
      have := congrArg (fun v : A => ((v : T) : X)) ht
      simpa using this
    exact Subtype.ext (Subtype.ext (H2 _ (hcenX A hA hAc s s.2) _ (hcenX A hA hAc t t.2) hs' ht'
      (fun h => hs1 (Subtype.ext (Subtype.ext h))) (fun h => ht1 (Subtype.ext (Subtype.ext h)))))
  have hnt : Nontrivial T := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hTZ
    intro s hs
    have : (⟨s, hs⟩ : T) = 1 := Subsingleton.elim _ _
    rw [show s = 1 from congrArg Subtype.val this]
    exact one_mem _
  rcases structure_of_central hT2 hsymp hcenT with hcyc |
      ⟨z, hzc, hzord, -, hcomm, -, -, -, w, hw1, hcard⟩
  ·
    exfalso
    apply hTZ
    intro t ht
    refine hZX ⟨t, ht⟩ (mem_center_iff.mpr fun g => ?_)
    exact (IsCyclic.isMulCommutative : IsMulCommutative T).is_comm.comm g ⟨t, ht⟩
  · have hz2 : z * z = 1 := by
      have h := pow_orderOf_eq_one z
      rwa [hzord, sq] at h
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hzord
      exact absurd hzord (by norm_num)
    have hcd : CommData T z :=
      { mem_center := hzc
        sq_eq_one := hz2
        ne_one := hz1
        comm_mem := hcomm
        sq_mem := sq_mem_center_of_comm hzc hz2 hcomm }
    exact ⟨z, hcd, hZX, w, hw1, hcard⟩

theorem le_center_of_quotConj_eq_one [Group.IsPerfect X] {T : Subgroup X} [T.Normal]
    (hZX : ∀ c ∈ center T, (c : X) ∈ center X) (h1 : ∀ x : X, quotConj T x = 1) :
    T ≤ center X := by
  have hTX : ⁅T, (⊤ : Subgroup X)⁆ ≤ center X := by
    rw [commutator_le]
    intro t ht x _
    have hq := congrArg (fun σ : MulAut (T ⧸ center T) => σ ((⟨t, ht⟩ : T) : T ⧸ center T))
      (h1 x)
    simp only [quotConj_mk, MulAut.one_apply] at hq
    have hc := hZX _ (QuotientGroup.eq.mp hq.symm)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply] at hc
    have he : ⁅t, x⁆ = t * (t⁻¹ * (x * t * x⁻¹))⁻¹ * t⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [he, mem_center_iff.mp (inv_mem hc) t, mul_inv_cancel_right]
    exact inv_mem hc
  have hbot : ⁅⁅T, (⊤ : Subgroup X)⁆, (⊤ : Subgroup X)⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro c hc
    rw [mem_centralizer_iff]
    intro g _
    exact mem_center_iff.mp (hTX hc) g
  have hcomm : ⁅(⊤ : Subgroup X), T⁆ = ⁅T, (⊤ : Subgroup X)⁆ := commutator_comm _ _
  have h3 : ⁅⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆, T⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (by rw [hcomm]; exact hbot) hbot
  rw [← commutator_def, Group.IsPerfect.commutator_eq_top,
    commutator_eq_bot_iff_le_centralizer] at h3
  intro t ht
  rw [mem_center_iff]
  intro g
  exact (mem_centralizer_iff.mp (h3 (mem_top g)) t ht).symm

theorem alt_of_commData [Finite X] [Group.IsPerfect X] {K : Subgroup X} [K.Normal]
    (hK : Group.IsSolvable K) (hs : IsSimpleGroup (X ⧸ K)) {T : Subgroup X} [T.Normal]
    (hTZ : ¬ T ≤ center X) (hZX : ∀ c ∈ center T, (c : X) ∈ center X) {z : T}
    (h : CommData T z) (hcard : Nat.card (T ⧸ center T) = 4 ∨ Nat.card (T ⧸ center T) = 16) :
    Nonempty (X ⧸ K ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (X ⧸ K ≃* alternatingGroup (Fin 6)) := by
  have hne1 : ¬ ∀ x : X, quotConj T x = 1 := fun h1 => hTZ (le_center_of_quotConj_eq_one hZX h1)
  have : IsElementaryAbelian 2 (T ⧸ center T) := isElementaryAbelian_quot h
  rcases hcard with h4 | h16
  ·
    exfalso
    apply hne1
    intro x
    have : Group.IsSolvable (Equiv.Perm (T ⧸ center T)) := Equiv.Perm.isSolvable h4.le
    have h1 := map_eq_one_of_isPerfect ((MulAut.toPerm _).comp (quotConj T)) x
    ext u
    exact congrArg (fun π : Equiv.Perm _ => π u) h1
  ·
    obtain ⟨ε⟩ := h.nonempty_mulEquiv
    obtain ⟨bs, hbs⟩ := exists_basis_antidiag h16 (commB h ε) (commB_mul_left h ε)
      (commB_mul_right h ε) (commB_self h ε) (eq_one_of_commB h ε)
    have hφ : ∀ (γ : X) (u v : T ⧸ center T),
        commB h ε (quotConj T γ u) (quotConj T γ v) = commB h ε u v := fun γ u v => by
      rw [quotConj_apply]
      exact commB_quotAut h ε (conjNormal_eq_of_mem_center (hZX z h.mem_center) γ) u v
    obtain ⟨ψ, hψ⟩ : ∃ ψ : X →* Equiv.Perm (Fin 6), ∀ x, ψ x = omegaPerm
        (sympRep (commB h ε) (commB_mul_left h ε) (commB_mul_right h ε) bs hbs _ hφ x) :=
      ⟨omegaPerm.comp
        (sympRep (commB h ε) (commB_mul_left h ε) (commB_mul_right h ε) bs hbs _ hφ),
        fun _ => rfl⟩
    have hψ1 : ∀ x, ψ x = 1 → quotConj T x = 1 := by
      intro x hx
      rw [hψ] at hx
      have h1 := (map_eq_one_iff omegaPerm omegaPerm_injective).1 hx
      rw [← sympRepGL_eq_one_iff bs]
      exact congrArg Subtype.val h1
    have hne : ψ.range ≠ ⊥ := by
      intro hbot
      apply hne1
      intro x
      apply hψ1
      have hx : ψ x ∈ ψ.range := ⟨x, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hx
    have hperf : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
    have key : ∀ n : ℕ, 5 ≤ n → Nonempty (ψ.range ≃* alternatingGroup (Fin n)) →
        Nonempty (X ⧸ K ≃* alternatingGroup (Fin n)) := by
      rintro n hn ⟨e⟩
      have hsψ : IsSimpleGroup ψ.range := (MulEquiv.isSimpleGroup_congr e).2
        (alternatingGroup.isSimpleGroup (by rwa [Nat.card_eq_fintype_card, Fintype.card_fin]))
      have hsk : IsSimpleGroup (X ⧸ ψ.ker) :=
        (MulEquiv.isSimpleGroup_congr (QuotientGroup.quotientKerEquivRange ψ)).2 hsψ
      exact ⟨(QuotientGroup.quotientMulEquivOfEq (eq_of_simple_quotients hK hs hsk)).trans
        ((QuotientGroup.quotientKerEquivRange ψ).trans e)⟩
    rcases perfect_perm_six hperf hne with hA6 | he5
    · exact Or.inr (key 6 (by norm_num) ⟨MulEquiv.subgroupCongr hA6⟩)
    · exact Or.inl (key 5 le_rfl he5)

end CFSG.LocalAnalysis.UniquenessCase.UC22.K318
