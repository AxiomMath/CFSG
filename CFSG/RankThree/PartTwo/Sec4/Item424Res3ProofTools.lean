module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofSylow
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofGroup
import CFSG.RankThree.PartTwo.Sec16.KS16ProofGTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item424Res3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem false_of_isType424_pair {X : Type} [Group X] [Finite X] (hT : Sec11.IsType424 X)
    (hQ : IsQuasisimple X) {x y : X} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hx1 : x ≠ 1)
    (hcx : Commute ⁅x, y⁆ x) (hcy : Commute ⁅x, y⁆ y) (hyx : y ∉ Subgroup.zpowers x) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube := Sec16.KS1622GTwoProof.pow_three_eq_one_of_mem_closure hx3 hy3 hcx hcy
  have hP : IsPGroup 3 (Subgroup.closure ({x, y} : Set X)) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hcube g g.2)⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hSc : IsCyclic S := Sec11.KS11LieProof.isCyclic_sylow_three_of_isType424 hT hQ S
  have hxS : x ∈ S := hS (Subgroup.subset_closure (by simp))
  have hyS : y ∈ S := hS (Subgroup.subset_closure (by simp))
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyx (Subgroup.one_mem _)
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hzS : Subgroup.zpowers (⟨x, hxS⟩ : S) = Subgroup.zpowers ⟨y, hyS⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hox, hoy]
  have hyx' : (⟨y, hyS⟩ : S) ∈ Subgroup.zpowers ⟨x, hxS⟩ := by
    rw [hzS]
    exact Subgroup.mem_zpowers _
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hyx'
  exact hyx (Subgroup.mem_zpowers_iff.mpr ⟨i, by simpa using congrArg Subtype.val hi⟩)

theorem false_of_isType424_map_pair {Y : Type*} [Group Y] {X : Type} [Group X] [Finite X]
    (hT : Sec11.IsType424 X) (hQ : IsQuasisimple X) (ψ : Y →* X)
    (hker : ψ.ker ≤ Subgroup.center Y) {x y : Y} (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1)
    (hcx : Commute ⁅x, y⁆ x) (hcy : Commute ⁅x, y⁆ y) (hx : x ∉ Subgroup.center Y)
    (hyx : ∀ k : ℤ, y * (x ^ k)⁻¹ ∉ Subgroup.center Y) : False := by
  refine false_of_isType424_pair hT hQ (x := ψ x) (y := ψ y) (by rw [← map_pow, hx3, map_one])
    (by rw [← map_pow, hy3, map_one]) (fun h => hx (hker h)) ?_ ?_ ?_
  · rw [← map_commutatorElement]
    exact hcx.map ψ
  · rw [← map_commutatorElement]
    exact hcy.map ψ
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hyx k
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hk, mul_inv_cancel]

theorem congr_inv_conj {P : Type*} [Group P] (d φ : MulAut P) :
    MulAut.congr d⁻¹ (d * φ * d⁻¹) = φ := by
  ext x
  simp [MulAut.congr_apply, MulAut.mul_apply, MulAut.inv_def]

theorem hasType424_fixSub_of_conj {P : Type} [Group P] [Finite P] {d φ : MulAut P}
    (h : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (d * φ * d⁻¹))) :
    Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub φ) := by
  have h' := h.of_mulEquiv (Sec11.KS11Lie2Proof.fixSubCongr d⁻¹ (d * φ * d⁻¹))
  rwa [congr_inv_conj] at h'

theorem isType424_of_hasType424 {Γ : Type} [Group Γ] [Finite Γ] (N : Subgroup Γ)
    (hN : IsQuasisimple N) (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ N)
    (h : Sec11.KS11Lie2Proof.HasType424 Γ) :
    Sec11.IsType424 (N ⧸ aschbacherSolvableCore 3 N) ∧
      IsQuasisimple (N ⧸ aschbacherSolvableCore 3 N) := by
  obtain ⟨J, ⟨hJp, hJsn, hJq⟩, hT⟩ := h
  have hJN : J ≤ N := by
    have h1 : ⁅J, J⁆ = J := Subgroup.commutator_eq_self
    rw [← h1, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    exact hcomm a b
  have hsn : (J.subgroupOf N).IsSubnormal := hJsn.comap N.subtype
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hN hsn with
    htop | hcen
  · have hNJ : N ≤ J := fun y hy => by
      have : (⟨y, hy⟩ : N) ∈ J.subgroupOf N := htop ▸ Subgroup.mem_top _
      exact this
    obtain rfl : J = N := le_antisymm hJN hNJ
    exact ⟨hT, hJq⟩
  · exfalso
    have hJp' : Group.IsPerfect (J.subgroupOf N) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJN).symm.toMonoidHom)
        (MulEquiv.surjective _)
    have hbot := Sec11.KS11Lie4Proof.eq_bot_of_isPerfect_of_le_center hJp' hcen
    have hall : ∀ w : J, w = 1 := fun w => by
      have hw : (⟨w, hJN w.2⟩ : N) ∈ J.subgroupOf N := w.2
      rw [hbot, Subgroup.mem_bot] at hw
      exact Subtype.ext (by simpa using congrArg Subtype.val hw)
    obtain ⟨u, v, huv⟩ := (CFSG.LocalCores.isQuasisimple_nontrivial hJq).exists_pair_ne
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    rw [hall u', hall v'] at huv
    exact huv rfl

theorem aschbacherSolvableCore_le_center_of_isQuasisimple {N : Type*} [Group N] [Finite N]
    (hN : IsQuasisimple N) : aschbacherSolvableCore 3 N ≤ Subgroup.center N := by
  obtain ⟨hθs, -⟩ := solvable_prime_complement_core_characterization (H := N) Nat.prime_three
  have hsn : (aschbacherSolvableCore 3 N).IsSubnormal :=
    Subgroup.Normal.isSubnormal inferInstance
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hN hsn with h | h
  · exfalso
    have h2 : Group.IsSolvable ↥(⊤ : Subgroup N) := by rw [← h]; exact hθs
    have h3 : Group.IsSolvable N :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup N) ≃* N).toMonoidHom)
        (Subgroup.topEquiv : ↥(⊤ : Subgroup N) ≃* N).surjective
    have : Nontrivial N := CFSG.LocalCores.isQuasisimple_nontrivial hN
    have : Group.IsPerfect N := hN.1
    exact Group.IsPerfect.not_isSolvable N h3
  · exact h

theorem ker_le_center_of_comp {Y N : Type*} [Group Y] [Group N] [Finite N] (hY : IsQuasisimple Y)
    (ρ : Y →* N) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ Subgroup.center Y) :
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 N)).comp ρ).ker ≤ Subgroup.center Y := by
  have hN : IsQuasisimple N := CFSG.LocalCores.isQuasisimple_of_surjective hY ρ hρ hker
  intro y hy
  rw [← CFSG.LocalCores.comap_center_eq_of_perfect hY.1 ρ hρ hker]
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hy
  exact aschbacherSolvableCore_le_center_of_isQuasisimple hN hy

end CFSG.RankThree.PartTwo.Sec4.Item424Res3
