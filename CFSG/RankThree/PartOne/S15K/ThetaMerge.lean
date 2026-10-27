module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.RankThree.PartOne.S12.InputsCT
import CFSG.GroupTheory.LocalCores.Components
import CFSG.RankThree.PartOne.CTP.PhanBridge

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped commutatorElement

theorem commutator_mem_solvableCore {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {L₁ L₂ : Subgroup H} (h₁ : L₁ ∈ thetaComponents p H) (h₂ : L₂ ∈ thetaComponents p H)
    (hne : L₁ ≠ L₂) {x y : H} (hx : x ∈ L₁) (hy : y ∈ L₂) :
    ⁅x, y⁆ ∈ aschbacherSolvableCore p H := by
  set N := aschbacherSolvableCore p H with hN
  have hchar : N.Characteristic := (solvable_prime_complement_core_characterization hp).2.1
  have hNn : N.Normal := inferInstance
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) hp
  have hK₁ := isComponent_map_of_mem_thetaComponents hp h₁
  have hK₂ := isComponent_map_of_mem_thetaComponents hp h₂
  have hKne : L₁.map (QuotientGroup.mk' N) ≠ L₂.map (QuotientGroup.mk' N) := fun h =>
    hne (hbij.injOn h₁ h₂ h)
  have hcomm := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  have h1 : ⁅QuotientGroup.mk' N x, QuotientGroup.mk' N y⁆ ∈
      ⁅L₁.map (QuotientGroup.mk' N), L₂.map (QuotientGroup.mk' N)⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hx)
      (Subgroup.mem_map_of_mem _ hy)
  rw [hcomm, Subgroup.mem_bot] at h1
  rw [← map_commutatorElement] at h1
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem le_center_of_solvable_normal {Q : Type*} [Group Q]
    (hQ : IsSimpleGroup (Q ⧸ Subgroup.center Q)) {R : Subgroup Q} (hR : Group.IsPerfect ↥R)
    (hRne : R ≠ ⊥) (W : Subgroup Q) [W.Normal] (hW : Group.IsSolvable ↥W) :
    W ≤ Subgroup.center Q := by
  by_contra hcon
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hmapn : (W.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hQ.eq_bot_or_eq_top_of_normal (W.map π) with h | h
  · apply hcon
    intro w hw
    have : π w ∈ W.map π := Subgroup.mem_map_of_mem π hw
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  · have hsurj : Function.Surjective (π.comp W.subtype) := by
      intro y
      have : y ∈ W.map π := by rw [h]; trivial
      obtain ⟨w, hw, rfl⟩ := this
      exact ⟨⟨w, hw⟩, rfl⟩
    have hsolQ : Group.IsSolvable (Q ⧸ Subgroup.center Q) := Group.isSolvable_of_surjective hsurj
    have hsolQ' : Group.IsSolvable Q :=
      Group.isSolvable_of_ker_le_range (Subgroup.center Q).subtype π (by
        rw [hπ, QuotientGroup.ker_mk', Subgroup.range_subtype])
    have hsolR : Group.IsSolvable ↥R := inferInstance
    have hnt : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).2 hRne
    exact Group.IsPerfect.not_isSolvable ↥R hsolR

theorem eq_or_commute_of_thetaComponents_of_simple {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {L₁ L₂ : Subgroup H} (h₁ : L₁ ∈ thetaComponents p H)
    (h₂ : L₂ ∈ thetaComponents p H) {X Y : Subgroup H} (hX : X ≤ L₁) (hY : Y ≤ L₂)
    (hperf : Group.IsPerfect ↥X) (hXne : X ≠ ⊥)
    (hsimple : IsSimpleGroup (↥(X ⊔ Y) ⧸ Subgroup.center ↥(X ⊔ Y))) :
    L₁ = L₂ ∨ ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  classical
  by_cases heq : L₁ = L₂
  · exact Or.inl heq
  refine Or.inr fun x hx y hy => ?_
  set J : Subgroup H := X ⊔ Y with hJ
  set N := aschbacherSolvableCore p H with hN
  have hchar : N.Characteristic := (solvable_prime_complement_core_characterization hp).2.1
  have hNn : N.Normal := inferInstance
  have hNsol : Group.IsSolvable ↥N := (solvable_prime_complement_core_characterization hp).1
  have hXJ : X ≤ J := le_sup_left
  have hYJ : Y ≤ J := le_sup_right
  set W : Subgroup ↥J := (N ⊓ J).subgroupOf J with hW
  have hWn : W.Normal := by
    refine ⟨fun w hw g => ?_⟩
    have hw' : (w : H) ∈ N := (Subgroup.mem_subgroupOf.1 hw).1
    refine Subgroup.mem_subgroupOf.2 ⟨?_, (g * w * g⁻¹).2⟩
    have := hNn.conj_mem _ hw' (g : H)
    simpa using this
  have hWsol : Group.IsSolvable ↥W := by
    let g : ↥W →* ↥N :=
      { toFun := fun w => ⟨(w : H), (Subgroup.mem_subgroupOf.1 w.2).1⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective g := fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥N => (z : H)) hab))
    exact Group.isSolvable_of_isSolvable_injective hinj
  have hRperf : Group.IsPerfect ↥(X.subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hXJ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hXJ).symm.surjective
  have hRne : X.subgroupOf J ≠ ⊥ := by
    intro h
    apply hXne
    rw [eq_bot_iff]
    intro z hz
    have : (⟨z, hXJ hz⟩ : ↥J) ∈ X.subgroupOf J := Subgroup.mem_subgroupOf.2 hz
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hWc : W ≤ Subgroup.center ↥J := le_center_of_solvable_normal hsimple hRperf hRne W hWsol
  have hmemJ : ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ J := by
    intro x hx y hy
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem (hXJ hx) (hYJ hy)) (J.inv_mem (hXJ hx)))
      (J.inv_mem (hYJ hy))
  have hcentral : ∀ x ∈ X, ∀ y ∈ Y, ∀ j ∈ J, ⁅x, y⁆ * j = j * ⁅x, y⁆ := by
    intro x hx y hy j hj
    have hxy : ⁅x, y⁆ ∈ N := commutator_mem_solvableCore hp h₁ h₂ heq (hX hx) (hY hy)
    have hmem : (⟨⁅x, y⁆, hmemJ x hx y hy⟩ : ↥J) ∈ W := Subgroup.mem_subgroupOf.2 ⟨hxy, hmemJ x hx y hy⟩
    have := Subgroup.mem_center_iff.1 (hWc hmem) ⟨j, hj⟩
    exact (congrArg Subtype.val this).symm
  have hX1 : ∀ y ∈ Y, ∀ x : ↥X, ⁅(x : H), y⁆ = 1 := by
    intro y hy
    let φ : ↥X →* H :=
      { toFun := fun a => ⁅(a : H), y⁆
        map_one' := by simp
        map_mul' := fun a b => by
          have hcb := hcentral (b : H) b.2 y hy (a : H) (hXJ a.2)
          have hca := hcentral (a : H) a.2 y hy ⁅(b : H), y⁆ (hmemJ _ b.2 y hy)
          have e1 : ⁅((a * b : ↥X) : H), y⁆ = ((a : H) * ⁅(b : H), y⁆ * (a : H)⁻¹) * ⁅(a : H), y⁆ := by
            simp only [Subgroup.coe_mul, commutatorElement_def]
            group
          have e2 : (a : H) * ⁅(b : H), y⁆ * (a : H)⁻¹ = ⁅(b : H), y⁆ := by
            rw [← hcb, mul_inv_cancel_right]
          show ⁅((a * b : ↥X) : H), y⁆ = ⁅(a : H), y⁆ * ⁅(b : H), y⁆
          rw [e1, e2]
          exact hca.symm }
    have : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
    have hcomm : IsMulCommutative ↥φ.range := by
      refine ⟨⟨fun u v => ?_⟩⟩
      obtain ⟨_, ⟨a, rfl⟩⟩ := u
      obtain ⟨_, ⟨b, rfl⟩⟩ := v
      exact Subtype.ext (hcentral (a : H) a.2 y hy ⁅(b : H), y⁆ (hmemJ _ b.2 y hy))
    intro a
    have hsub : Subsingleton ↥φ.range := inferInstance
    have h1 : (⟨φ a, ⟨a, rfl⟩⟩ : ↥φ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  exact commutatorElement_eq_one_iff_mul_comm.1 (hX1 y hy ⟨x, hx⟩)

theorem isSimple_quotient_center_of_centrallyUThree {f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X]
    (hX : CentrallyUThree f X) : IsSimpleGroup (X ⧸ Subgroup.center X) := by
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  obtain ⟨θ₀, hθ, hker⟩ := CTP.exists_su3_surj_of_centrallyUThree hK hX
  have hmodel := CTP.statedClassicalModel_psu_of_surjective hK hq (le_refl 3) θ₀ hθ hker
  exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 f hmodel).2

theorem eq_or_commute_of_thetaComponents {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {L₁ L₂ : Subgroup H} (h₁ : L₁ ∈ thetaComponents p H) (h₂ : L₂ ∈ thetaComponents p H)
    {X Y : Subgroup H} (hX : X ≤ L₁) (hY : Y ≤ L₂) (hperf : Group.IsPerfect ↥X) (hXne : X ≠ ⊥)
    {f : ℕ} (hf : 2 ≤ f) (hU : CentrallyUThree f ↥(X ⊔ Y)) :
    L₁ = L₂ ∨ ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x :=
  eq_or_commute_of_thetaComponents_of_simple hp h₁ h₂ hX hY hperf hXne
    (isSimple_quotient_center_of_centrallyUThree hf hU)

end CFSG.RankThree.PartOne.S15K
