module

public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusRootPair
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Faithful
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Onto
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2LeviProduct

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

theorem adjointGroup_inf_centralizer_rootDiagUnit_eq {M : Type} [Field M] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {c : Fin Tag.F4.rank → Mˣ} (hcp : c ^ p = 1) (hc1 : c ≠ 1)
    (hker : rootCharKernel c = parabolicRoots .F4 {1, 2}) :
    adjointGroup .F4 M ⊓ Subgroup.centralizer {rootDiagUnit .F4 c} =
      torusGroup .F4 M ⊔ subsystemGroup .F4 M {1, 2} := by
  have h1 := toralCentralizer_eq_toralRootGroup_of_le
    (EvenF4QPlus.F4_rootCharStabilizer_le_kernelReflectionGroup hp hp3 hcp hc1)
  rw [toralCentralizer, toralRootGroup, hker, ← subsystemGroup_eq_rootSpan] at h1
  exact h1

section Product

variable {G : Type*} [Group G] {A P D : Subgroup G}
  (hcomm : ∀ a ∈ A, ∀ x ∈ P, a * x = x * a)
  (hprod : ∀ g ∈ D, ∃ a ∈ A, ∃ x ∈ P, g = a * x)
include hcomm hprod

theorem commutator_eq_of_abelian_mul (hA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hPD : P ≤ D) : ⁅D, D⁆ = ⁅P, P⁆ := by
  refine le_antisymm ((Subgroup.commutator_le).2 fun g hg g' hg' => ?_)
    (Subgroup.commutator_mono hPD hPD)
  obtain ⟨a, ha, x, hx, rfl⟩ := hprod g hg
  obtain ⟨a', ha', x', hx', rfl⟩ := hprod g' hg'
  have e : ⁅a * x, a' * x'⁆ = ⁅x, x'⁆ := by
    have hu : x * x' * x⁻¹ ∈ P := mul_mem (mul_mem hx hx') (inv_mem hx)
    have hv : x * x' * x⁻¹ * x'⁻¹ ∈ P := mul_mem hu (inv_mem hx')
    have c1 : x * a' = a' * x := (hcomm a' ha' x hx).symm
    have c2 : (x * x' * x⁻¹) * a⁻¹ = a⁻¹ * (x * x' * x⁻¹) :=
      (hcomm a⁻¹ (inv_mem ha) _ hu).symm
    have c3 : a * a' * a⁻¹ = a' := by rw [hA a ha a' ha', mul_inv_cancel_right]
    have c4 : a' * (x * x' * x⁻¹ * x'⁻¹) * a'⁻¹ = x * x' * x⁻¹ * x'⁻¹ := by
      rw [hcomm a' ha' _ hv, mul_inv_cancel_right]
    calc ⁅a * x, a' * x'⁆ = a * (x * a') * x' * x⁻¹ * a⁻¹ * x'⁻¹ * a'⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = a * (a' * x) * x' * x⁻¹ * a⁻¹ * x'⁻¹ * a'⁻¹ := by rw [c1]
      _ = a * a' * ((x * x' * x⁻¹) * a⁻¹) * x'⁻¹ * a'⁻¹ := by group
      _ = a * a' * (a⁻¹ * (x * x' * x⁻¹)) * x'⁻¹ * a'⁻¹ := by rw [c2]
      _ = (a * a' * a⁻¹) * (x * x' * x⁻¹ * x'⁻¹) * a'⁻¹ := by group
      _ = a' * (x * x' * x⁻¹ * x'⁻¹) * a'⁻¹ := by rw [c3]
      _ = x * x' * x⁻¹ * x'⁻¹ := c4
      _ = ⁅x, x'⁆ := by rw [commutatorElement_def]
  rw [e]
  exact Subgroup.commutator_mem_commutator hx hx'

theorem inf_centralizer_eq_of_abelian_mul {R : Subgroup G} (hAD : A ≤ D) (hRP : R ≤ P)
    (hCR : ∀ x ∈ P, (∀ r ∈ R, r * x = x * r) → x = 1) :
    D ⊓ Subgroup.centralizer (R : Set G) = A := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgD, hgc⟩ := Subgroup.mem_inf.1 hg
    rw [Subgroup.mem_centralizer_iff] at hgc
    obtain ⟨a, ha, x, hx, rfl⟩ := hprod g hgD
    have hx1 : x = 1 := hCR x hx fun r hr => by
      have h := hgc r hr
      have c := hcomm a ha r (hRP hr)
      calc r * x = a⁻¹ * (r * (a * x)) := by rw [← mul_assoc r a, ← c]; group
        _ = a⁻¹ * (a * x * r) := by rw [h]
        _ = x * r := by group
    rw [hx1, mul_one]
    exact ha
  · intro a ha
    refine Subgroup.mem_inf.2 ⟨hAD ha, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    exact (hcomm a ha r (hRP hr)).symm

end Product

section Small

variable {K : Type} [Field K]

theorem center_subsystemGroup_one_two [CharP K 2] :
    Subgroup.center (subsystemGroup Tag.F4 K {1, 2}) = ⊥ :=
  center_subsystemGroup_F4_eq_bot (Or.inl val_image_f4B2Pair)

theorem isSimpleGroup_subsystemGroup_one_two [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    IsSimpleGroup (subsystemGroup Tag.F4 K {1, 2}) ∧
      Group.IsPerfect (subsystemGroup Tag.F4 K {1, 2}) ∧
      ∃ a b : subsystemGroup Tag.F4 K {1, 2}, a * b ≠ b * a := by
  have hdec : ∀ i j k : Fin Tag.F4.rank, (i = 1 ∨ i = 2) → (j = 1 ∨ j = 2) → i ≤ k → k ≤ j →
      k = 1 ∨ k = 2 := by decide
  have hconn : ∀ i ∈ ({1, 2} : Set (Fin Tag.F4.rank)), ∀ j ∈ ({1, 2} : Set (Fin Tag.F4.rank)),
      ∀ k, i ≤ k → k ≤ j → k ∈ ({1, 2} : Set (Fin Tag.F4.rank)) :=
    fun i hi j hj k hik hkj => hdec i j k hi hj hik hkj
  obtain ⟨hperf, -, -, -, h5⟩ := even_F4_connected_standard_root_groups_quasisimple K hK {1, 2}
    ⟨1, Or.inl rfl⟩ hconn
  obtain ⟨-, hsimple, hnab⟩ := h5 (Or.inl val_image_f4B2Pair)
  exact ⟨hsimple, hperf, hnab⟩

theorem nonempty_subsystemGroup_mulEquiv_of_ringEquiv {K' : Type} [Field K'] (e : K ≃+* K')
    (J : Set (Fin Tag.F4.rank)) :
    Nonempty (subsystemGroup Tag.F4 K J ≃* subsystemGroup Tag.F4 K' J) := by
  let φ : subsystemGroup Tag.F4 K J →* subsystemGroup Tag.F4 K' J :=
    { toFun z := ⟨baseChangeGL e.toRingHom z, baseChangeGL_mem_subsystemGroup e.toRingHom z.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' a b := Subtype.ext (map_mul _ _ _) }
  refine ⟨MulEquiv.ofBijective φ ⟨fun a b h => Subtype.ext
    (baseChangeGL_injective e.toRingHom (congrArg Subtype.val h)), fun z => ?_⟩⟩
  refine ⟨⟨baseChangeGL e.symm.toRingHom z, baseChangeGL_mem_subsystemGroup _ z.2⟩,
    Subtype.ext ?_⟩
  change baseChangeGL e.toRingHom (baseChangeGL e.symm.toRingHom (z : ModGL Tag.F4 K')) = z
  rw [baseChangeGL_baseChangeGL, RingEquiv.toRingHom_comp_symm_toRingHom, baseChangeGL_id]

theorem matrixIsometryGroup_f4J0_eq_sympFour :
    matrixIsometryGroup (f4J0 (ZMod 2)) =
      CFSG.ComponentClassification.PresentationLocal.sympFour := by
  have e : f4J0 (ZMod 2) = CFSG.ComponentClassification.PresentationLocal.antidiagGram := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  ext g
  rw [mem_matrixIsometryGroup, e]
  rfl

theorem nonempty_subsystemGroup_one_two_mulEquiv_sympFour [Fintype K]
    (hK : Fintype.card K = 2) :
    Nonempty (subsystemGroup Tag.F4 K {1, 2} ≃*
      CFSG.ComponentClassification.PresentationLocal.sympFour) := by
  obtain ⟨e₁⟩ := nonempty_subsystemGroup_mulEquiv_of_ringEquiv
    (ZMod.ringEquivOfPrime K Nat.prime_two hK).symm {1, 2}
  exact ⟨e₁.trans ((MulEquiv.ofBijective (f4B2Rep (ZMod 2))
    ⟨f4B2Rep_injective, f4B2Rep_surjective⟩).trans
      (MulEquiv.subgroupCongr matrixIsometryGroup_f4J0_eq_sympFour))⟩

end Small

section Transfer

variable {G S : Type*} [Group G] [Group S] {P : Subgroup G}

theorem commutator_eq_map_of_mulEquiv (e : P ≃* S) :
    ⁅P, P⁆ = (commutator S).map (P.subtype.comp e.symm.toMonoidHom) := by
  have h2 : (⊤ : Subgroup S).map (P.subtype.comp e.symm.toMonoidHom) = P := by
    ext x
    constructor
    · rintro ⟨s, -, rfl⟩
      exact (e.symm s).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, trivial, by simp⟩
  rw [_root_.commutator_def, Subgroup.map_commutator, h2]

theorem mem_commutator_iff_of_mulEquiv (e : P ≃* S) (x : P) :
    (x : G) ∈ ⁅P, P⁆ ↔ e x ∈ commutator S := by
  rw [commutator_eq_map_of_mulEquiv e, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, hsx⟩
    have : x = e.symm s := Subtype.ext hsx.symm
    rw [this, MulEquiv.apply_symm_apply]
    exact hs
  · intro hx
    exact ⟨e x, hx, by simp⟩

theorem nonempty_commutator_mulEquiv (e : P ≃* S) :
    Nonempty (↥(⁅P, P⁆ : Subgroup G) ≃* commutator S) := by
  rw [commutator_eq_map_of_mulEquiv e]
  exact ⟨((commutator S).equivMapOfInjective _ (P.subtype_injective.comp
    e.symm.injective)).symm⟩

theorem eq_one_of_commute_commutator_of_mulEquiv (e : P ≃* S)
    (hC : Subgroup.centralizer (commutator S : Set S) = ⊥) {x : G} (hx : x ∈ P)
    (hc : ∀ r ∈ ⁅P, P⁆, r * x = x * r) : x = 1 := by
  have h : e ⟨x, hx⟩ ∈ Subgroup.centralizer (commutator S : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨y, rfl⟩ := e.surjective s
    have hy : (y : G) ∈ ⁅P, P⁆ := (mem_commutator_iff_of_mulEquiv e y).2 hs
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc _ hy)
  rw [hC, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h
  exact congrArg Subtype.val h

end Transfer

section FixedLevi

variable {G : Type*} [Group G]

theorem commutator_le_of_self (P : Subgroup G) : ⁅P, P⁆ ≤ P :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem levi_fixed_group_theory {Z₀ P D R : Subgroup G}
    (hZab : ∀ a ∈ Z₀, ∀ b ∈ Z₀, a * b = b * a) (hcomm : ∀ z ∈ Z₀, ∀ x ∈ P, z * x = x * z)
    (hdisj : Z₀ ⊓ P = ⊥) (hsup : Z₀ ⊔ P = D) (hR : R = ⁅D, D⁆)
    (hZP : ∀ x ∈ P, (∀ x' ∈ P, x' * x = x * x') → x = 1)
    (hCR : ∀ x ∈ P, (∀ r ∈ ⁅P, P⁆, r * x = x * r) → x = 1) :
    (∃ e : Z₀ × P ≃* D, ∀ q, (e q : G) = q.1 * q.2) ∧ (Subgroup.center D).map D.subtype = Z₀ ∧
      R = ⁅P, P⁆ ∧ D ⊓ Subgroup.centralizer (R : Set G) = Z₀ := by
  obtain ⟨e, he⟩ := exists_prod_mulEquiv_of_commute hcomm hdisj hsup
  have hprod : ∀ g ∈ D, ∃ z ∈ Z₀, ∃ x ∈ P, g = z * x := fun g hg =>
    ⟨_, (e.symm ⟨g, hg⟩).1.2, _, (e.symm ⟨g, hg⟩).2.2, by rw [← he, MulEquiv.apply_symm_apply]⟩
  have hZD : Z₀ ≤ D := hsup ▸ le_sup_left
  have hPD : P ≤ D := hsup ▸ le_sup_right
  have hRP : R = ⁅P, P⁆ := hR.trans (commutator_eq_of_abelian_mul hcomm hprod hZab hPD)
  refine ⟨⟨e, he⟩, ?_, hRP, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨z, hz, x, hx, hgzx⟩ := hprod g g.2
      have hx1 : x = 1 := hZP x hx fun x' hx' => by
        have h1 := congrArg Subtype.val ((Subgroup.mem_center_iff.1 hg) ⟨x', hPD hx'⟩)
        simp only [Subgroup.coe_mul] at h1
        rw [hgzx] at h1
        have h2 := hcomm z hz x' hx'
        calc x' * x = z⁻¹ * (x' * (z * x)) := by rw [← mul_assoc x' z, ← h2]; group
          _ = z⁻¹ * (z * x * x') := by rw [h1]
          _ = x * x' := by group
      change (g : G) ∈ Z₀
      rw [hgzx, hx1, mul_one]
      exact hz
    · intro z hz
      refine Subgroup.mem_map.2 ⟨⟨z, hZD hz⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      obtain ⟨z', hz', x, hx, hg⟩ := hprod g g.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hg]
      have h1 := hZab z' hz' z hz
      have h2 := hcomm z hz x hx
      calc z' * x * z = z' * (x * z) := mul_assoc _ _ _
        _ = z * (z' * x) := by rw [← h2, ← mul_assoc, h1, mul_assoc]
  · rw [hRP]
    exact inf_centralizer_eq_of_abelian_mul hcomm hprod hZD (commutator_le_of_self P) hCR

theorem simple_factor_facts {S : Type*} [Group S] [IsSimpleGroup S] (hperf : Group.IsPerfect S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {P : Subgroup G} (e : P ≃* S) :
    ⁅P, P⁆ = P ∧ (∀ x ∈ P, (∀ x' ∈ P, x' * x = x * x') → x = 1) ∧
      (∀ x ∈ P, (∀ r ∈ ⁅P, P⁆, r * x = x * r) → x = 1) ∧ IsSimpleGroup P ∧
      Group.IsPerfect P ∧ ∃ a b : P, a * b ≠ b * a := by
  have hcomm : ⁅P, P⁆ = P := by
    rw [commutator_eq_map_of_mulEquiv e, Group.isPerfect_def.1 hperf]
    ext x
    constructor
    · rintro ⟨s, -, rfl⟩
      exact (e.symm s).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, trivial, by simp⟩
  have hZ : Subgroup.center S = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have hZP : ∀ x ∈ P, (∀ x' ∈ P, x' * x = x * x') → x = 1 := by
    intro x hx hc
    have h : e ⟨x, hx⟩ ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨y, rfl⟩ := e.surjective s
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc _ y.2)
    rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h
    exact congrArg Subtype.val h
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨hcomm, hZP, fun x hx hc => hZP x hx fun x' hx' => hc x' (hcomm.symm ▸ hx'),
    (MulEquiv.isSimpleGroup_congr e).2 inferInstance,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective,
    e.symm a, e.symm b, fun h => hab (by rw [← map_mul, ← map_mul] at h; exact e.symm.injective h)⟩

end FixedLevi

end CFSG.RankThree.Chevalley
