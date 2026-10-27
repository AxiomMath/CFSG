module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartOne.S12.LinAlg

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G]

theorem isEA_of_le {S A : Subgroup G} (hS : IsElementaryAbelian 2 S) (hA : A ≤ S) :
    IsElementaryAbelian 2 A := by
  have hcm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : S) ⟨y, hy⟩)
  have hsq : ∀ x ∈ S, x ^ 2 = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := S) x hx
  refine
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hcm _ (hA a.2) _ (hA b.2))⟩⟩
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => Subtype.ext ?_
  simpa using hsq _ (hA a.2)

theorem coord_exists [Finite G] {S A B C : Subgroup G} (hS : IsElemAb 2 6 S) (hA : A ≤ S)
    (hB : B ≤ S) (hC : C ≤ S) (cA : Nat.card A = 4) (cB : Nat.card B = 4) (cC : Nat.card C = 4)
    (hjoin : A ⊔ B ⊔ C = S) :
    ∃ E : ↥S ≃* Multiplicative (Fin 3 → Fin 2 → ZMod 2),
      (∀ x : ↥S, Multiplicative.toAdd (E x) 0 = 0 ↔ (x : G) ∈ B ⊔ C) ∧
      (∀ x : ↥S, Multiplicative.toAdd (E x) 1 = 0 ↔ (x : G) ∈ A ⊔ C) ∧
      (∀ x : ↥S, Multiplicative.toAdd (E x) 2 = 0 ↔ (x : G) ∈ A ⊔ B) := by
  obtain ⟨hEA, hS64⟩ := hS
  haveI := hEA
  haveI : IsElementaryAbelian 2 A := isEA_of_le hEA hA
  haveI : IsElementaryAbelian 2 B := isEA_of_le hEA hB
  haveI : IsElementaryAbelian 2 C := isEA_of_le hEA hC
  obtain ⟨fA⟩ := CFSG.RankThree.PartOne.LinAlg.exists_coords (p := 2) A (n := 2)
    (by rw [cA]; norm_num)
  obtain ⟨fB⟩ := CFSG.RankThree.PartOne.LinAlg.exists_coords (p := 2) B (n := 2)
    (by rw [cB]; norm_num)
  obtain ⟨fC⟩ := CFSG.RankThree.PartOne.LinAlg.exists_coords (p := 2) C (n := 2)
    (by rw [cC]; norm_num)
  letI : CommGroup ↥S :=
    { (inferInstance : Group ↥S) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  let proj : Fin 3 → (Multiplicative (Fin 3 → Fin 2 → ZMod 2) →* Multiplicative (Fin 2 → ZMod 2)) :=
    fun i => AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 3 => Fin 2 → ZMod 2) i)
  let F : Multiplicative (Fin 3 → Fin 2 → ZMod 2) →* ↥S :=
    ((Subgroup.inclusion hA).comp (fA.toMonoidHom.comp (proj 0))) *
      ((Subgroup.inclusion hB).comp (fB.toMonoidHom.comp (proj 1))) *
      ((Subgroup.inclusion hC).comp (fC.toMonoidHom.comp (proj 2)))
  have hF : ∀ v, (F v : G) = (fA (proj 0 v) : G) * (fB (proj 1 v) : G) * (fC (proj 2 v) : G) :=
    fun v => rfl
  have hproj : ∀ (i : Fin 3) v, proj i v = Multiplicative.ofAdd (Multiplicative.toAdd v i) :=
    fun i v => rfl
  let ι : Fin 3 → (Multiplicative (Fin 2 → ZMod 2) →* Multiplicative (Fin 3 → Fin 2 → ZMod 2)) :=
    fun i => AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ : Fin 3 => Fin 2 → ZMod 2) i)
  have hι : ∀ (i j : Fin 3) y, proj j (ι i y) =
      if i = j then y else 1 := by
    intro i j y
    by_cases hij : i = j
    · subst hij
      simp [hproj, ι]
    · simp only [hij, if_false]
      rw [hproj]
      have : Multiplicative.toAdd (ι i y) j = 0 := by
        simp [ι, AddMonoidHom.single_apply, Pi.single_apply, Ne.symm hij]
      simp [this]
  have hFA : ∀ y, F (ι 0 y) = Subgroup.inclusion hA (fA y) := by
    intro y
    apply Subtype.ext
    rw [hF]
    simp [hι]
  have hFB : ∀ y, F (ι 1 y) = Subgroup.inclusion hB (fB y) := by
    intro y
    apply Subtype.ext
    rw [hF]
    simp [hι]
  have hFC : ∀ y, F (ι 2 y) = Subgroup.inclusion hC (fC y) := by
    intro y
    apply Subtype.ext
    rw [hF]
    simp [hι]
  have hsurj : Function.Surjective F := by
    have hAle : A ≤ F.range.map S.subtype := by
      intro a ha
      obtain ⟨y, hy⟩ := fA.surjective ⟨a, ha⟩
      exact ⟨Subgroup.inclusion hA ⟨a, ha⟩, ⟨ι 0 y, by rw [hFA, hy]⟩, rfl⟩
    have hBle : B ≤ F.range.map S.subtype := by
      intro a ha
      obtain ⟨y, hy⟩ := fB.surjective ⟨a, ha⟩
      exact ⟨Subgroup.inclusion hB ⟨a, ha⟩, ⟨ι 1 y, by rw [hFB, hy]⟩, rfl⟩
    have hCle : C ≤ F.range.map S.subtype := by
      intro a ha
      obtain ⟨y, hy⟩ := fC.surjective ⟨a, ha⟩
      exact ⟨Subgroup.inclusion hC ⟨a, ha⟩, ⟨ι 2 y, by rw [hFC, hy]⟩, rfl⟩
    intro x
    have hx : (x : G) ∈ F.range.map S.subtype := by
      have : (x : G) ∈ A ⊔ B ⊔ C := by rw [hjoin]; exact x.2
      exact (sup_le (sup_le hAle hBle) hCle) this
    obtain ⟨z, ⟨v, hv⟩, hzx⟩ := hx
    refine ⟨v, ?_⟩
    rw [hv]
    exact Subtype.ext hzx
  have hcard : Nat.card (Multiplicative (Fin 3 → Fin 2 → ZMod 2)) = Nat.card ↥S := by
    rw [hS64]
    simp [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card]
  have hbij : Function.Bijective F := hsurj.bijective_of_nat_card_le hcard.le
  let E : ↥S ≃* Multiplicative (Fin 3 → Fin 2 → ZMod 2) := (MulEquiv.ofBijective F hbij).symm
  have hEF : ∀ v, E (F v) = v := fun v => (MulEquiv.ofBijective F hbij).symm_apply_apply v
  have hFE : ∀ x, F (E x) = x := fun x => (MulEquiv.ofBijective F hbij).apply_symm_apply x
  have hEA' : ∀ y, E (Subgroup.inclusion hA (fA y)) = ι 0 y := fun y => by
    rw [← hFA, hEF]
  have hEB' : ∀ y, E (Subgroup.inclusion hB (fB y)) = ι 1 y := fun y => by
    rw [← hFB, hEF]
  have hEC' : ∀ y, E (Subgroup.inclusion hC (fC y)) = ι 2 y := fun y => by
    rw [← hFC, hEF]
  have hιz : ∀ (i j : Fin 3) y, i ≠ j → Multiplicative.toAdd (ι i y) j = 0 := by
    intro i j y hij
    simp [ι, AddMonoidHom.single_apply, Pi.single_apply, Ne.symm hij]
  have hmem1 : ∀ x : ↥S, (x : G) = (fA (proj 0 (E x)) : G) * (fB (proj 1 (E x)) : G) *
      (fC (proj 2 (E x)) : G) := fun x => by rw [← hF, hFE]
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro h0
      have h1 := hmem1 x
      have h2 : proj 0 (E x) = 1 := by rw [hproj, h0]; rfl
      rw [h2, map_one] at h1
      simp only [OneMemClass.coe_one, one_mul] at h1
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (fB _).2) (Subgroup.mem_sup_right (fC _).2)
    · intro hx
      let T0 : Subgroup G := ((proj 0).ker.map F).map S.subtype
      have hBle : B ≤ T0 := by
        intro a ha
        obtain ⟨y, hy⟩ := fB.surjective ⟨a, ha⟩
        refine ⟨Subgroup.inclusion hB ⟨a, ha⟩, ⟨ι 1 y, ?_, ?_⟩, rfl⟩
        · show proj 0 (ι 1 y) = 1
          rw [hι]; simp
        · rw [hFB, hy]
      have hCle : C ≤ T0 := by
        intro a ha
        obtain ⟨y, hy⟩ := fC.surjective ⟨a, ha⟩
        refine ⟨Subgroup.inclusion hC ⟨a, ha⟩, ⟨ι 2 y, ?_, ?_⟩, rfl⟩
        · show proj 0 (ι 2 y) = 1
          rw [hι]; simp
        · rw [hFC, hy]
      obtain ⟨z, ⟨v, hv, hvz⟩, hzx⟩ := (sup_le hBle hCle) hx
      have hzx' : z = x := Subtype.ext hzx
      have : E x = v := by rw [← hzx', ← hvz, hEF]
      rw [this]
      have := MonoidHom.mem_ker.1 hv
      rw [hproj] at this
      exact Multiplicative.ofAdd.injective this
  · intro x
    constructor
    · intro h0
      have h1 := hmem1 x
      have h2 : proj 1 (E x) = 1 := by rw [hproj, h0]; rfl
      rw [h2, map_one] at h1
      simp only [OneMemClass.coe_one, mul_one] at h1
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (fA _).2) (Subgroup.mem_sup_right (fC _).2)
    · intro hx
      let T0 : Subgroup G := ((proj 1).ker.map F).map S.subtype
      have hAle : A ≤ T0 := by
        intro a ha
        obtain ⟨y, hy⟩ := fA.surjective ⟨a, ha⟩
        refine ⟨Subgroup.inclusion hA ⟨a, ha⟩, ⟨ι 0 y, ?_, ?_⟩, rfl⟩
        · show proj 1 (ι 0 y) = 1
          rw [hι]; simp
        · rw [hFA, hy]
      have hCle : C ≤ T0 := by
        intro a ha
        obtain ⟨y, hy⟩ := fC.surjective ⟨a, ha⟩
        refine ⟨Subgroup.inclusion hC ⟨a, ha⟩, ⟨ι 2 y, ?_, ?_⟩, rfl⟩
        · show proj 1 (ι 2 y) = 1
          rw [hι]; simp
        · rw [hFC, hy]
      obtain ⟨z, ⟨v, hv, hvz⟩, hzx⟩ := (sup_le hAle hCle) hx
      have hzx' : z = x := Subtype.ext hzx
      have : E x = v := by rw [← hzx', ← hvz, hEF]
      rw [this]
      have := MonoidHom.mem_ker.1 hv
      rw [hproj] at this
      exact Multiplicative.ofAdd.injective this
  · intro x
    constructor
    · intro h0
      have h1 := hmem1 x
      have h2 : proj 2 (E x) = 1 := by rw [hproj, h0]; rfl
      rw [h2, map_one] at h1
      simp only [OneMemClass.coe_one, mul_one] at h1
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (fA _).2) (Subgroup.mem_sup_right (fB _).2)
    · intro hx
      let T0 : Subgroup G := ((proj 2).ker.map F).map S.subtype
      have hAle : A ≤ T0 := by
        intro a ha
        obtain ⟨y, hy⟩ := fA.surjective ⟨a, ha⟩
        refine ⟨Subgroup.inclusion hA ⟨a, ha⟩, ⟨ι 0 y, ?_, ?_⟩, rfl⟩
        · show proj 2 (ι 0 y) = 1
          rw [hι]; simp
        · rw [hFA, hy]
      have hBle : B ≤ T0 := by
        intro a ha
        obtain ⟨y, hy⟩ := fB.surjective ⟨a, ha⟩
        refine ⟨Subgroup.inclusion hB ⟨a, ha⟩, ⟨ι 1 y, ?_, ?_⟩, rfl⟩
        · show proj 2 (ι 1 y) = 1
          rw [hι]; simp
        · rw [hFB, hy]
      obtain ⟨z, ⟨v, hv, hvz⟩, hzx⟩ := (sup_le hAle hBle) hx
      have hzx' : z = x := Subtype.ext hzx
      have : E x = v := by rw [← hzx', ← hvz, hEF]
      rw [this]
      have := MonoidHom.mem_ker.1 hv
      rw [hproj] at this
      exact Multiplicative.ofAdd.injective this

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
