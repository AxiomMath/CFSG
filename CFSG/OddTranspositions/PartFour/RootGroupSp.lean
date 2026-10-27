module

public import CFSG.OddTranspositions.PartFour.SpPlaneSL2
import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSpElt
import CFSG.RankThree.GF2n.Stroth80.Sec83SpA2
import CFSG.OddTranspositions.PartFour.Fourteen.TableSp

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
open CFSG.LocalAnalysis.WeakClosure81

section Model

variable {k : ℕ} {F : Type} [Field F]

private theorem rootGroupSp_Vmem_subset {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c : F}
    (hc : c ≠ 0) :
    Vmem {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection a c) ⊆
      {x | ∃ μ : F, μ ≠ 0 ∧ x = spTransvection (μ • a) c} := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  intro x hx
  obtain ⟨hxS, hxperp⟩ := mem_Vmem.mp hx
  obtain ⟨b, hb, rfl⟩ := hxS
  by_contra hcon
  have hb' : ∀ s : F, b ≠ s • a := by
    intro s
    by_cases hs : s = 0
    · rw [hs, zero_smul]
      exact hb
    · intro hbs
      exact hcon ⟨s, hs, by rw [hbs]⟩
  obtain ⟨y, hya, hyb⟩ :=
    CFSG.ClassicalGroups.Symplectic.a2_exists_form_apply_ne_zero
      (B := spForm k F) spForm_isAlt spForm_nondegenerate ha hb'
  have hy0 : y ≠ 0 := fun h => hyb (by rw [h, map_zero])
  have hza : spTransvection y c ∈ perpMem S (spTransvection a c) := by
    refine mem_perpMem.mpr ⟨⟨y, hy0, rfl⟩, (commute_spTransvection_iff hc hc).mpr ?_⟩
    have h := spForm_isAlt.neg_eq a y
    rw [hya, neg_zero] at h
    exact h.symm
  have hzb : spTransvection y c ∈ perpMem S (spTransvection b c) := by
    rw [hxperp]
    exact hza
  have hform : spForm k F y b = 0 :=
    (commute_spTransvection_iff hc hc).mp (mem_perpMem.mp hzb).2
  have hz0 : spForm k F b y = 0 := by
    have h := spForm_isAlt.neg_eq b y
    rw [hform] at h
    exact neg_eq_zero.mp h
  exact hyb hz0

private theorem rootGroupSp_Vmem_supset {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c : F}
    (hc : c ≠ 0) :
    {x | ∃ μ : F, μ ≠ 0 ∧ x = spTransvection (μ • a) c} ⊆
      Vmem {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection a c) := by
  rintro x ⟨μ, hμ, rfl⟩
  refine mem_Vmem.mpr ⟨⟨μ • a, smul_ne_zero hμ ha, rfl⟩, ?_⟩
  ext y
  rw [mem_perpMem, mem_perpMem]
  exact ⟨fun h => ⟨h.1, (commute_spTransvection_smul_iff y a hμ hc).mp h.2⟩,
    fun h => ⟨h.1, (commute_spTransvection_smul_iff y a hμ hc).mpr h.2⟩⟩

private theorem rootGroupSp_Vmem_eq {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0) :
    Vmem {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
        (spTransvection a c) =
      {x | ∃ μ : F, μ ≠ 0 ∧ x = spTransvection (μ • a) c} :=
  Set.Subset.antisymm (rootGroupSp_Vmem_subset ha hc) (rootGroupSp_Vmem_supset ha hc)

private theorem rootGroupSp_mul_mem_insert_one [CharP F 2]
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0)
    {x y : ↥(StatedSp k F)}
    (hx : x ∈ insert 1 (Vmem {z : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ z = spTransvection b c}
      (spTransvection a c)))
    (hy : y ∈ insert 1 (Vmem {z : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ z = spTransvection b c}
      (spTransvection a c))) :
    x * y ∈ insert 1 (Vmem {z : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ z = spTransvection b c}
      (spTransvection a c)) := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  have hV : Vmem S (spTransvection a c) =
      {x | ∃ μ : F, μ ≠ 0 ∧ x = spTransvection (μ • a) c} := rootGroupSp_Vmem_eq ha hc
  rw [hV] at hx hy ⊢
  obtain rfl | ⟨μ, hμ, rfl⟩ := hx
  · rw [one_mul]
    exact hy
  obtain rfl | ⟨ν, hν, rfl⟩ := hy
  · rw [mul_one, Set.mem_insert_iff]
    right
    exact ⟨μ, hμ, rfl⟩
  have hprod : spTransvection (μ • a) c * spTransvection (ν • a) c =
      spTransvection a ((μ * μ + ν * ν) * c) := by
    rw [CFSG.RankThree.PartOne.CTP.spTransvection_smul,
      CFSG.RankThree.PartOne.CTP.spTransvection_smul,
      CFSG.LocalAnalysis.WeakClosure81.spConf_transvection_mul]
    congr 1
    ring
  have hsq : (μ + ν) * (μ + ν) = μ * μ + ν * ν := by
    linear_combination (μ * ν) * (CharTwo.two_eq_zero : (2 : F) = 0)
  by_cases hd : μ + ν = 0
  · left
    rw [hprod, ← hsq, hd]
    simp [CFSG.LocalAnalysis.WeakClosure81.borel86_spn_spTransvection_param_zero]
  · right
    refine ⟨μ + ν, hd, ?_⟩
    rw [hprod, ← hsq, ← CFSG.RankThree.PartOne.CTP.spTransvection_smul (μ + ν) a c]

private theorem rootGroupSp_inv_mem_insert_one [CharP F 2]
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0) {x : ↥(StatedSp k F)}
    (hx : x ∈ insert 1 (Vmem {z : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ z = spTransvection b c}
      (spTransvection a c))) :
    x⁻¹ ∈ insert 1 (Vmem {z : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ z = spTransvection b c}
      (spTransvection a c)) := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  have hV : Vmem S (spTransvection a c) =
      {x | ∃ μ : F, μ ≠ 0 ∧ x = spTransvection (μ • a) c} := rootGroupSp_Vmem_eq ha hc
  rw [hV] at hx ⊢
  obtain rfl | ⟨μ, hμ, rfl⟩ := hx
  · rw [inv_one, Set.mem_insert_iff]
    left
    rfl
  · rw [CFSG.RankThree.PartOne.KCSpFull.spTransvection_inv, CharTwo.neg_eq,
      Set.mem_insert_iff]
    right
    exact ⟨μ, hμ, rfl⟩

private theorem rootGroupSp_insert_one_Vmem_subgroup [CharP F 2]
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0) :
    ∃ R : Subgroup ↥(StatedSp k F),
      (R : Set ↥(StatedSp k F)) =
        insert 1 (Vmem {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
          (spTransvection a c)) := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  refine ⟨{ carrier := insert 1 (Vmem S (spTransvection a c))
            mul_mem' := fun hx hy => rootGroupSp_mul_mem_insert_one ha hc hx hy
            one_mem' := Set.mem_insert _ _
            inv_mem' := fun hx => rootGroupSp_inv_mem_insert_one ha hc hx }, rfl⟩

private theorem rootGroupSp_spTransvection_ne_smul [CharP F 2]
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0) {l : F} (hl : l ≠ 1) :
    spTransvection a c ≠ spTransvection (l • a) c := by
  obtain ⟨y, hy⟩ :=
    CFSG.ClassicalGroups.Symplectic.a2_exists_form_ne_zero
      (B := spForm k F) spForm_isAlt spForm_nondegenerate ha
  intro hEq
  have h := congrArg (fun g => spEnd g y) hEq
  rw [CFSG.RankThree.PartOne.CTP.spTransvection_smul, spEnd_spTransvection,
    spEnd_spTransvection] at h
  have h2 : (c * spForm k F y a) • a = ((l * l * c) * spForm k F y a) • a :=
    add_left_cancel h
  have h3 : c * spForm k F y a = (l * l * c) * spForm k F y a :=
    smul_left_injective F ha h2
  have h4 : c = l * l * c := mul_right_cancel₀ hy h3
  have h4' : (1 : F) * c = (l * l) * c := by
    rw [one_mul]
    exact h4
  have hl2 : l * l = 1 := (mul_right_cancel₀ hc h4').symm
  have h6 : (l + 1) * (l + 1) = 0 := by
    linear_combination hl2 + (1 + l) * (CharTwo.two_eq_zero : (2 : F) = 0)
  have h7 : l + 1 = 0 := mul_self_eq_zero.mp h6
  have h8 : l = -1 := eq_neg_of_add_eq_zero_left h7
  rw [CharTwo.neg_eq] at h8
  exact hl h8

private theorem rootGroupSp_two_le_ncard [Finite F] [CharP F 2]
    {a : Fin k ⊕ Fin k → F} (ha : a ≠ 0) {c : F} (hc : c ≠ 0)
    (hcard : 2 < Nat.card F) :
    2 ≤ (Vmem {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
      (spTransvection a c)).ncard := by
  classical
  let S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}
  have hV : Vmem S (spTransvection a c) =
      {x | ∃ μ : F, μ ≠ 0 ∧ x = spTransvection (μ • a) c} := rootGroupSp_Vmem_eq ha hc
  obtain ⟨l, hl0, hl1⟩ := Fourteen.exists_ne_zero_ne_one hcard
  have hlt : spTransvection a c ∈ Vmem S (spTransvection a c) := mem_Vmem_self ⟨a, ha, rfl⟩
  have hlu : spTransvection (l • a) c ∈ Vmem S (spTransvection a c) := by
    rw [hV]
    exact ⟨l, hl0, rfl⟩
  have hne : spTransvection a c ≠ spTransvection (l • a) c :=
    rootGroupSp_spTransvection_ne_smul ha hc hl1
  have hfin : (Vmem S (spTransvection a c)).Finite := Set.toFinite _
  have h1 : 1 < (Vmem S (spTransvection a c)).ncard :=
    (Set.one_lt_ncard hfin).mpr ⟨_, hlt, _, hlu, hne⟩
  change 2 ≤ (Vmem S (spTransvection a c)).ncard
  omega

private theorem rootGroupSp_four {c : F} (hc : c ≠ 0) (hk : 2 ≤ k) :
    ∃ t ∈ {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c},
      ∃ u ∈ {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c},
      ∃ v ∈ {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c},
      ∃ w ∈ {x : ↥(StatedSp k F) | ∃ b, b ≠ 0 ∧ x = spTransvection b c},
        ¬ Commute t u ∧ ¬ Commute v w ∧ Commute v t ∧ Commute v u ∧
          Commute w t ∧ Commute w u := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  let e₀ : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i₀) 1
  let f₀ : Fin k ⊕ Fin k → F := Pi.single (Sum.inr i₀) 1
  let e₁ : Fin k ⊕ Fin k → F := Pi.single (Sum.inl i₁) 1
  let f₁ : Fin k ⊕ Fin k → F := Pi.single (Sum.inr i₁) 1
  have ht : ¬ Commute (spTransvection e₀ c) (spTransvection f₀ c) := by
    rw [commute_spTransvection_iff hc hc, spForm_single_inl_left]
    simp [f₀]
  have hw : ¬ Commute (spTransvection e₁ c) (spTransvection f₁ c) := by
    rw [commute_spTransvection_iff hc hc, spForm_single_inl_left]
    simp [f₁]
  exact ⟨spTransvection e₀ c, ⟨e₀, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩,
    spTransvection f₀ c, ⟨f₀, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩,
    spTransvection e₁ c, ⟨e₁, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩,
    spTransvection f₁ c, ⟨f₁, Pi.single_ne_zero_iff.2 one_ne_zero, rfl⟩,
    ht, hw,
    (commute_spTransvection_iff hc hc).mpr (spForm_single_inl_inl i₁ i₀),
    (commute_spTransvection_iff hc hc).mpr (by
      rw [spForm_single_inl_left]
      simp [f₀, Pi.single_apply, hi.symm]),
    (commute_spTransvection_iff hc hc).mpr (by rw [spForm_single_inr_inl, if_neg hi.symm]),
    (commute_spTransvection_iff hc hc).mpr (by
      rw [spForm_single_inr_left]
      simp [f₀])⟩

private theorem rootGroupSp_subgroup_of_image_class {X : Type} [Group X] {k : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] (φ : X ≃* ↥(StatedSp k F)) {s x : X} {c : F}
    (hc : c ≠ 0)
    (hclass : φ '' {y | IsConj s y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c})
    (hx : x ∈ {y | IsConj s y}) :
    ∃ R : Subgroup X, (R : Set X) = insert 1 (Vmem {y | IsConj s y} x) := by
  classical
  have hxS : φ x ∈ {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} := by
    rw [← hclass]
    exact ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hφx⟩ := hxS
  have hV : φ '' Vmem {y | IsConj s y} x =
      Vmem {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} (spTransvection a c) := by
    have h := Vmem_image_mulEquiv φ {y | IsConj s y} x
    rw [hclass] at h
    rw [← h, hφx]
  obtain ⟨R₀, hR₀⟩ := rootGroupSp_insert_one_Vmem_subgroup (k := k) (F := F) ha hc
  refine ⟨R₀.comap φ.toMonoidHom, ?_⟩
  have himg : φ '' insert 1 (Vmem {y | IsConj s y} x) =
      insert 1 (Vmem {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} (spTransvection a c)) := by
    rw [Set.image_insert_eq, map_one, hV]
  ext y
  rw [Subgroup.coe_comap, Set.mem_preimage, hR₀]
  constructor
  · intro hy
    rw [← himg] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rwa [φ.injective hzy] at hz
  · intro hy
    rw [← himg]
    exact ⟨y, hy, rfl⟩

private theorem rootGroupSp_two_le_of_image_class {X : Type} [Group X] {k : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] (φ : X ≃* ↥(StatedSp k F)) {s x : X} {c : F}
    (hc : c ≠ 0)
    (hclass : φ '' {y | IsConj s y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c})
    (hx : x ∈ {y | IsConj s y}) (hcard : 2 < Nat.card F) :
    2 ≤ (Vmem {y | IsConj s y} x).ncard := by
  have hxS : φ x ∈ {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} := by
    rw [← hclass]
    exact ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hφx⟩ := hxS
  have hV : φ '' Vmem {y | IsConj s y} x =
      Vmem {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} (spTransvection a c) := by
    have h := Vmem_image_mulEquiv φ {y | IsConj s y} x
    rw [hclass] at h
    rw [← h, hφx]
  have hnc : (Vmem {y | IsConj s y} x).ncard =
      (Vmem {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} (spTransvection a c)).ncard := by
    rw [← Set.ncard_image_of_injective (Vmem {y | IsConj s y} x) φ.injective, hV]
  rw [hnc]
  exact rootGroupSp_two_le_ncard (k := k) (F := F) ha hc hcard

private theorem rootGroupSp_four_of_image_class {X : Type} [Group X] {k : ℕ} {F : Type}
    [Field F] [Finite F] (φ : X ≃* ↥(StatedSp k F)) {s : X} {c : F} (hc : c ≠ 0)
    (hclass : φ '' {y | IsConj s y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c})
    (hk : 2 ≤ k) :
    ∃ t ∈ {y | IsConj s y}, ∃ u ∈ {y | IsConj s y}, ∃ v ∈ {y | IsConj s y},
      ∃ w ∈ {y | IsConj s y}, ¬ Commute t u ∧ ¬ Commute v w ∧ Commute v t ∧
        Commute v u ∧ Commute w t ∧ Commute w u := by
  obtain ⟨t', ht', u', hu', v', hv', w', hw', htu, hvw, hvt, hvu, hwt, hwu⟩ :=
    rootGroupSp_four (k := k) (F := F) hc hk
  have hclass' : φ.symm '' {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} = {y | IsConj s y} := by
    rw [← hclass]
    exact CFSG.Fischer.image_symm_image φ {y | IsConj s y}
  have hmem : ∀ z ∈ {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c},
      φ.symm z ∈ {y | IsConj s y} := by
    intro z hz
    rw [← hclass']
    exact ⟨z, hz, rfl⟩
  have hcomm : ∀ {z z' : ↥(StatedSp k F)}, Commute z z' →
      Commute (φ.symm z) (φ.symm z') := fun h => by
    simpa using h.map φ.symm.toMonoidHom
  have hnc : ∀ {z z' : ↥(StatedSp k F)}, ¬ Commute z z' →
      ¬ Commute (φ.symm z) (φ.symm z') := fun h hc' => h (by
    simpa using hc'.map φ.toMonoidHom)
  exact ⟨φ.symm t', hmem t' ht', φ.symm u', hmem u' hu', φ.symm v', hmem v' hv',
    φ.symm w', hmem w' hw', hnc htu, hnc hvw, hcomm hvt, hcomm hvu, hcomm hwt, hcomm hwu⟩

end Model

theorem exists_subgroup_eq_insert_Vmem_of_isSymplecticTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hs : IsSymplecticTransvection X m f s)
    {x : X} (hx : x ∈ {y | IsConj s y}) :
    ∃ R : Subgroup X, (R : Set X) = insert 1 (Vmem {y | IsConj s y} x) := by
  obtain ⟨k, rfl, F, hF, hFfin, hFcard, e, he⟩ := hs
  haveI : Finite F := hFfin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  let ψ : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ y : X, ψ y = QuotientGroup.mk y := by intro y; simp [ψ]
  let φ := ψ.trans e
  have hφ : φ s = e (QuotientGroup.mk s) := by simp [φ, hψ s]
  let t₀ := e (QuotientGroup.mk s)
  have ht : IsSymplecticTransvectionIn k t₀ := by simpa [t₀] using he
  obtain ⟨a₀, c, ha₀, hc, ht₀⟩ := borel86_spn_eq_spTransvection ht
  have hS : {y | IsConj t₀ y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} := by
    simpa [ht₀] using (setOf_isConj_spTransvection ha₀ c)
  have hclass : φ '' {y | IsConj s y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} := by
    rw [CFSG.Fischer.image_setOf_isConj φ s, hφ, hS]
  exact rootGroupSp_subgroup_of_image_class (k := k) (F := F) φ hc hclass hx

theorem two_le_ncard_Vmem_of_isSymplecticTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hf : 2 ≤ f)
    (hs : IsSymplecticTransvection X m f s) {x : X} (hx : x ∈ {y | IsConj s y}) :
    2 ≤ (Vmem {y | IsConj s y} x).ncard := by
  obtain ⟨k, rfl, F, hF, hFfin, hFcard, e, he⟩ := hs
  haveI : Finite F := hFfin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  let ψ : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ y : X, ψ y = QuotientGroup.mk y := by intro y; simp [ψ]
  let φ := ψ.trans e
  have hφ : φ s = e (QuotientGroup.mk s) := by simp [φ, hψ s]
  let t₀ := e (QuotientGroup.mk s)
  have ht : IsSymplecticTransvectionIn k t₀ := by simpa [t₀] using he
  obtain ⟨a₀, c, ha₀, hc, ht₀⟩ := borel86_spn_eq_spTransvection ht
  have hS : {y | IsConj t₀ y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} := by
    simpa [ht₀] using (setOf_isConj_spTransvection ha₀ c)
  have hclass : φ '' {y | IsConj s y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} := by
    rw [CFSG.Fischer.image_setOf_isConj φ s, hφ, hS]
  have hcard : 2 < Nat.card F := by
    rw [hFcard]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact rootGroupSp_two_le_of_image_class (k := k) (F := F) φ hc hclass hx hcard

theorem exists_four_of_isSymplecticTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {k f : ℕ} (hk : 2 ≤ k)
    (hs : IsSymplecticTransvection X (2 * k) f s) :
    ∃ t ∈ {y | IsConj s y}, ∃ u ∈ {y | IsConj s y}, ∃ v ∈ {y | IsConj s y},
      ∃ w ∈ {y | IsConj s y}, ¬ Commute t u ∧ ¬ Commute v w ∧
        Commute v t ∧ Commute v u ∧ Commute w t ∧ Commute w u := by
  obtain ⟨k', hk', F, hF, hFfin, hFcard, e, he⟩ := hs
  obtain rfl : k' = k := by omega
  haveI : Finite F := hFfin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by rw [← Nat.card_eq_fintype_card]; exact hFcard)
  let ψ : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ y : X, ψ y = QuotientGroup.mk y := by intro y; simp [ψ]
  let φ := ψ.trans e
  have hφ : φ s = e (QuotientGroup.mk s) := by simp [φ, hψ s]
  let t₀ := e (QuotientGroup.mk s)
  have ht : IsSymplecticTransvectionIn k' t₀ := by simpa [t₀] using he
  obtain ⟨a₀, c, ha₀, hc, ht₀⟩ := borel86_spn_eq_spTransvection ht
  have hS : {y | IsConj t₀ y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} := by
    simpa [ht₀] using (setOf_isConj_spTransvection ha₀ c)
  have hclass : φ '' {y | IsConj s y} = {y | ∃ b, b ≠ 0 ∧ y = spTransvection b c} := by
    rw [CFSG.Fischer.image_setOf_isConj φ s, hφ, hS]
  exact rootGroupSp_four_of_image_class (k := k') (F := F) φ hc hclass hk

end CFSG.OddTranspositions.PartFour
