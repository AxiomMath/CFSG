module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentTau
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2AbsDefs
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Y
import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2AbsA
import CFSG.RankThree.PartTwo.Sec15.Sylow155Swap
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Ker
import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJSyl
import CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJYFactsL2
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OpenSplit
public import CFSG.RankThree.PartTwo.Sec17.RouteForms

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped MatrixGroups commutatorElement

@[expose] def Res1L2CThetaZ (Q : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Sec14Std G A c L → ∀ X K Y M T P' : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P' → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P' →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    ∀ Yc : Subgroup (Res1Q A L), Res1AtOf A c L M Yc → IsSimpleGroup ↥Yc →
    Res1OpenL2Type ↥Yc →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G) →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
    (∀ u : ↥(Res1C A L), (u : G) ∈
        pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
      (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1) →
    (∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) →
    L ≤ X → L ≤ delta A (lB A) L → K = X ⊔ CFSG.Open.pCoreOf 2 K →
    omegaA A = {Subgroup.zpowers c} →
    M = Subgroup.normalizer (X : Set G) →
    M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) →
    ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K →
    ∀ z : G, orderOf z = 2 → z ∈ CFSG.Open.pCoreOf 2 K →
      z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) → z ∈ CFSG.Open.pCoreOf 2 Y →
      A ≤ Subgroup.centralizer ({z} : Set G) → K ≤ Subgroup.centralizer ({z} : Set G) →
      Subgroup.centralizer ({z} : Set G) ≤ n155 A K →
      ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))),
          Subgroup.zpowers z⁆ ≠ ⊥ →
      ∀ x ∈ Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L), z * x * z⁻¹ = x

section Abstract

variable {P₀ : Type*} [Group P₀] [Finite P₀] {Y₀ : Type*} [Group Y₀]

private theorem res1L2T_mem_zpowers_of_cyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {a b : C} {n : ℕ} (hn : 0 < n) (hb : orderOf b = n) (ha : a ^ n = 1) :
    a ∈ Subgroup.zpowers b := by
  classical
  have := Fintype.ofFinite C
  have hcard : (Subgroup.zpowers b : Set C).toFinset.card = n := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    change Nat.card (Subgroup.zpowers b) = n
    rw [Nat.card_zpowers, hb]
  have hsub : (Subgroup.zpowers b : Set C).toFinset ⊆
      Finset.univ.filter (fun c : C => c ^ n = 1) := by
    intro c hc
    rw [Set.mem_toFinset, SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hc
    obtain ⟨k, rfl⟩ := hc
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hb, pow_orderOf_eq_one,
      one_zpow]
  have hle : (Finset.univ.filter (fun c : C => c ^ n = 1)).card ≤ n :=
    IsCyclic.card_pow_eq_one_le hn
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  have : a ∈ Finset.univ.filter (fun c : C => c ^ n = 1) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ha⟩
  rw [← heq, Set.mem_toFinset] at this
  exact this

private theorem res1L2T_mulAut_mul_conj_mul_inv (α : MulAut Y₀) (y : Y₀) :
    α * MulAut.conj y * α⁻¹ = MulAut.conj (α y) := by
  ext u
  simp [MulAut.conj_apply]

private theorem res1L2T_commutator_inner {n : ℕ} (hn : 2 ≤ n)
    (e : Y₀ ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) (α β : MulAut Y₀) {x : Y₀}
    (hα : α x = x) (hβ : β x = x) :
    ∃ y ∈ Subgroup.centralizer ({x} : Set Y₀), α * β * α⁻¹ * β⁻¹ = MulAut.conj y := by
  obtain ⟨y, hy⟩ := l2_mulAut_commutator_inner hn e α β
  refine ⟨y, ?_, hy⟩
  have hα' : α⁻¹ x = x := by
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
    exact hα.symm
  have hβ' : β⁻¹ x = x := by
    rw [MulAut.inv_def, MulEquiv.symm_apply_eq]
    exact hβ.symm
  have h1 : (α * β * α⁻¹ * β⁻¹) x = x := by
    simp [MulAut.mul_apply, hα, hβ, hα', hβ']
  rw [hy] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_apply] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

omit [Finite P₀] in
private theorem res1L2T_conj_commutator_zpow {z : P₀} (hz : z ^ 2 = 1) (g : P₀) (k : ℤ) :
    z * ⁅g, z ^ k⁆ * z⁻¹ = ⁅g, z ^ k⁆⁻¹ := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz)
  have hzz : z⁻¹ * z⁻¹ = 1 := by rw [hzi, ← pow_two, hz]
  have hk : z ^ k = 1 ∨ z ^ k = z := by
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul]
      simp [hz]
    · right
      rw [zpow_add, zpow_mul, zpow_one]
      simp [hz]
  rcases hk with hk | hk
  · rw [hk]
    simp
  · rw [hk, commutatorElement_def]
    have h1 : z * (g * z * g⁻¹ * z⁻¹) * z⁻¹ = z * g * z * g⁻¹ * (z⁻¹ * z⁻¹) := by
      simp [hzi, mul_assoc]
    have h2 : (g * z * g⁻¹ * z⁻¹)⁻¹ = z * g * z⁻¹ * g⁻¹ := by group
    rw [h1, h2, hzz, mul_one, hzi]

theorem res1L2T_commutator_facts {n : ℕ} (hn : 2 ≤ n)
    (e : Y₀ ≃* ↥(CFSG.PGLModel.projSL 2 (GaloisField 2 n))) (ρ : P₀ →* MulAut Y₀)
    (O : Subgroup P₀) {z : P₀} (hz : z ^ 2 = 1) {x : Y₀} (hx : orderOf x = 3)
    (hOx : ∀ o ∈ O, ρ o x = x) (hzx : ρ z x = x)
    (hinj : ∀ u ∈ ⁅O, Subgroup.zpowers z⁆, ρ u = 1 → u = 1) :
    IsCyclic ↥⁅O, Subgroup.zpowers z⁆ ∧ Odd (Nat.card ↥⁅O, Subgroup.zpowers z⁆) ∧
      ¬ 3 ∣ Nat.card ↥⁅O, Subgroup.zpowers z⁆ ∧
      (∀ u ∈ ⁅O, Subgroup.zpowers z⁆, z * u * z⁻¹ = u⁻¹) ∧
      ∀ u ∈ ⁅O, Subgroup.zpowers z⁆, ∃ y : Y₀, ρ u = MulAut.conj y := by
  have : Finite Y₀ := res1L2A_l2_finite e
  have hconj := res1L2A_l2_conj_injective e
  set J : Subgroup P₀ := ⁅O, Subgroup.zpowers z⁆ with hJ
  set Cy : Subgroup Y₀ := Subgroup.centralizer ({x} : Set Y₀) with hCy
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hxodd : Odd (orderOf x) := by
    rw [hx]
    decide
  obtain ⟨hcyc, hodd⟩ := l2_centralizer_cyclic_odd hn e x hx1 hxodd
  have hxCy : x ∈ Cy := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let Fx : Subgroup (MulAut Y₀) := MulAction.stabilizer (MulAut Y₀) x
  have hFx : ∀ α : MulAut Y₀, α ∈ Fx ↔ α x = x := fun α => by
    rw [MulAction.mem_stabilizer_iff]
    rfl
  have hzle : Subgroup.zpowers z ≤ Fx.comap ρ :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr ((hFx _).mpr hzx))
  have hgen : ∀ g₁ ∈ O, ∀ g₂ ∈ Subgroup.zpowers z, ∃ y ∈ Cy, ρ ⁅g₁, g₂⁆ = MulAut.conj y := by
    intro g₁ h₁ g₂ h₂
    obtain ⟨y, hy, hyeq⟩ := res1L2T_commutator_inner hn e (ρ g₁) (ρ g₂) (hOx g₁ h₁)
      ((hFx _).mp (Subgroup.mem_comap.mp (hzle h₂)))
    refine ⟨y, hy, ?_⟩
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact hyeq
  have hJK : ∀ u ∈ J, ∃ y ∈ Cy, ρ u = MulAut.conj y := by
    have hle : J ≤ (Cy.map (MulAut.conj : Y₀ →* MulAut Y₀)).comap ρ := by
      rw [hJ, Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      obtain ⟨y, hy, hyeq⟩ := hgen g₁ h₁ g₂ h₂
      rw [Subgroup.mem_comap, hyeq]
      exact Subgroup.mem_map_of_mem _ hy
    intro u hu
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp (hle hu))
    exact ⟨y, hy, hyu.symm⟩
  let ρJ' : J →* ↥(Cy.map (MulAut.conj : Y₀ →* MulAut Y₀)) :=
    (ρ.comp J.subtype).codRestrict _ (fun u => by
      obtain ⟨y, hy, hyu⟩ := hJK u u.2
      exact ⟨y, hy, hyu.symm⟩)
  have hρJ'inj : Function.Injective ρJ' := by
    refine (injective_iff_map_eq_one ρJ').mpr fun u hu => ?_
    have h2 : ρ (u : P₀) = 1 := congrArg Subtype.val hu
    exact Subtype.ext (hinj u u.2 h2)
  let ψ : J →* Cy :=
    (Subgroup.equivMapOfInjective Cy (MulAut.conj : Y₀ →* MulAut Y₀) hconj).symm.toMonoidHom.comp
      ρJ'
  have hψ : Function.Injective ψ := fun a b h =>
    hρJ'inj ((Subgroup.equivMapOfInjective Cy (MulAut.conj : Y₀ →* MulAut Y₀)
      hconj).symm.injective h)
  have := hcyc
  have hJcyc : IsCyclic J := isCyclic_of_injective ψ hψ
  have hJodd : Odd (Nat.card J) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective ψ hψ)
  have hJcomm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := fun a ha b hb => by
    have h := (IsCyclic.commGroup (α := J)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  let S : Subgroup P₀ :=
    { carrier := {u | u ∈ J ∧ z * u * z⁻¹ = u⁻¹}
      mul_mem' := fun {a b} ha hb => ⟨J.mul_mem ha.1 hb.1, by
        rw [show z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) by group, ha.2, hb.2,
          mul_inv_rev]
        exact hJcomm a⁻¹ (J.inv_mem ha.1) b⁻¹ (J.inv_mem hb.1)⟩
      one_mem' := ⟨J.one_mem, by simp⟩
      inv_mem' := fun {a} ha => ⟨J.inv_mem ha.1, by
        rw [show z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ by group, ha.2]⟩ }
  have hJS : J ≤ S := by
    rw [hJ, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    refine ⟨Subgroup.commutator_mem_commutator h₁ h₂, ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h₂
    exact res1L2T_conj_commutator_zpow hz g₁ k
  have hinv : ∀ u ∈ J, z * u * z⁻¹ = u⁻¹ := fun u hu => (hJS hu).2
  refine ⟨hJcyc, hJodd, ?_, hinv, fun u hu => ?_⟩
  · intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 h3
    have hu3 : orderOf (u : P₀) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
    obtain ⟨y, hyC, hyu⟩ := hJK u u.2
    have hρu3 : (ρ (u : P₀)) ^ 3 = 1 := by rw [← map_pow, ← hu3, pow_orderOf_eq_one, map_one]
    have hy3 : y ^ 3 = 1 := hconj (by rw [map_pow, ← hyu, hρu3, map_one])
    have hxord : orderOf (⟨x, hxCy⟩ : Cy) = 3 := by rw [Subgroup.orderOf_mk, hx]
    have hmem : (⟨y, hyC⟩ : Cy) ∈ Subgroup.zpowers (⟨x, hxCy⟩ : Cy) :=
      res1L2T_mem_zpowers_of_cyclic (by norm_num) hxord (Subtype.ext (by simpa using hy3))
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hym : x ^ m = y := by simpa using congrArg Subtype.val hm
    have hzy : ρ z y = y := by rw [← hym, map_zpow, hzx]
    have h1 : ρ (z * (u : P₀) * z⁻¹) = ρ (u : P₀) := by
      rw [map_mul, map_mul, map_inv]
      calc ρ z * ρ ↑u * (ρ z)⁻¹ = ρ z * MulAut.conj y * (ρ z)⁻¹ := by rw [hyu]
        _ = MulAut.conj (ρ z y) := res1L2T_mulAut_mul_conj_mul_inv _ _
        _ = MulAut.conj y := by rw [hzy]
        _ = ρ ↑u := hyu.symm
    rw [hinv u u.2, map_inv] at h1
    have h2 : ρ ((u : P₀) * u) = 1 := by
      rw [map_mul]
      nth_rewrite 2 [← h1]
      exact mul_inv_cancel _
    have h3' : (u : P₀) * u = 1 := hinj _ (J.mul_mem u.2 u.2) h2
    have h4 : (u : P₀) ^ 2 = 1 := by rw [pow_two]; exact h3'
    have := Nat.le_of_dvd (by norm_num) (hu3 ▸ orderOf_dvd_of_pow_eq_one h4)
    omega
  · obtain ⟨y, -, hy⟩ := hJK u hu
    exact ⟨y, hy⟩

end Abstract

section Sylow

theorem res1L2T_exists_sylow_normalized {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]
    (Θ : Subgroup P) (hΘ : Θ.Normal) (j : P) (hj : j ^ p = 1) :
    ∃ R : Subgroup P, R ≤ Θ ∧ IsPGroup p R ∧
      (∀ X : Subgroup P, X ≤ Θ → IsPGroup p X → R ≤ X → X = R) ∧
      ∀ x ∈ R, j * x * j⁻¹ ∈ R := by
  let B : Subgroup P := Θ ⊔ Subgroup.zpowers j
  have hΘB : Θ ≤ B := le_sup_left
  have hjB : Subgroup.zpowers j ≤ B := le_sup_right
  have hjp : IsPGroup p (Subgroup.zpowers j) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hj)
  have : Finite (Subgroup P) := Finite.of_injective (fun H : Subgroup P => (H : Set P))
    SetLike.coe_injective
  let 𝒮 : Set (Subgroup P) := {X | X ≤ B ∧ IsPGroup p X ∧ Subgroup.zpowers j ≤ X}
  have hfin : (Set.toFinite 𝒮).toFinset.Nonempty :=
    ⟨Subgroup.zpowers j, (Set.Finite.mem_toFinset _).2 ⟨hjB, hjp, le_rfl⟩⟩
  obtain ⟨S, hS𝒮', hSmax⟩ := Finset.exists_max_image (Set.toFinite 𝒮).toFinset
    (fun X : Subgroup P => Nat.card X) hfin
  have hS𝒮 : S ∈ 𝒮 := (Set.Finite.mem_toFinset _).1 hS𝒮'
  obtain ⟨hSB, hSp, hjS⟩ := hS𝒮
  have hSmaxB : ∀ X : Subgroup P, X ≤ B → IsPGroup p X → S ≤ X → X = S := by
    intro X hXB hXp hSX
    have hX𝒮 : X ∈ 𝒮 := ⟨hXB, hXp, le_trans hjS hSX⟩
    have hcard : Nat.card X ≤ Nat.card S :=
      hSmax X ((Set.Finite.mem_toFinset _).2 hX𝒮)
    exact (Subgroup.eq_of_le_of_card_ge hSX hcard).symm
  refine ⟨S ⊓ Θ, inf_le_right, hSp.to_le inf_le_left, ?_, ?_⟩
  · intro X hXΘ hXp hRX
    obtain ⟨b, -, hb⟩ := res1L2A_exists_conj_mem_of_maximal B S X hSB (hXΘ.trans hΘB) hSp hXp
      hSmaxB
    have hconj : X.map (MulAut.conj b).toMonoidHom ≤ S ⊓ Θ := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨hb x hx, hΘ.conj_mem x (hXΘ hx) b⟩
    have hcard : Nat.card X ≤ Nat.card (S ⊓ Θ : Subgroup P) := by
      calc Nat.card X = Nat.card (X.map (MulAut.conj b).toMonoidHom) :=
            (Subgroup.card_map_of_injective (MulAut.conj b).injective).symm
        _ ≤ Nat.card (S ⊓ Θ : Subgroup P) := Subgroup.card_le_of_le hconj
    exact (Subgroup.eq_of_le_of_card_ge hRX hcard).symm
  · intro x hx
    have hjS' : j ∈ S := hjS (Subgroup.mem_zpowers j)
    exact ⟨S.mul_mem (S.mul_mem hjS' hx.1) (S.inv_mem hjS'), hΘ.conj_mem x hx.2 j⟩

end Sylow

private theorem res1L2T_card_le_sq_of_localRank {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) {M : Subgroup G}
    (hM : CFSG.IsPLocal 2 M) (P : Subgroup G) {E : Subgroup ↥P} (hEM : E ≤ M.subgroupOf P)
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  set E' : Subgroup G := E.map P.subtype
  have hcard : Nat.card E' = Nat.card E := Subgroup.card_subtype P E
  have hE'M : E' ≤ M := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    exact Subgroup.mem_subgroupOf.mp (hEM hy)
  have hcomm : IsMulCommutative E' := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨y, hy, hya⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨z, hz, hzb⟩ := Subgroup.mem_map.mp b.2
    have key : y * z = z * y := congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
    simp only [Subgroup.coe_mul, ← hya, ← hzb, ← map_mul, key]
  have hpow : ∀ x ∈ E', x ^ p = 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx, ← map_pow, hE.2 y hy, map_one]
  have hE' : CFSG.Open.IsElemAbelian p E' := ⟨hcomm, hpow⟩
  have hpg : IsPGroup p E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
  have hk : Nat.card E' = p ^ n := hcard.trans hn
  have hbdd1 := CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove p hp M
  have h1 : n ≤ CFSG.Open.pRank p M := le_csSup hbdd1 ⟨E', hE'M, hE', hk⟩
  have hbdd2 : BddAbove
      {k | ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k} := by
    refine ⟨Nat.card G, ?_⟩
    rintro _ ⟨H, -, rfl⟩
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp H).trans
      (Subgroup.card_le_card_group H)
  have h2 : CFSG.Open.pRank p M ≤ CFSG.Open.twoLocalPrimeRank p G :=
    le_csSup hbdd2 ⟨M, hM, rfl⟩
  have h3 : CFSG.Open.twoLocalPrimeRank p G < 3 := hloc
  have hn2 : n ≤ 2 := by omega
  calc Nat.card E = Nat.card E' := hcard.symm
    _ = p ^ n := hk
    _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos hn2

section Tau

variable {G : Type} [Group G] [Finite G]

@[expose] def res1L2Rho (A L : Subgroup G) (Yc : Subgroup (Res1Q A L)) [Yc.Normal] :
    ↥(Res1C A L) →* MulAut ↥Yc :=
  (MulAut.conjNormal : Res1Q A L →* MulAut ↥Yc).comp
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)))

omit [Finite G] in
theorem res1L2_rho_eq_one_iff {A L : Subgroup G} {Yc : Subgroup (Res1Q A L)} [Yc.Normal]
    (x : ↥(Res1C A L)) :
    res1L2Rho A L Yc x = 1 ↔ ∀ y ∈ Yc,
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x := by
  constructor
  · intro h y hy
    have h1 : (MulAut.conjNormal (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) :
        MulAut ↥Yc) ⟨y, hy⟩ = ⟨y, hy⟩ := by
      have := congrArg (fun α : MulAut ↥Yc => α ⟨y, hy⟩) h
      simpa [res1L2Rho] using this
    have h2 := congrArg Subtype.val h1
    simp only [MulAut.conjNormal_apply] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  · intro h
    refine MulEquiv.ext fun y => Subtype.ext ?_
    show (MulAut.conjNormal (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) y :
      Res1Q A L) = ((1 : MulAut ↥Yc) y : Res1Q A L)
    rw [MulAut.conjNormal_apply, MulAut.one_apply, h y y.2, mul_inv_cancel_right]

omit [Finite G] in
theorem res1L2_rho_surj {A L : Subgroup G} {Yc : Subgroup (Res1Q A L)} [Yc.Normal] (y : ↥Yc) :
    ∃ u : ↥(Res1C A L), res1L2Rho A L Yc u = MulAut.conj y := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥(Res1C A L)) (y : Res1Q A L)
  refine ⟨u, ?_⟩
  change MulAut.conjNormal (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) =
    MulAut.conj y
  rw [hu]
  exact MulAut.conjNormal_val

theorem res1L2_pGroup_ker_le {A : Subgroup G} {c : G} {L M : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} [Yc.Normal] (hS : Sec14Std G A c L) (hY : Res1AtOf A c L M Yc)
    (hsimple : IsSimpleGroup ↥Yc) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {Xp : Subgroup ↥(Res1C A L)} (hker : Xp ≤ (res1L2Rho A L Yc).ker) (hXp : IsPGroup p Xp) :
    Xp ≤ CFSG.pPrimeCore 3 ↥(Res1C A L) := by
  intro x hx
  obtain ⟨k, hk⟩ := hXp ⟨x, hx⟩
  have hxk : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime
      (orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x)) 3 := by
    have hd : orderOf (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk, map_one])
    exact Nat.Coprime.coprime_dvd_left hd
      (Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_three).mpr hp3))
  have hcomm := (res1L2_rho_eq_one_iff x).mp (MonoidHom.mem_ker.mp (hker hx))
  have h1 := Sylow155R1.res1_eq_one_of_centralizes hS hY.1 hY.2.2.2.1 hsimple hcop hcomm
  exact (QuotientGroup.eq_one_iff x).mp h1

omit [Finite G] in
private theorem res1L2_conj_mem_pPrimeCoreOf {H : Subgroup G} {h x : G} (hh : h ∈ H)
    (hx : x ∈ pPrimeCoreOf 2 H) : h * x * h⁻¹ ∈ pPrimeCoreOf 2 H := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  exact ⟨⟨h, hh⟩ * x₀ * ⟨h, hh⟩⁻¹,
    (inferInstance : (CFSG.pPrimeCore 2 ↥H).Normal).conj_mem x₀ hx₀ ⟨h, hh⟩, rfl⟩

theorem res1L2_commutator_le {A : Subgroup G} {c : G} {L : Subgroup G}
    {X K Y M T P' : Subgroup G} (hS : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P')
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P') {z : G} (hzR : z ∈ CFSG.Open.pCoreOf 2 Y) :
    ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))),
        Subgroup.zpowers z⁆ ≤
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) := by
  obtain ⟨-, hRH, -, -⟩ := Sylow155B1.delta_host_facts hS h146 hC hE hRP
    (Sylow155S.sup_mem_invariant hC hE hRP) (Sylow155S.sup_le_u155 hE hRP)
    (Sylow155S.p_le_normalizer_sup hE) le_sup_left
  have hzH := hRH hzR
  rw [Subgroup.commutator_le]
  intro o ho g hg
  have hgH := (Subgroup.zpowers_le.mpr hzH) hg
  have h1 := res1L2_conj_mem_pPrimeCoreOf hgH (inv_mem ho)
  rw [commutatorElement_def, show o * g * o⁻¹ * g⁻¹ = o * (g * o⁻¹ * g⁻¹) by group]
  exact mul_mem ho h1

omit [Finite G] in
theorem res1L2_centralizer_le_res1C (A L : Subgroup G) :
    Subgroup.centralizer (A : Set G) ≤ Res1C A L := fun _ hx =>
  Subgroup.mem_centralizer_iff.mpr fun b hb =>
    Subgroup.mem_centralizer_iff.mp hx b (Subgroup.mem_inf.mp hb).1

theorem res1L2_prop142 {A : Subgroup G} {c : G} {L : Subgroup G} {X K Y M T P' : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} [Yc.Normal] (hS : Sec14Std G A c L)
    (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P') (h146 : Item146 A (lB A))
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P') (hY : Res1AtOf A c L M Yc) (hP : Res1OpenL2Type ↥Yc)
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    (hEO : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))))
    (hcomm : ∀ u : ↥(Res1C A L), (u : G) ∈
        pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
      (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1)
    {z : G} (hz2 : orderOf z = 2) (hzR : z ∈ CFSG.Open.pCoreOf 2 Y)
    (hAz : A ≤ Subgroup.centralizer ({z} : Set G)) :
    ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))),
        Subgroup.zpowers z⁆ ≤ Res1C A L ∧
    IsCyclic ↥⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
        pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆ ∧
    Odd (Nat.card ↥⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
        pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆) ∧
    ¬ 3 ∣ Nat.card ↥⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
        pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆ ∧
    (∀ x ∈ ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
        pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆, z * x * z⁻¹ = x⁻¹) ∧
    (∀ u : ↥(Res1C A L), (u : G) ∈ ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
        pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆ →
      ∃ y : ↥Yc, res1L2Rho A L Yc u = MulAut.conj y) ∧
    (∀ u : ↥(Res1C A L), (u : G) ∈ ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
        pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆ →
      res1L2Rho A L Yc u = 1 → u = 1) := by
  obtain ⟨n, hn0, h4, ⟨e⟩⟩ := hP
  have hn2 : 2 ≤ n := by omega
  set H := delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X)) with hHdef
  set Ob := pPrimeCoreOf 2 H with hObdef
  set C := Res1C A L with hCdef
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) with hπdef
  set ρ := res1L2Rho A L Yc with hρdef
  set J := ⁅Ob, Subgroup.zpowers z⁆ with hJdef
  have hJO : J ≤ Ob := res1L2_commutator_le hS h146 hC hE hRP hzR
  have hOA : Ob ≤ Subgroup.centralizer (A : Set G) := by
    rw [← hEO]
    exact hEA
  have hzA : z ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hAz ha)
  have hOC : Ob ≤ C := hOA.trans (res1L2_centralizer_le_res1C A L)
  have hzC' : z ∈ C := res1L2_centralizer_le_res1C A L hzA
  have hJC : J ≤ C := hJO.trans hOC
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).1
  obtain ⟨c', hc'Y, hc'⟩ := hY.2.2.2.1.2.1
  have hc'val : (c' : G) = c := hc'
  have hc'Y' : π c' ∈ Yc := Subgroup.mem_comap.mp hc'Y
  set x : ↥Yc := ⟨π c', hc'Y'⟩ with hxdef
  have hx : orderOf x = 3 := by
    rw [hxdef, Subgroup.orderOf_mk]
    exact Gagen155R1HJ.res1_orderOf_pi_c'_eq_three hS hc'val
  have hfixx : ∀ u : ↥C, (u : G) ∈ Subgroup.centralizer (A : Set G) → ρ u x = x := by
    intro u hu
    apply Subtype.ext
    show π u * π c' * (π u)⁻¹ = π c'
    rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (u : G) * (c' : G) = (c' : G) * (u : G)
    rw [hc'val]
    exact (Subgroup.mem_centralizer_iff.mp hu c hcA).symm
  set O' : Subgroup ↥C := Ob.subgroupOf C with hO'def
  set z' : ↥C := ⟨z, hzC'⟩ with hz'def
  have hzz : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have hz2' : z' ^ 2 = 1 := Subtype.ext hzz
  have hmapJ : (⁅O', Subgroup.zpowers z'⁆).map C.subtype = J := by
    rw [Subgroup.map_commutator, hO'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hOC,
      MonoidHom.map_zpowers]
    rfl
  have hJ'mem : ∀ u : ↥C, (u : G) ∈ J ↔ u ∈ ⁅O', Subgroup.zpowers z'⁆ := fun u => by
    rw [← hmapJ]
    exact (Subgroup.mem_map_iff_mem C.subtype_injective)
  have hinj : ∀ u ∈ ⁅O', Subgroup.zpowers z'⁆, ρ u = 1 → u = 1 := by
    intro u hu h1
    exact hcomm u (hJO ((hJ'mem u).mpr hu)) ((res1L2_rho_eq_one_iff u).mp h1)
  obtain ⟨hcyc, hodd, h3, hinv, hinner⟩ := res1L2T_commutator_facts hn2 e ρ O' hz2' hx
    (fun o ho => hfixx o (hOA (Subgroup.mem_subgroupOf.mp ho))) (hfixx z' hzA) hinj
  have hequiv : ↥(⁅O', Subgroup.zpowers z'⁆) ≃* ↥J :=
    (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hmapJ)
  refine ⟨hJC, (MulEquiv.isCyclic hequiv).mp hcyc, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr hequiv.toEquiv]
    exact hodd
  · rw [← Nat.card_congr hequiv.toEquiv]
    exact h3
  · intro v hv
    rw [← hmapJ] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact congrArg Subtype.val (hinv u hu)
  · intro u hu
    obtain ⟨y, hy⟩ := hinner u ((hJ'mem u).mp hu)
    exact ⟨y, hy⟩
  · intro u hu h1
    exact hinj u ((hJ'mem u).mp hu) h1

theorem res1L2_J_isCyclic {A : Subgroup G} {c : G} {L : Subgroup G} {X K Y M T P' : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} (hS : Sec14Std G A c L)
    (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P') (h146 : Item146 A (lB A))
    (hRP : CFSG.Open.pCoreOf 2 Y ≤ P') (hY : Res1AtOf A c L M Yc) (hP : Res1OpenL2Type ↥Yc)
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    (hEO : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))))
    (hcomm : ∀ u : ↥(Res1C A L), (u : G) ∈
        pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
      (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1)
    {z : G} (hz2 : orderOf z = 2) (hzR : z ∈ CFSG.Open.pCoreOf 2 Y)
    (hAz : A ≤ Subgroup.centralizer ({z} : Set G)) :
    IsCyclic ↥⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
        pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆ := by
  have : Yc.Normal := Sylow155R1.res1_isComponent_normal hS hY.1 hY.2.2.2.1.1
  exact (res1L2_prop142 hS hC hE h146 hRP hY hP hEA hEO hcomm hz2 hzR hAz).2.1

theorem res1L2_exists_borel {A : Subgroup G} {c : G} {L M : Subgroup G}
    {Yc : Subgroup (Res1Q A L)} [Yc.Normal] (hS : Sec14Std G A c L) (hAM : A ≤ M)
    (h142 : Concl142 A (lB A)) (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hP : Res1OpenL2Type ↥Yc) :
    ∃ U : Sylow 2 ↥Yc, ∀ w ∈ M.subgroupOf (Res1C A L), ∀ u ∈ (U : Subgroup ↥Yc),
      res1L2Rho A L Yc w u ∈ (U : Subgroup ↥Yc) := by
  obtain ⟨n, hn0, h4, ⟨e⟩⟩ := hP
  have hYF : Res1HJYFacts ↥Yc :=
    Gagen155R1HJ.Res1HJYFacts.of_mulEquiv e (Gagen155R1HJ.res1HJYFacts_projSL hn0 h4)
  obtain ⟨U, hU⟩ := Gagen155R1HJ.res1_exists_sylow_two_normalized hS hAM h142 hY hsimple hYF.1
  refine ⟨U, fun w hw u hu => ?_⟩
  have hwM : (w : G) ∈ M := Subgroup.mem_subgroupOf.mp hw
  have hnorm := hU w (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hwM)
  have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w * (u : Res1Q A L) *
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w)⁻¹ ∈
        (U : Subgroup ↥Yc).map Yc.subtype :=
    (Subgroup.mem_normalizer_iff.mp hnorm _).mp (Subgroup.mem_map_of_mem _ hu)
  obtain ⟨u', hu', hu'eq⟩ := hmem
  have : res1L2Rho A L Yc w u = u' := by
    apply Subtype.ext
    exact (MulAut.conjNormal_apply (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) w)
      u).trans hu'eq.symm
  rw [this]
  exact hu'

theorem res1L2_localRank_lt {A : Subgroup G} {c : G} {L : Subgroup G} (hS : Sec14Std G A c L)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Assembly.RankThreeEven.localRank p G < 3 ∧
      CFSG.Assembly.RankThreeEven.localRank p ↥(Res1C A L) < 3 := by
  have h := hS.toTheoremFourHyp.localRank_lt p hp (by omega)
  exact ⟨h, lt_of_le_of_lt (CFSG.RankThree.PartTwo.localRank_subgroup_le hp (Res1C A L)) h⟩

theorem res1L2_card_le_sq {A : Subgroup G} {c : G} {L : Subgroup G} {X K Y M T : Subgroup G}
    (hS : Sec14Std G A c L) (hC : Ctx155 A X K Y M T) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E : Subgroup ↥(Res1C A L)} (hEM : E ≤ M.subgroupOf (Res1C A L))
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ 2 :=
  res1L2T_card_le_sq_of_localRank hp (res1L2_localRank_lt hS hp hp5).1 hC.mem_m.1.1 (Res1C A L)
    hEM hE

omit [Finite G] in
private theorem res1L2_conj_mem_centralizer {X : Subgroup G} {m x : G}
    (hm : m ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ Subgroup.centralizer (X : Set G)) :
    m * x * m⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hm' : m⁻¹ * a * m ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hm) a).mp ha
    simpa using this
  have h := Subgroup.mem_centralizer_iff.mp hx _ hm'
  calc a * (m * x * m⁻¹) = m * ((m⁻¹ * a * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * a * m)) * m⁻¹ := by rw [h]
    _ = (m * x * m⁻¹) * a := by group

theorem res1L2Abs_of_tau {Q : ∀ (X : Type) [Group X], Prop} (h142 : Concl142S14)
    (hCent : Sylow155R1.Res1CentLeMN Q Res1OpenL2Type) (hCT : Res1L2CThetaZ Q)
    {A : Subgroup G} {c : G} {L : Subgroup G} (hR : Sec15R G A c L)
    (hq : Q (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hN : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hS : Sec14Std G A c L) {X K Y M T P' : Subgroup G} (hC : Ctx155 A X K Y M T)
    (hmax : MaxT155 A X K T) (habove : Above155w A X) (hE : End155N A X K Y M T P')
    (h146 : Item146 A (lB A)) (hRP : CFSG.Open.pCoreOf 2 Y ≤ P')
    (hIX : delta A (lB A) M ≤ Subgroup.normalizer (X : Set G))
    {Yc : Subgroup (Res1Q A L)} (hY : Res1AtOf A c L M Yc) (hsimple : IsSimpleGroup ↥Yc)
    (hP : Res1OpenL2Type ↥Yc)
    (hEA : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G))
    (hEO : layerOddPreimage
        (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))))
    (hcomm : ∀ u : ↥(Res1C A L), (u : G) ∈
        pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
      (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1)
    (hfield : ∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x)
    (hLX : L ≤ X) (hLΔ : L ≤ delta A (lB A) L) (hKX : K = X ⊔ CFSG.Open.pCoreOf 2 K)
    (hΩ : omegaA A = {Subgroup.zpowers c}) (hMX : M = Subgroup.normalizer (X : Set G))
    (hMO : M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G))
    (hE0N : ¬ pPrimeCoreOf 2
      (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤ n155 A K)
    {z : G} (hz2 : orderOf z = 2) (hzV : z ∈ CFSG.Open.pCoreOf 2 K)
    (hzC : z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G))
    (hzR : z ∈ CFSG.Open.pCoreOf 2 Y) (hAz : A ≤ Subgroup.centralizer ({z} : Set G))
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hCN : Subgroup.centralizer ({z} : Set G) ≤ n155 A K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {j : G} (hjJ : j ∈ ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
        pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆) (hjp : orderOf j = p) :
    Nonempty (Res1L2Abs ↥(Res1C A L) ↥Yc p) := by
  have hYn : Yc.Normal := Sylow155R1.res1_isComponent_normal hS hY.1 hY.2.2.2.1.1
  obtain ⟨hJC, -, -, -, hinv, hinner, hinjJ⟩ :=
    res1L2_prop142 hS hC hE h146 hRP hY hP hEA hEO hcomm hz2 hzR hAz
  have hj1 : j ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hjp
    have := hp.two_le
    omega
  have hJne : ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔
      pPrimeCoreOf 3 (u155 A M X))), Subgroup.zpowers z⁆ ≠ ⊥ := by
    intro h
    rw [h] at hjJ
    exact hj1 (Subgroup.mem_bot.mp hjJ)
  have hjM : Subgroup.centralizer ({j} : Set G) ≤ M :=
    hCent G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP hEA hEO
      hcomm hfield hLX hLΔ hKX hΩ hMX hMO hE0N z hz2 hzV hzC hzR hAz hKz hCN j hjJ hj1
  have hCTz : ∀ x ∈ Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L),
      z * x * z⁻¹ = x :=
    hCT G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP hEA hEO
      hcomm hfield hLX hLΔ hKX hΩ hMX hMO hE0N z hz2 hzV hzC hzR hAz hKz hCN hJne
  obtain ⟨n, hn0, h4, ⟨e⟩⟩ := id hP
  have hp3 : p ≠ 3 := by omega
  have hzA : z ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hAz ha)
  have hzP : z ∈ Res1C A L := res1L2_centralizer_le_res1C A L hzA
  have hjP : j ∈ Res1C A L := hJC hjJ
  have hzM : z ∈ M :=
    hC.mem_m.2 (Subgroup.mem_sup_right (CFSG.LieType.BorelTits.pCoreOf_le 2 Y hzR))
  have hjM' : j ∈ M := hjM (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨U, hU⟩ := res1L2_exists_borel hS (fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha))
    (h142 G A c L hS) hY hsimple hP
  obtain ⟨-, hlocP⟩ := res1L2_localRank_lt hS hp hp5
  refine ⟨{ hp := hp, hp5 := hp5, n := n, hn4 := Nat.le_of_dvd hn0 h4, hn := h4, e := ⟨e⟩,
            ρ := res1L2Rho A L Yc, hinn := fun y => res1L2_rho_surj y,
            Θ := CFSG.pPrimeCore 3 ↥(Res1C A L), hΘn := inferInstance, hΘker := ?_, hker := ?_,
            j := ⟨j, hjP⟩, hj := ?_, hρj := ?_, hjinn := hinner ⟨j, hjP⟩ hjJ, z := ⟨z, hzP⟩,
            hzj := ?_, M := M.subgroupOf (Res1C A L), hzM := Subgroup.mem_subgroupOf.mpr hzM,
            hjM := Subgroup.mem_subgroupOf.mpr hjM', hCM := ?_, U := U, hBorel := hU,
            hrank := fun E hEM hE => res1L2_card_le_sq hS hC hp hp5 hEM hE, hloc := hlocP,
            Cc := (Subgroup.centralizer (X : Set G)).subgroupOf (Res1C A L), hCcM := ?_,
            hzCc := ?_, hCT := ?_ }⟩
  · intro t ht
    rw [MonoidHom.mem_ker, res1L2_rho_eq_one_iff]
    intro y hy
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) t = 1 :=
      (QuotientGroup.eq_one_iff t).mpr ht
    rw [h1, one_mul, mul_one]
  · exact fun Xp hX hXp => res1L2_pGroup_ker_le hS hY hsimple hp hp3 hX hXp
  · have hjj : j ^ p = 1 := hjp ▸ pow_orderOf_eq_one j
    exact Subtype.ext hjj
  · exact fun h => hj1 (congrArg Subtype.val (hinjJ ⟨j, hjP⟩ hjJ h))
  · exact Subtype.ext (hinv j hjJ)
  · intro u hu
    rw [Subgroup.mem_subgroupOf]
    apply hjM
    rw [Subgroup.mem_centralizer_singleton_iff] at hu ⊢
    exact congrArg Subtype.val hu
  · intro m hm x hx
    have hmN : (m : G) ∈ Subgroup.normalizer (X : Set G) := hMX ▸ Subgroup.mem_subgroupOf.mp hm
    exact res1L2_conj_mem_centralizer hmN (Subgroup.mem_subgroupOf.mp hx)
  · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mp (hKz (hC.le_k ha)))
  · intro x hx
    obtain ⟨hxC, hxΘ⟩ := Subgroup.mem_inf.mp hx
    have hxG : (x : G) ∈ Subgroup.centralizer (X : Set G) ⊓ pPrimeCoreOf 3 (Res1C A L) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hxC, ⟨x, hxΘ, rfl⟩⟩
    exact Subtype.ext (hCTz _ hxG)

theorem res1JCyclic_l2 {Q : ∀ (X : Type) [Group X], Prop} :
    Sylow155R1.Res1JCyclic Q Res1OpenL2Type := by
  intro G _ _ A c L X K Y M T P' Yc z h
  exact res1L2_J_isCyclic h.std h.ctx h.endN h.i146 h.r_le h.at_of h.p h.e_le h.e_eq h.comm
    h.z_two h.z_r h.a_z

end Tau

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2
