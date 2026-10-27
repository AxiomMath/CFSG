module

public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation

public section

namespace CFSG.RankThree.Chevalley

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory.SteinbergBY
open scoped Pointwise commutatorElement

namespace PlaneAssembly

section Generic

variable {H : Type*} [Group H]

theorem thetaT_le_core {p : ℕ} {E : Subgroup H} {b : H} (hb : b ∈ E) (hb1 : b ≠ 1) :
    thetaT p E ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({b} : Set H)) :=
  fun _ hx => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx b) hb) hb1

theorem plane_local_core_product_le {p : ℕ} {E : Subgroup H}
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {t : H} (ht : t ∈ E) (ht1 : t ≠ 1) :
    ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)), E⁆ ⊔
        thetaT p E ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)) := by
  set S := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set H)) with hS
  have hEC : E ≤ Subgroup.centralizer ({t} : Set H) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (hEab e he t ht)
  have hES : E ≤ Subgroup.normalizer (S : Set H) :=
    hEC.trans (Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p _))
  refine sup_le ?_ ?_
  · rw [Subgroup.commutator_le]
    intro s hs e he
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hs ?_
    have h1 := (Subgroup.mem_normalizer_iff.1 (hES he) s⁻¹).1 (inv_mem hs)
    rwa [← mul_assoc]
  · exact thetaT_le_core ht ht1

theorem thetaT_le_normalizer_commutator {p : ℕ} {E : Subgroup H} {t : H} (ht : t ∈ E)
    (ht1 : t ≠ 1) :
    thetaT p E ≤ Subgroup.normalizer ((⁅inSubgroup (aschbacherSolvableCore p)
      (Subgroup.centralizer ({t} : Set H)), E⁆ : Subgroup H) : Set H) := by
  intro g hg
  have hgC : g ∈ Subgroup.centralizer ({t} : Set H) :=
    Subgroup.map_subtype_le _ (thetaT_le_core ht ht1 hg)
  exact mem_normalizer_commutator
    (normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p _ (Subgroup.le_normalizer hgC))
    (Subgroup.centralizer_le_normalizer _ (thetaT_le_centralizer p E hg))

end Generic

section Aut

variable {C : Type*} [Group C] [Finite C]

theorem plane_local_core_product_odd (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    (hab : ∀ a b : MulAut C, a * b * a⁻¹ * b⁻¹ ∈ (MulAut.conj : C →* MulAut C).range)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup (MulAut C)}
    (hB : (MulAut.conj : C →* MulAut C).range ≤ B)
    (hnon : ∀ α : B, (α : MulAut C) ∉ (MulAut.conj : C →* MulAut C).range → orderOf α = p →
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({α} : Set B)) = ⊥)
    (P : C → Prop)
    (hP : ∀ x : C, orderOf x = p → P x →
      Odd (Nat.card (inSubgroup (aschbacherSolvableCore p)
        (Subgroup.centralizer ({(⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ : B)} : Set B)))))
    (hreg : ∀ x : C, orderOf x = p → ¬ P x →
      Odd (Nat.card (Subgroup.centralizer ({x} : Set C))))
    (hplane : ∀ E₀ : Subgroup C, Nat.card E₀ = p ^ 2 → (∀ x ∈ E₀, x ^ p = 1) →
      ∃ x ∈ E₀, x ≠ 1 ∧ P x)
    (E : Subgroup B) (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : B}
    (ht : t ∈ E) (ht1 : t ≠ 1) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), E⁆ ⊔
        thetaT p E : Subgroup B) : Set B) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), E⁆ :
        Subgroup B) : Set B) * (thetaT p E : Set B) ∧
    Odd (Nat.card (⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)),
      E⁆ ⊔ thetaT p E : Subgroup B)) ∧
    ((t : MulAut C) ∉ (MulAut.conj : C →* MulAut C).range →
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)) = ⊥ ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)), E⁆ ⊔
        thetaT p E = ⊥) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hE
  set S := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set B)) with hS
  have hset := (section_nine_residual_to_intersection hp hp2 E).1 t ht ht1
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    mul_comm_of_isMulCommutative ha hb
  have hWS : ⁅S, E⁆ ⊔ thetaT p E ≤ S := plane_local_core_product_le hEab ht ht1
  have hord : orderOf t = p := orderOf_eq_of_isElementaryAbelian hp ht ht1
  set Inn := (MulAut.conj : C →* MulAut C).range with hInn
  have hnonin : (t : MulAut C) ∉ Inn → S = ⊥ ∧ ⁅S, E⁆ ⊔ thetaT p E = ⊥ := fun hnt => by
    have hS0 : S = ⊥ := hnon t hnt hord
    exact ⟨hS0, eq_bot_iff.2 (hS0 ▸ hWS)⟩
  refine ⟨hset, ?_, hnonin⟩
  by_cases hti : (t : MulAut C) ∈ Inn
  swap
  · rw [(hnonin hti).2, Subgroup.card_bot]
    exact odd_one
  obtain ⟨x, hx⟩ := hti
  have htx : t = ⟨MulAut.conj x, hB ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
  have hxord : orderOf x = p := by
    rw [← orderOf_injective _ hinj x, hx, Subgroup.orderOf_coe, hord]
  by_cases hPx : P x
  ·
    have hSodd : Odd (Nat.card S) := by
      rw [hS, htx]
      exact hP x hxord hPx
    exact hSodd.of_dvd_nat (Subgroup.card_dvd_of_le hWS)
  set ι : C →* B := (MulAut.conj : C →* MulAut C).codRestrict B fun c => hB ⟨c, rfl⟩ with hι
  have hιinj : Function.Injective ι := fun a b h => hinj (congrArg Subtype.val h)
  have hSC : S ≤ Subgroup.centralizer ({t} : Set B) := Subgroup.map_subtype_le _
  have hEC : E ≤ Subgroup.centralizer ({t} : Set B) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (hEab e he t ht)
  have hcommle : ⁅S, E⁆ ≤ (Subgroup.centralizer ({x} : Set C)).map ι := by
    rw [Subgroup.commutator_le]
    intro s hs e he
    have hmem : ((⁅s, e⁆ : B) : MulAut C) ∈ Inn := by
      rw [commutatorElement_def]
      exact hab _ _
    obtain ⟨y, hy⟩ := hmem
    have hcen : ⁅s, e⁆ ∈ Subgroup.centralizer ({t} : Set B) := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hSC hs) (hEC he)) (inv_mem (hSC hs))) (inv_mem (hEC he))
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.2 ?_, Subtype.ext hy⟩
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hcen)
    simp only [Subgroup.coe_mul] at h1
    rw [← hy, ← hx] at h1
    exact hinj (by rw [map_mul, map_mul, h1])
  have hcommodd : Odd (Nat.card (⁅S, E⁆ : Subgroup B)) := by
    have h1 := Subgroup.card_dvd_of_le hcommle
    rw [Subgroup.card_map_of_injective hιinj] at h1
    exact (hreg x hxord hPx).of_dvd_nat h1
  have hIodd : Odd (Nat.card (thetaT p E)) := by
    by_cases hall : ∀ b ∈ E, (b : MulAut C) ∈ Inn
    · set E₀ := (E.map B.subtype).comap (MulAut.conj : C →* MulAut C) with hE₀
      have hE₀map : E₀.map ι = E := by
        ext b
        constructor
        · rintro ⟨y, ⟨b', hb', hb'y⟩, rfl⟩
          have : ι y = b' := Subtype.ext hb'y.symm
          rw [this]
          exact hb'
        · intro hb
          obtain ⟨y, hy⟩ := hall b hb
          refine ⟨y, ⟨b, hb, hy.symm⟩, Subtype.ext hy⟩
      have hE₀card : Nat.card E₀ = p ^ 2 := by
        rw [← hEcard, ← hE₀map, Subgroup.card_map_of_injective hιinj]
      have hE₀exp : ∀ y ∈ E₀, y ^ p = 1 := fun y hy => by
        obtain ⟨b', hb', hb'y⟩ := hy
        have h1 := elemPow_eq_one_of_isElementaryAbelian (p := p) b' hb'
        apply hinj
        rw [map_pow, map_one]
        have h2 := congrArg Subtype.val h1
        rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
        rw [← hb'y]
        exact h2
      obtain ⟨y, hyE, hy1, hPy⟩ := hplane E₀ hE₀card hE₀exp
      have hyord : orderOf y = p := orderOf_eq_prime (hE₀exp y hyE) hy1
      have hbE : (⟨MulAut.conj y, hB ⟨y, rfl⟩⟩ : B) ∈ E := by
        rw [← hE₀map]
        exact ⟨y, hyE, rfl⟩
      have hb1 : (⟨MulAut.conj y, hB ⟨y, rfl⟩⟩ : B) ≠ 1 := fun h1 =>
        hy1 (hinj (by rw [map_one]; exact congrArg Subtype.val h1))
      exact (hP y hyord hPy).of_dvd_nat (Subgroup.card_dvd_of_le (thetaT_le_core hbE hb1))
    · push Not at hall
      obtain ⟨b, hb, hbn⟩ := hall
      have hb1 : b ≠ 1 := fun h1 => hbn (by rw [h1]; exact one_mem _)
      have hθb := hnon b hbn (orderOf_eq_of_isElementaryAbelian hp hb hb1)
      have hI : thetaT p E = ⊥ := eq_bot_iff.2 (hθb ▸ thetaT_le_core hb hb1)
      rw [hI, Subgroup.card_bot]
      exact odd_one
  rw [sup_comm]
  exact CFSG.OddSolvableUnitary.odd_card_sup_of_le_normalizer
    (thetaT_le_normalizer_commutator ht ht1) hIodd hcommodd

end Aut

end PlaneAssembly

end CFSG.RankThree.Chevalley
