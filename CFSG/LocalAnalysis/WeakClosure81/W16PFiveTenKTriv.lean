module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNine
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNineGen
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveKGp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

private theorem mem_center_of_bar_eq {K : Subgroup G} {X : Type} [Group X]
    {φ : ↥K →* X} (hsurj : Function.Surjective φ) {y y' : X}
    (h : ∀ k : ↥K, y * φ k * y⁻¹ = y' * φ k * y'⁻¹) :
    y'⁻¹ * y ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨k, rfl⟩ := hsurj g
  have hk := h k
  have hz : (y'⁻¹ * y) * φ k * (y'⁻¹ * y)⁻¹ = φ k := by
    calc (y'⁻¹ * y) * φ k * (y'⁻¹ * y)⁻¹
        = y'⁻¹ * (y * φ k * y⁻¹) * y' := by group
      _ = y'⁻¹ * (y' * φ k * y'⁻¹) * y' := by rw [hk]
      _ = φ k := by group
  have hc : (y'⁻¹ * y) * φ k = φ k * (y'⁻¹ * y) := by
    have := congrArg (fun t => t * (y'⁻¹ * y)) hz
    simpa [mul_assoc] using this
  exact hc.symm

theorem IsMinFam16.exists_hom_ne_one (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G))
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {x : G}
    (hxS : conjSubgroup V x ≤ S) (hxk : ¬ conjSubgroup V x ≤ kerMOf M H)
    {w : ↥(conjSubgroup V x) →* X}
    (hw : ∀ (a : ↥(conjSubgroup V x)) (k k' : ↥(conjClosure V H)),
      (k' : G) = (a : G) * k * (a : G)⁻¹ → φ k' = w a * φ k * (w a)⁻¹) :
    ∃ a : ↥(conjSubgroup V x), w a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hSH : S ≤ H := hH.1.1
  have hAH : conjSubgroup V x ≤ H := hxS.trans hSH
  have hnormK : H ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H
  have hnormN : H ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure V H) : Set G) :=
    hnormK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf
      (r := 2) (conjClosure V H))
  have hprop : ∀ a : ↥(conjSubgroup V x), ∀ k ∈ conjClosure V H,
      (a : G) * k * (a : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H) := by
    intro a k hk
    have haN : (a : G) ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
      hnormK (hAH a.2)
    let kK : ↥(conjClosure V H) := ⟨k, hk⟩
    let k' : ↥(conjClosure V H) :=
      ⟨(a : G) * k * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp haN k).mp hk⟩
    have hk' : (k' : G) = (a : G) * k * (a : G)⁻¹ := rfl
    have hφk' : φ k' = φ kK := by
      rw [hw a kK k' hk', hcon a]
      simp
    have hker : (k' * kK⁻¹) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφk', mul_inv_cancel]
    have hmem : ((k' * kK⁻¹ : ↥(conjClosure V H)) : G) ∈
        pCoreOf 2 (conjClosure V H) :=
      (hφ.ker_iff (k' * kK⁻¹)).mp hker
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hk'] at hmem
    exact hmem
  have hconjM : ∀ a : ↥(conjSubgroup V x), ∀ g ∈ H,
      g * (a : G) * g⁻¹ ∈ M := by
    intro a g hg
    have hgN : g ∈ Subgroup.normalizer (pCoreOf 2 (conjClosure V H) : Set G) := hnormN hg
    have hbH : g * (a : G) * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg (hAH a.2)) (H.inv_mem hg)
    refine Cex16.mem_of_conj_le_sup h1 h5 hS h hH.1 hV hQ hbH ?_
    intro v hv
    have hgv : g⁻¹ * v * g ∈ conjClosure V H := by
      have hginv : g⁻¹ ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
        Subgroup.inv_mem _ (hnormK hg)
      simpa using (Subgroup.mem_normalizer_iff.mp hginv v).mp (le_conjClosure V H hv)
    have hcomm : (a : G) * (g⁻¹ * v * g) * (a : G)⁻¹ * (g⁻¹ * v * g)⁻¹ ∈
        pCoreOf 2 (conjClosure V H) := hprop a (g⁻¹ * v * g) hgv
    have hconj : g * ((a : G) * (g⁻¹ * v * g) * (a : G)⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹
        = g * (a : G) * g⁻¹ * v * (g * (a : G) * g⁻¹)⁻¹ * v⁻¹ := by group
    have hmemN : g * (a : G) * g⁻¹ * v * (g * (a : G) * g⁻¹)⁻¹ * v⁻¹
        ∈ pCoreOf 2 (conjClosure V H) := by
      rw [← hconj]
      exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hcomm
    have hsplit : g * (a : G) * g⁻¹ * v * (g * (a : G) * g⁻¹)⁻¹
        = (g * (a : G) * g⁻¹ * v * (g * (a : G) * g⁻¹)⁻¹ * v⁻¹) * v := by group
    rw [hsplit]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmemN) (Subgroup.mem_sup_left hv)
  apply hxk
  intro y hy
  rw [mem_kerMOf_iff]
  exact ⟨hAH hy, fun g hg => hconjM ⟨y, hy⟩ g hg⟩

theorem IsMinFam16.hom_conj_eq (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    {X : Type} [Group X] {φ : ↥(conjClosure V H) →* X}
    (hφ : SevenK.IsBarMap (conjClosure V H) (pCoreOf 2 (conjClosure V H)) φ) {n : ℕ}
    (hX : Shape166 X (SevenK.barSub (conjClosure V H) φ V) n) {x : G}
    (hxS : conjSubgroup V x ≤ S)
    {w : ↥(conjSubgroup V x) →* X}
    (hw1 : ∀ a, w a ∈ SevenK.barSub (conjClosure V H) φ V)
    (hw : ∀ (a : ↥(conjSubgroup V x)) (k k' : ↥(conjClosure V H)),
      (k' : G) = (a : G) * k * (a : G)⁻¹ → φ k' = w a * φ k * (w a)⁻¹)
    {u : ↥(conjClosure V H)} (hu : (u : G) ∈ normalizer (conjSubgroup V x : Set G))
    {a a' : ↥(conjSubgroup V x)} (haa : (a' : G) = (u : G) * (a : G) * (u : G)⁻¹) :
    w a' = φ u * w a * (φ u)⁻¹ := by
  classical
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  have hSH : S ≤ H := hH.1.1
  have hAH : conjSubgroup V x ≤ H := hxS.trans hSH
  have hnormK : H ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H
  have haN : (a : G) ∈ Subgroup.normalizer (conjClosure V H : Set G) := hnormK (hAH a.2)
  have ha'N : (a' : G) ∈ Subgroup.normalizer (conjClosure V H : Set G) := hnormK (hAH a'.2)
  have hact : ∀ k : ↥(conjClosure V H),
      w a' * φ k * (w a')⁻¹
        = (φ u * w a * (φ u)⁻¹) * φ k * (φ u * w a * (φ u)⁻¹)⁻¹ := by
    intro k
    let k' : ↥(conjClosure V H) :=
      ⟨(a' : G) * k * (a' : G)⁻¹, (Subgroup.mem_normalizer_iff.mp ha'N (k : G)).mp k.2⟩
    have hk' : (k' : G) = (a' : G) * k * (a' : G)⁻¹ := rfl
    have h1' : φ k' = w a' * φ k * (w a')⁻¹ := hw a' k k' hk'
    let k1 : ↥(conjClosure V H) :=
      ⟨(u : G)⁻¹ * (k : G) * (u : G),
        (conjClosure V H).mul_mem
          ((conjClosure V H).mul_mem ((conjClosure V H).inv_mem u.2) k.2) u.2⟩
    have hk1 : (k1 : G) = (u : G)⁻¹ * (k : G) * (u : G) := rfl
    have hk1eq : k1 = u⁻¹ * k * u := rfl
    have hφk1 : φ k1 = (φ u)⁻¹ * φ k * φ u := by
      rw [hk1eq, map_mul, map_mul, map_inv]
    let k2 : ↥(conjClosure V H) :=
      ⟨(a : G) * (k1 : G) * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp haN (k1 : G)).mp k1.2⟩
    have hk2 : (k2 : G) = (a : G) * (k1 : G) * (a : G)⁻¹ := rfl
    have h2' : φ k2 = w a * φ k1 * (w a)⁻¹ := hw a k1 k2 hk2
    let k3 : ↥(conjClosure V H) :=
      ⟨(u : G) * (k2 : G) * (u : G)⁻¹,
        (conjClosure V H).mul_mem
          ((conjClosure V H).mul_mem u.2 k2.2) ((conjClosure V H).inv_mem u.2)⟩
    have hk3 : (k3 : G) = (u : G) * (k2 : G) * (u : G)⁻¹ := rfl
    have hk3eq : k3 = u * k2 * u⁻¹ := rfl
    have hφk3 : φ k3 = φ u * φ k2 * (φ u)⁻¹ := by
      rw [hk3eq, map_mul, map_mul, map_inv]
    have hk3k' : k3 = k' := by
      apply Subtype.ext
      rw [hk3, hk2, hk1, hk', haa]
      group
    calc w a' * φ k * (w a')⁻¹
        = φ k' := h1'.symm
      _ = φ k3 := by rw [hk3k']
      _ = φ u * φ k2 * (φ u)⁻¹ := hφk3
      _ = φ u * (w a * φ k1 * (w a)⁻¹) * (φ u)⁻¹ := by rw [h2']
      _ = φ u * (w a * ((φ u)⁻¹ * φ k * φ u) * (w a)⁻¹) * (φ u)⁻¹ := by rw [hφk1]
      _ = (φ u * w a * (φ u)⁻¹) * φ k * (φ u * w a * (φ u)⁻¹)⁻¹ := by group
  have hzmem : (φ u * w a * (φ u)⁻¹)⁻¹ * w a' ∈ Subgroup.center X :=
    mem_center_of_bar_eq hφ.surjective hact
  have hY : IsElemAbelian 2 (SevenK.barSub (conjClosure V H) φ V) :=
    (h.hyp.h6.elemAbelian.subgroupOf (conjClosure V H)).map φ
  have hgen : normalClosure
      ((SevenK.barSub (conjClosure V H) φ V : Subgroup X) : Set X) = ⊤ :=
    IsMinFam16.normalClosure_barSub_eq_top h1 hS h hH hV hφ
  have hodd : Odd (Nat.card (Subgroup.center X)) := Shape166.odd_card_center hY hgen hX
  have hY2 : IsPGroup 2 (SevenK.barSub (conjClosure V H) φ V) := hY.isPGroup
  obtain ⟨j1, hj1sub⟩ := hY2 ⟨w a', hw1 a'⟩
  have hj1 : (w a') ^ (2 ^ j1) = 1 := by
    simpa using congrArg Subtype.val hj1sub
  obtain ⟨j2, hj2sub⟩ := hY2 ⟨w a, hw1 a⟩
  have hj2 : (w a) ^ (2 ^ j2) = 1 := by
    simpa using congrArg Subtype.val hj2sub
  have hypow : (w a') ^ (2 ^ (j1 + j2)) = 1 := by
    have h : 2 ^ (j1 + j2) = 2 ^ j1 * 2 ^ j2 := by rw [pow_add]
    rw [h, pow_mul, hj1, one_pow]
  have hy'pow : (φ u * w a * (φ u)⁻¹) ^ (2 ^ (j1 + j2)) = 1 := by
    have hwa : (w a) ^ (2 ^ (j1 + j2)) = 1 := by
      have h : 2 ^ (j1 + j2) = 2 ^ j2 * 2 ^ j1 := by rw [pow_add]; ring
      rw [h, pow_mul, hj2, one_pow]
    rw [conj_pow, hwa]
    simp
  have hcomm : Commute (φ u * w a * (φ u)⁻¹)⁻¹ (w a') := by
    have hyz : w a' * (((φ u * w a * (φ u)⁻¹)⁻¹) * w a')
        = (((φ u * w a * (φ u)⁻¹)⁻¹) * w a') * w a' :=
      (Subgroup.mem_center_iff.mp hzmem) (w a')
    have h' : w a' * (φ u * w a * (φ u)⁻¹)⁻¹
        = (φ u * w a * (φ u)⁻¹)⁻¹ * w a' := by
      have h'' : w a' * (φ u * w a * (φ u)⁻¹)⁻¹ * w a'
          = (φ u * w a * (φ u)⁻¹)⁻¹ * w a' * w a' := by
        simpa [mul_assoc] using hyz
      exact mul_right_cancel h''
    exact (commute_iff_eq _ _).mpr h'.symm
  have hzpow : ((φ u * w a * (φ u)⁻¹)⁻¹ * w a') ^ (2 ^ (j1 + j2)) = 1 := by
    rw [hcomm.mul_pow, inv_pow, hy'pow, hypow]
    simp
  have hdvd_pow : orderOf ((φ u * w a * (φ u)⁻¹)⁻¹ * w a') ∣ 2 ^ (j1 + j2) :=
    orderOf_dvd_of_pow_eq_one hzpow
  have hdvd_card : orderOf ((φ u * w a * (φ u)⁻¹)⁻¹ * w a') ∣
      Nat.card (Subgroup.center X) := Subgroup.orderOf_dvd_natCard _ hzmem
  have hcop : Nat.Coprime (2 ^ (j1 + j2)) (Nat.card (Subgroup.center X)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have hz1 : (φ u * w a * (φ u)⁻¹)⁻¹ * w a' = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvd_pow hdvd_card)
  have : w a' = φ u * w a * (φ u)⁻¹ := by
    have h := congrArg (fun t => (φ u * w a * (φ u)⁻¹) * t) hz1
    simpa [mul_assoc] using h
  exact this

end CFSG.LocalAnalysis.WeakClosure81

end
