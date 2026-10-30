module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217ALe

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint CFSG.Sporadic.Schreier
  CFSG.RankThree.Asc83Table

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
theorem perfect_core_centralizer_J3Plain {X : Type} [Group X] [Finite X]
    (e : X ≃* NativeSporadic.J3) {a : X} (ha3 : a ^ 3 = 1) (ha : a ≠ 1)
    (h5 : 5 ∣ Nat.card (centralizer ({e a} : Set NativeSporadic.J3))) :
    ∃ P : Subgroup X, P ≤ centralizer ({a} : Set X) ∧ ⁅P, P⁆ = P ∧
      Nonempty (↥P ≃* alternatingGroup (Fin 6)) ∧
      ∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ P := by
  set ψ : X ≃* ↥j3P := e.trans Item228CensusProof.j3CarrierEquiv with hψ
  set ρ : X →* Equiv.Perm (Fin 6156) := j3P.subtype.comp ψ.toMonoidHom with hρ
  have hρapp : ∀ w : X, ρ w = (ψ w : Equiv.Perm (Fin 6156)) := fun w => rfl
  have hρker : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker, hρapp] at hw
    have h1 : ψ w = 1 := Subtype.ext hw
    rw [map_eq_one_iff ψ ψ.injective] at h1
    exact (Subgroup.mem_bot.2 h1)
  have hρR : ρ.range = j3P := by
    ext r
    constructor
    · rintro ⟨w, rfl⟩
      rw [hρapp]
      exact (ψ _).2
    · intro hr
      refine ⟨ψ.symm ⟨r, hr⟩, ?_⟩
      rw [hρapp, MulEquiv.apply_symm_apply]
  have hK : ∀ P : Subgroup X, P ≤ centralizer ({a} : Set X) → ⁅P, P⁆ = P → P ⊓ ρ.ker = ⊥ := by
    intro P _ _
    rw [hρker, inf_bot_eq]
  have hyR : ρ a ∈ j3P := by rw [← hρR]; exact ⟨a, rfl⟩
  have hy3 : orderOf (ρ a) = 3 := by
    have h3 : ρ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
    have h1 : ρ a ≠ 1 := by
      intro h
      apply ha
      have : a ∈ ρ.ker := MonoidHom.mem_ker.2 h
      rwa [hρker, Subgroup.mem_bot] at this
    exact orderOf_eq_prime h3 h1
  have h5' : 5 ∣ Nat.card (centralizer ({ρ a} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
      Subgroup (Equiv.Perm (Fin 6156))) := by
    have hya : ρ a = ((Item228CensusProof.j3CarrierEquiv (e a) : ↥j3P) : Equiv.Perm (Fin 6156)) :=
      hρapp a
    rw [hya]
    have h5c : 5 ∣ Nat.card (centralizer ({e a} : Set (NativeSporadic.Carrier .J3))) := h5
    generalize e a = x at h5c ⊢
    have := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
      Item228CensusProof.j3CarrierEquiv x
    exact Dvd.dvd.trans h5c (dvd_of_eq this)
  obtain ⟨Dy, hDy1, hDy2, hDy3, ⟨eD⟩⟩ := exists_A6_in_centralizer_j3P hyR hy3 h5'
  have hpre : ((centralizer ({ρ a} : Set (Equiv.Perm (Fin 6156)))).comap ρ).map ρ =
      centralizer ({ρ a} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P := by
    rw [Subgroup.map_comap_eq, hρR, inf_comm]
  obtain ⟨P, hP1, hP2, -, ⟨eP⟩, hP5⟩ := perfect_core_of_cover ρ (by rw [hρker]; exact bot_le) a Dy
    (by rw [hpre]; exact hDy1) (by rw [hpre]; exact hDy2) hDy3 hK
  exact ⟨P, hP1, hP2, ⟨eP.trans eD⟩, hP5⟩

theorem exists_E27_J3 {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.J3) :
    ∃ B : Subgroup X, CFSG.IsElementaryAbelian 3 B ∧ Nat.card B = 27 := by
  obtain ⟨B₀, -, hB₀j, hB₀e, hB₀c, -⟩ := j3P_e27_split
  set ψ : X ≃* ↥j3P := e.trans Item228CensusProof.j3CarrierEquiv with hψ
  set A' : Subgroup ↥j3P := B₀.subgroupOf j3P with hA'
  have hA'e : IsElementaryAbelian 3 A' := by
    have hB₀' := isElementaryAbelian_iff.1 hB₀e
    rw [isElementaryAbelian_iff]
    refine ⟨fun a ha b hb => Subtype.ext (hB₀'.1 a.1 ha b.1 hb), fun a ha => ?_⟩
    exact Subtype.ext (hB₀'.2 a.1 ha)
  have hA'27 : Nat.card A' = 27 := by
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀j).toEquiv, hB₀c]
  refine ⟨A'.map ψ.symm.toMonoidHom, IsElementaryAbelian.map_hom ψ.symm.toMonoidHom hA'e, ?_⟩
  rw [Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective, hA'27]

set_option maxRecDepth 20000 in
theorem exists_local_frame_J3 {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.J3) :
    ∃ (a y : X) (W : Subgroup X), a ≠ 1 ∧ a ^ 3 = 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ a * y = y * a ∧
      y ∉ zpowers a ∧ W ≠ ⊥ ∧ IsPGroup 2 W ∧ (∀ w ∈ W, a * w = w * a) ∧
      y ∈ normalizer (W : Set X) := by
  obtain ⟨B, hBe, hB27⟩ := exists_E27_J3 e
  obtain ⟨B₁, hB₁B, hB₁9, -, h3A⟩ := j3_e27_class_split e hBe hB27
  obtain ⟨a, haB, haB₁⟩ : ∃ a ∈ B, a ∉ B₁ := by
    by_contra hno
    push Not at hno
    have : Nat.card B ≤ Nat.card B₁ := Subgroup.card_le_of_le (fun x hx => hno x hx)
    omega
  have ha1 : a ≠ 1 := fun h => haB₁ (h ▸ Subgroup.one_mem _)
  have ha3 : a ^ 3 = 1 := (isElementaryAbelian_iff.1 hBe).2 a haB
  have h5 : 5 ∣ Nat.card (centralizer ({e a} : Set NativeSporadic.J3)) := by
    rw [card_cent_J3_eq e a, h3A a haB haB₁]
    norm_num
  obtain ⟨P, hPC, hPperf, ⟨φ⟩, -⟩ := perfect_core_centralizer_J3Plain e ha3 ha1 h5
  obtain ⟨y, hyP, hy3, hy1, W, hWP, hW0, hW2, hyN⟩ := exists_three_normalizing_two_subgroup P φ
  have hZP := center_eq_bot_of_equiv_alt6 P φ
  have haP_of : a ∈ P → False := by
    intro haP
    have : (⟨a, haP⟩ : ↥P) ∈ center ↥P := by
      rw [Subgroup.mem_center_iff]
      intro z
      exact Subtype.ext (mem_centralizer_singleton_iff.1 (hPC z.2))
    rw [hZP, Subgroup.mem_bot] at this
    exact ha1 (congrArg Subtype.val this)
  refine ⟨a, y, W, ha1, ha3, hy3, hy1, ?_, ?_, hW0, hW2, ?_, hyN⟩
  · exact (mem_centralizer_singleton_iff.1 (hPC hyP)).symm
  · intro hya
    rcases mem_zpowers_of_pow_three ha3 hya with h1 | h1 | h1
    · exact hy1 h1
    · exact haP_of (h1 ▸ hyP)
    · apply haP_of
      have : a = y ^ 2 := by
        rw [h1]
        have : (a ^ 2) ^ 2 = a ^ 3 * a := by group
        rw [this, ha3, one_mul]
      rw [this]
      exact pow_mem hyP 2
  · intro w hw
    exact (mem_centralizer_singleton_iff.1 (hPC (hWP hw))).symm

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
