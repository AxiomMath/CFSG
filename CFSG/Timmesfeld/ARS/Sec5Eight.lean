module

public import CFSG.Timmesfeld.ARS.Sec5Conj
public import CFSG.Timmesfeld.ARS.Sec5Seven

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

def commutatorInto (V ℓ : Subgroup G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.centralizer (ℓ : Set G) ∧ y ∈ Subgroup.normalizer (V : Set G) ∧
    ∀ v ∈ V, ⁅v, y⁆ ∈ ℓ}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun v _ => by
    rw [commutatorElement_one_right]
    exact ℓ.one_mem⟩
  mul_mem' := fun {y y'} hy hy' => by
    refine ⟨Subgroup.mul_mem _ hy.1 hy'.1, Subgroup.mul_mem _ hy.2.1 hy'.2.1, fun v hv => ?_⟩
    have e : ⁅v, y * y'⁆ = ⁅v, y⁆ * (y * ⁅v, y'⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, (Subgroup.mem_centralizer_iff.1 hy.1 _ (hy'.2.2 v hv)).symm, mul_inv_cancel_right]
    exact ℓ.mul_mem (hy.2.2 v hv) (hy'.2.2 v hv)
  inv_mem' := fun {y} hy => by
    refine ⟨Subgroup.inv_mem _ hy.1, Subgroup.inv_mem _ hy.2.1, fun v hv => ?_⟩
    have e : ⁅v, y⁻¹⁆ = y⁻¹ * ⁅v, y⁆⁻¹ * y⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, (Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hy.1) _
      (ℓ.inv_mem (hy.2.2 v hv))).symm, mul_inv_cancel_right]
    exact ℓ.inv_mem (hy.2.2 v hv)

theorem mem_commutatorInto {V ℓ : Subgroup G} {y : G} :
    y ∈ commutatorInto V ℓ ↔ y ∈ Subgroup.centralizer (ℓ : Set G) ∧
      y ∈ Subgroup.normalizer (V : Set G) ∧ ∀ v ∈ V, ⁅v, y⁆ ∈ ℓ := Iff.rfl

theorem mem_of_commute_of_mem_sup [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A P B : Subgroup G} (hP : P ∈ R) (hB : B ∈ R) (hAP : Commuting A P) (hAB : Commuting A B)
    (hBP : Special R B P) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) {u : G} (hu : u ∈ A ⊔ P)
    (hub : Commute b u) : u ∈ A := by
  have hle : A ≤ Subgroup.normalizer (P : Set G) :=
    (commuting_iff_le_centralizer.1 hAP.symm).trans (Subgroup.centralizer_le_normalizer _)
  have hu' : u ∈ (A : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hu
  obtain ⟨a, ha, p, hp, rfl⟩ := hu'
  dsimp only at hub ⊢
  have hba : Commute b a := (hAB a ha b hb).symm
  have hbp : Commute b p := by
    have h1 : b * (a * p) = (a * p) * b := hub
    have h2 : b * a = a * b := hba
    have : a * (b * p) = a * (p * b) := by
      calc a * (b * p) = (b * a) * p := by rw [h2]; group
        _ = (a * p) * b := by rw [mul_assoc, h1]
        _ = a * (p * b) := by group
    exact mul_left_cancel this
  rw [eq_one_of_commute_of_special hR hiso hB hP hBP hb hb1 hp hbp, mul_one]
  exact ha

theorem commute_commutatorElement {ℓ : Subgroup G} (hℓ : Commuting ℓ ℓ) {y z v : G}
    (hyz : Commute y z) (hyv : ⁅y, v⁆ ∈ ℓ) (hvz : ⁅v, z⁆ ∈ ℓ)
    (hz : z ∈ Subgroup.centralizer (ℓ : Set G)) : Commute y ⁅v, z⁆ := by
  have hconj : y * z * y⁻¹ = z := by rw [hyz.eq, mul_inv_cancel_right]
  have h1 : y * ⁅v, z⁆ * y⁻¹ = ⁅y * v * y⁻¹, z⁆ := by
    calc y * ⁅v, z⁆ * y⁻¹ = (y * v * y⁻¹) * (y * z * y⁻¹) * (y * v * y⁻¹)⁻¹ *
          (y * z * y⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      _ = ⁅y * v * y⁻¹, z⁆ := by rw [hconj, commutatorElement_def]
  have h2 : ⁅⁅y, v⁆, z⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hz _ hyv)
  rw [conj_eq_commutator_mul y v, Plane.commutatorElement_mul_left_of_commute (hℓ _ hyv _ hvz), h2,
    mul_one] at h1
  have := congrArg (· * y) h1
  simp only [inv_mul_cancel_right] at this
  exact this

section Eight

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ Δ' : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem exists_commuting_not_le_sup (hΔ' : IsWeakTI R Δ') {A B : Subgroup G} (hA : A ∈ Δ')
    (hB : B ∈ lambdaSet R A) (hBΔ : B ∉ Δ') {m : ℕ} (hm : Nat.card ↥(gen Δ') = Nat.card A ^ m)
    (h4 : 4 ≤ m) :
    ∃ C ∈ Δ', C ≠ A ∧ Commuting C B ∧ ∃ C' ∈ Δ', C' ≠ A ∧ Commuting C' B ∧ ¬ C' ≤ A ⊔ C := by
  have hAR := hΔ'.1 hA
  have hq : 2 ≤ Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hAR)
  have hcard := card_gen_eq hR hiso hnd hΩ hΔ' hA hB hBΔ
  have hax : Nat.card ↥(axis Δ' B) = Nat.card A ^ (m - 1) := by
    rw [hm, show m = (m - 1) + 1 by omega, pow_succ, mul_comm] at hcard
    exact (Nat.eq_of_mul_eq_mul_left (by omega) hcard.symm)
  have hq3 : Nat.card A ^ 2 < Nat.card ↥(axis Δ' B) := by
    rw [hax]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hnA : ¬ axis Δ' B ≤ A := fun h => by
    have := Subgroup.card_le_of_le h
    nlinarith
  obtain ⟨x, hx, hxA⟩ := IsConcreteLE.not_le_iff_exists.1 hnA
  have hx1 : x ≠ 1 := fun h => hxA (h ▸ A.one_mem)
  obtain ⟨C, hC, hCax, hxC⟩ := exists_mem_le_axis hR hiso hnd hΩ hΔ' hA hB hBΔ hx hx1
  have hCA : C ≠ A := fun e => hxA (e ▸ hxC)
  have hnAC : ¬ axis Δ' B ≤ A ⊔ C := fun h => by
    have h1 := Subgroup.card_le_of_le h
    have h2 := card_sup_le_of_commuting (commuting_of_mem hR hiso hnd hΔ' hA hC)
    rw [hR.card_eq (hΔ'.1 hC) hAR] at h2
    nlinarith
  obtain ⟨y, hy, hyAC⟩ := IsConcreteLE.not_le_iff_exists.1 hnAC
  have hy1 : y ≠ 1 := fun h => hyAC (h ▸ Subgroup.one_mem _)
  obtain ⟨C', hC', hC'ax, hyC'⟩ := exists_mem_le_axis hR hiso hnd hΩ hΔ' hA hB hBΔ hy hy1
  refine ⟨C, hC, hCA, (le_axis_iff hC).1 hCax, C', hC', fun e => hyAC ?_,
    (le_axis_iff hC').1 hC'ax, fun h => hyAC (h hyC')⟩
  exact Subgroup.mem_sup_left (e ▸ hyC')


theorem false_of_commuting {Δ₁ Δ₂ Δ₃ : Set (Subgroup G)} (hΔ₁ : IsWeakTI R Δ₁)
    (hΔ₂ : IsWeakTI R Δ₂) (hΔ₃ : IsWeakTI R Δ₃) {A B C : Subgroup G} (hA₁ : A ∈ Δ₁)
    (hA₂ : A ∈ Δ₂) (hA₃ : A ∈ Δ₃) (h12 : ∀ X ∈ Δ₁, X ∈ Δ₂ → X = A)
    (h13 : ∀ X ∈ Δ₁, X ∈ Δ₃ → X = A) (h23 : ∀ X ∈ Δ₂, X ∈ Δ₃ → X = A) (hB : B ∈ Δ₂)
    (hBA : B ≠ A) (hC : C ∈ Δ₃) (hCA : C ≠ A) (hBC : Commuting B C)
    (hax : axis Δ₁ C ≠ axis Δ₁ B) : False := by
  have hAR := hΔ₁.1 hA₁
  obtain ⟨hBl, hBΔ₁⟩ := mem_lambdaSet_notMem hR hiso hnd hΩ hΔ₂ h12 hA₂ hB hBA
  obtain ⟨hCl, hCΔ₁⟩ := mem_lambdaSet_notMem hR hiso hnd hΩ hΔ₃ h13 hA₃ hC hCA
  have hBR : B ∈ R := hBl.1.1
  have hCR : C ∈ R := hCl.1.1
  have hCB : C ∉ lambdaSet R B := by
    intro hCBl
    have hCΔ₂ : C ∉ Δ₂ := fun h => hCA (h23 C h hC)
    have hbot : ⁅gen Δ₂, C⁆ = ⊥ := by
      rw [eq_bot_iff, ← inf_eq_bot hR hiso hAR hBR hBA.symm]
      exact le_inf (commutator_gen_le hR hiso hnd hΩ hΔ₂ hA₂ hCl)
        (commutator_gen_le hR hiso hnd hΩ hΔ₂ hB hCBl)
    exact hCΔ₂ (mem_of_commuting_gen hR hiso hnd hΩ hΔ₂ hCR
      (commuting_iff_commutator_eq_bot.2 hbot).symm)
  have hnle : ¬ axis Δ₁ C ≤ axis Δ₁ B := by
    intro h
    apply hax
    refine Subgroup.eq_of_le_of_card_ge h ?_
    have hcardC := card_gen_eq hR hiso hnd hΩ hΔ₁ hA₁ hCl hCΔ₁
    rw [card_gen_eq hR hiso hnd hΩ hΔ₁ hA₁ hBl hBΔ₁] at hcardC
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardC).le
  obtain ⟨x, hx, hxB⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hx1 : x ≠ 1 := fun h => hxB (h ▸ Subgroup.one_mem _)
  obtain ⟨P, hP, hPC, hxP⟩ := exists_mem_le_axis hR hiso hnd hΩ hΔ₁ hA₁ hCl hCΔ₁ hx hx1
  have hPB : ¬ Commuting P B := fun h => hxB ((le_axis_iff hP).2 h hxP)
  have hPCc : Commuting P C := (le_axis_iff hP).1 hPC
  have hPA : P ≠ A := fun e => hPB (e ▸ hBl.1.2.2)
  have hPR := hΔ₁.1 hP
  have hAPl : A ∈ lambdaSet R P :=
    mem_lambdaSet_comm hAR (mem_lambdaSet hR hiso hnd hΩ hΔ₁ hA₁ hP (Ne.symm hPA))
  obtain ⟨h, hh, hAh⟩ := exists_mem_stabSet_conjSub_eq hR hiso hnd hΩ hΔ₁ hA₁ hP
  have hΔ₄ : IsWeakTI R (conjSet Δ₂ h) := isWeakTI_conjSet hR hΔ₂ h
  have hP₄ : P ∈ conjSet Δ₂ h := hAh ▸ conjSub_mem_conjSet hA₂ h
  have h14 : ∀ X ∈ Δ₁, X ∈ conjSet Δ₂ h → X = P := by
    intro X hX hX₄
    have hX' : conjSub X h⁻¹ ∈ Δ₂ := (mem_conjSet).1 hX₄
    have hX'' : conjSub X h⁻¹ ∈ Δ₁ := conjSub_mem_of_mem_stabSet (Subgroup.inv_mem _ hh) hX
    rw [← hAh, ← h12 _ hX'' hX', ← conjSub_mul, mul_inv_cancel, conjSub_one]
  have hA₄ : A ∉ conjSet Δ₂ h := fun h' => hPA (h14 A hA₁ h').symm
  obtain ⟨D, hD₄, hDA, -⟩ := exists_special hR hiso hnd hΩ hΔ₄ hP₄ hAPl hA₄
  have hDR : D ∈ R := hΔ₄.1 hD₄
  have hDP : D ≠ P := by
    intro e
    rw [e] at hDA
    exact hDA.not_commuting hR hAPl.1.2.2
  obtain ⟨hDl, hDΔ₁⟩ := mem_lambdaSet_notMem hR hiso hnd hΩ hΔ₄ h14 hP₄ hD₄ hDP
  have hAD : ¬ Commuting A D := fun h' => hDA.not_commuting hR h'.symm
  have hBD : Opposite B D :=
    opposite_of_centre hR hiso hnd hΩ hΔ₁ hA₁ hP (Ne.symm hPA) hBl hBΔ₁ hDl hDΔ₁ hAD hPB
  have hDC : Special R D C := special_of_centre hR hiso hnd hΩ hΔ₁ hP hA₁ hDl hCl hCΔ₁ hPCc hAD
  have hCψ : C ∈ psiSet R D := ⟨hCR, hDC⟩
  obtain ⟨-, ⟨hWeq, -, -, -, -, -, -⟩, ⟨-, -, hZiff⟩⟩ :=
    natural_module_of_commuting hR hiso hBR hDR hBD hCψ hBC rfl rfl rfl
  rcases centralizer_eq_bot_or_mem hR hiso hnd hΩ hBR hDR hBD hCψ hBC rfl rfl rfl with
    hZ0 | ⟨hZR, hCZ⟩
  · exact hCB (hZiff.1 hZ0)
  set W := C ⊔ (⁅D, C⁆ ⊔ ⁅B, ⁅D, C⁆⁆) with hWdef
  set Z := W ⊓ Subgroup.centralizer ((B ⊔ D ⊔ C : Subgroup G) : Set G) with hZdef
  have hℓ : Commuting (A ⊔ P) (A ⊔ P) :=
    (commuting_gen_of_isWeakTI_of hR hiso hnd hΔ₁).mono (sup_le (le_gen hA₁) (le_gen hP))
      (sup_le (le_gen hA₁) (le_gen hP))
  have hnorm : ∀ {E Q Y : Subgroup G}, Q ∈ Δ₁ → E ∈ lambdaSet R Q → Y ∈ Δ₁ →
      E ≤ Subgroup.normalizer ((Q ⊔ Y : Subgroup G) : Set G) := by
    intro E Q Y hQ hE hY
    refine le_normalizer_of_conjSub_le fun e he => ?_
    rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
      conjSub_of_forall_commute fun x hx => (hE.1.2.2 x hx e he).symm]
    refine sup_le le_sup_left ((conjSub_le_commutator_sup he).trans (sup_le ?_ le_sup_right))
    exact ((Subgroup.commutator_mono (le_gen hY) le_rfl).trans
      (commutator_gen_le hR hiso hnd hΩ hΔ₁ hQ hE)).trans le_sup_left
  have hXℓ : B ⊔ D ≤ Subgroup.normalizer ((A ⊔ P : Subgroup G) : Set G) :=
    sup_le (hnorm hA₁ hBl hP) (sup_comm P A ▸ hnorm hP hDl hA₁)
  have hCℓ : Commuting C (A ⊔ P) := Commuting.sup_right hCl.1.2.2.symm hPCc.symm
  have hS : B ⊔ D ⊔ C ≤ Subgroup.normalizer ((gen Δ₁ : Subgroup G) : Set G) :=
    (sup_le (sup_le (le_stabSet_of_commuting hR hΔ₁ hBR hA₁ hBl.1.2.2.symm)
      (le_stabSet_of_commuting hR hΔ₁ hDR hP hDl.1.2.2.symm))
      (le_stabSet_of_commuting hR hΔ₁ hCR hA₁ hCl.1.2.2.symm)).trans
      (stabSet_le_normalizer_gen Δ₁)
  have hWT : W ≤ commutatorInto (gen Δ₁) (A ⊔ P) := by
    rw [hWeq]
    refine iSup₂_le fun y hy => ?_
    have hyℓ : conjSub (A ⊔ P) y = A ⊔ P := conjSub_eq_self_iff.2 (hXℓ hy)
    have hyV : conjSub (gen Δ₁) y = gen Δ₁ :=
      conjSub_eq_self_iff.2 (hS (Subgroup.mem_sup_left hy))
    have hcomm : Commuting (conjSub C y) (A ⊔ P) := hyℓ ▸ hCℓ.conjSub y
    have hcomm' : ⁅gen Δ₁, conjSub C y⁆ ≤ A ⊔ P := by
      calc ⁅gen Δ₁, conjSub C y⁆ = ⁅conjSub (gen Δ₁) y, conjSub C y⁆ := by rw [hyV]
        _ = conjSub ⁅gen Δ₁, C⁆ y := (Subgroup.map_commutator _ _ _).symm
        _ ≤ conjSub (A ⊔ P) y :=
            Subgroup.map_mono ((commutator_gen_le hR hiso hnd hΩ hΔ₁ hA₁ hCl).trans le_sup_left)
        _ = A ⊔ P := hyℓ
    intro c hc
    exact ⟨commuting_iff_le_centralizer.1 hcomm.symm hc,
      hS (conjSub_le le_sup_right (Subgroup.mem_sup_left hy) hc),
      fun v hv => hcomm' (Subgroup.commutator_mem_commutator hv hc)⟩
  have hPBs : Special R B P :=
    (special_of_not_commuting hR hiso hnd hΩ hΔ₁ hA₁ hBl hBΔ₁ hP hPB).1.symm
  have hZV : Commuting Z (gen Δ₁) := by
    intro z hz v hv
    have hzT := hWT hz.1
    have hzc : ∀ y ∈ B ⊔ D ⊔ C, Commute y z := fun y hy =>
      Subgroup.mem_centralizer_iff.1 hz.2 y hy
    have hu := hzT.2.2 v hv
    have hcommB : ∀ b ∈ B, Commute b ⁅v, z⁆ := fun b hb => by
      refine commute_commutatorElement hℓ (hzc b (Subgroup.mem_sup_left
        (Subgroup.mem_sup_left hb))) ?_ hu hzT.1
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.mem_sup_left (commutator_gen_le hR hiso hnd hΩ hΔ₁ hA₁
        hBl (Subgroup.commutator_mem_commutator hv hb)))
    have hcommD : ∀ d ∈ D, Commute d ⁅v, z⁆ := fun d hd => by
      refine commute_commutatorElement hℓ (hzc d (Subgroup.mem_sup_left
        (Subgroup.mem_sup_right hd))) ?_ hu hzT.1
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (Subgroup.mem_sup_right (commutator_gen_le hR hiso hnd hΩ hΔ₁ hP
        hDl (Subgroup.commutator_mem_commutator hv hd)))
    obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
    obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
    have huA : ⁅v, z⁆ ∈ A := mem_of_commute_of_mem_sup hR hiso hPR hBR
      (hℓ.mono le_sup_left le_sup_right) hBl.1.2.2 hPBs hb hb1 hu (hcommB b hb)
    have huP : ⁅v, z⁆ ∈ P := mem_of_commute_of_mem_sup hR hiso hAR hDR
      (hℓ.mono le_sup_right le_sup_left) hDl.1.2.2 hDA hd hd1 (sup_comm A P ▸ hu) (hcommD d hd)
    have hmem : ⁅v, z⁆ ∈ A ⊓ P := ⟨huA, huP⟩
    rw [inf_eq_bot hR hiso hAR hPR (Ne.symm hPA), Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
  have hZ₁ : Z ∈ Δ₁ := mem_of_commuting_gen hR hiso hnd hΩ hΔ₁ hZR hZV
  have hZA : Z = A := by
    by_contra hZA
    have hbot : ⁅gen Δ₁, C⁆ = ⊥ := by
      rw [eq_bot_iff, ← inf_eq_bot hR hiso hZR hAR hZA]
      exact le_inf (commutator_gen_le hR hiso hnd hΩ hΔ₁ hZ₁ hCZ)
        (commutator_gen_le hR hiso hnd hΩ hΔ₁ hA₁ hCl)
    exact hCΔ₁ (mem_of_commuting_gen hR hiso hnd hΩ hΔ₁ hCR
      (commuting_iff_commutator_eq_bot.2 hbot).symm)
  apply hAD
  intro a ha d hd
  have haZ : a ∈ Z := hZA ▸ ha
  exact (Subgroup.mem_centralizer_iff.1 haZ.2 d
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hd))).symm

theorem false_of_three (hΔ : IsWeakTI R Δ) {A : Subgroup G} (hA : A ∈ Δ) {m : ℕ}
    (hm : Nat.card ↥(gen Δ) = Nat.card A ^ m) (h4 : 4 ≤ m) {g₂ g₃ : G}
    (hA₂ : A ∈ conjSet Δ g₂) (hA₃ : A ∈ conjSet Δ g₃) (h12 : conjSet Δ g₂ ≠ Δ)
    (h13 : conjSet Δ g₃ ≠ Δ) (h23 : conjSet Δ g₂ ≠ conjSet Δ g₃) : False := by
  have hΔ₂ := isWeakTI_conjSet hR hΔ g₂
  have hΔ₃ := isWeakTI_conjSet hR hΔ g₃
  have hint : ∀ {Θ Θ' : Set (Subgroup G)}, IsWeakTI R Θ → IsWeakTI R Θ' →
      Nat.card Θ' = Nat.card Θ → A ∈ Θ → A ∈ Θ' → Θ' ≠ Θ → ∀ X ∈ Θ, X ∈ Θ' → X = A := by
    intro Θ Θ' hΘ hΘ' hc hAΘ hAΘ' hne X hX hX'
    by_contra hXA
    exact hne (eq_of_mem_of_mem hR hiso hnd hΩ hΘ hΘ' hc hAΘ hAΘ' hX hX' (Ne.symm hXA))
  have hc2 := card_conjSet Δ g₂
  have hc3 := card_conjSet Δ g₃
  have i12 := hint hΔ hΔ₂ hc2 hA hA₂ h12
  have i13 := hint hΔ hΔ₃ hc3 hA hA₃ h13
  have i23 := hint hΔ₂ hΔ₃ (hc3.trans hc2.symm) hA₂ hA₃ (Ne.symm h23)
  obtain ⟨B, hB, hBA⟩ : ∃ B ∈ conjSet Δ g₂, B ≠ A := by
    obtain ⟨X, hX, Y, hY, hXY⟩ := hΔ₂.2.1
    by_cases h : X = A
    · exact ⟨Y, hY, fun e => hXY (h.trans e.symm)⟩
    · exact ⟨X, hX, h⟩
  obtain ⟨hBl, hBΔ₃⟩ :=
    mem_lambdaSet_notMem hR hiso hnd hΩ hΔ₂ (fun X h3 h2 => i23 X h2 h3) hA₂ hB hBA
  have hm₃ : Nat.card ↥(gen (conjSet Δ g₃)) = Nat.card A ^ m := by
    rw [card_gen_conjSet, hm]
  obtain ⟨C, hC, hCA, hCB, C', hC', hC'A, hC'B, hC'le⟩ :=
    exists_commuting_not_le_sup hR hiso hnd hΩ hΔ₃ hA₃ hBl hBΔ₃ hm₃ h4
  have hne := axis_ne_of_not_le_sup hR hiso hnd hΩ hΔ hΔ₃ hA hA₃ i13 hC hCA hC' hC'A hC'le
  by_cases hcase : axis Δ C = axis Δ B
  · exact false_of_commuting hR hiso hnd hΩ hΔ hΔ₂ hΔ₃ hA hA₂ hA₃ i12 i13 i23 hB hBA hC' hC'A
      hC'B.symm (fun e => hne (hcase.trans e.symm))
  · exact false_of_commuting hR hiso hnd hΩ hΔ hΔ₂ hΔ₃ hA hA₂ hA₃ i12 i13 i23 hB hBA hC hCA
      hCB.symm hcase

end Eight

end Sec5

end CFSG.Timmesfeld.ARS
