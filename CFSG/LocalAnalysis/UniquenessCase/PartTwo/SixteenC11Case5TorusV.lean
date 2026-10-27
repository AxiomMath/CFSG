module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusAlg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5TorusCoord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.Om4 Matrix

variable {K : Type} [Field K] [Finite K]

private noncomputable def s16c11_case5_psi : Multiplicative (K × K) →* MulAut (VM K) where
  toFun x := s16c11_case5_rhoU (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
  map_one' := s16c11_case5_rhoU_one
  map_mul' x y := by
    change s16c11_case5_rhoU (Multiplicative.toAdd (x * y)).1
        (Multiplicative.toAdd (x * y)).2 =
      s16c11_case5_rhoU (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 *
        s16c11_case5_rhoU (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2
    have h : Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x + Multiplicative.toAdd y := rfl
    rw [h, Prod.fst_add, Prod.snd_add, s16c11_case5_rhoU_mul]

private theorem s16c11_case5_psi_injective [CharP K 2] :
    Function.Injective (s16c11_case5_psi (K := K)) := by
  intro x y h
  have h' := s16c11_case5_rhoU_injective (K := K) h
  apply Multiplicative.toAdd.injective
  exact Prod.ext h'.1 h'.2

private theorem s16c11_case5_mem_psi_map_iff [CharP K 2]
    (P : AddSubgroup (K × K)) (a b : K) :
    s16c11_case5_rhoU a b ∈
        Subgroup.map (s16c11_case5_psi (K := K)) (AddSubgroup.toSubgroup P) ↔
      (a, b) ∈ P := by
  constructor
  · intro h
    rcases Subgroup.mem_map.mp h with ⟨y, hy, hyeq⟩
    have h₁ : (Multiplicative.toAdd y).1 = a ∧ (Multiplicative.toAdd y).2 = b :=
      s16c11_case5_rhoU_injective hyeq
    have hy' : Multiplicative.toAdd y = (a, b) := Prod.ext h₁.1 h₁.2
    change Multiplicative.toAdd y ∈ P at hy
    simpa [hy'] using hy
  · intro hp
    exact Subgroup.mem_map.mpr
      ⟨Multiplicative.ofAdd (a, b), by simpa using hp, rfl⟩

theorem s16c11_case5_V_ann (hK : Nat.card K = 4) {A : Subgroup (MulAut (VM K))}
    (hAV : A ≤ s16c11_case5_V) (hA : A ∈ E3.aSet 2 (s16c11_case5_S0 (K := K))) :
    ∃ P : AddSubgroup (K × K), P ≠ ⊥ ∧
      (∀ a b : K, s16c11_case5_rhoU a b ∈ A ↔ (a, b) ∈ P) ∧
      ∀ P' : AddSubgroup (K × K), P' ≤ P → Nat.card ↥P ≤ 2 * Nat.card ↥P' →
        s16c11_case5_ann P' = s16c11_case5_ann P := by
  haveI := s16c11_case5_charP hK
  obtain ⟨hAS, hA1, hAe, hAc⟩ := hA
  let P : AddSubgroup (K × K) :=
    { carrier := {p | s16c11_case5_rhoU p.1 p.2 ∈ A}
      zero_mem' := by
        change s16c11_case5_rhoU (0 : K) (0 : K) ∈ A
        rw [s16c11_case5_rhoU_one]
        exact A.one_mem
      add_mem' := by
        rintro p q hp hq
        show s16c11_case5_rhoU (p.1 + q.1) (p.2 + q.2) ∈ A
        rw [← s16c11_case5_rhoU_mul]
        exact A.mul_mem hp hq
      neg_mem' := by
        rintro p hp
        show s16c11_case5_rhoU (-p.1) (-p.2) ∈ A
        rw [← s16c11_case5_rhoU_inv]
        exact A.inv_mem hp }
  have hiff : ∀ a b : K, s16c11_case5_rhoU a b ∈ A ↔ (a, b) ∈ P := fun a b => Iff.rfl
  have hP : P ≠ ⊥ := by
    intro hbot
    apply hA1
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨⟨a, b⟩, rfl⟩ := s16c11_case5_mem_V.mp (hAV hx)
    have hxP : (a, b) ∈ P := (hiff a b).mp hx
    rw [hbot] at hxP
    simp only [AddSubgroup.mem_bot, Prod.mk_eq_zero] at hxP
    obtain ⟨ha, hb⟩ := hxP
    subst ha
    subst hb
    simpa using s16c11_case5_rhoU_one (K := K)
  refine ⟨P, hP, hiff, ?_⟩
  intro P' hle hcard
  let B : Subgroup (MulAut (VM K)) :=
    Subgroup.map (s16c11_case5_psi (K := K)) (AddSubgroup.toSubgroup P')
  have hBA : B ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact hle (by simpa using hy)
  have hmapP : Subgroup.map (s16c11_case5_psi (K := K)) (AddSubgroup.toSubgroup P) = A := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact (hiff (Multiplicative.toAdd y).1 (Multiplicative.toAdd y).2).mpr
        (by simpa using hy)
    · intro hx
      obtain ⟨⟨a, b⟩, rfl⟩ := s16c11_case5_mem_V.mp (hAV hx)
      exact Subgroup.mem_map.mpr
        ⟨Multiplicative.ofAdd (a, b), by simpa using (hiff a b).mp hx, rfl⟩
  have hcard_A : Nat.card ↥A = Nat.card ↥P := by
    rw [← hmapP, Subgroup.card_map_of_injective
      (s16c11_case5_psi_injective (K := K))]
    rfl
  have hcard_B : Nat.card ↥B = Nat.card ↥P' := by
    rw [Subgroup.card_map_of_injective (s16c11_case5_psi_injective (K := K))]
    rfl
  have hposP : 0 < Nat.card ↥P := Nat.card_pos
  have hposP' : 0 < Nat.card ↥P' := Nat.card_pos
  have hmul : B.relIndex A * Nat.card ↥P' = Nat.card ↥P := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := A)
    rw [inf_eq_left.mpr hBA, hcard_B, hcard_A] at h
    exact h
  have hidxle : B.relIndex A ≤ 2 := by
    have hle2 : B.relIndex A * Nat.card ↥P' ≤ 2 * Nat.card ↥P' := by
      rw [hmul]
      exact hcard
    exact le_of_mul_le_mul_right hle2 hposP'
  have hidxpos : 0 < B.relIndex A := by
    rcases Nat.eq_zero_or_pos (B.relIndex A) with h | h
    · rw [h, zero_mul] at hmul
      omega
    · exact h
  have hidx : B.relIndex A = 1 ∨ B.relIndex A = 2 := by omega
  have hm : E3.mQuot A B < 2 := by
    rcases hidx with h | h
    · rw [E3.mQuot, h]
      have h1 : padicValNat 2 1 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
      rw [h1]
      norm_num
    · rw [E3.mQuot, h, padicValNat_self]
      norm_num
  have hfix : fixV B = fixV A := hAc B hBA hm
  refine Set.Subset.antisymm ?_ ?_
  · intro w hw p hp
    change ∀ q ∈ P', q.1 * w.1 + q.2 * w.2 = 0 at hw
    let X : Matrix (Fin 2) (Fin 2) K := !![0, w.2; w.1, 0]
    have hXB : Multiplicative.ofAdd X ∈ fixV B := by
      rw [s16c11_case5_mem_fixV_iff_of_le_V (hBA.trans hAV) X]
      intro a b hab
      have hab' : (a, b) ∈ P' := (s16c11_case5_mem_psi_map_iff P' a b).mp hab
      have hw' := hw (a, b) hab'
      refine ⟨?_, ?_, ?_⟩
      · simp [X]
      · simp [X]
      · simpa [X] using hw'
    rw [hfix] at hXB
    have hcond := (s16c11_case5_mem_fixV_iff_of_le_V hAV X).mp hXB p.1 p.2
      ((hiff p.1 p.2).mpr hp)
    simpa [X] using hcond.2.2
  · intro w hw p hp
    change ∀ q ∈ P, q.1 * w.1 + q.2 * w.2 = 0 at hw
    exact hw p (hle hp)


theorem s16c11_case5_V_kInv (hK : Nat.card K = 4) {A : Subgroup (MulAut (VM K))}
    (hAV : A ≤ s16c11_case5_V) (hA : A ∈ E3.aSet 2 (s16c11_case5_S0 (K := K))) {a b : K}
    (hab : s16c11_case5_rhoU a b ∈ A) (c : K) :
    s16c11_case5_rhoU (c * a) (c * b) ∈ A := by
  obtain ⟨P, hP, hiff, hprop⟩ := s16c11_case5_V_ann hK hAV hA
  exact (hiff (c * a) (c * b)).mpr
    (s16c11_case5_ann_kInv hK hP hprop c (a, b) ((hiff a b).mp hab))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
