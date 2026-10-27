module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step209LNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    (IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n) →
      L ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G)

@[expose] def Step209LCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    (IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n) →
    L ≤ Subgroup.normalizer (normalClosureIn (kTwenty M c ⊓ N) c : Set G) →
      ⁅L, normalClosureIn (kTwenty M c ⊓ N) c⁆ = ⊥

theorem step209L_of (hN : Step209LNormal) (hC : Step209LCentral) : Step209L :=
  fun G _ _ A M L N c T hT hTN h7 h8 =>
    hC G A M L N c T hT hTN h7 h8 (hN G A M L N c T hT hTN h7 h8)

variable {G : Type} [Group G] [Finite G]

theorem commutator_mem_pCoreOf_of_mem_normalClosureIn_core {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {d : G}
    (hd : d ∈ normalClosureIn (kTwenty M c ⊓ N) c) :
    ∀ l ∈ L, d * l * d⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  have hNO : N ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hN ▸ CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hN ▸ le_rfl
  have hc : ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    have hc' : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
      rw [hT.centralizer_eq]
      exact Subgroup.mem_zpowers c
    exact hc'.2
  let P : G → Prop := fun d => d ∈ N ∧ ∀ l ∈ L, d * l * d⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L
  have hPmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨hxN, hx⟩ ⟨hyN, hy⟩
    refine ⟨N.mul_mem hxN hyN, fun l hl => ?_⟩
    have h1 := hy l hl
    have h2 : x * (y * l * y⁻¹ * l⁻¹) * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp (hNO hxN) _).mp h1
    have h3 := hx l hl
    have : x * y * l * (x * y)⁻¹ * l⁻¹ =
        (x * (y * l * y⁻¹ * l⁻¹) * x⁻¹) * (x * l * x⁻¹ * l⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ h2 h3
  have hPinv : ∀ x, P x → P x⁻¹ := by
    rintro x ⟨hxN, hx⟩
    refine ⟨N.inv_mem hxN, fun l hl => ?_⟩
    have hl' : x⁻¹ * l * x ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hNL (N.inv_mem hxN)) l).mp hl
      simpa using this
    have h1 := hx _ hl'
    have : x⁻¹ * l * x⁻¹⁻¹ * l⁻¹ = (x * (x⁻¹ * l * x) * x⁻¹ * (x⁻¹ * l * x)⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ h1
  have hgen : ∀ k ∈ kTwenty M c ⊓ N, P (k * c * k⁻¹) := by
    intro k hk
    have hcN : c ∈ N := by
      rw [hN]
      exact hAL (mem_of_hyp201 hT.toHyp201)
    have hcP : P c := ⟨hcN, hc⟩
    refine ⟨N.mul_mem (N.mul_mem hk.2 hcN) (N.inv_mem hk.2), fun l hl => ?_⟩
    have hl' : k⁻¹ * l * k ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hNL (N.inv_mem hk.2)) l).mp hl
      simpa using this
    have h1 := hcP.2 _ hl'
    have h2 : k * (c * (k⁻¹ * l * k) * c⁻¹ * (k⁻¹ * l * k)⁻¹) * k⁻¹ ∈
        CFSG.Open.pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp (hNO hk.2) _).mp h1
    have : k * c * k⁻¹ * l * (k * c * k⁻¹)⁻¹ * l⁻¹ =
        k * (c * (k⁻¹ * l * k) * c⁻¹ * (k⁻¹ * l * k)⁻¹) * k⁻¹ := by group
    rw [this]
    exact h2
  have hP : P d := by
    refine Subgroup.closure_induction (p := fun x _ => P x) ?_ ?_ ?_ ?_ hd
    · rintro _ ⟨k, hk, rfl⟩
      exact hgen k hk
    · exact ⟨N.one_mem, fun l hl => by simp⟩
    · intro x y _ _ hx hy
      exact hPmul x y hx hy
    · intro x _ hx
      exact hPinv x hx
  exact hP.2

theorem le_normalizer_normalClosureIn_sup_pCoreOf_core {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (hT : Ctx20 G A M L N c T) (hN : N = Subgroup.normalizer (L : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    L ≤ Subgroup.normalizer
      ((normalClosureIn (kTwenty M c ⊓ N) c ⊔ CFSG.Open.pCoreOf 2 L : Subgroup G) : Set G) := by
  intro l hl
  apply mem_normalizer_of_map_conj_le
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨d, hd, rfl⟩
    have h1 := commutator_mem_pCoreOf_of_mem_normalClosureIn_core hT hN hAL
      (Subgroup.inv_mem _ hd) l hl
    have heq : (MulAut.conj l).toMonoidHom d = d * (d⁻¹ * l * d⁻¹⁻¹ * l⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right h1)
  · rintro _ ⟨o, ho, rfl⟩
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl) o).mp ho)

end CFSG.RankThree.PartTwo.Sec20
