module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveLemma41
public import CFSG.LocalAnalysis.GLTheoremB.Prop95NonAbFactors
public import CFSG.GroupTheory.ComponentCovering
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveSzFiveLines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure ChiefSetup (D : Data G) (V₀ V : Subgroup G) where
  L : Subgroup G
  X : Subgroup G
  p : ℕ
  n : ℕ
  l : ℕ
  r : ℕ
  C : Subgroup G
  Dc : Subgroup G
  Gamma : Set G
  x : G
  A₀ : Subgroup G
  A : Subgroup G
  B : Subgroup G
  hV₀ : V₀ ≠ ⊥
  ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma
  h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X
  hc4 : F08.Case8100FourR D ![L, conjSubgroup L x] p X
  hAsyl : CFSG.ABGLocalTools.IsSylowOf r A X
  hAT : Permutes A D.T
  hBM : B ≤ D.M
  hBcard : Nat.card B = p
  hAB : ⁅A, B⁆ = A
  hBT : Permutes B D.T
  hcent : centralizer (D.Z : Set G) ≤ D.M
  hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M
  hR8101 : F08.R8101R D
  N : Subgroup G
  H : Subgroup G
  R : Subgroup G
  hN : N ∈ calMOf (A ⊔ B ⊔ D.T)
  hne : N ≠ D.M
  hD₀H : A ⊔ B ⊔ D.T ≤ H
  hHN : H ≤ N
  hHM : ¬ H ≤ D.M
  hmin : ∀ H' : Subgroup G, A ⊔ B ⊔ D.T ≤ H' → H' ≤ H → ¬ H' ≤ D.M → H' = H
  hYR : kerM D.M H < R
  hRH : R ≤ H
  hRn : H ≤ normalizer (R : Set G)
  hminR : ∀ W : Subgroup G, kerM D.M H ≤ W → W ≤ R → H ≤ normalizer (W : Set G) →
    W = kerM D.M H ∨ W = R
  hab : ¬ ⁅R, R⁆ ≤ kerM D.M H

namespace ChiefSetup

variable {D : Data G} {V₀ V : Subgroup G} (s : ChiefSetup D V₀ V)

@[expose] def Y : Subgroup G := kerM D.M s.H

theorem Y_le_H : s.Y ≤ s.H := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_left D.M s.H

theorem Y_le_M : s.Y ≤ D.M := CFSG.LocalAnalysis.RankThreeUC.WeakClosure.kerIn_le_right D.M s.H

theorem H_le_normalizer_Y : s.H ≤ normalizer (s.Y : Set G) := le_normalizer_kerM D.M s.H

theorem A_le_H : s.A ≤ s.H := (le_sup_left.trans le_sup_left).trans s.hD₀H

theorem B_le_H : s.B ≤ s.H := (le_sup_right.trans le_sup_left).trans s.hD₀H

theorem T_le_H : D.T ≤ s.H :=
  (le_sup_right : D.T ≤ (s.A ⊔ s.B) ⊔ D.T).trans s.hD₀H

@[expose] def YH : Subgroup ↥s.H := s.Y.subgroupOf s.H

instance YH_normal : (s.YH).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer s.Y_le_H).mpr s.H_le_normalizer_Y

abbrev Q : Type := ↥s.H ⧸ s.YH

@[expose] def π : ↥s.H →* s.Q := QuotientGroup.mk' s.YH

theorem π_ker : s.π.ker = s.YH := QuotientGroup.ker_mk' s.YH

theorem eq_one_iff {h : ↥s.H} : s.π h = 1 ↔ h ∈ s.YH := QuotientGroup.eq_one_iff h

@[expose] def bar (U : Subgroup G) : Subgroup s.Q := (U.subgroupOf s.H).map s.π

theorem bar_mono {U W : Subgroup G} (h : U ≤ W) : s.bar U ≤ s.bar W :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ h)

theorem mem_bar_iff {U : Subgroup G} (hUH : U ≤ s.H) {z : s.Q} :
    z ∈ s.bar U ↔ ∃ (u : G) (hu : u ∈ U), s.π ⟨u, hUH hu⟩ = z := by
  constructor
  · intro hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨(u : G), hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact Subgroup.mem_map_of_mem s.π (Subgroup.mem_subgroupOf.mpr hu)

theorem bar_injective {U : Subgroup G} (hUH : U ≤ s.H)
    (hUY : U ⊓ s.Y = ⊥) : Function.Injective (fun u : ↥U => s.π ⟨(u : G), hUH u.2⟩) := by
  intro u v huv
  have h1 : s.π (⟨(u : G), hUH u.2⟩ * ⟨(v : G), hUH v.2⟩⁻¹) = 1 := by
    rw [map_mul, map_inv]
    have huv' : s.π ⟨(u : G), hUH u.2⟩ = s.π ⟨(v : G), hUH v.2⟩ := huv
    rw [huv']
    simp
  have h2 : (⟨(u : G), hUH u.2⟩ * ⟨(v : G), hUH v.2⟩⁻¹ : ↥s.H) ∈ s.YH :=
    (s.eq_one_iff).mp h1
  have h3 : ((⟨(u : G), hUH u.2⟩ * ⟨(v : G), hUH v.2⟩⁻¹ : ↥s.H) : G) ∈ s.Y :=
    Subgroup.mem_subgroupOf.mp h2
  have h4 : ((⟨(u : G), hUH u.2⟩ * ⟨(v : G), hUH v.2⟩⁻¹ : ↥s.H) : G) ∈ U :=
    U.mul_mem (show (u : G) ∈ U from u.2) (U.inv_mem (show (v : G) ∈ U from v.2))
  have h5 : ((⟨(u : G), hUH u.2⟩ * ⟨(v : G), hUH v.2⟩⁻¹ : ↥s.H) : G) = 1 := by
    have hmem : ((⟨(u : G), hUH u.2⟩ * ⟨(v : G), hUH v.2⟩⁻¹ : ↥s.H) : G) ∈ U ⊓ s.Y :=
      ⟨h4, h3⟩
    rwa [hUY, Subgroup.mem_bot] at hmem
  apply Subtype.ext
  have hgun : (u : G) * (v : G)⁻¹ = 1 := by simpa using h5
  calc (u : G) = (u : G) * (v : G)⁻¹ * (v : G) := by group
    _ = (v : G) := by rw [hgun, one_mul]

theorem card_bar {U : Subgroup G} (hUH : U ≤ s.H) (hUY : U ⊓ s.Y = ⊥) :
    Nat.card (s.bar U) = Nat.card U := by
  classical
  let f : ↥U → ↥(s.bar U) := fun u =>
    ⟨s.π ⟨(u : G), hUH u.2⟩, (s.mem_bar_iff hUH).mpr ⟨(u : G), u.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro u v huv
    apply s.bar_injective hUH hUY
    exact Subtype.ext_iff.mp huv
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨u, hu, huz⟩ := (s.mem_bar_iff hUH).mp z.2
    exact ⟨⟨u, hu⟩, Subtype.ext huz⟩
  calc Nat.card (s.bar U) = Nat.card ↥U :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    _ = Nat.card U := rfl

section Data

@[expose] def A₁ : Subgroup G := s.A ⊓ s.L

@[expose] def A₂ : Subgroup G := s.A ⊓ conjSubgroup s.L s.x

theorem A₁_le_A : s.A₁ ≤ s.A := inf_le_left

theorem A₂_le_A : s.A₂ ≤ s.A := inf_le_left

theorem A₁_le_H : s.A₁ ≤ s.H := s.A₁_le_A.trans s.A_le_H

theorem A₂_le_H : s.A₂ ≤ s.H := s.A₂_le_A.trans s.A_le_H

theorem factors_holds :
    Nat.card s.A₁ = 31 ∧ Nat.card s.A₂ = 31 ∧
      s.A₁ ≤ Subgroup.centralizer ((s.A₂ : Subgroup G) : Set G) ∧
      s.A₁ ⊓ s.A₂ = ⊥ ∧ Nat.card s.B = 5 ∧
      s.B ≤ Subgroup.normalizer ((s.A₁ : Subgroup G) : Set G) ∧
      s.B ≤ Subgroup.normalizer ((s.A₂ : Subgroup G) : Set G) ∧
      s.A₁ ⊔ s.A₂ = s.A ∧
      (∀ b ∈ s.B, b ≠ 1 → ∀ a ∈ s.A₁ ⊔ s.A₂, a * b = b * a → a = 1) :=
  factors_of_case8100Four D s.hV₀ s.ctx s.h8100 s.hc4 s.hAsyl s.hAT s.hBM s.hBcard s.hAB s.hBT

theorem A₁_card : Nat.card s.A₁ = 31 := s.factors_holds.1

theorem A₂_card : Nat.card s.A₂ = 31 := s.factors_holds.2.1

theorem A₁_le_centralizer_A₂ : s.A₁ ≤ Subgroup.centralizer ((s.A₂ : Subgroup G) : Set G) :=
  s.factors_holds.2.2.1

theorem A₁_inf_A₂ : s.A₁ ⊓ s.A₂ = ⊥ := s.factors_holds.2.2.2.1

theorem B_card5 : Nat.card s.B = 5 := s.factors_holds.2.2.2.2.1

theorem B_le_normalizer_A₁ : s.B ≤ Subgroup.normalizer ((s.A₁ : Subgroup G) : Set G) :=
  s.factors_holds.2.2.2.2.2.1

theorem B_le_normalizer_A₂ : s.B ≤ Subgroup.normalizer ((s.A₂ : Subgroup G) : Set G) :=
  s.factors_holds.2.2.2.2.2.2.1

theorem A₁_sup_A₂ : s.A₁ ⊔ s.A₂ = s.A := s.factors_holds.2.2.2.2.2.2.2.1

theorem A₁_commute_A₂ : ∀ x ∈ s.A₁, ∀ y ∈ s.A₂, x * y = y * x := by
  intro x hx y hy
  exact ((Subgroup.mem_centralizer_iff.1 (s.A₁_le_centralizer_A₂ hx)) y hy).symm

theorem A_card : Nat.card s.A = 31 ^ 2 := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute s.A₁ s.A₂
    s.A₁_commute_A₂).1
  rw [s.A₁_inf_A₂, Subgroup.card_bot, mul_one, s.A₁_card, s.A₂_card] at h
  rw [← s.A₁_sup_A₂, h]
  norm_num

theorem A_dvd : Nat.card s.A ∣ 31 ^ 2 := by
  rw [s.A_card]

theorem uniqueSet_data :
    s.r = 31 ∧ s.A₁ ∈ uniqueSet D.M ∧ s.A₂ ∈ uniqueSet D.M :=
  mem_uniqueSet_inf_of_r8101 D s.hV₀ s.ctx s.h8100 s.hc4 s.hAsyl s.hAT s.hBM s.hBcard
    s.hAB s.hBT s.hR8101

theorem A₁_mem_uniqueSet : s.A₁ ∈ uniqueSet D.M := s.uniqueSet_data.2.1

theorem A₂_mem_uniqueSet : s.A₂ ∈ uniqueSet D.M := s.uniqueSet_data.2.2

theorem B_mem_uniqueSet : s.B ∈ uniqueSet D.M := by
  obtain ⟨-, -, -, -, -, hpSig, -, -, -, -⟩ := s.h8100
  have hp : s.p.Prime := (D.sig_prime s.p hpSig).1
  have hBne : s.B ≠ ⊥ := by
    intro h
    have : s.p = 1 := by rw [← s.hBcard, h, Subgroup.card_bot]
    exact hp.ne_one this
  have hBp : IsPGroup s.p s.B := IsPGroup.of_card (n := 1) (by rw [s.hBcard, pow_one])
  exact uc22p22r_mem_uniqueSet_of_sp D hp s.hsp s.hBM hBp hBne

theorem B_le_normalizer_A : s.B ≤ Subgroup.normalizer ((s.A : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb a ha
  have hcomm : ⁅b, a⁆ ∈ s.A := by
    have := Subgroup.commutator_mem_commutator hb ha
    rwa [Subgroup.commutator_comm, s.hAB] at this
  rw [show b * a * b⁻¹ = ⁅b, a⁆ * a from by rw [commutatorElement_def]; group]
  exact s.A.mul_mem hcomm ha

theorem A₁_inf_Y : s.A₁ ⊓ s.Y = ⊥ :=
  inf_kerM_eq_bot_of_mem_uniqueSet D s.A₁_mem_uniqueSet (by norm_num) s.A₁_card s.A₁_le_H s.hHM

theorem A₂_inf_Y : s.A₂ ⊓ s.Y = ⊥ :=
  inf_kerM_eq_bot_of_mem_uniqueSet D s.A₂_mem_uniqueSet (by norm_num) s.A₂_card s.A₂_le_H s.hHM

theorem B_inf_Y : s.B ⊓ s.Y = ⊥ :=
  inf_kerM_eq_bot_of_mem_uniqueSet D s.B_mem_uniqueSet (by norm_num) s.B_card5 s.B_le_H s.hHM

theorem A_inf_Y : s.A ⊓ s.Y = ⊥ := by
  have hlines : ∀ D' : Subgroup G, D' ≤ s.A → Nat.card D' = 31 →
      s.B ≤ Subgroup.normalizer (D' : Set G) → D' = s.A₁ ∨ D' = s.A₂ :=
    lines_of_case8100Four D s.hV₀ s.ctx s.h8100 s.hc4 s.hAsyl s.hAT s.hBM s.hBcard
      s.hAB s.hBT
  have h := conjSubgroup_inf_kerM_eq_bot (D := D) (A := s.A) (A₁ := s.A₁) (A₂ := s.A₂)
    (B := s.B) (H := s.H) s.A₁_mem_uniqueSet s.A₂_mem_uniqueSet s.A₁_card s.A₂_card
    s.A₁_sup_A₂ s.A_dvd s.B_le_H s.B_le_normalizer_A hlines s.A_le_H s.hHM
  have h1 := h 1 s.H.one_mem
  rwa [conjSubgroup_one] at h1

theorem bar_A₁_card : Nat.card (s.bar s.A₁) = 31 :=
  (s.card_bar s.A₁_le_H s.A₁_inf_Y).trans s.A₁_card

theorem bar_A₂_card : Nat.card (s.bar s.A₂) = 31 :=
  (s.card_bar s.A₂_le_H s.A₂_inf_Y).trans s.A₂_card

theorem bar_B_card : Nat.card (s.bar s.B) = 5 :=
  (s.card_bar s.B_le_H s.B_inf_Y).trans s.B_card5

theorem bar_A_card : Nat.card (s.bar s.A) = 31 ^ 2 :=
  (s.card_bar s.A_le_H s.A_inf_Y).trans s.A_card

theorem bar_A₁_inf_bar_A₂ : s.bar s.A₁ ⊓ s.bar s.A₂ = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨u, hu, rfl⟩ := (s.mem_bar_iff s.A₁_le_H).mp h1
  obtain ⟨v, hv, hvu⟩ := (s.mem_bar_iff s.A₂_le_H).mp h2
  have hEq : s.π (⟨u, s.A₁_le_H hu⟩ * (⟨v, s.A₂_le_H hv⟩ : ↥s.H)⁻¹) = 1 := by
    rw [map_mul, map_inv, hvu]
    simp
  have hY : u * v⁻¹ ∈ s.Y := by
    have hmem : (⟨u, s.A₁_le_H hu⟩ * (⟨v, s.A₂_le_H hv⟩ : ↥s.H)⁻¹) ∈ s.YH :=
      (s.eq_one_iff).mp hEq
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hA : u * v⁻¹ ∈ s.A :=
    s.A.mul_mem (s.A₁_le_A hu) (s.A.inv_mem (s.A₂_le_A hv))
  have hbot : u * v⁻¹ = 1 := by
    have hmem : u * v⁻¹ ∈ s.A ⊓ s.Y := ⟨hA, hY⟩
    rwa [s.A_inf_Y, Subgroup.mem_bot] at hmem
  have huv : u = v := by
    calc u = u * v⁻¹ * v := by group
      _ = v := by rw [hbot, one_mul]
  have hu2 : u ∈ s.A₂ := huv ▸ hv
  have hmem2 : u ∈ s.A₁ ⊓ s.A₂ := ⟨hu, hu2⟩
  rw [s.A₁_inf_A₂, Subgroup.mem_bot] at hmem2
  rw [Subgroup.mem_bot]
  have h1u : (⟨u, s.A₁_le_H hu⟩ : ↥s.H) = 1 := Subtype.ext hmem2
  rw [h1u, map_one]

theorem bar_A₁_le_centralizer_bar_A₂ :
    s.bar s.A₁ ≤ Subgroup.centralizer ((s.bar s.A₂ : Subgroup s.Q) : Set s.Q) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := (s.mem_bar_iff s.A₁_le_H).mp hz
  obtain ⟨v, hv, rfl⟩ := (s.mem_bar_iff s.A₂_le_H).mp hw
  have hcomm : (⟨v, s.A₂_le_H hv⟩ : ↥s.H) * ⟨u, s.A₁_le_H hu⟩ =
      ⟨u, s.A₁_le_H hu⟩ * ⟨v, s.A₂_le_H hv⟩ := by
    apply Subtype.ext
    exact (s.A₁_commute_A₂ u hu v hv).symm
  show s.π ⟨v, s.A₂_le_H hv⟩ * s.π ⟨u, s.A₁_le_H hu⟩ =
    s.π ⟨u, s.A₁_le_H hu⟩ * s.π ⟨v, s.A₂_le_H hv⟩
  rw [← map_mul, ← map_mul, hcomm]

theorem bar_A₁_sup_bar_A₂ : s.bar s.A₁ ⊔ s.bar s.A₂ = s.bar s.A := by
  calc s.bar s.A₁ ⊔ s.bar s.A₂
      = ((s.A₁.subgroupOf s.H) ⊔ (s.A₂.subgroupOf s.H)).map s.π :=
        (Subgroup.map_sup _ _ _).symm
    _ = ((s.A₁ ⊔ s.A₂).subgroupOf s.H).map s.π := by
        rw [Subgroup.subgroupOf_sup s.A₁_le_H s.A₂_le_H]
    _ = s.bar s.A := by rw [s.A₁_sup_A₂]; rfl

theorem bar_B_le_normalizer_bar_A₁ :
    s.bar s.B ≤ Subgroup.normalizer ((s.bar s.A₁ : Subgroup s.Q) : Set s.Q) :=
  CFSG.GroupTheory.map_subgroupOf_le_normalizer (M := s.H) s.π s.B_le_normalizer_A₁

theorem bar_B_le_normalizer_bar_A₂ :
    s.bar s.B ≤ Subgroup.normalizer ((s.bar s.A₂ : Subgroup s.Q) : Set s.Q) :=
  CFSG.GroupTheory.map_subgroupOf_le_normalizer (M := s.H) s.π s.B_le_normalizer_A₂

theorem bar_commutator : ⁅s.bar s.A, s.bar s.B⁆ = s.bar s.A := by
  have hsub := CFSG.GroupTheory.commutator_subgroupOf_eq s.A_le_H s.B_le_H
  calc ⁅s.bar s.A, s.bar s.B⁆
      = ⁅s.A.subgroupOf s.H, s.B.subgroupOf s.H⁆.map s.π := by
        rw [Subgroup.map_commutator]
        rfl
    _ = ((⁅s.A, s.B⁆).subgroupOf s.H).map s.π := by rw [hsub]
    _ = s.bar s.A := by rw [s.hAB]; rfl

theorem bar_A_eq_sup : s.bar s.A = s.bar s.A₁ ⊔ s.bar s.A₂ := s.bar_A₁_sup_bar_A₂.symm

@[expose] def Rbar : Subgroup s.Q := s.bar s.R

theorem Rbar_normal : s.Rbar.Normal := by
  have hRn : (s.R.subgroupOf s.H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer s.hRH).mpr s.hRn
  exact hRn.map s.π (QuotientGroup.mk'_surjective s.YH)

theorem Rbar_ne_bot : s.Rbar ≠ ⊥ := by
  intro h
  obtain ⟨r, hrR, hrY⟩ := SetLike.exists_of_lt s.hYR
  have hmem : s.π ⟨r, s.hRH hrR⟩ ∈ s.Rbar :=
    (s.mem_bar_iff s.hRH).mpr ⟨r, hrR, rfl⟩
  rw [h] at hmem
  have h1 : s.π ⟨r, s.hRH hrR⟩ = 1 := Subgroup.mem_bot.mp hmem
  have h2 : (⟨r, s.hRH hrR⟩ : ↥s.H) ∈ s.YH := (s.eq_one_iff).mp h1
  exact hrY (Subgroup.mem_subgroupOf.mp h2)

theorem Rbar_min {M : Subgroup s.Q} (hMn : M.Normal) (hMle : M ≤ s.Rbar) :
    M = ⊥ ∨ M = s.Rbar := by
  classical
  let W : Subgroup ↥s.H := M.comap s.π
  let W' : Subgroup G := W.map s.H.subtype
  have hWM : W.map s.π = M :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective s.YH) M
  have hWsub : W'.subgroupOf s.H = W := by
    ext x
    constructor
    · intro hx
      obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hx
      have hweq : w = x := Subtype.ext hwx
      rwa [← hweq]
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hW'leH : W' ≤ s.H := Subgroup.map_subtype_le W
  have hYW' : s.Y ≤ W' := by
    intro y hy
    refine Subgroup.mem_map.mpr ⟨⟨y, s.Y_le_H hy⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    have h1 : s.π ⟨y, s.Y_le_H hy⟩ = 1 :=
      (s.eq_one_iff).mpr (Subgroup.mem_subgroupOf.mpr hy)
    rw [h1]
    exact M.one_mem
  have hW'leR : W' ≤ s.R := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    have hMw : s.π w ∈ M := Subgroup.mem_comap.mp hw
    obtain ⟨r, hr, hpr⟩ := (s.mem_bar_iff s.hRH).mp (hMle hMw)
    have hmemY : ((w * (⟨r, s.hRH hr⟩ : ↥s.H)⁻¹ : ↥s.H) : G) ∈ s.Y := by
      have h1 : s.π (w * (⟨r, s.hRH hr⟩ : ↥s.H)⁻¹) = 1 := by
        rw [map_mul, map_inv, hpr]
        simp
      have h2 : (w * (⟨r, s.hRH hr⟩ : ↥s.H)⁻¹) ∈ s.YH := (s.eq_one_iff).mp h1
      simpa using Subgroup.mem_subgroupOf.mp h2
    have hRm : (w : G) * r⁻¹ ∈ s.R := s.hYR.le hmemY
    have heq : (w : G) = (w : G) * r⁻¹ * r := by group
    change (w : G) ∈ s.R
    rw [heq]
    exact s.R.mul_mem hRm hr
  have hW'n : s.H ≤ Subgroup.normalizer (W' : Set G) := by
    have hWn : W.Normal := hMn.comap s.π
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hW'leH).mp (hWsub ▸ hWn)
  rcases s.hminR W' hYW' hW'leR hW'n with h | h
  · left
    have hπ : (W'.subgroupOf s.H).map s.π = M := by rw [hWsub, hWM]
    rw [← hπ, h]
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [s.π_ker]
    exact hx
  · right
    have hπ : (W'.subgroupOf s.H).map s.π = M := by rw [hWsub, hWM]
    rw [← hπ, h]
    rfl

theorem Rbar_nonab : ∃ a ∈ s.Rbar, ∃ b ∈ s.Rbar, a * b ≠ b * a := by
  classical
  have hex : ∃ a ∈ s.R, ∃ b ∈ s.R, ⁅a, b⁆ ∉ s.Y := by
    by_contra h
    push Not at h
    exact s.hab (Subgroup.commutator_le.mpr h)
  obtain ⟨a, ha, b, hb, hab⟩ := hex
  refine ⟨s.π ⟨a, s.hRH ha⟩, (s.mem_bar_iff s.hRH).mpr ⟨a, ha, rfl⟩,
    s.π ⟨b, s.hRH hb⟩, (s.mem_bar_iff s.hRH).mpr ⟨b, hb, rfl⟩, ?_⟩
  intro hcomm
  apply hab
  have hmap : s.π ⁅(⟨a, s.hRH ha⟩ : ↥s.H), (⟨b, s.hRH hb⟩ : ↥s.H)⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_def, hcomm]
    group
  have hmem : ⁅(⟨a, s.hRH ha⟩ : ↥s.H), (⟨b, s.hRH hb⟩ : ↥s.H)⁆ ∈ s.YH :=
    (s.eq_one_iff).mp hmap
  have hval : ((⁅(⟨a, s.hRH ha⟩ : ↥s.H), (⟨b, s.hRH hb⟩ : ↥s.H)⁆ : ↥s.H) : G) = ⁅a, b⁆ := by
    rw [commutatorElement_def]
    rfl
  rw [← hval]
  exact Subgroup.mem_subgroupOf.mp hmem

open CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb in
theorem exists_factorization_Rbar :
    ∃ (r : ℕ) (S : Fin r → Subgroup s.Q),
      CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb.IsFactorization s.Rbar S :=
  exists_factorization s.Rbar_normal s.Rbar_ne_bot
    (fun M hMn hMle => s.Rbar_min hMn hMle) s.Rbar_nonab

theorem A_le_M : s.A ≤ D.M := by
  have hLM : s.L ≤ D.M := s13_le_of_mem_calC (by
    have h := s.h8100.1 0
    simpa using h)
  have hKM : conjSubgroup s.L s.x ≤ D.M := s13_le_of_mem_calC (by
    have h := s.h8100.1 1
    simpa using h)
  have hXprod : (s.X : Set G) = (s.L : Set G) * (conjSubgroup s.L s.x : Set G) := by
    simpa using s.h8100.2.2.2.2.2.2.2.2.1
  have hXM : s.X ≤ D.M := by
    intro z hz
    have hz' : z ∈ (s.L : Set G) * (conjSubgroup s.L s.x : Set G) := hXprod ▸ hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz'
    exact D.M.mul_mem (hLM ha) (hKM hb)
  exact s.hAsyl.le.trans hXM

theorem J_le_M : s.A ⊔ s.B ⊔ D.T ≤ D.M := sup_le (sup_le s.A_le_M s.hBM) D.sylowM.le

theorem R_not_le_M : ¬ s.R ≤ D.M := fun h =>
  (not_le_of_gt s.hYR) (le_kerM_of_normal s.hRH s.hRn h)

theorem H_le_MR : s.H ≤ (D.M ⊓ s.H) ⊔ s.R := by
  have hKle : (s.A ⊔ s.B ⊔ D.T) ⊔ s.R ≤ s.H := sup_le s.hD₀H s.hRH
  have hKnotM : ¬ (s.A ⊔ s.B ⊔ D.T) ⊔ s.R ≤ D.M :=
    fun hle => s.R_not_le_M (le_sup_right.trans hle)
  have hHeq : (s.A ⊔ s.B ⊔ D.T) ⊔ s.R = s.H := s.hmin _ le_sup_left hKle hKnotM
  calc s.H = (s.A ⊔ s.B ⊔ D.T) ⊔ s.R := hHeq.symm
    _ ≤ (D.M ⊓ s.H) ⊔ s.R := sup_le_sup_right (le_inf s.J_le_M s.hD₀H) s.R

@[expose] def Mbar : Subgroup s.Q := s.bar (D.M ⊓ s.H)

theorem Mbar_sup_Rbar : s.Mbar ⊔ s.Rbar = ⊤ := by
  refine le_antisymm le_top ?_
  intro z _
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective s.YH z
  have hh' : (h : G) ∈ (D.M ⊓ s.H) ⊔ s.R := s.H_le_MR h.2
  have hh : h ∈ ((D.M ⊓ s.H).subgroupOf s.H) ⊔ (s.R.subgroupOf s.H) := by
    rw [← Subgroup.subgroupOf_sup (inf_le_right : D.M ⊓ s.H ≤ s.H) s.hRH]
    exact hh'
  haveI : (s.R.subgroupOf s.H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer s.hRH).mpr s.hRn
  rw [Subgroup.mem_sup_of_normal_right] at hh
  obtain ⟨m, hm, r, hr, hmr⟩ := hh
  have hz : s.π h = s.π m * s.π r := by
    rw [← map_mul, hmr]
  change s.π h ∈ s.Mbar ⊔ s.Rbar
  rw [hz]
  exact (s.Mbar ⊔ s.Rbar).mul_mem
    (Subgroup.mem_sup_left ((s.mem_bar_iff (inf_le_right : D.M ⊓ s.H ≤ s.H)).mpr
      ⟨(m : G), Subgroup.mem_subgroupOf.mp hm, rfl⟩))
    (Subgroup.mem_sup_right ((s.mem_bar_iff s.hRH).mpr
      ⟨(r : G), Subgroup.mem_subgroupOf.mp hr, rfl⟩))

theorem mem_Mbar_of_centralizes {U : Subgroup G} (hU : U ∈ uniqueSet D.M)
    (hUH : U ≤ s.H)
    {q : s.Q} (hq : q ∈ Subgroup.centralizer ((s.bar U : Subgroup s.Q) : Set s.Q)) :
    q ∈ s.Mbar := by
  classical
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective s.YH q
  have hstar := hstar_of_inU D (inU_iff_mem_uniqueSet.mpr hU)
  have hnorm : ∀ u ∈ U, (h : G)⁻¹ * u * h ∈ D.M := by
    intro u hu
    have hub : s.π ⟨u, hUH hu⟩ ∈ s.bar U := (s.mem_bar_iff hUH).mpr ⟨u, hu, rfl⟩
    have hcent := (Subgroup.mem_centralizer_iff.mp hq) _ hub
    have hcomm : s.π ((⟨h, h.2⟩ : ↥s.H)⁻¹ * ⟨u, hUH hu⟩ * ⟨h, h.2⟩) =
        s.π ⟨u, hUH hu⟩ := by
      rw [map_mul, map_mul, map_inv]
      calc (s.π ⟨h, h.2⟩)⁻¹ * s.π ⟨u, hUH hu⟩ * s.π ⟨h, h.2⟩
          = (s.π ⟨h, h.2⟩)⁻¹ * (s.π ⟨u, hUH hu⟩ * s.π ⟨h, h.2⟩) := by group
        _ = (s.π ⟨h, h.2⟩)⁻¹ * (s.π ⟨h, h.2⟩ * s.π ⟨u, hUH hu⟩) :=
            congrArg (fun z => (s.π ⟨h, h.2⟩)⁻¹ * z) hcent
        _ = s.π ⟨u, hUH hu⟩ := by group
    have h1 : s.π (((⟨h, h.2⟩ : ↥s.H)⁻¹ * ⟨u, hUH hu⟩ * ⟨h, h.2⟩) *
        (⟨u, hUH hu⟩ : ↥s.H)⁻¹) = 1 := by
      rw [map_mul, map_inv, hcomm]
      simp
    have h2 : (((⟨h, h.2⟩ : ↥s.H)⁻¹ * ⟨u, hUH hu⟩ * ⟨h, h.2⟩) *
        (⟨u, hUH hu⟩ : ↥s.H)⁻¹) ∈ s.YH := (s.eq_one_iff).mp h1
    have h3 : ((((⟨h, h.2⟩ : ↥s.H)⁻¹ * ⟨u, hUH hu⟩ * ⟨h, h.2⟩) *
        (⟨u, hUH hu⟩ : ↥s.H)⁻¹ : ↥s.H) : G) ∈ s.Y := Subgroup.mem_subgroupOf.mp h2
    have h3' : ((h : G)⁻¹ * u * h) * u⁻¹ ∈ s.Y := by simpa using h3
    have hM : ((h : G)⁻¹ * u * h) * u⁻¹ ∈ D.M := s.Y_le_M h3'
    have huM : u ∈ D.M := hU.1 hu
    have heq : (h : G)⁻¹ * u * h = ((h : G)⁻¹ * u * h) * u⁻¹ * u := by group
    rw [heq]
    exact D.M.mul_mem hM huM
  have hhM : (h : G) ∈ D.M := hstar h hnorm
  exact (s.mem_bar_iff (inf_le_right : D.M ⊓ s.H ≤ s.H)).mpr
    ⟨(h : G), ⟨hhM, h.2⟩, rfl⟩

theorem mem_Mbar_of_normalizes {U W : Subgroup G} (hU : U ∈ uniqueSet D.M)
    (hUH : U ≤ s.H) (hUW : U ≤ W) (hWH : W ≤ s.H) (hWM : W ≤ D.M)
    {q : s.Q} (hq : q ∈ Subgroup.normalizer ((s.bar W : Subgroup s.Q) : Set s.Q)) :
    q ∈ s.Mbar := by
  classical
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective s.YH q
  have hstar := hstar_of_inU D (inU_iff_mem_uniqueSet.mpr hU)
  have hqinv : ((QuotientGroup.mk' s.YH) h)⁻¹ ∈
      Subgroup.normalizer ((s.bar W : Subgroup s.Q) : Set s.Q) :=
    (Subgroup.normalizer _).inv_mem hq
  have hnorm : ∀ u ∈ U, (h : G)⁻¹ * u * h ∈ D.M := by
    intro u hu
    have hub : s.π ⟨u, hUH hu⟩ ∈ s.bar W :=
      (s.mem_bar_iff hWH).mpr ⟨u, hUW hu, rfl⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hqinv (s.π ⟨u, hUH hu⟩)).mp hub
    have hconj' : ((QuotientGroup.mk' s.YH) h)⁻¹ * s.π ⟨u, hUH hu⟩ *
        (QuotientGroup.mk' s.YH) h ∈ s.bar W := by
      simpa only [inv_inv] using hconj
    have h1 : s.π ((⟨h, h.2⟩ : ↥s.H)⁻¹ * ⟨u, hUH hu⟩ * ⟨h, h.2⟩) ∈ s.bar W := by
      rw [map_mul, map_mul, map_inv]
      exact hconj'
    obtain ⟨w, hw, hwπ⟩ := (s.mem_bar_iff hWH).mp h1
    have hker : s.π (((⟨h, h.2⟩ : ↥s.H)⁻¹ * ⟨u, hUH hu⟩ * ⟨h, h.2⟩) *
        (⟨w, hWH hw⟩ : ↥s.H)⁻¹) = 1 := by
      rw [map_mul, map_inv, hwπ]
      simp
    have hmemY : ((((⟨h, h.2⟩ : ↥s.H)⁻¹ * ⟨u, hUH hu⟩ * ⟨h, h.2⟩) *
        (⟨w, hWH hw⟩ : ↥s.H)⁻¹ : ↥s.H) : G) ∈ s.Y :=
      Subgroup.mem_subgroupOf.mp ((s.eq_one_iff).mp hker)
    have hMY : (((h : G)⁻¹ * u * h) * w⁻¹) ∈ D.M := s.Y_le_M hmemY
    have heq : (h : G)⁻¹ * u * h = (((h : G)⁻¹ * u * h) * w⁻¹) * w := by group
    rw [heq]
    exact D.M.mul_mem hMY (hWM hw)
  have hhM : (h : G) ∈ D.M := hstar h hnorm
  exact (s.mem_bar_iff (inf_le_right : D.M ⊓ s.H ≤ s.H)).mpr
    ⟨(h : G), ⟨hhM, h.2⟩, rfl⟩

theorem bar_le_Mbar {U : Subgroup G} (hUH : U ≤ s.H) (hUM : U ≤ D.M) :
    s.bar U ≤ s.Mbar := by
  intro z hz
  obtain ⟨u, hu, rfl⟩ := (s.mem_bar_iff hUH).mp hz
  exact (s.mem_bar_iff (inf_le_right : D.M ⊓ s.H ≤ s.H)).mpr
    ⟨(u : G), ⟨hUM hu, hUH hu⟩, rfl⟩

theorem Tbar_isSylow : CFSG.ABGLocalTools.IsSylowOf 2 (s.bar D.T) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : CFSG.ABGLocalTools.IsSylowOf 2 D.T s.H :=
    D.sylowG.of_le s.T_le_H le_top
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf s.H) ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff s.H).mp ?_
    simpa [Subgroup.map_subgroupOf_eq_of_le s.T_le_H, Subgroup.map_top,
      Subgroup.range_subtype] using hTH
  have hmap := CFSG.RankThree.PartTwo.Sec12.IsSylowOf.map hTsyl s.π
  simpa [bar, Subgroup.map_top_of_surjective s.π (QuotientGroup.mk'_surjective s.YH)] using hmap

section Factor

variable {r : ℕ} {S : Fin r → Subgroup s.Q}

theorem factor_normal_in_Rbar (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    ((S i).subgroupOf s.Rbar).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (hFac.le i)).mpr (hFac.normal i)

theorem factor_isSubnormal (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    CFSG.Open.IsSubnormal (S i) ⊤ := by
  have hSR : CFSG.Open.IsSubnormal (S i) s.Rbar :=
    CFSG.Open.IsSubnormal.step (hFac.le i) (factor_normal_in_Rbar s hFac i)
      (CFSG.Open.IsSubnormal.refl s.Rbar)
  haveI : s.Rbar.Normal := s.Rbar_normal
  have hRbar : CFSG.Open.IsSubnormal s.Rbar ⊤ :=
    CFSG.Open.IsSubnormal.step le_top inferInstance (CFSG.Open.IsSubnormal.refl ⊤)
  exact CFSG.Open.IsSubnormal.trans hSR hRbar

theorem SL_isSylow (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    CFSG.ABGLocalTools.IsSylowOf 2 (s.bar D.T ⊓ S i) (S i) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact s.Tbar_isSylow.inf_of_isSubnormal (factor_isSubnormal s hFac i)

theorem SL_ne_bot (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    s.bar D.T ⊓ S i ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEven : Even (Nat.card ↥(S i)) :=
    CFSG.LocalAnalysis.ComponentInitial.even_card_of_simple_nonabelian
      (hFac.simple i) (hFac.nonab i)
  have h2dvd : 2 ∣ Nat.card ↥(S i) := hEven.two_dvd
  obtain ⟨Q, hQ⟩ := SL_isSylow s hFac i
  have hQne : (Q : Subgroup ↥(S i)) ≠ ⊥ := Q.ne_bot_of_dvd_card h2dvd
  intro hbot
  apply hQne
  rw [← hQ] at hbot
  exact le_bot_iff.mp (by simpa using (Subgroup.map_eq_bot_iff _).mp hbot)

theorem factor_not_le_Mbar (hFac : IsFactorization s.Rbar S) (i : Fin r) :
    ¬ S i ≤ s.Mbar := by
  classical
  intro hi
  haveI : s.Rbar.Normal := s.Rbar_normal
  have hconj : ∀ q : s.Q, cj q (S i) ≤ s.Mbar := by
    intro q
    have hq : q ∈ s.Mbar ⊔ s.Rbar := by rw [s.Mbar_sup_Rbar]; trivial
    rw [Subgroup.mem_sup_of_normal_right] at hq
    obtain ⟨m, hm, r, hr, hmr⟩ := hq
    subst hmr
    rw [cj_mul]
    have hLfix : cj r (S i) = S i :=
      cj_eq_of_mem_normalizer (hFac.normal i hr)
    rw [hLfix]
    intro z hz
    rw [mem_cj] at hz
    have hzM : m⁻¹ * z * m ∈ s.Mbar := hi hz
    have heq : z = m * (m⁻¹ * z * m) * m⁻¹ := by group
    rw [heq]
    exact s.Mbar.mul_mem (s.Mbar.mul_mem hm hzM) (s.Mbar.inv_mem hm)
  have hPleM : Subgroup.normalClosure ((S i : Subgroup s.Q) : Set s.Q) ≤ s.Mbar := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    obtain ⟨y, hy, hconj'⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj'
    rw [← hg]
    exact hconj g ((mem_cj (q := g) (T := S i)).mpr (by
      simpa [mul_assoc] using hy))
  have hPnorm : (Subgroup.normalClosure ((S i : Subgroup s.Q) : Set s.Q)).Normal :=
    Subgroup.normalClosure_normal
  have hPleR : Subgroup.normalClosure ((S i : Subgroup s.Q) : Set s.Q) ≤ s.Rbar :=
    Subgroup.normalClosure_le_normal (hFac.le i)
  have hPne : Subgroup.normalClosure ((S i : Subgroup s.Q) : Set s.Q) ≠ ⊥ := by
    intro hbot
    have hle : S i ≤ ⊥ := (Subgroup.le_normalClosure).trans (le_of_eq hbot)
    exact hFac.ne_bot i (le_bot_iff.mp hle)
  rcases s.Rbar_min hPnorm hPleR with h | h
  · exact hPne h
  ·
    have hRM : s.Rbar ≤ s.Mbar := h ▸ hPleM
    apply s.R_not_le_M
    intro r hr
    have hbar : s.π ⟨r, s.hRH hr⟩ ∈ s.Mbar := hRM ((s.mem_bar_iff s.hRH).mpr ⟨r, hr, rfl⟩)
    obtain ⟨x, hx, hxπ⟩ := (s.mem_bar_iff (inf_le_right : D.M ⊓ s.H ≤ s.H)).mp hbar
    have hker : s.π ((⟨x, hx.2⟩ : ↥s.H)⁻¹ * ⟨r, s.hRH hr⟩) = 1 := by
      rw [map_mul, map_inv, hxπ]
      simp
    have hmemY : (((⟨x, hx.2⟩ : ↥s.H)⁻¹ * ⟨r, s.hRH hr⟩ : ↥s.H) : G) ∈ s.Y :=
      Subgroup.mem_subgroupOf.mp ((s.eq_one_iff).mp hker)
    have hM' : (x : G)⁻¹ * r ∈ D.M := s.Y_le_M hmemY
    have heq : r = x * (x⁻¹ * r) := by group
    rw [heq]
    exact D.M.mul_mem hx.1 hM'

end Factor

end Data

end ChiefSetup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
