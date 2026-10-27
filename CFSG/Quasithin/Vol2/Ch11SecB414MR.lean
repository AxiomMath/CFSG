module

public import CFSG.Quasithin.Vol2.Ch11SecB414MQ
public import CFSG.Quasithin.Vol2.Ch11SecB414MN
public import CFSG.Quasithin.Vol2.Ch11SecB414MO

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]
  {Γ V Z L X : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F} (m : Model Γ V Z F k α)

omit [Finite F] [CharP F 2] in
theorem e01_mem_Wp :
    !![0, 1, 0; 0, 0, 0; 0, 0, 0] ∈ (Wp : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd ⟨rfl, by decide⟩ hij

omit [Finite F] [CharP F 2] in
theorem e12_mem_W3 :
    !![0, 0, 0; 0, 0, 1; 0, 0, 0] ∈ (W3 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [Finite F] [CharP F 2] in
theorem e10_mem_Wsl :
    !![0, 0, 0; 1, 0, 0; 0, 0, 0] ∈ (Wsl : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
  show Matrix.trace _ = 0
  simp [Matrix.trace_fin_three]

include m in
theorem Model.labSeries_twisted (hF : Nat.card F = 4) (hk3 : k < 3) (hk0 : k ≠ 0)
    (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ) (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {ν : Fˣ}
    (hν : ν ≠ 1)
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
    (α₀' : ↥(Ptheta F 0) →* ↥(StatedSL 2 F)) (α₀ : ↥L →* ↥(StatedSL 2 F))
    (hα₀s : Function.Surjective α₀)
    (hcomp : ∀ (l : ↥L) (γ : ↥Γ) (p : ↥(Ptheta F 0)), (γ : G) = l →
      (p : PGL3 F) = α γ → α₀ l = α₀' p)
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ (p : ↥(Ptheta F 0)) (v : Fin 2 → F),
      T (((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((α₀' p : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v)
    {γx : ↥Γ} {c : Fˣ} (hγx : α γx = ProjGenLinGroup.mk (dgHom c)) {μ : F}
    (hμ : ∀ w : Fin 2 → F, T ((c : F) • w) = μ • T w) :
    ∃ l : List (Subgroup G × Option F), IsLabSeries (L ⊔ X) L (γx : G) α₀ Z l V ∧
      labMultiset l = ({μ ^ (k + 1), μ ^ (2 * k), μ ^ (k + 2)} : Multiset F) := by
  obtain ⟨x₁, hx₁X, hx₁⟩ : ∃ x₁ : ↥Γ, (x₁ : G) ∈ X ∧ α x₁ = ProjGenLinGroup.mk (dgHom ν) := by
    have h : ProjGenLinGroup.mk (dgHom ν) ∈ (X.subgroupOf Γ).map α := by
      rw [hX]
      exact Subgroup.mem_zpowers _
    obtain ⟨x₁, hx₁, h1⟩ := h
    exact ⟨x₁, Subgroup.mem_subgroupOf.mp hx₁, h1⟩
  have hνk : ((ν : F)) ^ k ≠ 1 :=
    pow_ne_one_of_lt_three (pow_three_eq_one hF ν.ne_zero) (fun h => hν (Units.ext h)) hk3 hk0
  have hx₁Y : ∀ J : Subgroup G, L ⊔ X ≤ Subgroup.normalizer (J : Set G) →
      (x₁ : G) ∈ Subgroup.normalizer (J : Set G) := fun J hJ => hJ (le_sup_right (a := L) hx₁X)
  have hnat1 := m.natEig_Wp hF hLΓ hL α₀' α₀ hcomp T hT hγx hμ
  have hnat3 := m.natEig_W3 hF hLΓ hL α₀' α₀ hcomp T hT hγx hμ
  have hnat5 := m.natEig_Wsl hF hLΓ hL α₀' α₀ hcomp T hT hγx hμ
  have hYb := m.Y_le_bot hLΓ hXΓ hL hX
  have hYp := m.Y_le_Wp hLΓ hXΓ hL hX
  have hY2 := m.Y_le_W2 hLΓ hXΓ hL hX
  have hY3 := m.Y_le_W3 hLΓ hXΓ hL hX
  have hY4 := m.Y_le_W4 hLΓ hXΓ hL hX
  have hYs := m.Y_le_Wsl hLΓ hXΓ hL hX
  refine ⟨[(m.pre Wp, some (μ ^ (k + 1))), (m.pre W2, none), (m.pre W3, some (μ ^ (2 * k))),
    (m.pre W4, none), (m.pre Wsl, some (μ ^ (k + 2)))], ?_, rfl⟩
  suffices key : IsLabSeries (L ⊔ X) L (γx : G) α₀ (m.pre ⊥)
      [(m.pre Wp, some (μ ^ (k + 1))), (m.pre W2, none), (m.pre W3, some (μ ^ (2 * k))),
        (m.pre W4, none), (m.pre Wsl, some (μ ^ (k + 2)))] V by
    rwa [m.pre_bot] at key
  refine ⟨?_, ?_, ?_, ?_, ?_, m.pre_Wsl⟩
  · refine m.isLabFactor_pre bot_le e01_mem_Wp (by simp [Matrix.trace_fin_three])
      (fun h => by
        have := congrFun (congrFun (AddSubgroup.mem_bot.mp h) 0) 1
        exact one_ne_zero (this : (1 : F) = 0)) hYb hYp
      (fun J h1 h2 _ hYJ => hnat1.eq_or_eq le_rfl hα₀s (le_sup_left.trans hYp) h1 h2
        (le_sup_left.trans hYJ)) hnat1
  · refine m.isLabFactor_pre (Wp_le_W2a.trans W2a_le_W2) hatI_mem_W2 hatI_trace
      (fun h => by simpa [hatI] using (h : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → _) 1 1 (by simp))
      hYp hY2 (fun J h1 h2 _ hYJ => m.min_scalar_diag hF (d := ![0, 1, 1])
        (fun M hM => ⟨M 1 1, sub_hatI_mem_Wp hM⟩) (fun c M hM => Wp_dg k c hM) hx₁ hνk h1 h2
        (hx₁Y J hYJ)) ?_
    exact m.comm_mem_pre_L hLΓ hL (fun A h10 h20 hdet M hM => W2_cnj_sub h10 h20 hdet hM)
  · refine m.isLabFactor_pre W2_le_W3 e12_mem_W3 (by simp [Matrix.trace_fin_three])
      (fun h => by simpa using h.2.2.2.1) hY2 hY3
      (fun J h1 h2 _ hYJ => hnat3.eq_or_eq le_rfl hα₀s (le_sup_left.trans hY3) h1 h2
        (le_sup_left.trans hYJ)) hnat3
  · refine m.isLabFactor_pre (W3_le_W4a.trans W4a_le_W4) dD_mem_W4 dD_mem_W4.1
      (fun h => by simpa [dD] using h.1) hY3 hY4
      (fun J h1 h2 _ hYJ => m.min_scalar_diag hF (d := ![1, 1, 0])
        (fun M hM => ⟨M 0 0, sub_dD_mem_W3 hM⟩) (fun c M hM => W3_dg k c hM) hx₁ hνk h1 h2
        (hx₁Y J hYJ)) ?_
    exact m.comm_mem_pre_L hLΓ hL (fun A h10 h20 hdet M hM => W4_cnj_sub h10 h20 hdet hM)
  · refine m.isLabFactor_pre W4_le_Wsl e10_mem_Wsl e10_mem_Wsl
      (fun h => by simpa using h.2.1) hY4 hYs
      (fun J h1 h2 _ hYJ => hnat5.eq_or_eq le_rfl hα₀s (le_sup_left.trans hYs) h1 h2
        (le_sup_left.trans hYJ)) hnat5

omit m in
theorem Model.labSeries_untwisted (m : Model Γ V Z F 0 α) (hF : Nat.card F = 4)
    (hLΓ : L ≤ Γ) (hXΓ : X ≤ Γ) (hL : (L.subgroupOf Γ).map α = Ptheta F 0) {ν : Fˣ}
    (hν : ν ≠ 1)
    (hX : (X.subgroupOf Γ).map α = Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)))
    (α₀' : ↥(Ptheta F 0) →* ↥(StatedSL 2 F)) (α₀ : ↥L →* ↥(StatedSL 2 F))
    (hα₀s : Function.Surjective α₀)
    (hcomp : ∀ (l : ↥L) (γ : ↥Γ) (p : ↥(Ptheta F 0)), (γ : G) = l →
      (p : PGL3 F) = α γ → α₀ l = α₀' p)
    (T : (Fin 2 → F) ≃+ (Fin 2 → F))
    (hT : ∀ (p : ↥(Ptheta F 0)) (v : Fin 2 → F),
      T (((rhoRef hF p : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (((α₀' p : StatedSL 2 F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ T v)
    {γx : ↥Γ} {c : Fˣ} (hγx : α γx = ProjGenLinGroup.mk (dgHom c)) {μ : F}
    (hμ : ∀ w : Fin 2 → F, T ((c : F) • w) = μ • T w) :
    ∃ l : List (Subgroup G × Option F), IsLabSeries (L ⊔ X) L (γx : G) α₀ Z l V ∧
      labMultiset l = ({μ ^ (0 + 1), μ ^ (2 * 0), μ ^ (0 + 2)} : Multiset F) := by
  have hnat1 := m.natEig_Wp hF hLΓ hL α₀' α₀ hcomp T hT hγx hμ
  have hnat3 := m.natEig_W3 hF hLΓ hL α₀' α₀ hcomp T hT hγx hμ
  have hnat5 := m.natEig_Wsl hF hLΓ hL α₀' α₀ hcomp T hT hγx hμ
  have hYb := m.Y_le_bot hLΓ hXΓ hL hX
  have hYp := m.Y_le_Wp hLΓ hXΓ hL hX
  have hY2a := m.Y_le_W2a hLΓ hXΓ hL hX
  have hY2 := m.Y_le_W2 hLΓ hXΓ hL hX
  have hY3 := m.Y_le_W3 hLΓ hXΓ hL hX
  have hY4a := m.Y_le_W4a hLΓ hXΓ hL hX
  have hY4 := m.Y_le_W4 hLΓ hXΓ hL hX
  have hYs := m.Y_le_Wsl hLΓ hXΓ hL hX
  have hν1 : (ν : F) ≠ 1 := fun h => hν (Units.ext h)
  have hν0 : (ν : F) ≠ 0 := ν.ne_zero
  refine ⟨[(m.pre Wp, some (μ ^ (0 + 1))), (m.pre W2a, none), (m.pre W2, none),
    (m.pre W3, some (μ ^ (2 * 0))), (m.pre W4a, none), (m.pre W4, none),
    (m.pre Wsl, some (μ ^ (0 + 2)))], ?_, rfl⟩
  suffices key : IsLabSeries (L ⊔ X) L (γx : G) α₀ (m.pre ⊥)
      [(m.pre Wp, some (μ ^ (0 + 1))), (m.pre W2a, none), (m.pre W2, none),
        (m.pre W3, some (μ ^ (2 * 0))), (m.pre W4a, none), (m.pre W4, none),
        (m.pre Wsl, some (μ ^ (0 + 2)))] V by
    rwa [m.pre_bot] at key
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, m.pre_Wsl⟩
  · refine m.isLabFactor_pre bot_le e01_mem_Wp (by simp [Matrix.trace_fin_three])
      (fun h => by
        have := congrFun (congrFun (AddSubgroup.mem_bot.mp h) 0) 1
        exact one_ne_zero (this : (1 : F) = 0)) hYb hYp
      (fun J h1 h2 _ hYJ => hnat1.eq_or_eq le_rfl hα₀s (le_sup_left.trans hYp) h1 h2
        (le_sup_left.trans hYJ)) hnat1
  · refine m.isLabFactor_pre Wp_le_W2a ⟨hatI_mem_W2, Or.inr (by simp [hatI])⟩ hatI_trace
      (fun h => by simpa [hatI] using (h : ∀ i j : Fin 3, ¬ (i = 0 ∧ j ≠ 0) → _) 1 1 (by simp))
      hYp hY2a (fun J h1 h2 _ _ => m.min_Wp_W2a h1 h2) ?_
    exact m.comm_mem_pre_L hLΓ hL (fun A h10 h20 hdet M hM => W2_cnj_sub h10 h20 hdet hM.1)
  · have hI : (ν : F) • hatI F ∈ (W2 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hatI]
    refine m.isLabFactor_pre W2a_le_W2 hI (by rw [Matrix.trace_smul, hatI_trace, smul_zero])
      (fun h => by
        rcases h.2 with h' | h' <;> simp [hatI, hν0, hν1] at h') hY2a hY2
      (fun J h1 h2 _ _ => m.min_W2a_W2 hF hν h1 h2) ?_
    exact m.comm_mem_pre_L hLΓ hL (fun A h10 h20 hdet M hM =>
      Wp_le_W2a (W2_cnj_sub h10 h20 hdet hM))
  · refine m.isLabFactor_pre W2_le_W3 e12_mem_W3 (by simp [Matrix.trace_fin_three])
      (fun h => by simpa using h.2.2.2.1) hY2 hY3
      (fun J h1 h2 _ hYJ => hnat3.eq_or_eq le_rfl hα₀s (le_sup_left.trans hY3) h1 h2
        (le_sup_left.trans hYJ)) hnat3
  · refine m.isLabFactor_pre W3_le_W4a ⟨dD_mem_W4, Or.inr (by simp [dD])⟩ dD_mem_W4.1
      (fun h => by simpa [dD] using h.1) hY3 hY4a (fun J h1 h2 _ _ => m.min_W3_W4a h1 h2) ?_
    exact m.comm_mem_pre_L hLΓ hL (fun A h10 h20 hdet M hM => W4_cnj_sub h10 h20 hdet hM.1)
  · have hD : (ν : F) • dD F ∈ (W4 : AddSubgroup (Matrix (Fin 3) (Fin 3) F)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Matrix.trace_smul, (dD_mem_W4 (F := F)).1, smul_zero]
      · simp [dD]
      · simp [dD]
    refine m.isLabFactor_pre W4a_le_W4 hD hD.1
      (fun h => by
        rcases h.2 with h' | h' <;> simp [dD, hν0, hν1] at h') hY4a hY4
      (fun J h1 h2 _ _ => m.min_W4a_W4 hF hν h1 h2) ?_
    exact m.comm_mem_pre_L hLΓ hL (fun A h10 h20 hdet M hM =>
      W3_le_W4a (W4_cnj_sub h10 h20 hdet hM))
  · refine m.isLabFactor_pre W4_le_Wsl e10_mem_Wsl e10_mem_Wsl
      (fun h => by simpa using h.2.1) hY4 hYs
      (fun J h1 h2 _ hYJ => hnat5.eq_or_eq le_rfl hα₀s (le_sup_left.trans hYs) h1 h2
        (le_sup_left.trans hYJ)) hnat5

end CFSG.Quasithin.H13.Ch4.B414.M
