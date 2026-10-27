module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaFork
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrCoxOrder
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTypeA

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGNoReflFork {G : Type} [Group G] (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ¬ ∃ c₀ ∈ ggAutomizer X Bs, ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs,
      ∃ c₃ ∈ ggAutomizer X Bs, GGIsReflection p c₀ ∧ GGIsReflection p c₁ ∧
        GGIsReflection p c₂ ∧ GGIsReflection p c₃ ∧
        3 ∣ orderOf (c₀ * c₁) ∧ 3 ∣ orderOf (c₀ * c₂) ∧ 3 ∣ orderOf (c₀ * c₃) ∧
        2 ∣ orderOf (c₁ * c₂) ∧ 2 ∣ orderOf (c₁ * c₃) ∧ 2 ∣ orderOf (c₂ * c₃)

theorem not_commute_of_three_dvd_orderOf_coxRefl {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    {t t' : M.Group} {c c' : MulAut ↥Bs} (hc : c = ((e t : ↥A) : MulAut ↥Bs))
    (hc' : c' = ((e t' : ↥A) : MulAut ↥Bs)) (h2 : c * c = 1) (h2' : c' * c' = 1)
    (h3 : 3 ∣ orderOf (c * c')) : t * t' ≠ t' * t := by
  intro hcomm
  have hcc : c * c' = c' * c := by
    rw [hc, hc', ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm]
  have hsq : (c * c') ^ 2 = 1 := by
    calc (c * c') ^ 2 = c * c' * (c * c') := sq _
      _ = c * (c' * c) * c' := by simp only [mul_assoc]
      _ = c * (c * c') * c' := by rw [← hcc]
      _ = (c * c) * (c' * c') := by simp only [mul_assoc]
      _ = 1 := by rw [h2, h2', one_mul]
  have h32 : 3 ∣ 2 := h3.trans (orderOf_dvd_of_pow_eq_one hsq)
  omega

theorem commute_ne_of_two_dvd_orderOf_coxRefl {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A}
    {t t' : M.Group} {c c' : MulAut ↥Bs} (hc : c = ((e t : ↥A) : MulAut ↥Bs))
    (hc' : c' = ((e t' : ↥A) : MulAut ↥Bs)) (h2 : c * c = 1) (h2' : c' * c' = 1)
    (hord : (c * c') ^ 2 = 1 ∨ (c * c') ^ 3 = 1) (h2d : 2 ∣ orderOf (c * c')) :
    t * t' = t' * t ∧ t ≠ t' := by
  have hsq : (c * c') ^ 2 = 1 := by
    rcases hord with h | h
    · exact h
    · have h23 : 2 ∣ 3 := h2d.trans (orderOf_dvd_of_pow_eq_one h)
      omega
  refine ⟨?_, ?_⟩
  · apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ← hc']
    have h1 : (c * c')⁻¹ = c * c' := inv_eq_of_mul_eq_one_right (by simpa [sq] using hsq)
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h2'] at h1
    exact h1.symm
  · intro htt
    have hcc : c = c' := by rw [hc, hc', htt]
    rw [← hcc, h2, orderOf_one] at h2d
    omega

theorem ggX_fork_coxeter {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G}
    (hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦)
    {c₀ c₁ c₂ c₃ : MulAut ↥Bs} (hc₀ : c₀ ∈ ggAutomizer X Bs) (hc₁ : c₁ ∈ ggAutomizer X Bs)
    (hc₂ : c₂ ∈ ggAutomizer X Bs) (hc₃ : c₃ ∈ ggAutomizer X Bs) (hr₀ : GGIsReflection p c₀)
    (hr₁ : GGIsReflection p c₁) (hr₂ : GGIsReflection p c₂) (hr₃ : GGIsReflection p c₃)
    (h01 : 3 ∣ orderOf (c₀ * c₁)) (h02 : 3 ∣ orderOf (c₀ * c₂)) (h03 : 3 ∣ orderOf (c₀ * c₃))
    (h12 : 2 ∣ orderOf (c₁ * c₂)) (h13 : 2 ∣ orderOf (c₁ * c₃)) (h23 : 2 ∣ orderOf (c₂ * c₃)) :
    ∃ t₀ t₁ t₂ t₃ : M.Group,
      (∃ (w : M.Group) (i : ι), t₀ = w * M.simple i * w⁻¹) ∧
      (∃ (w : M.Group) (i : ι), t₁ = w * M.simple i * w⁻¹) ∧
      (∃ (w : M.Group) (i : ι), t₂ = w * M.simple i * w⁻¹) ∧
      (∃ (w : M.Group) (i : ι), t₃ = w * M.simple i * w⁻¹) ∧
      ((e t₀ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = c₀ ∧
      ((e t₁ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = c₁ ∧
      ((e t₂ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = c₂ ∧
      ((e t₃ : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = c₃ ∧
      t₁ * t₂ = t₂ * t₁ ∧ t₁ * t₃ = t₃ * t₁ ∧ t₂ * t₃ = t₃ * t₂ ∧
      t₁ ≠ t₂ ∧ t₁ ≠ t₃ ∧ t₂ ≠ t₃ ∧
      t₀ * t₁ ≠ t₁ * t₀ ∧ t₀ * t₂ ≠ t₂ * t₀ ∧ t₀ * t₃ ≠ t₃ * t₀ := by
  have hC : ∀ {c : MulAut ↥Bs}, c ∈ ggAutomizer X Bs → GGIsReflection p c →
      c ∈ ggCoxRefl M e := fun hc hr =>
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres hle3 (hle hc) hr
  have hsq : ∀ {c : MulAut ↥Bs}, GGIsReflection p c → c * c = 1 := fun hr => by
    simpa [sq] using hr.1
  have hord : ∀ {c c' : MulAut ↥Bs}, c ∈ ggCoxRefl M e → c' ∈ ggCoxRefl M e →
      (c * c') ^ 2 = 1 ∨ (c * c') ^ 3 = 1 := fun hc hc' =>
    ggCoxRefl_mul_orderOf_le_three hpres.1 hle3 hc hc'
  have hC₀ := hC hc₀ hr₀
  have hC₁ := hC hc₁ hr₁
  have hC₂ := hC hc₂ hr₂
  have hC₃ := hC hc₃ hr₃
  obtain ⟨w₀, i₀, hw₀⟩ := id hC₀
  obtain ⟨w₁, i₁, hw₁⟩ := id hC₁
  obtain ⟨w₂, i₂, hw₂⟩ := id hC₂
  obtain ⟨w₃, i₃, hw₃⟩ := id hC₃
  obtain ⟨h12c, hn12⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hw₁ hw₂ (hsq hr₁) (hsq hr₂)
    (hord hC₁ hC₂) h12
  obtain ⟨h13c, hn13⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hw₁ hw₃ (hsq hr₁) (hsq hr₃)
    (hord hC₁ hC₃) h13
  obtain ⟨h23c, hn23⟩ := commute_ne_of_two_dvd_orderOf_coxRefl hw₂ hw₃ (hsq hr₂) (hsq hr₃)
    (hord hC₂ hC₃) h23
  exact ⟨w₀ * M.simple i₀ * w₀⁻¹, w₁ * M.simple i₁ * w₁⁻¹, w₂ * M.simple i₂ * w₂⁻¹,
    w₃ * M.simple i₃ * w₃⁻¹, ⟨w₀, i₀, rfl⟩, ⟨w₁, i₁, rfl⟩, ⟨w₂, i₂, rfl⟩, ⟨w₃, i₃, rfl⟩,
    hw₀.symm, hw₁.symm, hw₂.symm, hw₃.symm, h12c, h13c, h23c, hn12, hn13, hn23,
    not_commute_of_three_dvd_orderOf_coxRefl hw₀ hw₁ (hsq hr₀) (hsq hr₁) h01,
    not_commute_of_three_dvd_orderOf_coxRefl hw₀ hw₂ (hsq hr₀) (hsq hr₂) h02,
    not_commute_of_three_dvd_orderOf_coxRefl hw₀ hw₃ (hsq hr₀) (hsq hr₃) h03⟩

theorem ggX_noReflFork_typeA {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) {m : ℕ} {σ : Fin m ≃ ι}
    (hM : M = (CoxeterMatrix.A m).reindex σ) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hle : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) :
    GGNoReflFork p Bs X := by
  rintro ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, hr₀, hr₁, hr₂, hr₃, h01, h02, h03, h12, h13,
    h23⟩
  obtain ⟨t₀, t₁, t₂, t₃, h₀, h₁, h₂, h₃, -, -, -, -, h12c, h13c, h23c, hn12, hn13, hn23, hn01,
    hn02, hn03⟩ :=
    ggX_fork_coxeter hcfg hpres hle3 hle hc₀ hc₁ hc₂ hc₃ hr₀ hr₁ hr₂ hr₃ h01 h02 h03 h12 h13 h23
  exact ggCoxFork_absurd_typeA hM h₀ h₁ h₂ h₃ h12c h13c h23c hn12 hn13 hn23 hn01 hn02 hn03

theorem ggX_row_absurd_of_noReflFork (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} (hF : GGRowFork S) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) (hNF : GGNoReflFork p Bs X)
    (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  exact hNF (ggX_exists_fork hRig hcfg hX hInn hΛ hhas (hF p hp hodd lab hΛ hS))

theorem ggX_row_absurd_of_noReflForkAt (hRig : GGLabelRigidInput)
    {S : ℕ → LargeEvenLabel → Prop} {r : ℕ} (hr3 : 3 ≤ r) (hF : GGRowForkAt S r)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X) (hNF : GGNoReflFork p Bs X)
    (hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), p ^ r ≤ Nat.card (ggGamma X hN).range)
    (hrow : GGInnerDiagOnLabel S p Bs X) : False := by
  obtain ⟨hp, hodd⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  exact hNF (ggX_exists_fork_of_card hRig hr3 hcfg.1.1 hInn hΛ hhas hrk
    (hF p hp hodd lab hΛ hS))

end CFSG.StandardType

end
