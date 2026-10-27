module

public import CFSG.Timmesfeld.Bridge.RootSetsConn17

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem mul_mul_mul_eq {d t₃ b₁ t₁ b₂ t₂ : G} (h31 : Commute t₃ b₁) (h32 : Commute t₃ t₁)
    (h33 : Commute t₃ b₂) (h34 : Commute t₃ t₂) (h12 : Commute t₁ b₂) :
    d * t₃ * (b₁ * t₁) * (b₂ * t₂) = d * b₁ * b₂ * (t₁ * t₂ * t₃) := by
  have h3 : Commute t₃ (b₁ * t₁ * (b₂ * t₂)) :=
    (h31.mul_right h32).mul_right (h33.mul_right h34)
  calc d * t₃ * (b₁ * t₁) * (b₂ * t₂) = d * (t₃ * (b₁ * t₁ * (b₂ * t₂))) := by group
    _ = d * (b₁ * t₁ * (b₂ * t₂) * t₃) := by rw [h3.eq]
    _ = d * (b₁ * (t₁ * b₂) * t₂ * t₃) := by group
    _ = d * (b₁ * (b₂ * t₁) * t₂ * t₃) := by rw [h12.eq]
    _ = d * b₁ * b₂ * (t₁ * t₂ * t₃) := by group

namespace Step6

variable {a b c x z : G} {P : Subgroup G}

theorem threeClasses_of_psl2 (hB : OddTranspBender) (hC : ConnCex D) (h : Step6 D a b c x z P)
    (hL2 : ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (lsub D x P ⧸ CFSG.solvableRadical (lsub D x P) ≃* CFSG.Theory.Comparator.PSL2Model m)) :
    ThreeClasses D x P := by
  have hD := hC.setting.root
  have h3 := step6ThreeProductHyp hB OddTransp.oddTranspThirdKind
  intro e₁ he₁ he₁P e₂ he₂ he₂P h12 ℓ hℓ hℓP
  by_contra hne
  push Not at hne
  obtain ⟨hℓ₁, hℓ₂, hℓ₁₂⟩ := hne
  obtain ⟨f, hf, hfN, hfP, hfe⟩ := h.exists_mem_normalizer_commute hB h3 hC he₁ he₁P
  have hS := h.isPGroup_sup_zpowers hC hf hfN
  have hfS : f ∈ (P ⊔ Subgroup.zpowers f : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have h5 : ∀ u ∈ D, u ∈ P → e₁ * u ∉ qcore D x P → ¬ Commute f u := fun u hu huP hq hfu =>
    hfP (h.mem_of_commute_of_mul_not_mem hB h3 hC hL2 hS le_sup_left he₁ hu he₁P huP hq hf hfS
      hfe hfu)
  have hact : ∀ u ∈ D, u ∈ P → e₁ * u ∉ qcore D x P →
      u * (f * u * f⁻¹) ∈ D ∧ u * (f * u * f⁻¹) ∈ P ∧
        e₁ * (u * (f * u * f⁻¹)) ∈ qcore D x P := by
    intro u hu huP hq
    obtain ⟨htD, htP, hft⟩ := h.mul_conj_mem hC hf hfN hu huP (h5 u hu huP hq)
    exact ⟨htD, htP, Classical.byContradiction fun hq' => h5 _ htD htP hq' hft⟩
  have hconj : ∀ u ∈ D, f * u * f⁻¹ = u * (u * (f * u * f⁻¹)) := fun u hu => by
    rw [← mul_assoc, hD.mul_self_eq_one hu, one_mul]
  have h2ℓ : e₂ * ℓ ∉ qcore D x P := fun hq => hℓ₂ (mul_mem_qcore_comm hC he₂ hℓ hq)
  obtain ⟨d, hd, hdP, w, hw, hdw⟩ := h.exists_eq_mul_of_mem hB h3 hC (P.mul_mem he₂P hℓP) h2ℓ
  have hwQ : w ∈ qcore D x P := zcore_le_qcore hw
  have hd1 : e₁ * d ∉ qcore D x P := by
    intro hq
    apply hℓ₁₂
    have hc : Commute ℓ (e₁ * e₂) := (h.commute_of_mem hC hℓ he₁ hℓP he₁P).mul_right
      (h.commute_of_mem hC hℓ he₂ hℓP he₂P)
    rw [show ℓ * e₁ * e₂ = e₁ * d * w by
      rw [mul_assoc ℓ e₁ e₂, hc.eq, mul_assoc e₁ e₂ ℓ, hdw, ← mul_assoc]]
    exact (qcore D x P).mul_mem hq hwQ
  obtain ⟨ht₁D, ht₁P, ht₁⟩ := hact e₂ he₂ he₂P h12
  obtain ⟨ht₂D, ht₂P, ht₂⟩ := hact ℓ hℓ hℓP fun hq => hℓ₁ (mul_mem_qcore_comm hC he₁ hℓ hq)
  obtain ⟨ht₃D, ht₃P, -⟩ := hact d hd hdP hd1
  set t₁ := e₂ * (f * e₂ * f⁻¹) with ht₁def
  set t₂ := ℓ * (f * ℓ * f⁻¹) with ht₂def
  set t₃ := d * (f * d * f⁻¹) with ht₃def
  have hwf : f * w * f⁻¹ ∈ qcore D x P :=
    mcore_le_qcore (h.conj_mem_mcore hB h3 hC hfN (h.zcore_le_mcore hB hC hw))
  have hw' : w = d * e₂ * ℓ := by
    rw [mul_assoc d e₂ ℓ, hdw, ← mul_assoc, hD.mul_self_eq_one hd, one_mul]
  have hcm : ∀ {u v : G}, u ∈ D → v ∈ D → u ∈ P → v ∈ P → Commute u v :=
    fun hu hv huP hvP => h.commute_of_mem hC hu hv huP hvP
  have hwf' : f * w * f⁻¹ = w * (t₁ * t₂ * t₃) := by
    rw [hw', show f * (d * e₂ * ℓ) * f⁻¹ = f * d * f⁻¹ * (f * e₂ * f⁻¹) * (f * ℓ * f⁻¹) by group,
      hconj d hd, hconj e₂ he₂, hconj ℓ hℓ]
    exact mul_mul_mul_eq (hcm ht₃D he₂ ht₃P he₂P) (hcm ht₃D ht₁D ht₃P ht₁P)
      (hcm ht₃D hℓ ht₃P hℓP) (hcm ht₃D ht₂D ht₃P ht₂P) (hcm ht₁D hℓ ht₁P hℓP)
  have h123 : t₁ * t₂ * t₃ ∈ qcore D x P := by
    have := (qcore D x P).mul_mem ((qcore D x P).inv_mem hwQ) hwf
    rwa [hwf', inv_mul_cancel_left] at this
  have h12' : t₁ * t₂ ∈ qcore D x P :=
    mul_mem_qcore_trans hC he₁ (mul_mem_qcore_comm hC he₁ ht₁D ht₁) ht₂
  have := (qcore D x P).mul_mem ((qcore D x P).inv_mem h12') h123
  rw [inv_mul_cancel_left] at this
  exact h.not_mem_qcore hC ht₃D this

end Step6

end CFSG.Timmesfeld.Bridge
