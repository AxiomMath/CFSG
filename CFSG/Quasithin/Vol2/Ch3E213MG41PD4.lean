module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PD3
public import CFSG.Quasithin.Vol2.Ch3E213MG41PC

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {k : Type} [Field k] [CharP k 2]

@[expose] def cenT (G₀ : Subgroup (antiSp k)) : Set (Fin 4 → k) :=
  {z | z ∈ Refl.normC G₀ ∧ z 2 = 0}

theorem cenT_two {G₀ : Subgroup (antiSp k)} : ∀ z ∈ cenT G₀, z 2 = 0 :=
  fun _ hz => hz.2

@[expose] def CaseA (G₀ : Subgroup (antiSp k)) : Prop :=
  (∃ z : ℕ, 3 ≤ z ∧ Odd z ∧ Nat.card (secGrp (cenT G₀)) = 2 * z ∧
    Nonempty (secGrp (cenT G₀) ≃* DihedralGroup z)) ∨ Nat.card (secGrp (cenT G₀)) = 6

theorem mem_of_sq_mem [Finite k] (F : Subfield k) {x : k} (hx : x ^ 2 ∈ F) : x ∈ F := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hinj : Function.Injective (fun y : F => y ^ 2) := by
    intro a b hab
    have hab' : (a : k) ^ 2 = (b : k) ^ 2 := by simpa using congrArg Subtype.val hab
    apply Subtype.ext
    have h0 : ((a : k) - b) ^ 2 = 0 := by
      linear_combination hab' + ((b : k) ^ 2 - a * b) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinj ⟨x ^ 2, hx⟩
  have hy' : (y : k) ^ 2 = x ^ 2 := by simpa using congrArg Subtype.val hy
  have h0 : ((y : k) - x) ^ 2 = 0 := by
    linear_combination hy' + (x ^ 2 - y * x) * h2
  rw [← sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)]
  exact y.2

theorem bil_mem_of_trv_mem [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) {H : Subgroup (antiSp k)} {F : Subfield k}
    {v p : Fin 4 → k} (hF : (Lam H v : Set k) = F) (h4 : 4 ≤ Nat.card (Lam H v))
    (hp : trv p 1 ∈ H) : spBil v p ∈ F := by
  set β := spBil v p with hβ
  by_cases hβ0 : β = 0
  · rw [hβ0]
    exact F.zero_mem
  have h1 : (1 : k) ∈ Lam H v := by
    have h : (1 : k) ∈ (F : Set k) := F.one_mem
    rw [← hF] at h
    exact h
  have hvp : spBil v (β⁻¹ • p) = 1 := by
    rw [map_smul, smul_eq_mul, ← hβ, inv_mul_cancel₀ hβ0]
  have hpL : β ^ 2 * 1 ∈ Lam H (β⁻¹ • p) := by
    rw [mem_Lam, ← trv_smul, smul_smul, mul_inv_cancel₀ hβ0, one_smul]
    exact hp
  obtain ⟨F₀, hv0, hp0⟩ := pair_lemma hk hvp h1 h4 (mul_ne_zero (pow_ne_zero 2 hβ0) one_ne_zero)
    hpL
  have h : β ^ 2 * 1 ∈ (F : Set k) := by
    rw [← hF, hv0, ← hp0]
    exact hpL
  rw [mul_one] at h
  exact mem_of_sq_mem F h

theorem eq_bil_smul_add {v w p : Fin 4 → k} (hv : v 1 = 0 ∧ v 2 = 0) (hw : w 1 = 0 ∧ w 2 = 0)
    (hp : p 1 = 0 ∧ p 2 = 0) (hvw : spBil v w = 1) : p = spBil w p • v + spBil v p • w := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [bil_apply, hv.1, hv.2, hw.1, hw.2] at hvw
  funext i
  fin_cases i
  · simp [bil_apply, hv.1, hv.2, hw.1, hw.2, hp.1, hp.2]
    linear_combination (-p 0) * hvw - (v 0 * w 0 * p 3) * h2
  · simp [hv.1, hw.1, hp.1]
  · simp [hv.2, hw.2, hp.2]
  · simp [bil_apply, hv.1, hv.2, hw.1, hw.2, hp.1, hp.2]
    linear_combination (-p 3) * hvw - (v 3 * w 3 * p 0) * h2

theorem act_trv_frame {v w : Fin 4 → k} (hvw : spBil v w = 1) (c d : k) :
    natAct (trv v c) (v + d • w) = (1 + c * d) • v + d • w := by
  have hwv : spBil w v = 1 := by rw [bil_symm]; exact hvw
  rw [act_trv, LinearMap.map_add₂, LinearMap.map_smul₂, bil_self, hwv]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_act_eq {H : Subgroup (antiSp k)} {F : Subfield k} {v w : Fin 4 → k}
    (hvw : spBil v w = 1) (hv : ∀ c ∈ F, trv v c ∈ H) (hw : ∀ c ∈ F, trv w c ∈ H) {a b : k}
    (ha : a ∈ F) (hb : b ∈ F) (hab : a ≠ 0 ∨ b ≠ 0) : ∃ h ∈ H, natAct h v = a • v + b • w := by
  have hwv : spBil w v = 1 := by rw [bil_symm]; exact hvw
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have e1 : ∀ c : k, natAct (trv w c) v = v + c • w := fun c => by rw [act_trv, hvw, mul_one]
  by_cases hb0 : b = 0
  · subst hb0
    have ha0 : a ≠ 0 := hab.resolve_right (not_not.mpr rfl)
    refine ⟨trv w a⁻¹ * trv v a * trv v 1 * trv w 1, H.mul_mem (H.mul_mem (H.mul_mem
      (hw _ (F.inv_mem ha)) (hv a ha)) (hv 1 F.one_mem)) (hw 1 F.one_mem), ?_⟩
    have e2 : natAct (trv v 1) (v + (1 : k) • w) = w := by
      rw [act_trv_frame hvw]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination v i * h2
    have e3 : natAct (trv v a) w = w + a • v := by rw [act_trv, hwv, mul_one]
    have e4 : natAct (trv w a⁻¹) (w + a • v) = a • v := by
      rw [act_trv_frame hwv, inv_mul_cancel₀ ha0]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination w i * h2
    rw [natAct_mul, natAct_mul, natAct_mul, e1, e2, e3, e4, zero_smul, add_zero]
  · refine ⟨trv v ((a + 1) * b⁻¹) * trv w b,
      H.mul_mem (hv _ (F.mul_mem (F.add_mem ha F.one_mem) (F.inv_mem hb))) (hw b hb), ?_⟩
    have hcoef : 1 + (a + 1) * b⁻¹ * b = a := by
      rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
      linear_combination h2
    rw [natAct_mul, e1, act_trv_frame hvw, hcoef]

theorem exists_act_eq_of_mem {H : Subgroup (antiSp k)} {F : Subfield k} {v w : Fin 4 → k}
    (hvw : spBil v w = 1) (hv : ∀ c ∈ F, trv v c ∈ H) (hw : ∀ c ∈ F, trv w c ∈ H)
    {α β a b : k} (hα : α ∈ F) (hβ : β ∈ F) (hαβ : α ≠ 0 ∨ β ≠ 0) (ha : a ∈ F) (hb : b ∈ F)
    (hab : a ≠ 0 ∨ b ≠ 0) : ∃ h ∈ H, natAct h (α • v + β • w) = a • v + b • w := by
  obtain ⟨h₁, hh₁, e₁⟩ := exists_act_eq hvw hv hw hα hβ hαβ
  obtain ⟨h₂, hh₂, e₂⟩ := exists_act_eq hvw hv hw ha hb hab
  exact ⟨h₂ * h₁⁻¹, H.mul_mem hh₂ (H.inv_mem hh₁), by rw [natAct_mul, ← e₁, act_inv_act, e₂]⟩

theorem exists_mem_of_secGrp {G₀ : Subgroup (antiSp k)} {h : antiSp k}
    (hh : h ∈ secGrp (cenT G₀)) {z : Fin 4 → k} (hz : z 2 = 0) :
    ∃ g ∈ G₀, natAct g (eOne k) = eOne k ∧ proj (natAct g z) = natAct h (proj z) := by
  obtain ⟨g, hg, rfl, hproj⟩ := exists_lift hh
  exact ⟨g, liftGrp_le (fun z hz => hz.1.2) hg, g.2, hproj z hz⟩

theorem caseB_of_four [Finite k]
    {n : ℕ} (hk : Nat.card k = 2 ^ n) {G₀ : Subgroup (antiSp k)} {z₁ z₂ : Fin 4 → k}
    (hz₁ : z₁ ∈ cenT G₀) (hz₂ : z₂ ∈ cenT G₀) (hc : spBil (proj z₁) (proj z₂) ≠ 0)
    (h4 : 4 ≤ Nat.card (Lam (secGrp (cenT G₀)) (proj z₁))) :
    ∃ F₁ : Subfield k, CaseB G₀ F₁ (proj z₁) ((spBil (proj z₁) (proj z₂))⁻¹ • proj z₂) := by
  set H := secGrp (cenT G₀) with hH
  set c := spBil (proj z₁) (proj z₂) with hcdef
  set w := c⁻¹ • proj z₂ with hw
  have hvw : spBil (proj z₁) w = 1 := by
    rw [hw, map_smul, smul_eq_mul, ← hcdef, inv_mul_cancel₀ hc]
  have h1 : (1 : k) ∈ Lam H (proj z₁) := trv_proj_mem_secGrp cenT_two hz₁
  have hwL : c ^ 2 ∈ Lam H w := by
    have h := trv_proj_mem_secGrp cenT_two hz₂
    rwa [show proj z₂ = c • w by rw [hw, smul_smul, mul_inv_cancel₀ hc, one_smul], trv_smul,
      mul_one] at h
  obtain ⟨F₁, hFv, hFw⟩ := pair_lemma hk hvw h1 h4 (pow_ne_zero 2 hc) hwL
  have hcv : Nat.card F₁ = Nat.card (Lam H (proj z₁)) :=
    (Nat.card_congr (Set.equivOfEq hFv)).symm
  have hcw : Nat.card F₁ = Nat.card (Lam H w) := (Nat.card_congr (Set.equivOfEq hFw)).symm
  have h4w : 4 ≤ Nat.card (Lam H w) := by
    rw [← hcw, hcv]
    exact h4
  have hv' : ∀ a ∈ F₁, trv (proj z₁) a ∈ H := fun a ha => by
    have h : a ∈ (Lam H (proj z₁) : Set k) := by rw [hFv]; exact ha
    exact h
  have hw' : ∀ a ∈ F₁, trv w a ∈ H := fun a ha => by
    have h : a ∈ (Lam H w : Set k) := by rw [hFw]; exact ha
    exact h
  have hsv : proj z₁ 1 = 0 ∧ proj z₁ 2 = 0 := by simp [proj]
  have hsw : w 1 = 0 ∧ w 2 = 0 := by simp [hw, proj]
  have himage : ∀ z ∈ Refl.normC G₀, z 2 = 0 → proj z ≠ 0 →
      ∃ a ∈ F₁, ∃ b ∈ F₁, proj z = a • proj z₁ + b • w := by
    intro z hz hz2 _
    have hp : trv (proj z) 1 ∈ H := trv_proj_mem_secGrp cenT_two ⟨hz, hz2⟩
    exact ⟨_, bil_mem_of_trv_mem hk hFw h4w hp, _, bil_mem_of_trv_mem hk hFv h4 hp,
      eq_bil_smul_add hsv hsw (by simp [proj]) hvw⟩
  have htrans : ∀ z ∈ Refl.normC G₀, z 2 = 0 → proj z ≠ 0 → ∀ a ∈ F₁, ∀ b ∈ F₁,
      (a ≠ 0 ∨ b ≠ 0) → ∃ g ∈ G₀, natAct g (eOne k) = eOne k ∧
        proj (natAct g z) = a • proj z₁ + b • w := by
    intro z hz hz2 hpz a ha b hb hab
    obtain ⟨α, hα, β, hβ, hzαβ⟩ := himage z hz hz2 hpz
    have hαβ : α ≠ 0 ∨ β ≠ 0 := by
      by_contra hcon
      obtain ⟨hα0, hβ0⟩ := not_or.mp hcon
      apply hpz
      rw [hzαβ, not_not.mp hα0, not_not.mp hβ0, zero_smul, zero_smul, add_zero]
    obtain ⟨h, hh, he⟩ := exists_act_eq_of_mem hvw hv' hw' hα hβ hαβ ha hb hab
    obtain ⟨g, hg, hge, hgz⟩ := exists_mem_of_secGrp hh hz2
    exact ⟨g, hg, hge, by rw [hgz, hzαβ, he]⟩
  refine ⟨F₁, by rw [hcv]; exact h4, ⟨hsv.1, hsv.2, hsw.1, hsw.2⟩, hvw, himage, ?_, htrans⟩
  intro a ha b hb hab
  obtain ⟨g, hg, hge, hgz⟩ := htrans z₁ hz₁.1 hz₁.2 (ne_zero_of_bil_eq_one hvw) a ha b hb hab
  refine ⟨natAct g z₁, Refl.act_mem_normC hz₁.1 hg, ?_, hgz⟩
  have h := bil_act g z₁ (eOne k)
  rw [hge, bil_eOne, bil_eOne] at h
  rw [h]
  exact hz₁.2

theorem caseA_or_caseB [Finite k]
    {n : ℕ} (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ n) {G₀ : Subgroup (antiSp k)}
    {z₁ z₂ : Fin 4 → k} (hz₁ : z₁ ∈ Refl.normC G₀) (hz₂ : z₂ ∈ Refl.normC G₀) (h₁ : z₁ 2 = 0)
    (h₂ : z₂ 2 = 0) (hc : spBil (proj z₁) (proj z₂) ≠ 0) :
    CaseA G₀ ∨
      ∃ F₁ : Subfield k, CaseB G₀ F₁ (proj z₁) ((spBil (proj z₁) (proj z₂))⁻¹ • proj z₂) := by
  rcases secGrp_dihedral_or_large hn hk cenT_two (⟨hz₁, h₁⟩ : z₁ ∈ cenT G₀) ⟨hz₂, h₂⟩ hc with
    h4 | hA | hA
  · exact Or.inr (caseB_of_four hk ⟨hz₁, h₁⟩ ⟨hz₂, h₂⟩ hc h4)
  · exact Or.inl (Or.inl hA)
  · exact Or.inl (Or.inr hA)

end CFSG.Quasithin.Ch3E213M.G41.Big
