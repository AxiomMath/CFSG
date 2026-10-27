module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAIface

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem irr_of_two_lines (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {L₃ L₄ : Type} [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
    {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
    {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
    {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
    {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
    {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}
    (hD : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ)
    (hRoot : RootEltProp hS t eN Z0) {g₁ g₂ : G} {f₁ f₂ : Fin 2 → K} {y₁ y₂ : L₄}
    (h₁ : IsSymNbr hc t Z0 g₁) (h₂ : IsSymNbr hc t Z0 g₂) (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) (hl₁ : HasLine hS t eN Z0 g₁ f₁ y₁)
    (hl₂ : HasLine hS t eN Z0 g₂ f₂ y₂) (hdet : det2 f₁ f₂ ≠ 0) :
    ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ k ∈ NormH0 M Z Z0, conjSubgroup k A = A) → A = Z0 ∨ A = hc.CN t := by
  classical
  intro A hZA hAN hAK
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hNM : ∀ x ∈ hc.CN t, x ∈ M := fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1
  have hNR : ∀ c ∈ bar M Q (hc.CN t), c ∈ bar M Q (Rt M (LB M Q B) t) := by
    intro c hc'
    obtain ⟨c', hc'', rfl⟩ := exists_of_mem_bar hc'
    exact mk_mem_bar c' (Ctx.mem_CN.mp hc'').1
  have hAconj : ∀ k ∈ NormH0 M Z Z0, ∀ a ∈ A, k * a * k⁻¹ ∈ A := by
    intro k hk a ha
    have h1 : k * a * k⁻¹ ∈ conjSubgroup k A := mem_conjSubgroup.mpr (by group; exact ha)
    rwa [hAK k hk] at h1
  have hAbar : ∀ a (ha : a ∈ A),
      (QuotientGroup.mk (⟨a, hNM a (hAN ha)⟩ : ↥M) : Mbar M Q) ∈ bar M Q (hc.CN t) :=
    fun a ha => mk_mem_bar _ (hAN ha)
  set D : ∀ a, a ∈ A → (Fin 2 → L₄) := fun a ha =>
    eN ⟨delta hS t _ (mem_bar_H0_of_CN (hAbar a ha)), delta_mem_deltaSub hS (hAbar a ha)⟩ with hDdef
  have hDcongr : ∀ (a : G) (ha : a ∈ A) (x : Mbar M Q) (hx : x ∈ bar M Q (hc.CN t)),
      (QuotientGroup.mk (⟨a, hNM a (hAN ha)⟩ : ↥M) : Mbar M Q) = x →
      D a ha = eN ⟨delta hS t x (mem_bar_H0_of_CN hx), delta_mem_deltaSub hS hx⟩ := by
    intro a ha x hx hax
    subst hax
    rfl
  have hDeq : ∀ a (ha : a ∈ A) a' (ha' : a' ∈ A), a = a' → D a ha = D a' ha' := by
    intro a ha a' ha' h
    subst h
    rfl
  have hDmul : ∀ a (ha : a ∈ A) a' (ha' : a' ∈ A),
      D (a * a') (A.mul_mem ha ha') = D a ha + D a' ha' := by
    intro a ha a' ha'
    rw [hDdef]
    show eN _ = eN _ + eN _
    rw [← map_add]
    congr 1
    refine Subtype.ext ?_
    show delta hS t _ _ = delta hS t _ _ + delta hS t _ _
    rw [← delta_mul h310chi h52a hS hs hr (hAbar a ha) (hAbar a' ha')]
    exact delta_congr hS t rfl _ _
  have hD1 : D 1 A.one_mem = 0 := by
    have h := hDmul 1 A.one_mem 1 A.one_mem
    rw [hDeq (1 * 1) (A.mul_mem A.one_mem A.one_mem) 1 A.one_mem (mul_one 1)] at h
    exact (add_eq_left.mp h.symm)
  have hDinv : ∀ a (ha : a ∈ A), D a⁻¹ (A.inv_mem ha) = -D a ha := by
    intro a ha
    have h := hDmul a ha a⁻¹ (A.inv_mem ha)
    rw [hDeq (a * a⁻¹) (A.mul_mem ha (A.inv_mem ha)) 1 A.one_mem (mul_inv_cancel a), hD1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  let 𝒜 : AddSubgroup (Fin 2 → L₄) :=
    { carrier := {x | ∃ (a : G) (ha : a ∈ A), D a ha = x}
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
        exact ⟨a * a', A.mul_mem ha ha', hDmul a ha a' ha'⟩
      zero_mem' := ⟨1, A.one_mem, hD1⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨a⁻¹, A.inv_mem ha, hDinv a ha⟩ }
  have hmem𝒜 : ∀ x, x ∈ 𝒜 ↔ ∃ (a : G) (ha : a ∈ A), D a ha = x := fun x => Iff.rfl
  have hH : ∀ h, ∀ x ∈ 𝒜, (fun i => ρ₄ h (x i)) ∈ 𝒜 := by
    rintro h _ ⟨a, ha, rfl⟩
    obtain ⟨hm, hhR, hhe⟩ := exists_of_mem_bar h.2
    have hhK := sec8_Rt_le_NormH0 hc hZ0 hhR
    have hca := hAconj _ hhK a ha
    refine ⟨_, hca, ?_⟩
    rw [hDdef]
    simp only []
    rw [← hD.equivN, deltaAct_delta hS ht h (hAbar a ha)]
    congr 1
    refine Subtype.ext ?_
    refine delta_congr hS t ?_ _ _
    rw [← hhe]
    rfl
  have hroot : ∀ (g : G) (f : Fin 2 → K) (y : L₄), IsSymNbr hc t Z0 g → f ≠ 0 → y ≠ 0 →
      HasLine hS t eN Z0 g f y → ∀ (s : K), ∀ x ∈ 𝒜, x + s • matAct (rootN f) x ∈ 𝒜 := by
    intro g f y hg hf hy hl s
    obtain ⟨z, hz, hzΔ⟩ := hRoot g f y hg hf hy hl s
    rintro _ ⟨a, ha, rfl⟩
    have hza := hAconj z hz a ha
    have hzx : QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hz.1.1⟩ : ↥M) *
        (QuotientGroup.mk (⟨a, hNM a (hAN ha)⟩ : ↥M) : Mbar M Q) *
          (QuotientGroup.mk' (Q.subgroupOf M) (⟨z, hz.1.1⟩ : ↥M))⁻¹ ∈ bar M Q (hc.CN t) := by
      have h1 := hAbar _ hza
      exact h1
    refine ⟨_, hza, ?_⟩
    rw [← hzΔ _ (hAbar a ha) hzx]
    exact hDcongr _ hza _ hzx rfl
  rcases eq_bot_or_eq_top_of_rootN ρ₄ hD.irr₄ hdet 𝒜 hH (hroot g₁ f₁ y₁ h₁ hf₁ hy₁ hl₁)
      (hroot g₂ f₂ y₂ h₂ hf₂ hy₂ hl₂) with h0 | htop
  ·
    left
    refine le_antisymm (fun a ha => ?_) hZA
    have h1 : D a ha ∈ 𝒜 := ⟨a, ha, rfl⟩
    rw [h0, AddSubgroup.mem_bot] at h1
    have h2 : delta hS t _ (mem_bar_H0_of_CN (hAbar a ha)) = 0 := by
      have h3 := congrArg Subtype.val ((LinearEquiv.map_eq_zero_iff eN).mp h1)
      exact h3
    have h4 := (delta_eq_zero_iff hCRW hMp hS hs hZ0 (hNR _ (hAbar a ha))).mp h2
    exact (mk_mem_bar_iff_sec4 hQZ0 ⟨a, hNM a (hAN ha)⟩).mp h4
  ·
    right
    refine le_antisymm hAN fun x hx => ?_
    let xm : ↥M := ⟨x, hNM x hx⟩
    have hxb : (QuotientGroup.mk xm : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar xm hx
    have h1 : eN ⟨delta hS t _ (mem_bar_H0_of_CN hxb), delta_mem_deltaSub hS hxb⟩ ∈ 𝒜 := by
      rw [htop]; exact AddSubgroup.mem_top _
    obtain ⟨a, ha, hax⟩ := h1
    have h2 : delta hS t _ (mem_bar_H0_of_CN (hAbar a ha)) =
        delta hS t _ (mem_bar_H0_of_CN hxb) := congrArg Subtype.val (eN.injective hax)
    set ab : Mbar M Q := QuotientGroup.mk (⟨a, hNM a (hAN ha)⟩ : ↥M) with hab
    have hainv : ab⁻¹ ∈ bar M Q (hc.CN t) := (bar M Q (hc.CN t)).inv_mem (hAbar a ha)
    have hxa : (QuotientGroup.mk xm : Mbar M Q) * ab⁻¹ ∈ bar M Q (hc.CN t) :=
      (bar M Q (hc.CN t)).mul_mem hxb hainv
    have h0 : delta hS t _ (mem_bar_H0_of_CN hxa) = 0 := by
      rw [delta_mul h310chi h52a hS hs hr hxb hainv, ← h2,
        ← delta_mul h310chi h52a hS hs hr (hAbar a ha) hainv]
      refine LinearMap.ext fun w => ?_
      rw [delta_apply, LinearMap.zero_apply, mul_inv_cancel, dmap_one]
    have hZ := (delta_eq_zero_iff hCRW hMp hS hs hZ0 (hNR _ hxa)).mp h0
    have hZ' : x * a⁻¹ ∈ Z0 := by
      have e : (QuotientGroup.mk xm : Mbar M Q) * ab⁻¹ =
          QuotientGroup.mk (xm * (⟨a, hNM a (hAN ha)⟩ : ↥M)⁻¹) := rfl
      rw [e] at hZ
      exact (mk_mem_bar_iff_sec4 hQZ0 _).mp hZ
    have hx' := A.mul_mem (hZA hZ') ha
    rwa [inv_mul_cancel_right] at hx'

end CFSG.RankThree.GF2n.Stroth80.S715L
