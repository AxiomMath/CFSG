module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs4
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

theorem w183_centralizer_eq_bot {Y : Type*} [Group Y] {X T : Subgroup Y} [X.Normal]
    (hZ : Subgroup.center ↥X = ⊥) (hXT : X ⊔ T = ⊤) (hT : IsPGroup 2 ↥T)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 ↥N → N = ⊥) :
    Subgroup.centralizer (X : Set Y) = ⊥ := by
  set C := Subgroup.centralizer (X : Set Y) with hC
  haveI hCn : C.Normal := Subgroup.normal_centralizer
  have hCX : C ⊓ X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxZ : (⟨x, hx.2⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.1 (y : Y) y.2)
    rw [hZ, Subgroup.mem_bot] at hxZ
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hxZ)
  have hQ : IsPGroup 2 (Y ⧸ X) := by
    have hsurj : Function.Surjective ((QuotientGroup.mk' X).comp T.subtype) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      have hy : y ∈ X ⊔ T := by rw [hXT]; trivial
      obtain ⟨x, hx, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      refine ⟨⟨t, ht⟩, ?_⟩
      show (QuotientGroup.mk t : Y ⧸ X) = QuotientGroup.mk (x * t)
      rw [QuotientGroup.eq, ← mul_assoc]
      exact (inferInstance : X.Normal).conj_mem' x hx t
    exact hT.of_surjective _ hsurj
  have hCp : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨k, hk⟩ := hQ (QuotientGroup.mk (c : Y))
    refine ⟨k, ?_⟩
    have hmem : (c : Y) ^ (2 ^ k) ∈ X := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hk
    have hmemC : (c : Y) ^ (2 ^ k) ∈ C := C.pow_mem c.2 _
    have hboth : (c : Y) ^ (2 ^ k) ∈ C ⊓ X := ⟨hmemC, hmem⟩
    rw [hCX, Subgroup.mem_bot] at hboth
    exact Subtype.ext (by simpa using hboth)
  exact hO2 C hCn hCp

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

namespace Assumption131

theorem centralizes_of_ne_one_centralizes (h : Assumption131 G Γ VA i)
    {A L : Subgroup (LGL 2 V)} [IsSimpleGroup ↥L] (hA : A ∈ Γ) (hr : mRank A ≤ i)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) (hLG : L ≤ G)
    (hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L)
    {t : LGL 2 V} (ht : t ∈ A) (ht1 : t ≠ 1) (htL : ∀ l ∈ L, t * l = l * t) :
    ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
  have hLN : ∀ l ∈ L, l ∈ Subgroup.normalizer (A : Set (LGL 2 V)) := fun l hl =>
    h.centralizer_le_normalizer_of_mRank_le hA hr ht ht1 (hLG hl) (htL l hl).symm
  let N : Subgroup ↥L := (A ⊓ L).subgroupOf L
  haveI hNn : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨?_, L.mul_mem (L.mul_mem g.2 n.2) (L.inv_mem g.2)⟩
    have := (Subgroup.mem_normalizer_iff.mp (hLN g g.2) (n : LGL 2 V)).mp hn.1
    exact this⟩
  have hbot : A ⊓ L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | htop
    · rw [eq_bot_iff]
      intro x hx
      have hxN : (⟨x, hx.2⟩ : ↥L) ∈ N := Subgroup.mem_subgroupOf.mpr hx
      rw [hb, Subgroup.mem_bot] at hxN
      exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hxN)
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := hnab
      have haA : a ∈ A := by
        have : (⟨a, ha⟩ : ↥L) ∈ N := by rw [htop]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).1
      have hbA : b ∈ A := by
        have : (⟨b, hb⟩ : ↥L) ∈ N := by rw [htop]; trivial
        exact (Subgroup.mem_subgroupOf.mp this).1
      exact hab (CFSG.Open.IsElemAbelian.comm (h.isElemAb A hA) haA hbA)
  intro a haA l hl
  have hc : a * l * a⁻¹ * l⁻¹ ∈ A ⊓ L := by
    refine ⟨?_, L.mul_mem (hAn a haA l hl) (L.inv_mem hl)⟩
    have h1 : l * a⁻¹ * l⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hLN l hl) a⁻¹).mp (A.inv_mem haA)
    have : a * l * a⁻¹ * l⁻¹ = a * (l * a⁻¹ * l⁻¹) := by group
    rw [this]
    exact A.mul_mem haA h1
  rw [hbot, Subgroup.mem_bot] at hc
  calc a * l = a * l * a⁻¹ * l⁻¹ * (l * a) := by group
    _ = l * a := by rw [hc, one_mul]

theorem false_of_sylow_and_reflection (h : Assumption131 G Γ VA i)
    {S₁ : Subgroup (LGL 2 V)} (hS₁ : S₁ ∈ Γ) (hS₁r : mRank S₁ ≤ i) (hVfix : VA S₁ ≤ fixSub S₁)
    (hS₁sq : ∀ x ∈ S₁, x * x = 1) {σ : LGL 2 V} (hσG : σ ∈ G) (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    (hσΓ : Subgroup.zpowers σ ∈ Γ) (hσr : mRank (Subgroup.zpowers σ) ≤ i)
    (hne : cj σ S₁ ≠ S₁) (hcomm : ∀ a ∈ S₁, ∀ b ∈ cj σ S₁, a * b = b * a)
    {s : LGL 2 V} (hs : s ∈ S₁) (hs1 : s ≠ 1) : False := by
  have hS₂Γ : cj σ S₁ ∈ Γ := h.invariant S₁ hS₁ σ hσG
  have hS₂r : mRank (cj σ S₁) ≤ i := by
    unfold mRank
    rw [card_cj]
    exact hS₁r
  have hsG : s ∈ G := h.le_G S₁ hS₁ hs
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hS₁sq s hs)
  have hmemS₂ : σ * s * σ ∈ cj σ S₁ :=
    Subgroup.mem_map.mpr ⟨s, hs, by show σ * s * σ⁻¹ = σ * s * σ; rw [hσinv]⟩
  have hV : commSub S₁ ≤ VA S₁ := commSub_le_VA_of_mRank_le h hS₁ hS₁r
  have hVne : VA S₁ ≠ ⊥ := fun hb => (commSub_ne_bot_of_mem h hS₁) (le_bot_iff.mp (hb ▸ hV))
  obtain ⟨w, hwV, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
  have hw'V : σ w ∈ VA (cj σ S₁) := by
    rw [h.equivariant S₁ hS₁ σ hσG]
    exact apply_mem_conjSub hwV
  have hw'ne : σ w ≠ w := by
    intro heq
    have hboth : w ∈ VA S₁ ⊓ VA (cj σ S₁) := ⟨hwV, heq ▸ hw'V⟩
    rw [h.disjoint S₁ hS₁ (cj σ S₁) hS₂Γ hne.symm] at hboth
    exact hw0 (by simpa using hboth)
  have hS₂fix : ∀ b ∈ cj σ S₁, ∀ v ∈ VA S₁, b v = v := fun b hb v hv =>
    commSpace_eq_bot_iff.mp
      (h.commSpace_VA_eq_bot_of_commute hS₁ hS₂Γ hS₂r hne.symm hcomm) b hb v hv
  have hsw : s w = w := hVfix hwV s hs
  have hu : ((σ * s * σ) * s) w = w := by
    show (σ * s * σ) (s w) = w
    rw [hsw]
    exact hS₂fix _ hmemS₂ w hwV
  have hσu : σ * ((σ * s * σ) * s) = s * σ * s⁻¹ := by
    rw [hsinv]
    calc σ * ((σ * s * σ) * s) = (σ * σ) * s * σ * s := by group
      _ = s * σ * s := by rw [hσ2, one_mul]
  have hmem' : s * σ * s⁻¹ ∈ cj s (Subgroup.zpowers σ) :=
    Subgroup.mem_map.mpr ⟨σ, Subgroup.mem_zpowers σ, rfl⟩
  have hsΓ : cj s (Subgroup.zpowers σ) ∈ Γ := h.invariant _ hσΓ s hsG
  have hsr : mRank (cj s (Subgroup.zpowers σ)) ≤ i := by
    unfold mRank
    rw [card_cj]
    exact hσr
  have hA₁ : σ w - w ∈ VA (Subgroup.zpowers σ) :=
    commSub_le_VA_of_mRank_le h hσΓ hσr (sub_mem_commSub _ (Subgroup.mem_zpowers σ) w)
  have hA₂ : σ w - w ∈ VA (cj s (Subgroup.zpowers σ)) := by
    have := commSub_le_VA_of_mRank_le h hsΓ hsr (sub_mem_commSub _ hmem' w)
    have e : (s * σ * s⁻¹) w = σ w := by
      rw [← hσu]
      show σ (((σ * s * σ) * s) w) = σ w
      rw [hu]
    rw [e] at this
    exact this
  have hdist : Subgroup.zpowers σ ≠ cj s (Subgroup.zpowers σ) := by
    intro heq
    have hin : s * σ * s⁻¹ ∈ Subgroup.zpowers σ := heq ▸ hmem'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hin
    obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
    · have h1 : σ ^ k = 1 := by
        rw [hn, zpow_mul]
        have : σ ^ (2 : ℤ) = 1 := by rw [zpow_two, hσ2]
        rw [this, one_zpow]
      rw [h1] at hk
      apply hσ1
      have : σ = s⁻¹ * (s * σ * s⁻¹) * s := by group
      rw [this, ← hk]
      group
    · have h1 : σ ^ k = σ := by
        rw [hn, zpow_add_one, zpow_mul]
        have : σ ^ (2 : ℤ) = 1 := by rw [zpow_two, hσ2]
        rw [this, one_zpow, one_mul]
      rw [h1] at hk
      have hu1 : (σ * s * σ) * s = 1 := by
        have : σ * ((σ * s * σ) * s) = σ := by rw [hσu, ← hk]
        exact mul_left_cancel (a := σ) (by rw [this, mul_one])
      have hsσ : σ * s * σ = s := by
        have := eq_inv_of_mul_eq_one_left hu1
        rw [this, hsinv]
      have hsS₂ : s ∈ cj σ S₁ := hsσ ▸ hmemS₂
      have hbot := h.inf_eq_bot_of_mRank_le hS₁ hS₂Γ hS₁r hS₂r hne.symm
      have : s ∈ S₁ ⊓ cj σ S₁ := ⟨hs, hsS₂⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hs1 this
  have hboth2 : σ w - w ∈ VA (Subgroup.zpowers σ) ⊓ VA (cj s (Subgroup.zpowers σ)) := ⟨hA₁, hA₂⟩
  rw [h.disjoint _ hσΓ _ hsΓ hdist] at hboth2
  exact hw'ne (sub_eq_zero.mp (by simpa using hboth2))

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
