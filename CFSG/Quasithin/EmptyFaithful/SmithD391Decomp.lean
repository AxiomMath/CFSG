module

public import CFSG.Quasithin.EmptyFaithful.S153ZN
public import CFSG.Quasithin.EmptyFaithful.SmithD391Count

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem smul_mem_of_mem_sup {A Λ : Subgroup Γ} {S : Subgroup Q}
    (hA : ∀ a ∈ A, ∀ s ∈ S, a • s ∈ S) (hΛ : ∀ l ∈ Λ, ∀ s ∈ S, l • s ∈ S) {g : Γ}
    (hg : g ∈ A ⊔ Λ) : ∀ s ∈ S, g • s ∈ S := by
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hA x hx
    · exact hΛ x hx
  | inv_mem x hx =>
    rcases hx with hx | hx
    · exact hA x⁻¹ (A.inv_mem hx)
    · exact hΛ x⁻¹ (Λ.inv_mem hx)
  | one => intro s hs; rwa [one_smul]
  | mul x y _ _ hx hy =>
    intro s hs
    rw [mul_smul]
    exact hx _ (hy s hs)

theorem exists_isIrr_le [Finite Q] {Λ : Subgroup Γ} {B : Subgroup Q} (hB : XMod.IsInv ↥Λ B)
    (hne : B ≠ ⊥) : ∃ S ≤ B, XMod.IsIrr ↥Λ S := by
  classical
  obtain ⟨S, ⟨hSB, hSinv, hSne⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup Q))
    {J : Subgroup Q | J ≤ B ∧ XMod.IsInv ↥Λ J ∧ J ≠ ⊥} ⟨B, le_rfl, hB, hne⟩
  refine ⟨S, hSB, hSinv, bot_lt_iff_ne_bot.2 hSne, fun J hJ _ hJS => ?_⟩
  by_cases hJ0 : J = ⊥
  · exact Or.inl hJ0
  · right
    by_contra hne'
    exact hmin J ⟨hJS.trans hSB, hJ, hJ0⟩ (lt_of_le_of_ne hJS hne')

theorem exists_iso_of_le_iSup {A : Type*} [Group A] [MulDistribMulAction A Q] {ι : Type*}
    {S : ι → Subgroup Q} (hS : ∀ i, XMod.IsIrr A (S i)) {V : Subgroup Q} (hV : XMod.IsIrr A V)
    (hle : V ≤ ⨆ i, S i) : ∃ i, XMod.Iso A V (S i) := by
  have hinv : ∀ i, XMod.IsInv A (S i) := fun i => (hS i).1
  have hP : XMod.IsInv A (⨆ i, S i) := XMod.isInv_iSup hinv
  have h1 : XMod.toSubmod hV.1 ≤ ⨆ i, XMod.toSubmod (hinv i) := by
    rw [← XMod.toSubmod_iSup hinv]
    exact (XMod.toSubmod_le_iff (hL := hV.1) (hL' := hP)).2 hle
  rw [← sSup_range] at h1
  have hsimple : ∀ m : ↥(Set.range fun i => XMod.toSubmod (hinv i)),
      IsSimpleModule ↥(XMod.opRing A Q) ↥(m : Submodule ↥(XMod.opRing A Q) (Additive Q)) := by
    rintro ⟨_, i, rfl⟩
    exact (XMod.isIrr_iff (hinv i)).1 (hS i)
  have hVs : IsSimpleModule ↥(XMod.opRing A Q) ↥(XMod.toSubmod hV.1) := (XMod.isIrr_iff hV.1).1 hV
  obtain ⟨S', ⟨i, rfl⟩, ⟨e⟩⟩ := Submodule.linearEquiv_of_le_sSup (XMod.toSubmod hV.1) _ h1
  exact ⟨i, (XMod.iso_iff hV.1 (hinv i)).2 ⟨e⟩⟩

@[expose] def isoSum (Λ : Subgroup Γ) (V : Subgroup Q) : Subgroup Q :=
  ⨆ (g : Γ) (_ : XMod.Iso ↥Λ (g • V) V), g • V

section Iso

variable {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {V : Subgroup Q}

theorem le_isoSum {g : Γ} (hg : XMod.Iso ↥Λ (g • V) V) : g • V ≤ isoSum Λ V :=
  le_iSup₂_of_le g hg le_rfl

theorem self_le_isoSum : V ≤ isoSum Λ V := by
  have := le_isoSum (Λ := Λ) (V := V) (g := 1) (by rw [one_smul]; exact XMod.Iso.refl V)
  rwa [one_smul] at this

include hΛ in
theorem isInv_isoSum (hV : XMod.IsInv ↥Λ V) : XMod.IsInv ↥Λ (isoSum Λ V) :=
  XMod.isInv_iSup fun g => XMod.isInv_iSup fun _ =>
    XMod.isInv_smul_of_normalizes (normalizes_whole Λ hΛ) g hV

include hΛ in
theorem smul_isoSum_le {x : Γ} (hx : XMod.Iso ↥Λ (x • V) V) :
    x • isoSum Λ V ≤ isoSum Λ V := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  unfold isoSum
  have h : ∀ T : Subgroup Q, x • T = T.map (MulDistribMulAction.toMonoidHom Q x) := fun T => rfl
  rw [h, Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hg => ?_
  rw [← h, smul_smul]
  refine le_iSup₂_of_le (x * g) ?_ le_rfl
  have h1 : XMod.Iso ↥Λ (x • g • V) (x • V) := XMod.iso_smul hN x hg
  rw [smul_smul] at h1
  exact h1.trans hx

include hΛ in
theorem smul_isoSum_eq [Finite Q] {x : Γ}
    (hx : XMod.Iso ↥Λ (x • V) V) : x • isoSum Λ V = isoSum Λ V := by
  refine Subgroup.eq_of_le_of_card_ge (smul_isoSum_le hΛ hx) ?_
  rw [Nat.card_congr (XMod.smulEquiv x (isoSum Λ V)).toEquiv.symm]

include hΛ in
theorem smul_isoSum_eq_of_iso [Finite Q] {g t : Γ}
    (hg : XMod.Iso ↥Λ (g • V) (t • V)) : g • isoSum Λ V = t • isoSum Λ V := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  have h1 : XMod.Iso ↥Λ ((t⁻¹ * g) • V) V := by
    have := XMod.iso_smul hN t⁻¹ hg
    rwa [smul_smul, inv_smul_smul] at this
  have h2 := smul_isoSum_eq hΛ h1
  calc g • isoSum Λ V = t • ((t⁻¹ * g) • isoSum Λ V) := by rw [smul_smul, mul_inv_cancel_left]
    _ = t • isoSum Λ V := by rw [h2]

end Iso

section Decomp

variable [Finite Q] {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {V : Subgroup Q}
  (hV : XMod.IsIrr ↥Λ V) {t : Γ}

omit [Finite Q] in
include hΛ in
theorem sup_isoSum_smul (hgen : (⨆ g : Γ, g • V) = ⊤)
    (hdich : ∀ g : Γ, XMod.Iso ↥Λ (g • V) V ∨ XMod.Iso ↥Λ (g • V) (t • V)) :
    isoSum Λ V ⊔ t • isoSum Λ V = ⊤ := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  rw [eq_top_iff, ← hgen]
  refine iSup_le fun g => ?_
  rcases hdich g with h | h
  · exact (le_isoSum h).trans le_sup_left
  · refine le_trans ?_ le_sup_right
    have h1 : XMod.Iso ↥Λ ((t⁻¹ * g) • V) V := by
      have := XMod.iso_smul hN t⁻¹ h
      rwa [smul_smul, inv_smul_smul] at this
    have h2 := le_isoSum h1
    have h3 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t)).2 h2
    rwa [smul_smul, mul_inv_cancel_left] at h3

omit [Finite Q] in
include hΛ hV in
theorem iso_of_le_isoSum {S : Subgroup Q} (hS : XMod.IsIrr ↥Λ S) (hle : S ≤ isoSum Λ V) :
    XMod.Iso ↥Λ S V := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  have e : isoSum Λ V = ⨆ p : {g : Γ // XMod.Iso ↥Λ (g • V) V}, (p.1 : Γ) • V := by
    unfold isoSum
    exact iSup_subtype'
  rw [e] at hle
  have hirr : ∀ p : {g : Γ // XMod.Iso ↥Λ (g • V) V}, XMod.IsIrr ↥Λ ((p.1 : Γ) • V) :=
    fun p => isIrr_smul hN p.1 hV
  obtain ⟨⟨g, hg⟩, hiso⟩ :=
    exists_iso_of_le_iSup (S := fun p : {g : Γ // XMod.Iso ↥Λ (g • V) V} => (p.1 : Γ) • V)
      hirr hS hle
  exact hiso.trans hg

include hΛ hV in
theorem inf_isoSum_smul (ht : ¬ XMod.Iso ↥Λ (t • V) V) :
    isoSum Λ V ⊓ t • isoSum Λ V = ⊥ := by
  have hN := normalizes_whole (Q := Q) Λ hΛ
  by_contra hne
  have hinv : XMod.IsInv ↥Λ (isoSum Λ V ⊓ t • isoSum Λ V) :=
    (isInv_isoSum hΛ hV.1).inf (XMod.isInv_smul_of_normalizes hN t (isInv_isoSum hΛ hV.1))
  obtain ⟨S, hSle, hS⟩ := exists_isIrr_le hinv hne
  have h1 : XMod.Iso ↥Λ S V := iso_of_le_isoSum hΛ hV hS (hSle.trans inf_le_left)
  have h2 : t⁻¹ • S ≤ isoSum Λ V := by
    have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t⁻¹)).2 (hSle.trans inf_le_right)
    rwa [inv_smul_smul] at this
  have h3 : XMod.Iso ↥Λ (t⁻¹ • S) V := iso_of_le_isoSum hΛ hV (isIrr_smul hN t⁻¹ hS) h2
  have h4 : XMod.Iso ↥Λ S (t • V) := by
    have := XMod.iso_smul hN t h3
    rwa [smul_inv_smul] at this
  exact ht ((XMod.Iso.symm hS.1 h4).trans h1)

end Decomp

section Count

variable {H : Subgroup Γ}

theorem nB_top_subAct [Finite Q] (S : Subgroup Q) (hS : ∀ g : ↥H, ∀ s ∈ S, g • s ∈ S)
    (B : Subgroup Γ) (hBH : B ≤ H) :
    letI := subAct (Γ := ↥H) S hS
    nB (B.subgroupOf H) (⊤ : Subgroup ↥S) = nB B S := by
  let _i := subAct (Γ := ↥H) S hS
  unfold nB
  rw [rk_top, top_inf_eq]
  set F := XMod.fixed ↥(B.subgroupOf H) (⊤ : Subgroup ↥S) with hF
  have hmap : F.map S.subtype = S ⊓ XMod.fixed ↥B (⊤ : Subgroup Q) := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s.2, XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩⟩
      have h1 := (XMod.mem_fixed.1 hs).2 ⟨⟨(b : Γ), hBH b.2⟩, b.2⟩
      exact congrArg Subtype.val h1
    · rintro ⟨hxS, hx⟩
      refine ⟨⟨x, hxS⟩, XMod.mem_fixed.2 ⟨trivial, fun b => ?_⟩, rfl⟩
      apply Subtype.ext
      exact (XMod.mem_fixed.1 hx).2 ⟨((b : ↥H) : Γ), b.2⟩
  have hrk : rk ↥F = rk ↥(S ⊓ XMod.fixed ↥B (⊤ : Subgroup Q)) := by
    rw [← hmap]
    unfold rk
    rw [Subgroup.card_map_of_injective S.subtype_injective]
  rw [hrk]

theorem count_isoSum [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V)
    {A : Subgroup Γ} (hA : IsPGroup 2 A) (hAV : ∀ a ∈ A, a • V = V) :
    ∃ k : ℕ, rk ↥(isoSum Λ V) = k * rk ↥V ∧ k * nB A V ≤ nB A (isoSum Λ V) := by
  classical
  set H : Subgroup Γ := A ⊔ Λ with hH
  set Q₁ := isoSum Λ V with hQ₁
  have hN := normalizes_whole (Q := Q) Λ hΛ
  have hAVmem : ∀ a ∈ A, ∀ v ∈ V, a • v ∈ V := by
    intro a ha v hv
    rw [← hAV a ha]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
  have hΛV : ∀ l ∈ Λ, ∀ v ∈ V, l • v ∈ V := fun l hl v hv => hV.1 ⟨l, hl⟩ v hv
  have hVH : ∀ g : ↥H, ∀ v ∈ V, g • v ∈ V := fun g => smul_mem_of_mem_sup hAVmem hΛV g.2
  have hAQ₁ : ∀ a ∈ A, ∀ q ∈ Q₁, a • q ∈ Q₁ := by
    intro a ha q hq
    have h1 : XMod.Iso ↥Λ (a • V) V := by rw [hAV a ha]; exact XMod.Iso.refl V
    have h2 := smul_isoSum_eq hΛ h1
    rw [hQ₁, ← h2]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  have hΛQ₁ : ∀ l ∈ Λ, ∀ q ∈ Q₁, l • q ∈ Q₁ :=
    fun l hl q hq => isInv_isoSum hΛ hV.1 ⟨l, hl⟩ q hq
  have hQ₁H : ∀ g : ↥H, ∀ q ∈ Q₁, g • q ∈ Q₁ := fun g => smul_mem_of_mem_sup hAQ₁ hΛQ₁ g.2
  let _iV := subAct (Γ := ↥H) V hVH
  let _iQ := subAct (Γ := ↥H) Q₁ hQ₁H
  have hA' : IsPGroup 2 (A.subgroupOf H) := A4.isPGroup_subgroupOf_of_le le_sup_left hA
  have hAΛ' : ∀ a ∈ A.subgroupOf H, ∀ l ∈ Λ.subgroupOf H, a * l * a⁻¹ ∈ Λ.subgroupOf H :=
    fun a _ l hl => hΛ a l hl
  have hgen : A.subgroupOf H ⊔ Λ.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hirr : ∀ J : Subgroup ↥V, (∀ l ∈ Λ.subgroupOf H, ∀ p ∈ J, l • p ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hinv : XMod.IsInv ↥Λ (J.map V.subtype) := by
      rintro ⟨l, hl⟩ _ ⟨p, hp, rfl⟩
      have hlH : l ∈ H := (le_sup_right : Λ ≤ A ⊔ Λ) hl
      exact ⟨_, hJ ⟨l, hlH⟩ hl p hp, rfl⟩
    rcases hV.2.2 _ hinv bot_le (Subgroup.map_subtype_le J) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective J V.subtype_injective).1 h
    · right
      rw [eq_top_iff]
      intro p _
      have : (p : Q) ∈ J.map V.subtype := by rw [h]; exact p.2
      obtain ⟨p', hp', he⟩ := this
      rwa [show p' = p from Subtype.ext he] at hp'
  have hQ₁sq : ∀ q : ↥Q₁, q ^ 2 = 1 := fun q => Subtype.ext (by simpa using hQ q)
  have hgenQ : (⊤ : Subgroup ↥Q₁) ≤ ⨆ (φ : ↥V →* ↥Q₁)
      (_ : ∀ l ∈ Λ.subgroupOf H, ∀ p, φ (l • p) = l • φ p), φ.range := by
    set R := ⨆ (φ : ↥V →* ↥Q₁) (_ : ∀ l ∈ Λ.subgroupOf H, ∀ p, φ (l • p) = l • φ p), φ.range
      with hR
    have hle : Q₁ ≤ R.map Q₁.subtype := by
      show isoSum Λ V ≤ R.map Q₁.subtype
      unfold isoSum
      refine iSup₂_le fun g hg => ?_
      have hinvg : XMod.IsInv ↥Λ (g • V) := XMod.isInv_smul_of_normalizes hN g hV.1
      obtain ⟨φ, hφ⟩ := XMod.Iso.symm hinvg hg
      have hgle : g • V ≤ Q₁ := le_isoSum hg
      let ψ : ↥V →* ↥Q₁ := (Subgroup.inclusion hgle).comp φ.toMonoidHom
      have hψ : ∀ l ∈ Λ.subgroupOf H, ∀ p, ψ (l • p) = l • ψ p := by
        intro l hl p
        apply Subtype.ext
        have h1 := hφ ⟨((l : ↥H) : Γ), hl⟩ p (l • p) rfl
        exact h1.symm
      intro x hx
      refine ⟨ψ (φ.symm ⟨x, hx⟩), ?_, ?_⟩
      · exact (le_iSup₂_of_le ψ hψ le_rfl : ψ.range ≤ R) ⟨_, rfl⟩
      · show ((φ (φ.symm ⟨x, hx⟩) : ↥(g • V)) : Q) = x
        rw [MulEquiv.apply_symm_apply]
    rintro q -
    obtain ⟨r, hr, he⟩ := hle q.2
    rwa [show r = q from Subtype.ext he] at hr
  obtain ⟨k, hk1, hk2⟩ := count_of_homs hA' hAΛ' hgen hirr (Nat.card ↥Q₁) ↥Q₁ rfl hQ₁sq hgenQ
  refine ⟨k, hk1, ?_⟩
  rw [nB_top_subAct V hVH A le_sup_left, nB_top_subAct Q₁ hQ₁H A le_sup_left] at hk2
  exact hk2

theorem nB_sup_of_inf_eq_bot [Finite Q] (B : Subgroup Γ) {S S' : Subgroup Q}
    (hS : ∀ b ∈ B, ∀ s ∈ S, b • s ∈ S) (hS' : ∀ b ∈ B, ∀ s ∈ S', b • s ∈ S') (hd : S ⊓ S' = ⊥) :
    nB B (S ⊔ S') = nB B S + nB B S' :=
  nB_sup_of_disjoint B (fun b s hs => hS b b.2 s hs) (fun b s hs => hS' b b.2 s hs) hd

theorem count_nonswap [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) {t : Γ}
    (ht : ¬ XMod.Iso ↥Λ (t • V) V) (hgen : (⨆ g : Γ, g • V) = ⊤)
    (hdich : ∀ g : Γ, XMod.Iso ↥Λ (g • V) V ∨ XMod.Iso ↥Λ (g • V) (t • V))
    {A : Subgroup Γ} (hA : IsPGroup 2 A) (hAV : ∀ a ∈ A, a • V = V)
    (hAtV : ∀ a ∈ A, a • t • V = t • V) :
    ∃ k : ℕ, rk ↥(isoSum Λ V) = k * rk ↥V ∧
      k * nB A (V ⊔ t • V) ≤ nB A (⊤ : Subgroup Q) := by
  obtain ⟨k, hk1, hk2⟩ := count_isoSum hQ hΛ hV hA hAV
  set A' := A.map (MulAut.conj t⁻¹).toMonoidHom with hA'def
  have hA'p : IsPGroup 2 A' := hA.map _
  have hA'V : ∀ a ∈ A', a • V = V := by
    intro a ha
    rw [mem_conjMap, inv_inv] at ha
    have h1 := hAtV _ ha
    rw [smul_smul, show t * a * t⁻¹ * t = t * a by group, mul_smul] at h1
    have h2 := congrArg (fun S : Subgroup Q => t⁻¹ • S) h1
    simp only [inv_smul_smul] at h2
    exact h2
  obtain ⟨k', hk1', hk2'⟩ := count_isoSum hQ hΛ hV hA'p hA'V
  have hrkV : 0 < rk ↥V := by
    by_contra h0
    have h0' : rk ↥V = 0 := by omega
    exact hV.2.1.ne' ((rk_eq_zero_iff hQ).1 h0')
  have hkk : k' = k := Nat.eq_of_mul_eq_mul_right hrkV (hk1'.symm.trans hk1)
  rw [hkk] at hk2'
  have hAA : A'.map (MulAut.conj t).toMonoidHom = A := by
    rw [hA'def]
    have := map_conj_inv_conj A t
    exact this
  have e1 : nB A (t • isoSum Λ V) = nB A' (isoSum Λ V) := by
    rw [← nB_smul A' t (isoSum Λ V), hAA]
  have e2 : nB A (t • V) = nB A' V := by
    rw [← nB_smul A' t V, hAA]
  have hsup := sup_isoSum_smul hΛ hgen hdich
  have hinf := inf_isoSum_smul hΛ hV ht
  have hAQ : ∀ a ∈ A, ∀ q ∈ isoSum Λ V, a • q ∈ isoSum Λ V := by
    intro a ha q hq
    have h1 : XMod.Iso ↥Λ (a • V) V := by rw [hAV a ha]; exact XMod.Iso.refl V
    rw [← smul_isoSum_eq hΛ h1]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  have hAtQ : ∀ a ∈ A, ∀ q ∈ t • isoSum Λ V, a • q ∈ t • isoSum Λ V := by
    intro a ha q hq
    have h1 : XMod.Iso ↥Λ ((a * t) • V) (t • V) := by
      rw [mul_smul, hAtV a ha]; exact XMod.Iso.refl _
    have h2 := smul_isoSum_eq_of_iso hΛ h1
    rw [mul_smul] at h2
    rw [← h2]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  have hAVm : ∀ a ∈ A, ∀ v ∈ V, a • v ∈ V := by
    intro a ha v hv
    rw [← hAV a ha]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
  have hAtVm : ∀ a ∈ A, ∀ v ∈ t • V, a • v ∈ t • V := by
    intro a ha v hv
    rw [← hAtV a ha]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
  have hVt : V ⊓ t • V = ⊥ := by
    refine le_bot_iff.1 (le_trans (inf_le_inf self_le_isoSum ?_) hinf.le)
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t)).2 self_le_isoSum
  refine ⟨k, hk1, ?_⟩
  rw [← hsup, nB_sup_of_inf_eq_bot A hAQ hAtQ hinf, nB_sup_of_inf_eq_bot A hAVm hAtVm hVt, e1, e2]
  have := hk2'
  nlinarith

theorem count_swap [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) {t : Γ}
    (ht : ¬ XMod.Iso ↥Λ (t • V) V) (hgen : (⨆ g : Γ, g • V) = ⊤)
    (hdich : ∀ g : Γ, XMod.Iso ↥Λ (g • V) V ∨ XMod.Iso ↥Λ (g • V) (t • V))
    {A A₀ : Subgroup Γ} (hA : IsPGroup 2 A) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {a₀ : Γ} (ha₀ : a₀ ∈ A) (ha₀2 : a₀ ^ 2 = 1) (hA₀A : A₀ ≤ A)
    (hsplit : ∀ x ∈ A, x ∈ A₀ ∨ a₀⁻¹ * x ∈ A₀) (hA₀V : ∀ a ∈ A₀, a • V = V)
    (ha₀V : a₀ • V = t • V) :
    ∃ k : ℕ, rk ↥(isoSum Λ V) = k * rk ↥V ∧
      k * nB A (V ⊔ t • V) ≤ nB A (⊤ : Subgroup Q) := by
  have hA₀p : IsPGroup 2 A₀ := hA.to_le hA₀A
  obtain ⟨k, hk1, hk2⟩ := count_isoSum hQ hΛ hV hA₀p hA₀V
  have ha₀Q : a₀ • isoSum Λ V = t • isoSum Λ V := by
    refine smul_isoSum_eq_of_iso hΛ ?_
    rw [ha₀V]
    exact XMod.Iso.refl _
  have hsup := sup_isoSum_smul hΛ hgen hdich
  have hinf := inf_isoSum_smul hΛ hV ht
  rw [← ha₀Q] at hsup hinf
  have hA₀Q : XMod.IsInv ↥A₀ (isoSum Λ V) := by
    intro a q hq
    have h1 : XMod.Iso ↥Λ ((a : Γ) • V) V := by rw [hA₀V a a.2]; exact XMod.Iso.refl V
    have h2 := smul_isoSum_eq hΛ h1
    rw [← h2]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
  have hA₀Vi : XMod.IsInv ↥A₀ V := by
    intro a v hv
    rw [← hA₀V a a.2]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
  have hVt : V ⊓ a₀ • V = ⊥ := by
    refine le_bot_iff.1 (le_trans (inf_le_inf self_le_isoSum ?_) hinf.le)
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a₀)).2 self_le_isoSum
  have h1 := nB_index_two ha₀ ha₀2 hAc hA₀A hsplit hA₀Q hinf
  have h2 := nB_index_two ha₀ ha₀2 hAc hA₀A hsplit hA₀Vi hVt
  refine ⟨k, hk1, ?_⟩
  rw [← hsup, h1, ← ha₀V, h2, hk1]
  nlinarith

end Count


end CFSG.Quasithin.SmithD391
