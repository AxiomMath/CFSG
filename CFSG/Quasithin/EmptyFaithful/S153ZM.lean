module

public import CFSG.Quasithin.EmptyFaithful.S153ZK
public import CFSG.Quasithin.EmptyFaithful.S153ZG

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem exists_iso_of_le_iSup_smul {A : Type*} [Group A] {T : Type*} [Group T] [MulDistribMulAction A Q]
    [MulDistribMulAction T Q] (h : XMod.Normalizes A T Q) {S V : Subgroup Q} (hS : XMod.IsIrr A S)
    (hV : XMod.IsIrr A V) (hle : V ≤ ⨆ t : T, t • S) : ∃ t : T, XMod.Iso A V (t • S) := by
  let _ := XMod.twistAction h
  have hinv : ∀ t : T, XMod.IsInv A (t • S) := fun t => XMod.isInv_smul_of_normalizes h t hS.1
  have hP : XMod.IsInv A (⨆ t : T, t • S) := XMod.isInv_iSup hinv
  have h1 : XMod.toSubmod hV.1 ≤ ⨆ t : T, XMod.toSubmod (hinv t) := by
    rw [← XMod.toSubmod_iSup hinv]
    exact (XMod.toSubmod_le_iff (hL := hV.1) (hL' := hP)).2 hle
  rw [← sSup_range] at h1
  have hsimple : ∀ m : ↥(Set.range fun t : T => XMod.toSubmod (hinv t)),
      IsSimpleModule ↥(XMod.opRing A Q) ↥(m : Submodule ↥(XMod.opRing A Q) (Additive Q)) := by
    rintro ⟨_, t, rfl⟩
    exact (XMod.isIrr_iff (hinv t)).1 (isIrr_smul h t hS)
  have hVs : IsSimpleModule ↥(XMod.opRing A Q) ↥(XMod.toSubmod hV.1) := (XMod.isIrr_iff hV.1).1 hV
  obtain ⟨S', ⟨t, rfl⟩, ⟨e⟩⟩ := Submodule.linearEquiv_of_le_sSup (XMod.toSubmod hV.1) _ h1
  exact ⟨t, (XMod.iso_iff hV.1 (hinv t)).2 ⟨e⟩⟩

theorem nB_subgroupOf {A H : Subgroup Γ} (hAH : A ≤ H) (S : Subgroup Q) :
    nB (A.subgroupOf H) S = nB A S := by
  unfold nB
  have : XMod.fixed ↥(A.subgroupOf H) (⊤ : Subgroup Q) = XMod.fixed ↥A (⊤ : Subgroup Q) := by
    ext q
    simp only [XMod.mem_fixed, Subgroup.mem_top, true_and]
    constructor
    · intro hq a
      exact hq ⟨⟨(a : Γ), hAH a.2⟩, a.2⟩
    · intro hq b
      exact hq ⟨((b : ↥H) : Γ), b.2⟩
  rw [this]

theorem isIrr_subgroupOf {Λ H : Subgroup Γ} (hΛH : Λ ≤ H) {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) :
    XMod.IsIrr ↥(Λ.subgroupOf H) V := by
  have key : ∀ J : Subgroup Q, XMod.IsInv ↥(Λ.subgroupOf H) J ↔ XMod.IsInv ↥Λ J := by
    intro J
    constructor
    · intro hJ a x hx
      exact hJ ⟨⟨(a : Γ), hΛH a.2⟩, a.2⟩ x hx
    · intro hJ b x hx
      exact hJ ⟨((b : ↥H) : Γ), b.2⟩ x hx
  exact ⟨(key V).2 hV.1, hV.2.1, fun J hJ h1 h2 => hV.2.2 J ((key J).1 hJ) h1 h2⟩

theorem caseA_of_iso [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ A H : Subgroup Γ} (hΛH : Λ ≤ H)
    (hAH : A ≤ H) (hA2 : IsPGroup 2 A) (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) {V : Subgroup Q}
    (hVH : ∀ g ∈ H, ∀ v ∈ V, g • v ∈ V) (hV : XMod.IsIrr ↥Λ V) {S₀ : Subgroup Q}
    (hS₀inv : XMod.IsInv ↥Λ S₀) (hdisj : S₀ ⊓ V = ⊥) (hiso : XMod.Iso ↥Λ S₀ V) :
    2 * nB A V ≤ nB A (⊤ : Subgroup Q) := by
  classical
  have hVinv : ∀ g : ↥H, ∀ v ∈ V, g • v ∈ V := fun g v hv => hVH g g.2 v hv
  obtain ⟨φ, hφ⟩ := hiso
  let ψ₀ : ↥V →* QuotMod V hVinv :=
    (QuotMod.mk V hVinv).comp (S₀.subtype.comp φ.symm.toMonoidHom)
  have hψ₀ : ∀ l ∈ Λ.subgroupOf H, ∀ v : ↥V, ψ₀ ⟨l • (v : Q), hVinv l v v.2⟩ = l • ψ₀ v := by
    intro l hl v
    have hlΛ : ((l : ↥H) : Γ) ∈ Λ := hl
    set x : ↥S₀ := φ.symm v with hx
    set a : ↥Λ := ⟨((l : ↥H) : Γ), hlΛ⟩ with ha
    have hlx : l • (x : Q) ∈ S₀ := hS₀inv a x x.2
    have h1 := hφ a x ⟨l • (x : Q), hlx⟩ rfl
    have hφx : φ x = v := φ.apply_symm_apply v
    rw [hφx] at h1
    have h2 : φ ⟨l • (x : Q), hlx⟩ = ⟨l • (v : Q), hVinv l v v.2⟩ := Subtype.ext h1.symm
    have h3 : φ.symm ⟨l • (v : Q), hVinv l v v.2⟩ = ⟨l • (x : Q), hlx⟩ := by
      rw [← h2, φ.symm_apply_apply]
    show QuotMod.mk V hVinv ((φ.symm ⟨l • (v : Q), hVinv l v v.2⟩ : ↥S₀) : Q) =
      l • QuotMod.mk V hVinv ((x : ↥S₀) : Q)
    rw [h3, quotMod_smul_mk]
  have hne : ψ₀ ≠ 1 := by
    obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v ∈ V, v ≠ 1 := by
      by_contra hcon
      apply hV.2.1.ne'
      refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
      by_contra h
      exact hcon ⟨v, hv, h⟩
    intro h
    have h1 : ψ₀ ⟨v₀, hv₀⟩ = 1 := by rw [h]; rfl
    have h2 : ((φ.symm ⟨v₀, hv₀⟩ : ↥S₀) : Q) ∈ (QuotMod.mk V hVinv).ker := h1
    rw [QuotMod.ker_mk] at h2
    have h3 : ((φ.symm ⟨v₀, hv₀⟩ : ↥S₀) : Q) ∈ S₀ ⊓ V := ⟨(φ.symm ⟨v₀, hv₀⟩).2, h2⟩
    rw [hdisj, Subgroup.mem_bot] at h3
    have h4 : φ.symm ⟨v₀, hv₀⟩ = 1 := Subtype.ext h3
    have h5 : (⟨v₀, hv₀⟩ : ↥V) = 1 := by
      have := congrArg φ h4
      rwa [φ.apply_symm_apply, map_one] at this
    exact hv₀1 (congrArg Subtype.val h5)
  have hA2' : IsPGroup 2 ↥(A.subgroupOf H) := A4.isPGroup_subgroupOf_of_le hAH hA2
  have hAΛ' : ∀ a ∈ A.subgroupOf H, ∀ l ∈ Λ.subgroupOf H, a * l * a⁻¹ ∈ Λ.subgroupOf H := by
    intro a ha l hl
    exact hAΛ _ ha _ hl
  have := two_nB_le (Γ := ↥H) hQ hA2' hAΛ' hVinv (isIrr_subgroupOf hΛH hV) ψ₀ hψ₀ hne
  rwa [nB_subgroupOf hAH, nB_subgroupOf hAH] at this

end CFSG.Quasithin.Z391
