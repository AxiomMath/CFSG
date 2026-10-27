module

public import CFSG.Quasithin.EmptyFaithful.S153ZM
public import CFSG.Quasithin.EmptyFaithful.S153ZJ

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise
open CFSG.QuasithinUnique

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem map_conj_inv_conj (A₁ : Subgroup Γ) (g : Γ) :
    (A₁.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A₁ := by
  ext x
  rw [mem_conjMap, mem_conjMap]
  have : g⁻¹⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [this]

theorem rk_map_conj (A₁ : Subgroup Γ) (g : Γ) :
    rk ↥(A₁.map (MulAut.conj g).toMonoidHom) = rk ↥A₁ := by
  unfold rk
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mackey_count [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ T A : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hT : IsSylowTwoOf T ⊤) (hAT : A ≤ T)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1) {V : Subgroup Q}
    (hV : XMod.IsIrr ↥Λ V) (hVT : ∀ t ∈ T, t • V = V) (hgen : (⨆ g : Γ, g • V) = ⊤)
    (hne : V ≠ ⊤) :
    ∃ (g : Γ) (A₁ B : Subgroup Γ), A₁ ≤ A ∧ B = A₁.map (MulAut.conj g⁻¹).toMonoidHom ∧ B ≤ T ∧
      nB A V + nB B V + (rk ↥A - rk ↥A₁) ≤ nB A (⊤ : Subgroup Q) := by
  classical
  have hNΓ : XMod.Normalizes ↥Λ Γ Q := normalizes_whole Λ hΛ
  have hNA : XMod.Normalizes ↥Λ ↥A Q := normalizes_of_conj Λ A (fun g _ l hl => hΛ g l hl)
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : Γ, ¬ g₀ • V ≤ V := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [eq_top_iff, ← hgen]
    exact iSup_le hcon
  set S₀ : Subgroup Q := g₀ • V with hS₀
  have hS₀irr : XMod.IsIrr ↥Λ S₀ := isIrr_smul hNΓ g₀ hV
  have hdisj : S₀ ⊓ V = ⊥ := by
    have hinv : XMod.IsInv ↥Λ (S₀ ⊓ V) := XMod.IsInv.inf hS₀irr.1 hV.1
    rcases hS₀irr.2.2 (S₀ ⊓ V) hinv bot_le inf_le_left with h | h
    · exact h
    · exfalso
      exact hg₀ (h ▸ inf_le_right)
  have hAexp : IsPGroup 2 ↥A :=
    isPGroup_two_of_sq_eq_one (fun x : ↥A => Subtype.ext (by simpa using hA2 _ x.2))
  by_cases hiso : XMod.Iso ↥Λ S₀ V
  ·
    set H : Subgroup Γ := MulAction.stabilizer Γ V with hH
    have hΛH : Λ ≤ H := by
      intro l hl
      rw [hH, MulAction.mem_stabilizer_iff]
      refine le_antisymm ?_ ?_
      · rintro _ ⟨v, hv, rfl⟩
        exact hV.1 ⟨l, hl⟩ v hv
      · intro v hv
        refine ⟨l⁻¹ • v, ?_, by simp [smul_inv_smul]⟩
        exact hV.1 ⟨l⁻¹, Λ.inv_mem hl⟩ v hv
    have hTH : T ≤ H := fun t ht => by rw [hH, MulAction.mem_stabilizer_iff]; exact hVT t ht
    have hVH : ∀ g ∈ H, ∀ v ∈ V, g • v ∈ V := by
      intro g hg v hv
      have : g • V = V := hg
      rw [← this]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
    have h2 := caseA_of_iso hQ hΛH (hAT.trans hTH) hAexp
      (fun a _ l hl => hΛ a l hl) hVH hV hS₀irr.1 hdisj hiso
    refine ⟨1, A, A.map (MulAut.conj (1 : Γ)⁻¹).toMonoidHom, le_rfl, rfl, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      have : (MulAut.conj (1 : Γ)⁻¹).toMonoidHom a = a := by simp
      rw [this]
      exact hAT ha
    · have : A.map (MulAut.conj (1 : Γ)⁻¹).toMonoidHom = A := by
        ext x
        rw [mem_conjMap]
        simp
      rw [this]
      omega
  ·
    obtain ⟨g, hgiso, hgT⟩ := exists_fixing_translate hΛ hT hAT hV.1 hVT g₀
    set S : Subgroup Q := g • V with hS
    have hSirr : XMod.IsIrr ↥Λ S := isIrr_smul hNΓ g hV
    set A₁ : Subgroup Γ := A ⊓ typeStab Λ hNΓ hS₀irr.1 with hA₁
    have hA₁A : A₁ ≤ A := inf_le_left
    have hmemA₁ : ∀ a ∈ A, a ∈ A₁ ↔ XMod.Iso ↥Λ (a • S₀) S₀ := fun a ha =>
      ⟨fun h => mem_typeStab.1 h.2, fun h => ⟨ha, mem_typeStab.2 h⟩⟩
    have hfix : ∀ a ∈ A₁, a • S = S := fun a ha =>
      smul_translate_eq hVT (hgT a ha.1 (mem_typeStab.1 ha.2))
    have hiso_of : ∀ a : Γ, XMod.Iso ↥Λ (a • S) S → XMod.Iso ↥Λ (a • S₀) S₀ := by
      intro a ha
      have h1 : XMod.Iso ↥Λ S S₀ := hgiso
      have h2 : XMod.Iso ↥Λ (a • S) (a • S₀) := XMod.iso_smul hNΓ a h1
      have h3 : XMod.Iso ↥Λ (a • S₀) (a • S) :=
        XMod.Iso.symm (XMod.isInv_smul_of_normalizes hNΓ a hSirr.1) h2
      exact (h3.trans ha).trans h1
    have hstab : ∀ a ∈ A, a • S = S → a ∈ A₁ := by
      intro a ha h
      have : XMod.Iso ↥Λ (a • S) S := by rw [h]; exact XMod.Iso.refl S
      exact (hmemA₁ a ha).2 (hiso_of a this)
    have hfixiso : ∀ t : ↥A, XMod.Iso ↥Λ (t • S) S → t • S = S := by
      intro t ht
      have h1 : XMod.Iso ↥Λ ((t : Γ) • S) S := ht
      have h2 : (t : Γ) ∈ A₁ := (hmemA₁ t t.2).2 (hiso_of (t : Γ) h1)
      exact hfix t h2
    have hind : sSupIndep (Set.range fun t : ↥A => (t : Γ) • S) :=
      XMod.sSupIndep_smul_of_isHomComp hNA hSirr
        ((XMod.forall_iso_smul_eq_iff_isHomComp hNA hSirr).1 hfixiso)
    set P : Subgroup Q := ⨆ t : ↥A, (t : Γ) • S with hP
    have hVA : XMod.IsInv ↥A V := by
      intro a v hv
      have h1 : (a : Γ) • V = V := hVT a (hAT a.2)
      rw [← h1]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
    have hPΛ : XMod.IsInv ↥Λ P :=
      XMod.isInv_iSup (fun t : ↥A => XMod.isInv_smul_of_normalizes hNΓ (t : Γ) hSirr.1)
    have hPA : XMod.IsInv ↥A P := by
      intro a x hx
      have h1 : (a : Γ) • P ≤ P := by
        rw [hP, smul_iSup_translate]
        exact iSup_le fun t =>
          le_iSup (fun s : ↥A => (s : Γ) • S) ⟨(a : Γ) * (t : Γ), A.mul_mem a.2 t.2⟩
      exact h1 (Subgroup.smul_mem_pointwise_smul _ _ _ hx)
    have hVP : V ⊓ P = ⊥ := by
      have hinv : XMod.IsInv ↥Λ (V ⊓ P) := XMod.IsInv.inf hV.1 hPΛ
      rcases hV.2.2 (V ⊓ P) hinv bot_le inf_le_left with h | h
      · exact h
      · exfalso
        have hle : V ≤ P := h ▸ inf_le_right
        obtain ⟨t, ht⟩ := exists_iso_of_le_iSup_smul hNA hSirr hV hle
        have h1 : XMod.Iso ↥Λ ((t : Γ) • S) V := XMod.Iso.symm hV.1 ht
        have h2 : XMod.Iso ↥Λ ((t : Γ) • S) ((t : Γ) • S₀) := XMod.iso_smul hNΓ (t : Γ) hgiso
        have h3 : XMod.Iso ↥Λ ((t : Γ) • S₀) V :=
          (XMod.Iso.symm (XMod.isInv_smul_of_normalizes hNΓ (t : Γ) hSirr.1) h2).trans h1
        have h4 := XMod.iso_smul hNΓ (t : Γ)⁻¹ h3
        rw [inv_smul_smul, show (t : Γ)⁻¹ • V = V from hVT _ (T.inv_mem (hAT t.2))] at h4
        exact hiso h4
    set B : Subgroup Γ := A₁.map (MulAut.conj g⁻¹).toMonoidHom with hB
    have hBT : B ≤ T := by
      rintro _ ⟨a, ha, rfl⟩
      have := hgT a ha.1 (mem_typeStab.1 ha.2)
      have e : (MulAut.conj g⁻¹).toMonoidHom a = g⁻¹ * a * g := by
        show g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * a * g
        rw [inv_inv]
      rw [e]
      exact this
    have hBS : nB B V = nB A₁ S := by
      have := nB_smul B g V
      rw [hB, map_conj_inv_conj] at this
      exact this.symm
    have hsum := nB_sup_of_disjoint A hVA hPA hVP
    have hmono := nB_mono A (le_top : V ⊔ P ≤ ⊤)
    have hn : rk ↥A = rk ↥A₁ + (rk ↥A - rk ↥A₁) := by
      have := rk_mono hA₁A
      omega
    obtain ⟨hb1, -⟩ := nB_block S (rk ↥A - rk ↥A₁) A A₁ hAc hA2 hA₁A hn hfix hstab hind
    rw [← hP] at hb1
    have hSbot : S ≠ ⊥ := hSirr.2.1.ne'
    have hrkS : 1 ≤ rk ↥S := by
      by_contra h0
      have : rk ↥S = 0 := by omega
      exact hSbot ((rk_eq_zero_iff hQ).1 this)
    have hpow : rk ↥A - rk ↥A₁ ≤ 2 ^ (rk ↥A - rk ↥A₁) - 1 := by
      have := Nat.lt_two_pow_self (n := rk ↥A - rk ↥A₁)
      omega
    have hmul : rk ↥A - rk ↥A₁ ≤ (2 ^ (rk ↥A - rk ↥A₁) - 1) * rk ↥S :=
      hpow.trans (Nat.le_mul_of_pos_right _ hrkS)
    refine ⟨g, A₁, B, hA₁A, rfl, hBT, ?_⟩
    rw [hBS]
    omega

end CFSG.Quasithin.Z391
