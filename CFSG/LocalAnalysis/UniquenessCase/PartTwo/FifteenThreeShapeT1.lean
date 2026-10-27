module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

section Transport

variable {Γ Δ : Type*} [Group Γ] [Group Δ] {X : Subgroup Γ} {X' : Subgroup Δ}

@[expose] def ConjIntertwines (θ : ↥X ≃* ↥X') (n : Γ) (n' : Δ) : Prop :=
  ∀ x : ↥X, ∃ hx : n * (x : Γ) * n⁻¹ ∈ X,
    (θ ⟨n * (x : Γ) * n⁻¹, hx⟩ : Δ) = n' * (θ x : Δ) * n'⁻¹

private def Corr (θ : ↥X ≃* ↥X') (Y : Subgroup Γ) (Y' : Subgroup Δ) : Prop :=
  Y ≤ X ∧ Y' ≤ X' ∧ ∀ x : ↥X, (x : Γ) ∈ Y ↔ (θ x : Δ) ∈ Y'

private theorem corr_le_iff {θ : ↥X ≃* ↥X'} {Y Z : Subgroup Γ} {Y' Z' : Subgroup Δ}
    (hY : Corr θ Y Y') (hZ : Corr θ Z Z') : Y ≤ Z ↔ Y' ≤ Z' := by
  constructor
  · intro hle d hd
    obtain ⟨x, hx⟩ := θ.surjective ⟨d, hY.2.1 hd⟩
    have hxd : (θ x : Δ) = d := congrArg Subtype.val hx
    subst hxd
    exact (hZ.2.2 x).1 (hle ((hY.2.2 x).2 hd))
  · intro hle g hg
    have hgX : g ∈ X := hY.1 hg
    exact (hZ.2.2 ⟨g, hgX⟩).2 (hle ((hY.2.2 ⟨g, hgX⟩).1 hg))

private theorem corr_eq_iff {θ : ↥X ≃* ↥X'} {Y Z : Subgroup Γ} {Y' Z' : Subgroup Δ}
    (hY : Corr θ Y Y') (hZ : Corr θ Z Z') : Y = Z ↔ Y' = Z' := by
  rw [le_antisymm_iff, le_antisymm_iff, corr_le_iff hY hZ, corr_le_iff hZ hY]

private theorem corr_commutator_eq_bot {θ : ↥X ≃* ↥X'} {Y Z : Subgroup Γ} {Y' Z' : Subgroup Δ}
    (hY : Corr θ Y Y') (hZ : Corr θ Z Z') (h : ⁅Y', Z'⁆ = ⊥) : ⁅Y, Z⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro y hy z hz
  have hyX : y ∈ X := hY.1 hy
  have hzX : z ∈ X := hZ.1 hz
  have h1 : ⁅(θ ⟨y, hyX⟩ : Δ), (θ ⟨z, hzX⟩ : Δ)⁆ ∈ ⁅Y', Z'⁆ :=
    Subgroup.commutator_mem_commutator ((hY.2.2 ⟨y, hyX⟩).1 hy) ((hZ.2.2 ⟨z, hzX⟩).1 hz)
  rw [h, Subgroup.mem_bot] at h1
  have h2 : θ ⁅(⟨y, hyX⟩ : ↥X), ⟨z, hzX⟩⁆ = 1 := by
    rw [map_commutatorElement]
    apply Subtype.ext
    simpa [commutatorElement_def] using h1
  have h3 := θ.injective (h2.trans (map_one θ).symm)
  have h4 := congrArg Subtype.val h3
  exact Subgroup.mem_bot.2 (by simpa [commutatorElement_def] using h4)

theorem isDirectProdOfConj_of_mulEquiv {X K N : Subgroup Γ} {X' K' N' : Subgroup Δ}
    (θ : ↥X ≃* ↥X') (hKX : K ≤ X) (hK : ∀ y : ↥X, (y : Γ) ∈ K ↔ (θ y : Δ) ∈ K')
    (hN : ∀ n ∈ N, ∃ n' ∈ N', ConjIntertwines θ n n')
    (hN' : ∀ n' ∈ N', ∃ n ∈ N, ConjIntertwines θ n n')
    (h : IsDirectProdOfConj X' K' N') : IsDirectProdOfConj X K N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hK'X' : K' ≤ X' := by
    have h1' := h1 K' ⟨1, N'.one_mem, by ext x; simp [Subgroup.mem_map, MulAut.conj_apply]⟩
    exact h1'
  have hcorr : ∀ {n : Γ} {n' : Δ}, ConjIntertwines θ n n' →
      Corr θ (K.map (MulAut.conj n).toMonoidHom) (K'.map (MulAut.conj n').toMonoidHom) := by
    intro n n' hn
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨k, hk, rfl⟩
      obtain ⟨hx, -⟩ := hn ⟨k, hKX hk⟩
      simpa using hx
    · rintro _ ⟨k', hk', rfl⟩
      obtain ⟨κ, hκ⟩ := θ.surjective ⟨k', hK'X' hk'⟩
      have hκk : (θ κ : Δ) = k' := congrArg Subtype.val hκ
      obtain ⟨hx, hθ⟩ := hn κ
      have : (MulAut.conj n').toMonoidHom k' = (θ ⟨n * (κ : Γ) * n⁻¹, hx⟩ : Δ) := by
        rw [hθ, hκk]
        simp
      rw [this]
      exact (θ _).2
    · intro x
      constructor
      · rintro ⟨k, hk, hkx⟩
        obtain ⟨hx, hθ⟩ := hn ⟨k, hKX hk⟩
        have hxeq : x = ⟨n * k * n⁻¹, hx⟩ := Subtype.ext (by simpa using hkx.symm)
        refine ⟨(θ ⟨k, hKX hk⟩ : Δ), (hK ⟨k, hKX hk⟩).1 hk, ?_⟩
        rw [hxeq, hθ]
        simp
      · rintro ⟨k', hk', hk'x⟩
        obtain ⟨κ, hκ⟩ := θ.surjective ⟨k', hK'X' hk'⟩
        have hκk : (θ κ : Δ) = k' := congrArg Subtype.val hκ
        obtain ⟨hx, hθ⟩ := hn κ
        refine ⟨(κ : Γ), (hK κ).2 (hκk ▸ hk'), ?_⟩
        have h5 : θ x = θ ⟨n * (κ : Γ) * n⁻¹, hx⟩ := by
          apply Subtype.ext
          rw [hθ, hκk]
          simpa using hk'x.symm
        have h6 := congrArg Subtype.val (θ.injective h5)
        simpa using h6.symm
  have hpart : ∀ Y ∈ conjSet K N, ∃ Y' ∈ conjSet K' N', Corr θ Y Y' := by
    rintro Y ⟨n, hn, rfl⟩
    obtain ⟨n', hn', hnn⟩ := hN n hn
    exact ⟨_, ⟨n', hn', rfl⟩, hcorr hnn⟩
  have hpart' : ∀ Y' ∈ conjSet K' N', ∃ Y ∈ conjSet K N, Corr θ Y Y' := by
    rintro Y' ⟨n', hn', rfl⟩
    obtain ⟨n, hn, hnn⟩ := hN' n' hn'
    exact ⟨_, ⟨n, hn, rfl⟩, hcorr hnn⟩
  have hle : ∀ Y ∈ conjSet K N, Y ≤ X := fun Y hY => by
    obtain ⟨Y', -, hYY⟩ := hpart Y hY
    exact hYY.1
  refine ⟨hle, ?_, ?_, ?_⟩
  · refine le_antisymm (iSup₂_le hle) ?_
    intro g hg
    have hgθ : (θ ⟨g, hg⟩ : Δ) ∈ ⨆ Y' ∈ conjSet K' N', Y' := by
      rw [h2]
      exact (θ _).2
    have hsub : (⨆ Y' ∈ conjSet K' N', Y') ≤
        ((⨆ Y ∈ conjSet K N, Y).subgroupOf X).map (X'.subtype.comp θ.toMonoidHom) := by
      refine iSup₂_le fun Y' hY' d hd => ?_
      obtain ⟨Y, hY, hYY⟩ := hpart' Y' hY'
      obtain ⟨x, hx⟩ := θ.surjective ⟨d, hYY.2.1 hd⟩
      have hxd : (θ x : Δ) = d := congrArg Subtype.val hx
      subst hxd
      refine ⟨x, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
      exact le_iSup₂ (f := fun Y (_ : Y ∈ conjSet K N) => Y) Y hY ((hYY.2.2 x).2 hd)
    obtain ⟨t, ht, htg⟩ := hsub hgθ
    have htx : t = ⟨g, hg⟩ := by
      apply θ.injective
      apply Subtype.ext
      simpa using htg
    have ht' := Subgroup.mem_subgroupOf.1 ht
    simpa [htx] using ht'
  · intro Y hY Z hZ hYZ
    obtain ⟨Y', hY', hYY⟩ := hpart Y hY
    obtain ⟨Z', hZ', hZZ⟩ := hpart Z hZ
    exact corr_commutator_eq_bot hYY hZZ
      (h3 Y' hY' Z' hZ' (fun e => hYZ ((corr_eq_iff hYY hZZ).2 e)))
  · intro Y hY
    obtain ⟨Y', hY', hYY⟩ := hpart Y hY
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgY, hgU⟩ := Subgroup.mem_inf.1 hg
    have hgX : g ∈ X := hYY.1 hgY
    have hUle : (⨆ Z ∈ conjSet K N, ⨆ (_ : Z ≠ Y), Z) ≤
        ((⨆ Z' ∈ conjSet K' N', ⨆ (_ : Z' ≠ Y'), Z').comap
          (X'.subtype.comp θ.toMonoidHom)).map X.subtype := by
      refine iSup₂_le fun Z hZ => iSup_le fun hZY z hz => ?_
      obtain ⟨Z', hZ', hZZ⟩ := hpart Z hZ
      have hzX : z ∈ X := hZZ.1 hz
      refine ⟨⟨z, hzX⟩, Subgroup.mem_comap.2 ?_, rfl⟩
      have hZ'Y' : Z' ≠ Y' := fun e => hZY ((corr_eq_iff hZZ hYY).2 e)
      have hle' : Z' ≤ ⨆ Z' ∈ conjSet K' N', ⨆ (_ : Z' ≠ Y'), Z' :=
        le_iSup₂_of_le Z' hZ' (le_iSup (fun _ : Z' ≠ Y' => Z') hZ'Y')
      exact hle' ((hZZ.2.2 ⟨z, hzX⟩).1 hz)
    obtain ⟨x, hxU, hxg⟩ := hUle hgU
    have hx : x = ⟨g, hgX⟩ := Subtype.ext hxg
    subst hx
    have h5 : (θ ⟨g, hgX⟩ : Δ) ∈ Y' ⊓ ⨆ Z' ∈ conjSet K' N', ⨆ (_ : Z' ≠ Y'), Z' :=
      ⟨(hYY.2.2 ⟨g, hgX⟩).1 hgY, hxU⟩
    rw [h4 Y' hY'] at h5
    have h6 : θ ⟨g, hgX⟩ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h5)
    have h7 : (⟨g, hgX⟩ : ↥X) = 1 := θ.injective (h6.trans (map_one θ).symm)
    have h8 : g = 1 := congrArg Subtype.val h7
    exact Subgroup.mem_bot.2 h8

end Transport

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
