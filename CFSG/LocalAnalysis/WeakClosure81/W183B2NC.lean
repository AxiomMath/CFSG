module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2One
public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y R T L : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

private theorem w183b2_isSylowIn_imgOf_inf {R L : Subgroup (LGL 2 V)}
    (hcore : SimpleCore R L) {T : Subgroup (LGL 2 V)} (hTR : IsSylowIn 2 (T ⊓ R) R)
    {X₀ : Subgroup (MulAut ↥L)} (hX₀ : X₀ ≤ (psiOf R L hcore.normal).range)
    (hX₀n : ∀ r : ↥R, ∀ x ∈ X₀,
      psiOf R L hcore.normal r * x * (psiOf R L hcore.normal r)⁻¹ ∈ X₀) :
    IsSylowIn 2 (imgOf (psiOf R L hcore.normal) (T ⊓ R) ⊓ X₀) X₀ := by
  let ψ : ↥R →* MulAut ↥L := psiOf R L hcore.normal
  have hψ : Function.Injective ψ := psiOf_injective hcore
  have hnorm : (X₀.subgroupOf ψ.range).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hX₀]
    intro g hg
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.1 hg
    rw [← hr, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hX₀n r x hx
    · intro hx
      have h := hX₀n r⁻¹ (ψ r * x * (ψ r)⁻¹) hx
      simpa [ψ, map_inv, mul_assoc] using h
  exact IsSylowIn.inf_normal (isSylowIn_imgOf hψ hTR) hX₀ hnorm

theorem w183b2_exists_normal_member {i : ℕ} (hc : Assumption131 Y Γ VA i) (hRY : R ≤ Y)
    (hcore : SimpleCore R L) (hTR : IsSylowIn 2 (T ⊓ R) R) {X₀ : Subgroup (MulAut ↥L)}
    (hX₀ : X₀ ≤ (psiOf R L hcore.normal).range)
    (hX₀n : ∀ r : ↥R, ∀ x ∈ X₀,
      psiOf R L hcore.normal r * x * (psiOf R L hcore.normal r)⁻¹ ∈ X₀)
    (hnc : Br2NormalConj ↥L X₀) {D₀ : Subgroup (LGL 2 V)} (hD₀ : D₀ ∈ Γ) (hD₀R : D₀ ≤ R)
    (hD₀X : imgOf (psiOf R L hcore.normal) D₀ ≤ X₀) (hD₀card : 8 ≤ Nat.card D₀) :
    ∃ D ∈ Γ, D ≤ T ⊓ R ∧ 8 ≤ Nat.card D ∧ imgOf (psiOf R L hcore.normal) D ≤ X₀ ∧
      imgOf (psiOf R L hcore.normal) (T ⊓ R) ⊓ X₀ ≤
        Subgroup.normalizer (imgOf (psiOf R L hcore.normal) D : Set (MulAut ↥L)) ∧
      ∀ B : Subgroup (LGL 2 V), B ≤ T ⊓ R → imgOf (psiOf R L hcore.normal) B ≤ X₀ →
        B ≤ Subgroup.normalizer (D : Set (LGL 2 V)) := by
  let ψ : ↥R →* MulAut ↥L := psiOf R L hcore.normal
  have hψ : Function.Injective ψ := psiOf_injective hcore
  have hP₀ : IsSylowIn 2 (imgOf ψ (T ⊓ R) ⊓ X₀) X₀ :=
    w183b2_isSylowIn_imgOf_inf hcore hTR hX₀ hX₀n
  have hEA₀ : IsElemAbelian 2 (imgOf ψ D₀) :=
    (imgOf_isElemAbelian_iff hψ hD₀R).2 (hc.isElemAb D₀ hD₀)
  have hcard₀ : 8 ≤ Nat.card (imgOf ψ D₀) := by
    rw [imgOf_card hψ hD₀R]
    exact hD₀card
  obtain ⟨g, hg_inn, hg_le, hg_norm⟩ :=
    hnc (imgOf ψ (T ⊓ R) ⊓ X₀) hP₀ (imgOf ψ D₀) hD₀X hEA₀ hcard₀
  obtain ⟨l, hl, hlg⟩ := exists_psiOf_eq_of_mem_innAutOf hcore hg_inn
  let D : Subgroup (LGL 2 V) := cj l D₀
  have hlR : l ∈ R := hcore.le hl
  have hlY : l ∈ Y := hRY hlR
  have hDmem : D ∈ Γ := hc.invariant D₀ hD₀ l hlY
  have hDR : D ≤ R := by
    change D₀.map (MulAut.conj l).toMonoidHom ≤ R
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    show l * x * l⁻¹ ∈ R
    exact R.mul_mem (R.mul_mem hlR (hD₀R hx)) (R.inv_mem hlR)
  have hDimg : imgOf ψ D = autConj g (imgOf ψ D₀) := by
    change imgOf ψ (cj l D₀) = autConj g (imgOf ψ D₀)
    rw [imgOf_cj ψ hD₀R hlR]
    rw [show ψ ⟨l, hcore.le hl⟩ = g from hlg]
    rfl
  have hDT : D ≤ T ⊓ R := by
    have h1 : imgOf ψ D ≤ imgOf ψ (T ⊓ R) := by
      rw [hDimg]
      exact hg_le.trans inf_le_left
    exact (imgOf_le_iff hψ hDR inf_le_right).1 h1
  have hDcard : 8 ≤ Nat.card D := by
    change 8 ≤ Nat.card (cj l D₀)
    rw [card_cj (A := D₀) l]
    exact hD₀card
  have hDimgX : imgOf ψ D ≤ X₀ := by
    rw [hDimg]
    exact hg_le.trans inf_le_right
  have hP₀norm : imgOf ψ (T ⊓ R) ⊓ X₀ ≤
      Subgroup.normalizer (imgOf ψ D : Set (MulAut ↥L)) := by
    rw [hDimg]
    exact hg_norm
  have hgen : ∀ B : Subgroup (LGL 2 V), B ≤ T ⊓ R → imgOf ψ B ≤ X₀ →
      B ≤ Subgroup.normalizer (D : Set (LGL 2 V)) := by
    intro B hBT hBX
    have hBR : B ≤ R := hBT.trans inf_le_right
    have h3 : imgOf ψ B ≤ Subgroup.normalizer (imgOf ψ D : Set (MulAut ↥L)) :=
      (le_inf (imgOf_mono ψ hBT) hBX).trans hP₀norm
    exact (imgOf_normalizer_le_iff hψ hBR hDR).1 h3
  exact ⟨D, hDmem, hDT, hDcard, hDimgX, hP₀norm, hgen⟩

theorem w183b2_false_of_dynkin (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br2OneComp Y T L)
    {X₀ : Subgroup (MulAut ↥L)} (hX₀ : X₀ ≤ (psiOf Y L hL.normal).range)
    (hX₀n : ∀ r : ↥Y, ∀ x ∈ X₀, psiOf Y L hL.normal r * x * (psiOf Y L hL.normal r)⁻¹ ∈ X₀)
    (hmem : ∀ D ∈ Γ, imgOf (psiOf Y L hL.normal) D ≤ X₀) (hnc1 : Br2NormalConj ↥L X₀)
    (hnc2 : Br2DynkinMoves ↥L X₀) (hrk : ∀ D ∈ Γ, 3 ≤ mRank D) (hne : Γ.Nonempty) : False := by
  let ψ : ↥Y →* MulAut ↥L := psiOf Y L hL.normal
  have hcore : SimpleCore Y L := hL.core
  have hψ : Function.Injective ψ := psiOf_injective hcore
  have hTY : T ≤ Y := hc.sylow.le
  have hTR : IsSylowIn 2 (T ⊓ Y) Y := by
    simpa [inf_eq_left.2 hTY] using hc.sylow
  obtain ⟨D₀, hD₀⟩ := hne
  have hD₀card : 8 ≤ Nat.card D₀ := by
    haveI : Nonempty ↥D₀ := (OneMemClass.coe_nonempty D₀).to_subtype
    have h := hrk D₀ hD₀
    dsimp only [mRank] at h
    have h2 : 2 ^ 3 ≤ Nat.card D₀ := Nat.pow_le_of_le_log Nat.card_pos.ne' h
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h2
    exact h2
  obtain ⟨D, hDmem, hDT, hDcard, hDimgX, hP₀norm, hgen⟩ :=
    w183b2_exists_normal_member (R := Y) (T := T) hc.h131 le_rfl hcore hTR hX₀ hX₀n hnc1
      hD₀ (hc.h131.le_G D₀ hD₀) (hmem D₀ hD₀) hD₀card
  have hDT' : D ≤ T := hDT.trans inf_le_left
  have hDR : D ≤ Y := hDT.trans inf_le_right
  have hgenN : ∀ B ∈ 𝒢, B ≤ Subgroup.normalizer (D : Set (LGL 2 V)) := by
    intro B hB
    obtain ⟨hBT, D', hD'mem, hBD', _⟩ := hc.gens B hB
    have hBinf : B ≤ T ⊓ Y := le_inf hBT (hBT.trans hTY)
    have himg : imgOf ψ B ≤ X₀ := (imgOf_mono ψ hBD').trans (hmem D' hD'mem)
    exact hgen B hBinf himg
  have hTne : T ≠ Y := hcore.ne_of_isSylowIn hc.sylow
  have hTN : T ≤ Subgroup.normalizer (D : Set (LGL 2 V)) :=
    hc.weakClosure D hDmem hDT' hgenN T hTY le_rfl hTne
  obtain ⟨τ, hτT, hτdyn⟩ := hL.dynkin
  have hτY : τ ∈ Y := hTY hτT
  let t : MulAut ↥L := ψ ⟨τ, hτY⟩
  have hEA : IsElemAbelian 2 (imgOf ψ D) :=
    (imgOf_isElemAbelian_iff hψ hDR).2 (hc.h131.isElemAb D hDmem)
  have hAcard : 8 ≤ Nat.card (imgOf ψ D) := by
    rw [imgOf_card hψ hDR]
    exact hDcard
  have hP₀ : IsSylowIn 2 (imgOf ψ (T ⊓ Y) ⊓ X₀) X₀ :=
    w183b2_isSylowIn_imgOf_inf hcore hTR hX₀ hX₀n
  have hA_le : imgOf ψ D ≤ imgOf ψ (T ⊓ Y) ⊓ X₀ :=
    le_inf (imgOf_mono ψ hDT) hDimgX
  have ht_mem : t ∈ imgOf ψ (T ⊓ Y) :=
    apply_mem_imgOf (A := T ⊓ Y) ψ ⟨hτT, hτY⟩ hτY
  have htN_T : t ∈ Subgroup.normalizer (imgOf ψ (T ⊓ Y) : Set (MulAut ↥L)) :=
    Subgroup.le_normalizer ht_mem
  have htN_X : t ∈ Subgroup.normalizer (X₀ : Set (MulAut ↥L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hX₀n ⟨τ, hτY⟩ x hx
    · intro hx
      have h := hX₀n (⟨τ, hτY⟩ : ↥Y)⁻¹ (ψ ⟨τ, hτY⟩ * x * (ψ ⟨τ, hτY⟩)⁻¹) hx
      simpa [ψ, map_inv, mul_assoc] using h
  have htN_P₀ : t ∈ Subgroup.normalizer (imgOf ψ (T ⊓ Y) ⊓ X₀ : Set (MulAut ↥L)) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htN_T, htN_X⟩
  have ht_dyn : ActsOnDynkinMod ⊥ (innAutOf ↥L) t := psiOf_dynkin hcore hτY hτdyn
  have htN_A : t ∈ Subgroup.normalizer (imgOf ψ D : Set (MulAut ↥L)) :=
    (imgOf_normalizer_le_iff hψ hTY hDR).2 hTN (apply_mem_imgOf ψ hτT hτY)
  exact (hnc2 (imgOf ψ (T ⊓ Y) ⊓ X₀) hP₀ (imgOf ψ D) hA_le hEA hAcard hP₀norm t htN_P₀ ht_dyn)
    htN_A

end CFSG.LocalAnalysis.WeakClosure81

end
