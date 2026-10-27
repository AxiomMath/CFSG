module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3InnerMem

public section

namespace CFSG.LocalAnalysis.WeakClosure81

namespace W183K3

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y R T L N : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {𝒢 : Set (Subgroup (LGL 2 V))}
  {Zs : Submodule (ZMod 2) V} {m i₀ : ℕ} {δ : Subgroup (LGL 2 V) → ℕ}

private theorem w183K3NC_isSylowIn_imgOf_range {R L N : Subgroup (LGL 2 V)}
    (hcore : QuasiCore R L N) {T : Subgroup (LGL 2 V)} (hTR : IsSylowIn 2 T R) :
    IsSylowIn 2 (imgOf (psiQuot R L hcore.normal) T)
      (psiQuot R L hcore.normal).range := by
  let ψ := psiQuot R L hcore.normal
  have hT2 : IsPGroup 2 T := hTR.isPGroup
  refine ⟨?_, ?_, ?_⟩
  · rw [imgOf, ← Subgroup.map_top ψ]
    exact Subgroup.map_mono le_top
  · rw [imgOf]
    exact (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTR.le).symm).map ψ
  · rw [imgOf, ← Subgroup.map_top ψ]
    rw [Subgroup.relIndex_map_map, top_sup_eq]
    intro h2
    have hdvd : ((T.subgroupOf R) ⊔ ψ.ker).relIndex ⊤ ∣ (T.subgroupOf R).relIndex ⊤ := by
      refine ⟨(T.subgroupOf R).relIndex ((T.subgroupOf R) ⊔ ψ.ker), ?_⟩
      rw [← Subgroup.relIndex_mul_relIndex (H := T.subgroupOf R)
        (K := (T.subgroupOf R) ⊔ ψ.ker) (L := ⊤) le_sup_left le_top, mul_comm]
    have h2' : 2 ∣ (T.subgroupOf R).relIndex ⊤ := h2.trans hdvd
    rw [Subgroup.relIndex_top_right] at h2'
    exact hTR.not_dvd_relIndex (by simpa [Subgroup.relIndex] using h2')

private theorem w183K3NC_isSylowIn_imgOf_inf {R L N : Subgroup (LGL 2 V)}
    (hcore : QuasiCore R L N) {T : Subgroup (LGL 2 V)} (hTR : IsSylowIn 2 (T ⊓ R) R)
    {X₀ : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L))}
    (hX₀ : X₀ ≤ (psiQuot R L hcore.normal).range)
    (hX₀n : ∀ r : ↥R, ∀ x ∈ X₀,
      psiQuot R L hcore.normal r * x * (psiQuot R L hcore.normal r)⁻¹ ∈ X₀) :
    IsSylowIn 2 (imgOf (psiQuot R L hcore.normal) (T ⊓ R) ⊓ X₀) X₀ := by
  let ψ := psiQuot R L hcore.normal
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
  exact IsSylowIn.inf_normal (w183K3NC_isSylowIn_imgOf_range hcore hTR) hX₀ hnorm

theorem w183k3_false_of_dynkin (hc : Br1Base Y Γ VA T 𝒢 Zs m i₀ δ) (hL : Br3OneComp Y T L)
    {X₀ : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L))}
    (hX₀ : X₀ ≤ (psiQuot Y L hL.core.normal).range)
    (hX₀n : ∀ r : ↥Y, ∀ x ∈ X₀,
      psiQuot Y L hL.core.normal r * x * (psiQuot Y L hL.core.normal r)⁻¹ ∈ X₀)
    (hmem : ∀ D ∈ Γ, imgOf (psiQuot Y L hL.core.normal) D ≤ X₀)
    (hnc1 : Br2NormalConj (↥L ⧸ Subgroup.center ↥L) X₀)
    (hnc2 : Br2DynkinMoves (↥L ⧸ Subgroup.center ↥L) X₀) (hrk : ∀ D ∈ Γ, 3 ≤ mRank D)
    (hne : Γ.Nonempty) : False := by
  let ψ := psiQuot Y L hL.core.normal
  have hcore : QuasiCore Y L (quasiCentre L) := hL.core
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
    w183k3_exists_normal_member (R := Y) (T := T) (N := quasiCentre L) hc.h131 le_rfl
      hcore hTR hX₀ hX₀n hnc1 hD₀ (hc.h131.le_G D₀ hD₀) (hmem D₀ hD₀) hD₀card
  have hDT' : D ≤ T := hDT.trans inf_le_left
  have hDR : D ≤ Y := hDT.trans inf_le_right
  have hgenN : ∀ B ∈ 𝒢, B ≤ Subgroup.normalizer (D : Set (LGL 2 V)) := by
    intro B hB
    obtain ⟨hBT, D', hD'mem, hBD', _⟩ := hc.gens B hB
    have hBinf : B ≤ T ⊓ Y := le_inf hBT (hBT.trans hTY)
    have himg : imgOf ψ B ≤ X₀ := (imgOf_mono ψ hBD').trans (hmem D' hD'mem)
    exact hgen B hBinf himg
  have hTne : T ≠ Y := by
    intro hTYeq
    have hY2 : IsPGroup 2 ↥Y := hTYeq ▸ hc.sylow.isPGroup
    exact hcore.not_isPGroup hY2
  have hTN : T ≤ Subgroup.normalizer (D : Set (LGL 2 V)) :=
    hc.weakClosure D hDmem hDT' hgenN T hTY le_rfl hTne
  obtain ⟨τ, hτT, hτdyn⟩ := hL.dynkin
  have hτY : τ ∈ Y := hTY hτT
  let t : MulAut (↥L ⧸ Subgroup.center ↥L) := ψ ⟨τ, hτY⟩
  have hD2 : IsPGroup 2 D := (hc.h131.isElemAb D hDmem).isPGroup
  have hEA : IsElemAbelian 2 (imgOf ψ D) := by
    rw [imgOf]
    exact CFSG.Open.IsElemAbelian.map
      (CFSG.Open.IsElemAbelian.subgroupOf (hc.h131.isElemAb D hDmem) Y) ψ
  have hAcard : 8 ≤ Nat.card (imgOf ψ D) := by
    rw [QuasiCore.card_imgOf_psiQuot hcore hDR hD2]
    exact hDcard
  have hP₀ : IsSylowIn 2 (imgOf ψ (T ⊓ Y) ⊓ X₀) X₀ :=
    w183K3NC_isSylowIn_imgOf_inf hcore hTR hX₀ hX₀n
  have hA_le : imgOf ψ D ≤ imgOf ψ (T ⊓ Y) ⊓ X₀ :=
    le_inf (imgOf_mono ψ hDT) hDimgX
  have ht_mem : t ∈ imgOf ψ (T ⊓ Y) :=
    apply_mem_imgOf ψ (A := T ⊓ Y) (t := τ) ⟨hτT, hτY⟩ hτY
  have htN_T : t ∈ Subgroup.normalizer (imgOf ψ (T ⊓ Y) :
      Set (MulAut (↥L ⧸ Subgroup.center ↥L))) :=
    Subgroup.le_normalizer ht_mem
  have htN_X : t ∈ Subgroup.normalizer (X₀ :
      Set (MulAut (↥L ⧸ Subgroup.center ↥L))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hX₀n ⟨τ, hτY⟩ x hx
    · intro hx
      have h := hX₀n (⟨τ, hτY⟩ : ↥Y)⁻¹ (ψ ⟨τ, hτY⟩ * x * (ψ ⟨τ, hτY⟩)⁻¹) hx
      simpa [ψ, map_inv, mul_assoc] using h
  have htN_P₀ : t ∈ Subgroup.normalizer (imgOf ψ (T ⊓ Y) ⊓ X₀ :
      Set (MulAut (↥L ⧸ Subgroup.center ↥L))) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨htN_T, htN_X⟩
  have ht_dyn : ActsOnDynkinMod ⊥ (innAutOf (↥L ⧸ Subgroup.center ↥L)) t :=
    QuasiCore.psiQuot_dynkin hcore hτY hτdyn
  have htN_A : t ∈ Subgroup.normalizer (imgOf ψ D :
      Set (MulAut (↥L ⧸ Subgroup.center ↥L))) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (imgOf ψ D).map (MulAut.conj (ψ ⟨τ, hτY⟩)).toMonoidHom = imgOf ψ D
    rw [← imgOf_cj ψ hDR hτY]
    have hcj : cj τ D = D :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := D) (g := τ)).mp (hTN hτT)
    rw [hcj]
  exact (hnc2 (imgOf ψ (T ⊓ Y) ⊓ X₀) hP₀ (imgOf ψ D) hA_le hEA hAcard hP₀norm t
    htN_P₀ ht_dyn) htN_A

end W183K3

end CFSG.LocalAnalysis.WeakClosure81

end
