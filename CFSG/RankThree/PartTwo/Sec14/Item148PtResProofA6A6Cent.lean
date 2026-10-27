module

import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.ComponentClassification
open scoped commutatorElement Pointwise

namespace Item148PtRes

section CentralProduct

variable {Γ : Type*} [Group Γ] [Finite Γ] {U V : Subgroup Γ}

@[expose] def centerIn (U : Subgroup Γ) : Subgroup Γ := (Subgroup.center ↥U).map U.subtype

omit [Finite Γ] in
theorem mem_centerIn_iff {x : Γ} :
    x ∈ centerIn U ↔ ∃ hx : x ∈ U, (⟨x, hx⟩ : ↥U) ∈ Subgroup.center ↥U := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hx, h⟩
    exact ⟨_, h, rfl⟩

omit [Finite Γ] in
theorem centerIn_le (U : Subgroup Γ) : centerIn U ≤ U := Subgroup.map_subtype_le _

theorem inf_eq_centerIn_left (hUV : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hZ : Nat.card (Subgroup.center ↥U) = 3) : U ⊓ V = centerIn U := by
  have hle : U ⊓ V ≤ centerIn U := by
    intro x hx
    refine mem_centerIn_iff.mpr ⟨hx.1, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_⟩
    have h1 : ⁅(y : Γ), x⁆ = 1 := by
      have h2 : ⁅(y : Γ), x⁆ ∈ ⁅U, V⁆ := Subgroup.commutator_mem_commutator y.2 hx.2
      rw [hUV, Subgroup.mem_bot] at h2
      exact h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h3, centerIn, Subgroup.card_map_of_injective U.subtype_injective, hZ]

theorem inf_eq_centerIn_right (hUV : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hZ : Nat.card (Subgroup.center ↥V) = 3) : U ⊓ V = centerIn V := by
  rw [inf_comm]
  refine inf_eq_centerIn_left ?_ (by rwa [inf_comm]) hZ
  rw [Subgroup.commutator_comm, hUV]

omit [Finite Γ] in
theorem exists_mul_eq [hUn : U.Normal] (hUV : U ⊔ V = ⊤) (g : Γ) :
    ∃ y ∈ U, ∃ v ∈ V, g = y * v := by
  have hg : g ∈ ((U ⊔ V : Subgroup Γ) : Set Γ) := by rw [hUV]; exact Subgroup.mem_top g
  rw [Subgroup.coe_mul_of_right_le_normalizer_left U V (by
    rw [Subgroup.normalizer_eq_top_iff.mpr hUn]; exact le_top)] at hg
  obtain ⟨y, hy, v, hv, rfl⟩ := hg
  exact ⟨y, hy, v, hv, rfl⟩

omit [Finite Γ] in
theorem commute_of_commutator_eq_bot (hUV : ⁅U, V⁆ = ⊥) {y v : Γ} (hy : y ∈ U) (hv : v ∈ V) :
    y * v = v * y := by
  have h1 : ⁅y, v⁆ ∈ ⁅U, V⁆ := Subgroup.commutator_mem_commutator hy hv
  rw [hUV, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

omit [Finite Γ] in
theorem mem_center_of_mem_inf [U.Normal] (hUV' : U ⊔ V = ⊤) (hUV : ⁅U, V⁆ = ⊥) {x : Γ}
    (hx : x ∈ U ⊓ V) : x ∈ Subgroup.center Γ := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_eq hUV' g
  have h1 : y * x = x * y := (commute_of_commutator_eq_bot hUV hy hx.2)
  have h2 : x * v = v * x := commute_of_commutator_eq_bot hUV hx.1 hv
  calc y * v * x = y * (x * v) := by rw [mul_assoc, h2]
    _ = x * (y * v) := by rw [← mul_assoc, h1, mul_assoc]

omit [Finite Γ] in
theorem mem_centerIn_of_commutator_mem (e : ↥U ⧸ Subgroup.center ↥U ≃* alternatingGroup (Fin 6))
    {y : Γ} (hy : y ∈ U) (h : ∀ u ∈ U, ⁅y, u⁆ ∈ centerIn U) : y ∈ centerIn U := by
  set π := QuotientGroup.mk' (Subgroup.center ↥U) with hπ
  have hcen : π ⟨y, hy⟩ ∈ Subgroup.center (↥U ⧸ Subgroup.center ↥U) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥U) x
    obtain ⟨hc, hcZ⟩ := mem_centerIn_iff.mp (h u u.2)
    have h1 : ⁅(⟨y, hy⟩ : ↥U), u⁆ = ⟨⁅y, (u : Γ)⁆, hc⟩ :=
      Subtype.ext (by simp [commutatorElement_def])
    have h2 : π ⁅(⟨y, hy⟩ : ↥U), u⁆ = 1 := by
      rw [h1, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hcZ
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2.symm
  have h1 : e (π ⟨y, hy⟩) ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨_, hcen, rfl⟩
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
  have h2 : π ⟨y, hy⟩ = 1 := e.injective (h1.trans (map_one e).symm)
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact mem_centerIn_iff.mpr ⟨hy, h2⟩

omit [Finite Γ] in
theorem inf_le_centerIn_or (e : ↥U ⧸ Subgroup.center ↥U ≃* alternatingGroup (Fin 6))
    {W : Subgroup Γ} (hW : U ≤ Subgroup.normalizer (W : Set Γ)) :
    W ⊓ U ≤ centerIn U ∨ ∀ y ∈ U, ∃ w ∈ W ⊓ U, w⁻¹ * y ∈ centerIn U := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (↥U ⧸ Subgroup.center ↥U) := e.isSimpleGroup
  set π := QuotientGroup.mk' (Subgroup.center ↥U) with hπ
  set P := (W.subgroupOf U).map π with hP
  have hPn : P.Normal := by
    refine Subgroup.Normal.map ⟨fun a ha g => ?_⟩ π (QuotientGroup.mk'_surjective _)
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hW g.2) a).mp ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hb | ht
  · left
    intro x hx
    have h1 : π ⟨x, hx.2⟩ ∈ P := ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx.1, rfl⟩
    rw [hb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_centerIn_iff.mpr ⟨hx.2, h1⟩
  · right
    intro y hy
    have h1 : π ⟨y, hy⟩ ∈ P := ht ▸ Subgroup.mem_top _
    obtain ⟨w, hw, hwy⟩ := h1
    refine ⟨w, ⟨Subgroup.mem_subgroupOf.mp hw, w.2⟩, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hwy
    exact ⟨_, hwy, by simp⟩

omit [Finite Γ] in
theorem top_eq_commutator_sup [hU : U.Normal] [hV : V.Normal] [Group.IsPerfect Γ]
    (hUV' : U ⊔ V = ⊤) (hUV : ⁅U, V⁆ = ⊥) : (⊤ : Subgroup Γ) = ⁅U, U⁆ ⊔ ⁅V, V⁆ := by
  have h1 : ⁅(⊤ : Subgroup Γ), ⊤⁆ = ⊤ :=
    (commutator_def Γ).symm.trans Group.IsPerfect.commutator_eq_top
  have hN : (U ⊔ V).Normal := by
    rw [hUV']
    infer_instance
  rw [← h1, ← hUV', Subgroup.commutator_sup_right U V (U ⊔ V),
    Subgroup.commutator_sup_left U U V, Subgroup.commutator_sup_left V U V, hUV,
    Subgroup.commutator_comm V U, hUV]
  simp

omit [Finite Γ] in
theorem card_eq_of_isTripleCover (hT : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6))) :
    Nat.card U = 1080 := by
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  have h1 := (Subgroup.center ↥U).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr e.toEquiv, hZ, Item148HJ.card_alternatingGroup_six] at h1
  exact h1

theorem eq_or_eq_of_normal [hU : U.Normal] [hV : V.Normal] [Group.IsPerfect Γ]
    (hUV' : U ⊔ V = ⊤) (hUV : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hTU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hTV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6)))
    {W : Subgroup Γ} (hW : W.Normal) (hWc : Nat.card W = Nat.card U) : W = U ∨ W = V := by
  have hcU := card_eq_of_isTripleCover hTU
  have hcV := card_eq_of_isTripleCover hTV
  obtain ⟨hZU, ⟨eU⟩⟩ := hTU
  obtain ⟨hZV, ⟨eV⟩⟩ := hTV
  have hUZ := inf_eq_centerIn_left hUV h3 hZU
  have hVZ := inf_eq_centerIn_right hUV h3 hZV
  have hnorm : ∀ X : Subgroup Γ, X ≤ Subgroup.normalizer (W : Set Γ) := fun X =>
    (Subgroup.normalizer_eq_top_iff.mpr hW).symm ▸ le_top
  have hcommX : ∀ X : Subgroup Γ, X.Normal → ∀ w ∈ W, ∀ y ∈ X, ⁅w, y⁆ ∈ W ⊓ X := by
    intro X hX w hw y hy
    have h1 : w * y * w⁻¹ * y⁻¹ = w * (y * w⁻¹ * y⁻¹) := by group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def, h1]
      exact W.mul_mem hw (hW.conj_mem _ (W.inv_mem hw) y)
    · rw [commutatorElement_def]
      exact X.mul_mem (hX.conj_mem _ hy w) (X.inv_mem hy)
  have hcomm := hcommX U hU
  have hcommV := hcommX V hV
  rcases inf_le_centerIn_or eU (hnorm U) with hA | hA
  ·
    right
    have hWV : W ≤ V := by
      intro w hw
      obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_eq hUV' w
      have hyZ : y ∈ centerIn U := mem_centerIn_of_commutator_mem eU hy fun u hu => by
        have h1 : ⁅y * v, u⁆ = ⁅y, u⁆ := by
          have hvu : v * u = u * v := (commute_of_commutator_eq_bot hUV hu hv).symm
          simp only [commutatorElement_def]
          calc y * v * u * (y * v)⁻¹ * u⁻¹ = y * (v * u) * v⁻¹ * y⁻¹ * u⁻¹ := by group
            _ = y * (u * v) * v⁻¹ * y⁻¹ * u⁻¹ := by rw [hvu]
            _ = y * u * y⁻¹ * u⁻¹ := by group
        have h2 := hcomm _ hw u hu
        rw [h1] at h2
        exact hA h2
      rw [← hUZ] at hyZ
      exact mul_mem hyZ.2 hv
    exact Subgroup.eq_of_le_of_card_ge hWV (by rw [hWc, hcU, hcV])
  · rcases inf_le_centerIn_or eV (hnorm V) with hB | hB
    ·
      left
      have hWU : W ≤ U := by
        intro w hw
        obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_eq hUV' w
        have hvZ : v ∈ centerIn V := mem_centerIn_of_commutator_mem eV hv fun v' hv' => by
          have h1 : ⁅y * v, v'⁆ = ⁅v, v'⁆ := by
            have hyv' : y * v' = v' * y := commute_of_commutator_eq_bot hUV hy hv'
            simp only [commutatorElement_def]
            calc y * v * v' * (y * v)⁻¹ * v'⁻¹
                = y * (v * v' * v⁻¹) * y⁻¹ * v'⁻¹ := by group
              _ = (v * v' * v⁻¹) * y * y⁻¹ * v'⁻¹ := by
                rw [commute_of_commutator_eq_bot hUV hy
                  (mul_mem (mul_mem hv hv') (inv_mem hv))]
              _ = v * v' * v⁻¹ * v'⁻¹ := by group
          have h2 := hcommV _ hw v' hv'
          rw [h1] at h2
          exact hB h2
        rw [← hVZ] at hvZ
        exact mul_mem hy hvZ.1
      exact Subgroup.eq_of_le_of_card_ge hWU (by rw [hWc])
    ·
      exfalso
      have hcen : ∀ x ∈ U ⊓ V, x ∈ Subgroup.center Γ := fun x hx =>
        mem_center_of_mem_inf hUV' hUV hx
      have hsub : ∀ (X : Subgroup Γ), (∀ y ∈ X, ∃ w ∈ W ⊓ X, w⁻¹ * y ∈ centerIn X) →
          U ⊓ V = centerIn X → ⁅X, X⁆ ≤ W := by
        intro X hX hXZ
        rw [Subgroup.commutator_le]
        intro y₁ hy₁ y₂ hy₂
        obtain ⟨w₁, hw₁, hc₁⟩ := hX y₁ hy₁
        obtain ⟨w₂, hw₂, hc₂⟩ := hX y₂ hy₂
        rw [← hXZ] at hc₁ hc₂
        have h1 : ⁅y₁, y₂⁆ = ⁅w₁ * (w₁⁻¹ * y₁), w₂ * (w₂⁻¹ * y₂)⁆ := by group
        rw [h1, Item148HJ.commutatorElement_mul_central (hcen _ hc₁) (hcen _ hc₂)]
        exact Subgroup.commutator_mem_commutator hw₁.1 hw₂.1 |> fun h =>
          (Subgroup.commutator_le_self W) h
      have htop : (⊤ : Subgroup Γ) ≤ W := by
        rw [top_eq_commutator_sup hUV' hUV]
        exact sup_le (hsub U hA hUZ) (hsub V hB hVZ)
      have hWt : W = ⊤ := top_le_iff.mp htop
      have hUt : U = ⊤ := by
        refine Subgroup.eq_of_le_of_card_ge le_top ?_
        rw [← hWt, hWc]
      have h1 : U ⊓ V = V := by rw [hUt, top_inf_eq]
      rw [h1, hcV] at h3
      norm_num at h3

theorem map_eq_of_pow_three [hU : U.Normal] [hV : V.Normal] [Group.IsPerfect Γ]
    (hUV' : U ⊔ V = ⊤) (hUV : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hTU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hTV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6))) {σ : MulAut Γ} (hσ3 : σ ^ 3 = 1) :
    U.map σ.toMonoidHom = U ∧ V.map σ.toMonoidHom = V := by
  have hcU := card_eq_of_isTripleCover hTU
  have hcV := card_eq_of_isTripleCover hTV
  have hn : ∀ W : Subgroup Γ, W.Normal → (W.map σ.toMonoidHom).Normal := fun W hW =>
    hW.map _ σ.surjective
  have hc : ∀ W : Subgroup Γ, Nat.card (W.map σ.toMonoidHom) = Nat.card W := fun W =>
    Subgroup.card_map_of_injective σ.injective
  have hUV_ne : U ≠ V := by
    intro h
    rw [h, inf_idem, hcV] at h3
    norm_num at h3
  have hinj : ∀ W W' : Subgroup Γ, W.map σ.toMonoidHom = W'.map σ.toMonoidHom → W = W' :=
    fun W W' h => Subgroup.map_injective σ.injective h
  have hmapV : V.map σ.toMonoidHom = U ∨ V.map σ.toMonoidHom = V :=
    eq_or_eq_of_normal hUV' hUV h3 hTU hTV (hn V hV) (by rw [hc, hcU, hcV])
  rcases eq_or_eq_of_normal hUV' hUV h3 hTU hTV (hn U hU) (hc U) with h1 | h1
  · refine ⟨h1, ?_⟩
    rcases hmapV with h2 | h2
    · exact absurd (hinj V U (h2.trans h1.symm)) hUV_ne.symm
    · exact h2
  · exfalso
    have h2 : V.map σ.toMonoidHom = U := by
      rcases hmapV with h2 | h2
      · exact h2
      · exact absurd (hinj U V (h1.trans h2.symm)) hUV_ne
    have key : ∀ W : Subgroup Γ, W.map (σ ^ 3).toMonoidHom =
        ((W.map σ.toMonoidHom).map σ.toMonoidHom).map σ.toMonoidHom := by
      intro W
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    have h4 := key U
    rw [h1, h2, h1, hσ3] at h4
    have h5 : U.map (1 : MulAut Γ).toMonoidHom = U := by
      ext x
      simp
    exact hUV_ne (h5.symm.trans h4)

omit [Finite Γ] in
theorem mem_centerIn_of_fixed (e : ↥U ⧸ Subgroup.center ↥U ≃* alternatingGroup (Fin 6))
    {σ : MulAut Γ} (hσ3 : σ ^ 3 = 1) (hσU : U.map σ.toMonoidHom = U) {y₀ : Γ} (hy₀ : y₀ ∈ U)
    (hy₀σ : σ y₀ * y₀⁻¹ ∉ centerIn U) {y : Γ} (hy : y ∈ U) (hyσ : σ y * y⁻¹ ∈ centerIn U)
    {k : ℕ} (hyk : y ^ k ∈ centerIn U) (hk3 : Nat.Coprime k 3) : y ∈ centerIn U := by
  set σU : MulAut ↥U := (σ.subgroupMap U).trans (MulEquiv.subgroupCongr hσU) with hσUdef
  have hσUapp : ∀ (x : Γ) (hx : x ∈ U), (σU ⟨x, hx⟩ : Γ) = σ x := fun x hx => rfl
  set π := QuotientGroup.mk' (Subgroup.center ↥U) with hπ
  set τ : MulAut (alternatingGroup (Fin 6)) :=
    MulAut.congr e (PerfectAutomorphisms.centerQuotientHom ↥U σU) with hτdef
  have hmk : ∀ (x x' : Γ) (hx : x ∈ U) (hx' : x' ∈ U),
      π ⟨x, hx⟩ = π ⟨x', hx'⟩ ↔ x * x'⁻¹ ∈ centerIn U := by
    intro x x' hx hx'
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    constructor
    · intro h1
      exact ⟨_, h1, by simp [div_eq_mul_inv]⟩
    · rintro ⟨z, hz, hzeq⟩
      have : z = (⟨x, hx⟩ : ↥U) / ⟨x', hx'⟩ := Subtype.ext (by
        simp only [Subgroup.coe_subtype] at hzeq
        rw [hzeq, Subgroup.coe_div, div_eq_mul_inv])
      rwa [← this]
  have hτ : ∀ (x : Γ) (hx : x ∈ U),
      τ (e (π ⟨x, hx⟩)) = e (π (σU ⟨x, hx⟩)) := by
    intro x hx
    rw [hτdef, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact congrArg e (PerfectAutomorphisms.onCenterQuotient_apply_mk σU ⟨x, hx⟩)
  have hσU3 : σU ^ 3 = 1 := by
    ext x
    have h1 : ((σU ^ 3) x : Γ) = (σ ^ 3) (x : Γ) := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
      rfl
    rw [h1, hσ3]
    rfl
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτdef, ← map_pow, ← map_pow, hσU3, map_one, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hy₀σ
    have h2 := hτ y₀ hy₀
    rw [h1, MulAut.one_apply] at h2
    have h3 := e.injective h2
    have h4 : σU ⟨y₀, hy₀⟩ = ⟨σ y₀, (hσUapp y₀ hy₀) ▸ (σU ⟨y₀, hy₀⟩).2⟩ := Subtype.ext rfl
    rw [h4] at h3
    exact (hmk _ _ _ _).mp h3.symm
  have hfix : τ (e (π ⟨y, hy⟩)) = e (π ⟨y, hy⟩) := by
    rw [hτ]
    congr 1
    have h4 : σU ⟨y, hy⟩ = ⟨σ y, (hσUapp y hy) ▸ (σU ⟨y, hy⟩).2⟩ := Subtype.ext rfl
    rw [h4]
    exact (hmk _ _ _ _).mpr hyσ
  have hpow : (e (π ⟨y, hy⟩)) ^ k = 1 := by
    rw [← map_pow, ← map_pow]
    have h1 : (⟨y, hy⟩ : ↥U) ^ k ∈ Subgroup.center ↥U := by
      obtain ⟨hyk', hz⟩ := mem_centerIn_iff.mp hyk
      have h2 : (⟨y, hy⟩ : ↥U) ^ k = ⟨y ^ k, hyk'⟩ := Subtype.ext (by simp)
      rw [h2]
      exact hz
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr h1, map_one]
  have h1 := eq_one_of_fixed_alternating_six hτ3 hτ1 hfix hpow hk3
  have h2 : π ⟨y, hy⟩ = 1 := e.injective (h1.trans (map_one e).symm)
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact mem_centerIn_iff.mpr ⟨hy, h2⟩

omit [Finite Γ] in
theorem fixed_of_mem_commutator {σ : MulAut Γ} (hcen : centerIn U ≤ Subgroup.center Γ)
    (htriv : ∀ y ∈ U, σ y * y⁻¹ ∈ centerIn U) {x : Γ} (hx : x ∈ ⁅U, U⁆) : σ x = x := by
  have hle : ⁅U, U⁆ ≤ MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id Γ) := by
    rw [Subgroup.commutator_le]
    intro y₁ hy₁ y₂ hy₂
    have hc : ∀ y ∈ U, y⁻¹ * σ y ∈ Subgroup.center Γ := fun y hy => by
      have h1 := hcen (htriv y hy)
      have h2 : y⁻¹ * σ y = y⁻¹ * (σ y * y⁻¹) * y := by group
      rw [h2, Subgroup.mem_center_iff.mp h1 y⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      exact h1
    change σ ⁅y₁, y₂⁆ = ⁅y₁, y₂⁆
    rw [map_commutatorElement]
    have e₁ : σ y₁ = y₁ * (y₁⁻¹ * σ y₁) := by group
    have e₂ : σ y₂ = y₂ * (y₂⁻¹ * σ y₂) := by group
    rw [e₁, e₂, Item148HJ.commutatorElement_mul_central (hc y₁ hy₁) (hc y₂ hy₂)]
  exact hle hx

omit [Finite Γ] in
theorem mem_zpowers_pow_of_coprime {x : Γ} (hx3 : x ^ 3 = 1) {k : ℕ} (hk3 : Nat.Coprime k 3) :
    x ∈ Subgroup.zpowers (x ^ k) := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hk3 (by norm_num)
  have h1 : x = (x ^ k) ^ m := by
    rw [← pow_mul, pow_eq_pow_mod (k * m) hx3, hm, pow_one]
  have h2 : (x ^ k) ^ m ∈ Subgroup.zpowers (x ^ k) := pow_mem (Subgroup.mem_zpowers (x ^ k)) m
  rwa [← h1] at h2

omit [Finite Γ] in
theorem fixed_components [hU : U.Normal] (hUV' : U ⊔ V = ⊤) (hUV : ⁅U, V⁆ = ⊥)
    {σ : MulAut Γ} (hσU : U.map σ.toMonoidHom = U) (hσV : V.map σ.toMonoidHom = V) {y v : Γ}
    (hy : y ∈ U) (hv : v ∈ V) (hz : σ (y * v) = y * v) {k : ℕ} (hzk : (y * v) ^ k = 1) :
    σ y * y⁻¹ ∈ U ⊓ V ∧ σ v * v⁻¹ ∈ U ⊓ V ∧ y ^ k ∈ U ⊓ V ∧ v ^ k ∈ U ⊓ V := by
  have hσy : σ y ∈ U := hσU ▸ Subgroup.mem_map_of_mem σ.toMonoidHom hy
  have hσv : σ v ∈ V := hσV ▸ Subgroup.mem_map_of_mem σ.toMonoidHom hv
  have hcen : ∀ x ∈ U ⊓ V, x ∈ Subgroup.center Γ := fun x hx =>
    mem_center_of_mem_inf hUV' hUV hx
  have h1 : y⁻¹ * σ y = v * (σ v)⁻¹ := by
    rw [map_mul] at hz
    calc y⁻¹ * σ y = y⁻¹ * (σ y * σ v) * (σ v)⁻¹ := by group
      _ = y⁻¹ * (y * v) * (σ v)⁻¹ := by rw [hz]
      _ = v * (σ v)⁻¹ := by group
  have h2 : y⁻¹ * σ y ∈ U ⊓ V :=
    ⟨U.mul_mem (U.inv_mem hy) hσy, h1 ▸ V.mul_mem hv (V.inv_mem hσv)⟩
  have hc := Subgroup.mem_center_iff.mp (hcen _ h2)
  have e1 : σ y * y⁻¹ = y⁻¹ * σ y := by
    calc σ y * y⁻¹ = y * (y⁻¹ * σ y) * y⁻¹ := by group
      _ = (y⁻¹ * σ y) * y * y⁻¹ := by rw [hc y]
      _ = y⁻¹ * σ y := by group
  have e2 : σ v * v⁻¹ = (v * (σ v)⁻¹)⁻¹ := by group
  have hyv : y * v = v * y := commute_of_commutator_eq_bot hUV hy hv
  have hpow : (y * v) ^ k = y ^ k * v ^ k := (Commute.mul_pow hyv k)
  have h4 : y ^ k = (v ^ k)⁻¹ := eq_inv_of_mul_eq_one_left (hpow ▸ hzk)
  refine ⟨e1 ▸ h2, ?_, ⟨U.pow_mem hy k, h4 ▸ V.inv_mem (V.pow_mem hv k)⟩, ?_⟩
  · rw [e2]
    exact (U ⊓ V).inv_mem (h1 ▸ h2)
  · have h5 : v ^ k = (y ^ k)⁻¹ := by rw [h4, inv_inv]
    exact ⟨h5 ▸ U.inv_mem (U.pow_mem hy k), V.pow_mem hv k⟩

omit [Finite Γ] in
theorem mem_commutator_of_mem [hU : U.Normal] [hV : V.Normal] [Group.IsPerfect Γ]
    (hUV' : U ⊔ V = ⊤) (hUV : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3) {z : Γ} (hzV : z ∈ V)
    {k : ℕ} (hzk : z ^ k = 1) (hk3 : Nat.Coprime k 3) : z ∈ ⁅V, V⁆ := by
  have hU' : (⁅U, U⁆).Normal := Subgroup.commutator_normal U U
  have hV' : (⁅V, V⁆).Normal := Subgroup.commutator_normal V V
  have htop := top_eq_commutator_sup hUV' hUV
  obtain ⟨y', hy', v', hv', rfl⟩ := exists_mul_eq (U := ⁅U, U⁆) htop.symm z
  have hy'U : y' ∈ U := Subgroup.commutator_le_self U hy'
  have hv'V : v' ∈ V := Subgroup.commutator_le_self V hv'
  have hy'V : y' ∈ V := by
    have : y' = y' * v' * v'⁻¹ := by group
    rw [this]
    exact V.mul_mem hzV (V.inv_mem hv'V)
  have hcen := mem_center_of_mem_inf hUV' hUV ⟨hy'U, hy'V⟩
  have hy'3 : y' ^ 3 = 1 := by
    have h1 := Subgroup.orderOf_dvd_natCard (U ⊓ V) ⟨hy'U, hy'V⟩
    rw [h3] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hcomm : y' * v' = v' * y' := (Subgroup.mem_center_iff.mp hcen v').symm
  have hpow : (y' * v') ^ k = y' ^ k * v' ^ k := Commute.mul_pow hcomm k
  have hyk : y' ^ k ∈ ⁅V, V⁆ := by
    have h1 : y' ^ k = (v' ^ k)⁻¹ := eq_inv_of_mul_eq_one_left (hpow ▸ hzk)
    rw [h1]
    exact inv_mem (pow_mem hv' k)
  have hy'c : y' ∈ ⁅V, V⁆ :=
    (Subgroup.zpowers_le.mpr hyk) (mem_zpowers_pow_of_coprime hy'3 hk3)
  exact mul_mem hy'c hv'

omit [Finite Γ] in
theorem commutatorElement_mul_of_commute {y v u : Γ} (hvu : v * u = u * v) :
    ⁅y * v, u⁆ = ⁅y, u⁆ := by
  simp only [commutatorElement_def]
  calc y * v * u * (y * v)⁻¹ * u⁻¹ = y * (v * u) * v⁻¹ * y⁻¹ * u⁻¹ := by group
    _ = y * (u * v) * v⁻¹ * y⁻¹ * u⁻¹ := by rw [hvu]
    _ = y * u * y⁻¹ * u⁻¹ := by group

omit [Finite Γ] in
theorem commutatorElement_mul_of_commute' {y v v' : Γ}
    (h2 : y * (v * v' * v⁻¹) = (v * v' * v⁻¹) * y) : ⁅y * v, v'⁆ = ⁅v, v'⁆ := by
  simp only [commutatorElement_def]
  calc y * v * v' * (y * v)⁻¹ * v'⁻¹ = y * (v * v' * v⁻¹) * y⁻¹ * v'⁻¹ := by group
    _ = (v * v' * v⁻¹) * y * y⁻¹ * v'⁻¹ := by rw [h2]
    _ = v * v' * v⁻¹ * v'⁻¹ := by group

omit [Finite Γ] in
theorem inf_le_centerIn_of_coprime (e : ↥U ⧸ Subgroup.center ↥U ≃* alternatingGroup (Fin 6))
    {W : Subgroup Γ} (hW : U ≤ Subgroup.normalizer (W : Set Γ))
    (h3 : ¬ 3 ∣ Nat.card ↥(W ⊓ U)) : W ⊓ U ≤ centerIn U := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (↥U ⧸ Subgroup.center ↥U) := e.isSimpleGroup
  set π := QuotientGroup.mk' (Subgroup.center ↥U) with hπ
  set P := (W.subgroupOf U).map π with hP
  have hPn : P.Normal := by
    refine Subgroup.Normal.map ⟨fun a ha g => ?_⟩ π (QuotientGroup.mk'_surjective _)
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hW g.2) a).mp ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hb | ht
  · intro x hx
    have h1 : π ⟨x, hx.2⟩ ∈ P := ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx.1, rfl⟩
    rw [hb, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_centerIn_iff.mpr ⟨hx.2, h1⟩
  · exfalso
    have h1 : Nat.card P ∣ Nat.card (W.subgroupOf U) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (W.subgroupOf U) = Nat.card ↥(W ⊓ U) := by
      rw [← Subgroup.card_map_of_injective U.subtype_injective, Subgroup.subgroupOf_map_subtype]
    have h4 : Nat.card P = 360 := by
      rw [ht, Subgroup.card_top, Nat.card_congr e.toEquiv, Item148HJ.card_alternatingGroup_six]
    apply h3
    rw [← h2]
    exact (by norm_num : 3 ∣ 360).trans (h4 ▸ h1)

theorem eq_bot_of_normal_of_coprime [hU : U.Normal] [hV : V.Normal] (hUV' : U ⊔ V = ⊤)
    (hUV : ⁅U, V⁆ = ⊥) (h3 : Nat.card ↥(U ⊓ V) = 3)
    (hTU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hTV : Sec4.IsTripleCover ↥V (alternatingGroup (Fin 6))) {P : Subgroup Γ} (hP : P.Normal)
    (hP3 : ¬ 3 ∣ Nat.card P) : P = ⊥ := by
  obtain ⟨hZU, ⟨eU⟩⟩ := hTU
  obtain ⟨hZV, ⟨eV⟩⟩ := hTV
  have hUZ := inf_eq_centerIn_left hUV h3 hZU
  have hVZ := inf_eq_centerIn_right hUV h3 hZV
  have hnorm : ∀ X : Subgroup Γ, X ≤ Subgroup.normalizer (P : Set Γ) := fun X =>
    (Subgroup.normalizer_eq_top_iff.mpr hP).symm ▸ le_top
  have hcop : ∀ X : Subgroup Γ, ¬ 3 ∣ Nat.card ↥(P ⊓ X) := fun X h =>
    hP3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hsmall : ∀ X : Subgroup Γ, X ≤ U ⊓ V → ¬ 3 ∣ Nat.card X → X = ⊥ := fun X hX hX3 => by
    have h2 : Nat.card X ∣ 3 := h3 ▸ Subgroup.card_dvd_of_le hX
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exact absurd (by rw [h] : 3 ∣ Nat.card X) hX3
  have hPU : P ⊓ U = ⊥ :=
    hsmall _ (hUZ ▸ inf_le_centerIn_of_coprime eU (hnorm U) (hcop U)) (hcop U)
  have hPV : P ⊓ V = ⊥ :=
    hsmall _ (hVZ ▸ inf_le_centerIn_of_coprime eV (hnorm V) (hcop V)) (hcop V)
  have hcU : ⁅P, U⁆ = ⊥ := le_bot_iff.mp (hPU ▸ Subgroup.commutator_le_inf P U)
  have hcV : ⁅P, V⁆ = ⊥ := le_bot_iff.mp (hPV ▸ Subgroup.commutator_le_inf P V)
  have hPZ : P ≤ U ⊓ V := by
    intro p hp
    obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_eq hUV' p
    have hyZ : y ∈ centerIn U := mem_centerIn_of_commutator_mem eU hy fun u hu => by
      have h1 : ⁅y * v, u⁆ ∈ ⁅P, U⁆ := Subgroup.commutator_mem_commutator hp hu
      rw [hcU, Subgroup.mem_bot,
        commutatorElement_mul_of_commute (commute_of_commutator_eq_bot hUV hu hv).symm] at h1
      rw [h1]
      exact one_mem _
    have hvZ : v ∈ centerIn V := mem_centerIn_of_commutator_mem eV hv fun v' hv' => by
      have h1 : ⁅y * v, v'⁆ ∈ ⁅P, V⁆ := Subgroup.commutator_mem_commutator hp hv'
      rw [hcV, Subgroup.mem_bot, commutatorElement_mul_of_commute'
        (commute_of_commutator_eq_bot hUV hy (V.mul_mem (V.mul_mem hv hv') (V.inv_mem hv)))]
        at h1
      rw [h1]
      exact one_mem _
    rw [← hUZ] at hyZ
    rw [← hVZ] at hvZ
    exact (U ⊓ V).mul_mem hyZ hvZ
  exact hsmall P hPZ hP3

end CentralProduct

end Item148PtRes

end CFSG.RankThree.PartTwo.Sec14
