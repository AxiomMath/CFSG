module

public import CFSG.Quasithin.Background.G2A5Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A5Model
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem commutator_sup_le_of {I VL X Y : Subgroup G} (hXI : X ≤ I) (hYI : Y ≤ I)
    (hIVL : I ≤ Subgroup.normalizer (VL : Set G))
    (hX : ∀ x ∈ X, ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ VL)
    (hY : ∀ x ∈ Y, ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ VL) : ⁅X ⊔ Y, I⁆ ≤ VL := by
  rw [Subgroup.commutator_le]
  let Z : Subgroup G :=
    { carrier := {x | x ∈ I ∧ ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ VL}
      one_mem' := ⟨I.one_mem, fun y _ => by simp⟩
      mul_mem' := by
        rintro x₁ x₂ ⟨hx₁I, hx₁⟩ ⟨hx₂I, hx₂⟩
        refine ⟨I.mul_mem hx₁I hx₂I, fun y hy => ?_⟩
        have h1 : x₁ * (x₂ * y * x₂⁻¹ * y⁻¹) * x₁⁻¹ ∈ VL :=
          (Subgroup.mem_normalizer_iff.1 (hIVL hx₁I) _).1 (hx₂ y hy)
        have : x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹ =
            (x₁ * (x₂ * y * x₂⁻¹ * y⁻¹) * x₁⁻¹) * (x₁ * y * x₁⁻¹ * y⁻¹) := by group
        rw [this]
        exact VL.mul_mem h1 (hx₁ y hy)
      inv_mem' := by
        rintro x ⟨hxI, hx⟩
        refine ⟨I.inv_mem hxI, fun y hy => ?_⟩
        have h1 : x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x ∈ VL := by
          have := (Subgroup.mem_normalizer_iff.1 (hIVL (I.inv_mem hxI)) _).1
            (VL.inv_mem (hx y hy))
          simpa [mul_assoc] using this
        have : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
        rw [this]
        exact h1 }
  have hZ : X ⊔ Y ≤ Z := sup_le (fun x hx => ⟨hXI hx, hX x hx⟩) (fun x hx => ⟨hYI hx, hY x hx⟩)
  intro x hx y hy
  exact (hZ hx).2 y hy

namespace RawData5

variable {L K V₁ : Subgroup G} (D : RawData5 L K (conjClosure V₁ L))

include D

theorem rconj_V₁_le_VL {k : G} (hk : k ∈ L) : rconj V₁ k ≤ conjClosure V₁ L := by
  intro y hy
  rw [mem_rconj] at hy
  have h1 : k * y * k⁻¹ ∈ conjClosure V₁ L := (le_conjClosure V₁ L) hy
  exact (Subgroup.mem_normalizer_iff.1 (D.hnorm hk) y).2 h1

end RawData5

namespace A5SettingCore

variable [Finite G] {V V₁ L T H : Subgroup G} (S : A5SettingCore V V₁ L T H)

include S

omit [Finite G] in
theorem rconj_V₁_le_VL {k : G} (hk : k ∈ L) : rconj V₁ k ≤ conjClosure V₁ L := S.D.rconj_V₁_le_VL hk

theorem series_facts {g : G} (hg : g ∈ L) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    conjClosure V₁ L ≤ conjClosure V₁ L ⊔ (conjClosure V H ⊓ rconj (conjClosure V H) g) ∧
    conjClosure V₁ L ⊔ (conjClosure V H ⊓ rconj (conjClosure V H) g) ≤
      pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g) ∧
    conjClosure V₁ L ≤ centerOf (pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g)) ∧
    conjClosure V H ⊔ rconj (conjClosure V H) g ≤
      Subgroup.normalizer (conjClosure V₁ L : Set G) ∧
    conjClosure V H ⊔ rconj (conjClosure V H) g ≤
      Subgroup.normalizer
        ((conjClosure V₁ L ⊔ (conjClosure V H ⊓ rconj (conjClosure V H) g) : Subgroup G) :
          Set G) ∧
    conjClosure V H ⊔ rconj (conjClosure V H) g ≤
      Subgroup.normalizer (pCoreOf 2 (conjClosure V H ⊔ rconj (conjClosure V H) g) : Set G) ∧
    ⁅conjClosure V₁ L ⊔ (conjClosure V H ⊓ rconj (conjClosure V H) g),
      conjClosure V H ⊔ rconj (conjClosure V H) g⁆ ≤ conjClosure V₁ L := by
  set U := conjClosure V H with hU
  set VL := conjClosure V₁ L with hVL
  have hI' : U ⊔ rconj U g = L ⊔ U := S.G24_two_aux hg hgN
  set I := U ⊔ rconj U g with hI
  obtain ⟨hIle, hSxO, hSxT, hINorm, hSxU⟩ := sx_facts_gen hI' S.U_le_T
    S.hyp.G22_three.2 S.hyp.base.T_le_normL S.hyp.base.sylow_LT
  have hLI : L ≤ I := hI' ▸ le_sup_left
  have hUI : U ≤ I := le_sup_left
  have hVLI : VL ≤ I := conjClosure_le fun l hl v hv =>
    I.mul_mem (I.mul_mem (hLI hl) (hUI (le_conjClosure V H (S.hyp.base.le_V hv)))) (I.inv_mem (hLI hl))
  have hIVL : I ≤ Subgroup.normalizer (VL : Set G) := hI' ▸ S.LU_le_normVL
  have hcomm : ⁅U ⊓ rconj U g, I⁆ ≤ VL :=
    commutator_inter_le_of hI hIVL (fun x hx y hy => S.hyp.G22_commutator_mem hx hy)
      (le_conjClosure V₁ L) (S.rconj_V₁_le_VL hg)
  have hS₂N : I ≤ Subgroup.normalizer ((VL ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) := by
    refine le_normalizer_sup_of_conj_mem (fun x hx a ha => ?_) (fun x hx b hb => ?_)
    · exact (le_sup_left : VL ≤ VL ⊔ (U ⊓ rconj U g))
        ((Subgroup.mem_normalizer_iff.1 (hIVL hx) a).1 ha)
    · have h1 : x * b * x⁻¹ * b⁻¹ ∈ VL := by
        have := VL.inv_mem (hcomm (Subgroup.commutator_mem_commutator hb hx))
        simpa [commutatorElement_def, mul_assoc] using this
      have h2 : x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
      rw [h2]
      exact Subgroup.mul_mem _ ((le_sup_left : VL ≤ VL ⊔ (U ⊓ rconj U g)) h1)
        ((le_sup_right : U ⊓ rconj U g ≤ VL ⊔ (U ⊓ rconj U g)) hb)
  have hS₂T : VL ⊔ (U ⊓ rconj U g) ≤ T :=
    sup_le (S.VL_le_O.trans S.O_le_T) (inf_le_left.trans S.U_le_T)
  have hS₂S : VL ⊔ (U ⊓ rconj U g) ≤ pCoreOf 2 I :=
    le_pCoreOf_of_le_normalizer 2 (sup_le hVLI (inf_le_left.trans hUI)) hS₂N
      (S.hyp.base.isPGroup_T.to_le hS₂T)
  have hVLS : VL ≤ pCoreOf 2 I := le_pCoreOf_of_le_normalizer 2 hVLI hIVL S.isPGroup_VL
  refine ⟨le_sup_left, hS₂S, ?_, hIVL, hS₂N, le_normalizer_pCoreOf 2 I, ?_⟩
  · intro v hv
    refine ⟨hVLS hv, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    have h1 := S.O_centralizes_VL s (hSxO hs) v hv
    calc s * v = (s * v * s⁻¹) * s := by group
      _ = v * s := by rw [h1]
  · refine commutator_sup_le_of hVLI (inf_le_left.trans hUI) hIVL (fun x hx y hy => ?_)
      (fun x hx y hy => hcomm (Subgroup.commutator_mem_commutator hx hy))
    have h1 : y * x⁻¹ * y⁻¹ ∈ VL := (Subgroup.mem_normalizer_iff.1 (hIVL hy) x⁻¹).1 (VL.inv_mem hx)
    have := VL.mul_mem hx h1
    simpa [mul_assoc] using this

end A5SettingCore

namespace AlmostSpecialA5Core

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Core V V₁ L T H)

include hyp

theorem G24_four {U I S : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) :
    conjClosure V₁ L ≤ conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
      conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤ S ∧ conjClosure V₁ L ≤ centerOf S ∧
      I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) ∧
      I ≤ Subgroup.normalizer ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) ∧
      I ≤ Subgroup.normalizer (S : Set G) := by
  obtain ⟨D⟩ := hyp.natural.nonempty_natData5 hyp.base.le_V (le_conjClosure V₁ L) hyp.card_V₁
    hyp.V_eq
  let St : A5SettingCore V V₁ L T H := ⟨hyp, D⟩
  subst hU hI hS
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := St.series_facts hg hgN
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem G24_five {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    ⁅conjClosure V₁ L ⊔ (U ⊓ rconj U g), I⁆ ≤ conjClosure V₁ L := by
  obtain ⟨D⟩ := hyp.natural.nonempty_natData5 hyp.base.le_V (le_conjClosure V₁ L) hyp.card_V₁
    hyp.V_eq
  let St : A5SettingCore V V₁ L T H := ⟨hyp, D⟩
  subst hU hI
  exact (St.series_facts hg hgN).2.2.2.2.2.2

end AlmostSpecialA5Core

namespace AlmostSpecialA5Hyp

variable [Finite G] {V V₁ L T H : Subgroup G} (hyp : AlmostSpecialA5Hyp V V₁ L T H)

include hyp

theorem G24_four {U I S : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g)
    (hS : S = pCoreOf 2 I) :
    conjClosure V₁ L ≤ conjClosure V₁ L ⊔ (U ⊓ rconj U g) ∧
      conjClosure V₁ L ⊔ (U ⊓ rconj U g) ≤ S ∧ conjClosure V₁ L ≤ centerOf S ∧
      I ≤ Subgroup.normalizer (conjClosure V₁ L : Set G) ∧
      I ≤ Subgroup.normalizer ((conjClosure V₁ L ⊔ (U ⊓ rconj U g) : Subgroup G) : Set G) ∧
      I ≤ Subgroup.normalizer (S : Set G) := hyp.toCore.G24_four hU hg hgN hI hS

theorem G24_five {U I : Subgroup G} (hU : U = conjClosure V H) {g : G} (hg : g ∈ L)
    (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) (hI : I = U ⊔ rconj U g) :
    ⁅conjClosure V₁ L ⊔ (U ⊓ rconj U g), I⁆ ≤ conjClosure V₁ L := hyp.toCore.G24_five hU hg hgN hI

end AlmostSpecialA5Hyp

end CFSG.Quasithin
