module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4Sec
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreNat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4Tab

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv
open scoped commutatorElement

variable {G : Type} [Group G]

theorem fixSecIn_le (A L N : Subgroup G) : fixSecIn A L N ≤ N :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem eq_of_le_of_relIndex_le [Finite G] {K F Z : Subgroup G} (hle : K ≤ F) (hFZ : F ≤ Z)
    (h : K.relIndex Z ≤ F.relIndex Z) : K = F := by
  have h1 := Subgroup.relIndex_mul_relIndex K F Z hle hFZ
  have hpos := relIndex_pos F Z
  have hpos' := relIndex_pos K F
  have : K.relIndex F = 1 := by
    by_contra hne
    have : 2 ≤ K.relIndex F := by omega
    have : 2 * F.relIndex Z ≤ K.relIndex Z := by rw [← h1]; exact Nat.mul_le_mul_right _ this
    omega
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp this)

section API

variable [Finite G] {X S Z Z₀ : Subgroup G} {θ : ↥X →* Perm (Fin 5)}

omit [Finite G] in
theorem OrthFacts.ker_eq (hF : OrthFacts X S Z Z₀ θ) : θ.ker = (pCoreOf 2 X).subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact hF.ker x.1 x.2

omit [Finite G] in
theorem OrthFacts.card_map (hF : OrthFacts X S Z Z₀ θ) {A : Subgroup G} (hA : A ≤ X) :
    Nat.card ((A.subgroupOf X).map θ) = (A ⊓ pCoreOf 2 X).relIndex A := by
  rw [← Subgroup.relIndex_ker (A.subgroupOf X) θ, hF.ker_eq, Subgroup.relIndex_subgroupOf hA]
  exact (Subgroup.inf_relIndex_left A (pCoreOf 2 X)).symm

omit [Finite G] in
theorem OrthFacts.map_le (hF : OrthFacts X S Z Z₀ θ) {A : Subgroup G} (hA : A ≤ S) :
    (A.subgroupOf X).map θ ≤ S5Syl := by
  rw [← hF.map_S]
  exact Subgroup.map_mono fun x hx => hA hx

omit [Finite G] in
theorem OrthFacts.sq_map {A : Subgroup G} (hA : IsElemAbelian 2 A) : ∀ x ∈ (A.subgroupOf X).map θ, x * x = 1 := by
  rintro _ ⟨y, hy, rfl⟩
  have hy2 : (y : G) ^ 2 = 1 := hA.2 y (Subgroup.mem_subgroupOf.mp hy)
  rw [← map_mul]
  have : y * y = 1 := Subtype.ext (by simpa [pow_two] using hy2)
  rw [this, map_one]

theorem OrthFacts.index_le (hF : OrthFacts X S Z Z₀ θ) {A : Subgroup G} (hA : A ≤ X) :
    (fixW orth ((A.subgroupOf X).map θ)).index ≤
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z := by
  rw [← hF.relIndex_fix A hA]
  refine relIndex_le_of_le Z fun z hz => ?_
  refine Subgroup.subset_closure ⟨hz.1, fun a ha => ?_⟩
  have hc : a * z = z * a := Subgroup.mem_centralizer_iff.mp hz.2 a ha
  have : a * z * a⁻¹ * z⁻¹ = 1 := by rw [hc]; group
  rw [this]
  exact one_mem _

omit [Finite G] in
theorem OrthFacts.index_mul_card (B : Subgroup (Perm (Fin 5))) :
    (fixW orth B).index * Nat.card (fixW orth B) = 16 := by
  rw [Subgroup.index_mul_card, card_orth]

end API

section Offender

variable [Finite G] {X S Z Z₀ : Subgroup G} {θ : ↥X →* Perm (Fin 5)}

theorem offender_image (h : PushHyp X S Z) (hF : OrthFacts X S Z Z₀ θ) {A : Subgroup G}
    (hA : IsMaxElemAbelian S A) (hAQ : ¬ A ≤ pCoreOf 2 X) :
    (A.subgroupOf X).map θ ≤ S5That ∧
      (swap 0 2 ∈ (A.subgroupOf X).map θ ∨ swap 1 3 ∈ (A.subgroupOf X).map θ) ∧
      (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A ∧
      Z ⊓ Subgroup.centralizer (A : Set G) =
        fixSecIn A Z₀ Z := by
  set B := (A.subgroupOf X).map θ with hB
  have hAX : A ≤ X := hA.1.trans h.le_self
  have hne : B ≠ ⊥ := by
    obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
    intro hB0
    have hmem : θ ⟨a, hAX haA⟩ ∈ B := ⟨⟨a, hAX haA⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
    rw [hB0, Subgroup.mem_bot] at hmem
    exact haQ ((hF.ker a (hAX haA)).mp hmem)
  have hm : Nat.card B = (A ⊓ pCoreOf 2 X).relIndex A := hF.card_map hAX
  have hT1 := offender_count h hA
  have hidx : (fixW orth B).index ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z :=
    hF.index_le hAX
  have h16 := OrthFacts.index_mul_card B
  have hc : 0 < Nat.card (fixW orth B) := Nat.card_pos
  have hadm : 16 ≤ Nat.card B * Nat.card (fixW orth B) := by
    rw [← h16]
    exact Nat.mul_le_mul_right _ (hidx.trans (hT1.trans hm.ge))
  obtain ⟨hBT, h01, heq⟩ := adm_subgroup B (hF.map_le hA.1) (OrthFacts.sq_map hA.2.1) hne hadm
  have hBidx : Nat.card B = (fixW orth B).index :=
    Nat.eq_of_mul_eq_mul_right hc (heq.trans h16.symm)
  have hn : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z = (A ⊓ pCoreOf 2 X).relIndex A := by
    rw [← hm]; omega
  refine ⟨hBT, h01, hn, ?_⟩
  refine eq_of_le_of_relIndex_le ?_ (fixSecIn_le _ _ _) ?_
  · intro z hz
    refine Subgroup.subset_closure ⟨hz.1, fun a ha => ?_⟩
    have hc : a * z = z * a := Subgroup.mem_centralizer_iff.mp hz.2 a ha
    have : a * z * a⁻¹ * z⁻¹ = 1 := by rw [hc]; group
    rw [this]
    exact one_mem _
  · rw [hF.relIndex_fix A hAX, hn]
    exact (hm.symm.trans hBidx).le

omit [Finite G] in
theorem le_thompsonJ_of_isMax' {S A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ thompsonJ S :=
  le_iSup₂_of_le A hA le_rfl

theorem image_thompsonJ (h : PushHyp X S Z) (hF : OrthFacts X S Z Z₀ θ)
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    ((thompsonJ S).subgroupOf X).map θ = S5That := by
  have hJS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hJX : thompsonJ S ≤ X := hJS.trans h.le_self
  apply le_antisymm
  ·
    set K : Subgroup G := (S5That.comap θ).map X.subtype with hK
    have hJK : thompsonJ S ≤ K := by
      refine iSup₂_le fun A hA a ha => ?_
      have haX : a ∈ X := h.le_self (hA.1 ha)
      refine ⟨⟨a, haX⟩, ?_, rfl⟩
      show θ ⟨a, haX⟩ ∈ S5That
      by_cases hAQ : A ≤ pCoreOf 2 X
      · rw [(hF.ker a haX).mpr (hAQ ha)]
        exact one_mem _
      · exact (offender_image h hF hA hAQ).1
          ⟨⟨a, haX⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hyy⟩ := hJK (Subgroup.mem_subgroupOf.mp hy)
    have : y' = y := Subtype.ext hyy
    rw [← this]
    exact hy'
  · obtain ⟨A₀, hA₀, hA₀Q⟩ := exists_offender hJ
    have hA₀X : A₀ ≤ X := hA₀.1.trans h.le_self
    obtain ⟨-, h01, -, -⟩ := offender_image h hF hA₀ hA₀Q
    have hmono : (A₀.subgroupOf X).map θ ≤ ((thompsonJ S).subgroupOf X).map θ :=
      Subgroup.map_mono fun x hx =>
        Subgroup.mem_subgroupOf.mpr (le_thompsonJ_of_isMax' hA₀ (Subgroup.mem_subgroupOf.mp hx))
    obtain ⟨s, hsS, hs⟩ : ∃ s ∈ S.subgroupOf X, θ s = S5g := by
      have : S5g ∈ (S5Syl : Subgroup (Perm (Fin 5))) := by
        rw [mem_S5Syl_iff]; unfold S5g; decide +kernel
      rw [← hF.map_S] at this
      obtain ⟨s, hs, hsg⟩ := this
      exact ⟨s, hs, hsg⟩
    have hsn : (s : G) ∈ Subgroup.normalizer (thompsonJ S : Set G) :=
      le_normalizer_thompsonJ_of_le le_rfl (Subgroup.mem_subgroupOf.mp hsS)
    have hconj : ∀ τ ∈ ((thompsonJ S).subgroupOf X).map θ, S5g * τ * S5g⁻¹ ∈
        ((thompsonJ S).subgroupOf X).map θ := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (s : G) * y * (s : G)⁻¹ ∈ thompsonJ S :=
        (Subgroup.mem_normalizer_iff.mp hsn y).mp (Subgroup.mem_subgroupOf.mp hy)
      refine ⟨s * y * s⁻¹, Subgroup.mem_subgroupOf.mpr hy', ?_⟩
      rw [map_mul, map_mul, map_inv, hs]
    have h02 : swap (0 : Fin 5) 2 ∈ ((thompsonJ S).subgroupOf X).map θ ∧
        swap (1 : Fin 5) 3 ∈ ((thompsonJ S).subgroupOf X).map θ := by
      rcases h01 with h0 | h1
      · refine ⟨hmono h0, ?_⟩
        have := hconj _ (hmono h0)
        rwa [show S5g * swap 0 2 * S5g⁻¹ = swap 1 3 by unfold S5g; decide +kernel] at this
      · refine ⟨?_, hmono h1⟩
        have := hconj _ (hmono h1)
        rwa [show S5g * swap 1 3 * S5g⁻¹ = swap 0 2 by unfold S5g; decide +kernel] at this
    intro σ hσ
    rw [mem_S5That_iff] at hσ
    have hσ' : σ = 1 ∨ σ = swap 0 2 ∨ σ = swap 1 3 ∨ σ = swap 0 2 * swap 1 3 := by
      revert σ; unfold S5ThatF; decide +kernel
    rcases hσ' with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact h02.1
    · exact h02.2
    · exact mul_mem h02.1 h02.2

theorem centralizer_thompsonJ (h : PushHyp X S Z) (hF : OrthFacts X S Z Z₀ θ)
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    Z ⊓ Subgroup.centralizer (thompsonJ S : Set G) =
        fixSecIn (thompsonJ S) Z₀ Z ∧
      (Z ⊓ Subgroup.centralizer (thompsonJ S : Set G)).relIndex Z = 4 := by
  have hJX : thompsonJ S ≤ X := (thompsonJ_le_self S).trans h.le_self
  have hle : Z ⊓ Subgroup.centralizer (thompsonJ S : Set G) ≤
      fixSecIn (thompsonJ S) Z₀ Z := by
    intro z hz
    refine Subgroup.subset_closure ⟨hz.1, fun a ha => ?_⟩
    have hc : a * z = z * a := Subgroup.mem_centralizer_iff.mp hz.2 a ha
    have : a * z * a⁻¹ * z⁻¹ = 1 := by rw [hc]; group
    rw [this]
    exact one_mem _
  have hge : fixSecIn (thompsonJ S) Z₀ Z ≤
      Z ⊓ Subgroup.centralizer (thompsonJ S : Set G) := by
    intro z hz
    obtain ⟨hzZ, hzJ⟩ := (hF.mem_fix _ z).mp hz
    refine ⟨hzZ, ?_⟩
    have hJle : thompsonJ S ≤ Subgroup.centralizer ({z} : Set G) := by
      refine iSup₂_le fun A hA a ha => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hAQ : A ≤ pCoreOf 2 X
      · exact (Subgroup.mem_centralizer_iff.mp (h.core_le_centralizer (hAQ ha)) z hzZ).symm
      · obtain ⟨-, -, -, hAeq⟩ := offender_image h hF hA hAQ
        have hzA : z ∈ fixSecIn A Z₀ Z :=
          (hF.mem_fix _ z).mpr ⟨hzZ, fun a' ha' => hzJ a' (le_thompsonJ_of_isMax' hA ha')⟩
        rw [← hAeq] at hzA
        exact Subgroup.mem_centralizer_iff.mp hzA.2 a ha
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (hJle ha)
  have heq := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  rw [heq, hF.relIndex_fix _ hJX, image_thompsonJ h hF hJ]
  exact index_fixW_That


theorem exists_mem_thompsonJ (h : PushHyp X S Z) (hF : OrthFacts X S Z Z₀ θ)
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) {σ : Perm (Fin 5)} (hσ : σ ∈ S5That) :
    ∃ (j : G) (hj : j ∈ X), j ∈ thompsonJ S ∧ θ ⟨j, hj⟩ = σ := by
  rw [← image_thompsonJ h hF hJ] at hσ
  obtain ⟨y, hy, rfl⟩ := hσ
  exact ⟨y.1, y.2, Subgroup.mem_subgroupOf.mp hy, rfl⟩

theorem exists_generated (h : PushHyp X S Z) (hF : OrthFacts X S Z Z₀ θ)
    (hJ : ¬ thompsonJ S ≤ pCoreOf 2 X) :
    ∃ g ∈ pResidualOf 2 X,
      pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g (thompsonJ S)) ⊔ pCoreOf 2 X := by
  have hJX : thompsonJ S ≤ X := (thompsonJ_le_self S).trans h.le_self
  obtain ⟨x, hx⟩ := hF.surj pu4G
  obtain ⟨g₀, hg₀L, hg₀X, hθg⟩ := exists_mem_residual_of_odd (le_refl X) θ x.2
    (σ := pu4G) hx (m := 3) (by decide) pu4G_pow_three
  refine ⟨g₀, hg₀L, fun l hl => ?_⟩
  have hlX : l ∈ X := pResidualOf_le_self X hl
  set I₂ := thompsonJ S ⊔ cj g₀ (thompsonJ S) with hI₂
  have hI₂X : I₂ ≤ X := sup_le hJX (cj_le_of_mem hg₀X hJX)
  set H : Subgroup (Perm (Fin 5)) := (I₂.subgroupOf X).map θ with hH
  have hHJ : ∀ σ ∈ S5That, σ ∈ H := by
    intro σ hσ
    obtain ⟨j, hj, hjJ, hjθ⟩ := exists_mem_thompsonJ h hF hJ hσ
    exact ⟨⟨j, hj⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hjJ), hjθ⟩
  have hHc : ∀ σ ∈ S5That, pu4G * σ * pu4G⁻¹ ∈ H := by
    intro σ hσ
    obtain ⟨j, hj, hjJ, hjθ⟩ := exists_mem_thompsonJ h hF hJ hσ
    have hc : g₀ * j * g₀⁻¹ ∈ cj g₀ (thompsonJ S) := by
      rw [mem_cj]; simpa [mul_assoc] using hjJ
    have hcX : g₀ * j * g₀⁻¹ ∈ X := X.mul_mem (X.mul_mem hg₀X hj) (X.inv_mem hg₀X)
    refine ⟨⟨g₀ * j * g₀⁻¹, hcX⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right hc), ?_⟩
    have : (⟨g₀ * j * g₀⁻¹, hcX⟩ : ↥X) = ⟨g₀, hg₀X⟩ * ⟨j, hj⟩ * ⟨g₀, hg₀X⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hθg, hjθ]
  have h02 : swap (0 : Fin 5) 2 ∈ S5That := by rw [mem_S5That_iff]; unfold S5ThatF; decide +kernel
  have h13 : swap (1 : Fin 5) 3 ∈ S5That := by rw [mem_S5That_iff]; unfold S5ThatF; decide +kernel
  have htop : H = ⊤ :=
    top_of_conj_swaps H (hHJ _ h02) (hHJ _ h13) (hHc _ h02) (hHc _ h13)
  have hlH : θ ⟨l, hlX⟩ ∈ H := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨y, hy, hyl⟩ := hlH
  have hyI : (y : G) ∈ I₂ := Subgroup.mem_subgroupOf.mp hy
  have hq : (y : G)⁻¹ * l ∈ pCoreOf 2 X := by
    have hyl' : (y : G)⁻¹ * l ∈ X := X.mul_mem (X.inv_mem y.2) hlX
    rw [← hF.ker _ hyl']
    have : (⟨(y : G)⁻¹ * l, hyl'⟩ : ↥X) = y⁻¹ * ⟨l, hlX⟩ := rfl
    rw [this, map_mul, map_inv, hyl, inv_mul_cancel]
  have : l = (y : G) * ((y : G)⁻¹ * l) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hyI hq

theorem centralizer_residual_le (hF : OrthFacts X S Z Z₀ θ) (hZ₀Z : Z₀ ≤ Z) :
    Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G) ≤ Z₀ := by
  obtain ⟨x, hx⟩ := hF.surj pu4F
  obtain ⟨l, hl, hlX, hθl⟩ := exists_mem_residual_of_odd (le_refl X) θ x.2 (σ := pu4F) hx
    (m := 5) (by decide) pu4F_pow_five
  have hzl : Subgroup.zpowers l ≤ X := (Subgroup.zpowers_le).mpr hlX
  have hF16 : (fixSecIn (Subgroup.zpowers l) Z₀ Z).relIndex Z = 16 := by
    rw [hF.relIndex_fix _ hzl]
    set B := ((Subgroup.zpowers l).subgroupOf X).map θ with hB
    have hσB : pu4F ∈ B :=
      ⟨⟨l, hlX⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers l), hθl⟩
    have hle : fixW orth B ≤ fixW orth (Subgroup.zpowers pu4F) := fun w hw b hb => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact hw _ (zpow_mem hσB k)
    have h1 : (fixW orth (Subgroup.zpowers pu4F)).index ∣ (fixW orth B).index :=
      Subgroup.index_dvd_of_le hle
    have h2 : (fixW orth B).index ∣ 16 := ⟨Nat.card (fixW orth B), (OrthFacts.index_mul_card B).symm⟩
    have h3 : (fixW orth (Subgroup.zpowers pu4F)).index = 16 := idx_orth_pu4F
    rw [h3] at h1
    exact Nat.dvd_antisymm h2 h1
  have hZ₀F : Z₀ ≤ fixSecIn (Subgroup.zpowers l) Z₀ Z := by
    intro z₀ hz₀
    refine (hF.mem_fix _ z₀).mpr ⟨hZ₀Z hz₀, fun a ha => ?_⟩
    have haX : a ∈ X := hzl ha
    have := Z₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hF.norm haX) z₀).mp hz₀) (Z₀.inv_mem hz₀)
    simpa [mul_assoc] using this
  have hEq : Z₀ = fixSecIn (Subgroup.zpowers l) Z₀ Z :=
    eq_of_le_of_relIndex_le hZ₀F (fixSecIn_le _ _ _) (by rw [hF.relIndex_Z0, hF16])
  intro z hz
  rw [hEq]
  refine (hF.mem_fix _ z).mpr ⟨hz.1, fun a ha => ?_⟩
  have haL : a ∈ pResidualOf 2 X := (Subgroup.zpowers_le).mpr hl ha
  have hc : a * z = z * a := Subgroup.mem_centralizer_iff.mp hz.2 a haL
  have : a * z * a⁻¹ * z⁻¹ = 1 := by rw [hc]; group
  rw [this]
  exact one_mem _

end Offender

end CFSG.Quasithin.F53Push
