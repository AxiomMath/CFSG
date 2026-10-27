module

public import CFSG.Quasithin.Vol2.Ch11SecU1U3P
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IL
public import CFSG.Quasithin.Vol2.Ch11SecU1Main
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5T
public import CFSG.Quasithin.H13.NParamRootFourLift
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PrimeRecognition
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem no_four_group_aux {L Y H : Subgroup G} {y : G} (hYL : Y ≤ L)
    (hyC : y ∈ Subgroup.centralizer (Y : Set G)) (hy1 : y ≠ 1) (hy2 : y * y = 1)
    (hY2 : ∀ s ∈ Y, s * s = 1 → s = 1 ∨ s = y)
    (hLC : ∀ g ∈ L, g ∈ Subgroup.centralizer (Y : Set G) → g = 1 ∨ g = y)
    (hout : ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L → orderOf t₁ = 2 → orderOf t₂ = 2 →
      t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L)
    (hHy : H ≤ Subgroup.centralizer ({y} : Set G)) (ψ : ↥H →* Perm (Fin 5))
    (hψsurj : ∀ σ ∈ alternatingGroup (Fin 5), ∃ s : ↥(Y.subgroupOf H), ψ (s : ↥H) = σ)
    (hψ1 : ∀ s : ↥(Y.subgroupOf H), ψ (s : ↥H) = 1 ↔
      ((s : ↥H) : G) ∈ Subgroup.centralizer (Y : Set G))
    (hψker : ∀ h : ↥H, ψ h = 1 → (h : G) ∈ Subgroup.centralizer (Y : Set G))
    {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hVA : (A.subgroupOf H).map ψ ≤ alternatingGroup (Fin 5))
    (hV4 : Nat.card ↥((A.subgroupOf H).map ψ) = 4) : False := by
  set V := (A.subgroupOf H).map ψ with hV
  obtain ⟨v₁, hv₁, hv₁1, -⟩ := exists_mem_ne_ne (A := V) (by omega) 1 1
  obtain ⟨v₂, hv₂, hv₂1, hv₂v₁⟩ := exists_mem_ne_ne (A := V) (by omega) 1 v₁
  obtain ⟨a₁, ha₁, rfl⟩ := hv₁
  obtain ⟨a₂, ha₂, rfl⟩ := hv₂
  obtain ⟨s₁, hs₁⟩ := hψsurj _ (hVA ⟨a₁, ha₁, rfl⟩)
  obtain ⟨s₂, hs₂⟩ := hψsurj _ (hVA ⟨a₂, ha₂, rfl⟩)
  have hA₁ : ((a₁ : ↥H) : G) ∈ A := Subgroup.mem_subgroupOf.mp ha₁
  have hA₂ : ((a₂ : ↥H) : G) ∈ A := Subgroup.mem_subgroupOf.mp ha₂
  have hS₁ : (((s₁ : ↥H) : G)) ∈ Y := Subgroup.mem_subgroupOf.mp s₁.2
  have hS₂ : (((s₂ : ↥H) : G)) ∈ Y := Subgroup.mem_subgroupOf.mp s₂.2
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hA.2 x hx
  have hn : ∀ a s : ↥H, ψ s = ψ a → (a : G) * (s : G)⁻¹ ∈ Subgroup.centralizer (Y : Set G) := by
    intro a s h
    have h1 : ψ (a * s⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    simpa using hψker _ h1
  have hsC : ∀ (s : ↥(Y.subgroupOf H)) (a : ↥H), ψ (s : ↥H) = ψ a → ψ a ≠ 1 →
      ((s : ↥H) : G) ∉ Subgroup.centralizer (Y : Set G) :=
    fun s a h ha hC => ha (h ▸ (hψ1 s).mpr hC)
  have hn₁y : (a₁ : G) * ((s₁ : ↥H) : G)⁻¹ * y = y * ((a₁ : G) * ((s₁ : ↥H) : G)⁻¹) := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hHy (a₁ * (s₁ : ↥H)⁻¹).2)
    simpa using this
  have hcomm : (a₁ : G) * (a₂ : G) = (a₂ : G) * (a₁ : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isElemAbelian hA hA₂ hA₁)
  have key := mul_mem_centralizer_of_pair hYL hyC hy1 hy2 hY2 hLC hout hS₁ hS₂
    (hn a₁ s₁ hs₁) (hn a₂ s₂ hs₂) hn₁y (hsC s₁ a₁ hs₁ hv₁1) (hsC s₂ a₂ hs₂ hv₂1)
    (hsq _ hA₁) (hsq _ hA₂) hcomm
  have h12 : ψ ((s₁ * s₂ : ↥(Y.subgroupOf H)) : ↥H) = 1 := (hψ1 (s₁ * s₂)).mpr key
  rw [Subgroup.coe_mul, map_mul, hs₁, hs₂] at h12
  have haa : a₁ * a₁ = 1 := Subtype.ext (hsq _ hA₁)
  have hinv : ψ a₁ * ψ a₁ = 1 := by rw [← map_mul, haa, map_one]
  apply hv₂v₁
  calc ψ a₂ = (ψ a₁)⁻¹ := eq_inv_of_mul_eq_one_right h12
    _ = ψ a₁ := inv_eq_of_mul_eq_one_right hinv

theorem nParam_centralizer_le_one_five {L : Subgroup G} {y : G}
    {Y : Subgroup G} (hYL : Y ≤ L) (hYC : Y ≤ Subgroup.centralizer ({y} : Set G))
    (hYn : Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (e : ↥Y ≃* SL(2, ZMod 5)) (hyY : y ∈ Y) (hy1 : y ≠ 1) (hy2 : y * y = 1)
    (hLC : ∀ g ∈ L, g ∈ Subgroup.centralizer (Y : Set G) → g = 1 ∨ g = y)
    (hGL : ∀ g : G, ∃ k : ℕ, g ^ 2 ^ k ∈ L)
    (hout : ∀ t₁ t₂ : G, t₁ ∉ L → t₂ ∉ L → orderOf t₁ = 2 → orderOf t₂ = 2 →
      t₁ * t₂ = t₂ * t₁ → t₁ * t₂ ∈ L) :
    nParam (Subgroup.centralizer ({y} : Set G)) ≤ 1 := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have h4 : ∃ s : Finset (ZMod 5), s.card = 4 := ⟨{0, 1, 2, 3}, by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set H := Subgroup.centralizer ({y} : Set G) with hH
  have hyC : y ∈ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hYC hs))
  have hsl : ∀ {s : G} (hs : s ∈ Y), s * s = 1 → e ⟨s, hs⟩ = 1 ∨ e ⟨s, hs⟩ = -1 :=
    fun hs hss => sl2_eq_one_or_neg_one h2 (by
      rw [← map_mul, show (⟨_, hs⟩ * ⟨_, hs⟩ : ↥Y) = 1 from Subtype.ext hss, map_one])
  have hey : e ⟨y, hyY⟩ = -1 := by
    rcases hsl hyY hy2 with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans (map_one e).symm))) hy1
    · exact h
  have hY2 : ∀ s ∈ Y, s * s = 1 → s = 1 ∨ s = y := by
    intro s hs hss
    rcases hsl hs hss with h | h
    · exact Or.inl (congrArg Subtype.val (e.injective (h.trans (map_one e).symm)))
    · exact Or.inr (congrArg Subtype.val (e.injective (h.trans hey.symm)))
  set Y' : Subgroup ↥H := Y.subgroupOf H with hY'
  have : Y'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYn
  let e' : ↥Y' ≃* SL(2, ZMod 5) := (Subgroup.subgroupOfEquivOfLe hYC).trans e
  obtain ⟨e5⟩ := CFSG.SectionRank.Ccomm.projective_five_alternating
  let E' : ↥Y' ⧸ Subgroup.center ↥Y' ≃* alternatingGroup (Fin 5) :=
    (L3I.quotCenterEquiv e').trans e5
  let ψ : ↥H →* Perm (Fin 5) := LiftS5.autAltFive.symm.toMonoidHom.comp
    ((MulAut.congr E').toMonoidHom.comp (L3I.conjQuotCenter Y'))
  have hψY : ∀ s : ↥Y', ψ (s : ↥H) =
      ((E' (s : ↥Y' ⧸ Subgroup.center ↥Y') : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
    intro s
    apply LiftS5.autAltFive.injective
    have h1 : LiftS5.autAltFive (ψ (s : ↥H)) =
        MulAut.congr E' (L3I.conjQuotCenter Y' (s : ↥H)) := by
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rw [h1, L3I.conjQuotCenter_coe]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [LiftS5.autAltFive_apply, MulAut.conjNormal_apply]
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hψsurj : ∀ σ ∈ alternatingGroup (Fin 5), ∃ s : ↥Y', ψ (s : ↥H) = σ := by
    intro σ hσ
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (E'.symm ⟨σ, hσ⟩)
    refine ⟨q, ?_⟩
    rw [hψY q]
    have : (q : ↥Y' ⧸ Subgroup.center ↥Y') = E'.symm ⟨σ, hσ⟩ := hq
    rw [this, MulEquiv.apply_symm_apply]
  have hA5 : alternatingGroup (Fin 5) ≤ ψ.range := fun σ hσ => by
    obtain ⟨s, hs⟩ := hψsurj σ hσ
    exact ⟨_, hs⟩
  have hcen : ∀ s : ↥Y', s ∈ Subgroup.center ↥Y' ↔
      ((s : ↥H) : G) ∈ Subgroup.centralizer (Y : Set G) := by
    intro s
    rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h t ht
      have h1 := congrArg (fun u : ↥Y' => ((u : ↥H) : G))
        (h ⟨⟨t, hYC ht⟩, Subgroup.mem_subgroupOf.mpr ht⟩)
      exact h1
    · intro h t
      exact Subtype.ext (Subtype.ext (h _ (Subgroup.mem_subgroupOf.mp t.2)))
  have hψ1 : ∀ s : ↥Y', ψ (s : ↥H) = 1 ↔
      ((s : ↥H) : G) ∈ Subgroup.centralizer (Y : Set G) := by
    intro s
    rw [hψY, ← hcen, ← QuotientGroup.eq_one_iff (N := Subgroup.center ↥Y')]
    constructor
    · intro h
      exact E'.injective (Subtype.ext (by rw [h, map_one]; rfl))
    · intro h
      rw [h, map_one]
      rfl
  have hperf : commutator ↥Y' = ⊤ := by
    have : Group.IsPerfect SL(2, ZMod 5) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    have : Group.IsPerfect ↥Y' := Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom)
      e'.symm.surjective
    exact Group.isPerfect_def.mp this
  have hψker : ∀ h : ↥H, ψ h = 1 → (h : G) ∈ Subgroup.centralizer (Y : Set G) := by
    intro h hh
    have h1 : L3I.conjQuotCenter Y' h = 1 := by
      have h2 : LiftS5.autAltFive.symm (MulAut.congr E' (L3I.conjQuotCenter Y' h)) = 1 := hh
      rwa [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff] at h2
    have h3 := L3I.mem_centralizer_of_mem_ker Y' hperf (MonoidHom.mem_ker.mpr h1)
    rw [Subgroup.mem_centralizer_iff] at h3 ⊢
    intro t ht
    exact congrArg Subtype.val (h3 ⟨t, hYC ht⟩ (Subgroup.mem_subgroupOf.mpr ht))
  have hker : IsPGroup 2 ψ.ker := by
    intro g
    have hgC := hψker (g : ↥H) (MonoidHom.mem_ker.mp g.2)
    obtain ⟨k, hk⟩ := hGL ((g : ↥H) : G)
    have hkC : ((g : ↥H) : G) ^ 2 ^ k ∈ Subgroup.centralizer (Y : Set G) :=
      Subgroup.pow_mem _ hgC _
    refine ⟨k + 1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_succ, pow_mul]
    rcases hLC _ hk hkC with h1 | h1 <;> rw [h1]
    · rw [one_pow]
    · rw [sq, hy2]
  refine ThinA5.nParam_le_one_of_a5Quot ψ hA5 hker ?_
  rintro A - hA ⟨hVA, hV4⟩
  exact no_four_group_aux hYL hyC hy1 hy2 hY2 hLC hout le_rfl ψ hψsurj hψ1 hψker hA hVA hV4

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
