module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDel
import CFSG.Quasithin.Background.G119Group2
import CFSG.Permutation.FiveTransitive.AlternatingOddFullImage
import CFSG.Adapters.StatedPSLTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open CFSG.QuasithinUnique.Setup.Offender (weight commGL fixGL)
open CFSG.QuasithinUnique.Setup.Lift (ComponentOffenderOutput DelData)
open scoped MatrixGroups LinearAlgebra.Projectivization

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

section Deleted

variable {L B : Subgroup G} {L₁ B₁ : Subgroup (↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤))}
  {n : ℕ} {F : Type} [Field F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {α : (↥L₁ ⧸ Subgroup.center ↥L₁) ≃* SL(2, F)}

theorem exists_perm_of_delData (e : ↥L ≃* ↥L₁)
    (he : ∀ (l : ↥L) (u : ↥(commOn ρ L ⊤)), (((e l : _ ≃ₗ[ZMod 2] _) u : ↥(commOn ρ L ⊤)) : V) = ρ l u)
    (r : ↥(L ⊔ B) →* ↥(L₁ ⊔ B₁))
    (hr : ∀ (g : ↥(L ⊔ B)) (u : ↥(commOn ρ L ⊤)),
      ((((r g : ↥(L₁ ⊔ B₁)) : _ ≃ₗ[ZMod 2] _) u : ↥(commOn ρ L ⊤)) : V) = ρ g u)
    (hB₁ : ∀ y ∈ B₁, ∃ b ∈ B, ∀ u : ↥(commOn ρ L ⊤), ((y u : ↥(commOn ρ L ⊤)) : V) = ρ b u)
    (hI : commGL L₁ ⊤ = ⊤) (hdel : DelData n L₁ B₁ α) :
    ∃ (Φ : ↥(L ⊔ B) →* Equiv.Perm (ℙ F (Fin 2 → F))) (ψ : V →+ (ℙ F (Fin 2 → F) → ZMod 2)),
      (∀ l (hl : l ∈ L), Φ ⟨l, Subgroup.mem_sup_left hl⟩ ∈ alternatingGroup (ℙ F (Fin 2 → F))) ∧
      (∀ σ ∈ alternatingGroup (ℙ F (Fin 2 → F)), ∃ l, ∃ hl : l ∈ L, Φ ⟨l, Subgroup.mem_sup_left hl⟩ = σ) ∧
      (∀ l (hl : l ∈ L), Φ ⟨l, Subgroup.mem_sup_left hl⟩ = 1 → l = 1) ∧
      (∃ a, ∃ ha : a ∈ B, ∃ x y, x ≠ y ∧ Φ ⟨a, Subgroup.mem_sup_right ha⟩ = Equiv.swap x y) ∧
      (∀ x ∈ commOn ρ L ⊤, ψ x = 0 → x = 0) ∧ (∀ x ∈ commOn ρ L ⊤, ∑ p, ψ x p = 0) ∧
      (∀ z : ℙ F (Fin 2 → F) → ZMod 2, ∑ p, z p = 0 → ∃ x ∈ commOn ρ L ⊤, ψ x = z) ∧
      ∀ (g : ↥(L ⊔ B)) (x : V), x ∈ commOn ρ L ⊤ → ψ (ρ g x) = fun p => ψ x ((Φ g).symm p) := by
  classical
  obtain ⟨-, -, -, β, ψ₀, hβ, -, hL₀, hA₀⟩ := hdel
  have hmemI : ∀ y : ↥(commOn ρ L ⊤), y ∈ commGL L₁ ⊤ := fun y => by rw [hI]; exact Submodule.mem_top
  obtain ⟨t, ht⟩ := LinearMap.exists_leftInverse_of_injective (commOn ρ L ⊤).subtype
    (Submodule.ker_subtype _)
  have htu : ∀ (u : V) (hu : u ∈ commOn ρ L ⊤), t u = ⟨u, hu⟩ := fun u hu =>
    LinearMap.congr_fun ht ⟨u, hu⟩
  let toI : V →ₗ[ZMod 2] ↥(commGL L₁ ⊤) := LinearMap.codRestrict _ t fun v => hmemI _
  let ψ : V →+ (ℙ F (Fin 2 → F) → ZMod 2) :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.evenWeight _).subtype.toAddMonoidHom.comp
      (β.toLinearMap.comp toI).toAddMonoidHom
  have hψ : ∀ (u : V) (hu : u ∈ commOn ρ L ⊤),
      ψ u = (β ⟨⟨u, hu⟩, hmemI _⟩ : ℙ F (Fin 2 → F) → ZMod 2) := by
    intro u hu
    show ((β (toI u) : ↥(CFSG.QuasithinUnique.Setup.SL2Modules.evenWeight _)) :
      ℙ F (Fin 2 → F) → ZMod 2) = _
    rw [show toI u = ⟨⟨u, hu⟩, hmemI _⟩ from Subtype.ext (htu u hu)]
  let Φ : ↥(L ⊔ B) →* Equiv.Perm (ℙ F (Fin 2 → F)) := ψ₀.comp r
  have hrl : ∀ l : ↥L, r ⟨l, Subgroup.mem_sup_left l.2⟩ = ⟨e l, Subgroup.mem_sup_left (e l).2⟩ := by
    intro l
    apply Subtype.ext
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    rw [hr, he]
  have hE : ∀ (g : ↥(L ⊔ B)) (x : V), x ∈ commOn ρ L ⊤ →
      ψ (ρ g x) = fun p => ψ x ((Φ g).symm p) := by
    intro g x hx
    have hgx : ρ g x ∈ commOn ρ L ⊤ := by
      rw [← hr g ⟨x, hx⟩]
      exact Subtype.property _
    rw [hψ _ hgx, hψ x hx]
    exact hβ (r g) ⟨⟨x, hx⟩, hmemI _⟩ ⟨⟨ρ g x, hgx⟩, hmemI _⟩ (Subtype.ext (hr g ⟨x, hx⟩).symm)
  have hK : ∀ x ∈ commOn ρ L ⊤, ψ x = 0 → x = 0 := by
    intro x hx h0
    rw [hψ x hx] at h0
    have h1 : β ⟨⟨x, hx⟩, hmemI _⟩ = 0 := Subtype.ext h0
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact congrArg (fun w : ↥(commGL L₁ ⊤) => ((w : ↥(commOn ρ L ⊤)) : V)) h1
  refine ⟨Φ, ψ, fun l hl => ?_, fun σ hσ => ?_, fun l hl h1 => ?_, ?_, hK, fun x hx => ?_,
    fun z hz => ?_, hE⟩
  · show ψ₀ (r _) ∈ _
    rw [hrl ⟨l, hl⟩, ← hL₀]
    exact Subgroup.mem_map_of_mem ψ₀ (Subgroup.mem_subgroupOf.2 (e ⟨l, hl⟩).2)
  · rw [← hL₀] at hσ
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hσ
    refine ⟨(e.symm ⟨y, hy⟩ : G), (e.symm ⟨y, hy⟩).2, ?_⟩
    show ψ₀ (r _) = ψ₀ y
    rw [hrl (e.symm ⟨y, hy⟩), MulEquiv.apply_symm_apply]
  · have h2 : ∀ u ∈ commOn ρ L ⊤, ρ l u = u := by
      intro u hu
      have h3 := hE ⟨l, Subgroup.mem_sup_left hl⟩ u hu
      rw [h1] at h3
      have h4 : ψ (ρ l u - u) = 0 := by
        rw [map_sub, h3]
        funext p
        show ψ u ((1 : Equiv.Perm (ℙ F (Fin 2 → F))).symm p) - ψ u p = 0
        exact sub_self _
      exact sub_eq_zero.1 (hK _ (Submodule.sub_mem _
        (commOn_top_mapsTo (Subgroup.le_normalizer hl) hu) hu) h4)
    have h5 : e ⟨l, hl⟩ = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      rw [he]
      exact h2 u u.2
    exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff e).1 h5)
  · have hsw : ∃ x y, x ≠ y ∧ Equiv.swap x y ∈ (B₁.subgroupOf (L₁ ⊔ B₁)).map ψ₀ := by
      rcases hA₀ with ⟨x, y, hxy, h⟩ | ⟨x, y, z, w, hxy, -, -, -, -, -, h⟩
      · exact ⟨x, y, hxy, by rw [h]; exact Subgroup.subset_closure (Set.mem_singleton _)⟩
      · exact ⟨x, y, hxy, by rw [h]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩
    obtain ⟨x, y, hxy, hm⟩ := hsw
    obtain ⟨z, hz, hzσ⟩ := Subgroup.mem_map.1 hm
    obtain ⟨b, hb, hbz⟩ := hB₁ _ (Subgroup.mem_subgroupOf.1 hz)
    refine ⟨b, hb, x, y, hxy, ?_⟩
    have hrb : r ⟨b, Subgroup.mem_sup_right hb⟩ = z := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      rw [hr, hbz]
    show ψ₀ (r _) = _
    rw [hrb, hzσ]
  · rw [hψ x hx]
    exact (β _).2
  · obtain ⟨w, hw⟩ := β.surjective ⟨z, hz⟩
    refine ⟨(w : ↥(commOn ρ L ⊤)), (w : ↥(commOn ρ L ⊤)).2, ?_⟩
    rw [hψ _ (w : ↥(commOn ρ L ⊤)).2]
    exact congrArg Subtype.val hw

end Deleted

theorem secNatS5_of_perm {L B : Subgroup G} {Ω : Type} [Fintype Ω] [DecidableEq Ω] (hΩ : Fintype.card Ω = 5)
    (hBe : CFSG.IsElementaryAbelian 2 ↥B) (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (Φ : ↥(L ⊔ B) →* Equiv.Perm Ω) (ψ : V →+ (Ω → ZMod 2))
    (hΦL : ∀ l (hl : l ∈ L), Φ ⟨l, Subgroup.mem_sup_left hl⟩ ∈ alternatingGroup Ω)
    (hΦLs : ∀ σ ∈ alternatingGroup Ω, ∃ l, ∃ hl : l ∈ L, Φ ⟨l, Subgroup.mem_sup_left hl⟩ = σ)
    (hΦLi : ∀ l (hl : l ∈ L), Φ ⟨l, Subgroup.mem_sup_left hl⟩ = 1 → l = 1)
    {a : G} (ha : a ∈ B) (hodd : Equiv.Perm.sign (Φ ⟨a, Subgroup.mem_sup_right ha⟩) = -1)
    (hK : ∀ x ∈ commOn ρ L ⊤, ψ x = 0 → x = 0) (hsum : ∀ x ∈ commOn ρ L ⊤, ∑ p, ψ x p = 0)
    (hsurj : ∀ z : Ω → ZMod 2, ∑ p, z p = 0 → ∃ x ∈ commOn ρ L ⊤, ψ x = z)
    (hE : ∀ (g : ↥(L ⊔ B)) (x : V), x ∈ commOn ρ L ⊤ → ψ (ρ g x) = fun p => ψ x ((Φ g).symm p)) :
    a ∉ L ∧ SecNatS5 ρ (L ⊔ Subgroup.zpowers a) (commOn ρ L ⊤) ⊥ ∧
      ∀ b ∈ B, ∃ h ∈ L ⊔ Subgroup.zpowers a, ∀ u ∈ commOn ρ L ⊤, ρ b u = ρ h u := by
  classical
  haveI := hBe
  have ha2 : a * a = 1 := by rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian a ha
  have hnorm : ∀ m ∈ L, a * m * a⁻¹ ∈ L := fun m hm =>
    (Subgroup.mem_normalizer_iff.1 (hBN ha) m).1 hm
  have hH : L ⊔ Subgroup.zpowers a ≤ L ⊔ B :=
    sup_le le_sup_left (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right ha))
  have hHN : L ⊔ B ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hBN
  have haL : a ∉ L := fun haL => by
    have h1 := hΦL a haL
    have h2 : Equiv.Perm.sign (Φ ⟨a, Subgroup.mem_sup_left haL⟩) = -1 := hodd
    rw [Equiv.Perm.mem_alternatingGroup] at h1
    rw [h1] at h2
    exact absurd h2 (by decide)
  let Φ₁ : ↥(L ⊔ Subgroup.zpowers a) →* Equiv.Perm Ω := Φ.comp (Subgroup.inclusion hH)
  have hinj : Function.Injective Φ₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    rw [Subgroup.mem_bot]
    rcases CFSG.Quasithin.G11.g119_mem_or_mul_mem_of_sup_zpowers ha2 hnorm h.2 with hL | hL
    · exact Subtype.ext (hΦLi _ hL hh)
    · exfalso
      have h1 := hΦL _ hL
      rw [Equiv.Perm.mem_alternatingGroup] at h1
      have h2 : (⟨(h : G) * a, Subgroup.mem_sup_left hL⟩ : ↥(L ⊔ B)) =
          Subgroup.inclusion hH h * ⟨a, Subgroup.mem_sup_right ha⟩ := rfl
      have h3 : Φ (Subgroup.inclusion hH h) = 1 := hh
      rw [h2, map_mul, Equiv.Perm.sign_mul, h3, Equiv.Perm.sign_one, one_mul, hodd] at h1
      exact absurd h1 (by decide)
  have hsurjΦ : Function.Surjective Φ₁ := by
    rw [← MonoidHom.range_eq_top]
    refine CFSG.FiveTransitive.AlternatingOddFullImage.eq_top _ (fun σ hσ => ?_)
      (Φ₁ ⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩) (MonoidHom.mem_range.2 ⟨_, rfl⟩) hodd
    obtain ⟨l, hl, rfl⟩ := hΦLs σ hσ
    exact MonoidHom.mem_range.2 ⟨⟨l, Subgroup.mem_sup_left hl⟩, rfl⟩
  have htriv : ∀ g : ↥(L ⊔ B), Φ g = 1 → ∀ x ∈ commOn ρ L ⊤, ρ g x = x := by
    intro g hg x hx
    have h1 := hE g x hx
    rw [hg] at h1
    refine sub_eq_zero.1 (hK _ (Submodule.sub_mem _ (commOn_top_mapsTo (hHN g.2) hx) hx) ?_)
    rw [map_sub, h1]
    funext p
    show ψ x ((1 : Equiv.Perm Ω).symm p) - ψ x p = 0
    exact sub_self _
  let eΩ : Ω ≃ Fin 5 := Fintype.equivFinOfCardEq hΩ
  let φ : ↥(L ⊔ Subgroup.zpowers a) ≃* Equiv.Perm (Fin 5) :=
    (MulEquiv.ofBijective Φ₁ ⟨hinj, hsurjΦ⟩).trans eΩ.permCongrHom
  let κ : (Ω → ZMod 2) →+ (Fin 5 → ZMod 2) :=
    { toFun := fun f i => f (eΩ.symm i), map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨haL, ⟨isInvariant_commOn_top (sup_le Subgroup.le_normalizer
      (Subgroup.zpowers_le.2 (hBN ha))), fun _ _ x hx => ?_, bot_le, φ, κ.comp ψ, fun x hx => ?_,
    fun x hx h0 => ?_, fun x hx => ?_, fun y hy => ?_, fun h x hx => ?_⟩, fun b hb => ?_⟩
  · rw [(Submodule.mem_bot _).1 hx, map_zero]
    exact Submodule.zero_mem _
  · rw [(Submodule.mem_bot _).1 hx, map_zero]
  · rw [Submodule.mem_bot]
    refine hK x hx (funext fun p => ?_)
    have h1 : ψ x (eΩ.symm (eΩ p)) = 0 := congrFun h0 (eΩ p)
    rw [Equiv.symm_apply_apply] at h1
    exact h1
  · show ∑ i, ψ x (eΩ.symm i) = 0
    rw [Equiv.sum_comp eΩ.symm (ψ x)]
    exact hsum x hx
  · obtain ⟨x, hx, hxy⟩ := hsurj (fun p => y (eΩ p)) (by rw [Equiv.sum_comp eΩ y]; exact hy)
    refine ⟨x, hx, funext fun i => ?_⟩
    show ψ x (eΩ.symm i) = y i
    rw [hxy]
    exact congrArg y (eΩ.apply_symm_apply i)
  · have h1 := hE (Subgroup.inclusion hH h) x hx
    funext i
    have h2 : (φ h).symm i = eΩ ((Φ (Subgroup.inclusion hH h)).symm (eΩ.symm i)) := rfl
    show ψ (ρ (Subgroup.inclusion hH h : G) x) (eΩ.symm i) = ψ x (eΩ.symm ((φ h).symm i))
    rw [h1, h2, Equiv.symm_apply_apply]
  · obtain ⟨h, hh⟩ := hsurjΦ (Φ ⟨b, Subgroup.mem_sup_right hb⟩)
    refine ⟨h, h.2, fun u hu => ?_⟩
    have h1 : Φ ((Subgroup.inclusion hH h)⁻¹ * ⟨b, Subgroup.mem_sup_right hb⟩) = 1 := by
      rw [map_mul, map_inv]
      exact inv_mul_eq_one.2 hh
    have h2 : ρ ((h : G)⁻¹ * b) u = u := htriv _ h1 u hu
    calc ρ b u = ρ (h : G) (ρ ((h : G)⁻¹ * b) u) := by rw [glRep_mul_apply, glRep_apply_inv]
      _ = ρ h u := by rw [h2]

theorem dichotomy_of_componentOffenderOutput [Finite G] [Finite V] (hρ : Function.Injective ρ)
    {L : Subgroup G} (hL : IsComponentOf L ⊤) {n : ℕ} (hX : IsL2 ↥L n) {A : Subgroup G} (hA : A ∈ calP ρ)
    (hLA : ⁅L, A⁆ ≠ ⊥) {B : Subgroup G} (hBA : B ≤ A) (hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ B) (commOn ρ L ⊤))
    (hT : TransportGL ρ L B hinv) {F : Type} [Field F] [Fintype F] [Fintype (ℙ F (Fin 2 → F))]
    [DecidableEq (ℙ F (Fin 2 → F))] (hF : Fintype.card F = 2 ^ n)
    {α : (↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) ⧸
      Subgroup.center ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L)) ≃* SL(2, F)}
    (hout : ComponentOffenderOutput (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L)
      (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B) n α (commGL (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) ⊤)) :
    (NatL2 ρ L (commOn ρ L ⊤) (commOn ρ L ⊤ ⊓ fixSub ρ L) n ∧
        ∀ b ∈ B, ∃ l ∈ L, ∀ u ∈ commOn ρ L ⊤, ρ b u = ρ l u) ∨
      (n = 2 ∧ commOn ρ L ⊤ ⊓ fixSub ρ L = ⊥ ∧ ∃ a ∈ B, a ∉ L ∧
        SecNatS5 ρ (L ⊔ Subgroup.zpowers a) (commOn ρ L ⊤) ⊥ ∧
        ∀ b ∈ B, ∃ h ∈ L ⊔ Subgroup.zpowers a, ∀ u ∈ commOn ρ L ⊤, ρ b u = ρ h u) := by
  classical
  haveI : IsSimpleGroup ↥L := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
  obtain ⟨hUL, hnt⟩ := commOn_facts_of_mem_calP hρ hL hA hLA
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans (le_normalizer_of_mem_calP hρ hL hA)
  obtain ⟨e, he'⟩ := hT.iso
  have he : ∀ (l : ↥L) (u : ↥(commOn ρ L ⊤)),
      (((e l : _ ≃ₗ[ZMod 2] _) u : ↥(commOn ρ L ⊤)) : V) = ρ l u := fun l u => by rw [he' l]; rfl
  obtain ⟨θ, hθ, hnat | ⟨hdel, hZ⟩⟩ := hout.alternatives
  · exact Or.inl ⟨natL2_of_naturalAlt (by rw [Nat.card_eq_fintype_card, hF]) e he hT.center hT.commU hout
      hnat, exists_eq_apply_of_naturalAlt hUL hnt hBN e he (fun b hb => ⟨_, resGL_mem_imgGL hb
        (Subgroup.mem_sup_right hb), fun u => rfl⟩) hT.commU hout hnat⟩
  right
  have hD := CFSG.QuasithinUnique.Setup.Lift.delData_of_deleted α hout.A_norm
    (CFSG.QuasithinUnique.Setup.Layer.isInvariant_sup_subgroup hout.inv_L hout.inv_A) rfl hZ θ hθ hdel
  have hZ' : commOn ρ L ⊤ ⊓ fixSub ρ L = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, hfix⟩
    have h1 : (⟨v, hv⟩ : ↥(commOn ρ L ⊤)) ∈ commGL (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) ⊤ ⊓
        fixGL (imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L) := by
      refine ⟨by rw [hT.commU]; exact Submodule.mem_top, fun y hy => ?_⟩
      obtain ⟨l, hl⟩ := e.surjective ⟨y, hy⟩
      have hy' : y = (e l : _ ≃ₗ[ZMod 2] _) := congrArg Subtype.val hl.symm
      subst hy'
      apply Subtype.ext
      show (((e l : ↥(commOn ρ L ⊤) ≃ₗ[ZMod 2] ↥(commOn ρ L ⊤)) ⟨v, hv⟩ : ↥(commOn ρ L ⊤)) : V) = v
      rw [he]
      exact hfix l l.2
    rw [hZ] at h1
    exact (Submodule.mem_bot _).2 (congrArg Subtype.val ((Submodule.mem_bot _).1 h1))
  have hsup : imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv (L ⊔ B) =
      imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L ⊔ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B := by
    simp only [imgGL]
    rw [Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.map_sup]
  let r : ↥(L ⊔ B) →* ↥(imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv L ⊔ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B) :=
    (resGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv).codRestrict _ fun g => by
      rw [← hsup]
      exact resGL_mem_imgGL g.2 g.2
  have hB₁ : ∀ z ∈ imgGL ρ (L ⊔ B) (commOn ρ L ⊤) hinv B, ∃ b ∈ B,
      ∀ u : ↥(commOn ρ L ⊤), ((z u : ↥(commOn ρ L ⊤)) : V) = ρ b u := by
    intro z hz
    obtain ⟨g, hgB, rfl⟩ := mem_imgGL.1 hz
    exact ⟨g, hgB, fun u => rfl⟩
  obtain ⟨Φ, ψ, hΦL, hΦLs, hΦLi, ⟨a, ha, x, y, hxy, hΦa⟩, hK, hsum, hsurj, hE⟩ :=
    exists_perm_of_delData e he r (fun g u => rfl) hB₁ hT.commU hD
  obtain ⟨haL, hS5, hBa⟩ := secNatS5_of_perm hdel.2.2.1 ((isElementaryAbelian_of_mem_calP hA).of_le hBA)
    hBN Φ ψ hΦL hΦLs hΦLi ha (by rw [hΦa]; exact Equiv.Perm.sign_swap hxy) hK hsum hsurj hE
  exact ⟨hD.1, hZ', a, ha, haL, hS5, hBa⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
