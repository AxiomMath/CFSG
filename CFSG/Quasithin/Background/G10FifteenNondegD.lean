module

public import CFSG.Quasithin.Background.G10FifteenInputs
public import CFSG.Quasithin.Background.G10Stmts
public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem pRank_set_subset {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ} [Fact p.Prime]
    (r : ℕ) (h : ∃ A : Subgroup X, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ r) :
    ∃ A : Subgroup Y, CFSG.IsElementaryAbelian p A ∧ Nat.card A = p ^ r := by
  obtain ⟨A, hA, hc⟩ := h
  refine ⟨A.map e.toMonoidHom, ?_, by rw [Subgroup.card_map_of_injective e.injective, hc]⟩
  exact @CFSG.IsElementaryAbelian.map p _ X Y _ _ A hA e.toMonoidHom

theorem pRank_eq_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {p : ℕ}
    [Fact p.Prime] : CFSG.pRank p X = CFSG.pRank p Y := by
  unfold CFSG.pRank
  congr 1
  ext r
  exact ⟨pRank_set_subset e r, pRank_set_subset e.symm r⟩

theorem isStronglyQuasithin_of_simple (hSQT : SectionSQTInput) {G : Type} [Group G]
    (hq : IsQuotientOfSQTKTauCeti G) (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    CFSG.IsStronglyQuasithin G := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := hq
  have hX : CFSG.SectionRank.IsSQTKCat S := ⟨isStronglyQuasithin_of_tc hst, hkg⟩
  let ψ : ↥(⊤ : Subgroup S) →* G := φ.comp (⊤ : Subgroup S).subtype
  have hψ : Function.Surjective ψ := by
    intro g
    obtain ⟨s, rfl⟩ := hφ g
    exact ⟨⟨s, trivial⟩, rfl⟩
  let e : (↥(⊤ : Subgroup S) ⧸ ψ.ker) ≃* G := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  have : IsSimpleGroup (↥(⊤ : Subgroup S) ⧸ ψ.ker) := e.isSimpleGroup
  have hnab' : ∃ a b : ↥(⊤ : Subgroup S) ⧸ ψ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e.symm a, e.symm b, fun h => hab (by
      have := congrArg e h
      simpa using this)⟩
  have h1 := hSQT S hX ⊤ ψ.ker hnab'
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  rw [pRank_eq_of_mulEquiv' e.symm]
  exact h1 p hp hp2


theorem centralizerOn_normal {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}
    (hU : Invariant H U) :
    ∀ h ∈ H, ∀ r ∈ centralizerOn H U, h * r * h⁻¹ ∈ centralizerOn H U := by
  intro h hh r hr
  refine ⟨H.mul_mem (H.mul_mem hh hr.1) (H.inv_mem hh), fun u hu => ?_⟩
  have h1 : h⁻¹ u ∈ U := hU h⁻¹ (H.inv_mem hh) u hu
  have h3 : h (h⁻¹ u) = u := LinearEquiv.apply_symm_apply h u
  show h (r (h⁻¹ u)) = u
  rw [hr.2 _ h1]
  exact h3

theorem centralizerOn_conj {H : Subgroup (GLV V)} {x : GLV V}
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) {U : Submodule (ZMod 2) V} :
    ∀ r ∈ centralizerOn H U, x * r * x⁻¹ ∈ centralizerOn H (conjSub x U) := by
  intro r hr
  refine ⟨hxH r hr.1, fun u hu => ?_⟩
  have hw : x.symm u ∈ U := mem_conjSub.1 hu
  have h1 : x (x.symm u) = u := LinearEquiv.apply_symm_apply x u
  show x (r (x⁻¹ u)) = u
  have h2 : (x⁻¹ : GLV V) u = x.symm u := rfl
  rw [h2, hr.2 _ hw]
  exact h1

theorem eq_one_of_centralizes_compl {I I' : Submodule (ZMod 2) V} (hc : IsCompl I I')
    {r : GLV V} (h1 : ∀ u ∈ I, r u = u) (h2 : ∀ u ∈ I', r u = u) : r = 1 := by
  ext v
  have hv : v ∈ I ⊔ I' := by
    rw [codisjoint_iff.1 hc.codisjoint]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  show r (a + b) = a + b
  rw [map_add, h1 a ha, h2 b hb]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem centralizers_comm {I : Submodule (ZMod 2) V} (hI : Invariant (normalClosure Γ L) I)
    {x : GLV V} (hx : x ∈ X) (hc : IsCompl I (conjSub x I)) {r r' : GLV V}
    (hr : r ∈ centralizerOn (normalClosure Γ L) I)
    (hr' : r' ∈ centralizerOn (normalClosure Γ L) (conjSub x I)) : r * r' = r' * r := by
  have hI' : Invariant (normalClosure Γ L) (conjSub x I) :=
    hI.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  have hn := centralizerOn_normal hI
  have hn' := centralizerOn_normal hI'
  have h1 : r * r' * r⁻¹ ∈ centralizerOn (normalClosure Γ L) (conjSub x I) :=
    hn' r hr.1 r' hr'
  have h2 : r' * r⁻¹ * r'⁻¹ ∈ centralizerOn (normalClosure Γ L) I := by
    have := hn r' hr'.1 r⁻¹ ((centralizerOn (normalClosure Γ L) I).inv_mem hr)
    exact this
  have h3 : r * r' * r⁻¹ * r'⁻¹ ∈ centralizerOn (normalClosure Γ L) (conjSub x I) :=
    (centralizerOn (normalClosure Γ L) (conjSub x I)).mul_mem h1
      ((centralizerOn (normalClosure Γ L) (conjSub x I)).inv_mem hr')
  have h4 : r * r' * r⁻¹ * r'⁻¹ ∈ centralizerOn (normalClosure Γ L) I := by
    have := (centralizerOn (normalClosure Γ L) I).mul_mem hr h2
    convert this using 1
    group
  have h5 : r * r' * r⁻¹ * r'⁻¹ = 1 :=
    eq_one_of_centralizes_compl hc h4.2 h3.2
  calc r * r' = (r * r' * r⁻¹ * r'⁻¹) * (r' * r) := by group
    _ = r' * r := by rw [h5, one_mul]


theorem dichotomy {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I) {x : GLV V}
    (hx : x ∈ X) (hc : IsCompl I (conjSub x I))
    (hsimp : IsSimpleGroup ↥(restrictRange (normalClosure Γ L) I hI.1)) :
    (∀ r ∈ centralizerOn (normalClosure Γ L) (conjSub x I), r = 1) ∨
      ∀ h ∈ normalClosure Γ L, ∃ r ∈ centralizerOn (normalClosure Γ L) I,
        ∃ r' ∈ centralizerOn (normalClosure Γ L) (conjSub x I), h = r * r' := by
  have hI' : Invariant (normalClosure Γ L) (conjSub x I) :=
    hI.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  set R' := centralizerOn (normalClosure Γ L) (conjSub x I) with hR'
  have hρ' : Function.Surjective (restrictHom (normalClosure Γ L) I hI.1).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hR'le : R' ≤ normalClosure Γ L := fun r hr => hr.1
  have hnorm : (R'.subgroupOf (normalClosure Γ L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hR'le]
    intro h k hh hk
    exact centralizerOn_normal hI' k hk h hh
  have hN : ((R'.subgroupOf (normalClosure Γ L)).map
      (restrictHom (normalClosure Γ L) I hI.1).rangeRestrict).Normal := hnorm.map _ hρ'
  have : IsSimpleGroup ↥(restrictHom (normalClosure Γ L) I hI.1).range := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R'.subgroupOf (normalClosure Γ L)).map
      (restrictHom (normalClosure Γ L) I hI.1).rangeRestrict) with h0 | h1
  · left
    intro r hr
    have hmem : (restrictHom (normalClosure Γ L) I hI.1).rangeRestrict ⟨r, hr.1⟩ ∈
        (R'.subgroupOf (normalClosure Γ L)).map
          (restrictHom (normalClosure Γ L) I hI.1).rangeRestrict := ⟨⟨r, hr.1⟩, hr, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    have h2 : restrictHom (normalClosure Γ L) I hI.1 ⟨r, hr.1⟩ = 1 := congrArg Subtype.val hmem
    rw [restrictHom_eq_one_iff] at h2
    exact eq_one_of_centralizes_compl hc h2 hr.2
  · right
    intro h hh
    have hmem : (restrictHom (normalClosure Γ L) I hI.1).rangeRestrict ⟨h, hh⟩ ∈
        (R'.subgroupOf (normalClosure Γ L)).map
          (restrictHom (normalClosure Γ L) I hI.1).rangeRestrict := by
      rw [h1]
      trivial
    obtain ⟨⟨r', hr'H⟩, hr'mem, heq⟩ := hmem
    have hr' : r' ∈ R' := hr'mem
    have h2 : restrictHom (normalClosure Γ L) I hI.1 ⟨r', hr'H⟩ =
        restrictHom (normalClosure Γ L) I hI.1 ⟨h, hh⟩ := congrArg Subtype.val heq
    refine ⟨h * r'⁻¹, ⟨(normalClosure Γ L).mul_mem hh ((normalClosure Γ L).inv_mem hr'H),
      fun u hu => ?_⟩, r', hr', by group⟩
    have hw : r'⁻¹ u ∈ I := hI.1 r'⁻¹ ((normalClosure Γ L).inv_mem hr'H) u hu
    have h3 := congrArg (fun e : GLV ↥I => ((e ⟨r'⁻¹ u, hw⟩ : ↥I) : V)) h2
    simp only [coe_restrictHom] at h3
    show h (r'⁻¹ u) = u
    rw [← h3]
    exact LinearEquiv.apply_symm_apply r' u

end G108Hyp

end G11

end CFSG.Quasithin
