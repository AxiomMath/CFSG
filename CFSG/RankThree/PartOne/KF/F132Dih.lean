module

public import CFSG.RankThree.PartOne.KF.F132D8

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G] {p : ℕ} {c : G} {L E F : Subgroup G} {Γ V : Type} [Group Γ] [Group V]
  {act : Γ →* MulAut V}

@[expose] noncomputable def weylG (S : WCtx act L F) (R : Sec12Three.Restr c L E F)
    (hinj : Function.Injective S.actF) : ↥(torusImage E L) ≃* Γ :=
  (Classical.choose R.exists_resE).trans
    ((MulEquiv.subgroupCongr S.torusImage_eq_range).trans (MonoidHom.ofInjective hinj).symm)

theorem actF_weylG_eq (S : WCtx act L F) (R : Sec12Three.Restr c L E F)
    (hinj : Function.Injective S.actF) (γ : ↥(torusImage E L)) :
    S.actF (weylG S R hinj γ) = (((Classical.choose R.exists_resE) γ : ↥(torusImage F L)) :
      MulAut F) := by
  have h := (MonoidHom.ofInjective hinj).apply_symm_apply
    ⟨(((Classical.choose R.exists_resE) γ : ↥(torusImage F L)) : MulAut F),
      S.torusImage_eq_range ▸ ((Classical.choose R.exists_resE) γ).2⟩
  exact congrArg Subtype.val h

theorem actF_weylG (S : WCtx act L F) (R : Sec12Three.Restr c L E F)
    (hinj : Function.Injective S.actF) {x : G} (hxL : x ∈ L)
    (hxE : x ∈ Subgroup.normalizer (E : Set G)) (hxF : x ∈ Subgroup.normalizer (F : Set G)) :
    S.actF (weylG S R hinj ⟨conjAut E x hxE, Sec12Three.mem_torusImage_iff.mpr
      ⟨x, hxL, hxE, rfl⟩⟩) = F.normalizerMonoidHom ⟨x, hxF⟩ := by
  classical
  set γ : ↥(torusImage E L) := ⟨conjAut E x hxE, Sec12Three.mem_torusImage_iff.mpr
    ⟨x, hxL, hxE, rfl⟩⟩ with hγ
  obtain ⟨x', -, hx'E, hx'F, h1, h2⟩ := Classical.choose_spec R.exists_resE γ
  have hxx' : F.normalizerMonoidHom ⟨x, hxF⟩ = F.normalizerMonoidHom ⟨x', hx'F⟩ :=
    normalizerMonoidHom_restrict_eq R hxE hxF hx'E hx'F h1
  rw [actF_weylG_eq, h2, hxx']

theorem isAutReflection_iff_weylG (S : WCtx act L F) (R : Sec12Three.Restr c L E F)
    (hinj : Function.Injective S.actF) (γ : ↥(torusImage E L)) :
    IsAutReflection p E (γ : MulAut E) ↔ IsAutReflection p F (S.actF (weylG S R hinj γ)) := by
  classical
  obtain ⟨x, hxL, hxE, hxF, h1, h2⟩ := Classical.choose_spec R.exists_resE γ
  set e := Classical.choose R.exists_resE with he
  have hmoved : autMovedInG E (γ : MulAut E) =
      autMovedInG F ((e γ : ↥(torusImage F L)) : MulAut F) := by
    rw [h1, h2]
    exact R.autMovedInG_eq (R.comm x hxL).symm hxE hxF
  have hcard : Nat.card (autMoved E (γ : MulAut E)) =
      Nat.card (autMoved F ((e γ : ↥(torusImage F L)) : MulAut F)) := by
    rw [← Sec12Three.natCard_autMovedInG, ← Sec12Three.natCard_autMovedInG, hmoved]
  have hord : orderOf (γ : MulAut E) = orderOf ((e γ : ↥(torusImage F L)) : MulAut F) := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  rw [actF_weylG_eq]
  unfold IsAutReflection
  rw [hord, hcard]

section Conj

variable {n : ℕ} (S : WCtx act L F) (R : Sec12Three.Restr c L E F)
  (hinj : Function.Injective S.actF) (eΓ : Γ ≃* DihedralGroup n)

theorem exists_conj_of_parity_G
    (hconj : ∀ i₀ i : ZMod n, i₀.val % 2 = i.val % 2 →
      ∃ w : DihedralGroup n, w * DihedralGroup.sr i₀ * w⁻¹ = DihedralGroup.sr i)
    {t₀ t : MulAut E} {ht₀ : t₀ ∈ torusImage E L} {ht : t ∈ torusImage E L} {i₀ i : ZMod n}
    (h₀ : eΓ (weylG S R hinj ⟨t₀, ht₀⟩) = DihedralGroup.sr i₀)
    (h : eΓ (weylG S R hinj ⟨t, ht⟩) = DihedralGroup.sr i) (hpar : i₀.val % 2 = i.val % 2) :
    ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
      t = conjAut E x hxE * t₀ * (conjAut E x hxE)⁻¹ := by
  obtain ⟨w, hw⟩ := hconj i₀ i hpar
  set u : ↥(torusImage E L) := (weylG S R hinj).symm (eΓ.symm w) with hu
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conjAut_of_mem_torusImage u.2
  refine ⟨x, hxL, hxE, ?_⟩
  have h1 : u * ⟨t₀, ht₀⟩ * u⁻¹ = ⟨t, ht⟩ := by
    apply (weylG S R hinj).injective
    apply eΓ.injective
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hu, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, h₀, h, hw]
  have h2 := congrArg (fun y : ↥(torusImage E L) => (y : MulAut E)) h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [← h2, ← hx]

theorem kfAt_of_parity_G [Finite G]
    (hconj : ∀ i₀ i : ZMod n, i₀.val % 2 = i.val % 2 →
      ∃ w : DihedralGroup n, w * DihedralGroup.sr i₀ * w⁻¹ = DihedralGroup.sr i)
    {g : ℕ} {t₀ t : MulAut E} {ht₀ : t₀ ∈ torusImage E L} {ht : t ∈ torusImage E L}
    {i₀ i : ZMod n} (h₀ : eΓ (weylG S R hinj ⟨t₀, ht₀⟩) = DihedralGroup.sr i₀)
    (h : eΓ (weylG S R hinj ⟨t, ht⟩) = DihedralGroup.sr i) (hpar : i₀.val % 2 = i.val % 2)
    (hK : KFAt p E g t₀) : KFAt p E g t := by
  obtain ⟨x, hxL, hxE, hx⟩ := exists_conj_of_parity_G S R hinj eΓ hconj h₀ h hpar
  rw [hx]
  exact hK.conj hxE

end Conj

end CFSG.RankThree.PartOne.KF132
