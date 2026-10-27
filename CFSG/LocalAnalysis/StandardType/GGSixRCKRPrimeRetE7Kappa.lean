module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeRetE7Frame

import CFSG.Blueprint.ChevalleyRootGroups
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
import CFSG.LocalAnalysis.StandardType.GGFamTrivialRoots

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem rckE7Kappa_range {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {a : Fin τ.rank → GGLˣ} (i : KernelComponent (rootCharHom a))
    (F : RCKE7Frame (componentRoots (rootCharHom a) i)) (SK : LangSetup Tag.E7 GGL 5)
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (htr : ∀ y : adjointGroup Tag.E7 GGL, ∃ hy : SK.D.step y ∈ adjointGroup Tag.E7 GGL,
      (F.ε ⟨SK.D.step y, hy⟩ : ModGL τ GGL) = S.D.step (F.ε y))
    (hperf : Group.IsPerfect ↥SK.Γ)
    (hR : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan τ GGL (componentRoots (rootCharHom a) i)) :
    (rckE7Kappa F hR).range = SK.Γ := by
  let Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i
  let US : Subgroup (ModGL τ GGL) := rootSpan τ GGL Ψ
  let MS : Subgroup (ModGL τ GGL) := S.D.model
  let Q : Subgroup (ModGL τ GGL) := rationalSpan S.ρ S.Γ (rootCharHom a) i
  let R : Subgroup (ModGL τ GGL) := rationalComponent S.ρ S.Γ (rootCharHom a) i
  let adjE : Subgroup (ModGL Tag.E7 GGL) := adjointGroup Tag.E7 GGL
  let MK : Subgroup (ModGL Tag.E7 GGL) := SK.D.model
  let MKadj : Subgroup ↥adjE := MK.subgroupOf adjE
  let ΓK : Subgroup (ModGL Tag.E7 GGL) := SK.Γ
  let Γa : Subgroup ↥adjE := ΓK.subgroupOf adjE
  let ε' : ↥adjE →* ↥US := F.ε.toMonoidHom
  let ψ : ↥US →* ↥adjE := F.ε.symm.toMonoidHom
  let X' : Subgroup ↥US := MKadj.map ε'
  let X : Subgroup (ModGL τ GGL) := US ⊓ MS
  have hrat : rationalRoots S.ρ (rootCharHom a) i = Ψ := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k with
      | zero => exact hδ
      | succ k ih => rw [Function.iterate_succ_apply']; exact hρ _ ih
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  have hUS_adj : US ≤ adjointGroup τ GGL := rootSpan_le_adjointGroup GGL Ψ
  have hMK_adj : MK ≤ adjE := inf_le_left
  have hΓK_MK : ΓK ≤ MK := by
    show ⁅MK, MK⁆ ≤ MK
    exact Subgroup.commutator_le_self MK
  have hΓK_adj : ΓK ≤ adjE := hΓK_MK.trans hMK_adj
  have hQ_US : Q ≤ US := by
    change rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ rootSpan τ GGL Ψ
    rw [rationalSpan, hrat]
    exact inf_le_left
  have hQ_MS : Q ≤ MS := by
    change rationalSpan S.ρ S.Γ (rootCharHom a) i ≤ S.D.model
    rw [rationalSpan]
    exact inf_le_right.trans (Subgroup.commutator_le_self S.D.model)
  have hQ_X : Q ≤ X := le_inf hQ_US hQ_MS
  have hR_US : R ≤ US := hR
  have hstep_iff : ∀ y : ↥adjE,
      SK.D.step y = y ↔ S.D.step ((F.ε y : ↥US) : ModGL τ GGL) =
        ((F.ε y : ↥US) : ModGL τ GGL) := by
    intro y
    constructor
    · intro hy
      obtain ⟨hy', hstep⟩ := htr y
      have h1 : (⟨SK.D.step y, hy'⟩ : ↥adjE) = y := Subtype.ext hy
      rw [← hstep, h1]
    · intro hy
      obtain ⟨hy', hstep⟩ := htr y
      have h1 : (F.ε ⟨SK.D.step y, hy'⟩ : ↥US) = F.ε y := by
        apply Subtype.ext
        rw [hstep, hy]
      exact Subtype.ext_iff.mp (F.ε.injective h1)
  have hmem_MK : ∀ y : ↥adjE, y ∈ MKadj ↔ SK.D.step y = y := by
    intro y
    change (y : ModGL Tag.E7 GGL) ∈ SK.D.model ↔ SK.D.step y = y
    rw [LangDatum.mem_model]
    constructor
    · rintro ⟨-, h⟩
      simpa [LangDatum.step] using h
    · intro h
      exact ⟨y.2, by simpa [LangDatum.step] using h⟩
  have hmem_X : ∀ y : ↥adjE, y ∈ MKadj ↔ ((F.ε y : ↥US) : ModGL τ GGL) ∈ X := by
    intro y
    rw [hmem_MK y]
    constructor
    · intro hstep
      refine ⟨(F.ε y).2, ?_⟩
      change ((F.ε y : ↥US) : ModGL τ GGL) ∈ S.D.model
      rw [LangDatum.mem_model]
      exact ⟨hUS_adj (F.ε y).2, by simpa [LangDatum.step] using (hstep_iff y).1 hstep⟩
    · rintro ⟨-, hMS⟩
      exact (hstep_iff y).2 (by
        have h := (S.D.mem_model.mp (by simpa [MS] using hMS)).2
        simpa [LangDatum.step] using h)
  have hX'_map : X'.map US.subtype = X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
      exact (hmem_X y').1 hy'
    · rintro ⟨hxUS, hxMS⟩
      let y : ↥adjE := F.ε.symm ⟨x, hxUS⟩
      have hxy : ((F.ε y : ↥US) : ModGL τ GGL) = x := by simp [y]
      have hy : y ∈ MKadj := by
        rw [hmem_X]
        rw [hxy]
        exact ⟨hxUS, hxMS⟩
      refine ⟨ε' y, Subgroup.mem_map_of_mem ε' hy, ?_⟩
      change ((ε' y : ↥US) : ModGL τ GGL) = x
      simpa [ε', y] using hxy
  have hmap_model : MKadj.map (US.subtype.comp ε') = X := by
    rw [← Subgroup.map_map]
    exact hX'_map
  have hQmap : (Q.subgroupOf US).map ψ ≤ MKadj := by
    rintro y ⟨q, hq, rfl⟩
    have hqQ : (q : ModGL τ GGL) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    have hqX : (q : ModGL τ GGL) ∈ X := hQ_X hqQ
    have hqmap : (q : ModGL τ GGL) ∈ MKadj.map (US.subtype.comp ε') := by
      rwa [hmap_model]
    obtain ⟨m, hm, hmq⟩ := Subgroup.mem_map.mp hqmap
    have hqeq : q = F.ε m := Subtype.ext hmq.symm
    rw [show ψ q = m by
      rw [hqeq]
      simp [ψ, ε']]
    exact hm
  have hQcomm : R.subgroupOf US = ⁅Q.subgroupOf US, Q.subgroupOf US⁆ := by
    apply Subgroup.map_injective US.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hR_US,
      Subgroup.map_subgroupOf_eq_of_le hQ_US]
    rfl
  have hMKadj_map : MKadj.map adjE.subtype = MK :=
    Subgroup.map_subgroupOf_eq_of_le hMK_adj
  have hGamma_comm : Γa = ⁅MKadj, MKadj⁆ := by
    apply Subgroup.map_injective adjE.subtype_injective
    change Subgroup.map adjE.subtype (ΓK.subgroupOf adjE) =
      Subgroup.map adjE.subtype ⁅MKadj, MKadj⁆
    rw [Subgroup.map_commutator, hMKadj_map, Subgroup.map_subgroupOf_eq_of_le hΓK_adj]
    rfl
  have hGamma_image : Γa.map ε' = ⁅X', X'⁆ := by
    rw [hGamma_comm, Subgroup.map_commutator]
  have hperfΓa : Group.IsPerfect ↥Γa :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hΓK_adj).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hΓK_adj).symm.surjective
  haveI : Group.IsPerfect ↥Γa := hperfΓa
  have hperfX' : Group.IsPerfect ↥(⁅X', X'⁆) := by
    rw [← hGamma_image]
    exact Group.IsPerfect.map (f := ε')
  haveI : Group.IsPerfect ↥(⁅X', X'⁆) := hperfX'
  have hXXperf : Group.IsPerfect ↥(⁅X, X⁆) := by
    have h := Group.IsPerfect.map (H := ⁅X', X'⁆) (f := US.subtype)
    have hmap : (⁅X', X'⁆).map US.subtype = ⁅X, X⁆ := by
      rw [Subgroup.map_commutator, hX'_map]
    rwa [hmap] at h
  have hXX_eq : ⁅(⁅X, X⁆ : Subgroup (ModGL τ GGL)), ⁅X, X⁆⁆ = ⁅X, X⁆ :=
    Subgroup.isPerfect_iff.mp hXXperf
  have hXX_le_US : ⁅X, X⁆ ≤ US := (Subgroup.commutator_le_self X).trans inf_le_left
  have hXX_le_SΓ : ⁅X, X⁆ ≤ S.Γ := by
    have h := Subgroup.commutator_mono (inf_le_right : X ≤ MS) (inf_le_right : X ≤ MS)
    simpa [MS, LangSetup.Γ, LangDatum.Γ] using h
  have hXX_le_root : ⁅X, X⁆ ≤ rootSpan τ GGL (rationalRoots S.ρ (rootCharHom a) i) := by
    rw [hrat]
    exact hXX_le_US
  have hXX_le_Q : ⁅X, X⁆ ≤ Q := by
    change ⁅X, X⁆ ≤ rationalSpan S.ρ S.Γ (rootCharHom a) i
    rw [rationalSpan]
    exact le_inf hXX_le_root hXX_le_SΓ
  have hXX_le_R : ⁅X, X⁆ ≤ R := by
    calc ⁅X, X⁆ = ⁅⁅X, X⁆, ⁅X, X⁆⁆ := hXX_eq.symm
      _ ≤ ⁅Q, Q⁆ := Subgroup.commutator_mono hXX_le_Q hXX_le_Q
      _ = R := rfl
  have hX'comm_le : ⁅X', X'⁆ ≤ R.subgroupOf US := by
    have hmap_comm : (⁅X', X'⁆).map US.subtype = ⁅X, X⁆ := by
      rw [Subgroup.map_commutator, hX'_map]
    have heq : ⁅X', X'⁆ = (⁅X, X⁆).subgroupOf US := by
      apply Subgroup.map_injective US.subtype_injective
      rw [hmap_comm, Subgroup.map_subgroupOf_eq_of_le hXX_le_US]
    rw [heq]
    exact Subgroup.subgroupOf_mono _ hXX_le_R
  have hΓa_mapψ : (Γa.map ε').map ψ = Γa := by
    rw [Subgroup.map_map]
    have hcomp : ψ.comp ε' = MonoidHom.id ↥adjE := by
      ext x
      simp [ψ, ε']
    rw [hcomp, Subgroup.map_id]
  have hrange_decomp : (rckE7Kappa F hR).range =
      ((R.subgroupOf US).map ψ).map adjE.subtype := by
    unfold rckE7Kappa
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hκ_le : (rckE7Kappa F hR).range ≤ ΓK := by
    rw [hrange_decomp]
    calc ((R.subgroupOf US).map ψ).map adjE.subtype
        = ((⁅Q.subgroupOf US, Q.subgroupOf US⁆).map ψ).map adjE.subtype := by rw [hQcomm]
      _ = (⁅(Q.subgroupOf US).map ψ, (Q.subgroupOf US).map ψ⁆).map adjE.subtype := by
            rw [Subgroup.map_commutator]
      _ ≤ (⁅MKadj, MKadj⁆).map adjE.subtype :=
            Subgroup.map_mono (Subgroup.commutator_mono hQmap hQmap)
      _ = Γa.map adjE.subtype := by rw [hGamma_comm]
      _ = ΓK := Subgroup.map_subgroupOf_eq_of_le hΓK_adj
  have hΓK_le : ΓK ≤ (rckE7Kappa F hR).range := by
    rw [hrange_decomp]
    calc ΓK = Γa.map adjE.subtype := (Subgroup.map_subgroupOf_eq_of_le hΓK_adj).symm
      _ = (((Γa.map ε').map ψ)).map adjE.subtype := by rw [hΓa_mapψ]
      _ = (Γa.map ε').map (adjE.subtype.comp ψ) := by rw [Subgroup.map_map]
      _ ≤ ((R.subgroupOf US).map (adjE.subtype.comp ψ)) :=
            Subgroup.map_mono (by rw [hGamma_image]; exact hX'comm_le)
      _ = ((R.subgroupOf US).map ψ).map adjE.subtype := by rw [Subgroup.map_map]
  exact le_antisymm hκ_le hΓK_le

theorem rckE7Kappa_ker {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ)
    {R : Subgroup (ModGL τ GGL)} (hR : R ≤ rootSpan τ GGL Ψ) {Γ : Subgroup (ModGL Tag.E7 GGL)}
    (hrange : (rckE7Kappa F hR).range = Γ) (hcen : Subgroup.center ↥Γ = ⊥) :
    (rckE7Kappa F hR).ker = Subgroup.center ↥R := by
  have hinj : Function.Injective (rckE7Kappa F hR) := rckE7Kappa_injective F hR
  have hker : (rckE7Kappa F hR).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 hinj
  have hcenter : Subgroup.center ↥R = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro z hz
    rw [Subgroup.mem_bot]
    apply hinj
    let y : ↥Γ := ⟨rckE7Kappa F hR z, by rw [← hrange]; exact ⟨z, rfl⟩⟩
    have hycen : y ∈ Subgroup.center ↥Γ := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨x, hx⟩ := (show (w : ModGL Tag.E7 GGL) ∈ (rckE7Kappa F hR).range by
        rw [hrange]
        exact w.2)
      apply Subtype.ext
      change (w : ModGL Tag.E7 GGL) * rckE7Kappa F hR z =
        rckE7Kappa F hR z * (w : ModGL Tag.E7 GGL)
      calc (w : ModGL Tag.E7 GGL) * rckE7Kappa F hR z
          = rckE7Kappa F hR x * rckE7Kappa F hR z := by rw [hx]
        _ = rckE7Kappa F hR (x * z) := by rw [map_mul]
        _ = rckE7Kappa F hR (z * x) := by rw [← Subgroup.mem_center_iff.mp hz x]
        _ = rckE7Kappa F hR z * rckE7Kappa F hR x := by rw [map_mul]
        _ = rckE7Kappa F hR z * (w : ModGL Tag.E7 GGL) := by rw [hx]
    have hy1 : y = 1 := by
      have h := hycen
      rw [hcen] at h
      simpa using h
    simpa [y] using congrArg Subtype.val hy1
  rw [hker, hcenter]

theorem isQuasisimple_of_rckE7Kappa {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ)
    {R : Subgroup (ModGL τ GGL)} (hR : R ≤ rootSpan τ GGL Ψ) {Γ : Subgroup (ModGL Tag.E7 GGL)}
    (hrange : (rckE7Kappa F hR).range = Γ) (hQS : CFSG.IsQuasisimple ↥R) :
    CFSG.IsQuasisimple ↥Γ := by
  let e : ↥R ≃* ↥Γ :=
    (MonoidHom.ofInjective (rckE7Kappa_injective F hR)).trans
      (MulEquiv.subgroupCongr hrange)
  exact (CFSG.IsQuasisimple.congr e).mp hQS

theorem exists_cover_of_rckE7Kappa {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (F : RCKE7Frame Ψ)
    {R : Subgroup (ModGL τ GGL)} (hR : R ≤ rootSpan τ GGL Ψ) {Γ : Subgroup (ModGL Tag.E7 GGL)}
    (hrange : (rckE7Kappa F hR).range = Γ) {U : Type*} [Group U] (φK : U →* ModGL Tag.E7 GGL)
    (hφK : φK.range = Γ) :
    ∃ φ : U →* ↥R, (rckE7Kappa F hR).comp φ = φK ∧ Function.Surjective φ ∧ φ.ker = φK.ker := by
  let e : ↥R ≃* ↥Γ :=
    (MonoidHom.ofInjective (rckE7Kappa_injective F hR)).trans
      (MulEquiv.subgroupCongr hrange)
  have hmem : ∀ x, φK x ∈ Γ := fun x => by
    rw [← hφK, MonoidHom.mem_range]
    exact ⟨x, rfl⟩
  let φ : U →* ↥R := e.symm.toMonoidHom.comp (φK.codRestrict Γ hmem)
  have hκe : ∀ x : ↥R, rckE7Kappa F hR x = (e x : ModGL Tag.E7 GGL) := by
    intro x
    simp only [e, MulEquiv.trans_apply, MonoidHom.ofInjective_apply,
      MulEquiv.subgroupCongr_apply]
  have hc_surj : Function.Surjective (φK.codRestrict Γ hmem) := by
    intro y
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (show (y : ModGL Tag.E7 GGL) ∈ φK.range by
      rw [hφK]
      exact y.2)
    exact ⟨u, Subtype.ext hu⟩
  refine ⟨φ, ?_, ?_, ?_⟩
  · apply MonoidHom.ext
    intro u
    change rckE7Kappa F hR (φ u) = φK u
    rw [hκe, show φ u = e.symm ((φK.codRestrict Γ hmem) u) from rfl,
      MulEquiv.apply_symm_apply]
    rfl
  · exact e.symm.surjective.comp hc_surj
  · apply le_antisymm
    · intro u hu
      have h2 : (φK.codRestrict Γ hmem) u = 1 := by
        apply e.symm.injective
        simpa [φ] using hu
      exact congrArg Subtype.val h2
    · intro u hu
      have h2 : (φK.codRestrict Γ hmem) u = 1 := Subtype.ext hu
      show φ u = 1
      simp [φ, h2]

theorem rationalComponent_one_eq_E7 (SK : LangSetup Tag.E7 GGL 5)
    (i : KernelComponent (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)))
    (hperf : Group.IsPerfect ↥SK.Γ) :
    rationalComponent SK.ρ SK.Γ (rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)) i = SK.Γ := by
  let χ : Multiplicative (Fin Tag.E7.rank → ℤ) →* GGLˣ :=
    rootCharHom (1 : Fin Tag.E7.rank → GGLˣ)
  have hχ : ∀ γ : Fin Tag.E7.rank → ℤ, χ (Multiplicative.ofAdd γ) = 1 := by
    intro γ
    simp [χ, rootCharHom, rootChar]
  have hcomponent : componentRoots χ i = {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ} :=
    CFSG.StandardType.TableCRes.famTrivial_componentRoots_eq_univ
      (Or.inr (Or.inl rfl)) χ hχ i
  have hstab : (SK.ρ : (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ)) ''
      componentRoots χ i = componentRoots χ i := by
    rw [hcomponent, CFSG.StandardType.TableCRes.famTrivial_image_roots_eq SK.ρ SK.frob.isRoot_iff]
  have hiter : ∀ k : ℕ, (SK.ρ : (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ))^[k] ''
      componentRoots χ i = componentRoots χ i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ', Set.image_comp, ih, hstab]
  have hrat : rationalRoots SK.ρ χ i = {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ} := by
    apply Set.Subset.antisymm
    · rintro γ ⟨k, δ, hδ, rfl⟩
      have h := Set.mem_image_of_mem ((SK.ρ : (Fin Tag.E7.rank → ℤ) → _)^[k]) hδ
      rw [hiter k, hcomponent] at h
      exact h
    · rintro γ hγ
      exact ⟨0, γ, hcomponent.ge hγ, by simp⟩
  have hΓ_model : SK.Γ ≤ SK.D.model := Subgroup.commutator_le_self SK.D.model
  have hΓ_rootSpan : SK.Γ ≤ rootSpan Tag.E7 GGL {γ : Fin Tag.E7.rank → ℤ | IsRoot Tag.E7 γ} := by
    refine hΓ_model.trans ?_
    rw [← adjointGroup_eq_rootSpan]
    exact inf_le_left
  have hspan : rationalSpan SK.ρ SK.Γ χ i = SK.Γ := by
    rw [rationalSpan, hrat]
    exact le_antisymm inf_le_right (le_inf hΓ_rootSpan le_rfl)
  rw [rationalComponent, hspan]
  exact Subgroup.isPerfect_iff.mp hperf

end CFSG.StandardType.RCKRP

end
