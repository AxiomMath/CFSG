module

public import CFSG.LocalAnalysis.StandardType.PhanEStdLevi

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry
open scoped MatrixGroups Pointwise

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H)
  {w₀ : W} (F : FrobData D n H w₀) (hext : SteinbergExtras D n H)
  (hw₀ : IsLongest (coxeterMatrix D.isFiniteType).toCoxeterSystem Set.univ w₀)
  (hsq : ∀ i, n i * n i = 1)

include hext hw₀ hsq in
theorem stdTau_stdTau (g : K) :
    stdTau F (nrep hct w₀) (stdTau F (nrep hct w₀) g) = g := by
  have h : F.φ (nrep hct w₀) = (nrep hct w₀)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (nrep_mul_phi_self hct F hext hw₀ hsq)).symm
  simp only [stdTau_apply, map_mul, map_inv, F.invol, h]
  group

theorem map_phi_borel : (borel D H).map F.φ = borel D H := by
  refine le_antisymm F.borel_map ?_
  intro b hb
  rw [Subgroup.mem_map]
  exact ⟨F.φ b, (F.mem_borel_iff b).2 hb, F.invol b⟩

include hext hw₀ hsq in
theorem borel_inf_map_conj (hBU : BruhatExtras D H) :
    borel D H ⊓ (borel D H).map (MulAut.conj (nrep hct w₀)).toMonoidHom = ⨆ i, H i := by
  let n₀ := nrep hct w₀
  have hw₀' : ∀ i, (coxeterMatrix D.isFiniteType).toCoxeterSystem.IsRightDescent w₀ i :=
    fun i => hw₀.isRightDescent (Set.mem_univ i)
  have hconjT : ((⨆ i, H i : Subgroup K)).map (MulAut.conj n₀).toMonoidHom ≤ ⨆ i, H i := by
    rintro _ ⟨t, ht, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      conj_mem_iSup_of_mem_weylN hct (nrep_mem_weylN hct w₀) ht
  have hconjU : (posUnipotent D).map (MulAut.conj n₀).toMonoidHom ≤ negUnipotent D := by
    rintro _ ⟨u, hu, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      CFSG.LieType.TitsSimplicity.nrep_conj_mem_negUnipotent_of_forall_isRightDescent
        hct hw₀' hu
  have hconjB : (borel D H).map (MulAut.conj n₀).toMonoidHom ≤
      (⨆ i, H i) ⊔ negUnipotent D := by
    rw [show borel D H = (⨆ i, H i : Subgroup K) ⊔ posUnipotent D from rfl,
      Subgroup.map_sup]
    exact sup_le_sup hconjT hconjU
  have hTnormU : (⨆ i, H i : Subgroup K) ≤ Subgroup.normalizer (negUnipotent D : Set K) :=
    CFSG.LieType.Steinberg.le_normalizer_iSup₂ fun t ht γ hγ y hy =>
      rootGroup_le_negUnipotent hγ.1 hγ.2
        ((Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hγ.1 ht) y).1 hy)
  have hTUset : (((⨆ i, H i : Subgroup K) ⊔ negUnipotent D : Subgroup K) : Set K) =
      ((⨆ i, H i : Subgroup K) : Set K) * (negUnipotent D : Set K) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTnormU
  refine le_antisymm ?_ (le_inf iSup_le_borel ?_)
  · intro x hx
    obtain ⟨hxB, hxmap⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨b, hb, hbax⟩ := Subgroup.mem_map.1 hxmap
    have hxTU : x ∈ (⨆ i, H i : Subgroup K) ⊔ negUnipotent D :=
      hconjB (hbax ▸ Subgroup.mem_map_of_mem (MulAut.conj n₀).toMonoidHom hb)
    have hxmul : x ∈ ((⨆ i, H i : Subgroup K) : Set K) * (negUnipotent D : Set K) := by
      rw [← hTUset]
      exact hxTU
    obtain ⟨t, ht, v, hv, htv⟩ := Set.mem_mul.1 hxmul
    have hvB : v ∈ borel D H := by
      have hvx : v = t⁻¹ * x := by rw [← htv]; group
      rw [hvx]
      exact mul_mem (inv_mem (iSup_le_borel ht)) hxB
    have hvbot : v ∈ (⊥ : Subgroup K) := by
      rw [← hBU.borel_inf_negUnipotent]
      exact Subgroup.mem_inf.2 ⟨hvB, hv⟩
    have hv1 : v = 1 := by simpa using hvbot
    rw [← htv, hv1, mul_one]
    exact ht
  · intro t ht
    refine Subgroup.mem_map.2 ⟨(nrep hct w₀)⁻¹ * t * nrep hct w₀, ?_, ?_⟩
    · exact iSup_le_borel (nrep_inv_conj_mem_iSup hct w₀ ht)
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

include hext hw₀ hsq in
theorem borel_inf_map_stdTau (hBU : BruhatExtras D H) :
    borel D H ⊓ (borel D H).map (stdTau F (nrep hct w₀)) = ⨆ i, H i := by
  have hcomp : (borel D H).map (stdTau F (nrep hct w₀)) =
      ((borel D H).map F.φ).map (MulAut.conj (nrep hct w₀)).toMonoidHom := by
    rw [show stdTau F (nrep hct w₀) =
      (MulAut.conj (nrep hct w₀)).toMonoidHom.comp F.φ from rfl, Subgroup.map_map]
  rw [hcomp, map_phi_borel F]
  exact borel_inf_map_conj hct hext hw₀ hsq hBU

private theorem hmbTor_units_map_inv_eq_iff {Fld : Type} [Field Fld] (θ : Fld →+* Fld)
    (a : Fldˣ) : (Units.map θ.toMonoidHom a)⁻¹ = a ↔ θ (a : Fld) * a = 1 := by
  rw [inv_eq_iff_mul_eq_one, Units.ext_iff, Units.val_mul, Units.val_one]
  exact Iff.rfl

theorem ε_torusHom_mem_stdFix_iff {n₀ : K} (L : StdLevi F n₀) (i : Fin D.rank) (a : L.Fldˣ) :
    L.ε i (WeakCT.torusHom L.Fld a) ∈ stdFix F n₀ ↔ L.θ (a : L.Fld) * a = 1 := by
  rw [mem_stdFix_iff, ← stdTau_apply]
  rw [StdLevi.stdTau_ε L i (WeakCT.torusHom L.Fld a)]
  rw [(L.ε_inj i).eq_iff]
  rw [slSigma_torusHom L.θ a]
  rw [(WeakCT.torusHom_injective (K := L.Fld)).eq_iff]
  exact hmbTor_units_map_inv_eq_iff L.θ a

include hext in
theorem torus_lang {n₀ : K} (L : StdLevi F n₀) {s : K} (hs : s ∈ ⨆ i, H i)
    (hτ : stdTau F n₀ s = s⁻¹) : ∃ r ∈ ⨆ i, H i, s = r * (stdTau F n₀ r)⁻¹ := by
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 (by rw [L.range_torusMap hext]; exact hs)
  have hτa : stdTau F n₀ (L.torusMap hext a) = (L.torusMap hext a)⁻¹ := by
    rw [ha]
    exact hτ
  rw [L.stdTau_torusMap hext a, ← map_inv] at hτa
  have hcoord : (fun i => (Units.map L.θ.toMonoidHom (a i))⁻¹) = a⁻¹ :=
    L.torusMap_injective hext hτa
  have hθa : ∀ i, L.θ (a i : L.Fld) = (a i : L.Fld) := by
    intro i
    have h : Units.map L.θ.toMonoidHom (a i) = a i := by
      have h1 := congr_fun hcoord i
      simp only [Pi.inv_apply] at h1
      rwa [inv_inj] at h1
    have h2 := congrArg (fun u : L.Fldˣ => (u : L.Fld)) h
    exact h2
  choose b hb using fun i => L.norm_surj (a i : L.Fld) (a i).ne_zero (hθa i)
  have hbne : ∀ i, b i ≠ 0 := fun i h0 => by
    have h := hb i
    rw [h0, zero_mul] at h
    exact (a i).ne_zero h.symm
  let b' : Fin D.rank → L.Fldˣ := fun i => Units.mk0 (b i) (hbne i)
  refine ⟨L.torusMap hext b', ?_, ?_⟩
  · rw [← L.range_torusMap hext]
    exact MonoidHom.mem_range.2 ⟨b', rfl⟩
  · rw [← ha, L.stdTau_torusMap hext b', ← map_inv, ← map_mul]
    congr 1
    funext i
    have hunit : b' i * Units.map L.θ.toMonoidHom (b' i) = a i := by
      refine Units.ext ?_
      exact hb i
    simpa only [Pi.mul_apply, Pi.inv_apply, inv_inv] using hunit.symm

include hext hw₀ hsq in
theorem borel_inf_stdFix (hBU : BruhatExtras D H) (L : StdLevi F (nrep hct w₀)) :
    borel D H ⊓ stdFix F (nrep hct w₀) = ⨆ i, (H i ⊓ stdFix F (nrep hct w₀)) := by
  refine le_antisymm ?_ (le_inf ?_ ?_)
  · intro g hg
    obtain ⟨hgB, hgfix⟩ := Subgroup.mem_inf.1 hg
    have hgτ : stdTau F (nrep hct w₀) g = g := hgfix
    have hgmap : g ∈ (borel D H).map (stdTau F (nrep hct w₀)) :=
      Subgroup.mem_map.2 ⟨g, hgB, hgτ⟩
    have hgT : g ∈ ⨆ i, H i := by
      rw [← borel_inf_map_stdTau hct F hext hw₀ hsq hBU]
      exact Subgroup.mem_inf.2 ⟨hgB, hgmap⟩
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 (by rw [L.range_torusMap hext]; exact hgT)
    have hτa : stdTau F (nrep hct w₀) (L.torusMap hext a) = L.torusMap hext a := by
      rw [ha]
      exact hgτ
    rw [L.stdTau_torusMap hext a] at hτa
    have hcoord : (fun i => (Units.map L.θ.toMonoidHom (a i))⁻¹) = a :=
      L.torusMap_injective hext hτa
    have hθa : ∀ i, L.θ (a i : L.Fld) * (a i : L.Fld) = 1 := by
      intro i
      have h : (Units.map L.θ.toMonoidHom (a i))⁻¹ = a i := congr_fun hcoord i
      have hu : Units.map L.θ.toMonoidHom (a i) * a i = 1 := inv_eq_iff_mul_eq_one.mp h
      have h2 := congrArg (fun u : L.Fldˣ => (u : L.Fld)) hu
      exact h2
    rw [← ha, show L.torusMap hext = MonoidHom.noncommPiCoprod
        (fun i => (L.ε i).comp (WeakCT.torusHom L.Fld)) (L.torus_commute hext) from rfl,
      MonoidHom.noncommPiCoprod_apply]
    refine Subgroup.noncommProd_mem _ _ (fun i _ => ?_)
    exact le_iSup (fun i => H i ⊓ stdFix F (nrep hct w₀)) i
      (Subgroup.mem_inf.2 ⟨L.ε_torusHom_mem i (a i),
        (ε_torusHom_mem_stdFix_iff (F := F) (L := L) i (a i)).2 (hθa i)⟩)
  · refine iSup_le fun i => ?_
    exact (inf_le_left : H i ⊓ stdFix F (nrep hct w₀) ≤ H i).trans
      ((le_iSup H i).trans iSup_le_borel)
  · exact iSup_le fun i => inf_le_right

end CFSG.ClassicalInvolution.Phan.PhanE
